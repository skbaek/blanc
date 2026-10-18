import Blanc.Lift.Curve3Pool.LivePremises
import Blanc.Lift.Curve3Crv.CostBounds
import Blanc.Lift.Curve3Crv.Check
import Blanc.Composition.Curve3CrvPositional
import Blanc.Composition.UniswapV2PairWeth9SwapLegsRead
import Blanc.Lift.StaticOnlyRoots
import Blanc.ExecutionErrorKeep
import Blanc.CodeDelegation

/-!
# The pool's 3Crv callee premises, discharged by the deployed 3Crv (U8d)

`Curve3Pool/LivePremises.lean` states what each pool call into 3Crv must do: `totalSupply()`
answers (`SupplyOkAt`, `remove_liquidity`'s `SupplyOk`), `mint(msg.sender, amt)` succeeds
(`MintOkAt`) and `burnFrom(msg.sender, amt)` succeeds (`BurnOkAt`, `remove_liquidity`'s `BurnOk`).
This module proves them for the deployed 3Crv runtime, at every call window, with the uniform
bound `U ≥ 70000` gas, from facts about the call-site world only:

* the token address holds 3Crv's code (`Curve3Crv.code`), is not the pool and is no precompile;
* for `mint`/`burnFrom`, 3Crv's `minter` is the pool and the amounts fit (`C3MintFits`,
  `C3BurnFits`: the exact acceptance conditions of 3Crv's `mint` and `burnFrom` bodies);
* for `totalSupply()`, 3Crv's supply slot holds the answer `T`.

The world invariant the call leaves (`W'`) only needs to be closed under what the call does:
storage kept everywhere but at the token (whose storage becomes 3Crv's model result), code kept
everywhere.

**This is also the non-vacuity witness for the 3Crv callee premises**: they hold for the deployed
3Crv code, so the pool liveness theorems that assume them (`exchange_live` … and the history
wrappers of `HistoryLive.lean`) are not vacuous on the 3Crv side.

The crossing is the zero-value `CALL` / `STATICCALL` crossing with a known child
(`Ninst.runCompiled_call_zero_child`, `Ninst.runCompiled_staticcall_child`); the child run is
`c3crv_exec_le` over the bounded bodies of `CostBounds.lean`; the child settles cleanly by
`Exec.ok_error_eq`; the code at the identity precompile survives the child by `Exec.codeAt_avoid`,
because every frame below a 3Crv frame is a static call frame (`Exec.staticOnly_rawFrameDescendants`
with `c3crv_cert_staticOnly`).

* `c3crv_supplyOkAt`, `c3crv_mintOkAt`, `c3crv_burnOkAt` — the windowed premises;
* `c3crv_supplyOk`, `c3crv_burnOk` — `remove_liquidity`'s.
-/

namespace Blanc.Composition.Curve3PoolCalleeLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.UniswapV2PairWeth9Joint (Ninst.runCompiled_staticcall_child)

/-! ## The call site: popped, warmed, charged -/

section Site

variable (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi os : B256)

/-- The call state with its operands popped (gas `g` left). -/
def popped (g : Nat) : Devm := b.setMach ⟨S, M, g, b.stateGas⟩

/-- The popped state with the callee warmed. -/
def warmed : Devm := addAccessedAddress (popped b S M G) t.toAdr

/-- The windows' expansion charge. -/
def ext : Nat := (popped b S M 0).extCost [⟨ii.toNat, is.toNat⟩, ⟨oi.toNat, os.toNat⟩]

/-- The callee's access charge. -/
def acc : Nat := accessCost t.toAdr b.accessedAddresses

/-- The gas the call forwards (`GAS; CALL`, all but a 64th of what the charges leave). -/
def fwd : Nat := except64th (G - ext b S M ii is oi os - acc b t)

/-- The parent the child returns to. -/
def parent : Devm :=
  callSpawnParent (warmed b S M G t) (fwd b S M G t ii is oi os + acc b t + ext b S M ii is oi os)
    ii.toNat is.toNat oi.toNat os.toNat

/-- The child message of a zero-value `CALL`. -/
def callMsg0 : Msg :=
  valueCallSpawnMsg sevm (parent b S M G t ii is oi os) (fwd b S M G t ii is oi os) 0 t.toAdr
    t.toAdr ii.toNat is.toNat (b.getCode t.toAdr) false

/-- The child message of a `STATICCALL`. -/
def staticMsg : Msg :=
  staticcallSpawnMsg sevm (parent b S M G t ii is oi os) (fwd b S M G t ii is oi os) t.toAdr
    t.toAdr ii.toNat is.toNat (b.getCode t.toAdr) false

end Site

/-! ## The crossings with a known child -/

section Cross

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {t ii is oi os : B256}

theorem popped_eq :
    (St b (Nat.toB256 G :: t :: ii :: is :: oi :: os :: S) M G).setMach
      ⟨S, (St b (Nat.toB256 G :: t :: ii :: is :: oi :: os :: S) M G).memory,
        (St b (Nat.toB256 G :: t :: ii :: is :: oi :: os :: S) M G).gasLeft,
        (St b (Nat.toB256 G :: t :: ii :: is :: oi :: os :: S) M G).stateGas⟩ =
      popped b S M G := rfl

theorem popped_extCost (g : Nat) :
    (popped b S M g).extCost [⟨ii.toNat, is.toNat⟩, ⟨oi.toNat, os.toNat⟩] =
      ext b S M ii is oi os := rfl

theorem warmed_delegation (hdel : getDelegatedCodeAddress (b.getCode t.toAdr) = none) :
    accessDelegation (addAccessedAddress (popped b S M G) t.toAdr) t.toAdr =
      ⟨false, t.toAdr, b.getCode t.toAdr, 0, warmed b S M G t⟩ := by
  unfold accessDelegation warmed
  dsimp only
  have h : (addAccessedAddress (popped b S M G) t.toAdr).state.getCode t.toAdr =
      b.getCode t.toAdr := rfl
  rw [h, hdel]

theorem warmed_gasLeft : (warmed b S M G t).gasLeft = G := rfl

theorem fwd_split (hG : G < 2 ^ 256) (hcharge : acc b t + ext b S M ii is oi os ≤ G) :
    calculateMsgCallGas 0 (Nat.toB256 G).toNat (warmed b S M G t).gasLeft
        (ext b S M ii is oi os) (acc b t) =
      ⟨fwd b S M G t ii is oi os + acc b t, fwd b S M G t ii is oi os⟩ := by
  rw [B256.toNat_toB256_of_lt hG, warmed_gasLeft]
  have hle : fwd b S M G t ii is oi os ≤ G := by unfold fwd except64th; omega
  unfold calculateMsgCallGas
  simp only [show ¬ G < acc b t + ext b S M ii is oi os from by omega, ↓reduceIte]
  rw [show except64th (G - ext b S M ii is oi os - acc b t) = fwd b S M G t ii is oi os from rfl,
    Nat.min_eq_right hle, Nat.add_zero]

theorem fwd_charge (hcharge : acc b t + ext b S M ii is oi os ≤ G) :
    fwd b S M G t ii is oi os + acc b t + ext b S M ii is oi os ≤ G := by
  unfold fwd except64th; omega

/-- **A zero-value `CALL` whose child halts cleanly** resumes in `callChildPost` at the site's
parent. -/
theorem call0_cross {cpost : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hdel : getDelegatedCodeAddress (b.getCode t.toAdr) = none) (hroom : S.length < 1024)
    (hG : G < 2 ^ 256) (hcharge : acc b t + ext b S M ii is oi os ≤ G)
    (hexec : exec (initEvm (callMsg0 sevm b S M G t ii is oi os)) = .ok cpost)
    (herr : cpost.error = none) :
    Ninst.RunCompiled sevm (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: os :: S) M G)
      (.exec .call) (callChildPost (parent b S M G t ii is oi os) cpost oi.toNat os.toNat) :=
  Ninst.runCompiled_call_zero_child (gw := Nat.toB256 G) (cw := t) (s := S) (dp := false)
    (dadr := t.toAdr) (code := b.getCode t.toAdr) (dgc := 0) (d1 := warmed b S M G t)
    (ext := ext b S M ii is oi os) (acc := acc b t) (mcc := fwd b S M G t ii is oi os + acc b t)
    (mcs := fwd b S M G t ii is oi os)
    (stmid := (warmed b S M G t).state.setBal sevm.currentTarget
      ((warmed b S M G t).state.bal sevm.currentTarget - 0))
    hfork rfl rfl (warmed_delegation hdel) rfl (fwd_split hG hcharge) (fwd_charge hcharge)
    hdepth hprec hroom
    (by
      unfold State.subBal
      simp only [show ¬ (warmed b S M G t).state.bal sevm.currentTarget < 0 from
        B256.not_lt.mpr (B256.zero_le _), ↓reduceIte])
    (by rw [UniswapV2PairWeth9Joint.callChildMsg_zero]; exact hexec) herr

/-- **A `STATICCALL` whose child halts cleanly** resumes in `callChildPost` at the site's
parent. -/
theorem static_cross {cpost : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hdel : getDelegatedCodeAddress (b.getCode t.toAdr) = none) (hroom : S.length < 1024)
    (hG : G < 2 ^ 256) (hcharge : acc b t + ext b S M ii is oi os ≤ G)
    (hexec : exec (initEvm (staticMsg sevm b S M G t ii is oi os)) = .ok cpost)
    (herr : cpost.error = none) :
    Ninst.RunCompiled sevm (St b (Nat.toB256 G :: t :: ii :: is :: oi :: os :: S) M G)
      (.exec .staticcall) (callChildPost (parent b S M G t ii is oi os) cpost oi.toNat os.toNat) :=
  Ninst.runCompiled_staticcall_child (gw := Nat.toB256 G) (tw := t) (s := S) (dp := false)
    (dadr := t.toAdr) (code := b.getCode t.toAdr) (dgc := 0) (d1 := warmed b S M G t)
    (ext := ext b S M ii is oi os) (acc := acc b t) (mcc := fwd b S M G t ii is oi os + acc b t)
    (mcs := fwd b S M G t ii is oi os)
    hfork rfl rfl (warmed_delegation hdel) rfl (fwd_split hG hcharge) (fwd_charge hcharge)
    hdepth hprec hroom hexec herr

end Cross

/-! ## The 3Crv child: a bounded body, run to a clean halt -/

section Child

/-- **A message entering 3Crv's deployed code with a bounded body** halts cleanly within the
bound plus the dispatcher's, lands as the body's raw result, and keeps the code everywhere. -/
theorem c3crv_msg_run {msg : Msg} {k : Nat} {f : SFunc} {r : Curve3Crv.Raw} {U : Nat}
    (hcode : (initSevm msg).code = Curve3Crv.code)
    (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hca : (initSevm msg).codeAddress ≠ none)
    (hf : Curve3Crv.bodies[k]? = some f)
    (hk : Curve3Crv.sels[k]? = some (Sevm.selector (initSevm msg)))
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hb : Curve3Crv.BodyLiveLe (initSevm msg) (initDevm msg) f r U)
    (herr0 : (initDevm msg).error = none)
    (hgas : U + Curve3Crv.dispatchGas k + gCallStipend < msg.gas) :
    ∃ cpost, exec (initEvm msg) = .ok cpost ∧ cpost.error = none ∧
      msg.gas ≤ cpost.gasLeft + (U + Curve3Crv.dispatchGas k) ∧ cpost.gasLeft ≤ msg.gas ∧
      Curve3Crv.Lands (initSevm msg) (initDevm msg) cpost r ∧
      ∀ a, cpost.getCode a = (initDevm msg).getCode a := by
  obtain ⟨c, hcU, hc⟩ := Curve3Crv.c3crv_exec_le hcode hfork hf hk hlen hcd hb
  obtain ⟨post, ⟨run⟩, hg, hl⟩ := hc (msg.gas - c) (by omega)
  have hst : St (initDevm msg) [] Mem.empty (msg.gas - c + c) = initDevm msg := by
    rw [Nat.sub_add_cancel (by omega)]
    exact (St.self (d := initDevm msg) rfl rfl).symm
  rw [hst] at run
  refine ⟨post, (exec_iff_exec_eq 0 _ _ _).mp ⟨run⟩,
    (Exec.ok_error_eq run hfork.rules_stateGas_none).trans herr0, by omega, by omega, hl,
    fun a => ?_⟩
  have keep := (Exec.codeAt_avoid (a := a) run hfork (fun root member hnone => ?_)).1
  · exact keep
  · simp only [Exec.rawFrameRoots, List.mem_cons] at member
    rcases member with rfl | member
    · exact absurd hnone hca
    · exact absurd hnone (Exec.staticOnly_rawFrameDescendants Curve3Crv.cert_check
        Curve3CrvToken.c3crv_cert_staticOnly (root := ⟨0, _, _, _, run⟩) rfl hcode hfork run
        (Exec.Deriv.ParentPrefix.refl _) root member)

end Child

/-! ## Gas: the windows' expansion and the access are bounded -/

section Gas

theorem memCost_ceil32 (x : Nat) :
    calculateMemoryGasCost (32 * ceilDiv x 32) = calculateMemoryGasCost x := by
  have h : ceilDiv (32 * ceilDiv x 32) 32 = ceilDiv x 32 := by
    unfold ceilDiv
    rw [Nat.mul_mod_right, ite_eq_left rfl, Nat.add_zero, Nat.mul_div_cancel_left _ (by decide)]
  unfold calculateMemoryGasCost
  rw [h]

theorem memExtSize_cost_le {n i s B : Nat} (h : i + s ≤ B) :
    calculateMemoryGasCost (memExtSize n i s) ≤
      max (calculateMemoryGasCost n) (calculateMemoryGasCost B) := by
  unfold memExtSize
  split
  · exact Nat.le_max_left _ _
  · rcases Nat.le_total (ceilDiv n 32) (ceilDiv (i + s) 32) with hle | hle
    · rw [Nat.max_eq_right hle, memCost_ceil32]
      exact (Lift.calculateMemoryGasCost_mono h).trans (Nat.le_max_right _ _)
    · rw [Nat.max_eq_left hle, memCost_ceil32]
      exact Nat.le_max_left _ _

/-- **Two windows inside the first `B` bytes cost at most the memory charge of `B` bytes.** -/
theorem extCost_two_le (d : Devm) {i1 s1 i2 s2 B : Nat} (h1 : i1 + s1 ≤ B) (h2 : i2 + s2 ≤ B) :
    d.extCost [⟨i1, s1⟩, ⟨i2, s2⟩] ≤ calculateMemoryGasCost B := by
  unfold Devm.extCost
  simp only [memExtsSize]
  have a1 := memExtSize_cost_le (n := d.memory.size) h1
  have a2 := memExtSize_cost_le (n := memExtSize d.memory.size i1 s1) h2
  omega

theorem calculateMemoryGasCost_4096 : calculateMemoryGasCost 4096 = 416 := by decide

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {t ii is oi os : B256}

theorem ext_le (hii : ii.toNat + is.toNat ≤ 4096) (hoi : oi.toNat + os.toNat ≤ 4096) :
    ext b S M ii is oi os ≤ 416 := by
  have := extCost_two_le (popped b S M 0) hii hoi
  rw [calculateMemoryGasCost_4096] at this
  exact this

theorem acc_le : acc b t ≤ 2600 := accessCost_le

/-- With at least `70000` gas, the charges leave the child at least `65000`. -/
theorem fwd_ge (hG : 70000 ≤ G) (hii : ii.toNat + is.toNat ≤ 4096)
    (hoi : oi.toNat + os.toNat ≤ 4096) :
    acc b t + ext b S M ii is oi os ≤ G ∧ 65000 ≤ fwd b S M G t ii is oi os := by
  have he := ext_le (b := b) (S := S) (M := M) hii hoi
  have ha := acc_le (b := b) (t := t)
  refine ⟨by omega, ?_⟩
  unfold fwd except64th
  omega

end Gas

/-! ## The child message -/

section MsgFacts

variable (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi os : B256)

theorem callMsg0_code : (initSevm (callMsg0 sevm b S M G t ii is oi os)).code = b.getCode t.toAdr :=
  rfl
theorem callMsg0_benvStat :
    (initSevm (callMsg0 sevm b S M G t ii is oi os)).benvStat = sevm.benvStat := rfl
theorem callMsg0_codeAddress :
    (initSevm (callMsg0 sevm b S M G t ii is oi os)).codeAddress = some t.toAdr := rfl
theorem callMsg0_value : (initSevm (callMsg0 sevm b S M G t ii is oi os)).value = 0 := rfl
theorem callMsg0_caller :
    (initSevm (callMsg0 sevm b S M G t ii is oi os)).caller = sevm.currentTarget := rfl
theorem callMsg0_currentTarget :
    (initSevm (callMsg0 sevm b S M G t ii is oi os)).currentTarget = t.toAdr := rfl
theorem callMsg0_isStatic :
    (initSevm (callMsg0 sevm b S M G t ii is oi os)).isStatic = sevm.isStatic := by
  show (false || sevm.isStatic) = sevm.isStatic
  simp only [Bool.false_or]
theorem callMsg0_data :
    (initSevm (callMsg0 sevm b S M G t ii is oi os)).data = (M.read ii.toNat is.toNat).1 := rfl
theorem callMsg0_gas : (callMsg0 sevm b S M G t ii is oi os).gas = fwd b S M G t ii is oi os :=
  rfl
theorem callMsg0_getStor (a : Adr) :
    Devm.getStor (initDevm (callMsg0 sevm b S M G t ii is oi os)) a = Devm.getStor b a := rfl
theorem callMsg0_getCode (a : Adr) :
    (initDevm (callMsg0 sevm b S M G t ii is oi os)).getCode a = b.getCode a := rfl
theorem callMsg0_error : (initDevm (callMsg0 sevm b S M G t ii is oi os)).error = none := rfl

theorem staticMsg_code : (initSevm (staticMsg sevm b S M G t ii is oi os)).code = b.getCode t.toAdr :=
  rfl
theorem staticMsg_benvStat :
    (initSevm (staticMsg sevm b S M G t ii is oi os)).benvStat = sevm.benvStat := rfl
theorem staticMsg_codeAddress :
    (initSevm (staticMsg sevm b S M G t ii is oi os)).codeAddress = some t.toAdr := rfl
theorem staticMsg_value : (initSevm (staticMsg sevm b S M G t ii is oi os)).value = 0 := rfl
theorem staticMsg_currentTarget :
    (initSevm (staticMsg sevm b S M G t ii is oi os)).currentTarget = t.toAdr := rfl
theorem staticMsg_data :
    (initSevm (staticMsg sevm b S M G t ii is oi os)).data = (M.read ii.toNat is.toNat).1 := rfl
theorem staticMsg_gas : (staticMsg sevm b S M G t ii is oi os).gas = fwd b S M G t ii is oi os :=
  rfl
theorem staticMsg_getStor (a : Adr) :
    Devm.getStor (initDevm (staticMsg sevm b S M G t ii is oi os)) a = Devm.getStor b a := rfl
theorem staticMsg_getCode (a : Adr) :
    (initDevm (staticMsg sevm b S M G t ii is oi os)).getCode a = b.getCode a := rfl
theorem staticMsg_error : (initDevm (staticMsg sevm b S M G t ii is oi os)).error = none := rfl

theorem parent_stack : (parent b S M G t ii is oi os).stack = S := rfl
theorem parent_gasLeft :
    (parent b S M G t ii is oi os).gasLeft =
      G - (fwd b S M G t ii is oi os + acc b t + ext b S M ii is oi os) := rfl
theorem parent_mem_warm (a : Adr) (h : a ∈ b.accessedAddresses) :
    a ∈ (parent b S M G t ii is oi os).accessedAddresses :=
  Std.HashSet.mem_insert.2 (Or.inr h)

end MsgFacts

/-! ## The resumed parent -/

section Resumed

variable (p c : Devm) (oi os : Nat)

theorem callChildPost_stack' : (callChildPost p c oi os).stack = 1 :: p.stack := rfl
theorem callChildPost_gasLeft' : (callChildPost p c oi os).gasLeft = p.gasLeft + c.gasLeft := rfl
theorem callChildPost_state' : (callChildPost p c oi os).state = c.state := rfl
theorem callChildPost_returnData' : (callChildPost p c oi os).returnData = c.output := rfl
theorem callChildPost_mem_warm (a : Adr) (h : a ∈ p.accessedAddresses) :
    a ∈ (callChildPost p c oi os).accessedAddresses :=
  Std.HashSet.mem_union_of_left h

end Resumed

/-! ## 3Crv's acceptance of the pool's calls -/

section Accept

open Curve3Crv

/-- The storage 3Crv's `mint(d, v)` leaves. -/
def mintStor (stor : Stor) (d v : B256) : Stor :=
  (stor.set vySupplySlot (stor.get vySupplySlot + v)).set (mapSlot 3 d)
    ((stor.set vySupplySlot (stor.get vySupplySlot + v)).get (mapSlot 3 d) + v)

/-- The storage 3Crv's `burnFrom(f, v)` leaves. -/
def burnStor (stor : Stor) (f v : B256) : Stor :=
  (stor.set vySupplySlot (stor.get vySupplySlot - v)).set (mapSlot 3 f)
    ((stor.set vySupplySlot (stor.get vySupplySlot - v)).get (mapSlot 3 f) - v)

/-- **3Crv accepts `mint(d, v)` from `pool`**: `pool` is the minter, `d` is no zero address, and
neither the supply nor `d`'s balance overflows (the conditions of 3Crv's `mint` body). -/
def MintFits (stor : Stor) (pool : Adr) (d v : B256) : Prop :=
  stor.get vyMinterSlot = pool.toB256 ∧ d ≠ 0 ∧ (stor.get vySupplySlot).toNat + v.toNat < 2 ^ 256 ∧
    ((stor.set vySupplySlot (stor.get vySupplySlot + v)).get (mapSlot 3 d)).toNat + v.toNat <
      2 ^ 256

/-- **3Crv accepts `burnFrom(f, v)` from `pool`**: `pool` is the minter, `f` is no zero address,
and `v` is covered by the supply and by `f`'s balance (the conditions of 3Crv's `burnFrom` body). -/
def BurnFits (stor : Stor) (pool : Adr) (f v : B256) : Prop :=
  stor.get vyMinterSlot = pool.toB256 ∧ f ≠ 0 ∧ v ≤ stor.get vySupplySlot ∧
    v ≤ (stor.set vySupplySlot (stor.get vySupplySlot - v)).get (mapSlot 3 f)

theorem adr_toB256_lt (a : Adr) : a.toB256.toNat < 2 ^ 160 := by
  have wordNat : a.toB256.toNat = a.toNat := by
    simp only [B256.toNat, B128.toNat, Adr.toB256, UInt64.toNat_zero, Nat.zero_shiftLeft,
      UInt32.toNat_toUInt64, Nat.zero_or, Adr.toNat]
  rw [wordNat]
  exact Adr.toNat_lt_size a

theorem argWords {e : Sevm} {sel d v : B256}
    (h : e.data = abiSelectorBytes sel ++ d.toBytes ++ v.toBytes) :
    Sevm.argWord e 0 = d ∧ Sevm.argWord e 1 = v ∧ e.data.length = 68 := by
  obtain ⟨h4, h36, hl⟩ := UniswapV2PairWeth9Joint.dataWord_twoWords h
  refine ⟨?_, ?_, hl⟩
  · show Sevm.dataWord e (32 * 0 + 4) = d
    rw [show (32 * 0 + 4 : B256) = 4 by decide]
    exact h4
  · show Sevm.dataWord e (32 * 1 + 4) = v
    rw [show (32 * 1 + 4 : B256) = 36 by decide]
    exact h36

theorem mintSel_eq : mintSel = abiSelectorBytes selMint := by decide
theorem burnFromSel_eq : burnFromSel = abiSelectorBytes selBurnFrom := by decide
theorem totalSupplySel_eq : totalSupplyData = abiSelectorBytes selTotalSupply := by decide

theorem rawMint_of_fits {e : Sevm} {stor : Stor} {d v : B256} (hv : e.value = 0)
    (hdata : e.data = mintSel ++ d.toBytes ++ v.toBytes) (hd : d.toNat < 2 ^ 160)
    (hfits : MintFits stor e.caller d v) :
    rawMint e stor = some (mintStor stor d v, [⟨e.currentTarget, [Curve3Crv.transferTopic, 0, d], v.toBytes⟩],
      some (1 : B256).toBytes) := by
  rw [mintSel_eq] at hdata
  obtain ⟨h0, h1, -⟩ := argWords hdata
  obtain ⟨hmin, hnz, hsup, hbal⟩ := hfits
  unfold rawMint
  simp only [h0, h1]
  rw [ite_eq_left ⟨hv, hd, hmin, hnz, hsup, hbal⟩]
  rfl

theorem rawBurnFrom_of_fits {e : Sevm} {stor : Stor} {f v : B256} (hv : e.value = 0)
    (hdata : e.data = burnFromSel ++ f.toBytes ++ v.toBytes) (hf : f.toNat < 2 ^ 160)
    (hfits : BurnFits stor e.caller f v) :
    rawBurnFrom e stor = some (burnStor stor f v,
      [⟨e.currentTarget, [Curve3Crv.transferTopic, f, 0], v.toBytes⟩], some (1 : B256).toBytes) := by
  rw [burnFromSel_eq] at hdata
  obtain ⟨h0, h1, -⟩ := argWords hdata
  obtain ⟨hmin, hnz, hsup, hbal⟩ := hfits
  unfold rawBurnFrom
  simp only [h0, h1]
  rw [ite_eq_left ⟨hv, hf, hmin, hnz, hsup, hbal⟩]
  rfl

end Accept

/-! ## From a clean child to the premise shapes -/

section Shapes

variable {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes} {U : Nat} {ii is oi : B256}

/-- **A value-`0` `CALL` premise from a clean child**: if at every call-site world the child of
the site's message halts cleanly, within `Cb` gas of the `65000` the site forwards at least,
replying at least 32 bytes, keeping the caller's storage and the code at the identity precompile,
and leaving a world in `W'`, the premise holds with any `U ≥ 70000`. -/
theorem mutCallOkAt_of_child (Cb : Nat) (hCb : Cb ≤ 60000)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hU : 70000 ≤ U)
    (hii : ii.toNat + is.toNat ≤ 4096) (hoi : oi.toNat + (0x20 : B256).toNat ≤ 4096)
    (hchild : ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b →
      (M.read ii.toNat is.toNat).1 = data → 65000 ≤ fwd b S M G t ii is oi 0x20 →
      getDelegatedCodeAddress (b.getCode t.toAdr) = none ∧
      ∃ cpost, exec (initEvm (callMsg0 sevm b S M G t ii is oi 0x20)) = .ok cpost ∧
        cpost.error = none ∧ fwd b S M G t ii is oi 0x20 ≤ cpost.gasLeft + Cb ∧
        cpost.gasLeft ≤ fwd b S M G t ii is oi 0x20 ∧ cpost.output.length = 32 ∧
        Devm.getStor cpost sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
        cpost.getCode 4 = b.getCode 4 ∧
        W' (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat (0x20 : B256).toNat)) :
    MutCallOkAt sevm W W' t data (fun r => 32 ≤ r.length) U ii is oi := by
  intro b S M G hWb hUG hG hin hS
  obtain ⟨hcharge, hfwd⟩ := fwd_ge (b := b) (S := S) (M := M) (t := t) (G := G) (by omega) hii hoi
  obtain ⟨hdel, cpost, hexec, herr, hg1, hg2, hlen, hstor, hcode4, hW'⟩ :=
    hchild b S M G hWb hin hfwd
  have hrun := call0_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
  have he := ext_le (b := b) (S := S) (M := M) hii hoi
  have ha := acc_le (b := b) (t := t)
  have hc := fwd_charge hcharge
  have hgas : (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
      (0x20 : B256).toNat).gasLeft =
      G - (fwd b S M G t ii is oi 0x20 + acc b t + ext b S M ii is oi 0x20) + cpost.gasLeft := rfl
  refine ⟨_, hrun, ?_, ?_, ?_, ?_, ?_, hstor, hW', fun hid => ⟨?_, ?_, hid.pre, hid.fork⟩⟩
  · obtain ⟨flag, hpost⟩ := ri_call_post hfork (Ninst.Run.of_runCompiled hrun)
    have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
      (callChildPost_stack' _ _ _ _))).1
    subst hflag
    exact hpost
  · show 32 ≤ cpost.output.length
    omega
  · rw [callChildPost_returnData', hlen]; decide
  · rw [hgas]; omega
  · rw [hgas]; omega
  · show getDelegatedCodeAddress (cpost.getCode 4) = none
    rw [hcode4]; exact hid.nodeleg
  · exact callChildPost_mem_warm _ _ _ _ 4 (parent_mem_warm b S M G t ii is oi 0x20 4 hid.warm)

/-- **A `STATICCALL` word premise from a clean child** answering the word `A`. -/
theorem staticWordOkAt_of_child {A : B256} (Cb : Nat) (hCb : Cb ≤ 60000)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hU : 70000 ≤ U)
    (hii : ii.toNat + is.toNat ≤ 4096) (hoi : oi.toNat + (0x20 : B256).toNat ≤ 4096)
    (hchild : ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b →
      (M.read ii.toNat is.toNat).1 = data → 65000 ≤ fwd b S M G t ii is oi 0x20 →
      getDelegatedCodeAddress (b.getCode t.toAdr) = none ∧
      ∃ cpost, exec (initEvm (staticMsg sevm b S M G t ii is oi 0x20)) = .ok cpost ∧
        cpost.error = none ∧ fwd b S M G t ii is oi 0x20 ≤ cpost.gasLeft + Cb ∧
        cpost.gasLeft ≤ fwd b S M G t ii is oi 0x20 ∧ cpost.output = A.toBytes ∧
        cpost.getCode 4 = b.getCode 4 ∧
        W' (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat (0x20 : B256).toNat)) :
    StaticWordOkAt sevm W W' t data A U ii is oi := by
  intro b S M G hWb hUG hG hin hS
  obtain ⟨hcharge, hfwd⟩ := fwd_ge (b := b) (S := S) (M := M) (t := t) (G := G) (by omega) hii hoi
  obtain ⟨hdel, cpost, hexec, herr, hg1, hg2, hout, hcode4, hW'⟩ :=
    hchild b S M G hWb hin hfwd
  have hrun := static_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
  have he := ext_le (b := b) (S := S) (M := M) hii hoi
  have ha := acc_le (b := b) (t := t)
  have hc := fwd_charge hcharge
  have hgas : (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
      (0x20 : B256).toNat).gasLeft =
      G - (fwd b S M G t ii is oi 0x20 + acc b t + ext b S M ii is oi 0x20) + cpost.gasLeft := rfl
  obtain ⟨flag, out, hpost, -, -⟩ := ri_staticcall_bounded hfork (Ninst.Run.of_runCompiled hrun)
  have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
    (callChildPost_stack' _ _ _ _))).1
  subst hflag
  have hout' : out = A.toBytes := by
    rw [← hpost.returnData, callChildPost_returnData', hout]
  subst hout'
  refine ⟨_, _, hrun, hpost, ?_, ?_, ?_, ?_, ?_, hW', fun hid => ⟨?_, ?_, hid.pre, hid.fork⟩⟩
  · rw [B256.length_toBytes]
  · rw [B256.length_toBytes]; decide
  · rw [List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes]
  · rw [hgas]; omega
  · rw [hgas]; omega
  · show getDelegatedCodeAddress (cpost.getCode 4) = none
    rw [hcode4]; exact hid.nodeleg
  · exact callChildPost_mem_warm _ _ _ _ 4 (parent_mem_warm b S M G t ii is oi 0x20 4 hid.warm)

end Shapes

/-! ## The 3Crv premises -/

section Premises

open Curve3Crv

variable {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {U : Nat} {ii oi : B256}

/-- **`mint(msg.sender, amt)` into the deployed 3Crv succeeds** at every call-site world where the
token holds 3Crv's code, is not the pool, and 3Crv accepts the mint (`MintFits`). -/
theorem c3crv_mintOkAt {amt : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Curve3Crv.code ∧ t.toAdr ≠ sevm.currentTarget ∧
      MintFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller.toB256 amt)
    (hW' : ∀ b d, W b → (∀ a, a ≠ t.toAdr → Devm.getStor d a = Devm.getStor b a) →
      Devm.getStor d t.toAdr = mintStor (b.getStor t.toAdr) sevm.caller.toB256 amt →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    MintOkAt sevm W W' t amt U ii oi := by
  refine mutCallOkAt_of_child (2119 + 3 * 2100 + 2 * 22100 + dispatchGas 7) (by decide) hfork
    hdepth hprec hU (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii)
    (by rw [show (0x20 : B256).toNat = 0x20 from rfl]; exact hoi) ?_
  intro b S M G hWb hin hfwd
  obtain ⟨hcode, hne, hfits⟩ := hW b hWb
  have hdata : (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)).data =
      mintSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes :=
    (callMsg0_data ..).trans hin
  have hraw := rawMint_of_fits (stor := Devm.getStor (initDevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20))
      (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)).currentTarget)
    (callMsg0_value ..) hdata (adr_toB256_lt _) hfits
  have hfork' : CoveredFork (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)).benvStat.fork :=
    hfork
  have hb := live_mint_le hfork' (by rw [callMsg0_isStatic]; exact hstatic)
    hraw
  have hsel : Sevm.selector (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)) = selMint :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hdata, mintSel_eq, List.append_assoc])
  have hlen := (argWords (by rw [hdata, mintSel_eq])).2.2
  obtain ⟨cpost, hexec, herr, hg1, hg2, hl, hcode'⟩ := c3crv_msg_run (k := 7)
    (by rw [callMsg0_code]; exact hcode) hfork'
    (by rw [callMsg0_codeAddress]; exact Option.some_ne_none _) rfl (by rw [hsel]; rfl)
    (by rw [hlen]; decide) (by rw [hlen]; decide) hb (callMsg0_error ..)
    (by rw [callMsg0_gas]; unfold dispatchGas gCallStipend; omega)
  refine ⟨by rw [hcode]; exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel),
    cpost, hexec, herr, hg1, hg2, ?_, ?_, hcode' 4, ?_⟩
  · rw [hl.output _ rfl, B256.length_toBytes]
  · exact (hl.other _ (Ne.symm hne)).trans (callMsg0_getStor ..)
  · exact hW' b _ hWb (fun a ha => hl.other a ha) hl.stor hcode'

/-- **`burnFrom(msg.sender, amt)` into the deployed 3Crv succeeds** at every call-site world where the
token holds 3Crv's code, is not the pool, and 3Crv accepts the burn (`BurnFits`). -/
theorem c3crv_burnOkAt {amt : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Curve3Crv.code ∧ t.toAdr ≠ sevm.currentTarget ∧
      BurnFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller.toB256 amt)
    (hW' : ∀ b d, W b → (∀ a, a ≠ t.toAdr → Devm.getStor d a = Devm.getStor b a) →
      Devm.getStor d t.toAdr = burnStor (b.getStor t.toAdr) sevm.caller.toB256 amt →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    BurnOkAt sevm W W' t amt U ii oi := by
  refine mutCallOkAt_of_child (2107 + 3 * 2100 + 2 * 22100 + dispatchGas 8) (by decide) hfork
    hdepth hprec hU (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii)
    (by rw [show (0x20 : B256).toNat = 0x20 from rfl]; exact hoi) ?_
  intro b S M G hWb hin hfwd
  obtain ⟨hcode, hne, hfits⟩ := hW b hWb
  have hdata : (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)).data =
      burnFromSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes :=
    (callMsg0_data ..).trans hin
  have hraw := rawBurnFrom_of_fits (stor := Devm.getStor (initDevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20))
      (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)).currentTarget)
    (callMsg0_value ..) hdata (adr_toB256_lt _) hfits
  have hfork' : CoveredFork (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)).benvStat.fork :=
    hfork
  have hb := live_burnFrom_le hfork' (by rw [callMsg0_isStatic]; exact hstatic)
    hraw
  have hsel : Sevm.selector (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)) = selBurnFrom :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hdata, burnFromSel_eq, List.append_assoc])
  have hlen := (argWords (by rw [hdata, burnFromSel_eq])).2.2
  obtain ⟨cpost, hexec, herr, hg1, hg2, hl, hcode'⟩ := c3crv_msg_run (k := 8)
    (by rw [callMsg0_code]; exact hcode) hfork'
    (by rw [callMsg0_codeAddress]; exact Option.some_ne_none _) rfl (by rw [hsel]; rfl)
    (by rw [hlen]; decide) (by rw [hlen]; decide) hb (callMsg0_error ..)
    (by rw [callMsg0_gas]; unfold dispatchGas gCallStipend; omega)
  refine ⟨by rw [hcode]; exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel),
    cpost, hexec, herr, hg1, hg2, ?_, ?_, hcode' 4, ?_⟩
  · rw [hl.output _ rfl, B256.length_toBytes]
  · exact (hl.other _ (Ne.symm hne)).trans (callMsg0_getStor ..)
  · refine hW' b _ hWb (fun a ha => hl.other a ha) ?_ hcode'
    have hs := hl.stor
    rw [callMsg0_currentTarget, callMsg0_getStor] at hs
    show Devm.getStor cpost t.toAdr = _
    rw [hs]

/-- **`totalSupply()` of the deployed 3Crv answers `T`** at every call-site world where the token
holds 3Crv's code and its supply slot holds `T`. -/
theorem c3crv_supplyOkAt {T : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hU : 70000 ≤ U) (hii : ii.toNat + 4 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Curve3Crv.code ∧
      (b.getStor t.toAdr).get vySupplySlot = T)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    SupplyOkAt sevm W W' t T U ii oi := by
  refine staticWordOkAt_of_child (34 + 2100 + dispatchGas 2) (by decide) hfork hdepth hprec hU
    (by rw [show (4 : B256).toNat = 4 from rfl]; exact hii)
    (by rw [show (0x20 : B256).toNat = 0x20 from rfl]; exact hoi) ?_
  intro b S M G hWb hin hfwd
  obtain ⟨hcode, hT⟩ := hW b hWb
  have hdata : (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)).data =
      abiSelectorBytes selTotalSupply ++ [] := by
    rw [staticMsg_data, hin, List.append_nil, totalSupplySel_eq]
  have hfork' : CoveredFork (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)).benvStat.fork :=
    hfork
  have hraw : rawTotalSupply (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20))
      (Devm.getStor (initDevm (staticMsg sevm b S M G t ii 4 oi 0x20))
        (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)).currentTarget) =
      some (Devm.getStor b t.toAdr, [], some ((Devm.getStor b t.toAdr).get vySupplySlot).toBytes) := by
    unfold rawTotalSupply
    rw [ite_eq_left (staticMsg_value ..)]
    rfl
  have hb := live_totalSupply_le hfork' hraw
  have hsel : Sevm.selector (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)) = selTotalSupply :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hdata
  have hlen : (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)).data.length = 4 := by
    rw [hdata]; decide
  obtain ⟨cpost, hexec, herr, hg1, hg2, hl, hcode'⟩ := c3crv_msg_run (k := 2)
    (by rw [staticMsg_code]; exact hcode) hfork'
    (by rw [staticMsg_codeAddress]; exact Option.some_ne_none _) rfl (by rw [hsel]; rfl)
    (by rw [hlen]) (by rw [hlen]; decide) hb (staticMsg_error ..)
    (by rw [staticMsg_gas]; unfold dispatchGas gCallStipend; omega)
  have hstor : ∀ a, Devm.getStor cpost a = Devm.getStor b a := by
    intro a
    by_cases ha : a = t.toAdr
    · subst ha
      exact hl.stor
    · exact hl.other a ha
  refine ⟨by rw [hcode]; exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel),
    cpost, hexec, herr, hg1, hg2, ?_, hcode' 4, hW' b _ hWb hstor hcode'⟩
  rw [hl.output _ rfl, hT]

/-- `remove_liquidity`'s `totalSupply()` window. -/
theorem c3crv_supplyOk {T : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hU : 70000 ≤ U)
    (hW : ∀ b, W b → b.getCode t.toAdr = Curve3Crv.code ∧
      (b.getStor t.toAdr).get vySupplySlot = T)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W d) :
    SupplyOk sevm W t T U :=
  c3crv_supplyOkAt hfork hdepth hprec hU (by decide) (by decide) hW hW'

/-- `remove_liquidity`'s `burnFrom(msg.sender, amt)` window. -/
theorem c3crv_burnOk {amt : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hU : 70000 ≤ U)
    (hW : ∀ b, W b → b.getCode t.toAdr = Curve3Crv.code ∧ t.toAdr ≠ sevm.currentTarget ∧
      BurnFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller.toB256 amt)
    (hW' : ∀ b d, W b → (∀ a, a ≠ t.toAdr → Devm.getStor d a = Devm.getStor b a) →
      Devm.getStor d t.toAdr = burnStor (b.getStor t.toAdr) sevm.caller.toB256 amt →
      (∀ a, d.getCode a = b.getCode a) → W d) :
    BurnOk sevm W t amt U :=
  (c3crv_burnOkAt (ii := 0x61c) (oi := 0x6a0) hfork hstatic hdepth hprec hU (by decide)
    (by decide) hW hW').burnOk

end Premises

end Blanc.Composition.Curve3PoolCalleeLive
