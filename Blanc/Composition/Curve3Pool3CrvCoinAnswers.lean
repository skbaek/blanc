import Blanc.Composition.Curve3Pool3CrvCoinCalls
import Blanc.Lift.Curve3Pool.CalldataWords
import Blanc.Composition.UniswapV2PairWeth9SwapLegsCall
import Blanc.StorageAccessGas
import Blanc.CodeDelegation
import Blanc.StorageRefundPotential
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.WalkSteps
import Blanc.Lift.Curve3Pool.Walk.LiveKit

/-!
# U9(b): the coins' answers at the pool's `CALL` sites, from `Token20`'s code

A value-`0` `CALL` from a pool call site into a coin running the synthetic token resumes in
`ccPost` (`cc_cross`); here the resumed parent is read back (`cc_answer`: the caller-visible post,
the reply, the gas, the world) and the child is `Token20`'s gas-exact run, lifted to an execution of
its code (`lift_exact`), so the coins' replies are their code's, not premises.

* `ccExt_le`: the call's two windows inside `[0, 0xc20)` cost at most 309 gas of expansion,
  whatever the memory;
* `ccMsg_data`: the child's calldata is the input window of the caller's memory;
* `pull_child`, `push_child`: `Token20`'s `transferFrom` / `transfer` from a pool call site, for
  any coin, ledger and amount the call fits (`T20PullFits`, `T20MoveFits`), leaving the coin's
  ledger as `t20Move (t20Allow …)` / `t20Move`;
* `token20_coinPullOkAt`, `token20_coinPushOkAt`: the pool's `CoinPullOkAt` / `CoinPushOkAt` at
  any window inside `[0, 0xc20)` and `U ≥ 80000`, over any world invariants closed under what the
  clean child leaves (`CoinLeaves`); `wPull_pullOkAt`, `wPush_pushOkAt` are `exchange`'s instances
  over the capstone's `WPull` / `WPush` / `WCore`.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Composition.Curve3Pool3CrvJoint
open Blanc.Composition.UniswapV2PairWeth9Joint (vcsm_benvStat vcsm_caller vcsm_currentTarget
  vcsm_value vcsm_isStatic vcsm_code vcsm_state vcsm_gasLeft vcsm_stack vcsm_memory vcsm_error
  mem_read_fst callSpawnParent_memory_data addAccessedAddress_setMach_memory)

/-! ## The expansion charge -/

theorem ceilDiv_32_mul (k : Nat) : ceilDiv (32 * k) 32 = k := by
  unfold ceilDiv
  rw [Nat.mul_div_cancel_left _ (by decide), Nat.mul_mod_right, ite_eq_left rfl, Nat.add_zero]

theorem ceilDiv_32_le {n : Nat} (h : n ≤ 3104) : ceilDiv n 32 ≤ 97 := by
  unfold ceilDiv
  split <;> omega

theorem memoryGas_32_mul (k : Nat) :
    calculateMemoryGasCost (32 * k) = 3 * k + k ^ 2 / 512 := by
  unfold calculateMemoryGasCost gMemory
  rw [ceilDiv_32_mul]

/-- **The call's expansion charge is at most 309** when both windows end by `0xc20`. -/
theorem ccExt_le {b : Devm} {S : List B256} {M : Mem} {G : Nat} {ii is oi : B256}
    (his : is.toNat ≠ 0) (hA : ii.toNat + is.toNat ≤ 3104) (hB : oi.toNat + 32 ≤ 3104) :
    ccExt b S M G ii is oi ≤ 309 := by
  unfold ccExt Devm.extCost
  rw [St.memory, show (0x20 : B256).toNat = 32 from rfl]
  simp only [memExtsSize, memExtSize, his, show (32 : Nat) ≠ 0 from by decide, ↓reduceIte,
    ceilDiv_32_mul, memoryGas_32_mul]
  have hw : calculateMemoryGasCost M.size =
      3 * ceilDiv M.size 32 + ceilDiv M.size 32 ^ 2 / 512 := by
    unfold calculateMemoryGasCost gMemory
    rfl
  rw [hw]
  have ha := ceilDiv_32_le hA
  have hb := ceilDiv_32_le hB
  generalize ceilDiv M.size 32 = w at *
  generalize ceilDiv (ii.toNat + is.toNat) 32 = a at *
  generalize ceilDiv (oi.toNat + 32) 32 = c at *
  by_cases hk : max (max w a) c = w
  · rw [hk]
    omega
  · have hle : max (max w a) c ≤ 97 := by omega
    have hsq : max (max w a) c ^ 2 ≤ 9409 :=
      (Nat.pow_le_pow_left hle 2).trans (by decide)
    generalize max (max w a) c = k at *
    generalize k ^ 2 = q at *
    omega

/-! ## The child message -/

/-- The child's calldata is the caller's input window. -/
theorem ccMsg_data (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat)
    (t ii is oi : B256) :
    (initSevm (ccMsg sevm b S M G t ii is oi)).data = (M.read ii.toNat is.toNat).1 := by
  rw [mem_read_fst]
  unfold ccMsg
  change (ccParent b S M G t ii is oi).memory.data.sliceD ii.toNat is.toNat 0 = _
  unfold ccParent ccWarm St
  rw [callSpawnParent_memory_data, addAccessedAddress_setMach_memory]

theorem ccMsg_state (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat)
    (t ii is oi : B256) :
    (initDevm (ccMsg sevm b S M G t ii is oi)).state = b.state := rfl

/-! ## The resumed parent -/

/-- **The resumed parent of a clean child, read back**: the caller-visible post with flag `1`, the
child's output as reply, the gas, the child's world, the warm addresses kept. -/
theorem cc_answer {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {t ii is oi : B256} {cpost : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdel : getDelegatedCodeAddress (b.state.getCode t.toAdr) = none)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hroom : S.length < 1024) (hG : G < 2 ^ 256)
    (hcharge : ccAcc b S M G t + ccExt b S M G ii is oi ≤ G)
    (hexec : exec (initEvm (ccMsg sevm b S M G t ii is oi)) = .ok cpost)
    (herr : cpost.error = none) :
    Ninst.RunCompiled sevm (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G)
        (.exec .call) (ccPost b S M G t ii is oi cpost) ∧
      MutableCallPost b (ccPost b S M G t ii is oi cpost) S M ii is oi 0x20 1 ∧
      (ccPost b S M G t ii is oi cpost).returnData = cpost.output ∧
      (ccPost b S M G t ii is oi cpost).gasLeft =
        G - (ccFwd b S M G t ii is oi + ccAcc b S M G t + ccExt b S M G ii is oi) +
          cpost.gasLeft ∧
      (ccPost b S M G t ii is oi cpost).state = cpost.state ∧
      (∀ a ∈ b.accessedAddresses, a ∈ (ccPost b S M G t ii is oi cpost).accessedAddresses) := by
  have hrun := cc_cross hfork hdel hdepth hprec hroom hG hcharge hexec herr
  have raw : Ninst.Run sevm (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G)
      (.exec .call) (ccPost b S M G t ii is oi cpost) := by
    obtain ⟨xl, filled, step⟩ := hrun
    exact ⟨xl, filled, 0, step 0⟩
  obtain ⟨flag, post⟩ := ri_call_post hfork raw
  have hstack : (ccPost b S M G t ii is oi cpost).stack = 1 :: S := rfl
  have flagOne : flag = 1 := (List.cons.inj (post.stack.symm.trans hstack)).1
  subst flagOne
  refine ⟨hrun, post, rfl, ?_, rfl, ?_⟩
  · change (ccParent b S M G t ii is oi).gasLeft + cpost.gasLeft = _
    rfl
  · intro a ha
    exact Std.HashSet.mem_union_of_left (Std.HashSet.mem_insert.mpr (Or.inr ha))

/-! ## Gas -/

theorem ccAcc_le (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t : B256) :
    ccAcc b S M G t ≤ 2600 := by
  unfold ccAcc accessCost
  split <;> decide

/-- With `80000` gas at the call and an expansion of at most `309`, the child gets at least
`75300`. -/
theorem ccFwd_ge {b : Devm} {S : List B256} {M : Mem} {G : Nat} {t ii is oi : B256}
    (hU : 80000 ≤ G) (hext : ccExt b S M G ii is oi ≤ 309) :
    75300 ≤ ccFwd b S M G t ii is oi := by
  have ha := ccAcc_le b S M G t
  unfold ccFwd except64th
  omega

/-! ## A clean `true` reply at a pool call site -/

/-- `true` passes the pool's reply test. -/
theorem rawCallOk_one : RawCallOk (1 : B256).toBytes := Or.inr (by decide +kernel)

/-- **A coin child that halts cleanly with `true`, charging at most `72918`, answers the pool's
`CALL` within `80000` gas** (`MutCallOkAt`'s conclusion, the world aside). -/
theorem cc_answer_true {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {t ii is oi : B256} {cpost : Devm} {used : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdel : getDelegatedCodeAddress (b.state.getCode t.toAdr) = none)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hroom : S.length < 1024) (hG : G < 2 ^ 256) (hU : 80000 ≤ G)
    (hext : ccExt b S M G ii is oi ≤ 309) (hused : used ≤ 72918)
    (hexec : exec (initEvm (ccMsg sevm b S M G t ii is oi)) = .ok cpost)
    (herr : cpost.error = none) (hout : cpost.output = (1 : B256).toBytes)
    (hgas : cpost.gasLeft = ccFwd b S M G t ii is oi - used) :
    Ninst.RunCompiled sevm (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G)
        (.exec .call) (ccPost b S M G t ii is oi cpost) ∧
      MutableCallPost b (ccPost b S M G t ii is oi cpost) S M ii is oi 0x20 1 ∧
      RawCallOk (ccPost b S M G t ii is oi cpost).returnData ∧
      (ccPost b S M G t ii is oi cpost).returnData.length < 2 ^ 256 ∧
      G ≤ (ccPost b S M G t ii is oi cpost).gasLeft + 80000 ∧
      (ccPost b S M G t ii is oi cpost).gasLeft ≤ G ∧
      (ccPost b S M G t ii is oi cpost).state = cpost.state ∧
      (∀ a ∈ b.accessedAddresses, a ∈ (ccPost b S M G t ii is oi cpost).accessedAddresses) := by
  have ha := ccAcc_le b S M G t
  have hf := ccFwd_ge (t := t) hU hext
  have hfle := cc_fwd_le b S M G t ii is oi
  obtain ⟨hrun, hpost, hret, hgl, hst, hacc⟩ := cc_answer hfork hdel hdepth hprec hroom hG
    (by omega) hexec herr
  rw [hout] at hret
  refine ⟨hrun, hpost, by rw [hret]; exact rawCallOk_one, by rw [hret]; decide +kernel, ?_, ?_, hst,
    hacc⟩
  · rw [hgl, hgas]; omega
  · rw [hgl, hgas]; omega

/-- What a returning tail keeps of its base. -/
theorem retPost_facts (b : Devm) (S : List B256) (M : Mem) (G : Nat) (w : B256) :
    (VyperNonreentrantDeployed.Token20.retPost b S M G w).error = b.error ∧
      (VyperNonreentrantDeployed.Token20.retPost b S M G w).output = w.toBytes ∧
      (VyperNonreentrantDeployed.Token20.retPost b S M G w).gasLeft = G ∧
      (VyperNonreentrantDeployed.Token20.retPost b S M G w).state = b.state :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A first `SSTORE` to a slot of an account not created in the transaction, whose current value is
its snapshot value, does not lower the refund counter. -/
theorem sstore_first_ge {s : Sevm} {d : Devm} {k v : B256} {σ : Stor}
    (hcr : s.currentTarget ∉ d.createdAccounts) (hor : (getOrigAcct s s.currentTarget).stor = σ)
    (hcur : d.getStorVal s.currentTarget k = σ.get k) :
    d.refundCounter ≤ (afterSstore s d k v).refundCounter :=
  afterSstore_refundCounter_ge_of_original_eq_current s d k v (by
    unfold Devm.getOrigStorVal
    rw [ite_eq_right hcr]
    unfold Jaune.getOrigStorVal
    rw [hor, hcur])

theorem retPost_refund_created (b : Devm) (S : List B256) (M : Mem) (G : Nat) (w : B256) :
    (VyperNonreentrantDeployed.Token20.retPost b S M G w).refundCounter = b.refundCounter ∧
      (VyperNonreentrantDeployed.Token20.retPost b S M G w).createdAccounts = b.createdAccounts :=
  ⟨rfl, rfl⟩

/-! ## `Token20`'s ledger after the pool's calls -/

theorem getStor_of_state {d c : Devm} (h : d.state = c.state) (a : Adr) :
    d.getStor a = c.getStor a := by
  unfold Devm.getStor Devm.getAcct
  rw [h]

theorem getCode_of_state {d c : Devm} (h : d.state = c.state) (a : Adr) :
    d.getCode a = c.getCode a := by
  unfold Devm.getCode Devm.getAcct
  rw [h]


open VyperNonreentrantDeployed.Token20 (balSlot allowSlot) in
/-- The ledger `transfer`'s move of `v` from `src` to `dst` leaves (its two writes). -/
def t20Move (σ : Stor) (src dst : Adr) (v : B256) : Stor :=
  (σ.set (balSlot src) (σ.get (balSlot src) - v)).set (balSlot dst)
    (v + (σ.set (balSlot src) (σ.get (balSlot src) - v)).get (balSlot dst))

open VyperNonreentrantDeployed.Token20 (balSlot allowSlot) in
/-- **The move fits**: `src`'s balance covers `v`, and `dst`'s credit does not wrap. -/
def T20MoveFits (σ : Stor) (src dst : Adr) (v : B256) : Prop :=
  v ≤ σ.get (balSlot src) ∧
    v ≤ v + (σ.set (balSlot src) (σ.get (balSlot src) - v)).get (balSlot dst)

open VyperNonreentrantDeployed.Token20 (balSlot allowSlot) in
/-- The ledger after `transferFrom`'s allowance debit (`src`'s allowance to `sp`). -/
def t20Allow (σ : Stor) (src sp : Adr) (v : B256) : Stor :=
  σ.set (allowSlot src sp) (σ.get (allowSlot src sp) - v)

open VyperNonreentrantDeployed.Token20 (balSlot allowSlot) in
/-- **`transferFrom(src, dst, v)` by `sp` fits**: the allowance covers `v`, then the move fits on
the debited ledger. -/
def T20PullFits (σ : Stor) (src sp dst : Adr) (v : B256) : Prop :=
  v ≤ σ.get (allowSlot src sp) ∧ T20MoveFits (t20Allow σ src sp v) src dst v

theorem transferSel_abi : Curve3Pool.transferSel = abiSelectorBytes 0xa9059cbb := by decide
theorem transferFromSel_abi : Curve3Pool.transferFromSel = abiSelectorBytes 0x23b872dd := by
  decide
theorem balanceOfSel_abi : Curve3Pool.balanceOfSel = abiSelectorBytes 0x70a08231 := by decide

/-! ## A coin's `transferFrom(src, pool, v)` from a pool call site -/

section Pull

open VyperNonreentrantDeployed.Token20 (tfFrom tfTo tfVal tfAllow tf1 tf2 mvFrom mvTo mv1 mv2 mv3 mv4
  mvCost transferFromGas transferFromBase transferFromPost transferFrom_runExact cert_check
  cert_jumpsOk balSlot allowSlot)

/-- What `transferFrom`'s halting machine keeps of its base. -/
theorem tfPost_facts (s : Sevm) (p : Devm) (G : Nat) :
    (transferFromPost s p G).error = (transferFromBase s p).error ∧
      (transferFromPost s p G).output = (1 : B256).toBytes ∧
      (transferFromPost s p G).gasLeft = G ∧
      (transferFromPost s p G).state = (transferFromBase s p).state := by
  unfold transferFromPost
  exact retPost_facts _ _ _ _ _

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {t ii oi : B256}

/-- **A coin running `Token20` answers the pool's `transferFrom(src, pool, v)` cleanly**: from a
pool call site whose input window holds the call's data, when the pull fits the coin's ledger
(`T20PullFits`), the child halts with `true`, charging at most `72918`, writing only the coin's
storage (as `t20Move (t20Allow …)`), creating nothing; its refund counter is nonnegative when the
coin is untouched in the transaction and the three slots it writes are distinct. -/
theorem pull_child (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {c src : Adr} {v : B256} (ht : t.toAdr = c)
    (hcode : b.state.getCode c = VyperNonreentrantDeployed.Token20.code)
    (hdata : (M.read ii.toNat (0x64 : B256).toNat).1 = Curve3Pool.transferFromSel ++
      src.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ v.toBytes)
    (hfits : T20PullFits (b.getStor c) src sevm.currentTarget sevm.currentTarget v)
    (hfwd : 75300 ≤ ccFwd b S M G t ii 0x64 oi) :
    ∃ cpost used, exec (initEvm (ccMsg sevm b S M G t ii 0x64 oi)) = .ok cpost ∧
      cpost.error = none ∧ cpost.output = (1 : B256).toBytes ∧
      cpost.gasLeft = ccFwd b S M G t ii 0x64 oi - used ∧ used ≤ 72918 ∧
      (∀ a, cpost.getCode a = b.getCode a) ∧
      (∀ a, a ≠ c → cpost.getStor a = b.getStor a) ∧
      cpost.getStor c = t20Move (t20Allow (b.getStor c) src sevm.currentTarget v) src
        sevm.currentTarget v ∧
      cpost.createdAccounts = b.createdAccounts ∧
      ((getOrigAcct sevm c).stor = b.getStor c → c ∉ b.createdAccounts →
        allowSlot src sevm.currentTarget ≠ balSlot src →
        allowSlot src sevm.currentTarget ≠ balSlot sevm.currentTarget →
        balSlot src ≠ balSlot sevm.currentTarget → 0 ≤ cpost.refundCounter) := by
  generalize hmsg : ccMsg sevm b S M G t ii 0x64 oi = msg
  have hcC : (initSevm msg).code = VyperNonreentrantDeployed.Token20.code := by
    rw [← hmsg, ← hcode, ← ht]; rfl
  have hfC : CoveredFork (initSevm msg).benvStat.fork := by rw [← hmsg]; exact hfork
  have hsC : (initSevm msg).isStatic = false := by
    rw [← hmsg]; show (false || sevm.isStatic) = false; rw [hstatic]; rfl
  have hct : (initSevm msg).currentTarget = c := by rw [← hmsg, ← ht]; rfl
  have hcl : (initSevm msg).caller = sevm.currentTarget := by rw [← hmsg]; rfl
  have hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ v.toBytes := by
    rw [← hmsg, ccMsg_data, hdata, transferFromSel_abi]
  have hgl : (initDevm msg).gasLeft = ccFwd b S M G t ii 0x64 oi := by rw [← hmsg]; rfl
  have hgs : (initDevm msg).getStor c = b.getStor c := by rw [← hmsg]; rfl
  have hget : ∀ k, (initDevm msg).getStorVal c k = (b.getStor c).get k := by
    intro k
    rw [← hgs]
    rfl
  have hsel : Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  obtain ⟨w4, w36, w68⟩ := Blanc.Lift.Curve3Pool.cc_dataWord_threeWords hd
  have hfrom : tfFrom (initSevm msg) = src := by unfold tfFrom; rw [w4, toAdr_toB256]
  have hto : tfTo (initSevm msg) = sevm.currentTarget := by unfold tfTo; rw [w36, toAdr_toB256]
  have hval : tfVal (initSevm msg) = v := w68
  -- the reads
  have hal : tfAllow (initSevm msg) (initDevm msg) = (b.getStor c).get (allowSlot src
      sevm.currentTarget) := by
    unfold tfAllow; rw [hct, hget, hfrom, hcl]
  have hs2 : Devm.getStor (tf2 (initSevm msg) (initDevm msg)) c =
      t20Allow (b.getStor c) src sevm.currentTarget v := by
    unfold tf2
    rw [← hct, afterSstore_getStor_self, hct, hal, hval, hfrom, hcl]
    unfold tf1
    rw [afterSload_getStor, hgs]
    rfl
  have hfromBal : mvFrom (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
      (tfFrom (initSevm msg)) = (t20Allow (b.getStor c) src sevm.currentTarget v).get
        (balSlot src) := by
    unfold mvFrom
    rw [getStorVal_eq_getStor, hct, hs2, hfrom]
  have hs3 : Devm.getStor (mv2 (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
      (tfFrom (initSevm msg)) (tfVal (initSevm msg))) c =
      (t20Allow (b.getStor c) src sevm.currentTarget v).set (balSlot src)
        ((t20Allow (b.getStor c) src sevm.currentTarget v).get (balSlot src) - v) := by
    unfold mv2
    rw [← hct, afterSstore_getStor_self, hct, hfromBal, hval, hfrom]
    unfold mv1
    rw [afterSload_getStor, hs2]
  have htoBal : mvTo (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg))
      (tfTo (initSevm msg)) (tfVal (initSevm msg)) =
      ((t20Allow (b.getStor c) src sevm.currentTarget v).set (balSlot src)
        ((t20Allow (b.getStor c) src sevm.currentTarget v).get (balSlot src) - v)).get
        (balSlot sevm.currentTarget) := by
    unfold mvTo
    rw [getStorVal_eq_getStor, hct, hs3, hto]
  have hs4 : Devm.getStor (transferFromBase (initSevm msg) (initDevm msg)) c =
      t20Move (t20Allow (b.getStor c) src sevm.currentTarget v) src sevm.currentTarget v := by
    unfold transferFromBase mv4
    rw [← hct, afterSstore_getStor_self, hct]
    unfold mv3
    rw [afterSload_getStor, hs3, htoBal, hval, hto]
    rfl
  -- the charge
  have hused : transferFromGas (initSevm msg) (initDevm msg) ≤ 72918 := by
    unfold transferFromGas mvCost
    have := Lift.Curve3Pool.sstoreCost_le_22100 (initSevm msg) (mv3 (initSevm msg)
      (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg)) (tfTo (initSevm msg))
      (tfVal (initSevm msg))) (balSlot (tfTo (initSevm msg)))
      (tfVal (initSevm msg) + mvTo (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
        (tfFrom (initSevm msg)) (tfTo (initSevm msg)) (tfVal (initSevm msg)))
    have := Lift.Curve3Pool.sstoreCost_le_22100 (initSevm msg) (mv1 (initSevm msg)
      (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg)))
      (balSlot (tfFrom (initSevm msg)))
      (mvFrom (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg)) -
        tfVal (initSevm msg))
    have := Lift.Curve3Pool.sstoreCost_le_22100 (initSevm msg) (tf1 (initSevm msg) (initDevm msg))
      (allowSlot (tfFrom (initSevm msg)) (initSevm msg).caller)
      (tfAllow (initSevm msg) (initDevm msg) - tfVal (initSevm msg))
    have := sloadCost_le (initSevm msg) (mv2 (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
      (tfFrom (initSevm msg)) (tfVal (initSevm msg))) (balSlot (tfTo (initSevm msg)))
    have := sloadCost_le (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
      (balSlot (tfFrom (initSevm msg)))
    have := sloadCost_le (initSevm msg) (initDevm msg)
      (allowSlot (tfFrom (initSevm msg)) (initSevm msg).caller)
    unfold gasColdSload at *
    omega
  obtain ⟨fa, fm, fn⟩ := hfits
  have run := transferFrom_runExact (pre := initDevm msg) (G := ccFwd b S M G t ii 0x64 oi -
      transferFromGas (initSevm msg) (initDevm msg)) hfC hsC hsel (by rw [← hmsg]; rfl)
    (by rw [← hmsg]; rfl) (by rw [hgl]; omega) (by unfold gCallStipend; omega)
    (by rw [hal, hval]; exact fa) (by rw [hfromBal, hval]; exact fm)
    (by rw [htoBal, hval]; exact fn)
  have hexec := (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok _)).mp
    (lift_exact cert_check cert_jumpsOk hcC hfC run)
  obtain ⟨pe, po, pg, ps⟩ := tfPost_facts (initSevm msg) (initDevm msg)
    (ccFwd b S M G t ii 0x64 oi - transferFromGas (initSevm msg) (initDevm msg))
  have c1 := afterSload_createdAccounts (initSevm msg) (initDevm msg)
    (allowSlot (tfFrom (initSevm msg)) (initSevm msg).caller)
  have c2 := (afterSstore_createdAccounts (initSevm msg) (tf1 (initSevm msg) (initDevm msg))
    (allowSlot (tfFrom (initSevm msg)) (initSevm msg).caller)
    (tfAllow (initSevm msg) (initDevm msg) - tfVal (initSevm msg))).trans c1
  have c3 := (afterSload_createdAccounts (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
    (balSlot (tfFrom (initSevm msg)))).trans c2
  have c4 := (afterSstore_createdAccounts (initSevm msg)
    (mv1 (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg)))
    (balSlot (tfFrom (initSevm msg)))
    (mvFrom (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg)) -
      tfVal (initSevm msg))).trans c3
  have c5 := (afterSload_createdAccounts (initSevm msg)
    (mv2 (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg))
      (tfVal (initSevm msg)))
    (balSlot (tfTo (initSevm msg)))).trans c4
  have c6 := (afterSstore_createdAccounts (initSevm msg)
    (mv3 (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg))
      (tfTo (initSevm msg)) (tfVal (initSevm msg)))
    (balSlot (tfTo (initSevm msg)))
    (tfVal (initSevm msg) + mvTo (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
      (tfFrom (initSevm msg)) (tfTo (initSevm msg)) (tfVal (initSevm msg)))).trans c5
  obtain ⟨pr, pc⟩ := retPost_refund_created (transferFromBase (initSevm msg) (initDevm msg))
    [tfVal (initSevm msg), (tfTo (initSevm msg)).toB256, (tfFrom (initSevm msg)).toB256,
      Sevm.selector (initSevm msg)]
    (VyperNonreentrantDeployed.Token20.okMem (VyperNonreentrantDeployed.Token20.scratch
      (tfFrom (initSevm msg)).toB256 (initSevm msg).caller.toB256))
    (ccFwd b S M G t ii 0x64 oi - transferFromGas (initSevm msg) (initDevm msg)) 1
  refine ⟨transferFromPost (initSevm msg) (initDevm msg)
      (ccFwd b S M G t ii 0x64 oi - transferFromGas (initSevm msg) (initDevm msg)),
    transferFromGas (initSevm msg) (initDevm msg), hexec, ?_, po, pg, hused, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pe]
    unfold transferFromBase mv4 mv3 mv2 mv1 tf2 tf1
    rw [afterSstore_error, afterSload_error, afterSstore_error, afterSload_error, afterSstore_error,
      afterSload_error, ← hmsg]
    rfl
  · intro a
    unfold Devm.getCode Devm.getAcct
    rw [ps]
    change (transferFromBase (initSevm msg) (initDevm msg)).getCode a = _
    unfold transferFromBase mv4 mv3 mv2 mv1 tf2 tf1
    rw [afterSstore_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode,
      afterSstore_getCode, afterSload_getCode, ← hmsg]
    rfl
  · intro a ha
    have hne : (initSevm msg).currentTarget ≠ a := by rw [hct]; exact Ne.symm ha
    unfold Devm.getStor Devm.getAcct
    rw [ps]
    change Devm.getStor (transferFromBase (initSevm msg) (initDevm msg)) a = _
    unfold transferFromBase mv4 mv3 mv2 mv1 tf2 tf1
    rw [afterSstore_getStor_ne _ _ _ _ _ hne, afterSload_getStor, afterSstore_getStor_ne _ _ _ _ _ hne,
      afterSload_getStor, afterSstore_getStor_ne _ _ _ _ _ hne, afterSload_getStor, ← hmsg]
    rfl
  · rw [getStor_of_state ps]
    exact hs4
  · change (VyperNonreentrantDeployed.Token20.retPost _ _ _ _ _).createdAccounts = _
    rw [pc]
    unfold transferFromBase mv4
    rw [c6, ← hmsg]
    rfl
  · intro horig hcr hd1 hd2 hd3
    have hcrC : (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts := by
      rw [hct, ← hmsg]; exact hcr
    have horC : (getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor = b.getStor c := by
      rw [hct, ← hmsg]; exact horig
    have r2 : (tf1 (initSevm msg) (initDevm msg)).refundCounter ≤
        (tf2 (initSevm msg) (initDevm msg)).refundCounter :=
      sstore_first_ge (by unfold tf1; rw [c1]; exact hcrC) horC (by
        unfold tf1; rw [getStorVal_afterSload, hct]; exact hget _)
    have r4 : (mv1 (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
          (tfFrom (initSevm msg))).refundCounter ≤
        (mv2 (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg))
          (tfVal (initSevm msg))).refundCounter :=
      sstore_first_ge (by unfold mv1; rw [c3]; exact hcrC) horC (by
        unfold mv1; rw [getStorVal_afterSload]
        show mvFrom (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg)) = _
        rw [hfromBal, hfrom]
        unfold t20Allow
        rw [Stor.get_set_ne _ hd1])
    have r6 : (mv3 (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg))
          (tfTo (initSevm msg)) (tfVal (initSevm msg))).refundCounter ≤
        (transferFromBase (initSevm msg) (initDevm msg)).refundCounter :=
      sstore_first_ge (by unfold mv3; rw [c5]; exact hcrC) horC (by
        unfold mv3; rw [getStorVal_afterSload]
        show mvTo (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg))
          (tfTo (initSevm msg)) (tfVal (initSevm msg)) = _
        rw [htoBal, hto, Stor.get_set_ne _ hd3]
        unfold t20Allow
        rw [Stor.get_set_ne _ hd2])
    have r1 : (tf1 (initSevm msg) (initDevm msg)).refundCounter = 0 := by
      unfold tf1; rw [afterSload_refundCounter, ← hmsg]; rfl
    have r3 := afterSload_refundCounter (sevm := initSevm msg)
      (b := tf2 (initSevm msg) (initDevm msg)) (key := balSlot (tfFrom (initSevm msg)))
    have r5 := afterSload_refundCounter (sevm := initSevm msg)
      (b := mv2 (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg))
        (tfVal (initSevm msg)))
      (key := balSlot (tfTo (initSevm msg)))
    change 0 ≤ (VyperNonreentrantDeployed.Token20.retPost _ _ _ _ _).refundCounter
    rw [pr]
    calc (0 : Int) = (tf1 (initSevm msg) (initDevm msg)).refundCounter := r1.symm
      _ ≤ (tf2 (initSevm msg) (initDevm msg)).refundCounter := r2
      _ = (mv1 (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
            (tfFrom (initSevm msg))).refundCounter := r3.symm
      _ ≤ (mv2 (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg))
            (tfVal (initSevm msg))).refundCounter := r4
      _ = (mv3 (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg))
            (tfTo (initSevm msg)) (tfVal (initSevm msg))).refundCounter := r5.symm
      _ ≤ _ := r6

end Pull

/-! ## A coin's `transfer(dst, v)` from a pool call site -/

section Push

open VyperNonreentrantDeployed.Token20 (trTo trVal mvFrom mvTo mv1 mv2 mv3 mv4 mvCost transferGas
  transferBase transferPost transfer_runExact cert_check cert_jumpsOk balSlot)

/-- What `transfer`'s halting machine keeps of its base. -/
theorem trPost_facts (s : Sevm) (p : Devm) (G : Nat) :
    (transferPost s p G).error = (transferBase s p).error ∧
      (transferPost s p G).output = (1 : B256).toBytes ∧
      (transferPost s p G).gasLeft = G ∧
      (transferPost s p G).state = (transferBase s p).state := by
  unfold transferPost
  exact retPost_facts _ _ _ _ _

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {t ii oi : B256}

/-- **A coin running `Token20` answers the pool's `transfer(dst, v)` cleanly**: from a pool call
site whose input window holds the call's data, when the move from the pool fits the coin's ledger
(`T20MoveFits`), the child halts with `true`, charging at most `72918`, writing only the coin's
storage (as `t20Move`), creating nothing; its refund counter is nonnegative when the coin is
untouched in the transaction and the two balance slots differ. -/
theorem push_child (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {c dst : Adr} {v : B256} (ht : t.toAdr = c)
    (hcode : b.state.getCode c = VyperNonreentrantDeployed.Token20.code)
    (hdata : (M.read ii.toNat (0x44 : B256).toNat).1 =
      Curve3Pool.transferSel ++ dst.toB256.toBytes ++ v.toBytes)
    (hfits : T20MoveFits (b.getStor c) sevm.currentTarget dst v)
    (hfwd : 75300 ≤ ccFwd b S M G t ii 0x44 oi) :
    ∃ cpost used, exec (initEvm (ccMsg sevm b S M G t ii 0x44 oi)) = .ok cpost ∧
      cpost.error = none ∧ cpost.output = (1 : B256).toBytes ∧
      cpost.gasLeft = ccFwd b S M G t ii 0x44 oi - used ∧ used ≤ 72918 ∧
      (∀ a, cpost.getCode a = b.getCode a) ∧
      (∀ a, a ≠ c → cpost.getStor a = b.getStor a) ∧
      cpost.getStor c = t20Move (b.getStor c) sevm.currentTarget dst v ∧
      cpost.createdAccounts = b.createdAccounts ∧
      ((getOrigAcct sevm c).stor = b.getStor c → c ∉ b.createdAccounts →
        balSlot sevm.currentTarget ≠ balSlot dst → 0 ≤ cpost.refundCounter) := by
  generalize hmsg : ccMsg sevm b S M G t ii 0x44 oi = msg
  have hcC : (initSevm msg).code = VyperNonreentrantDeployed.Token20.code := by
    rw [← hmsg, ← hcode, ← ht]; rfl
  have hfC : CoveredFork (initSevm msg).benvStat.fork := by rw [← hmsg]; exact hfork
  have hsC : (initSevm msg).isStatic = false := by
    rw [← hmsg]; show (false || sevm.isStatic) = false; rw [hstatic]; rfl
  have hct : (initSevm msg).currentTarget = c := by rw [← hmsg, ← ht]; rfl
  have hcl : (initSevm msg).caller = sevm.currentTarget := by rw [← hmsg]; rfl
  have hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++
      v.toBytes := by
    rw [← hmsg, ccMsg_data, hdata, transferSel_abi]
  have hgl : (initDevm msg).gasLeft = ccFwd b S M G t ii 0x44 oi := by rw [← hmsg]; rfl
  have hgs : (initDevm msg).getStor c = b.getStor c := by rw [← hmsg]; rfl
  have hget : ∀ k, (initDevm msg).getStorVal c k = (b.getStor c).get k := by
    intro k
    rw [← hgs]
    rfl
  have hsel : Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨w4, w36, -⟩ := UniswapV2PairWeth9Joint.dataWord_twoWords hd
  have hto : trTo (initSevm msg) = dst := by unfold trTo; rw [w4, toAdr_toB256]
  have hval : trVal (initSevm msg) = v := w36
  have hfromBal : mvFrom (initSevm msg) (initDevm msg) (initSevm msg).caller =
      (b.getStor c).get (balSlot sevm.currentTarget) := by
    unfold mvFrom
    rw [hct, hget, hcl]
  have hs2 : Devm.getStor (mv2 (initSevm msg) (initDevm msg) (initSevm msg).caller
      (trVal (initSevm msg))) c = (b.getStor c).set (balSlot sevm.currentTarget)
        ((b.getStor c).get (balSlot sevm.currentTarget) - v) := by
    unfold mv2
    rw [← hct, afterSstore_getStor_self, hct, hfromBal, hval, hcl]
    unfold mv1
    rw [afterSload_getStor, hgs]
  have htoBal : mvTo (initSevm msg) (initDevm msg) (initSevm msg).caller (trTo (initSevm msg))
      (trVal (initSevm msg)) = ((b.getStor c).set (balSlot sevm.currentTarget)
        ((b.getStor c).get (balSlot sevm.currentTarget) - v)).get (balSlot dst) := by
    unfold mvTo
    rw [getStorVal_eq_getStor, hct, hs2, hto]
  have hs4 : Devm.getStor (transferBase (initSevm msg) (initDevm msg)) c =
      t20Move (b.getStor c) sevm.currentTarget dst v := by
    unfold transferBase mv4
    rw [← hct, afterSstore_getStor_self, hct]
    unfold mv3
    rw [afterSload_getStor, hs2, htoBal, hval, hto]
    rfl
  have hused : transferGas (initSevm msg) (initDevm msg) ≤ 72918 := by
    unfold transferGas mvCost
    have := Lift.Curve3Pool.sstoreCost_le_22100 (initSevm msg) (mv3 (initSevm msg) (initDevm msg)
      (initSevm msg).caller (trTo (initSevm msg)) (trVal (initSevm msg)))
      (balSlot (trTo (initSevm msg)))
      (trVal (initSevm msg) + mvTo (initSevm msg) (initDevm msg) (initSevm msg).caller
        (trTo (initSevm msg)) (trVal (initSevm msg)))
    have := Lift.Curve3Pool.sstoreCost_le_22100 (initSevm msg) (mv1 (initSevm msg) (initDevm msg)
      (initSevm msg).caller) (balSlot (initSevm msg).caller)
      (mvFrom (initSevm msg) (initDevm msg) (initSevm msg).caller - trVal (initSevm msg))
    have := sloadCost_le (initSevm msg) (mv2 (initSevm msg) (initDevm msg) (initSevm msg).caller
      (trVal (initSevm msg))) (balSlot (trTo (initSevm msg)))
    have := sloadCost_le (initSevm msg) (initDevm msg) (balSlot (initSevm msg).caller)
    unfold gasColdSload at *
    omega
  obtain ⟨fm, fn⟩ := hfits
  have run := transfer_runExact (pre := initDevm msg) (G := ccFwd b S M G t ii 0x44 oi -
      transferGas (initSevm msg) (initDevm msg)) hfC hsC hsel (by rw [← hmsg]; rfl)
    (by rw [← hmsg]; rfl) (by rw [hgl]; omega) (by unfold gCallStipend; omega)
    (by rw [hfromBal, hval]; exact fm) (by rw [htoBal, hval]; exact fn)
  have hexec := (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok _)).mp
    (lift_exact cert_check cert_jumpsOk hcC hfC run)
  obtain ⟨pe, po, pg, ps⟩ := trPost_facts (initSevm msg) (initDevm msg)
    (ccFwd b S M G t ii 0x44 oi - transferGas (initSevm msg) (initDevm msg))
  have c1 := afterSload_createdAccounts (initSevm msg) (initDevm msg)
    (balSlot (initSevm msg).caller)
  have c2 := (afterSstore_createdAccounts (initSevm msg)
    (mv1 (initSevm msg) (initDevm msg) (initSevm msg).caller)
    (balSlot (initSevm msg).caller)
    (mvFrom (initSevm msg) (initDevm msg) (initSevm msg).caller - trVal (initSevm msg))).trans c1
  have c3 := (afterSload_createdAccounts (initSevm msg)
    (mv2 (initSevm msg) (initDevm msg) (initSevm msg).caller (trVal (initSevm msg)))
    (balSlot (trTo (initSevm msg)))).trans c2
  have c4 := (afterSstore_createdAccounts (initSevm msg)
    (mv3 (initSevm msg) (initDevm msg) (initSevm msg).caller (trTo (initSevm msg))
      (trVal (initSevm msg)))
    (balSlot (trTo (initSevm msg)))
    (trVal (initSevm msg) + mvTo (initSevm msg) (initDevm msg) (initSevm msg).caller
      (trTo (initSevm msg)) (trVal (initSevm msg)))).trans c3
  obtain ⟨pr, pc⟩ := retPost_refund_created (transferBase (initSevm msg) (initDevm msg))
    [trVal (initSevm msg), (trTo (initSevm msg)).toB256, (initSevm msg).caller.toB256,
      Sevm.selector (initSevm msg)]
    (VyperNonreentrantDeployed.Token20.okMem Mem.empty)
    (ccFwd b S M G t ii 0x44 oi - transferGas (initSevm msg) (initDevm msg)) 1
  refine ⟨transferPost (initSevm msg) (initDevm msg)
      (ccFwd b S M G t ii 0x44 oi - transferGas (initSevm msg) (initDevm msg)),
    transferGas (initSevm msg) (initDevm msg), hexec, ?_, po, pg, hused, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pe]
    unfold transferBase mv4 mv3 mv2 mv1
    rw [afterSstore_error, afterSload_error, afterSstore_error, afterSload_error, ← hmsg]
    rfl
  · intro a
    unfold Devm.getCode Devm.getAcct
    rw [ps]
    change (transferBase (initSevm msg) (initDevm msg)).getCode a = _
    unfold transferBase mv4 mv3 mv2 mv1
    rw [afterSstore_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode, ← hmsg]
    rfl
  · intro a ha
    have hne : (initSevm msg).currentTarget ≠ a := by rw [hct]; exact Ne.symm ha
    unfold Devm.getStor Devm.getAcct
    rw [ps]
    change Devm.getStor (transferBase (initSevm msg) (initDevm msg)) a = _
    unfold transferBase mv4 mv3 mv2 mv1
    rw [afterSstore_getStor_ne _ _ _ _ _ hne, afterSload_getStor, afterSstore_getStor_ne _ _ _ _ _ hne,
      afterSload_getStor, ← hmsg]
    rfl
  · rw [getStor_of_state ps]
    exact hs4
  · change (VyperNonreentrantDeployed.Token20.retPost _ _ _ _ _).createdAccounts = _
    rw [pc]
    unfold transferBase mv4
    rw [c4, ← hmsg]
    rfl
  · intro horig hcr hd1
    have hcrC : (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts := by
      rw [hct, ← hmsg]; exact hcr
    have horC : (getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor = b.getStor c := by
      rw [hct, ← hmsg]; exact horig
    have r2 : (mv1 (initSevm msg) (initDevm msg) (initSevm msg).caller).refundCounter ≤
        (mv2 (initSevm msg) (initDevm msg) (initSevm msg).caller
          (trVal (initSevm msg))).refundCounter :=
      sstore_first_ge (by unfold mv1; rw [c1]; exact hcrC) horC (by
        unfold mv1; rw [getStorVal_afterSload]
        show mvFrom (initSevm msg) (initDevm msg) (initSevm msg).caller = _
        rw [hfromBal, hcl])
    have r4 : (mv3 (initSevm msg) (initDevm msg) (initSevm msg).caller (trTo (initSevm msg))
          (trVal (initSevm msg))).refundCounter ≤
        (transferBase (initSevm msg) (initDevm msg)).refundCounter :=
      sstore_first_ge (by unfold mv3; rw [c3]; exact hcrC) horC (by
        unfold mv3; rw [getStorVal_afterSload]
        show mvTo (initSevm msg) (initDevm msg) (initSevm msg).caller (trTo (initSevm msg))
          (trVal (initSevm msg)) = _
        rw [htoBal, hto, Stor.get_set_ne _ hd1])
    have r1 : (mv1 (initSevm msg) (initDevm msg) (initSevm msg).caller).refundCounter = 0 := by
      unfold mv1; rw [afterSload_refundCounter, ← hmsg]; rfl
    have r3 := afterSload_refundCounter (sevm := initSevm msg)
      (b := mv2 (initSevm msg) (initDevm msg) (initSevm msg).caller (trVal (initSevm msg)))
      (key := balSlot (trTo (initSevm msg)))
    change 0 ≤ (VyperNonreentrantDeployed.Token20.retPost _ _ _ _ _).refundCounter
    rw [pr]
    calc (0 : Int) = (mv1 (initSevm msg) (initDevm msg) (initSevm msg).caller).refundCounter :=
          r1.symm
      _ ≤ (mv2 (initSevm msg) (initDevm msg) (initSevm msg).caller
            (trVal (initSevm msg))).refundCounter := r2
      _ = (mv3 (initSevm msg) (initDevm msg) (initSevm msg).caller (trTo (initSevm msg))
            (trVal (initSevm msg))).refundCounter := r3.symm
      _ ≤ _ := r4

end Push

/-! ## The coins' premises, from `Token20`'s code

`token20_coinPullOkAt` and `token20_coinPushOkAt` discharge the pool's `CoinPullOkAt` /
`CoinPushOkAt` at any call window inside `[0, 0xc20)` and any gas bound `U ≥ 80000`, for a coin
holding `Token20`, over any world invariants `W` (where the call fits the coin's ledger) and `W'`
(closed under what the clean child leaves, `CoinLeaves`). -/

/-- **What a clean coin child leaves**: every code kept, every storage but the coin's `c` kept, the
coin's storage `σ'`, the error flag and the created accounts kept, and the refund counter not
lowered when `R` holds. -/
structure CoinLeaves (c : Adr) (σ' : Stor) (R : Prop) (b d : Devm) : Prop where
  code : ∀ a, d.getCode a = b.getCode a
  other : ∀ a, a ≠ c → d.getStor a = b.getStor a
  stor : d.getStor c = σ'
  error : d.error = b.error
  created : d.createdAccounts = b.createdAccounts
  refund : R → b.refundCounter ≤ d.refundCounter

theorem token20_undelegated :
    getDelegatedCodeAddress VyperNonreentrantDeployed.Token20.code = none :=
  getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel)

/-- A non-precompile, as the crossing states it. -/
theorem prec_false {p : Prop} (h : ¬ p) : p = (false = true) :=
  propext ⟨fun hp => absurd hp h, fun hf => absurd hf Bool.false_ne_true⟩

theorem idReady_of_child {sevm : Sevm} {b d : Devm} (hcode : d.getCode 4 = b.getCode 4)
    (hacc : ∀ a ∈ b.accessedAddresses, a ∈ d.accessedAddresses) (h : IdReady sevm b) :
    IdReady sevm d :=
  ⟨by rw [hcode]; exact h.nodeleg, hacc _ h.warm, h.pre, h.fork⟩

theorem ccPost_error (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256)
    (c : Devm) : (ccPost b S M G t ii is oi c).error = b.error := rfl

theorem ccPost_refund (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256)
    (c : Devm) :
    (ccPost b S M G t ii is oi c).refundCounter = b.refundCounter + c.refundCounter := rfl

theorem ccPost_created (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256)
    (c : Devm) : (ccPost b S M G t ii is oi c).createdAccounts = c.createdAccounts := rfl

section Premises

open VyperNonreentrantDeployed.Token20 (balSlot allowSlot)

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {c : Adr} {U : Nat} {ii oi : B256}

/-- **A coin answers the pool's pull from `Token20`'s code** (`CoinPullOkAt` at any window inside
`[0, 0xc20)`): wherever the pull fits the coin's ledger, `Token20`'s actual `transferFrom` run
answers it. -/
theorem token20_coinPullOkAt (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp c) (ht : t.toAdr = c) (hne : c ≠ sevm.currentTarget)
    (hU : 80000 ≤ U) (hii : ii.toNat + 0x64 ≤ 3104) (hoi : oi.toNat + 32 ≤ 3104)
    (hW : ∀ b, W b → b.getCode c = VyperNonreentrantDeployed.Token20.code ∧
      T20PullFits (b.getStor c) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves c (t20Move (t20Allow (b.getStor c) sevm.caller
        sevm.currentTarget amt) sevm.caller sevm.currentTarget amt)
      ((getOrigAcct sevm c).stor = b.getStor c ∧ c ∉ b.createdAccounts ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.caller ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.currentTarget ∧
        balSlot sevm.caller ≠ balSlot sevm.currentTarget) b d → W' d) :
    Curve3Pool.CoinPullOkAt sevm W W' t amt U ii oi := by
  intro b S M G hW0 hUG hG hin hS
  obtain ⟨hc, hfits⟩ := hW b hW0
  have hext : ccExt b S M G ii 0x64 oi ≤ 309 :=
    ccExt_le (by decide) (by rw [show (0x64 : B256).toNat = 0x64 from rfl]; exact hii) hoi
  have hfwd := ccFwd_ge (t := t) (by omega) hext
  obtain ⟨cpost, used, hexec, herr, hout, hgas, hused, hcode, hstor, hs, hcr, hrf⟩ :=
    pull_child hfork hstatic ht hc hin hfits hfwd
  obtain ⟨hrun, hpost, hok, hlen, hg1, hg2, hst, hacc⟩ := cc_answer_true hfork
    (by rw [ht, show b.state.getCode c = b.getCode c from rfl, hc]; exact token20_undelegated)
    hdepth (by rw [ht]; exact prec_false hprec) hS hG (by omega) hext hused hexec herr hout hgas
  refine ⟨_, hrun, hpost, hok, hlen, by omega, hg2,
    by rw [getStor_of_state hst, hstor _ (Ne.symm hne)], hW' b _ hW0 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    idReady_of_child (by rw [getCode_of_state hst, hcode]) hacc⟩
  · intro a; rw [getCode_of_state hst, hcode]
  · intro a ha; rw [getStor_of_state hst, hstor a ha]
  · rw [getStor_of_state hst, hs]
  · exact ccPost_error ..
  · exact (ccPost_created ..).trans hcr
  · rintro ⟨h1, h2, h3, h4, h5⟩
    rw [ccPost_refund]
    have := hrf h1 h2 h3 h4 h5
    omega

/-- **A coin answers the pool's push from `Token20`'s code** (`CoinPushOkAt` at any window inside
`[0, 0xc20)`): wherever the transfer to the caller fits the coin's ledger, `Token20`'s actual
`transfer` run answers it. -/
theorem token20_coinPushOkAt (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp c) (ht : t.toAdr = c) (hne : c ≠ sevm.currentTarget)
    (hU : 80000 ≤ U) (hii : ii.toNat + 0x44 ≤ 3104) (hoi : oi.toNat + 32 ≤ 3104)
    (hW : ∀ b, W b → b.getCode c = VyperNonreentrantDeployed.Token20.code ∧
      T20MoveFits (b.getStor c) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves c (t20Move (b.getStor c) sevm.currentTarget sevm.caller amt)
      ((getOrigAcct sevm c).stor = b.getStor c ∧ c ∉ b.createdAccounts ∧
        balSlot sevm.currentTarget ≠ balSlot sevm.caller) b d → W' d) :
    Curve3Pool.CoinPushOkAt sevm W W' t amt U ii oi := by
  intro b S M G hW0 hUG hG hin hS
  obtain ⟨hc, hfits⟩ := hW b hW0
  have hext : ccExt b S M G ii 0x44 oi ≤ 309 :=
    ccExt_le (by decide) (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii) hoi
  have hfwd := ccFwd_ge (t := t) (by omega) hext
  obtain ⟨cpost, used, hexec, herr, hout, hgas, hused, hcode, hstor, hs, hcr, hrf⟩ :=
    push_child hfork hstatic ht hc hin hfits hfwd
  obtain ⟨hrun, hpost, hok, hlen, hg1, hg2, hst, hacc⟩ := cc_answer_true hfork
    (by rw [ht, show b.state.getCode c = b.getCode c from rfl, hc]; exact token20_undelegated)
    hdepth (by rw [ht]; exact prec_false hprec) hS hG (by omega) hext hused hexec herr hout hgas
  refine ⟨_, hrun, hpost, hok, hlen, by omega, hg2,
    by rw [getStor_of_state hst, hstor _ (Ne.symm hne)], hW' b _ hW0 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    idReady_of_child (by rw [getCode_of_state hst, hcode]) hacc⟩
  · intro a; rw [getCode_of_state hst, hcode]
  · intro a ha; rw [getStor_of_state hst, hstor a ha]
  · rw [getStor_of_state hst, hs]
  · exact ccPost_error ..
  · exact (ccPost_created ..).trans hcr
  · rintro ⟨h1, h2, h3⟩
    rw [ccPost_refund]
    have := hrf h1 h2 h3
    omega

end Premises

/-! ## The coins' premises for `exchange(0, 1, 100, 0)`

The world invariants share a core (`WCore`): no error, none of the pool and the two coins created
in the transaction, and a nonnegative refund potential at the pool (`refundPotential`, over the
keys of its synthetic storage) — what the transaction needs of the frame's post.  Before the pull
(`WPull`) both coins also hold `Token20` over their synthetic ledgers; after it (`WPush`) coin 1
still does; after the push the core alone is kept. -/

/-- The keys of the synthetic pool storage. -/
def poolKeys : Finset B256 := (Std.TreeMap.keys (cmp := compare) poolStor).toFinset

theorem poolStor_get_of_not_mem {x : B256} (h : x ∉ poolKeys) : poolStor.get x = 0 := by
  unfold Stor.get
  exact Std.TreeMap.getD_eq_fallback
    (fun hm => h (List.mem_toFinset.mpr (Std.TreeMap.mem_keys.mpr hm)))

/-- The core of the world invariants. -/
def WCore (sevm : Sevm) (b : Devm) : Prop :=
  b.error = none ∧ poolAddr ∉ b.createdAccounts ∧ coin0Addr ∉ b.createdAccounts ∧
    coin1Addr ∉ b.createdAccounts ∧ 0 ≤ refundPotential sevm b poolAddr poolKeys

/-- The world before the pull. -/
def WPull (sevm : Sevm) (b : Devm) : Prop :=
  b.getCode coin0Addr = VyperNonreentrantDeployed.Token20.code ∧
    b.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code ∧
    b.getStor coin0Addr = coin0Stor ∧ b.getStor coin1Addr = coin1Stor ∧ WCore sevm b

/-- The world after the pull. -/
def WPush (sevm : Sevm) (b : Devm) : Prop :=
  b.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code ∧ b.getStor coin1Addr = coin1Stor ∧
    WCore sevm b

/-- A clean coin child keeps the core when its refund condition holds: it writes only its coin's
storage, creates nothing, and does not lower the refund counter. -/
theorem wCore_leaves {sevm : Sevm} {c : Adr} {σ' : Stor} {R : Prop} {b d : Devm}
    (h : WCore sevm b) (hl : CoinLeaves c σ' R b d) (hc : c ≠ poolAddr) (hR : R) :
    WCore sevm d := by
  obtain ⟨he, hp, h0, h1, hpot⟩ := h
  refine ⟨hl.error.trans he, by rw [hl.created]; exact hp, by rw [hl.created]; exact h0,
    by rw [hl.created]; exact h1, ?_⟩
  have hr := hl.refund hR
  rw [refundPotential_add (x := d.refundCounter - b.refundCounter) (by omega) hl.created
    (hl.other _ (Ne.symm hc))]
  omega

/-- **Coin 0 answers `exchange`'s pull** over `WPull`/`WPush`: `token20_coinPullOkAt` at the
synthetic ledger. -/
theorem wPull_pullOkAt {sevm : Sevm} {t : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hcaller : sevm.caller = trader)
    (htarget : sevm.currentTarget = poolAddr)
    (horig : (getOrigAcct sevm coin0Addr).stor = coin0Stor)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp coin0Addr) (ht : t.toAdr = coin0Addr) :
    Curve3Pool.CoinPullOkAt sevm (WPull sevm) (WPush sevm) t (Nat.toB256 exchangeDx) 80000
      0x600 0x6c0 := by
  refine token20_coinPullOkAt hfork hstatic hdepth hprec ht (by rw [htarget]; decide +kernel)
    (le_refl _) (by decide) (by decide) (fun b hb => ⟨hb.1, ?_⟩) (fun b d hb hl => ?_)
  · rw [hb.2.2.1, hcaller, htarget]
    unfold T20PullFits T20MoveFits t20Allow
    decide +kernel
  · obtain ⟨c0, c1, s0, s1, hcore⟩ := hb
    refine ⟨by rw [hl.code]; exact c1, by rw [hl.other _ (by decide +kernel)]; exact s1,
      wCore_leaves hcore hl (by decide +kernel) ⟨by rw [horig, s0], hcore.2.2.1, ?_⟩⟩
    rw [hcaller, htarget]
    decide +kernel

/-- **Coin 1 answers `exchange`'s push** of `132` from `WPush` into `WCore`. -/
theorem wPush_pushOkAt {sevm : Sevm} {t : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hcaller : sevm.caller = trader)
    (htarget : sevm.currentTarget = poolAddr)
    (horig : (getOrigAcct sevm coin1Addr).stor = coin1Stor)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp coin1Addr) (ht : t.toAdr = coin1Addr) :
    Curve3Pool.CoinPushOkAt sevm (WPush sevm) (WCore sevm) t 132 80000 0xb60 0xc00 := by
  refine token20_coinPushOkAt hfork hstatic hdepth hprec ht (by rw [htarget]; decide +kernel)
    (le_refl _) (by decide) (by decide) (fun b hb => ⟨hb.1, ?_⟩) (fun b d hb hl => ?_)
  · rw [hb.2.1, hcaller, htarget]
    unfold T20MoveFits
    decide +kernel
  · obtain ⟨c1, s1, hcore⟩ := hb
    refine wCore_leaves hcore hl (by decide +kernel) ⟨by rw [horig, s1], hcore.2.2.2.1, ?_⟩
    rw [hcaller, htarget]
    decide +kernel

section Closed

variable {sevm : Sevm}

/-- The pool's snapshot storage is zero off `poolKeys`, as an `SSTORE` sentry reads it. -/
theorem pool_hK (horig : (getOrigAcct sevm poolAddr).stor = poolStor) {b : Devm}
    (hcr : poolAddr ∉ b.createdAccounts) :
    ∀ x, x ∉ poolKeys → b.getOrigStorVal sevm poolAddr x = 0 := by
  intro x hx
  unfold Devm.getOrigStorVal
  rw [ite_eq_right hcr]
  unfold Jaune.getOrigStorVal
  rw [horig]
  exact poolStor_get_of_not_mem hx

/-- `WCore` survives the pool's own steps. -/
theorem wCore_closed (htarget : sevm.currentTarget = poolAddr)
    (horig : (getOrigAcct sevm poolAddr).stor = poolStor) :
    Curve3Pool.WClosed sevm (WCore sevm) where
  st _ _ _ _ h := h
  sload b k h := by
    obtain ⟨he, hp, h0, h1, hpot⟩ := h
    have hc := afterSload_createdAccounts sevm b k
    refine ⟨by rw [afterSload_error]; exact he, by rw [hc]; exact hp, by rw [hc]; exact h0,
      by rw [hc]; exact h1, ?_⟩
    rw [refundPotential_congr afterSload_refundCounter hc (afterSload_getStor sevm b k poolAddr)]
    exact hpot
  sstore b k v h := by
    obtain ⟨he, hp, h0, h1, hpot⟩ := h
    have hc := afterSstore_createdAccounts sevm b k v
    refine ⟨by rw [afterSstore_error]; exact he, by rw [hc]; exact hp, by rw [hc]; exact h0,
      by rw [hc]; exact h1, ?_⟩
    have hmono := refundPotential_afterSstore (sevm := sevm) (b := b) (K := poolKeys) (k := k)
      (v := v) (by rw [htarget]; exact pool_hK horig hp)
    rw [htarget] at hmono
    exact hpot.trans hmono
  sha b b' rd hp h := by
    obtain ⟨he, hpl, h0, h1, hpot⟩ := h
    refine ⟨by rw [hp.error]; exact he, by rw [hp.created]; exact hpl, by rw [hp.created]; exact h0,
      by rw [hp.created]; exact h1, ?_⟩
    rw [refundPotential_congr hp.refund hp.created (hp.stor poolAddr)]
    exact hpot
  log _ _ h := h

/-- `WPull` survives the pool's own steps. -/
theorem wPull_closed (htarget : sevm.currentTarget = poolAddr)
    (horig : (getOrigAcct sevm poolAddr).stor = poolStor) :
    Curve3Pool.WClosed sevm (WPull sevm) where
  st b S M G h := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, (wCore_closed htarget horig).st b S M G h.2.2.2.2⟩
  sload b k h := by
    obtain ⟨c0, c1, s0, s1, hc⟩ := h
    refine ⟨by rw [afterSload_getCode]; exact c0, by rw [afterSload_getCode]; exact c1,
      by rw [afterSload_getStor]; exact s0, by rw [afterSload_getStor]; exact s1,
      (wCore_closed htarget horig).sload b k hc⟩
  sstore b k v h := by
    obtain ⟨c0, c1, s0, s1, hc⟩ := h
    refine ⟨by rw [afterSstore_getCode]; exact c0, by rw [afterSstore_getCode]; exact c1,
      by rw [afterSstore_getStor_ne _ _ _ _ _ (by rw [htarget]; decide +kernel)]; exact s0,
      by rw [afterSstore_getStor_ne _ _ _ _ _ (by rw [htarget]; decide +kernel)]; exact s1,
      (wCore_closed htarget horig).sstore b k v hc⟩
  sha b b' rd hp h := by
    obtain ⟨c0, c1, s0, s1, hc⟩ := h
    refine ⟨by rw [hp.code]; exact c0, by rw [hp.code]; exact c1, by rw [hp.stor]; exact s0,
      by rw [hp.stor]; exact s1, (wCore_closed htarget horig).sha b b' rd hp hc⟩
  log _ _ h := h

/-- `WPush` survives the pool's own steps. -/
theorem wPush_closed (htarget : sevm.currentTarget = poolAddr)
    (horig : (getOrigAcct sevm poolAddr).stor = poolStor) :
    Curve3Pool.WClosed sevm (WPush sevm) where
  st b S M G h := ⟨h.1, h.2.1, (wCore_closed htarget horig).st b S M G h.2.2⟩
  sload b k h := by
    obtain ⟨c1, s1, hc⟩ := h
    refine ⟨by rw [afterSload_getCode]; exact c1, by rw [afterSload_getStor]; exact s1,
      (wCore_closed htarget horig).sload b k hc⟩
  sstore b k v h := by
    obtain ⟨c1, s1, hc⟩ := h
    refine ⟨by rw [afterSstore_getCode]; exact c1,
      by rw [afterSstore_getStor_ne _ _ _ _ _ (by rw [htarget]; decide +kernel)]; exact s1,
      (wCore_closed htarget horig).sstore b k v hc⟩
  sha b b' rd hp h := by
    obtain ⟨c1, s1, hc⟩ := h
    refine ⟨by rw [hp.code]; exact c1, by rw [hp.stor]; exact s1,
      (wCore_closed htarget horig).sha b b' rd hp hc⟩
  log _ _ h := h

end Closed

end Blanc.Composition.Curve3Pool3CrvInstance
