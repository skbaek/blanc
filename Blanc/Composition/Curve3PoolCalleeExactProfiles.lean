import Blanc.Lift.StaticGasTransport
import Blanc.Lift.CallProfileTransport
import Blanc.Lift.Curve3Pool.ExactLivePremises
import Blanc.Composition.Curve3PoolCalleeLive

/-!
# Selected-cost exact profiles for the pool's deployed 3Crv calls

Retain a supplied, proved exact child cost and choose its full canonical
successor from normalized inputs before supplying call gas. Existing bounded profile statements
are retained; the closed-cost exports supply the exact body runs.
-/

namespace Blanc.Composition.Curve3PoolCalleeExactProfiles

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive

private theorem supply_body_certificate :
    Curve3Crv.t_0240_c0.gasFree = true ∧ Curve3Crv.t_0240_c0.refs = [] := by
  decide

private theorem mint_body_certificate :
    Curve3Crv.t_056e_c0.gasFree = true ∧ Curve3Crv.t_056e_c0.refs = [] := by
  decide

private theorem burn_body_certificate :
    Curve3Crv.t_0644_c0.gasFree = true ∧ Curve3Crv.t_0644_c0.refs = [] := by
  decide

open Classical in
/-- The canonical body post: one normalized run at residual `gCallStipend + 1`, gas cleared. -/
noncomputable def bodyCanon (s : Sevm) (b : Devm) (f : SFunc) (c : Nat) : Devm :=
  if h : ∃ post, SFunc.RunExact Curve3Crv.prog s
      (Curve3Crv.entrySt s b (gCallStipend + 1 + c)) f (.halted post) then
    (Classical.choose h).withGasLeft 0
  else b.withGasLeft 0

theorem bodyCanon_gasLeft (s : Sevm) (b : Devm) (f : SFunc) (c : Nat) :
    (bodyCanon s b f c).gasLeft = 0 := by
  unfold bodyCanon
  split <;> rfl

/-- Every same-cost body run, at any static gas and residual, agrees with `bodyCanon`
modulo gas. -/
theorem bodyCanon_spec {s : Sevm} {b : Devm} {f : SFunc} {c : Nat}
    (hsg : s.benvStat.rules.stateGas = none) (hf : f.gasFree = true) (hrefs : f.refs = [])
    (h0 : ∃ post, SFunc.RunExact Curve3Crv.prog s
      (Curve3Crv.entrySt s b (gCallStipend + 1 + c)) f (.halted post))
    {F R : Nat} {post : Devm}
    (hrun : SFunc.RunExact Curve3Crv.prog {s with gas := F}
      (Curve3Crv.entrySt s b (R + c)) f (.halted post)) :
    Devm.EqModGas post (bodyCanon s b f c) := by
  have hrun' : SFunc.RunExact Curve3Crv.prog s (Curve3Crv.entrySt s b (R + c)) f
      (.halted post) := hrun.withStaticGas s.gas
  unfold bodyCanon
  split
  · next h =>
    have he : Outcome.EqModGas (.halted post) (.halted (Classical.choose h)) :=
      SFunc.RunP.eqModGas (fun h => h) (fun h => h) (S := []) (by rfl) hsg hf
        (by rw [hrefs]; rfl) hrun'.toRun (Classical.choose_spec h).toRun
        ((Devm.EqModGas.refl b).st [] _ (R + c) (gCallStipend + 1 + c))
    have hpost : Devm.EqModGas post (Classical.choose h) := he
    exact hpost.trans (Devm.EqModGas.withGasLeft _ 0)
  · next h => exact absurd h0 h

/-- A supplied exact body cost has one full canonical post before either gas parameter. -/
theorem fixed_cost_body
    {s : Sevm} {b : Devm} {f : SFunc} {r : Curve3Crv.Raw}
    (c : Nat)
    (hsg : s.benvStat.rules.stateGas = none)
    (hf : f.gasFree = true) (hrefs : f.refs = [])
    (hbody : ∀ R, gCallStipend < R → ∃ post,
      SFunc.RunExact Curve3Crv.prog s (Curve3Crv.entrySt s b (R + c)) f (.halted post) ∧
      post.gasLeft = R ∧ Curve3Crv.Lands s b post r) :
    ∃ canonical : Devm, canonical.gasLeft = 0 ∧
      ∀ staticGas R, gCallStipend < R → ∃ post,
        SFunc.RunExact Curve3Crv.prog {s with gas := staticGas}
          (Curve3Crv.entrySt s b (R + c)) f (.halted post) ∧
        post.gasLeft = R ∧ Curve3Crv.Lands s b post r ∧
        Devm.EqModGas post canonical := by
  obtain ⟨p0, h0, _, _⟩ := hbody (gCallStipend + 1) (Nat.lt_succ_self _)
  refine ⟨bodyCanon s b f c, bodyCanon_gasLeft s b f c, ?_⟩
  intro staticGas R hR
  obtain ⟨post, hrun, hg, hl⟩ := hbody R hR
  have hs := hrun.withStaticGas staticGas
  exact ⟨post, hs, hg, hl, bodyCanon_spec hsg hf hrefs ⟨p0, h0⟩ hs⟩

/-- A message entering 3Crv's code whose body runs exactly halts cleanly as that body's post,
keeping the code everywhere. -/
private theorem c3crv_msg_exact {msg : Msg} {k : Nat} {f : SFunc} {R : Nat} {post : Devm}
    (hcode : (initSevm msg).code = Curve3Crv.code)
    (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hca : (initSevm msg).codeAddress ≠ none)
    (hf : Curve3Crv.bodies[k]? = some f)
    (hk : Curve3Crv.sels[k]? = some (Sevm.selector (initSevm msg)))
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (herr0 : (initDevm msg).error = none)
    (hgas : R + Curve3Crv.dispatchGas k = msg.gas)
    (hrun : SFunc.RunExact Curve3Crv.prog (initSevm msg)
      (Curve3Crv.entrySt (initSevm msg) (initDevm msg) R) f (.halted post)) :
    exec (initEvm msg) = .ok post ∧ post.error = none ∧
      ∀ a, post.getCode a = (initDevm msg).getCode a := by
  have hd := Curve3Crv.live_dispatch hf hk rfl hlen hcd hrun
  have hst : St (initDevm msg) [] Mem.empty (R + Curve3Crv.dispatchGas k) = initDevm msg := by
    rw [hgas]
    exact (St.self (d := initDevm msg) rfl rfl).symm
  rw [hst] at hd
  obtain ⟨run⟩ := Curve3Crv.exec_of_runExact hcode hfork ⟨_, rfl, hd⟩
  refine ⟨(exec_iff_exec_eq 0 _ _ _).mp ⟨run⟩,
    (Exec.ok_error_eq run hfork.rules_stateGas_none).trans herr0, fun a => ?_⟩
  have keep := (Exec.codeAt_avoid (a := a) run hfork (fun root member hnone => ?_)).1
  · exact keep
  · simp only [Exec.rawFrameRoots, List.mem_cons] at member
    rcases member with rfl | member
    · exact absurd hnone hca
    · exact absurd hnone (Exec.staticOnly_rawFrameDescendants Curve3Crv.cert_check
        Curve3CrvToken.c3crv_cert_staticOnly (root := ⟨0, _, _, _, run⟩) rfl hcode hfork run
        (Exec.Deriv.ParentPrefix.refl _) root member)

/-! ## `totalSupply()`: the exact `STATICCALL` profile -/

section Supply

open Curve3Crv

/-- The supply call's child body cost, at the normalized (gas-zero) call site. -/
def supplyBodyCost (sevm : Sevm) (t ii oi : B256) (b : Devm) (S : List B256) (M : Mem) : Nat :=
  totalSupplyBodyCost (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))
    (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))

/-- The supply call's parent debit: access, expansion, dispatch and body. It excludes the
forwarded grant. -/
def supplyDebit (sevm : Sevm) (t ii oi : B256) (b : Devm) (S : List B256) (M : Mem) : Nat :=
  acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii 4 oi 0x20 +
    (supplyBodyCost sevm t ii oi b S M + dispatchGas 2)

/-- The supply call's full canonical successor, from the normalized call site. -/
noncomputable def supplyNext (sevm : Sevm) (t ii oi : B256) (b : Devm) (S : List B256)
    (M : Mem) : Devm :=
  callChildPost (parent (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)
    (bodyCanon (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))
      (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)) t_0240_c0
      (supplyBodyCost sevm t ii oi b S M))
    oi.toNat (0x20 : B256).toNat

variable {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {U : Nat} {ii oi : B256}

/-- **`totalSupply()` of the deployed 3Crv has an exact profile** at every call window. -/
theorem c3crv_supplyExactAt {T : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hU : 70000 ≤ U) (hii : ii.toNat + 4 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Curve3Crv.code ∧
      (b.getStor t.toAdr).get vySupplySlot = T)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    SupplyExactAt sevm W W' t T U ii oi := by
  refine ⟨supplyDebit sevm t ii oi, supplyNext sevm t ii oi, ?_⟩
  refine { entry_gas := ?_, congr := ?_, sound := ?_ }
  · intros; rfl
  · intro b b' S M h
    unfold supplyDebit supplyNext supplyBodyCost
    rw [h.withGasLeft_eq 0]
    exact ⟨rfl, .refl _⟩
  · rintro b S M G ⟨hWb, hUG, hG, hin, hS⟩
    obtain ⟨hcharge, hfwd⟩ := fwd_ge (b := b) (S := S) (M := M) (t := t) (G := G)
      (ii := ii) (is := 4) (oi := oi) (os := 0x20) (by omega)
      (by rw [show (4 : B256).toNat = 4 from rfl]; exact hii)
      (by rw [show (0x20 : B256).toNat = 0x20 from rfl]; exact hoi)
    obtain ⟨hcode, hT⟩ := hW b hWb
    have hfork0 : CoveredFork
        (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)).benvStat.fork := hfork
    have hraw : rawTotalSupply (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))
        (Devm.getStor (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))
          (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)).currentTarget) =
        some (Devm.getStor b t.toAdr, [],
          some ((Devm.getStor b t.toAdr).get vySupplySlot).toBytes) := by
      unfold rawTotalSupply
      rw [ite_eq_left (staticMsg_value ..)]
      rfl
    have hbody := live_totalSupply_cost hfork0 hraw
    have hcost : supplyBodyCost sevm t ii oi b S M ≤ 34 + 2100 := by
      unfold supplyBodyCost totalSupplyBodyCost
      have := Blanc.sloadCost_le
        (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))
        (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)) vySupplySlot
      have hcs : gasColdSload = 2100 := rfl
      omega
    have hdisp : dispatchGas 2 = 186 := rfl
    obtain ⟨p0, h0, -, -⟩ := hbody (gCallStipend + 1) (Nat.lt_succ_self _)
    obtain ⟨post, hrun, hpg, hl⟩ := hbody
      (fwd b S M G t ii 4 oi 0x20 - (supplyBodyCost sevm t ii oi b S M + dispatchGas 2))
      (by unfold gCallStipend; omega)
    have hrunF := hrun.withStaticGas (fwd b S M G t ii 4 oi 0x20)
    have hrunA : SFunc.RunExact prog (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20))
        (entrySt (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20))
          (initDevm (staticMsg sevm b S M G t ii 4 oi 0x20))
          (fwd b S M G t ii 4 oi 0x20 - (supplyBodyCost sevm t ii oi b S M + dispatchGas 2) +
            supplyBodyCost sevm t ii oi b S M)) t_0240_c0 (.halted post) := hrunF
    have hdata : (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)).data =
        abiSelectorBytes selTotalSupply ++ [] := by
      rw [staticMsg_data, hin, List.append_nil, totalSupplySel_eq]
    have hsel : Sevm.selector (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)) =
        selTotalSupply := selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hdata
    have hlen : (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)).data.length = 4 := by
      rw [hdata]; decide
    obtain ⟨hexec, herr, hcode'⟩ :=
      c3crv_msg_exact (msg := staticMsg sevm b S M G t ii 4 oi 0x20) (k := 2)
      (by rw [staticMsg_code]; exact hcode) hfork
      (by rw [staticMsg_codeAddress]; exact Option.some_ne_none _) rfl (by rw [hsel]; rfl)
      (by rw [hlen]) (by rw [hlen]; decide) (staticMsg_error ..)
      (by rw [staticMsg_gas]; omega) hrunA
    have hdel : getDelegatedCodeAddress (b.getCode t.toAdr) = none := by
      rw [hcode]; exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel)
    have hrunP := static_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
    have he := ext_le (b := b) (S := S) (M := M) (ii := ii) (is := 4) (oi := oi) (os := 0x20)
      (by rw [show (4 : B256).toNat = 4 from rfl]; exact hii)
      (by rw [show (0x20 : B256).toNat = 0x20 from rfl]; exact hoi)
    have ha := acc_le (b := b) (t := t)
    have hfund := fwd_charge hcharge
    have hdebit : supplyDebit sevm t ii oi b S M = acc b t + ext b S M ii 4 oi 0x20 +
        (supplyBodyCost sevm t ii oi b S M + dispatchGas 2) := rfl
    have hgas : (callChildPost (parent b S M G t ii 4 oi 0x20) post oi.toNat
        (0x20 : B256).toNat).gasLeft =
        G - (fwd b S M G t ii 4 oi 0x20 + acc b t + ext b S M ii 4 oi 0x20) + post.gasLeft := rfl
    have hsg0 :
        (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)).benvStat.rules.stateGas =
          none := hfork.rules_stateGas_none
    have hcp := bodyCanon_spec hsg0 supply_body_certificate.1 supply_body_certificate.2
      ⟨p0, h0⟩ hrunF
    have hp : Devm.EqModGas (parent b S M G t ii 4 oi 0x20)
        (parent (b.withGasLeft 0) S M 0 t ii 4 oi 0x20) := by
      apply Devm.EqModGas.of_normalized_eq
      rfl
    have hn : Devm.EqModGas
        (callChildPost (parent b S M G t ii 4 oi 0x20) post oi.toNat (0x20 : B256).toNat)
        (supplyNext sevm t ii oi b S M) := hp.callChildPost hcp _ _
    obtain ⟨flag, out, hpost, -, -⟩ := ri_staticcall_bounded hfork (Ninst.Run.of_runCompiled hrunP)
    have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
      (callChildPost_stack' _ _ _ _))).1
    subst hflag
    have hout' : out = T.toBytes := by
      rw [← hpost.returnData, callChildPost_returnData', hl.output _ rfl, hT]
    subst hout'
    have hstor : ∀ a, Devm.getStor post a = Devm.getStor b a := by
      intro a
      by_cases ha : a = t.toAdr
      · subst ha
        exact hl.stor
      · exact hl.other a ha
    refine ⟨by rw [hdebit]; omega, _, hrunP, by rw [hgas, hdebit, hpg]; omega, hn, T.toBytes,
      hpost, ?_, ?_, ?_, ?_, ?_⟩
    · rw [B256.length_toBytes]
    · rw [B256.length_toBytes]; decide
    · rw [List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes]
    · exact hW' b _ hWb hstor hcode'
    · intro hid
      refine ⟨?_, ?_, hid.pre, hid.fork⟩
      · show getDelegatedCodeAddress (post.getCode 4) = none
        rw [hcode' 4]; exact hid.nodeleg
      · exact callChildPost_mem_warm _ _ _ _ 4
          (parent_mem_warm b S M G t ii 4 oi 0x20 4 hid.warm)

end Supply

/-! ## `mint` and `burnFrom`: exact zero-value `CALL` profiles -/

section Mutable

open Curve3Crv

/-- A mutable 3Crv call's child body cost, at the normalized (gas-zero) call site. -/
def mutBodyCost (cost : Sevm → Devm → Nat) (sevm : Sevm) (t ii oi : B256) (b : Devm)
    (S : List B256) (M : Mem) : Nat :=
  cost (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
    (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))

/-- A mutable 3Crv call's parent debit: access, expansion, dispatch and body. It excludes the
forwarded grant. -/
def mutDebit (cost : Sevm → Devm → Nat) (k : Nat) (sevm : Sevm) (t ii oi : B256) (b : Devm)
    (S : List B256) (M : Mem) : Nat :=
  acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii 0x44 oi 0x20 +
    (mutBodyCost cost sevm t ii oi b S M + dispatchGas k)

/-- A mutable 3Crv call's full canonical successor, from the normalized call site. -/
noncomputable def mutNext (cost : Sevm → Devm → Nat) (f : SFunc) (sevm : Sevm) (t ii oi : B256)
    (b : Devm) (S : List B256) (M : Mem) : Devm :=
  callChildPost (parent (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)
    (bodyCanon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) f
      (mutBodyCost cost sevm t ii oi b S M))
    oi.toNat (0x20 : B256).toNat

variable {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {U : Nat} {ii oi : B256}

/-- A mutable 3Crv body with a closed exact cost gives the exact `CALL` profile. -/
private theorem c3crv_mutExactAt {data : Bytes} {k : Nat} {f : SFunc}
    {cost : Sevm → Devm → Nat} {sel : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hU : 70000 ≤ U) (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hf : Curve3Crv.bodies[k]? = some f) (hk : Curve3Crv.sels[k]? = some sel)
    (hcert : f.gasFree = true ∧ f.refs = [])
    (hcost : ∀ s b, cost s b + dispatchGas k ≤ 60000)
    (hchild : ∀ b S M, W b → (M.read ii.toNat (0x44 : B256).toNat).1 = data →
      b.getCode t.toAdr = Curve3Crv.code ∧
      Sevm.selector (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) = sel ∧
      data.length = 68 ∧ ∃ r : Raw,
      (∀ R, gCallStipend < R → ∃ post,
        SFunc.RunExact prog (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
          (entrySt (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
            (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
            (R + mutBodyCost cost sevm t ii oi b S M)) f (.halted post) ∧
        post.gasLeft = R ∧
        Lands (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
          (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) post r) ∧
      ∀ G d, Lands (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
          (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) d r →
        (∀ a, d.getCode a = b.getCode a) →
        d.output.length = 32 ∧
        Devm.getStor d sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
        W' (callChildPost (parent b S M G t ii 0x44 oi 0x20) d oi.toNat (0x20 : B256).toNat)) :
    MutCallExactAt sevm W W' t data (fun r => 32 ≤ r.length) U ii 0x44 oi := by
  refine ⟨mutDebit cost k sevm t ii oi, mutNext cost f sevm t ii oi, ?_⟩
  refine { entry_gas := ?_, congr := ?_, sound := ?_ }
  · intros; rfl
  · intro b b' S M h
    unfold mutDebit mutNext mutBodyCost
    rw [h.withGasLeft_eq 0]
    exact ⟨rfl, .refl _⟩
  · rintro b S M G ⟨hWb, hUG, hG, hin, hS⟩
    obtain ⟨hcharge, hfwd⟩ := fwd_ge (b := b) (S := S) (M := M) (t := t) (G := G)
      (ii := ii) (is := 0x44) (oi := oi) (os := 0x20) (by omega)
      (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii)
      (by rw [show (0x20 : B256).toNat = 0x20 from rfl]; exact hoi)
    obtain ⟨hcode, hsel, hdlen, r, hbody, hland⟩ := hchild b S M hWb hin
    have hc := hcost (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
    change mutBodyCost cost sevm t ii oi b S M + dispatchGas k ≤ 60000 at hc
    obtain ⟨p0, h0, -, -⟩ := hbody (gCallStipend + 1) (Nat.lt_succ_self _)
    obtain ⟨post, hrun, hpg, hl⟩ := hbody
      (fwd b S M G t ii 0x44 oi 0x20 - (mutBodyCost cost sevm t ii oi b S M + dispatchGas k))
      (by unfold gCallStipend; omega)
    have hrunF := hrun.withStaticGas (fwd b S M G t ii 0x44 oi 0x20)
    have hrunA : SFunc.RunExact prog (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20))
        (entrySt (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20))
          (initDevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20))
          (fwd b S M G t ii 0x44 oi 0x20 - (mutBodyCost cost sevm t ii oi b S M + dispatchGas k) +
            mutBodyCost cost sevm t ii oi b S M)) f (.halted post) := hrunF
    have hlen : (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)).data.length = 68 := by
      rw [callMsg0_data, hin, hdlen]
    obtain ⟨hexec, herr, hcode'⟩ :=
      c3crv_msg_exact (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20) (k := k)
      (by rw [callMsg0_code]; exact hcode) hfork
      (by rw [callMsg0_codeAddress]; exact Option.some_ne_none _) hf
      (by rw [hk]; exact congrArg some hsel.symm)
      (by rw [hlen]; decide) (by rw [hlen]; decide) (callMsg0_error ..)
      (by rw [callMsg0_gas]; omega) hrunA
    have hdel : getDelegatedCodeAddress (b.getCode t.toAdr) = none := by
      rw [hcode]; exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel)
    have hrunP := call0_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
    have he := ext_le (b := b) (S := S) (M := M) (ii := ii) (is := 0x44) (oi := oi) (os := 0x20)
      (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii)
      (by rw [show (0x20 : B256).toNat = 0x20 from rfl]; exact hoi)
    have ha := acc_le (b := b) (t := t)
    have hfund := fwd_charge hcharge
    have hdebit : mutDebit cost k sevm t ii oi b S M = acc b t + ext b S M ii 0x44 oi 0x20 +
        (mutBodyCost cost sevm t ii oi b S M + dispatchGas k) := rfl
    have hgas : (callChildPost (parent b S M G t ii 0x44 oi 0x20) post oi.toNat
        (0x20 : B256).toNat).gasLeft =
        G - (fwd b S M G t ii 0x44 oi 0x20 + acc b t + ext b S M ii 0x44 oi 0x20) +
          post.gasLeft := rfl
    have hsg0 :
        (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)).benvStat.rules.stateGas
          = none := hfork.rules_stateGas_none
    have hcp := bodyCanon_spec hsg0 hcert.1 hcert.2 ⟨p0, h0⟩ hrunF
    have hp : Devm.EqModGas (parent b S M G t ii 0x44 oi 0x20)
        (parent (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20) := by
      apply Devm.EqModGas.of_normalized_eq
      rfl
    have hn : Devm.EqModGas
        (callChildPost (parent b S M G t ii 0x44 oi 0x20) post oi.toNat (0x20 : B256).toNat)
        (mutNext cost f sevm t ii oi b S M) := hp.callChildPost hcp _ _
    obtain ⟨hout, hstor, hW'⟩ := hland G post hl hcode'
    refine ⟨by rw [hdebit]; omega, _, hrunP, by rw [hgas, hdebit, hpg]; omega, hn, ?_,
      by show 32 ≤ post.output.length; omega, ?_, hstor, hW',
      fun hid => ⟨?_, ?_, hid.pre, hid.fork⟩⟩
    · obtain ⟨flag, hpost⟩ := ri_call_post hfork (Ninst.Run.of_runCompiled hrunP)
      have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
        (callChildPost_stack' _ _ _ _))).1
      subst hflag
      exact hpost
    · rw [callChildPost_returnData', hout]; decide
    · show getDelegatedCodeAddress (post.getCode 4) = none
      rw [hcode' 4]; exact hid.nodeleg
    · exact callChildPost_mem_warm _ _ _ _ 4
        (parent_mem_warm b S M G t ii 0x44 oi 0x20 4 hid.warm)

private theorem mintBodyCost_le (s : Sevm) (b : Devm) :
    mintBodyCost s b ≤ 2119 + 3 * 2100 + 2 * 22100 := by
  let d := Sevm.argWord s 0
  let v := Sevm.argWord s 1
  let s2 := mapSlot 3 d
  let b1 := afterSload s b vyMinterSlot
  let sup := b1.getStorVal s.currentTarget vySupplySlot
  let b2 := afterSstore s (afterSload s b1 vySupplySlot) vySupplySlot (sup + v)
  let y := b2.getStorVal s.currentTarget s2
  change 2119 + sloadCost s b vyMinterSlot + sloadCost s b1 vySupplySlot +
    sstoreCost s (afterSload s b1 vySupplySlot) vySupplySlot (sup + v) +
    sloadCost s b2 s2 + sstoreCost s (afterSload s b2 s2) s2 (y + v) ≤ _
  have hcost0 := sstoreCost_le s (afterSload s b2 s2) s2 (y + v)
  have hcost1 := Blanc.sloadCost_le s b2 s2
  have hcost2 := sstoreCost_le s (afterSload s b1 vySupplySlot) vySupplySlot (sup + v)
  have hcost3 := Blanc.sloadCost_le s b1 vySupplySlot
  have hcost4 := Blanc.sloadCost_le s b vyMinterSlot
  have hcs : gasColdSload = 2100 := rfl
  have hss : gasStorageSet = 20000 := rfl
  omega

private theorem burnBodyCost_le (s : Sevm) (b : Devm) :
    burnBodyCost s b ≤ 2107 + 3 * 2100 + 2 * 22100 := by
  let d := Sevm.argWord s 0
  let v := Sevm.argWord s 1
  let s2 := mapSlot 3 d
  let b1 := afterSload s b vyMinterSlot
  let sup := b1.getStorVal s.currentTarget vySupplySlot
  let b2 := afterSstore s (afterSload s b1 vySupplySlot) vySupplySlot (sup - v)
  let y := b2.getStorVal s.currentTarget s2
  change 2107 + sloadCost s b vyMinterSlot + sloadCost s b1 vySupplySlot +
    sstoreCost s (afterSload s b1 vySupplySlot) vySupplySlot (sup - v) +
    sloadCost s b2 s2 + sstoreCost s (afterSload s b2 s2) s2 (y - v) ≤ _
  have hcost0 := sstoreCost_le s (afterSload s b2 s2) s2 (y - v)
  have hcost1 := Blanc.sloadCost_le s b2 s2
  have hcost2 := sstoreCost_le s (afterSload s b1 vySupplySlot) vySupplySlot (sup - v)
  have hcost3 := Blanc.sloadCost_le s b1 vySupplySlot
  have hcost4 := Blanc.sloadCost_le s b vyMinterSlot
  have hcs : gasColdSload = 2100 := rfl
  have hss : gasStorageSet = 20000 := rfl
  omega

/-- **`mint(msg.sender, amt)` into the deployed 3Crv has an exact profile** at every call window
where the token holds 3Crv's code, is not the pool, and 3Crv accepts the mint. -/
theorem c3crv_mintExactAt {amt : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Curve3Crv.code ∧ t.toAdr ≠ sevm.currentTarget ∧
      MintFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller.toB256 amt)
    (hW' : ∀ b d, W b → (∀ a, a ≠ t.toAdr → Devm.getStor d a = Devm.getStor b a) →
      Devm.getStor d t.toAdr = mintStor (b.getStor t.toAdr) sevm.caller.toB256 amt →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    MintExactAt sevm W W' t amt U ii oi := by
  refine c3crv_mutExactAt (k := 7) (cost := mintBodyCost) (sel := selMint) hfork hdepth hprec hU
    hii hoi rfl rfl mint_body_certificate
    (fun s b => by have := mintBodyCost_le s b; unfold dispatchGas; omega) ?_
  intro b S M hWb hin
  obtain ⟨hcode, hne, hfits⟩ := hW b hWb
  have hdata : (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)).data =
      mintSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes :=
    (callMsg0_data ..).trans hin
  have hraw := rawMint_of_fits
    (stor := Devm.getStor (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)).currentTarget)
    (callMsg0_value ..) hdata (adr_toB256_lt _) hfits
  have hlen := (argWords (by rw [hdata, mintSel_eq])).2.2
  refine ⟨hcode, selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hdata, mintSel_eq, List.append_assoc]), by rw [← hdata]; exact hlen, _,
    live_mint_cost (sevm := initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      hfork (by rw [callMsg0_isStatic]; exact hstatic) hraw, ?_⟩
  intro G d hl hcode'
  have hs : Devm.getStor d t.toAdr = mintStor (b.getStor t.toAdr) sevm.caller.toB256 amt := by
    have hs := hl.stor
    rw [callMsg0_currentTarget, callMsg0_getStor,
      show Devm.getStor (b.withGasLeft 0) t.toAdr = Devm.getStor b t.toAdr from rfl] at hs
    rw [hs]
  refine ⟨by rw [hl.output _ rfl, B256.length_toBytes],
    (hl.other _ (Ne.symm hne)).trans (callMsg0_getStor ..),
    hW' b _ hWb (fun a ha => hl.other a ha) hs hcode'⟩

/-- **`burnFrom(msg.sender, amt)` into the deployed 3Crv has an exact profile** at every call
window where the token holds 3Crv's code, is not the pool, and 3Crv accepts the burn. -/
theorem c3crv_burnExactAt {amt : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Curve3Crv.code ∧ t.toAdr ≠ sevm.currentTarget ∧
      BurnFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller.toB256 amt)
    (hW' : ∀ b d, W b → (∀ a, a ≠ t.toAdr → Devm.getStor d a = Devm.getStor b a) →
      Devm.getStor d t.toAdr = burnStor (b.getStor t.toAdr) sevm.caller.toB256 amt →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    BurnExactAt sevm W W' t amt U ii oi := by
  refine c3crv_mutExactAt (k := 8) (cost := burnBodyCost) (sel := selBurnFrom) hfork hdepth
    hprec hU hii hoi rfl rfl burn_body_certificate
    (fun s b => by have := burnBodyCost_le s b; unfold dispatchGas; omega) ?_
  intro b S M hWb hin
  obtain ⟨hcode, hne, hfits⟩ := hW b hWb
  have hdata : (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)).data =
      burnFromSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes :=
    (callMsg0_data ..).trans hin
  have hraw := rawBurnFrom_of_fits
    (stor := Devm.getStor (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)).currentTarget)
    (callMsg0_value ..) hdata (adr_toB256_lt _) hfits
  have hlen := (argWords (by rw [hdata, burnFromSel_eq])).2.2
  refine ⟨hcode, selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hdata, burnFromSel_eq, List.append_assoc]), by rw [← hdata]; exact hlen, _,
    live_burnFrom_cost (sevm := initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      hfork (by rw [callMsg0_isStatic]; exact hstatic) hraw, ?_⟩
  intro G d hl hcode'
  have hs : Devm.getStor d t.toAdr = burnStor (b.getStor t.toAdr) sevm.caller.toB256 amt := by
    have hs := hl.stor
    rw [callMsg0_currentTarget, callMsg0_getStor,
      show Devm.getStor (b.withGasLeft 0) t.toAdr = Devm.getStor b t.toAdr from rfl] at hs
    rw [hs]
  refine ⟨by rw [hl.output _ rfl, B256.length_toBytes],
    (hl.other _ (Ne.symm hne)).trans (callMsg0_getStor ..),
    hW' b _ hWb (fun a ha => hl.other a ha) hs hcode'⟩

end Mutable

end Blanc.Composition.Curve3PoolCalleeExactProfiles
