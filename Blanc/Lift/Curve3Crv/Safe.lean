import Blanc.Lift.Curve3Crv.Lift
import Blanc.Lift.Curve3Crv.SafeBodies
import Blanc.Lift.Curve3Crv.SafeViewBodies
import Blanc.Lift.Curve3Crv.SafeViews
import Blanc.ExecutionFrameEntry

/-!
# The deployed 3Crv runtime refines the model (safety), composed from its segments

Every successful frame execution of the deployed bytes, from a frame start and the storage
abstraction `VyInv … s K`, with the frame-local `FreshKeys` premise for the keys the call touches:

* if the call writes (`set_minter`, `set_name`, `transfer`, `transferFrom`, `approve`, `mint`,
  `burnFrom`), it is exactly the model's `step` on the call `decodeCall` reads: the model
  accepts it (with, for `set_name`, the owner answer the frame's static call to the minter
  returned), the new storage abstracts the model's new state over the extended live keys, other
  accounts' storage is unchanged, the model's events are appended as `LOG3` entries, and the
  return data is the model's;
* otherwise (the six views; a selector miss or short calldata cannot succeed) every storage map
  and the log list are unchanged, the model accepts the call, and the return data is exactly the
  model's ABI-encoded answer (`RetOut`), whatever the enclosing output was.

Route: `lift_sound`; the dispatcher (`safe_dispatch`) hands body `k` its entry state; views by
the kernel-decided quiet sets (`view_world`) and their inversion segments (`safe_totalSupply`,
`safe_allowance`, `safe_name`, `safe_symbol`, `safe_decimals`, `safe_balanceOf`; the string views
use the length bound `VyInv.name`/`symbol` supplies); writers by their inversion segments
(`SafeBodies.lean`); both through the pure refinement (`refine_at`).

`c3crv_writer_nonstatic`: a successful writer frame is never static (`set_minter` and
`set_name` complete an `SSTORE`, `ri_sstore_nonstatic`; the other five append a `LOG3`,
which a static frame cannot, `Exec.logs_eq_of_static_ok`).

`c3crv_frame_refines_raw` keeps Jaune's exact `STOP` output preservation over
an arbitrary base. `c3crv_frame_refines` specializes to empty entry output;
`c3crv_entered_frame_refines` derives that freshness from actual frame entry.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc.Curve3Crv (Call)

/-- A writer's landing and correspondence give the frame's conclusion. -/
theorem writer_post {sevm : Sevm} {pre post : Devm} {K' : Key → Prop} {r : Raw}
    {o : Curve3Crv.Out} (hl : Lands sevm pre post r) (hc : Corr sevm K' r o) :
    VyInv (Devm.getStor post sevm.currentTarget) o.1 K' ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
      post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
      RetOutFrom pre.output post.output o.2.2 := by
  obtain ⟨hinv, hlogs, hret⟩ := hc
  refine ⟨hl.stor ▸ hinv, hl.other, hl.logs.trans (by rw [hlogs]), ?_⟩
  rcases h : r.2.2 with _ | out
  · rw [h] at hret
    simp only [RetMatch] at hret
    rw [hret]
    exact hl.stop_output h
  · rw [h] at hret
    rw [hl.output out h]
    cases hr : o.2.2 <;> simp only [hr, RetMatch, RetOutFrom] at hret ⊢
    · exact hret
    · exact hret
    · exact hret

/-- A view's raw effect always returns bytes. -/
theorem rawOf_view_some {k : Nat} {sevm : Sevm} {ow : Option B256} {stor : Stor} {r : Raw}
    (hk : k ∈ viewKs) (hr : rawOf k sevm ow stor = some r) : ∃ out, r.2.2 = some out := by
  simp only [viewKs, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rawOf, rawTotalSupply, rawAllowance, rawName, rawSymbol, rawDecimals,
      rawBalanceOf] at hr <;>
    split_ifs at hr <;> cases hr <;> exact ⟨_, rfl⟩

/-- A landing that returned bytes matching the model's result returns exactly the model's
answer, whatever the enclosing output was. -/
theorem retOut_of_some {sevm : Sevm} {pre post : Devm} {r : Raw} {o : Curve3Crv.Out}
    {out : Bytes} (hl : Lands sevm pre post r) (hret : RetMatch r.2.2 o.2.2)
    (hs : r.2.2 = some out) : RetOut post.output o.2.2 := by
  rw [hs] at hret
  rw [hl.output out hs]
  cases h : o.2.2 <;> simp only [h, RetMatch, RetOut] at hret ⊢ <;> exact hret

/-- **Raw refinement of the deployed runtime**, retaining exact output over an arbitrary base. -/
theorem c3crv_frame_refines_raw {sevm : Sevm} {pre post : Devm} {s : Curve3Crv.State}
    {K : Key → Prop}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hinv : VyInv (Devm.getStor pre sevm.currentTarget) s K)
    (hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)))
    (exc : Exec 0 sevm pre (.ok post)) :
    (IsWriter (decodeCall sevm) →
      ∃ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) ∧
        ∃ o, Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (decodeCall sevm))) ∧
          (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
          post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
          RetOutFrom pre.output post.output o.2.2) ∧
    (¬ IsWriter (decodeCall sevm) →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs ∧
        ∃ o, Curve3Crv.step (c3ctx sevm none) (decodeCall sevm) s = .ok o ∧
          RetOut post.output o.2.2) := by
  obtain ⟨f0, hf0, run⟩ := lift_sound cert_check hcode hfork exc
  rw [show (Cert.prog cert)[0]? = some t_0000_c0 from rfl] at hf0
  cases hf0
  rw [St.self hstack hmem] at run
  obtain ⟨k, f, sel, G', hk, hs, hsel, hlen, runB⟩ := safe_dispatch hcd run
  have hdec := decodeCall_at hs hsel hlen
  rw [hdec] at hfresh ⊢
  have hk13 : k < 13 := by
    have := (List.getElem?_eq_some_iff.mp hk).1
    simpa [bodies] using this
  set stor := Devm.getStor pre sevm.currentTarget with hstor
  -- a writer, from its landing
  have writer : ∀ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) →
      (∃ r, rawOf k sevm ow stor = some r ∧ Lands sevm pre post r) →
      ∃ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) ∧
        ∃ o, Curve3Crv.step (c3ctx sevm ow) (callAt sevm k) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (callAt sevm k))) ∧
          (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
          post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
          RetOutFrom pre.output post.output o.2.2 := by
    intro ow how ⟨r, hr, hl⟩
    obtain ⟨o, ho, hc⟩ := (refine_at (ow := ow) hk13 hinv hfresh).1 r hr
    exact ⟨ow, how, o, ho, writer_post hl hc⟩
  -- a view, from quietness and its inversion segment
  have view : k ∈ viewKs → (∃ r, rawOf k sevm none stor = some r ∧ Lands sevm pre post r) →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs ∧
        ∃ o, Curve3Crv.step (c3ctx sevm none) (callAt sevm k) s = .ok o ∧
          RetOut post.output o.2.2 := by
    intro hv ⟨r, hr, hl⟩
    have hw := view_world hfork hv hk runB
    obtain ⟨o, ho, hc⟩ := (refine_at (ow := none) hk13 hinv hfresh).1 r hr
    obtain ⟨out, hout⟩ := rawOf_view_some hv hr
    exact ⟨fun a => congrFun hw.1 a, hw.2, o, ho, retOut_of_some hl hc.2.2 hout⟩
  have hLname : (stor.get vyNameBase).toNat ≤ 64 := by
    have h := hinv.name; rw [VyStr] at h; omega
  have hLsym : (stor.get vySymbolBase).toNat ≤ 32 := by
    have h := hinv.symbol; rw [VyStr] at h; omega
  have none_ok : ∀ w, (none : Option B256) = some w → OwnerAnswer sevm pre s.minter w :=
    fun _ h => absurd h (by simp)
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp only [bodies, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hk
  all_goals try subst hk
  · exact ⟨fun _ => writer none none_ok (safe_setMinter hfork G' post runB).2,
      fun h => absurd trivial h⟩
  · refine ⟨fun _ => ?_, fun h => absurd trivial h⟩
    obtain ⟨-, w, hw, r, hr, hl⟩ := safe_setName hfork runB
    have hm : (stor.get vyMinterSlot).toAdr = s.minter := by
      rw [hinv.minter, toAdr_toB256]
    rw [hm] at hw
    exact writer (some w) (fun w' h => by cases h; exact hw) ⟨r, hr, hl⟩
  · exact ⟨fun h => False.elim h,
      fun _ => view (by simp [viewKs]) (safe_totalSupply hfork G' post runB)⟩
  · exact ⟨fun h => False.elim h,
      fun _ => view (by simp [viewKs]) (safe_allowance hfork G' post runB)⟩
  · exact ⟨fun _ => writer none none_ok (safe_transfer hfork G' post runB),
      fun h => absurd trivial h⟩
  · exact ⟨fun _ => writer none none_ok (safe_transferFrom hfork G' post runB),
      fun h => absurd trivial h⟩
  · exact ⟨fun _ => writer none none_ok (safe_approve hfork G' post runB),
      fun h => absurd trivial h⟩
  · exact ⟨fun _ => writer none none_ok (safe_mint hfork G' post runB),
      fun h => absurd trivial h⟩
  · exact ⟨fun _ => writer none none_ok (safe_burnFrom hfork G' post runB),
      fun h => absurd trivial h⟩
  · exact ⟨fun h => False.elim h,
      fun _ => view (by simp [viewKs]) (safe_name hfork hcd hLname G' post runB)⟩
  · exact ⟨fun h => False.elim h,
      fun _ => view (by simp [viewKs]) (safe_symbol hfork hcd hLsym G' post runB)⟩
  · exact ⟨fun h => False.elim h,
      fun _ => view (by simp [viewKs]) (safe_decimals hfork G' post runB)⟩
  · exact ⟨fun h => False.elim h,
      fun _ => view (by simp [viewKs]) (safe_balanceOf hfork G' post runB)⟩

/-- A raw effect that appends a log contradicts an unchanged log list. -/
private theorem lands_logs_nil {sevm : Sevm} {pre post : Devm} {r : Raw}
    (hl : Lands sevm pre post r) (same : post.logs = pre.logs) : r.2.1 = [] := by
  have h := hl.logs
  rw [same] at h
  simpa using h.symm

/-- A guarded raw effect that was produced is the guarded value. -/
private theorem eq_of_ite_some {p : Prop} [Decidable p] {x r : Raw}
    (h : (if p then some x else none) = some r) : r = x := by
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- **Every successful writer frame is non-static.** A successful execution of the deployed
runtime on a writer selector reaches an `SSTORE` (`set_minter`, `set_name`) or a `LOG3` (the
other five), and Jaune halts both with `writeInStaticContext` in a static frame. No storage
abstraction is assumed: the frame's own run decides it. -/
theorem c3crv_writer_nonstatic {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (exc : Exec 0 sevm pre (.ok post)) (hwriter : IsWriter (decodeCall sevm)) :
    sevm.isStatic = false := by
  cases hs : sevm.isStatic with
  | false => rfl
  | true =>
  exfalso
  have same : post.logs = pre.logs := Exec.logs_eq_of_static_ok exc hs hfork post rfl
  obtain ⟨f0, hf0, run⟩ := lift_sound cert_check hcode hfork exc
  rw [show (Cert.prog cert)[0]? = some t_0000_c0 from rfl] at hf0
  cases hf0
  rw [St.self hstack hmem] at run
  obtain ⟨k, f, sel, G', hk, hs', hsel, hlen, runB⟩ := safe_dispatch hcd run
  rw [decodeCall_at hs' hsel hlen] at hwriter
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp only [bodies, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hk
  all_goals try subst hk
  · rw [(safe_setMinter hfork G' post runB).1] at hs; cases hs
  · rw [(safe_setName hfork runB).1] at hs; cases hs
  · exact hwriter
  · exact hwriter
  · obtain ⟨r, hr, hl⟩ := safe_transfer hfork G' post runB
    have := lands_logs_nil hl same
    simp only [rawTransfer] at hr
    rw [eq_of_ite_some hr] at this; cases this
  · obtain ⟨r, hr, hl⟩ := safe_transferFrom hfork G' post runB
    have := lands_logs_nil hl same
    simp only [rawTransferFrom] at hr
    rw [eq_of_ite_some hr] at this; cases this
  · obtain ⟨r, hr, hl⟩ := safe_approve hfork G' post runB
    have := lands_logs_nil hl same
    simp only [rawApprove] at hr
    rw [eq_of_ite_some hr] at this; cases this
  · obtain ⟨r, hr, hl⟩ := safe_mint hfork G' post runB
    have := lands_logs_nil hl same
    simp only [rawMint] at hr
    rw [eq_of_ite_some hr] at this; cases this
  · obtain ⟨r, hr, hl⟩ := safe_burnFrom hfork G' post runB
    have := lands_logs_nil hl same
    simp only [rawBurnFrom] at hr
    rw [eq_of_ite_some hr] at this; cases this
  all_goals exact hwriter

/-- Fresh entry makes the exact raw output relation the model's return bytes. -/
theorem c3crv_frame_refines {sevm : Sevm} {pre post : Devm} {s : Curve3Crv.State}
    {K : Key → Prop}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (houtput : pre.output = [])
    (hinv : VyInv (Devm.getStor pre sevm.currentTarget) s K)
    (hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)))
    (exc : Exec 0 sevm pre (.ok post)) :
    (IsWriter (decodeCall sevm) →
      ∃ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) ∧
        ∃ o, Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (decodeCall sevm))) ∧
          (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
          post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
          RetOut post.output o.2.2) ∧
    (¬ IsWriter (decodeCall sevm) →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs ∧
        ∃ o, Curve3Crv.step (c3ctx sevm none) (decodeCall sevm) s = .ok o ∧
          RetOut post.output o.2.2) := by
  have h := c3crv_frame_refines_raw hcode hfork hcd hstack hmem hinv hfresh exc
  refine ⟨?_, h.2⟩
  intro hw
  obtain ⟨ow, how, o, hok, hinv', hother, hlogs, hret⟩ := h.1 hw
  exact ⟨ow, how, o, hok, hinv', hother, hlogs, hret.of_empty houtput⟩

/-- Refinement from a genuinely entered frame; initialization supplies all
three freshness facts, including empty output, rather than assuming a final result. -/
theorem c3crv_entered_frame_refines {sevm : Sevm} {pre post : Devm} {s : Curve3Crv.State}
    {K : Key → Prop} {frame : Jaune.Frame}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (henter : frame.enter = .run ⟨0, sevm, pre⟩)
    (hinv : VyInv (Devm.getStor pre sevm.currentTarget) s K)
    (hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)))
    (exc : Exec 0 sevm pre (.ok post)) :
    (IsWriter (decodeCall sevm) →
      ∃ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) ∧
        ∃ o, Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (decodeCall sevm))) ∧
          (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
          post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
          RetOut post.output o.2.2) ∧
    (¬ IsWriter (decodeCall sevm) →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs ∧
        ∃ o, Curve3Crv.step (c3ctx sevm none) (decodeCall sevm) s = .ok o ∧
          RetOut post.output o.2.2) := by
  obtain ⟨hstack, hmem⟩ := Frame.enter_run_fresh henter
  exact c3crv_frame_refines hcode hfork hcd hstack hmem
    (Frame.enter_run_output_empty henter) hinv hfresh exc

end Blanc.Lift.Curve3Crv
