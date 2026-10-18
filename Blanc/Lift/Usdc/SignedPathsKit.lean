import Blanc.Lift.Usdc.SignedSites
import Blanc.Lift.Usdc.RefineSignedPermit
import Blanc.Lift.Usdc.RefineSignedAuth
import Blanc.Lift.InvWalkDispatch

/-!
# F7b kit: walking the USDC signed paths under a site step relation

The signed walks of U6e (`RefineSignedAuth*`, `RefineSignedPermit*`) invert plain cut runs and
forget the step relation.  The site lemmas of F7a (`SignedSites.lean`) need the run at the site
node under a `SiteStep` relation.  This module gives the pieces of a re-walk that keeps the
relation: the walk tactics (`sxx`, `brP`, `dispP`), entering an internal call, crossing the
silent callees of the signed paths (entries 78, 79, 83, 110, 112), and the entry preamble.
Everything takes `hP : SiteStep P`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.FreePtr

set_option hygiene false in
/-- One straight-line step of a site walk, also over `SHL`, `MUL`, `CALLDATACOPY`, `TIMESTAMP`. -/
macro "sxx " h:ident : tactic => `(tactic| first
  | sx $h
  | sop $h => ri_shl
  | sop $h => ri_mul
  | sop $h => ri_calldatacopy
  | sop $h => ri_timestamp)

/-- A conditional jump of a site walk: the arm that cannot succeed closes. -/
macro "brP " h:ident : tactic => `(tactic|
  (have h' := ric_branchP $h; clear $h; rcases h' with ⟨_, _, $h⟩ | ⟨_, _, $h⟩ <;>
    try (exact (SFunc.RunCutP.false_of_noOk $h (by decide)).elim)))

set_option hygiene false in
/-- One comparison of the dispatcher's binary search on a known selector, in a site walk. -/
macro "dispP " h:ident : tactic => `(tactic| first
  | (have h' := ric_cmp_gtP (fun hh => (hP hh).1) $h; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (replace $h:ident := RunCut.ite_left (by decide) $h)
     | (replace $h:ident := RunCut.ite_right (by decide) $h))
  | (have h' := ric_cmp_eqP (fun hh => (hP hh).1) List.not_mem_nil rfl $h; clear $h
     obtain ⟨_, $h:ident⟩ := h'
     first
     | (replace $h:ident := RunCut.ite_left (by decide) $h)
     | (replace $h:ident := RunCut.ite_right (by decide) $h))
  | (have h' := ric_destP $h; clear $h; obtain ⟨_, $h:ident⟩ := h'))

variable {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {C : List Nat} {b : Devm}
  {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {r : Seg}

/-- **Into a callee**: a cut run through `callNext k` contains a run of entry `k` from the
caller's machine with the return address popped. -/
theorem ricP_enter {fs : List SFunc} {k : Nat} {g : SFunc} {dd : B256} (hk : fs[k]? = some g)
    (run : SFunc.RunCutP P fs sevm C (St b (dd :: S) M G) (.callNext k f) r) :
    ∃ G' o, SFunc.RunCutP P fs sevm [] (St b S M G') g (.done o) := by
  cases run with
  | callHalt d hget pop callee =>
    rw [hk] at hget
    cases hget
    rw [(St.of_pop1 pop).2] at callee
    exact ⟨_, _, SFunc.runP_iff_runCutP_nil.mp callee⟩
  | callRet d hget pop callee _ =>
    rw [hk] at hget
    cases hget
    rw [(St.of_pop1 pop).2] at callee
    exact ⟨_, _, SFunc.runP_iff_runCutP_nil.mp callee⟩

/-- Enter the callee of the `callNext k` that `h` runs into. -/
macro "enterP " h:ident k:num : tactic => `(tactic|
  (have h' := ricP_enter (k := $k) rfl $h; clear $h; obtain ⟨_, _, $h:ident⟩ := h'))

/-- Crossing `notBlacklisted`'s check (entry 83, frame `[_, ret]`, one return word). -/
theorem skipP_83 (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {dd x ρ : B256}
    (run : SFunc.RunCutP P Impl.cert.prog sevm C (St b (dd :: x :: ρ :: S) M G) (.callNext 83 f) r) :
    ∃ b' y M' G', b'.state = b.state ∧ SFunc.RunCutP P Impl.cert.prog sevm C (St b' (y :: S) M' G') f r := by
  obtain ⟨b', Y, M', G', hs, hlen, run⟩ := ricP_call_silent (fun h => (hP h).1) Impl.cert_check
    hfork auth_silent auth_noHalt (k := 83) (by decide) (by decide) (e := ⟨0x3f6a, [.unk, .ret], 1⟩)
    rfl rfl (ρ := ρ) run (List.Forall₂.cons trivial (.cons rfl .nil))
  obtain ⟨y, rfl⟩ : ∃ y, Y = [y] := match Y, hlen with | [y], _ => ⟨y, rfl⟩
  exact ⟨b', y, M', G', hs, run⟩

/-- Crossing `_requireValidAuthorization` (entry 112, frame `[_, _, _, _, ret]`). -/
theorem skipP_112 (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork)
    {dd x0 x1 x2 x3 ρ : B256}
    (run : SFunc.RunCutP P Impl.cert.prog sevm C (St b (dd :: x0 :: x1 :: x2 :: x3 :: ρ :: S) M G)
      (.callNext 112 f) r) :
    ∃ b' M' G', b'.state = b.state ∧ SFunc.RunCutP P Impl.cert.prog sevm C (St b' S M' G') f r := by
  obtain ⟨b', Y, M', G', hs, hlen, run⟩ := ricP_call_silent (fun h => (hP h).1) Impl.cert_check
    hfork auth_silent auth_noHalt (k := 112) (by decide) (by decide)
    (e := ⟨0x4dc8, [.unk, .unk, .unk, .unk, .ret], 0⟩) rfl rfl (ρ := ρ) run
    (List.Forall₂.cons trivial (.cons trivial (.cons trivial (.cons trivial (.cons rfl .nil)))))
  obtain rfl : Y = [] := List.eq_nil_of_length_eq_zero hlen
  exact ⟨b', M', G', hs, run⟩

/-- Crossing `_requireUnusedAuthorization` (entry 110, frame `[_, _, ret]`). -/
theorem skipP_110 (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {dd x0 x1 ρ : B256}
    (run : SFunc.RunCutP P Impl.cert.prog sevm C (St b (dd :: x0 :: x1 :: ρ :: S) M G)
      (.callNext 110 f) r) :
    ∃ b' M' G', b'.state = b.state ∧ SFunc.RunCutP P Impl.cert.prog sevm C (St b' S M' G') f r := by
  obtain ⟨b', Y, M', G', hs, hlen, run⟩ := ricP_call_silent (fun h => (hP h).1) Impl.cert_check
    hfork sil110_silent cancelCallees_noHalt (k := 110) (by decide) (by decide)
    (e := ⟨0x524e, [.unk, .unk, .ret], 0⟩) rfl rfl (ρ := ρ) run
    (List.Forall₂.cons trivial (.cons trivial (.cons rfl .nil)))
  obtain rfl : Y = [] := List.eq_nil_of_length_eq_zero hlen
  exact ⟨b', M', G', hs, run⟩

/-- Crossing `_domainSeparator` (entry 78, frame `[ret]`, one return word). -/
theorem skipP_78 (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {dd ρ : B256}
    (run : SFunc.RunCutP P Impl.cert.prog sevm C (St b (dd :: ρ :: S) M G) (.callNext 78 f) r) :
    ∃ b' y M' G', b'.state = b.state ∧ SFunc.RunCutP P Impl.cert.prog sevm C (St b' (y :: S) M' G') f r := by
  obtain ⟨b', Y, M', G', hs, hlen, run⟩ := ricP_call_silent (fun h => (hP h).1) Impl.cert_check
    hfork dom78_ok.1 dom78_ok.2.1 (k := 78) (by decide) (by decide) (e := ⟨0x4276, [.ret], 1⟩)
    rfl rfl (ρ := ρ) run (List.Forall₂.cons rfl .nil)
  obtain ⟨y, rfl⟩ : ∃ y, Y = [y] := match Y, hlen with | [y], _ => ⟨y, rfl⟩
  exact ⟨b', y, M', G', hs, run⟩

/-- Crossing `_hashTypedDataV4` (entry 79, frame `[_, _, ret]`, one return word). -/
theorem skipP_79 (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {dd x y ρ : B256}
    (run : SFunc.RunCutP P Impl.cert.prog sevm C (St b (dd :: x :: y :: ρ :: S) M G)
      (.callNext 79 f) r) :
    ∃ b' z M' G', b'.state = b.state ∧ SFunc.RunCutP P Impl.cert.prog sevm C (St b' (z :: S) M' G') f r := by
  obtain ⟨b', Y, M', G', hs, hlen, run⟩ := ricP_call_silent (fun h => (hP h).1) Impl.cert_check
    hfork dom78_ok.2.2.1 dom78_ok.2.2.2 (k := 79) (by decide) (by decide)
    (e := ⟨0x508b, [.unk, .unk, .ret], 1⟩) rfl rfl (ρ := ρ) run
    (List.Forall₂.cons trivial (.cons trivial (.cons rfl .nil)))
  obtain ⟨z, rfl⟩ : ∃ z, Y = [z] := match Y, hlen with | [z], _ => ⟨z, rfl⟩
  exact ⟨b', z, M', G', hs, run⟩

/-- **The entry preamble of a site walk**: the run reaches the dispatcher with the selector on
top of the stack and the base unchanged. -/
theorem preambleP (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b S M G) Impl.t_0000_c0 r) :
    ∃ M' G', SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M' G')
      dispTree r := by
  repeat sx run
  brP run
  repeat sx run
  brP run
  iterate 4 sx run
  rw [selector_word] at run
  exact ⟨_, _, run⟩

end Blanc.Lift.Usdc
