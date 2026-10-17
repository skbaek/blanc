import Blanc.Lift.QuietDelegateSkip
import Blanc.Lift.Usdc.ImplFrames
import Blanc.Lift.Usdc.LibSpawns
import Blanc.Lift.Usdc.FootprintLedger

/-!
# The signed family's library calls, skipped (route C, C2 instances)

The two skip facts the signed-family walks (U6e3/U6e4) call, and the node clause of
`ImplStepLaw` at the library-call nodes:

* `lib_quietCode`: the `SignatureChecker` runtime is quiet (`QuietCode Lib.code`), from the
  library's certificate (`lib_children`);
* `signed_closure_quiet`: the closure of `_requireValidSignature` (implementation entry 111,
  530 certificate instructions over entries 4, 6, 11, 76–79, 106, 107, 111, 117) writes no storage
  and executes no external instruction but `DELEGATECALL` (one kernel decide);
* `skip_requireValidSignature`: crossing the `callNext 111` keeps the proxy's storage and the
  library's code, and drops the callee's four frame words;
* `skip_libCall`: crossing the library `DELEGATECALL` itself (permit's inline call in entry 9) keeps
  them, leaving the flag above the operands;
* `libNode_clause`: storage at a library-call node equal to the pre-state, or to the pre-state with
  a tracked nonce word written, keeps `Ledger.Good` and the proxy's implementation and admin
  slots.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- **The library is quiet**: a successful frame running `Lib.code` keeps its storage owner's
storage. -/
theorem lib_quietCode : QuietCode Lib.code := fun run codeEq fork =>
  (lib_children run codeEq fork).2 _ rfl

theorem lib_undelegated : getDelegatedCodeAddress Lib.code = none := by decide +kernel

theorem lib_nonempty : Lib.code.toList ≠ [] := by decide +kernel

theorem usdcLib_word : usdcLib.toB256.toAdr = usdcLib := by decide +kernel

/-- `_requireValidSignature`'s closure. -/
def sigClosure : List Nat := [4, 6, 11, 76, 77, 78, 79, 106, 107, 111, 117]

/-- **No `SSTORE`, external instructions only `DELEGATECALL`** over `_requireValidSignature`'s
closure (530 certificate instructions). -/
theorem signed_closure_quiet : QuietDelegateSet Impl.cert.prog sigClosure = true := by
  decide +kernel

theorem implP_delegatecall (a : List AVal) (h : implP (.exec .delegatecall) a = true) :
    a[1]? = some (.const usdcLib.toB256) := by
  simpa only [implP, beq_iff_eq, libWord] using h

/-- **Crossing `_requireValidSignature`** (entry 111, frame `[_, _, _, ret]`, no return words). -/
theorem skip_requireValidSignature {sevm : Sevm} {C : List Nat} {b : Devm}
    {dd x0 x1 x2 x3 : B256} {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {r : Seg}
    (hfork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.RunCut Impl.cert.prog sevm C (St b (dd :: x0 :: x1 :: x2 :: x3 :: S) M G)
      (.callNext 111 f) r) :
    (∃ b' M' G', Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
        b'.getCode usdcLib = Lib.code ∧ SFunc.RunCut Impl.cert.prog sevm C (St b' S M' G') f r) ∨
      (∃ D, Devm.getStor D sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
        D.getCode usdcLib = Lib.code ∧ r = .done (.halted D)) := by
  have he : certL.entries[111]? = some ⟨0x4e88, [.unk, .unk, .unk, .ret], 0⟩ := by
    rw [certL_entries_ne (by decide)]
    rfl
  have hg : certL.prog[111]? = some Impl.t_4e88_c111 := by
    rw [certL_prog]
    rfl
  have hS : QuietDelegateSet certL.prog sigClosure = true := by
    rw [certL_prog]
    exact signed_closure_quiet
  have hcode' : b.getCode usdcLib.toB256.toAdr = Lib.code := by rw [usdcLib_word]; exact hcode
  rw [← certL_prog] at run ⊢
  rcases ric_call_quietDelegate certL_check certL_framesSat hfork lib_quietCode implP_delegatecall
      lib_undelegated lib_nonempty hS (by decide) he hg (S := x0 :: x1 :: x2 :: x3 :: S) (ρ := x3)
      (List.Forall₂.cons (R := AVal.Matches x3) trivial (.cons trivial (.cons trivial
        (.cons rfl .nil)))) hcode' run with
    ⟨b', Y, M', G', ⟨hst, hc⟩, hlen, cont⟩ | ⟨D, ⟨hst, hc⟩, hr⟩
  · obtain rfl : Y = [] := List.eq_nil_of_length_eq_zero hlen
    exact .inl ⟨b', M', G', hst, by rw [← usdcLib_word, hc, hcode'], cont⟩
  · exact .inr ⟨D, hst, by rw [← usdcLib_word, hc, hcode'], hr⟩

/-- **Crossing the library `DELEGATECALL`** (permit's inline call): the proxy's storage and the
library's code are kept, and a flag replaces the six operands. -/
theorem skip_libCall {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm}
    {g ii is oi os : B256} {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {r : Seg}
    (hfork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.RunCut fs sevm C (St b (g :: usdcLib.toB256 :: ii :: is :: oi :: os :: S) M G)
      (.next (.exec .delegatecall) f) r) :
    ∃ b' x M' G', Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
      b'.getCode usdcLib = Lib.code ∧ SFunc.RunCut fs sevm C (St b' (x :: S) M' G') f r := by
  have hcode' : b.getCode usdcLib.toB256.toAdr = Lib.code := by rw [usdcLib_word]; exact hcode
  obtain ⟨b', x, M', G', hst, hc, cont⟩ :=
    ric_delegatecall_quiet lib_quietCode hfork hcode' lib_undelegated lib_nonempty run
  exact ⟨b', x, M', G', hst, by rw [← usdcLib_word]; exact hc, cont⟩

/-- **The node clause at a library-call node.**  If the proxy's storage at the node is the frame's
pre-state, or the pre-state with a tracked nonce word written (permit bumps the nonce before its
library call), the ledger stays good and the implementation and admin slots are the pre-state's. -/
theorem libNode_clause {U : Key → Prop} {pre N : Stor}
    (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (h : N = pre ∨ ∃ o w, U (.nonce o) ∧ N = pre.set (nonceSlot o) w) :
    ((ledger U pre).Good → (ledger U N).Good) ∧ N.get implSlot = pre.get implSlot ∧
      N.get adminSlot = pre.get adminSlot := by
  have off : ∀ x ∈ fixedSlots, N.get x = pre.get x := by
    intro x hx
    rcases h with rfl | ⟨o, w, ho, rfl⟩
    · rfl
    · have hk : Key.slot (.nonce o) = nonceSlot o := rfl
      exact Stor.get_set_ne _ (fun e => apart (.nonce o) ho (by rw [hk, e]; exact hx)) w
  exact ⟨fun good => ledger_good_congr good (off 8 (by decide)) (off 18 (by decide)),
    off implSlot (by simp only [fixedSlots, List.mem_cons, true_or, or_true]),
    off adminSlot (by simp only [fixedSlots, List.mem_cons, List.not_mem_nil, true_or, or_true])⟩

end Blanc.Lift.Usdc
