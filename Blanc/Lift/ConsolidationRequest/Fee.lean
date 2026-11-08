import Blanc.Lift.RequestFee.Plain
import Blanc.Lift.SystemExecution.ConsolidationRequest.Jumps

/-!
# The EIP-7251 fee, under covered forks

The consolidation runtime's user path is the shared plain path (`RequestFee.PlainUserPath`): caller
dispatch, the slot-zero inhibitor guard, and the word `fake_exponential` at fraction 17 on slot 0 as
stored. While slot 0 holds the inhibitor every user call reverts, so the fee is never quoted from it.

The fee statements compare the word fee the bytes quote with the EIP's `fake_exponential(1, excess,
17)`, over the shared lemmas of `Blanc.RequestFeeWord*`: at most the natural fee always, equal to it
exactly on the recurrence's no-wrap domain, which holds through excess 2892, and different at 2893.
These are statements about one frame over any storage, not a claim that such storage is reachable.

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`; the bytes
`Blanc.consolidationRequestCode` (414 bytes, SHA-256 `99e3d84d...`).
-/

namespace Blanc.Lift.ConsolidationRequest

open Jaune
open SystemExecution.ConsolidationRequest
open RequestFee (PlainUserPath)

/-- The consolidation runtime's user path. -/
def userPath : PlainUserPath where
  code := code
  cert := cert
  check := cert_check
  jumps := jumps_ok
  noExec := progNoExec_of_all (by decide +kernel)
  shape :=
    { revert := ⟨0x01, [0x9a], by decide⟩
      post := ⟨0x68, [], by decide⟩
      loop := ⟨0x4d, [], by decide⟩
      loopEntry := 5
      len := ⟨0x60, [], by decide⟩
      submit := ⟨0x88, [], by decide⟩ }
  systemDest := ⟨0xd3, [], by decide⟩
  system := t_00d3_c0
  revert := t_019a_c0
  getterDest := ⟨0x01, [0x9a], by decide⟩
  getterRevert := t_019a_c0
  submission := t_0088_c0
  root := rfl
  loop := rfl
  revert_noOk := rfl
  getterRevert_noOk := rfl
  len_ne := by decide

/-- The EIP's fee at excess `excess`: `fake_exponential(1, excess, 17)`. -/
def SpecFee (excess : B256) : Nat := fakeExp 1 excess.toNat 17

/-- The fee the bytes quote from the word loop's output. -/
def WordFee (output : B256) : Nat := (output / (17 : B256)).toNat

/-- **EIP-7251 fee bound.** The word fee the bytes compute from excess `excess` is at most the EIP's
`fake_exponential(1, excess, 17)`. -/
theorem fee_le_spec {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output) :
    WordFee output ≤ SpecFee excess :=
  RequestFeeWord.word_fee_le run

/-- **EIP-7251 exact fee.** The word fee equals `fake_exponential(1, excess, 17)` exactly on the
recurrence's no-wrap domain. -/
theorem fee_eq_spec_iff {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output) :
    WordFee output = SpecFee excess ↔ RequestFeeWord.NoWrapDomain excess iterations :=
  RequestFeeWord.word_fee_eq_iff run

/-- **Through excess 2892 the fee is the EIP's.** -/
theorem fee_eq_spec_of_le {excess : B256} {iterations : Nat} {output : B256}
    (le : excess.toNat ≤ 2892) (run : WordFakeExponential.Run excess 17 1 17 0 iterations output) :
    WordFee output = SpecFee excess :=
  RequestFee.word_fee_eq_of_le le run

/-- **At excess 2893 the fee is not the EIP's.** -/
theorem fee_ne_spec_2893 {excess : B256} {iterations : Nat} {output : B256}
    (at2893 : excess.toNat = 2893) (run : WordFakeExponential.Run excess 17 1 17 0 iterations output) :
    WordFee output ≠ SpecFee excess :=
  RequestFee.word_fee_ne_at_2893 at2893 run

variable {sevm : Sevm} {pre post : Devm}

/-- **EIP-7251 fee read.** Under covered forks, a successful empty-calldata execution of the
consolidation code at a non-system caller from an empty stack carries no value, changes no storage,
balance or log, has slot 0 off the inhibitor, and returns the word fee of slot 0 as one word: at most
`fake_exponential(1, slot0, 17)`, and equal to it when slot 0 is at most 2892. `aligned` and `wf` hold of
the empty memory every frame starts with. -/
theorem exec_fee_read (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ iterations output, PlainUserPath.FeeRead sevm pre post iterations output ∧
      WordFee output ≤ SpecFee (pre.getStorVal sevm.currentTarget 0) ∧
      ((pre.getStorVal sevm.currentTarget 0).toNat ≤ 2892 →
        WordFee output = SpecFee (pre.getStorVal sevm.currentTarget 0)) := by
  obtain ⟨iterations, output, read⟩ :=
    PlainUserPath.exec_fee_read (k := userPath) fork hcode stack aligned wf caller empty exec
  exact ⟨iterations, output, read, fee_le_spec read.quote, fun le => fee_eq_spec_of_le le read.quote⟩

/-- The fee read, forward: empty calldata, no value and slot 0 off the inhibitor give a successful
execution at the exact charge, returning the word fee. -/
theorem exec_fee_read_exact {b : Devm} {M : Mem} {G iterations : Nat} {output : B256}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations output) :
    Nonempty (Exec 0 sevm (St b [] M (G + PlainUserPath.feeReadGas sevm b M iterations))
      (.ok (RequestFee.feeGetterPost (afterSload sevm b 0) M (output / (17 : B256)) G))) :=
  PlainUserPath.exec_fee_read_exact (k := userPath) fork hcode aligned caller empty zero off wordRun

/-- **Inhibited rejection.** While slot 0 holds the inhibitor, no execution of the consolidation code at
a non-system caller from an empty stack succeeds, for any calldata, value and memory. -/
theorem exec_user_inhibited_no_ok (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (caller : sevm.caller ≠ systemAddress)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max)
    (exec : Exec 0 sevm pre (.ok post)) : False :=
  PlainUserPath.exec_inhibited_no_ok (k := userPath) fork hcode stack caller inhibited exec

end Blanc.Lift.ConsolidationRequest
