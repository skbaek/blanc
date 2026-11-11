import Batteries.Tactic.OpenPrivate
import Blanc.Composition.BuilderRequestClassification
import Blanc.ConcreteRun
import Blanc.Lift.Witness
import Blanc.Lift.BuilderRequest.Deposit.Revert
import Blanc.Lift.BuilderRequest.Exit.Revert

/-!
# Canonical rejection and actual guard-deletion countermodels

The block record is only the index/fork witness required by the frozen
frame controls. Every countermodel frame carries its actual Exec derivation;
no kept-history membership or transaction validity is asserted here.
-/

namespace Blanc.Composition.BuilderRequestControls

open Jaune Blanc Blanc.Lift.BuilderRequest
open Corpus.Freeze.Builder
open BuilderRequestPublic (depositAddr exitAddr)
open private wordFee_of_run
  from Blanc.Composition.BuilderRequestClassification

private def block : KeptBlock where
  parent := ⟨[], .empty, 0⟩
  block :=
    { header :=
        { parentHash := 0, ommersHash := 0, coinbase := 0, stateRoot := 0,
          txsRoot := 0, receiptRoot := 0, bloom := [], difficulty := 0,
          number := 0, gasLimit := 1000000, gasUsed := 0, timestamp := 0,
          extraData := [], prevRandao := 0, nonce := 0, baseFeePerGas := none,
          withdrawalsRoot := none, blobGasUsed := none, excessBlobGas := none,
          parentBeaconBlockRoot := none, requestsHash := none,
          blockAccessListHash := none, slotNumber := none },
      txs := [], ommers := [], wds := [] }
  fork := .prague
  output := BlockOutput.init
  run := ⟨.empty, {}, [], default, BlockOutput.init, [], [], []⟩

private def depositBad (sevm : Sevm) (pre : Devm) : Prop :=
  (sevm.data ≠ [] ∧ sevm.data.length ≠ 184) ∨
  pre.getStorVal depositAddr 0 = B256.max ∨
  (sevm.data.length = 184 ∧ ¬ Deposit.Admitted sevm (wordFee (quotedExcess 8 pre depositAddr)))

private def exitBad (sevm : Sevm) (pre : Devm) : Prop :=
  (sevm.data ≠ [] ∧ sevm.data.length ≠ 48) ∨
  pre.getStorVal exitAddr 0 = B256.max ∨
  (sevm.data.length = 48 ∧ sevm.value.toNat < (wordFee (quotedExcess 2 pre exitAddr)).toNat)

private theorem deposit_guard_excludes {b : KeptBlock} {f : Exec.Frame}
    (caller : f.sevm.caller ≠ systemAddress) (bad : depositBad f.sevm f.pre) :
    ¬ DepositSettled b f := by
  intro settled
  cases settled with
  | dequeue system => exact caller system
  | latch system => exact caller system
  | submission _ length _ active admitted =>
      rcases bad with ⟨_, wrong⟩ | inhibited | ⟨_, rejected⟩
      · exact wrong length
      · exact active inhibited
      · exact rejected admitted
  | feeRead _ empty _ active =>
      rcases bad with ⟨nonempty, _⟩ | inhibited | ⟨length, _⟩
      · exact nonempty empty
      · exact active inhibited
      · rw [empty] at length
        contradiction

private theorem exit_guard_excludes {b : KeptBlock} {f : Exec.Frame}
    (caller : f.sevm.caller ≠ systemAddress) (bad : exitBad f.sevm f.pre) :
    ¬ ExitSettled b f := by
  intro settled
  cases settled with
  | dequeue system => exact caller system
  | latch system => exact caller system
  | submission _ length _ active covered =>
      rcases bad with ⟨_, wrong⟩ | inhibited | ⟨_, underpaid⟩
      · exact wrong length
      · exact active inhibited
      · exact Nat.not_lt_of_ge covered underpaid
  | feeRead _ empty _ active =>
      rcases bad with ⟨nonempty, _⟩ | inhibited | ⟨length, _⟩
      · exact nonempty empty
      · exact active inhibited
      · rw [empty] at length
        contradiction

private theorem deposit_reject_on {sevm : Sevm} {pre post : Devm} {l : StorageSteps sevm}
    (valid : l.Valid) (code : sevm.code = Deposit.code) (target : sevm.currentTarget = depositAddr)
    (caller : sevm.caller ≠ systemAddress) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (length : sevm.data.length < 2 ^ 256) (bad : depositBad sevm pre)
    (run : Exec 0 sevm pre (.ok post)) : False := by
  cases Deposit.exec_user_frame_on valid code stack aligned wf length caller run with
  | submission iterations finalOutput effect =>
      have fee : finalOutput / (17 : B256) = wordFee (quotedExcess 8 pre depositAddr) := by
        simpa only [storedExcess, quotedExcess, target] using wordFee_of_run effect.quote
      rcases bad with ⟨_, wrong⟩ | inhibited | ⟨_, rejected⟩
      · exact wrong effect.length
      · exact effect.active (by simpa only [target] using inhibited)
      · exact rejected (fee ▸ effect.admitted)
  | feeRead _ _ empty effect =>
      rcases bad with ⟨nonempty, _⟩ | inhibited | ⟨literal, _⟩
      · exact nonempty empty
      · exact effect.active (by simpa only [target] using inhibited)
      · rw [empty] at literal
        contradiction

private theorem exit_reject_on {sevm : Sevm} {pre post : Devm} {l : StorageSteps sevm}
    (valid : l.Valid) (code : sevm.code = Exit.code) (target : sevm.currentTarget = exitAddr)
    (caller : sevm.caller ≠ systemAddress) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (length : sevm.data.length < 2 ^ 256) (bad : exitBad sevm pre)
    (run : Exec 0 sevm pre (.ok post)) : False := by
  cases Exit.exec_user_frame_on valid code stack aligned wf length caller run with
  | submission iterations finalOutput effect =>
      have fee : finalOutput / (17 : B256) = wordFee (quotedExcess 2 pre exitAddr) := by
        simpa only [storedExcess, quotedExcess, target] using wordFee_of_run effect.quote
      rcases bad with ⟨_, wrong⟩ | inhibited | ⟨_, underpaid⟩
      · exact wrong effect.length
      · exact effect.active (by simpa only [target] using inhibited)
      · exact Nat.not_lt_of_ge (fee ▸ effect.covered) underpaid
  | feeRead _ _ empty effect =>
      rcases bad with ⟨nonempty, _⟩ | inhibited | ⟨literal, _⟩
      · exact nonempty empty
      · exact effect.active (by simpa only [target] using inhibited)
      · rw [empty] at literal
        contradiction

private theorem deposit_rejected {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Deposit.code) (target : sevm.currentTarget = depositAddr)
    (fork : KeptFork sevm.benvStat.fork) (caller : sevm.caller ≠ systemAddress)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (length : sevm.data.length < 2 ^ 256) (bad : depositBad sevm pre) :
    IsEmpty (Exec 0 sevm pre (.ok post)) := by
  refine ⟨fun run => ?_⟩
  rcases fork with covered | amsterdam
  · exact deposit_reject_on (coveredSteps_valid covered) code target caller stack aligned wf length bad run
  · exact deposit_reject_on (amsterdamSteps_valid amsterdam) code target caller stack aligned wf length bad run

private theorem exit_rejected {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Exit.code) (target : sevm.currentTarget = exitAddr)
    (fork : KeptFork sevm.benvStat.fork) (caller : sevm.caller ≠ systemAddress)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (length : sevm.data.length < 2 ^ 256) (bad : exitBad sevm pre) :
    IsEmpty (Exec 0 sevm pre (.ok post)) := by
  refine ⟨fun run => ?_⟩
  rcases fork with covered | amsterdam
  · exact exit_reject_on (coveredSteps_valid covered) code target caller stack aligned wf length bad run
  · exact exit_reject_on (amsterdamSteps_valid amsterdam) code target caller stack aligned wf length bad run

private def pre : Devm := (default : Devm).withGasLeft 1000000

private def input (target : Adr) (data : Bytes) (value : B256) : Sevm :=
  { (default : Sevm) with
    caller := 1
    target := some target
    currentTarget := target
    gas := 1000000
    value := value
    data := data
    codeAddress := some target
    depth := 0
    benvStat := { (default : BenvStat) with fork := .prague } }

private inductive Control where
  | depositFloor | depositSpurious | exitFee | exitSpurious

private def path : Control → UserPath
  | .depositFloor | .depositSpurious => Deposit.userPath
  | .exitFee | .exitSpurious => Exit.userPath

private def mutant : Control → Sevm
  | .depositFloor => { input depositAddr (List.replicate 184 0) 1 with code := depositNoFloorCode }
  | .depositSpurious => { input depositAddr [0] 0 with code := depositSpuriousArmCode }
  | .exitFee => { input exitAddr (List.replicate 48 0) 0 with code := exitNoFeeGuardCode }
  | .exitSpurious => { input exitAddr [0] 0 with code := exitSpuriousArmCode }

private def cutPc : Control → Nat
  | .depositFloor => 283
  | .depositSpurious => 627
  | .exitFee => 224
  | .exitSpurious => 457

private def entries : Control → List Nat
  | .depositFloor | .depositSpurious => Deposit.cutEntries
  | .exitFee | .exitSpurious => Exit.cutEntries

-- Only the guards changed by the frozen patch are new tree data. The store
-- tails below are the original generated trees, not duplicated instructions.
private def depositCover : Blanc.Lift.SFunc :=
  .next (.push [0x3b, 0x9a, 0xca, 0x00] (by decide)) (.next (.reg .mul) (.next (.reg (.swap 0))
    (.next (.reg .callvalue) (.next (.reg .sub) (.next (.reg .lt) (.next (.push [0x02, 0x70] (by decide))
      (.branch Deposit.t_00cd_c1 .undefined)))))))

private def depositFloorDeleted : Blanc.Lift.SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg .callvalue) (.next (.reg .lt)
    (.next (.push [0x02, 0x70] (by decide)) (.branch
      (.next (.push [0x38] (by decide)) (.next (.reg .calldataload)
        (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide))
          (.next (.reg .and) (.next (.reg (.dup 0)) (.next (.push [0x3b, 0x9a, 0xca, 0x00] (by decide))
            (.next (.reg .gt) (.next (.reg .pop) (.dest (.dest (.dest depositCover)))))))))))
      .undefined)))))

private def exitFeeDeleted : Blanc.Lift.SFunc :=
  .dest (.next (.reg .callvalue) (.next (.reg .lt)
    (.next (.reg .pop) (.dest (.dest (.dest Exit.t_00a5_c1))))))

private def getter (c : Control) : Blanc.Lift.SFunc :=
  match c with
  | .depositFloor | .exitFee => .undefined
  | .depositSpurious | .exitSpurious => UserPath.badLengthCut (path c)

private def submission : Control → Blanc.Lift.SFunc
  | .depositFloor => depositFloorDeleted
  | .exitFee => exitFeeDeleted
  | .depositSpurious | .exitSpurious => .undefined

private def program (c : Control) : List Blanc.Lift.SFunc := (path c).cutProg (getter c) (submission c)
private def root (c : Control) : Blanc.Lift.SFunc := (path c).cutRoot (getter c) (submission c)
private def start (c : Control) : Blanc.Lift.Witness.Cfg := ⟨pre, root c, [], [], [], [], []⟩

private theorem start_agree (c : Control) : Blanc.Lift.Witness.Agree (start c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    change x ∈ (∅ : Std.HashSet (Adr × B256)) ↔ x ∈ ([] : List (Adr × B256))
    exact ⟨fun h => (Std.HashSet.not_mem_empty h).elim, fun h => (List.not_mem_nil h).elim⟩
  · intro a
    change a ∈ (∅ : Std.HashSet Adr) ↔ a ∈ ([] : List Adr)
    exact ⟨fun h => (Std.HashSet.not_mem_empty h).elim, fun h => (List.not_mem_nil h).elim⟩
  · intro a k
    rfl
  · intro a
    rfl

private theorem program_checks (c : Control) :
    cutAll (mutant c).code (entries c) (cutPc c) (program c) (entries c) = true := by
  cases c <;> decide +kernel

private theorem root_checks (c : Control) :
    Blanc.Lift.cutOk (mutant c).code (entries c) (cutPc c) 0 none (root c) = true := by
  cases c <;> decide +kernel

private theorem stop_at (c : Control) : Linst.At (mutant c).code (cutPc c) .stop := by
  cases c <;> unfold Linst.At <;> kernel_rfl

private theorem run_commits (c : Control) :
    (match Blanc.Lift.Witness.wrun (program c) (mutant c) 512 (start c) with
      | .done (.halted post) _ => post.error.isNone | _ => false) = true := by
  cases c <;> kernel_rfl

private theorem mutant_runs (c : Control) : ∃ post,
    Nonempty (Exec 0 (mutant c) pre (.ok post)) ∧ Execution.commits (.ok post) = true := by
  have status := run_commits c
  cases result : Blanc.Lift.Witness.wrun (program c) (mutant c) 512 (start c) with
  | cont cl => rw [result] at status; contradiction
  | stuck => rw [result] at status; contradiction
  | done outcome cl =>
      cases outcome with
      | returned d => rw [result] at status; contradiction
      | halted post =>
          rw [result] at status
          have run := (Blanc.Lift.Witness.wrun_done result (start_agree c)).1
          have next : Nonempty (Exec (cutPc c) (mutant c) post (.ok post)) := by
            refine ⟨Exec.halt ?_⟩
            rw [Evm.step_last (stop_at c)]
            rfl
          refine ⟨post, ?_, status⟩
          exact Blanc.Lift.exec_of_cut (cutAll_spec (program_checks c)) run rfl 0 none
            (root_checks c) (fun _ h => by cases h) next

private theorem zero_fee : wordFee 0 = 1 := by
  have run : WordFakeExponential.Run 0 17 1 17 0 1 17 :=
    .step (by decide) (.stop 2 17)
  exact (wordFee_of_run run).symm

private theorem deposit_credit_zero : Deposit.creditedWei (mutant .depositFloor) = 0 := by
  kernel_rfl

private theorem deposit_floor_bad : depositBad (mutant .depositFloor) pre := by
  refine .inr (.inr ⟨by simp only [mutant, input, List.length_replicate], ?_⟩)
  intro admitted
  have floor := admitted.credited
  rw [deposit_credit_zero] at floor
  omega

private theorem exit_fee_bad : exitBad (mutant .exitFee) pre := by
  refine .inr (.inr ⟨by simp only [mutant, input, List.length_replicate], ?_⟩)
  change 0 < (wordFee 0).toNat
  rw [zero_fee]
  decide

/-- Canonical deposit guard rejection and both actual committed deposit
mutations outside the frozen relation. -/
theorem b_s2_deposit_control : B_S2_deposit_control := by
  refine ⟨deposit_rejected, ?_, ?_⟩
  · obtain ⟨post, ⟨run⟩, hc⟩ := mutant_runs .depositFloor
    refine ⟨block, mutant .depositFloor, pre, post, run, hc,
      rfl, by decide, .inl .prague, rfl, rfl, rfl, by simp only [mutant, input, List.length_replicate], ?_, ?_⟩
    · intro post'
      exact deposit_rejected rfl rfl (.inl .prague) (by decide) rfl (by decide)
        Mem.wf_empty (by simp only [mutant, input, List.length_replicate]; decide) (by
          refine .inr (.inr ⟨by simp only [mutant, input, List.length_replicate], ?_⟩)
          intro admitted
          have floor := admitted.credited
          simp only [Deposit.creditedWei_eq] at floor
          have zero : Deposit.creditOf (mutant .depositFloor).data = 0 :=
            (Deposit.creditedWei_eq _).symm.trans deposit_credit_zero
          rw [zero] at floor
          omega)
    · apply deposit_guard_excludes
      · change (1 : Adr) ≠ systemAddress; decide
      · change depositBad (mutant .depositFloor) pre
        exact deposit_floor_bad
  · obtain ⟨post, ⟨run⟩, hc⟩ := mutant_runs .depositSpurious
    refine ⟨block, mutant .depositSpurious, pre, post, run, hc,
      rfl, by decide, .inl .prague, rfl, rfl, rfl, by decide, by decide, ?_, ?_⟩
    · intro post'
      exact deposit_rejected rfl rfl (.inl .prague) (by decide) rfl (by decide)
        Mem.wf_empty (by decide) (.inl ⟨by decide, by decide⟩)
    · apply deposit_guard_excludes
      · change (1 : Adr) ≠ systemAddress; decide
      · change depositBad (mutant .depositSpurious) pre
        exact .inl ⟨by decide, by decide⟩

/-- The exit guard-deletion and spurious-arm controls, with their original
actual executions and the universal canonical rejection. -/
theorem b_s2_exit_control : B_S2_exit_control := by
  refine ⟨exit_rejected, ?_, ?_⟩
  · obtain ⟨post, ⟨run⟩, hc⟩ := mutant_runs .exitFee
    refine ⟨block, mutant .exitFee, pre, post, run, hc,
      rfl, by decide, .inl .prague, rfl, rfl, rfl, by simp only [mutant, input, List.length_replicate], ?_, ?_⟩
    · intro post'
      exact exit_rejected rfl rfl (.inl .prague) (by decide) rfl (by decide)
        Mem.wf_empty (by decide) exit_fee_bad
    · apply exit_guard_excludes
      · change (1 : Adr) ≠ systemAddress; decide
      · change exitBad (mutant .exitFee) pre
        exact exit_fee_bad
  · obtain ⟨post, ⟨run⟩, hc⟩ := mutant_runs .exitSpurious
    refine ⟨block, mutant .exitSpurious, pre, post, run, hc,
      rfl, by decide, .inl .prague, rfl, rfl, rfl, by decide, by decide, ?_, ?_⟩
    · intro post'
      exact exit_rejected rfl rfl (.inl .prague) (by decide) rfl (by decide)
        Mem.wf_empty (by decide) (.inl ⟨by decide, by decide⟩)
    · apply exit_guard_excludes
      · change (1 : Adr) ≠ systemAddress; decide
      · change exitBad (mutant .exitSpurious) pre
        exact .inl ⟨by decide, by decide⟩

/-- Both exact frozen control endpoints. -/
theorem b_s2_control : B_S2_deposit_control ∧ B_S2_exit_control :=
  ⟨b_s2_deposit_control, b_s2_exit_control⟩

end Blanc.Composition.BuilderRequestControls
