import Blanc.Corpus.Freeze.DepositCells
import Blanc.Lift.BalSilent
import Blanc.Lift.BeaconDeposit.HistEntryPrefix
import Blanc.Lift.BeaconDeposit.HistSafe
import Blanc.Lift.BeaconDeposit.ClassifyViews

/-!
# D-S2: Complete frame classification on the deployed Beacon Deposit runtime

Assembles the historical per-frame classification `frame_classifiedH` and the corpus matrix
theorem `d_s2` / `D_S2_proved` (`Blanc.Corpus.Freeze.Deposit.D_S2`) over every settled frame
at `depositAddr` from the actual Muir Glacier deployment block to `B`.
-/

namespace Blanc.Composition.DepositClassified

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.BeaconDeposit
open Blanc.Corpus.Freeze.Deposit

private def outcomeSelector : DepositOutcome → B256
  | .deposit => 0x22895118
  | .getDepositRoot => 0xc5f2892f
  | .getDepositCount => 0x621fd130
  | .supportsInterface => 0x01ffc9a7

private theorem supportsInterfaceSelector_val :
    BeaconDeposit.supportsInterfaceSelector = 0x01ffc9a7 := by
  decide +kernel

private theorem classified_selector_val {fr : Exec.Frame} {history : List B256}
    {o : DepositOutcome} (hc : Classified fr history o) :
    Sevm.selector fr.sevm = outcomeSelector o := by
  cases o with
  | deposit => exact hc.1.trans BeaconDeposit.depositSelector_eq
  | getDepositRoot => exact hc.1.trans BeaconDeposit.getDepositRootSelector_eq
  | getDepositCount => exact hc.1.trans BeaconDeposit.getDepositCountSelector_eq
  | supportsInterface => exact hc.1.trans supportsInterfaceSelector_val

private theorem classified_unique {fr : Exec.Frame} {history : List B256}
    {o₁ o₂ : DepositOutcome}
    (h₁ : Classified fr history o₁) (h₂ : Classified fr history o₂) : o₁ = o₂ := by
  have hs := (classified_selector_val h₁).symm.trans (classified_selector_val h₂)
  cases o₁ <;> cases o₂ <;> first | rfl | exact absurd hs (by decide)

/-- Every settled frame starting at `pc = 0` on the deployed Beacon Deposit runtime under
`HistFork`, fresh entry, bounded calldata, `ShaReadyRules`, and `SolInv` for `history`
satisfies `Classified fr history o` for a unique `o : DepositOutcome`. -/
theorem frame_classifiedH (fr : Exec.Frame) (history : List B256)
    (pc : fr.pc = 0) (image : fr.sevm.code = code)
    (fork : HistFork fr.sevm.benvStat.fork)
    (fresh : Exec.FreshEntry fr.sevm fr.pre)
    (calldata : fr.sevm.data.length < 2 ^ 256)
    (sha : ShaReadyRules fr.sevm fr.pre)
    (target : fr.sevm.currentTarget = depositAddr)
    (invariant : SolInv (fr.pre.getStor depositAddr) history) :
    ∃! o : DepositOutcome, Classified fr history o := by
  rcases fr with ⟨fpc, sevm, pre, out, run, committed⟩
  cases out with
  | error _ => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      dsimp only at pc image fork fresh calldata sha target invariant
      subst fpc
      have hbal_eq : ∀ a : Adr, post.getBal a = pre.getBal a := fun a =>
        congrFun (Blanc.Lift.frame_keeps_balances_of_staticcalls cert_check
          cert_execs_staticcall cert_noSelfdestruct image run) a
      have invariant' : SolInv (pre.getStor sevm.currentTarget) history := by
        rwa [target]
      obtain ⟨f, hf, srun⟩ := lift_sound_noStateGas cert_check image fork.stateGas_none run
      have hf0 : prog[0]? = some t_0000_c0 := rfl
      rw [hf0] at hf
      cases hf
      rw [St.self fresh.1 fresh.2] at srun
      obtain ⟨k, _, _, hk, hk31, hk32, hk33, hk34, -, -⟩ := safe_dispatch_full srun
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · have hsel : Sevm.selector sevm = BeaconDeposit.supportsInterfaceSelector := hk31.mp rfl
        obtain ⟨hval, hlen36, hout, hstor, hlogs⟩ :=
          interface_frame_effectH image fork calldata fresh hsel run
        have hfl : frameLogs ⟨0, sevm, pre, .ok post, run, committed⟩ = [] := by
          simp only [frameLogs, Exec.Frame.post, Execution.committedPost, hlogs, List.drop_length]
        have hc : Classified ⟨0, sevm, pre, .ok post, run, committed⟩ history .supportsInterface :=
          ⟨hsel, hval, hlen36, hout, hstor, hfl, hbal_eq⟩
        exact ⟨.supportsInterface, hc, fun o' ho' => classified_unique ho' hc⟩
      · have hsel : Sevm.selector sevm = BeaconDeposit.depositSelector := hk32.mp rfl
        obtain ⟨hdec, s', ev, hOk, hacc, hinv', ⟨h, v, hh32, hstor_set⟩, hstor_ne, hlogs⟩ :=
          (deposit_frame_refinesH_of_rules image fork.stateGas_none fork.bal_none calldata
            fresh.1 fresh.2 sha invariant' run).1 hsel
        have hout : post.output = pre.output :=
          deposit_frame_outputH image fork calldata fresh sha invariant' hsel run
        obtain ⟨-, -, -, -, -, -, -, hcap, -, -, -, hev⟩ := deposit_ok_facts hOk
        have hamt : ev.amount = BeaconDeposit.le64 (sevm.value.toNat / BeaconDeposit.oneGwei) := by
          rw [hev]
        rw [target] at hOk hacc hinv' hstor_set hstor_ne hlogs
        rw [hamt] at hinv'
        have hw_cnt : (bodyCount sevm pre).toNat = history.length := by
          change ((pre.getStor sevm.currentTarget).get solCountSlot).toNat = history.length
          rw [target]
          exact invariant.2.1
        have hcnt_lt : history.length < 2 ^ 32 - 1 := by
          rwa [invariant'.2.1] at hcap
        have hcnt_bump : 1 + bodyCount sevm pre = Nat.toB256 (history.length + 1) := by
          apply B256.toNat_inj
          rw [B256.toNat_toB256_of_lt (by omega), B256.toNat_add,
            show (1 : B256).toNat = 1 from rfl, hw_cnt, Nat.lo_eq_of_lt (by omega)]
          omega
        rw [hcnt_bump] at hstor_set
        have hfl : frameLogs ⟨0, sevm, pre, .ok post, run, committed⟩ =
            [BeaconDeposit.depositEventLog depositAddr ev] := by
          simp only [frameLogs, Exec.Frame.post, Execution.committedPost, hlogs, List.drop_left]
        have hc : Classified ⟨0, sevm, pre, .ok post, run, committed⟩ history .deposit :=
          ⟨hsel, hdec, s', ev, hOk, hacc, hinv', ⟨h, v, hh32, hstor_set⟩, hstor_ne, hfl, hout,
            hbal_eq⟩
        exact ⟨.deposit, hc, fun o' ho' => classified_unique ho' hc⟩
      · have hsel : Sevm.selector sevm = BeaconDeposit.getDepositCountSelector := hk33.mp rfl
        obtain ⟨hval, hout, hstor, hlogs⟩ :=
          count_frame_effectH image fork calldata fresh invariant' hsel run
        have hfl : frameLogs ⟨0, sevm, pre, .ok post, run, committed⟩ = [] := by
          simp only [frameLogs, Exec.Frame.post, Execution.committedPost, hlogs, List.drop_length]
        have hc : Classified ⟨0, sevm, pre, .ok post, run, committed⟩ history .getDepositCount :=
          ⟨hsel, hval, hout, hstor, hfl, hbal_eq⟩
        exact ⟨.getDepositCount, hc, fun o' ho' => classified_unique ho' hc⟩
      · have hsel : Sevm.selector sevm = BeaconDeposit.getDepositRootSelector := hk34.mp rfl
        obtain ⟨hval, hout, hstor, hlogs⟩ :=
          root_frame_effectH image fork calldata fresh sha invariant' hsel run
        rw [target] at hout
        have hfl : frameLogs ⟨0, sevm, pre, .ok post, run, committed⟩ = [] := by
          simp only [frameLogs, Exec.Frame.post, Execution.committedPost, hlogs, List.drop_length]
        have hc : Classified ⟨0, sevm, pre, .ok post, run, committed⟩ history .getDepositRoot :=
          ⟨hsel, hval, hout, hstor, hfl, hbal_eq⟩
        exact ⟨.getDepositRoot, hc, fun o' ho' => classified_unique ho' hc⟩

/-- **D-S2.** Every settled frame targeting `depositAddr` across the deployment-to-`B` retained
span enters with `SolInv` for the committed-deposit prefix before `idx` and satisfies a unique
`Classified` arm. -/
theorem d_s2 : Blanc.Corpus.Freeze.Deposit.D_S2 := by
  intro B d idx fr hlookup htarget
  obtain ⟨hpc, hfork, himage, hfresh, hcd, hsha, hinv⟩ :=
    d.classification_inputs idx fr hlookup htarget
  exact ⟨hinv, frame_classifiedH fr _ hpc himage hfork hfresh hcd hsha htarget hinv⟩

end Blanc.Composition.DepositClassified
