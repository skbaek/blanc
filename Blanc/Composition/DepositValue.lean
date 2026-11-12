import Batteries.Tactic.OpenPrivate
import Blanc.AbiBytesTail
import Blanc.Corpus.Freeze.DepositCells
import Blanc.ExecutionKeptFresh
import Blanc.ExecutionKeptValue
import Blanc.Lift.BalSilent
import Blanc.Lift.BeaconDeposit.LogOnly

/-!
# D-S6: Kept deposit value and event-amount attribution

Proves the frozen `D_S6` (`D6`) cell over covered-fork kept histories with the deployed Beacon
Deposit runtime installed at `start.state`, without assuming `SolInv`:

1. Every settled frame at `depositAddr` is balance-silent (`frame_keeps_balances_of_staticcalls`),
   so `KeptHistory.bal_covers` bounds `(stop.state.bal depositAddr).toNat` below by the starting
   balance plus the sum of incoming values of all kept frames at `depositAddr`.
2. Every kept frame at `depositAddr` selecting `depositSelector` satisfies the three value guards
   (`1 ETH ≤ value`, `value % 1 gwei = 0`, `value / 1 gwei ≤ 2^64 - 1`) and any `DepositEvent`
   matching its emitted log carries `le64 (value / 1 gwei)` as its `amount`.
-/

namespace Blanc.Composition.DepositValue

open Jaune Blanc Blanc.Lift Blanc.Lift.BeaconDeposit
open Blanc.Corpus.Freeze.Deposit

open private event_logs from Blanc.Lift.BeaconDeposit.LogOnly

private theorem depositKeptValue : KeptValueAt depositAddr code where
  nonempty := beaconInstalledCertH.nonempty
  nondelegating := beaconInstalledCertH.notDelegation
  law := fun {_ _ _} _ hcode run =>
    congrArg B256.toNat (congrFun (Blanc.Lift.frame_keeps_balances_of_staticcalls cert_check
      cert_execs_staticcall cert_noSelfdestruct hcode run) depositAddr)

private theorem depositAddr_not_precomp :
    ∀ f, KeptFork f → ¬ f.ruleSet.isPrecomp depositAddr := by
  intro f hf
  rcases hf with covered | rfl
  · exact covered.cases (motive := fun f => ¬ f.ruleSet.isPrecomp depositAddr)
      (by decide) (by decide) (by decide) (by decide)
  · decide

private theorem abiDepositEvent_amount_eq {ev ev₀ : Blanc.BeaconDeposit.DepositEvent}
    (hlen₀ : (Blanc.BeaconDeposit.abiDepositEvent ev₀).length = 576)
    (heq : Blanc.BeaconDeposit.abiDepositEvent ev = Blanc.BeaconDeposit.abiDepositEvent ev₀) :
    ev.amount = ev₀.amount := by
  have hlen : (Blanc.BeaconDeposit.abiDepositEvent ev).length = 576 := by
    rw [heq]
    exact hlen₀
  simp only [Blanc.BeaconDeposit.abiDepositEvent, List.length_append, B256.length_toBytes,
    Blanc.BeaconDeposit.abiBytesTail_length] at hlen hlen₀
  have hpk_le := Nat.le_ceil32 ev.pubkey.length
  have hwc_le := Nat.le_ceil32 ev.withdrawal_credentials.length
  have ham_le := Nat.le_ceil32 ev.amount.length
  have hpk₀_le := Nat.le_ceil32 ev₀.pubkey.length
  have hwc₀_le := Nat.le_ceil32 ev₀.withdrawal_credentials.length
  have ham₀_le := Nat.le_ceil32 ev₀.amount.length
  have h256 : (576 : Nat) < 2 ^ 256 := by decide
  let hdr : Bytes := (160 : B256).toBytes ++ (256 : B256).toBytes ++ (320 : B256).toBytes ++
    (384 : B256).toBytes ++ (512 : B256).toBytes
  have hsplit : ∀ e : Blanc.BeaconDeposit.DepositEvent,
      Blanc.BeaconDeposit.abiDepositEvent e =
        hdr ++ (abiBytesTail e.pubkey ++
          (abiBytesTail e.withdrawal_credentials ++
            (abiBytesTail e.amount ++
              (abiBytesTail e.signature ++ abiBytesTail e.index)))) := by
    intro e
    simp only [Blanc.BeaconDeposit.abiDepositEvent, hdr, List.append_assoc]
  have heq' := heq
  rw [hsplit, hsplit] at heq'
  have htails := (List.append_inj heq' rfl).2
  obtain ⟨-, htails1⟩ := abiBytesTail_append_inj (by omega) (by omega) htails
  obtain ⟨-, htails2⟩ := abiBytesTail_append_inj (by omega) (by omega) htails1
  exact (abiBytesTail_append_inj (by omega) (by omega) htails2).1

private theorem deposit_selector_frame_facts {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (htarget : sevm.currentTarget = depositAddr)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (executed : Exec 0 sevm pre (.ok post)) :
    BeaconDeposit.oneEther ≤ sevm.value.toNat ∧
    sevm.value.toNat % BeaconDeposit.oneGwei = 0 ∧
    sevm.value.toNat / BeaconDeposit.oneGwei ≤ 2 ^ 64 - 1 ∧
    ∀ ev, post.logs.drop pre.logs.length = [BeaconDeposit.depositEventLog depositAddr ev] →
      ev.amount = BeaconDeposit.le64 (sevm.value.toNat / BeaconDeposit.oneGwei) := by
  obtain ⟨f, found, run⟩ := (lift_sound_in_any_rules hcode executed).mono StepIn.toRun
  have root : prog[0]? = some t_0000_c0 := rfl
  rw [root] at found
  cases found
  rw [St.self hstack hmem] at run
  obtain ⟨k, _, wrapper, _, isDeposit, found, run⟩ := safe_dispatch run
  have hk : k = 32 := isDeposit.mpr hsel
  subst hk
  have hw : wrapper = t_00a4_c32 := by
    have at32 : prog[32]? = some t_00a4_c32 := rfl
    rw [at32] at found
    exact (Option.some.inj found).symm
  subst hw
  obtain ⟨_, _, _, body, _, logs⟩ := safe_decoder_any_data run
  obtain ⟨_, _, _, hlow, hmod, hhigh, b1, m1, _, kept1, mem1, body1⟩ :=
    safe_guards_any_data hfork body
  obtain ⟨b2, m2, _, kept2, mem2, body2⟩ := safe_event mem1 body1
  let ev₀ := bodyEvent sevm (argPtr sevm 0) (argPtr sevm 1) (argPtr sevm 2)
    (gweiAmount sevm) (pre.getStorVal sevm.currentTarget solCountSlot)
  have lengths : ev₀.pubkey.length = 48 ∧ ev₀.withdrawal_credentials.length = 32 ∧
      ev₀.amount.length = 8 ∧ ev₀.signature.length = 96 ∧ ev₀.index.length = 8 := by
    simp only [ev₀, bodyEvent, List.length_sliceD, BeaconDeposit.le64, List.length_cons,
      List.length_nil, Nat.reduceAdd, and_self]
  have hlen₀ := BeaconDeposit.abiDepositEvent_length ev₀ lengths.1 lengths.2.1
    lengths.2.2.1 lengths.2.2.2.1 lengths.2.2.2.2
  have eventLogs := event_logs hlen₀ mem2 body2
  simp only [Outcome.devm] at eventLogs
  have hpostLogs : post.logs = pre.logs ++ [BeaconDeposit.depositEventLog depositAddr ev₀] := by
    rw [logs, eventLogs, kept2.logs, kept1.logs, afterSload_logs, htarget]
    rfl
  have hgwei : (gweiAmount sevm).toNat = sevm.value.toNat / Blanc.BeaconDeposit.oneGwei := by
    unfold gweiAmount
    rw [B256.toNat_div (by decide)]
    rfl
  refine ⟨hlow, hmod, by unfold BeaconDeposit.oneGwei; omega, ?_⟩
  intro ev hfl
  rw [hpostLogs, List.drop_left] at hfl
  have hlogEq := List.singleton_inj.mp hfl
  have hdataEq : BeaconDeposit.abiDepositEvent ev = BeaconDeposit.abiDepositEvent ev₀ :=
    (congrArg Log.data hlogEq).symm
  rw [abiDepositEvent_amount_eq hlen₀ hdataEq]
  change BeaconDeposit.le64 (gweiAmount sevm).toNat = _
  rw [hgwei]

/-- **D-S6.** Kept deposit balance lower bound and per-frame deposit-value/amount attribution. -/
theorem d_s6 : D_S6 := by
  intro cfg start stop blocks kept forks installed senders roots credits
  refine ⟨kept.bal_covers depositKeptValue installed depositAddr_not_precomp senders roots credits,
    ?_⟩
  intro b hb fr hfr hsel
  obtain ⟨_, entry⟩ := kept.entry_in installed beaconInstalledCertH.nonempty
    beaconInstalledCertH.notDelegation b hb fr hfr
  have fresh := kept.fresh depositAddr b hb fr hfr
  rcases fr with ⟨pc, sevm, pre, out, run, committed⟩
  cases out with
  | error _ => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      have hpc : pc = 0 := entry.pc
      subst hpc
      have hfork : CoveredFork sevm.benvStat.fork := by
        rw [entry.benvStat]
        exact forks b hb
      obtain ⟨hlow, hmod, hhigh, hev⟩ :=
        deposit_selector_frame_facts entry.code hfork entry.target fresh.1 fresh.2 hsel run
      refine ⟨hlow, hmod, hhigh, fun ev hfl => hev ev ?_⟩
      simpa only [frameLogs, Exec.Frame.post, Execution.committedPost] using hfl

/-- Alias matching the corpus matrix naming convention. -/
theorem D_S6_proved : D_S6 := d_s6

end Blanc.Composition.DepositValue
