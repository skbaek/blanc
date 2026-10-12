import Blanc.Lift.BeaconDeposit.Jumps
import Blanc.Lift.BeaconDeposit.Body
import Blanc.Lift.BeaconDeposit.DepositDecode

/-!
# A model-accepted deposit, as a real execution of the deployed runtime (P2, B3 liveness)

The dispatcher (`dispatch_deposit`, 95 gas), the ABI decoder (`deposit_wrapper`, 560 gas), and the
body (`deposit_body_runExact`) compose into a gas-exact run of the whole lifted program; the
kernel-checked converse bridge `exec_of_runExact` makes it a real Jaune execution of the deployed
bytes.  When the model accepts the calldata-decoded deposit, the execution succeeds, the
contract's new storage abstracts to the model's new state and differs from the old one exactly at
the count slot and the one branch slot the model writes, and exactly the model's `DepositEvent`
log is appended.  Under the storage abstraction `SolInv … history`, the post storage satisfies
`SolInv` for the history extended by the model's reconstructed node.  Counterpart of the port's
`deposit_success_runCompiled` / `deposit_success_artifactInv`.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- The exact gas of a successful deposit frame: dispatcher 95, decoder 560, the wrapper's
closing `JUMPDEST` 1, and the body. -/
def depositGas (sevm : Sevm) (b : Devm) : Nat := 656 + bodyGas sevm b

/-- `depositGas` with the body's two `SSTORE`s priced from supplied original words
(`bodyGasOf`). -/
def depositGasOf (origLive origCount : B256) (sevm : Sevm) (b : Devm) : Nat :=
  656 + bodyGasOf origLive origCount sevm b

theorem depositGas_eq_of (sevm : Sevm) (b : Devm) :
    depositGas sevm b =
      depositGasOf (getOrigStorVal sevm sevm.currentTarget (solBranchSlot (bodyDepth sevm b)))
        (getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm b := rfl

theorem deposit_runExact (sevm : Sevm) (base : Devm) (G : Nat)
    (s' : BeaconDeposit.Acc) (ev : BeaconDeposit.DepositEvent) {origLive origCount : B256}
    (horigLive : base.getOrigStorVal sevm sevm.currentTarget
      (solBranchSlot (bodyDepth sevm base)) = origLive)
    (horigCount : base.getOrigStorVal sevm sevm.currentTarget solCountSlot = origCount)
    (hdataLength : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (hdec : DepositDecodable sevm)
    (hOk : BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor base sevm.currentTarget))
      (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm) sevm.value.toNat =
        .ok (s', ev))
    (hsha : ShaReady sevm base) (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false)
    (hsentryLive : gCallStipend < G + 52 + bodyLiveCostOf origLive sevm base)
    (hsentryCount : gCallStipend < G + 4 + bodyInsertGasOf origLive sevm base +
      countStoreCostOf origCount (bodyCount sevm base))
    (hbound : G + 1 + bodyGasOf origLive origCount sevm base < 2 ^ 256) :
    ∃ b' M', SProg.RunExact prog sevm
        (St base [] Mem.empty (G + depositGasOf origLive origCount sevm base))
        (St b' [Sevm.selector sevm] M' G) ∧
      Devm.getStor b' sevm.currentTarget = bodyStor sevm base ∧
      solAcc (Devm.getStor b' sevm.currentTarget) = s' ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor b' a = Devm.getStor base a) ∧
      b'.logs = base.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] := by
  obtain ⟨b', M', hbody, hst, hacc, hother, hlogs, -⟩ := deposit_body_runExact sevm base
    (Sevm.selector sevm) G s' ev horigLive horigCount hdec hcd hOk hsha hdepth hstatic
    hsentryLive hsentryCount hbound
  obtain ⟨post, hw, rfl⟩ := deposit_wrapper (g' := G) hdec hcd hbody
  have hsel' : Sevm.selector sevm = 0x22895118 :=
    hsel.trans Blanc.BeaconDeposit.depositSelector_eq
  have hd := dispatch_deposit (b := base) hdataLength hcd hsel' hw
  refine ⟨b', M', ⟨_, rfl, ?_⟩, hst, hacc, hother, hlogs⟩
  rw [show G + depositGasOf origLive origCount sevm base =
      G + 1 + bodyGasOf origLive origCount sevm base + depositDecodeGas + 95 by
    unfold depositGasOf depositDecodeGas; omega]
  exact hd

/-- **P2 / B3 (liveness).**  A deposit the model accepts, from a storage satisfying the
abstraction for `history`, is a real execution of the deployed runtime that ends in the
abstraction for `history ++ [node]`, with exactly the model's event appended.  The body's two
`SSTORE`s are priced from the entry machine's original reads `base.getOrigStorVal` of the stored
branch slot and of the count slot, which is what Jaune charges (`0` at an account created in
this transaction); decision blanc-repin-os-optionA-delegation-20261012, Option A. -/
theorem deposit_exec_solInv (sevm : Sevm) (base : Devm) (G : Nat) (history : List B256)
    (s' : BeaconDeposit.Acc) (ev : BeaconDeposit.DepositEvent)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (hdec : DepositDecodable sevm)
    (hinv : SolInv (Devm.getStor base sevm.currentTarget) history)
    (hOk : BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor base sevm.currentTarget))
      (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm) sevm.value.toNat =
        .ok (s', ev))
    (hsha : ShaReady sevm base) (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false)
    (hsentryLive : gCallStipend < G + 52 +
      bodyLiveCostOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base))) sevm base)
    (hsentryCount : gCallStipend < G + 4 +
      bodyInsertGasOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base))) sevm base +
      countStoreCostOf (base.getOrigStorVal sevm sevm.currentTarget solCountSlot)
        (bodyCount sevm base))
    (hbound : G + 1 + bodyGasOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base)))
      (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm (St base [] Mem.empty
        (G + depositGasOf (base.getOrigStorVal sevm sevm.currentTarget
          (solBranchSlot (bodyDepth sevm base)))
          (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base)) (.ok post)) ∧
      post.gasLeft = G ∧
      solAcc (Devm.getStor post sevm.currentTarget) = s' ∧
      SolInv (Devm.getStor post sevm.currentTarget)
        (history ++ [BeaconDeposit.depositDataNode Bytes.sha256 (argBytes sevm 0)
          (argBytes sevm 1) (argBytes sevm 2)
          (BeaconDeposit.le64 (sevm.value.toNat / BeaconDeposit.oneGwei))]) ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor base a) ∧
      post.logs = base.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] := by
  obtain ⟨b', M', hrun, hst, hacc, hother, hlogs⟩ := deposit_runExact sevm base G s' ev rfl rfl
    hdataLength hcd hsel hdec hOk hsha hdepth hstatic hsentryLive hsentryCount hbound
  refine ⟨St b' [Sevm.selector sevm] M' G, exec_of_runExact hcode hsha.fork hrun, rfl, hacc,
    ⟨fun h' hh' => ?_, ?_⟩, hother, hlogs⟩
  · -- the zero-hash table: the body writes only the count slot and one branch slot below 32
    have hn : bodyDepth sevm base < 32 := by
      obtain ⟨-, -, -, -, -, -, -, hcap, -⟩ := deposit_ok_facts hOk
      have hc : (bodyCount sevm base).toNat < 2 ^ 32 - 1 := hcap
      exact insertDepth_lt 32 _ (by omega) (by omega)
    obtain ⟨n1, n2⟩ := solZeroHashSlot_ne hh' hn
    show (Devm.getStor b' sevm.currentTarget).get _ = _
    rw [hst, bodyStor, Stor.get_set_ne _ (Ne.symm n1), Stor.get_set_ne _ (Ne.symm n2)]
    exact hinv.1 h' hh'
  · show BeaconDeposit.Inv Bytes.sha256 (solAcc (Devm.getStor b' sevm.currentTarget)) _
    rw [hacc]
    exact BeaconDeposit.deposit_inv Bytes.sha256 _ _ _ _ _ _ _ _ _ hinv.2 hOk

/-! ## The pre-re-pin header, refuted (evidence)

Under Jaune `ca9f27d` an `SSTORE` is priced from the machine original read
`Devm.getOrigStorVal`, which is `0` at an account in `createdAccounts`.  The pre-re-pin header
priced the body's two `SSTORE`s from the static snapshot read `getOrigStorVal` and pinned the
residual gas to `G`.  At a frame whose owner was created in this transaction, whose snapshot
count equals its current nonzero count, and whose stored branch slot has a zero snapshot, the
static budget exceeds the machine budget by exactly `2800` (`depositGas_created_gap`), and the
execution from that budget is unique (`Exec.result_unique`), so it leaves `G + 2800`, not `G`
(`not_oldDepositExecSolInv_of_gap`).  Evidence only: nothing uses these declarations. -/

/-- The pre-re-pin header of `deposit_exec_solInv`, verbatim (binders turned into a
proposition). -/
def OldDepositExecSolInv : Prop :=
  ∀ (sevm : Sevm) (base : Devm) (G : Nat) (history : List B256)
    (s' : BeaconDeposit.Acc) (ev : BeaconDeposit.DepositEvent)
    (_hcode : sevm.code = code)
    (_hdataLength : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
    (_hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (_hdec : DepositDecodable sevm)
    (_hinv : SolInv (Devm.getStor base sevm.currentTarget) history)
    (_hOk : BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor base sevm.currentTarget))
      (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm) sevm.value.toNat =
        .ok (s', ev))
    (_hsha : ShaReady sevm base) (_hdepth : sevm.depth ≠ 0) (_hstatic : sevm.isStatic = false)
    (_hsentryLive : gCallStipend < G + 52 + bodyLiveCost sevm base)
    (_hsentryCount : gCallStipend < G + 4 + bodyInsertGas sevm base +
      countStoreCost sevm (bodyCount sevm base))
    (_hbound : G + 1 + bodyGas sevm base < 2 ^ 256),
    ∃ post, Nonempty (Exec 0 sevm (St base [] Mem.empty (G + depositGas sevm base)) (.ok post)) ∧
      post.gasLeft = G ∧
      solAcc (Devm.getStor post sevm.currentTarget) = s' ∧
      SolInv (Devm.getStor post sevm.currentTarget)
        (history ++ [BeaconDeposit.depositDataNode Bytes.sha256 (argBytes sevm 0)
          (argBytes sevm 1) (argBytes sevm 2)
          (BeaconDeposit.le64 (sevm.value.toNat / BeaconDeposit.oneGwei))]) ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor base a) ∧
      post.logs = base.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev]

/-- **The static budget overpays a created owner by `2800`.**  At an owner created in this
transaction, with snapshot count equal to the current nonzero count and a zero snapshot at the
stored branch slot, `depositGas` (static snapshot prices) is the machine-priced `depositGasOf`
plus `2800`: the count `SSTORE` is a clean `2900` update to the snapshot but a dirty `100` write
to the machine read `0`. -/
theorem depositGas_created_gap (sevm : Sevm) (base : Devm)
    (hcreated : sevm.currentTarget ∈ base.createdAccounts)
    (hcount : getOrigStorVal sevm sevm.currentTarget solCountSlot = bodyCount sevm base)
    (hw : bodyCount sevm base ≠ 0)
    (hlive : getOrigStorVal sevm sevm.currentTarget (solBranchSlot (bodyDepth sevm base)) = 0) :
    depositGas sevm base =
      depositGasOf (base.getOrigStorVal sevm sevm.currentTarget
          (solBranchSlot (bodyDepth sevm base)))
        (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base + 2800 := by
  have hm : ∀ k, base.getOrigStorVal sevm sevm.currentTarget k = 0 := fun k => by
    unfold Devm.getOrigStorVal
    exact ite_eq_left hcreated
  have hne : bodyCount sevm base ≠ 1 + bodyCount sevm base := by
    intro h
    have h' := congrArg B256.toNat h
    rw [B256.toNat_add, show (1 : B256).toNat = 1 from rfl] at h'
    have := B256.toNat_lt (bodyCount sevm base)
    unfold Nat.lo at h'
    by_cases hlt : 1 + (bodyCount sevm base).toNat < 2 ^ 256
    · rw [Nat.mod_eq_of_lt hlt] at h'
      omega
    · have he : 1 + (bodyCount sevm base).toNat = 2 ^ 256 := by omega
      rw [he, Nat.mod_self] at h'
      omega
  rw [depositGas_eq_of, hlive, hm, hm, hcount]
  unfold depositGasOf bodyGasOf countStoreCostOf
  have hc : sstoreValueCost (bodyCount sevm base) (bodyCount sevm base)
      (1 + bodyCount sevm base) = 2900 := by
    unfold sstoreValueCost
    rw [ite_eq_left ⟨rfl, hne⟩, ite_eq_right hw]
    rfl
  have hd : sstoreValueCost 0 (bodyCount sevm base) (1 + bodyCount sevm base) = 100 := by
    unfold sstoreValueCost
    rw [ite_eq_right (fun h => hw h.1.symm)]
    rfl
  rw [hc, hd]
  omega

/-- **The pre-re-pin header is false at any frame where the budgets differ.**  Given the
premises of both headers at one frame, with the static budget `d ≠ 0` above the machine budget,
the restated `deposit_exec_solInv` runs the frame from the static budget to residual `G + d`,
and the run is unique, so the old conclusion's residual `G` is impossible. -/
theorem not_oldDepositExecSolInv_of_gap {sevm : Sevm} {base : Devm} {G d : Nat}
    {history : List B256} {s' : BeaconDeposit.Acc} {ev : BeaconDeposit.DepositEvent}
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (hdec : DepositDecodable sevm)
    (hinv : SolInv (Devm.getStor base sevm.currentTarget) history)
    (hOk : BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor base sevm.currentTarget))
      (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm) sevm.value.toNat =
        .ok (s', ev))
    (hsha : ShaReady sevm base) (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false)
    (hsentryLive : gCallStipend < G + 52 + bodyLiveCost sevm base)
    (hsentryCount : gCallStipend < G + 4 + bodyInsertGas sevm base +
      countStoreCost sevm (bodyCount sevm base))
    (hbound : G + 1 + bodyGas sevm base < 2 ^ 256)
    (hsentryLive' : gCallStipend < (G + d) + 52 +
      bodyLiveCostOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base))) sevm base)
    (hsentryCount' : gCallStipend < (G + d) + 4 +
      bodyInsertGasOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base))) sevm base +
      countStoreCostOf (base.getOrigStorVal sevm sevm.currentTarget solCountSlot)
        (bodyCount sevm base))
    (hgap : depositGas sevm base =
      depositGasOf (base.getOrigStorVal sevm sevm.currentTarget
          (solBranchSlot (bodyDepth sevm base)))
        (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base + d)
    (hd : d ≠ 0) : ¬ OldDepositExecSolInv := by
  intro H
  obtain ⟨post, ⟨hex⟩, hg, -⟩ := H sevm base G history s' ev hcode hdataLength hcd hsel hdec
    hinv hOk hsha hdepth hstatic hsentryLive hsentryCount hbound
  have hbound' : (G + d) + 1 + bodyGasOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base)))
      (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base < 2 ^ 256 := by
    unfold depositGas depositGasOf at hgap
    omega
  obtain ⟨post', ⟨hex'⟩, hg', -⟩ := deposit_exec_solInv sevm base (G + d) history s' ev hcode
    hdataLength hcd hsel hdec hinv hOk hsha hdepth hstatic hsentryLive' hsentryCount' hbound'
  rw [hgap, show ∀ x, G + (x + d) = G + d + x from fun x => by omega] at hex
  have he := Blanc.Exec.result_unique hex hex'
  cases he
  omega

end Blanc.Lift.BeaconDeposit
