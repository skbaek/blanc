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

theorem deposit_runExact (sevm : Sevm) (base : Devm) (G : Nat)
    (s' : BeaconDeposit.Acc) (ev : BeaconDeposit.DepositEvent)
    (hdataLength : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (hdec : DepositDecodable sevm)
    (hOk : BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor base sevm.currentTarget))
      (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm) sevm.value.toNat =
        .ok (s', ev))
    (hsha : ShaReady sevm base) (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false)
    (hsentryLive : gCallStipend < G + 52 + bodyLiveCost sevm base)
    (hsentryCount : gCallStipend < G + 4 + bodyInsertGas sevm base +
      countStoreCost sevm (bodyCount sevm base))
    (hbound : G + 1 + bodyGas sevm base < 2 ^ 256) :
    ∃ b' M', SProg.RunExact prog sevm (St base [] Mem.empty (G + depositGas sevm base))
        (St b' [Sevm.selector sevm] M' G) ∧
      Devm.getStor b' sevm.currentTarget = bodyStor sevm base ∧
      solAcc (Devm.getStor b' sevm.currentTarget) = s' ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor b' a = Devm.getStor base a) ∧
      b'.logs = base.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] := by
  obtain ⟨b', M', hbody, hst, hacc, hother, hlogs, -⟩ := deposit_body_runExact sevm base
    (Sevm.selector sevm) G s' ev hdec hcd hOk hsha hdepth hstatic hsentryLive hsentryCount hbound
  obtain ⟨post, hw, rfl⟩ := deposit_wrapper (g' := G) hdec hcd hbody
  have hsel' : Sevm.selector sevm = 0x22895118 :=
    hsel.trans Blanc.BeaconDeposit.depositSelector_eq
  have hd := dispatch_deposit (b := base) hdataLength hcd hsel' hw
  refine ⟨b', M', ⟨_, rfl, ?_⟩, hst, hacc, hother, hlogs⟩
  rw [show G + depositGas sevm base = G + 1 + bodyGas sevm base + depositDecodeGas + 95 by
    unfold depositGas depositDecodeGas; omega]
  exact hd

/-- **P2 / B3 (liveness).**  A deposit the model accepts, from a storage satisfying the
abstraction for `history`, is a real execution of the deployed runtime that ends in the
abstraction for `history ++ [node]`, with exactly the model's event appended. -/
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
    (hsentryLive : gCallStipend < G + 52 + bodyLiveCost sevm base)
    (hsentryCount : gCallStipend < G + 4 + bodyInsertGas sevm base +
      countStoreCost sevm (bodyCount sevm base))
    (hbound : G + 1 + bodyGas sevm base < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm (St base [] Mem.empty (G + depositGas sevm base)) (.ok post)) ∧
      post.gasLeft = G ∧
      solAcc (Devm.getStor post sevm.currentTarget) = s' ∧
      SolInv (Devm.getStor post sevm.currentTarget)
        (history ++ [BeaconDeposit.depositDataNode Bytes.sha256 (argBytes sevm 0)
          (argBytes sevm 1) (argBytes sevm 2)
          (BeaconDeposit.le64 (sevm.value.toNat / BeaconDeposit.oneGwei))]) ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor base a) ∧
      post.logs = base.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] := by
  obtain ⟨b', M', hrun, hst, hacc, hother, hlogs⟩ := deposit_runExact sevm base G s' ev
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

end Blanc.Lift.BeaconDeposit
