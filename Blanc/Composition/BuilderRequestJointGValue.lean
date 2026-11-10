import Blanc.Composition.BuilderRequestJointG
import Blanc.Lift.VyperRawCall

/-!
# B2's value clause over a valid Gloas joint chain: `ValidJointG.deposit_value`

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B2, "B2's value
clause", SF-8; conformance fix SF6).

* The builder contracts' value is kept over the joint history (O37's `value_kept`, instantiated for both contracts
  by `value_kept_bridge`): its premises are `ValidJointG`'s `codes`, `roots`, `depositNoSender`, `exitNoSender` and
  `creditsFit`.
* Every kept deposit submission credits at most what its frame paid: the record's amount bytes, big-endian, times
  `10^9`, plus the quoted fee, is at most the frame's value (`Deposit.Admits`, from the submission law of the
  history's delivery chain, `Deposit.history_chain`, on `ValidJointG.depositClean`).

So what the contract keeps beyond the credited stake (the fee, any excess, and the stakes of records the consensus
layer ignores) is an execution-side balance fact, and the consensus layer never credits more than `amount · 10^9`
per submission.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace ChainLink Blanc
open Blanc.Composition.BuilderRequestPublic (depositAddr exitAddr keptAt feesPaidAt value_kept_bridge)

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
  {anchor final : GJointState P}

/-- The wei a 184-byte submission credits is its record's amount bytes, big-endian, times `10^9`. -/
theorem Deposit.creditOf_eq_amount (s : Sevm) (h : s.data.length = 184) :
    Deposit.creditOf s.data = Bytes.toNat (Deposit.recordOf s h).amount * 10 ^ 9 := by
  obtain ⟨hb, hc⟩ := Deposit.credit_is_declared s h
  rw [← hc, B256.toNat_eq_toBytes, hb, Bytes.toNat_append, Bytes.toNat_replicate_zero, Nat.zero_mul, Nat.zero_add]

/-- **B2's value clause** (`bls` any). Over the joint history from the checkpoint to the final built-upon chain:

* the deposit contract's balance at the end is at least its balance at the checkpoint plus every value its kept
  frames carried (`feesPaidAt`: each deposit plus its fee), and likewise for the exit contract (`value_kept`);
* every kept frame at the deposit contract with a submission's 184 calldata bytes carries at least its record's
  amount (big-endian gwei) times `10^9` wei, and the guards admitted it at some quoted fee (`Deposit.Admits`: the
  value covers the credit plus the fee). -/
theorem ValidJointG.deposit_value (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    ((checkpoint.state.get depositAddr).bal).toNat + feesPaidAt v.blocks depositAddr ≤
        ((final.exec.state.get depositAddr).bal).toNat ∧
      ((checkpoint.state.get exitAddr).bal).toNat + feesPaidAt v.blocks exitAddr ≤
        ((final.exec.state.get exitAddr).bal).toNat ∧
      ∀ f ∈ keptAt v.blocks depositAddr, ∀ h : f.sevm.data.length = 184,
        Bytes.toNat (Deposit.recordOf f.sevm h).amount * 10 ^ 9 ≤ f.sevm.value.toNat ∧
          ∃ fee : B256, Deposit.Admits f.sevm.data f.sevm.value fee := by
  refine ⟨value_kept_bridge v.codes v.roots depositAddr List.mem_cons_self v.depositNoSender
      v.creditsFit.1,
    value_kept_bridge v.codes v.roots exitAddr (List.mem_cons_of_mem _ List.mem_cons_self)
      v.exitNoSender v.creditsFit.2, fun f hmem hlen => ?_⟩
  have H := v.depositClean
  obtain ⟨frames, -, corr, -⟩ := Deposit.history_chain H.history H.installed H.fresh H.noSystemCode H.senders
    H.authorities H.creates
  obtain ⟨xs, ys, hsplit0⟩ := List.mem_iff_append.mp hmem
  have hsplit : ChainLink.History.kept Deposit.contract.address v.blocks = xs ++ f :: ys := hsplit0
  have hcorr : ChainLink.Corresponds Deposit.contract frames (xs ++ f :: ys) := by
    rw [← hsplit]
    exact corr
  obtain ⟨gs, g, hs, rfl, left, m, -⟩ := hcorr.split
  have hlen' : f.sevm.data.length = Deposit.contract.payload := hlen
  have hkev : ChainLink.keptEvent Deposit.contract f = .submission (Deposit.contract.recordOf f.sevm hlen') :=
    ChainLink.keptEvent_of_length hlen'
  cases hg : g with
  | submission sevm pre post l i o rules tgt caller law =>
    have hval : sevm.value.toNat ≤ f.sevm.value.toNat := by
      have h := m.value
      rw [hg] at h
      exact h
    have h1 := m.event
    rw [hg, hkev] at h1
    change Delivery.Event.submission _ = _ at h1
    injection h1 with hr
    have hd : sevm.data = f.sevm.data := by
      have := congrArg Deposit.Record.data hr
      rwa [Deposit.recordOf_data, Deposit.recordOf_data] at this
    have hco := law.admitted.covered
    have hcr := law.admitted.credited
    rw [Deposit.creditedWei_eq, hd] at hco hcr
    rw [← Deposit.creditOf_eq_amount f.sevm hlen]
    exact ⟨by omega, o / 17, hcr, by omega⟩
  | feeRead sevm pre post l i o rules tgt caller law =>
    have h1 := m.event
    rw [hg, hkev] at h1
    change Delivery.Event.feeRead = .submission _ at h1
    cases h1
  | system benv data post out fork installed length run =>
    have h1 := m.event
    rw [hg, hkev] at h1
    change Delivery.Event.system _ = .submission _ at h1
    cases h1

end Blanc.Lift.BuilderRequest
