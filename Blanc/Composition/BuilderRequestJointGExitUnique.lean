import Blanc.Composition.BuilderRequestJointGExitAuth
import Blanc.Composition.BuilderRequestJointGBalance

/-!
# B4 unique resolution and B3's caller line over a valid Gloas joint chain

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B3, B4).

* `ValidJointG.exit_resolution_unique` (B4, G3-01's named clause, audit S3): when an exit initiates for index `i`
  at a Gloas step, `i` is the only builder with the request's pubkey in the state the exit trace reads. First
  match (`classifyBuilderExit_meaning`, through `ValidJointG.exit_authorization`) excludes the indices below `i`;
  G3-01 `BuilderPubkeysUnique`, carried along the run by `ValidJointG.gInv_pre` and along the step's deposit and
  exit loops (`builderExitTrace_pubkeysUnique`), excludes those above.
* `ValidJointG.exit_authorization_caller` (B3, conformance review NIT 10): `ValidJointG.exit_authorization` with
  the frozen line `req.source_address = f.sevm.caller`, from `Exit.Record.out = source ++ pubkey` and the
  serialization's first 20 bytes.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace ChainLink Blanc JauneConsensus.Facts.Gloas Occurrence
open Blanc.Composition.BuilderRequestPublic (keptAt exitAddr)

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## G3-01 along a step's builder-request loops -/

theorem traceLast_inv {σ : Type} (I : σ → Prop) {d : σ} {tr : List σ} (hd : I d)
    (htr : ∀ (k : Nat) (m : σ), tr[k]? = some m → I m) : I (traceLast d tr) := by
  unfold traceLast
  cases h : tr.getLast? with
  | none => exact hd
  | some x =>
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.mem_of_getLast? h)
    exact htr k x hk

/-- G3-01 holds at every state of a step's builder-exit trace when it holds at the state the traces start from:
the payment settlement and the validator request loops keep the registry (`applyParentPrefix_core`), a builder
deposit registers only a fresh pubkey or tops up (`depReq_pubkeysUnique`), and an exit writes only
`withdrawable_epoch` (`exitReq_pubkeysUnique`). -/
theorem builderExitTrace_pubkeysUnique {st : Gloas.BeaconState P} {b : Gloas.SignedBeaconBlock P}
    {tr : List (Gloas.BeaconState P)} (h : builderExitTrace ccfg bls st b = .ok tr)
    (hu : Inv.BuilderPubkeysUnique st) :
    ∀ (k : Nat) (m : Gloas.BeaconState P), tr[k]? = some m → Inv.BuilderPubkeysUnique m := by
  obtain ⟨trD, hD, hE, -⟩ := builderExitTrace_ok h
  have hDu : ∀ (k : Nat) (m : Gloas.BeaconState P), trD[k]? = some m → Inv.BuilderPubkeysUnique m := by
    rcases builderDepositTrace_ok hD with ⟨-, -, rfl⟩ | ⟨s0, hs0, hs⟩
    · intro k m hk
      cases k with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; exact hk ▸ hu
      | succ k => simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hk
    · have hu0 : Inv.BuilderPubkeysUnique s0 :=
        Inv.pubkeysUnique_of_eq (Inv.applyParentPrefix_core _ _ _ _ hs0).1 hu
      exact scanM_inv Inv.BuilderPubkeysUnique (fun _ _ _ hI hm => Inv.depReq_pubkeysUnique hm hI) _ hu0 hs
  exact scanM_inv Inv.BuilderPubkeysUnique (fun _ _ _ hI hm => Inv.exitReq_pubkeysUnique hm hI) _
    (traceLast_inv _ hu hDu) hE

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- **B4: unique resolution (G3-01's named clause).** Every builder exit initiated at a Gloas step `j` of a valid
joint chain consumes the builder exit request `req` at exit-trace position `k`, classified `initiate i` at the trace
state `m = tr[k]`, and `i` is the only index of `m`'s registry holding `req.pubkey`. Any `bls`. -/
theorem exit_resolution_unique (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D)) {i : Nat}
    (initiated : ExitInitiated D.preB D.postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderExitRequest) (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
      D.builderExits[k]? = some req ∧
      builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
      classifyBuilderExit ccfg m req = .ok (.initiate i) ∧
      ∀ (i' : Nat) (b' : Gloas.Builder), m.builders.toArray[i']? = some b' → b'.pubkey = req.pubkey → i' = i := by
  obtain ⟨k, req, tr, m, -, hreq, htr, hm, -, hcl, -, hfm, -⟩ := v.exit_authorization stepD initiated
  have hu0 : Inv.BuilderPubkeysUnique D.postSlots :=
    Inv.pubkeysUnique_of_eq D.postSlots_builders (v.gInv_pre stepD).1
  have hu := builderExitTrace_pubkeysUnique htr hu0 k m hm
  obtain ⟨⟨b, hb, hpk⟩, hlt⟩ := firstMatch_some hfm
  refine ⟨k, req, tr, m, hreq, htr, hm, hcl, fun i' b' hb' hpk' => ?_⟩
  rcases Nat.lt_trichotomy i' i with h | h | h
  · exact absurd hpk' (hlt i' h b' hb')
  · exact h
  · exact absurd (hpk.trans hpk'.symm) (hu i i' b b' h hb hb')

/-- **B3: exit authorization, with the recorded caller.** `exit_authorization` together with the frozen line
`req.source_address = f.sevm.caller`: the request's source address is the caller of the kept frame the exit
contract recorded it from. -/
theorem exit_authorization_caller (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D)) {i : Nat}
    (initiated : ExitInitiated D.preB D.postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderExitRequest) (tr : List (Gloas.BeaconState P)) (m m' : Gloas.BeaconState P),
      D.builderExits[k]? = some req ∧
      builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
      classifyBuilderExit ccfg m req = .ok (.initiate i) ∧
      (D.isFull ∧ ∃ bi b, v.run.payloadIndex j = bi ∧ v.blocks[v.preBlocks.length + bi]? = some b ∧
        (Exit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
        (Exit.Indexed.submissions v.blocks)[(Exit.Indexed.emissions
          (v.blocks.take (v.preBlocks.length + bi))).length + k]? = some (Ssz.serialize req)) ∧
      firstMatch m.builders req.pubkey = some i ∧
      (∃ (b : Gloas.Builder) (bi : Gloas.BuilderIndex), m.builders.toArray[i]? = some b ∧
        b.execution_address = req.source_address ∧ U64.ofNat? i "BuilderIndex" = .ok bi ∧
        Gloas.isActiveBuilder m bi = .ok true) ∧
      (Ssz.serialize req).take 20 = req.source_address.toBytes ∧
      ∃ (r : Exit.Record) (f : Exec.Frame), f ∈ keptAt v.blocks exitAddr ∧
        submittedBy Exit.contract f = some r ∧ Ssz.serialize req = Exit.Record.out r ∧
        r.source = f.sevm.caller ∧ req.source_address = f.sevm.caller := by
  obtain ⟨k, req, tr, m, m', hreq, htr, hm, hm', hcl, hpos, hfm, hb, htake, r, f, hf, hsub, hout, hsrc⟩ :=
    v.exit_authorization stepD initiated
  refine ⟨k, req, tr, m, m', hreq, htr, hm, hm', hcl, hpos, hfm, hb, htake, r, f, hf, hsub, hout, hsrc, ?_⟩
  have hlen : r.source.toBytes.length = 20 := by
    simp only [Adr.toBytes, List.length_append, UInt32.length_toBytes, B128.length_toBytes]
  have h20 : (Ssz.serialize req).take 20 = r.source.toBytes := by
    rw [hout]; unfold Exit.Record.out; exact List.take_left' hlen
  rw [← hsrc]
  exact Blanc.ConsensusSsz.adr_toBytes_injective (htake.symm.trans h20)

end ValidJointG

end Blanc.Lift.BuilderRequest
