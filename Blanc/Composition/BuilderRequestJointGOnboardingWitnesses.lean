import JauneConsensus.Facts.Gloas.Onboarding

/-!
# Closed witnesses for B1's fork step (conformance review SF8)

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B1, the fork controls).
Each class of Jaune's declarative `OnboardingSpec` occurs, on small closed pending-deposit queues under
`Config.mainnet`. Each witness builds the partition meeting the specification and, by `OnboardingSpec.unique`,
shows it is the only one, so the deposit lands in that class in every partition:

* `witness_register_topUp` (`bls = false`): a `0xB0` deposit with a valid signature lands in `R`, and a later
  deposit for the same pubkey with zero (non-builder) credentials lands in `T`;
* `witness_dropped` (`bls = true`): a `0xB0` deposit whose signature starts `0x00` (no compressed G2 point, so
  `blsVerify` rejects before any pairing, Jaune's `blsVerify_true_of_head_zero`) lands in `X`;
* `witness_kept`: a deposit for a validator pubkey and a non-`0xB0` deposit for a new pubkey land in `K`.

These are function-level: they are stated over the specification, not over a full `upgrade_to_gloas` run (whose
kernel cost, through `initialize_ptc_window`, is out of proportion). `upgradeToGloas_onboards` ties the
specification to the upgrade. The valid-signature case is at `bls = false`, where `blsVerify` accepts; a valid
signature at `bls = true` needs a real BLS key pair, which no closed witness here carries.
-/

namespace Blanc.Lift.BuilderRequest.OnboardingWitnesses

open Jaune JauneConsensus JauneConsensus.Facts.Gloas JauneConsensus.Facts.Gloas.Onboarding

variable {P : Preset}

/-- A 48-byte pubkey of the byte `x`. -/
def pk (x : UInt8) : BLSPubkey := ⟨Array.replicate 48 x, Array.size_replicate⟩

/-- A 96-byte signature of the byte `x`. -/
def sig (x : UInt8) : BLSSignature := ⟨Array.replicate 96 x, Array.size_replicate⟩

/-- Builder withdrawal credentials: `0xB0`, then zeros. -/
def wcBuilder : Bytes32 := B256.ofBytes (0xB0 :: List.replicate 31 0)

/-- A pending deposit at slot 0 with amount 0. -/
def dep (p : BLSPubkey) (wc : Bytes32) (s : BLSSignature) : PendingDeposit :=
  { pubkey := p, withdrawal_credentials := wc, amount := U64.zero, signature := s, slot := U64.zero }

def ctxOff : Ctx := { cfg := Config.mainnet, blsActive := false }
def ctxOn : Ctx := { cfg := Config.mainnet, blsActive := true }

theorem wcBuilder_isBuilder : Gloas.isBuilderWithdrawalCredential wcBuilder = true := by decide

theorem zero_notBuilder : Gloas.isBuilderWithdrawalCredential (0 : Bytes32) = false := by decide

theorem isPendingValidator_nil (ctx : Ctx) (p : BLSPubkey) :
    Gloas.isPendingValidator ctx #[] p = .ok false := rfl

theorem sig_off (p : BLSPubkey) (wc : Bytes32) (a : Gwei) (s : BLSSignature) :
    isValidDepositSignature ctxOff p wc a s = .ok true := rfl

theorem sig_on_head_zero (p : BLSPubkey) (wc : Bytes32) (a : Gwei) :
    isValidDepositSignature ctxOn p wc a (sig 0) = .ok false := by
  unfold isValidDepositSignature
  have h := blsVerify_true_of_head_zero p
    (computeSigningRoot ({ pubkey := p, withdrawal_credentials := wc, amount := a } : DepositMessage)
      (computeDomain DOMAIN_DEPOSIT ⟨Config.mainnet.GENESIS_FORK_VERSION.toArray, by decide⟩ (0 : B256)))
    (sig 0) rfl
  exact congrArg Except.ok h

/-! ## Register, then top up -/

/-- A registering `0xB0` deposit for `pk 1`, then a deposit for the same pubkey with zero credentials. -/
def qRT : List PendingDeposit := [dep (pk 1) wcBuilder (sig 7), dep (pk 1) 0 (sig 7)]

def i0 : Fin qRT.length := ⟨0, by decide⟩
def i1 : Fin qRT.length := ⟨1, by decide⟩

/-- **Witness: `R` and `T` occur** (`bls = false`). The first deposit registers, the second (same pubkey, zero
credentials) tops up, and this is the only partition. -/
theorem witness_register_topUp {e : Epoch} (he : computeEpochAtSlot P U64.zero = .ok e) :
    ∃ (b : Gloas.Builder) (addr : ExecutionAddress),
      OnboardingSpec P ctxOff [] qRT [] [i0] [i1] [] [b] [] ∧
      b = { pubkey := pk 1, version := Gloas.PAYLOAD_BUILDER_VERSION, execution_address := addr,
            balance := U64.zero, deposit_epoch := e, withdrawable_epoch := FAR_FUTURE_EPOCH } ∧
      ∀ (K R T X : List (Fin qRT.length)) (bs : List Gloas.Builder) (q : List PendingDeposit),
        OnboardingSpec P ctxOff [] qRT K R T X bs q → K = [] ∧ R = [i0] ∧ T = [i1] ∧ X = [] := by
  obtain ⟨addr, ha⟩ : ∃ a, Jaune.Bytes.toAdr? (wcBuilder.toBytes.drop 12) = some a :=
    Option.isSome_iff_exists.mp (by decide)
  have S : OnboardingSpec P ctxOff [] qRT [] [i0] [i1] []
      [{ pubkey := pk 1, version := Gloas.PAYLOAD_BUILDER_VERSION, execution_address := addr,
         balance := U64.zero, deposit_epoch := e, withdrawable_epoch := FAR_FUTURE_EPOCH }] [] := by
    refine ⟨(by decide), ⟨.nil, (by decide), (by decide), .nil⟩, fun t ht => (by cases ht), fun t ht => ?_,
      fun t ht => (by cases ht), fun t ht => ?_, rfl, .cons ⟨rfl, rfl, ha, he, rfl, ?_⟩ .nil⟩
    · simp only [List.mem_singleton] at ht
      subst ht
      have hr : regBefore qRT [i0] i0 = [] := by unfold regBefore; rfl
      exact ⟨List.not_mem_nil, by rw [hr]; exact List.not_mem_nil, wcBuilder_isBuilder,
        isPendingValidator_nil _ _, sig_off _ _ _ _⟩
    · simp only [List.mem_singleton] at ht
      subst ht
      have hr : regBefore qRT [i0] i1 = [qRT[i0].pubkey] := by unfold regBefore; rfl
      exact ⟨List.not_mem_nil, by rw [hr]; exact List.mem_singleton.mpr rfl⟩
    · rfl
  refine ⟨_, addr, S, rfl, fun K R T X bs q S' => ?_⟩
  have := S.unique S'
  simp only [Prod.mk.injEq] at this
  exact this

/-! ## Drop -/

/-- A `0xB0` deposit for a new pubkey whose signature starts `0x00`. -/
def qX : List PendingDeposit := [dep (pk 2) wcBuilder (sig 0)]

def j0 : Fin qX.length := ⟨0, by decide⟩

/-- **Witness: `X` occurs** (`bls = true`): the badly signed `0xB0` deposit is dropped (neither queued nor
registered), and this is the only partition. -/
theorem witness_dropped :
    OnboardingSpec P ctxOn [] qX [] [] [] [j0] [] [] ∧
      ∀ (K R T X : List (Fin qX.length)) (bs : List Gloas.Builder) (q : List PendingDeposit),
        OnboardingSpec P ctxOn [] qX K R T X bs q → K = [] ∧ R = [] ∧ T = [] ∧ X = [j0] := by
  have S : OnboardingSpec P ctxOn [] qX [] [] [] [j0] [] [] := by
    refine ⟨(by decide), ⟨.nil, .nil, .nil, (by decide)⟩, fun t ht => (by cases ht),
      fun t ht => (by cases ht), fun t ht => ?_, fun t ht => (by cases ht), rfl, .nil⟩
    simp only [List.mem_singleton] at ht
    subst ht
    have hr : regBefore qX [] j0 = [] := rfl
    exact ⟨List.not_mem_nil, by rw [hr]; exact List.not_mem_nil, wcBuilder_isBuilder,
      isPendingValidator_nil _ _, sig_on_head_zero _ _ _⟩
  refine ⟨S, fun K R T X bs q S' => ?_⟩
  have := S.unique S'
  simp only [Prod.mk.injEq] at this
  exact this

/-! ## Keep -/

/-- A deposit for the validator pubkey `pk 3` (builder credentials), then a zero-credential deposit for the new
pubkey `pk 4`. -/
def qK : List PendingDeposit := [dep (pk 3) wcBuilder (sig 7), dep (pk 4) 0 (sig 7)]

def k0 : Fin qK.length := ⟨0, by decide⟩
def k1 : Fin qK.length := ⟨1, by decide⟩

/-- **Witness: `K` occurs**: a validator-pubkey deposit (step 1, whatever its credentials) and a non-`0xB0` deposit
for a new pubkey (step 2) are kept, in order, and this is the only partition. Any `bls`. -/
theorem witness_kept (bls : Bool) :
    OnboardingSpec P { cfg := Config.mainnet, blsActive := bls } [pk 3] qK [k0, k1] [] [] [] [] qK ∧
      ∀ (K R T X : List (Fin qK.length)) (bs : List Gloas.Builder) (q : List PendingDeposit),
        OnboardingSpec P { cfg := Config.mainnet, blsActive := bls } [pk 3] qK K R T X bs q →
          K = [k0, k1] ∧ R = [] ∧ T = [] ∧ X = [] := by
  have S : OnboardingSpec P { cfg := Config.mainnet, blsActive := bls } [pk 3] qK [k0, k1] [] [] [] [] qK := by
    refine ⟨(by decide), ⟨(by decide), .nil, .nil, .nil⟩, fun t ht => ?_, fun t ht => (by cases ht),
      fun t ht => (by cases ht), fun t ht => (by cases ht), rfl, .nil⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (List.mem_singleton.mpr rfl)
    · exact Or.inr ⟨List.not_mem_nil, Or.inl zero_notBuilder⟩
  refine ⟨S, fun K R T X bs q S' => ?_⟩
  have := S.unique S'
  simp only [Prod.mk.injEq] at this
  exact this

end Blanc.Lift.BuilderRequest.OnboardingWitnesses
