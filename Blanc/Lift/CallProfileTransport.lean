import Blanc.Lift.GasErasureRun
import Blanc.Lift.ExactWalkCallChild

/-!
# Full-state transport for exact call profiles

Normalizing execution gas loses no other machine column. These lemmas preserve the complete
`Devm`, including all child-world, refund, access, state-gas and tracking metadata. They apply
to ordinary callees and identity-precompile resumes; no contract or selected opcode walk is
assumed here.
-/

namespace Blanc

open Jaune

/-- Equality modulo gas becomes literal equality after choosing a common gas value. -/
theorem Devm.EqModGas.withGasLeft_eq {a b : Devm} (h : EqModGas a b) (G : Nat) :
    a.withGasLeft G = b.withGasLeft G := by
  apply Devm.ext
  · apply Mach.ext
    · exact h.stack
    · exact h.memory
    · rfl
    · exact h.stateGas
  · apply Meta.ext
    · exact h.logs
    · exact h.refundCounter
    · exact h.output
    · exact h.accountsToDelete
    · exact h.returnData
    · exact h.error
    · exact h.accessedAddresses
    · exact h.accessedStorageKeys
    · exact h.createdAccounts
    · exact h.accountReads
    · exact h.storageReads
  · apply World.ext
    · exact h.state
    · exact h.transientStorage
    · exact h.storageWrites

/-- Literal equality after gas normalization proves agreement on every other column. -/
theorem Devm.EqModGas.of_normalized_eq {a b : Devm}
    (h : a.withGasLeft 0 = b.withGasLeft 0) : EqModGas a b := by
  have hz : EqModGas (a.withGasLeft 0) (b.withGasLeft 0) := h ▸ .refl _
  exact (Devm.EqModGas.withGasLeft a 0).trans
    (hz.trans (Devm.EqModGas.withGasLeft b 0).symm)

/-- Replacing stack and memory preserves full agreement modulo gas, at arbitrary residuals. -/
theorem Devm.EqModGas.st {a b : Devm} (h : EqModGas a b) (S : List B256) (M : Mem)
    (G H : Nat) : EqModGas (Lift.St a S M G) (Lift.St b S M H) := by
  apply of_normalized_eq
  change Lift.St (a.withGasLeft 0) S M 0 = Lift.St (b.withGasLeft 0) S M 0
  rw [h.withGasLeft_eq 0]

/-- Warming a callee preserves full agreement modulo gas. -/
theorem Devm.EqModGas.addAccessedAddress {a b : Devm} (h : EqModGas a b) (t : Adr) :
    EqModGas (Jaune.addAccessedAddress a t) (Jaune.addAccessedAddress b t) := by
  apply of_normalized_eq
  change Jaune.addAccessedAddress (a.withGasLeft 0) t =
    Jaune.addAccessedAddress (b.withGasLeft 0) t
  rw [h.withGasLeft_eq 0]

/-- Parent preparation changes only gas as the chosen forwarded charge changes. -/
theorem Devm.EqModGas.callSpawnParent {a b : Devm} (h : EqModGas a b)
    (ca cb ii is oi os : Nat) :
    EqModGas (Blanc.callSpawnParent a ca ii is oi os) (Blanc.callSpawnParent b cb ii is oi os) := by
  apply of_normalized_eq
  change (Blanc.callSpawnParent (a.withGasLeft 0) 0 ii is oi os).withGasLeft 0 =
    (Blanc.callSpawnParent (b.withGasLeft 0) 0 ii is oi os).withGasLeft 0
  rw [h.withGasLeft_eq 0]

/-- Resuming agreeing parents with agreeing child posts preserves every column except gas. -/
theorem Devm.EqModGas.callChildPost {a b c d : Devm} (hp : EqModGas a b) (hc : EqModGas c d)
    (oi os : Nat) : EqModGas (Lift.callChildPost a c oi os) (Lift.callChildPost b d oi os) := by
  apply of_normalized_eq
  change (Lift.callChildPost (a.withGasLeft 0) (c.withGasLeft 0) oi os).withGasLeft 0 =
    (Lift.callChildPost (b.withGasLeft 0) (d.withGasLeft 0) oi os).withGasLeft 0
  rw [hp.withGasLeft_eq 0, hc.withGasLeft_eq 0]

end Blanc

namespace Blanc.Lift.AllGasCall

open Jaune Blanc

section Cross

variable (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256)

/-- The expansion charge of the call's two windows. -/
def ext : Nat :=
  (St b S M G).extCost [⟨ii.toNat, is.toNat⟩, ⟨oi.toNat, (0x20 : B256).toNat⟩]

/-- The callee's access charge. -/
def access : Nat := accessCost t.toAdr (St b S M G).accessedAddresses + 0

/-- The gas forwarded to the child (all but one 64th of what is left). -/
def forwarded : Nat := except64th (G - ext b S M G ii is oi - access b S M G t)

/-- The popped call state with the callee warmed. -/
def warmed : Devm := addAccessedAddress (St b S M G) t.toAdr

/-- The parent the child returns to. -/
def parent : Devm :=
  callSpawnParent (warmed b S M G t)
    (forwarded b S M G t ii is oi + access b S M G t + ext b S M G ii is oi)
    ii.toNat is.toNat oi.toNat (0x20 : B256).toNat

/-- The child message. -/
def message : Msg :=
  valueCallSpawnMsg sevm (parent b S M G t ii is oi) (forwarded b S M G t ii is oi) 0 t.toAdr
    t.toAdr ii.toNat is.toNat (b.state.getCode t.toAdr) false

/-- The resumed parent, from the child's post `cpost`. -/
def resume (cpost : Devm) : Devm :=
  callChildPost (parent b S M G t ii is oi) cpost oi.toNat (0x20 : B256).toNat

end Cross

theorem forwarded_le (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256) :
    forwarded b S M G t ii is oi ≤ G - ext b S M G ii is oi - access b S M G t := by
  unfold forwarded except64th
  omega

/-- **The `CALL` crossing at an all-gas call site** (see the module note). -/
theorem cross {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {t ii is oi : B256} {cpost : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdel : getDelegatedCodeAddress (b.state.getCode t.toAdr) = none)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hroom : S.length < 1024) (hG : G < 2 ^ 256)
    (hcharge : access b S M G t + ext b S M G ii is oi ≤ G)
    (hexec : exec (initEvm (message sevm b S M G t ii is oi)) = .ok cpost)
    (herr : cpost.error = none) :
    Ninst.RunCompiled sevm (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G)
      (.exec .call) (resume b S M G t ii is oi cpost) := by
  have hfwd := forwarded_le b S M G t ii is oi
  have hsplit : calculateMsgCallGas 0 (Nat.toB256 G).toNat (warmed b S M G t).gasLeft
      (ext b S M G ii is oi) (access b S M G t) =
      ⟨forwarded b S M G t ii is oi + access b S M G t, forwarded b S M G t ii is oi⟩ := by
    rw [B256.toNat_toB256_of_lt hG]
    change calculateMsgCallGas 0 G G _ _ = _
    unfold calculateMsgCallGas
    simp only [show ¬ G < access b S M G t + ext b S M G ii is oi from by omega, ↓reduceIte]
    rw [Nat.min_eq_right (by unfold except64th; omega), Nat.add_zero]
    rfl
  exact Ninst.runCompiled_call_zero_child (stmid := (warmed b S M G t).state.setBal
      sevm.currentTarget ((warmed b S M G t).state.bal sevm.currentTarget - 0))
    hfork rfl rfl
    (by
      unfold accessDelegation
      have hs : ∀ m, (addAccessedAddress ((St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 ::
          S) M G).setMach m) t.toAdr).state = b.state := fun _ => rfl
      simp only [hs, hdel]
      rfl)
    rfl hsplit
    (by change _ ≤ G; omega) hdepth hprec hroom
    (by
      unfold State.subBal
      simp only [show ¬ (warmed b S M G t).state.bal sevm.currentTarget < 0 from
        B256.not_lt.mpr (B256.zero_le _), ↓reduceIte])
    (by simp only [callChildMsg, ite_true]; exact hexec) herr



/-- The child static machine changes only its initial-gas field when parent gas varies. -/
theorem message_sevm_reframe (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat)
    (t ii is oi : B256) :
    initSevm (message sevm b S M G t ii is oi) =
      { initSevm (message sevm (b.withGasLeft 0) S M 0 t ii is oi) with
        gas := forwarded b S M G t ii is oi } := rfl

/-- The entered child preserves the full normalized world and metadata as parent gas varies. -/
theorem message_devm_reframe (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat)
    (t ii is oi : B256) :
    initDevm (message sevm b S M G t ii is oi) =
      (initDevm (message sevm (b.withGasLeft 0) S M 0 t ii is oi)).withGasLeft
        (forwarded b S M G t ii is oi) := rfl

/-- Exact parent debit after a funded child returns its unspent forwarded gas. -/
theorem resume_debit (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256)
    (cpost : Devm) (used : Nat)
    (hfund : forwarded b S M G t ii is oi + access b S M G t + ext b S M G ii is oi ≤ G)
    (hused : used ≤ forwarded b S M G t ii is oi)
    (hgas : cpost.gasLeft = forwarded b S M G t ii is oi - used) :
    G = (resume b S M G t ii is oi cpost).gasLeft +
      (access b S M G t + ext b S M G ii is oi + used) := by
  change G = (G - (forwarded b S M G t ii is oi + access b S M G t + ext b S M G ii is oi) +
    cpost.gasLeft) + (access b S M G t + ext b S M G ii is oi + used)
  rw [hgas]
  omega

end Blanc.Lift.AllGasCall
