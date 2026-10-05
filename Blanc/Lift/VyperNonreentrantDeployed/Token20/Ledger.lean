import Blanc.Lift.VyperNonreentrantDeployed.Token20.Run
import Blanc.Lift.ExactLeaf
import Blanc.LedgerConservation

/-!
# The synthetic token `T`: exact storage deltas and a finite-footprint ledger

What each successful run of `Run.lean` does to storage, exactly: the token's own storage is the
pre-state's with the selector's writes (`moveStor` for a move; the allowance write first for
`transferFrom`; the allowance write for `approve`; nothing for `balanceOf`), and every other
account's storage is untouched.

The ledger is observed on a finite footprint `F` of holders (`ledgerSumOn F (balances s)`,
`Blanc/LedgerConservation.lean`): a move between two members of `F` keeps its sum
(`ledger_move`); a `transferFrom` does too when the allowance slot it writes is not a balance slot
of `F` (`ledger_transferFrom`, a finite separation premise a concrete footprint discharges by
kernel evaluation).  No universal hash-separation or all-address claim is made.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20

open Jaune Blanc Blanc.Lift Blanc.Lift.NodeWalk

/-- The token's balance view of a storage. -/
def balances (s : Stor) : Adr → B256 := fun a => s.get (balSlot a)

/-- A storage after `balanceOf[src] -= v`, then `balanceOf[dst] += v` read after the debit. -/
def moveStor (s : Stor) (src dst : Adr) (v : B256) : Stor :=
  (s.set (balSlot src) (s.get (balSlot src) - v)).set (balSlot dst)
    (v + (s.set (balSlot src) (s.get (balSlot src) - v)).get (balSlot dst))

theorem balSlot_ne {a b : Adr} (h : a ≠ b) : balSlot a ≠ balSlot b :=
  fun e => h (Adr.toB256_inj e)

/-! ## Exact storage deltas -/

theorem getStor_retPost (b : Devm) (S : List B256) (M : Mem) (G : Nat) (w : B256) (a : Adr) :
    Devm.getStor (retPost b S M G w) a = Devm.getStor b a := rfl

theorem getStor_mv2 (sevm : Sevm) (b : Devm) (src : Adr) (v : B256) :
    Devm.getStor (mv2 sevm b src v) sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set (balSlot src) (mvFrom sevm b src - v) := by
  unfold mv2 mv1; rw [afterSstore_getStor_self, afterSload_getStor]

theorem getStor_mv4 (sevm : Sevm) (b : Devm) (src dst : Adr) (v : B256) :
    Devm.getStor (mv4 sevm b src dst v) sevm.currentTarget =
      moveStor (Devm.getStor b sevm.currentTarget) src dst v := by
  have hTo : mvTo sevm b src dst v =
      (Devm.getStor (mv2 sevm b src v) sevm.currentTarget).get (balSlot dst) := rfl
  unfold mv4 mv3
  rw [afterSstore_getStor_self, afterSload_getStor, hTo, getStor_mv2]
  rfl

theorem getStor_mv4_ne (sevm : Sevm) (b : Devm) (src dst : Adr) (v : B256) {a : Adr}
    (ha : a ≠ sevm.currentTarget) :
    Devm.getStor (mv4 sevm b src dst v) a = Devm.getStor b a := by
  unfold mv4 mv3 mv2 mv1
  rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSload_getStor,
    afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSload_getStor]

/-- **`transfer` writes exactly the move** at the token, and nothing elsewhere. -/
theorem transferPost_getStor (sevm : Sevm) (pre : Devm) (G : Nat) :
    Devm.getStor (transferPost sevm pre G) sevm.currentTarget =
        moveStor (Devm.getStor pre sevm.currentTarget) sevm.caller (trTo sevm) (trVal sevm) ∧
      ∀ a, a ≠ sevm.currentTarget → Devm.getStor (transferPost sevm pre G) a = Devm.getStor pre a := by
  unfold transferPost transferBase
  refine ⟨?_, fun a ha => ?_⟩
  · rw [getStor_retPost, getStor_mv4]
  · rw [getStor_retPost, getStor_mv4_ne _ _ _ _ _ ha]

theorem getStor_tf2 (sevm : Sevm) (pre : Devm) :
    Devm.getStor (tf2 sevm pre) sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set (allowSlot (tfFrom sevm) sevm.caller)
        (tfAllow sevm pre - tfVal sevm) := by
  unfold tf2 tf1; rw [afterSstore_getStor_self, afterSload_getStor]

/-- **`transferFrom` writes exactly the allowance decrement, then the move.** -/
theorem transferFromPost_getStor (sevm : Sevm) (pre : Devm) (G : Nat) :
    Devm.getStor (transferFromPost sevm pre G) sevm.currentTarget =
        moveStor ((Devm.getStor pre sevm.currentTarget).set (allowSlot (tfFrom sevm) sevm.caller)
          (tfAllow sevm pre - tfVal sevm)) (tfFrom sevm) (tfTo sevm) (tfVal sevm) ∧
      ∀ a, a ≠ sevm.currentTarget →
        Devm.getStor (transferFromPost sevm pre G) a = Devm.getStor pre a := by
  unfold transferFromPost transferFromBase
  refine ⟨?_, fun a ha => ?_⟩
  · rw [getStor_retPost, getStor_mv4, getStor_tf2]
  · rw [getStor_retPost, getStor_mv4_ne _ _ _ _ _ ha]
    unfold tf2 tf1
    rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSload_getStor]

/-- **`approve` writes exactly the allowance.** -/
theorem approvePost_getStor (sevm : Sevm) (pre : Devm) (G : Nat) :
    Devm.getStor (approvePost sevm pre G) sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set (allowSlot sevm.caller (apSpender sevm))
          (apVal sevm) ∧
      ∀ a, a ≠ sevm.currentTarget → Devm.getStor (approvePost sevm pre G) a = Devm.getStor pre a :=
  ⟨afterSstore_getStor_self _ _ _ _, fun _ ha => afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha)⟩

/-- **`balanceOf` writes nothing.** -/
theorem balanceOfPost_getStor (sevm : Sevm) (pre : Devm) (G : Nat) (a : Adr) :
    Devm.getStor (balanceOfPost sevm pre G) a = Devm.getStor pre a :=
  afterSload_getStor _ _ _ _

/-! ## The finite-footprint ledger -/

/-- A checked credit (`v ≤ v + w`, what the token tests) does not wrap. -/
theorem nof_of_le_add {v w : B256} (h : v ≤ v + w) : B256.Nof v w := by
  rw [B256.le_iff_toNat_le_toNat, B256.toNat_add] at h
  unfold B256.Nof
  have hv := B256.toNat_lt v
  have hw := B256.toNat_lt w
  by_contra hc
  rw [Nat.lo] at h
  have : (v.toNat + w.toNat) % 2 ^ 256 = v.toNat + w.toNat - 2 ^ 256 := by
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- **A move keeps the ledger of a footprint holding both ends.**  The movement equation holds for
any footprint; with `src, dst ∈ F` the sum is unchanged. -/
theorem ledger_move_eq {F : Finset Adr} {s : Stor} {src dst : Adr} {v : B256}
    (hle : v ≤ s.get (balSlot src))
    (hnof : v ≤ v + (s.set (balSlot src) (s.get (balSlot src) - v)).get (balSlot dst)) :
    ledgerSumOn F (balances (moveStor s src dst v)) + (if src ∈ F then v.toNat else 0) =
      ledgerSumOn F (balances s) + (if dst ∈ F then v.toNat else 0) := by
  have dec : Decrease src v (balances s)
      (balances (s.set (balSlot src) (s.get (balSlot src) - v))) := by
    intro a
    refine ⟨fun e => ?_, fun ne => ?_⟩
    · subst e; unfold balances; rw [Stor.get_set_self]
    · unfold balances; rw [Stor.get_set_ne _ (balSlot_ne ne)]
  have inc : Increase dst v (balances (s.set (balSlot src) (s.get (balSlot src) - v)))
      (balances (moveStor s src dst v)) := by
    intro a
    refine ⟨fun e => ?_, fun ne => ?_⟩
    · subst e; unfold balances moveStor; rw [Stor.get_set_self, B256.add_comm]
    · unfold balances moveStor; rw [Stor.get_set_ne _ (balSlot_ne ne)]
  have h1 := ledgerSumOn_decrease (coalition := F) dec hle
  have h2 := ledgerSumOn_increase (coalition := F) inc
    (by have := nof_of_le_add hnof; unfold B256.Nof at this ⊢; unfold balances; omega)
  omega

/-- A move between two holders of the footprint keeps its sum. -/
theorem ledger_move {F : Finset Adr} {s : Stor} {src dst : Adr} {v : B256}
    (hsrc : src ∈ F) (hdst : dst ∈ F) (hle : v ≤ s.get (balSlot src))
    (hnof : v ≤ v + (s.set (balSlot src) (s.get (balSlot src) - v)).get (balSlot dst)) :
    ledgerSumOn F (balances (moveStor s src dst v)) = ledgerSumOn F (balances s) := by
  have := ledger_move_eq (F := F) hle hnof
  simp only [hsrc, hdst, ↓reduceIte] at this
  omega

/-- A write at a slot that is no balance slot of the footprint leaves its sum. -/
theorem ledger_set_apart {F : Finset Adr} {s : Stor} {k w : B256}
    (hsep : ∀ a ∈ F, k ≠ balSlot a) :
    ledgerSumOn F (balances (s.set k w)) = ledgerSumOn F (balances s) :=
  (ledgerSumOn_congr fun a ha => by
    unfold balances; rw [Stor.get_set_ne _ (hsep a ha)]).symm

/-- **`transfer` keeps the ledger of a footprint holding the caller and the recipient.**  Its
premises are exactly those of `transfer_runExact`. -/
theorem ledger_transfer {F : Finset Adr} {sevm : Sevm} {pre : Devm} {G : Nat}
    (hsrc : sevm.caller ∈ F) (hdst : trTo sevm ∈ F)
    (hle : trVal sevm ≤ mvFrom sevm pre sevm.caller)
    (hnof : trVal sevm ≤ trVal sevm + mvTo sevm pre sevm.caller (trTo sevm) (trVal sevm)) :
    ledgerSumOn F (balances (Devm.getStor (transferPost sevm pre G) sevm.currentTarget)) =
      ledgerSumOn F (balances (Devm.getStor pre sevm.currentTarget)) := by
  rw [(transferPost_getStor sevm pre G).1]
  refine ledger_move hsrc hdst hle ?_
  have e : mvTo sevm pre sevm.caller (trTo sevm) (trVal sevm) =
      ((Devm.getStor pre sevm.currentTarget).set (balSlot sevm.caller)
        ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) - trVal sevm)).get
          (balSlot (trTo sevm)) := by
    show (Devm.getStor (mv2 _ _ _ _) _).get _ = _
    rw [getStor_mv2]; rfl
  rw [← e]; exact hnof

/-- **`transferFrom` keeps the ledger of a footprint holding `from` and `to`**, when the allowance
slot it writes is no balance slot of the footprint (finite, decidable for a concrete footprint). -/
theorem ledger_transferFrom {F : Finset Adr} {sevm : Sevm} {pre : Devm} {G : Nat}
    (hsrc : tfFrom sevm ∈ F) (hdst : tfTo sevm ∈ F)
    (hsep : ∀ a ∈ F, allowSlot (tfFrom sevm) sevm.caller ≠ balSlot a)
    (hle : tfVal sevm ≤ mvFrom sevm (tf2 sevm pre) (tfFrom sevm))
    (hnof : tfVal sevm ≤ tfVal sevm + mvTo sevm (tf2 sevm pre) (tfFrom sevm) (tfTo sevm) (tfVal sevm)) :
    ledgerSumOn F (balances (Devm.getStor (transferFromPost sevm pre G) sevm.currentTarget)) =
      ledgerSumOn F (balances (Devm.getStor pre sevm.currentTarget)) := by
  have e : mvTo sevm (tf2 sevm pre) (tfFrom sevm) (tfTo sevm) (tfVal sevm) =
      ((Devm.getStor (tf2 sevm pre) sevm.currentTarget).set (balSlot (tfFrom sevm))
        ((Devm.getStor (tf2 sevm pre) sevm.currentTarget).get (balSlot (tfFrom sevm)) -
          tfVal sevm)).get (balSlot (tfTo sevm)) := by
    show (Devm.getStor (mv2 _ _ _ _) _).get _ = _
    rw [getStor_mv2]; rfl
  rw [(transferFromPost_getStor sevm pre G).1, ← getStor_tf2,
    ledger_move (s := Devm.getStor (tf2 sevm pre) sevm.currentTarget) hsrc hdst hle
      (by rw [← e]; exact hnof), getStor_tf2, ledger_set_apart hsep]

/-- **`approve` keeps the ledger of a footprint** whose balance slots the allowance slot avoids;
**`balanceOf`** keeps every storage. -/
theorem ledger_approve {F : Finset Adr} {sevm : Sevm} {pre : Devm} {G : Nat}
    (hsep : ∀ a ∈ F, allowSlot sevm.caller (apSpender sevm) ≠ balSlot a) :
    ledgerSumOn F (balances (Devm.getStor (approvePost sevm pre G) sevm.currentTarget)) =
      ledgerSumOn F (balances (Devm.getStor pre sevm.currentTarget)) := by
  rw [(approvePost_getStor sevm pre G).1]; exact ledger_set_apart hsep

end Blanc.Lift.VyperNonreentrantDeployed.Token20
