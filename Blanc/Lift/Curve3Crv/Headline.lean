import Blanc.Lift.Curve3Crv.HistDeployment
import Blanc.Lift.LedgerFootprint

/-!
# 3Crv headlines over storage words, from the actual deployment

Both headlines take the single deployment premise `d : C3crvDeploymentTo checkpoint` and state their
conclusion over the token's storage words only (`vySupplySlot`, `vyMinterSlot`, `vyBalSlot`,
`vyAllowSlot`, `Layout.lean`), with no model state in the statement.

* `c3crv_conserved`: at the checkpoint the supply word is the sum of the balance words of every
  holder whose balance the history touched (`SupplyConserved`, `C3crvDeploymentTo.holders`).
* `c3crv_policy`: every committed writer frame at the token, read through its own opening and
  closing storage, obeys four policy facts (`C3crvFramePolicy`): only the minter word's address
  moves the supply word, and only by `mint`/`burnFrom`; only that address moves the minter word; a
  non-minter `transferFrom` spends exactly its value of the caller's allowance word (so even the
  all-ones allowance is decremented: no infinite approval); and a touched allowance word moves only
  by its owner's `approve` or its spender's non-minter `transferFrom`.

The model correspondence is below them: `C3crvDeploymentTo.frames` (the committed replay frame by
frame, `HistDeployment.lean`) and the model facts of `Blanc/Curve3Crv/Properties.lean`.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.ExecutionTrace Blanc.Lift.Curve3Crv.Creation

/-! ## Reading storage words through the model -/

/-- A key of the collision universe `U` reads its model value from storage abstracting a state over
live keys inside `U` (`U` injective on slots and off the fixed slots). -/
theorem VyInv.get_slot_of_universe {stor : Stor} {s : Blanc.Curve3Crv.State} {K U : Key → Prop}
    (h : VyInv stor s K) (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) (included : ∀ k, K k → U k) {k : Key}
    (hk : U k) : stor.get k.slot = k.val s :=
  h.get_slot ((FreshKeys.of_universe injective apart included
    (fun _ member => (List.mem_singleton.mp member) ▸ hk)).1 k (List.mem_singleton_self k))

/-! ## Observers -/

/-- The holder of a balance key. -/
def Key.holder : Key → Option Adr
  | .bal a => some a
  | .allow _ _ => none

/-- **Supply conservation over storage words**: the supply word is the sum of the balance words of
`holders`. -/
def SupplyConserved (stor : Stor) (holders : Finset Adr) : Prop :=
  (stor.get vySupplySlot).toNat = ledgerSumOn holders fun a => stor.get (vyBalSlot a)

/-- The token's storage word at `x` when a committed writer frame opens. -/
def WriterInvocation.preWord (inv : WriterInvocation) (x : B256) : B256 :=
  (Devm.getStor inv.pre tokenAddress).get x

/-- The token's storage word at `x` when a committed writer frame closes. -/
def WriterInvocation.postWord (inv : WriterInvocation) (x : B256) : B256 :=
  (Devm.getStor inv.post tokenAddress).get x

/-- Only the minter word's address moves the supply word, and only by `mint` or `burnFrom`. -/
def OnlyMinterMovesSupply (inv : WriterInvocation) : Prop :=
  inv.postWord vySupplySlot ≠ inv.preWord vySupplySlot →
    inv.sevm.caller.toB256 = inv.preWord vyMinterSlot ∧
      ∃ a v, decodeCall inv.sevm = .mint a v ∨ decodeCall inv.sevm = .burnFrom a v

/-- Only the minter word's address moves the minter word. -/
def OnlyMinterMovesMinter (inv : WriterInvocation) : Prop :=
  inv.postWord vyMinterSlot ≠ inv.preWord vyMinterSlot →
    inv.sevm.caller.toB256 = inv.preWord vyMinterSlot

/-- A `transferFrom` by any address but the minter word's spends exactly its value of the caller's
allowance word, which covers it. -/
def TransferFromSpendsAllowance (inv : WriterInvocation) : Prop :=
  ∀ f dst v, decodeCall inv.sevm = .transferFrom f dst v →
    inv.sevm.caller.toB256 ≠ inv.preWord vyMinterSlot →
      v ≤ inv.preWord (vyAllowSlot f.toAdr inv.sevm.caller) ∧
        inv.postWord (vyAllowSlot f.toAdr inv.sevm.caller) =
          inv.preWord (vyAllowSlot f.toAdr inv.sevm.caller) - v

/-- An allowance word of a `tracked` pair moves only by its owner's `approve` of that spender or its
spender's `transferFrom` from that owner, the spender not being the minter word's address. -/
def AllowanceMovesAuthorized (tracked : List Key) (inv : WriterInvocation) : Prop :=
  ∀ o p, Key.allow o p ∈ tracked →
    inv.postWord (vyAllowSlot o p) ≠ inv.preWord (vyAllowSlot o p) →
      (inv.sevm.caller = o ∧ ∃ w v, decodeCall inv.sevm = .approve w v ∧ w.toAdr = p) ∨
        (inv.sevm.caller = p ∧ inv.sevm.caller.toB256 ≠ inv.preWord vyMinterSlot ∧
          ∃ f dst v, decodeCall inv.sevm = .transferFrom f dst v ∧ f.toAdr = o)

/-- **The 3Crv policy of one committed writer frame**, over its own storage words. -/
def C3crvFramePolicy (tracked : List Key) (inv : WriterInvocation) : Prop :=
  OnlyMinterMovesSupply inv ∧ OnlyMinterMovesMinter inv ∧ TransferFromSpendsAllowance inv ∧
    AllowanceMovesAuthorized tracked inv

namespace C3crvDeploymentTo

variable {checkpoint : BlockChain} (d : C3crvDeploymentTo checkpoint)

/-- The addresses whose balance key some raw token frame of the history touches. -/
noncomputable def holders : Finset Adr :=
  (d.touched.filterMap Key.holder).toFinset

/-- The touched keys' slots are pairwise distinct and off the fixed slots (from `fresh`). -/
theorem touched_topology :
    (∀ k k', Key.extend (fun _ => False) d.touched k →
        Key.extend (fun _ => False) d.touched k' → k.slot = k'.slot → k = k') ∧
      ∀ k, Key.extend (fun _ => False) d.touched k → k.slot ∉ vyFixedSlots := by
  have start : VyInv (d.cut.afterBenv.state.getStor tokenAddress)
      (curveDeployedState deployer) (Key.extend (fun _ => False) d.touched) :=
    d.created.2.2.extend d.fresh
  exact ⟨start.inj, start.apart⟩

end C3crvDeploymentTo

/-! ## The headlines -/

/-- **3Crv conservation from its actual deployment.** At any checkpoint after the deployment, the
token's supply word equals the sum of the balance words of every holder whose balance the history's
raw token frames touched. -/
theorem c3crv_conserved {checkpoint : BlockChain} (d : C3crvDeploymentTo checkpoint) :
    SupplyConserved (checkpoint.state.getStor tokenAddress) d.holders := by
  obtain ⟨s, -, -, final, keysIn⟩ := d.frames
  obtain ⟨injective, apart⟩ := d.touched_topology
  have included : ∀ k, d.keys k → Key.extend (fun _ => False) d.touched k :=
    fun k hk => hk.elim False.elim (keysIn k)
  have touchedMem : ∀ k, Key.extend (fun _ => False) d.touched k ↔ k ∈ d.touched :=
    fun k => ⟨fun hk => hk.elim False.elim id, Or.inr⟩
  unfold SupplyConserved
  rw [final.supply, final.conserved]
  rw [sum_eq_ledgerSumOn (coalition := d.holders) fun a nonzero => ?_]
  · apply ledgerSumOn_congr
    intro a member
    obtain ⟨k, hk, holder⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp member)
    cases k with
    | bal b =>
      cases holder
      exact (final.get_slot_of_universe injective apart included ((touchedMem _).mpr hk)).symm
    | allow _ _ => cases holder
  · by_cases live : d.keys (.bal a)
    · exact List.mem_toFinset.mpr (List.mem_filterMap.mpr
        ⟨.bal a, (touchedMem _).mp (included _ live), rfl⟩)
    · exact absurd (final.unknown (.bal a) live) nonzero

/-- **3Crv policy from its actual deployment.** Every committed writer frame at the token after
the deployment obeys `C3crvFramePolicy` over its own opening and closing storage words, the minter
read from the minter word as the frame opens, the allowance pairs tracked being those the history's
raw token frames touched. -/
theorem c3crv_policy {checkpoint : BlockChain} (d : C3crvDeploymentTo checkpoint) :
    ∀ inv ∈ d.invocations, C3crvFramePolicy d.touched inv := by
  obtain ⟨-, -, frames, -, -⟩ := d.frames
  obtain ⟨injective, apart⟩ := d.touched_topology
  intro inv member
  obtain ⟨s, o, K, ⟨accepted, -⟩, included, callIn, before, after⟩ := frames inv member
  have minterWord : inv.preWord vyMinterSlot = s.minter.toB256 := before.minter
  have read : ∀ k, k ∈ d.touched →
      inv.preWord k.slot = k.val s ∧ inv.postWord k.slot = k.val o.1 := fun k hk =>
    ⟨before.get_slot_of_universe injective apart included (Or.inr hk),
      after.get_slot_of_universe injective apart included (Or.inr hk)⟩
  refine ⟨fun moved => ?_, fun moved => ?_, fun f dst v call notMinter => ?_,
    fun op sp tracked moved => ?_⟩
  · have hne : o.1.totalSupply ≠ s.totalSupply := by
      intro same
      apply moved
      show (Devm.getStor inv.post tokenAddress).get vySupplySlot =
        (Devm.getStor inv.pre tokenAddress).get vySupplySlot
      rw [after.supply, before.supply, same]
    obtain ⟨sender, call⟩ := Blanc.Curve3Crv.supply_change_by_minter accepted hne
    exact ⟨by rw [minterWord]; exact congrArg Adr.toB256 sender, call⟩
  · have hne : o.1.minter ≠ s.minter := by
      intro same
      apply moved
      show (Devm.getStor inv.post tokenAddress).get vyMinterSlot =
        (Devm.getStor inv.pre tokenAddress).get vyMinterSlot
      rw [after.minter, before.minter, same]
    rw [minterWord]
    exact congrArg Adr.toB256 (Blanc.Curve3Crv.minter_change_by_minter accepted hne)
  · rw [call] at accepted callIn
    have hm : inv.sevm.caller ≠ s.minter := fun same =>
      notMinter (by rw [minterWord, same])
    obtain ⟨cover, spent⟩ := Blanc.Curve3Crv.transferFrom_spends_allowance accepted hm
    have key : K (.allow f.toAdr inv.sevm.caller) := callIn _ (by simp only [callKeys,
      List.mem_cons, reduceCtorEq, true_or, or_true])
    have pre : inv.preWord (vyAllowSlot f.toAdr inv.sevm.caller) =
        s.allowances f.toAdr inv.sevm.caller := before.known _ key
    have post : inv.postWord (vyAllowSlot f.toAdr inv.sevm.caller) =
        o.1.allowances f.toAdr inv.sevm.caller := after.known _ key
    rw [pre, post]
    exact ⟨cover, spent⟩
  · obtain ⟨pre, post⟩ := read (.allow op sp) tracked
    have hne : o.1.allowances op sp ≠ s.allowances op sp := by
      intro same
      apply moved
      change inv.postWord (Key.allow op sp).slot = inv.preWord (Key.allow op sp).slot
      rw [pre, post]
      exact same
    rcases Blanc.Curve3Crv.allowance_change_authorized accepted hne with owner | spender
    · exact .inl owner
    · obtain ⟨sender, notMinter, call⟩ := spender
      refine .inr ⟨sender, fun same => notMinter ?_, call⟩
      rw [minterWord] at same
      exact Adr.toB256_inj same

end Blanc.Lift.Curve3Crv
