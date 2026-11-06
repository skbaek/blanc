import Blanc.Lift.Curve3Crv.Headline
import Blanc.Lift.Curve3Crv.HistWindow

/-!
# A holder's 3Crv word is at most the supply word

`share_le_supply_window`: right after any transaction of a window from 3Crv's invariant, a holder's
balance word is at most the supply word, when that holder's key is collision-free with the keys the
window touches (HASH-T, one more key). The model conserves the supply (`Conserved.le_supply`), and the
words read the model on such a key.

The freshness cannot be dropped: an untracked holder's word is zero only when its slot is none of the
slots in use. It stays trace-local on purpose. Over all owners and spenders, "no allowance slot is this
slot" quantifies over more keys than there are slots, so it would not be a satisfiable premise.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.ExecutionTrace

/-- Read through a universe of keys: a key of the universe holds at most the supply word. -/
theorem VyInv.bal_le_supply {stor : Stor} {s : Blanc.Curve3Crv.State} {K U : Key → Prop}
    (h : VyInv stor s K) (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) (included : ∀ k, K k → U k) {E : Adr} (hE : U (.bal E)) :
    (stor.get (vyBalSlot E)).toNat ≤ (stor.get vySupplySlot).toNat := by
  have read : stor.get (vyBalSlot E) = s.balanceOf E := h.get_slot_of_universe injective apart included hE
  rw [read, h.supply]
  exact h.conserved.le_supply E

/-- **A holder's word is at most the supply word, at every transaction boundary of a window.** -/
theorem share_le_supply_window {ca : Adr} {cfg : ChainConfig} {start : Benv} {pre post : BlockChain}
    {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop}
    (mid : MidHistoryTraceIn HistFork cfg start pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (installed : some (start.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (start.state.getStor ca) initial initialKeys) {E : Adr}
    (fresh : FreshKeys initialKeys (.bal E :: midTouchedKeysIn ca (mid.step block))) :
    ((cut.afterBenv.state.getStor ca).get (vyBalSlot E)).toNat ≤
      ((cut.afterBenv.state.getStor ca).get vySupplySlot).toNat := by
  have touched : FreshKeys initialKeys (midTouchedKeysIn ca (mid.step block)) :=
    ⟨fun k hk => fresh.1 k (List.mem_cons_of_mem _ hk),
      fun k hk k' hk' => fresh.2 k (List.mem_cons_of_mem _ hk) k' (List.mem_cons_of_mem _ hk')⟩
  have topology := invariant.extend fresh
  obtain ⟨-, s, -, final⟩ := c3crv_window_framesHist mid block cut installed invariant touched
  obtain ⟨-, -, -, -, -, keysIn⟩ := c3crv_mid_history_framesHist (mid.step block) installed invariant touched
  refine final.bal_le_supply topology.inj topology.apart ?_ (Or.inr List.mem_cons_self)
  rintro k (live | member)
  · exact Or.inl live
  · have whole : k ∈ invocationKeys (midCommittedInvocationsIn ca (mid.step block)) := by
      obtain ⟨inv, invIn, keyIn⟩ := List.mem_flatMap.mp member
      refine List.mem_flatMap.mpr ⟨inv, ?_, keyIn⟩
      obtain ⟨f, fIn, invAt⟩ := List.mem_flatMap.mp invIn
      refine List.mem_flatMap.mpr ⟨f, ?_, invAt⟩
      change f ∈ mid.settledFrames ++ block.settledFrames
      rw [block.settledFrames_throughCut cut, ← List.append_assoc]
      exact List.mem_append_left _ fIn
    rcases keysIn k whole with live | hk
    · exact Or.inl live
    · exact Or.inr (List.mem_cons_of_mem _ hk)

end Blanc.Lift.Curve3Crv
