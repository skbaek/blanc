import Blanc.Lift.WriteSiteObs
import Blanc.Lift.Basic

/-! ## W5  `Blanc/Lift/WriteSiteLocality.lean` (the generic locality corollary) -/

namespace Blanc.Lift.WriteSite

open Jaune

/-- What a guarded slot family asks of an `SSTORE` step: a write at a protected slot either does
not increase it, or happens in an allowed frame. -/
def GuardObs (K : B256 → Prop) (allowed : Prop) (sevm : Sevm) (d : Devm) (n : Ninst) : Prop :=
  n = .reg .sstore → ∀ x v rest, d.stack = x :: v :: rest → K x →
    allowed ∨ v.toNat ≤ (d.getStorVal sevm.currentTarget x).toNat

/-- **Generic write locality over a key family.**  `slot` places keys (e.g. USDC's
`fun (o, s) => allowSlot o s`); `prot` picks the guarded keys (e.g. `o = pair`); `named s ε k`
is the consumer's reading of a listed site as a key.  If every site that may increase its slot
names a key (`hname`), names a protected key only in an allowed frame (`howner`, a structural
check on the root's finite site list), and two keys with one slot are one key (`hinj`: hash
freshness, which the consumer takes from `SlotFootprint.FreshKeys` over the frame's touched keys,
exactly where HASH-T states it), then every `SSTORE` at a protected slot is non-increasing or
allowed. -/
theorem ws_locality_keys {κ : Type} (slot : κ → B256) (prot : κ → Prop)
    (named : Site → Env → κ → Prop) {sites : List Site} {ε : Env} {allowed : Prop}
    (hname : ∀ s ∈ sites, s.nonInc = false → (∀ g ∈ s.guards, g.1.Den ε g.2) →
      ∀ x, s.slot.Den ε x → ∃ k, named s ε k ∧ slot k = x)
    (hinj : ∀ s ∈ sites, ∀ k k', named s ε k → prot k' → slot k = slot k' → k = k')
    (howner : ∀ s ∈ sites, s.nonInc = false → (∀ g ∈ s.guards, g.1.Den ε g.2) →
      ∀ k, named s ε k → prot k → allowed)
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {pre post : Devm}
    (run : SProg.RunP (WsStep sites ε P) fs sevm pre post) :
    SProg.RunP (fun s d n d' => P s d n d' ∧
        GuardObs (fun x => ∃ k, prot k ∧ slot k = x) allowed s d n) fs sevm pre post := by
  refine SProg.RunP.mono ?_ run
  intro s d n d' h
  obtain ⟨hP, hObs⟩ := h
  refine ⟨hP, ?_⟩
  intro hn x v rest hstack hK
  obtain ⟨t, ht, hslot, hguards, hni⟩ := hObs hn x v rest hstack
  obtain ⟨k', hk'prot, hk'eq⟩ := hK
  match hnb : t.nonInc with
  | true => exact Or.inr (hni hnb)
  | false =>
    obtain ⟨k, hnamed, hslotk⟩ := hname t ht hnb hguards x hslot
    have heq : slot k = slot k' := by rw [hslotk, hk'eq]
    have hkk : k = k' := hinj t ht k k' hnamed hk'prot heq
    subst hkk
    exact Or.inl (howner t ht hnb hguards k hnamed hk'prot)

end Blanc.Lift.WriteSite
