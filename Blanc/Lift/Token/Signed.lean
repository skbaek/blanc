import Blanc.Lift.Token.HolderLaws

/-!
# Token interface core: the signature variant (C4)

A book with an authorizer (`BookS`: who must have signed an entered message), the signature-variant
laws (`BookLawsS`: a holder's balance or allowance may also move on the holder's own signature), and
the trace-local facet that a holder never signs a booked entry (`NeverSigner`).  Under it the
signature laws give the holder-indexed laws (`BookLawsS.holderLaws`); every plain book is a
signature book with no signer (`Book.unsigned`, `BookLaws.unsigned`).  Contract-neutral.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace

/-- A book with an authorizer: who must have signed an entered frame (a permit's owner, an
authorization's `from`), `none` for every other message.  Calldata-syntactic: it names the account
whose signature the code checks, not whether the signature is valid (a committed frame passed it). -/
structure BookS extends Book where
  signer : Sevm → Option Adr

/-- **The signature-variant laws** (C4): `holder_only` and `allow_owner` admit a third authorizer,
the holder's signature; the other fields are `BookLaws`' verbatim. -/
structure BookLawsS (S : BookS) : Prop where
  holder_only : ∀ {l l' : S.Ledger} {a : Sevm} {h : Adr}, S.Good l → S.step l a = some l' →
    S.bal l' h < S.bal l h → a.caller = h ∨ 0 < S.allow l h a.caller ∨ S.signer a = some h
  allow_owner : ∀ {l l' : S.Ledger} {a : Sevm} {h g : Adr}, S.Good l → S.step l a = some l' →
    S.allow l h g < S.allow l' h g → a.caller = h ∨ S.signer a = some h
  holder_debit : ∀ {l l' : S.Ledger} {a : Sevm} {h : Adr}, S.Good l → S.step l a = some l' →
    a.caller = h → (S.op a).HolderSafe → S.bal l h ≤ S.bal l' h + (S.op a).debit h
  transfer_exact : ∀ {l l' : S.Ledger} {a : Sevm} {dst : Adr} {v : Nat}, S.Good l →
    S.step l a = some l' → S.op a = .transfer dst v → dst ≠ a.caller →
    S.bal l' a.caller + v = S.bal l a.caller
  allow_safe : ∀ {l l' : S.Ledger} {a : Sevm} {h g : Adr}, S.Good l → S.step l a = some l' →
    a.caller = h → (S.op a).HolderSafe → S.allow l' h g ≤ S.allow l h g
  bal_lt : ∀ {l : S.Ledger} {h : Adr}, S.Good l → S.bal l h < 2 ^ 256

/-- **Facet: `p` never signs a booked entry along `tr`** (trace-local; the segment form: no
settled non-static entry of `T` in the history has `p` as its signer). -/
structure NeverSigner (T : Adr) (S : BookS) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) (p : Adr) : Prop where
  never : ∀ g ∈ tr.settledFrames, IsEntry T g → g.sevm.isStatic = false → S.signer g.sevm ≠ some p

/-- The per-message laws of a message not signed by `h`. -/
theorem BookLawsS.askLaws {S : BookS} (laws : BookLawsS S) {h : Adr} {a : Sevm}
    (unsigned : S.signer a ≠ some h) : AskLaws S.toBook h a where
  holder_only good step lower := by
    rcases laws.holder_only good step lower with caller | allowed | signed
    · exact Or.inl caller
    · exact Or.inr allowed
    · exact absurd signed unsigned
  allow_owner good step raise :=
    (laws.allow_owner good step raise).resolve_right unsigned
  holder_debit := laws.holder_debit
  allow_safe := laws.allow_safe

/-- Bridge 2: the signature laws and `NeverSigner` give the holder-indexed laws for the holder. -/
theorem BookLawsS.holderLaws {S : BookS} (laws : BookLawsS S) (T : Adr) {cfg : ChainConfig}
    {checkpoint future : BlockChain} {tr : ConfiguredHistoryTrace cfg checkpoint future} {h : Adr}
    (never : NeverSigner T S tr h) : HolderLaws T S.toBook tr h :=
  ⟨fun g mem entry static => laws.askLaws (never.never g mem entry static), laws.bal_lt⟩

/-- A book read as a signature book with no signer. -/
def Book.unsigned (B : Book) : BookS := { B with signer := fun _ => none }

/-- The universal laws are the signature laws of the unsigned book. -/
theorem BookLaws.unsigned {B : Book} (laws : BookLaws B) : BookLawsS B.unsigned where
  holder_only good step lower := (laws.holder_only good step lower).imp_right Or.inl
  allow_owner good step raise := Or.inl (laws.allow_owner good step raise)
  holder_debit := laws.holder_debit
  transfer_exact := laws.transfer_exact
  allow_safe := laws.allow_safe
  bal_lt := laws.bal_lt

/-- Nobody signs for an unsigned book. -/
theorem neverSigner_unsigned (T : Adr) (B : Book) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future) (p : Adr) :
    NeverSigner T B.unsigned tr p :=
  ⟨fun _ _ _ _ signed => nomatch signed⟩

end Blanc.Lift.Token
