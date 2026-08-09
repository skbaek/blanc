import Blanc.Weth10HolderFlow

/-!
Local, non-circular balance algebra for classified WETH10 flow actions.

The relations in this file retain the actual modular credit, checked debit,
and transfer witnesses.  In particular, no constructor assumes the endpoint
balance equation that the theorems below derive.  A flash action is split at
its callback boundary: its mint and repayment segments share one
`FlowAction`, but no relation is asserted between the post-mint and
pre-repayment maps.
-/

namespace Blanc

open Jaune

namespace Weth10

abbrev HolderBalances := Adr → B256

/-- The credit metadata is the exact word addition performed by this action. -/
def FlowAction.ExactCredit (action : FlowAction) (recipient : Adr)
    (before amountWord : B256) : Prop :=
  action.credit = some { recipient, before, amountWord }

/-- The retained debit record names the raw and normalized source used by the
balance operation.  Its runtime authorization branch remains available in
the record but is deliberately not interpreted by this algebraic layer. -/
def FlowAction.HasDebitSource (action : FlowAction)
    (rawSource : B256) (source : Adr) : Prop :=
  ∃ debit, action.debit = some debit ∧
    debit.actualCaller = action.actualCaller ∧
    debit.rawSource = rawSource ∧ debit.source = source

/-- Flash repayment additionally pins the debit record to its flash-settlement
allowance arm. -/
def FlowAction.HasFlashDebitSource (action : FlowAction)
    (rawSource : B256) (source : Adr) : Prop :=
  ∃ debit allowance, action.debit = some debit ∧
    debit.actualCaller = action.actualCaller ∧
    debit.rawSource = rawSource ∧ debit.source = source ∧
    debit.branch = .flash allowance

/-- A chosen decomposition of an exact checked transfer.  Keeping the
intermediate map makes the recipient's pre-credit word available for exact
wrap accounting. -/
structure ExactTransferWitness (pre post : HolderBalances)
    (source : Adr) (amountWord : B256) (recipient : Adr) where
  amount_le : amountWord ≤ pre source
  intermediate : HolderBalances
  decrease : Decrease source amountWord pre intermediate
  increase : Increase recipient amountWord intermediate post

theorem ExactTransferWitness.toTransfer
    {pre post : HolderBalances} {source recipient : Adr} {amountWord : B256}
    (witness : ExactTransferWitness pre post source amountWord recipient) :
    Transfer pre source amountWord recipient post :=
  ⟨witness.amount_le, witness.intermediate,
    witness.decrease, witness.increase⟩

/-- Pointwise wrap-aware equation for an unchecked credit. -/
theorem increase_holder_eq
    {pre post : HolderBalances} {recipient u : Adr} {amountWord : B256}
    (increase : Increase recipient amountWord pre post) :
    (pre u).toNat + (if recipient = u then amountWord.toNat else 0) =
      (post u).toNat +
        (if recipient = u then creditLoss (pre recipient) amountWord else 0) := by
  by_cases hrecipient : recipient = u
  · subst recipient
    simpa using increase_toNat_add_creditLoss increase
  · have hsame : pre u = post u := (increase u).2 hrecipient
    simp [hrecipient, hsame]

/-- Pointwise exact equation for a checked debit. -/
theorem decrease_holder_eq
    {pre post : HolderBalances} {source u : Adr} {amountWord : B256}
    (amount_le : amountWord ≤ pre source)
    (decrease : Decrease source amountWord pre post) :
    (pre u).toNat =
      (post u).toNat + (if source = u then amountWord.toNat else 0) := by
  by_cases hsource : source = u
  · subst source
    simpa using (decrease_toNat_add decrease amount_le).symm
  · have hsame : pre u = post u := (decrease u).2 hsource
    simp [hsource, hsame]

/-- Pointwise exact equation for a checked debit followed by an unchecked
credit.  The same formula covers external transfers and self-transfers. -/
theorem ExactTransferWitness.holder_eq
    {pre post : HolderBalances} {source recipient u : Adr}
    {amountWord : B256}
    (transfer : ExactTransferWitness pre post source amountWord recipient) :
    (pre u).toNat + (if recipient = u then amountWord.toNat else 0) =
      (post u).toNat + (if source = u then amountWord.toNat else 0) +
        (if recipient = u then
          creditLoss (transfer.intermediate recipient) amountWord else 0) := by
  rcases transfer with ⟨amount_le, intermediate, decrease, increase⟩
  by_cases hsource : source = u
  · subst source
    have hdecrease := decrease_toNat_add decrease amount_le
    by_cases hrecipient : recipient = u
    · subst recipient
      have hincrease := increase_toNat_add_creditLoss increase
      simp only [ite_true]
      omega
    · have hincrease : intermediate u = post u :=
        (increase u).2 hrecipient
      simp only [hrecipient, ite_false, ite_true]
      rw [← hincrease]
      omega
  · have hdecrease : pre u = intermediate u :=
      (decrease u).2 hsource
    by_cases hrecipient : recipient = u
    · subst recipient
      have hincrease := increase_toNat_add_creditLoss increase
      simp only [hsource, ite_false, ite_true]
      rw [hdecrease]
      exact hincrease
    · have hincrease : intermediate u = post u :=
        (increase u).2 hrecipient
      simp [hsource, hrecipient, hdecrease, hincrease]

/-- A checked self-transfer's credit exactly restores its own debit, so this
credit cannot wrap even before any global conservation argument. -/
theorem ExactTransferWitness.self_creditLoss_eq_zero
    {pre post : HolderBalances} {source recipient : Adr}
    {amountWord : B256}
    (transfer : ExactTransferWitness pre post source amountWord recipient)
    (hself : source = recipient) :
    creditLoss (transfer.intermediate recipient) amountWord = 0 := by
  subst recipient
  apply (creditLoss_eq_zero_iff _ _).2
  unfold B256.Nof
  have hdecrease :=
    decrease_toNat_add transfer.decrease transfer.amount_le
  have hlt := B256.toNat_lt (pre source)
  omega

/-- The five kinds of contiguous balance segment.  Flash mint and repayment
are separate kinds because arbitrary committed callback/reentrant activity may
occur between them. -/
inductive LocalSegmentKind
  | ordinaryMint
  | ordinaryTransfer
  | redemption
  | flashCredit
  | flashRepayment
deriving DecidableEq

/-- One exact contiguous balance segment belonging to a classified action. -/
inductive LocalActionSegment :
    LocalSegmentKind → FlowAction → HolderBalances →
      HolderBalances → Prop
  | ordinaryMint
      {action pre post} (rawRecipient : B256) (recipient : Adr)
      (amountWord : B256)
      (atom_eq : action.atom =
        .ordinaryMint rawRecipient recipient amountWord.toNat)
      (credit_eq : action.ExactCredit recipient (pre recipient) amountWord)
      (debit_eq : action.debit = none)
      (increase : Increase recipient amountWord pre post) :
      LocalActionSegment .ordinaryMint action pre post
  | ordinaryTransfer
      {action pre post} (rawSource rawRecipient : B256)
      (source recipient : Adr) (amountWord : B256)
      (atom_eq : action.atom =
        .transfer rawSource rawRecipient source recipient amountWord.toNat)
      (transfer : ExactTransferWitness pre post source amountWord recipient)
      (credit_eq : action.ExactCredit recipient
        ((ExactTransferWitness.intermediate transfer) recipient) amountWord)
      (debit_source : action.HasDebitSource rawSource source)
      :
      LocalActionSegment .ordinaryTransfer action pre post
  | redemption
      {action pre post} (rawSource : B256) (source ethRecipient : Adr)
      (amountWord : B256)
      (atom_eq : action.atom =
        .redemption rawSource source ethRecipient amountWord.toNat)
      (credit_eq : action.credit = none)
      (debit_source : action.HasDebitSource rawSource source)
      (amount_le : amountWord ≤ pre source)
      (decrease : Decrease source amountWord pre post) :
      LocalActionSegment .redemption action pre post
  | flashCredit
      {action pre post} (rawReceiver : B256) (receiver : Adr)
      (amountWord : B256)
      (atom_eq : action.atom =
        .flashPair rawReceiver receiver amountWord.toNat)
      (credit_eq : action.ExactCredit receiver (pre receiver) amountWord)
      (debit_source : action.HasFlashDebitSource rawReceiver receiver)
      (increase : Increase receiver amountWord pre post) :
      LocalActionSegment .flashCredit action pre post
  | flashRepayment
      {action pre post} (rawReceiver : B256) (receiver : Adr)
      (amountWord creditBefore : B256)
      (atom_eq : action.atom =
        .flashPair rawReceiver receiver amountWord.toNat)
      (credit_eq : action.ExactCredit receiver creditBefore amountWord)
      (debit_source : action.HasFlashDebitSource rawReceiver receiver)
      (amount_le : amountWord ≤ pre receiver)
      (decrease : Decrease receiver amountWord pre post) :
      LocalActionSegment .flashRepayment action pre post

/-- One action's own balance effect.  The flash constructor retains both
same-action segments and leaves the callback gap unconstrained. -/
inductive LocalOwnEffect (action : FlowAction) :
    HolderBalances → HolderBalances → Prop
  | ordinaryMint {pre post}
      (segment : LocalActionSegment .ordinaryMint action pre post) :
      LocalOwnEffect action pre post
  | ordinaryTransfer {pre post}
      (segment : LocalActionSegment .ordinaryTransfer action pre post) :
      LocalOwnEffect action pre post
  | redemption {pre post}
      (segment : LocalActionSegment .redemption action pre post) :
      LocalOwnEffect action pre post
  | flashPair {pre minted settle post}
      (mint : LocalActionSegment .flashCredit action pre minted)
      (repayment : LocalActionSegment .flashRepayment action settle post) :
      LocalOwnEffect action pre post

def LocalSegmentKind.holderIn (kind : LocalSegmentKind)
    (action : FlowAction) (u : Adr) : Nat :=
  let flow := action.atom.holderFlow u
  match kind with
  | .ordinaryMint => flow.ordinaryIn
  | .ordinaryTransfer => flow.ordinaryIn + flow.selfTransfer
  | .redemption => 0
  | .flashCredit => flow.flashCredit
  | .flashRepayment => 0

def LocalSegmentKind.holderOut (kind : LocalSegmentKind)
    (action : FlowAction) (u : Adr) : Nat :=
  let flow := action.atom.holderFlow u
  match kind with
  | .ordinaryMint => 0
  | .ordinaryTransfer =>
      flow.externalTransferredOut + flow.selfTransfer
  | .redemption => flow.redeemed
  | .flashCredit => 0
  | .flashRepayment => flow.flashRepayment

def LocalSegmentKind.holderLoss (kind : LocalSegmentKind)
    (action : FlowAction) (u : Adr) : Nat :=
  match kind with
  | .ordinaryMint | .ordinaryTransfer | .flashCredit =>
      action.holderCreditLoss u
  | .redemption | .flashRepayment => 0

/-- Every local segment satisfies its exact per-holder `Nat` equation.  A
credit's only discrepancy is its explicitly retained modular loss. -/
theorem LocalActionSegment.holder_eq
    {kind : LocalSegmentKind} {action : FlowAction}
    {pre post : HolderBalances}
    (segment : LocalActionSegment kind action pre post) (u : Adr) :
    (pre u).toNat + kind.holderIn action u =
      (post u).toNat + kind.holderOut action u +
        kind.holderLoss action u := by
  cases segment with
  | ordinaryMint rawRecipient recipient amountWord atom_eq credit_eq
      debit_eq increase =>
      unfold FlowAction.ExactCredit at credit_eq
      by_cases hrecipient : recipient = u <;>
        simpa [LocalSegmentKind.holderIn, LocalSegmentKind.holderOut,
          LocalSegmentKind.holderLoss, atom_eq, credit_eq,
          FlowAtom.holderFlow, HolderFlow.zero,
          FlowAction.holderCreditLoss, CreditOccurrence.loss,
          hrecipient] using (increase_holder_eq (u := u) increase)
  | ordinaryTransfer rawSource rawRecipient source recipient amountWord
      atom_eq transfer credit_eq debit_source =>
      unfold FlowAction.ExactCredit at credit_eq
      have exact := transfer.holder_eq (u := u)
      by_cases hsource : source = u <;>
        by_cases hrecipient : recipient = u <;>
        simpa [LocalSegmentKind.holderIn, LocalSegmentKind.holderOut,
          LocalSegmentKind.holderLoss, atom_eq, credit_eq,
          FlowAtom.holderFlow, HolderFlow.zero, FlowAction.holderCreditLoss,
          CreditOccurrence.loss,
          hsource, hrecipient] using exact
  | redemption rawSource source ethRecipient amountWord atom_eq credit_eq
      debit_source amount_le decrease =>
      by_cases hsource : source = u <;>
        simpa [LocalSegmentKind.holderIn, LocalSegmentKind.holderOut,
          LocalSegmentKind.holderLoss, atom_eq, FlowAtom.holderFlow,
          HolderFlow.zero, hsource] using
          (decrease_holder_eq (u := u) amount_le decrease)
  | flashCredit rawReceiver receiver amountWord atom_eq credit_eq
      debit_source increase =>
      unfold FlowAction.ExactCredit at credit_eq
      by_cases hreceiver : receiver = u <;>
        simpa [LocalSegmentKind.holderIn, LocalSegmentKind.holderOut,
          LocalSegmentKind.holderLoss, atom_eq, credit_eq,
          FlowAtom.holderFlow, HolderFlow.zero,
          FlowAction.holderCreditLoss, CreditOccurrence.loss,
          hreceiver] using (increase_holder_eq (u := u) increase)
  | flashRepayment rawReceiver receiver amountWord creditBefore atom_eq
      credit_eq debit_source amount_le decrease =>
      by_cases hreceiver : receiver = u <;>
        simpa [LocalSegmentKind.holderIn, LocalSegmentKind.holderOut,
          LocalSegmentKind.holderLoss, atom_eq, FlowAtom.holderFlow,
          HolderFlow.zero, hreceiver] using
          (decrease_holder_eq (u := u) amount_le decrease)

/-- Constructor-shaped equations for one complete local action.  The flash
case exposes the two equations on either side of the unconstrained callback
gap; it does not pretend that the parent action alone owns callback writes. -/
inductive LocalOwnHolderEquations (action : FlowAction)
    (pre post : HolderBalances) (u : Adr) : Prop
  | ordinaryMint
      (equation : (pre u).toNat +
          LocalSegmentKind.ordinaryMint.holderIn action u =
        (post u).toNat +
          LocalSegmentKind.ordinaryMint.holderOut action u +
          LocalSegmentKind.ordinaryMint.holderLoss action u) :
      LocalOwnHolderEquations action pre post u
  | ordinaryTransfer
      (equation : (pre u).toNat +
          LocalSegmentKind.ordinaryTransfer.holderIn action u =
        (post u).toNat +
          LocalSegmentKind.ordinaryTransfer.holderOut action u +
          LocalSegmentKind.ordinaryTransfer.holderLoss action u) :
      LocalOwnHolderEquations action pre post u
  | redemption
      (equation : (pre u).toNat +
          LocalSegmentKind.redemption.holderIn action u =
        (post u).toNat + LocalSegmentKind.redemption.holderOut action u +
          LocalSegmentKind.redemption.holderLoss action u) :
      LocalOwnHolderEquations action pre post u
  | flashPair (minted settle : HolderBalances)
      (mintEquation : (pre u).toNat +
          LocalSegmentKind.flashCredit.holderIn action u =
        (minted u).toNat +
          LocalSegmentKind.flashCredit.holderOut action u +
          LocalSegmentKind.flashCredit.holderLoss action u)
      (repaymentEquation : (settle u).toNat +
          LocalSegmentKind.flashRepayment.holderIn action u =
        (post u).toNat +
          LocalSegmentKind.flashRepayment.holderOut action u +
          LocalSegmentKind.flashRepayment.holderLoss action u) :
      LocalOwnHolderEquations action pre post u

theorem LocalOwnEffect.holder_equations
    {action : FlowAction} {pre post : HolderBalances}
    (effect : LocalOwnEffect action pre post) (u : Adr) :
    LocalOwnHolderEquations action pre post u := by
  cases effect with
  | ordinaryMint segment =>
      exact .ordinaryMint (segment.holder_eq u)
  | ordinaryTransfer segment =>
      exact .ordinaryTransfer (segment.holder_eq u)
  | redemption segment =>
      exact .redemption (segment.holder_eq u)
  | flashPair mint repayment =>
      exact .flashPair _ _ (mint.holder_eq u) (repayment.holder_eq u)

/-- A contiguous sequence of local segments.  In a flash execution the mint,
all committed nested callback segments, and the repayment can appear in this
single chain, while `LocalOwnEffect.flashPair` separately certifies that the
two boundary segments belong to the same parent action. -/
inductive LocalSegmentChain :
    List (LocalSegmentKind × FlowAction) →
      HolderBalances → HolderBalances → Prop
  | nil (balances : HolderBalances) : LocalSegmentChain [] balances balances
  | cons {kind action tail pre middle post}
      (head : LocalActionSegment kind action pre middle)
      (rest : LocalSegmentChain tail middle post) :
      LocalSegmentChain ((kind, action) :: tail) pre post

def localSegmentsHolderIn
    (segments : List (LocalSegmentKind × FlowAction)) (u : Adr) : Nat :=
  (segments.map fun segment => segment.1.holderIn segment.2 u).sum

def localSegmentsHolderOut
    (segments : List (LocalSegmentKind × FlowAction)) (u : Adr) : Nat :=
  (segments.map fun segment => segment.1.holderOut segment.2 u).sum

def localSegmentsHolderLoss
    (segments : List (LocalSegmentKind × FlowAction)) (u : Adr) : Nat :=
  (segments.map fun segment => segment.1.holderLoss segment.2 u).sum

/-- Exact wrap-aware composition over any contiguous list of local segments. -/
theorem LocalSegmentChain.holder_eq
    {segments : List (LocalSegmentKind × FlowAction)}
    {pre post : HolderBalances}
    (chain : LocalSegmentChain segments pre post) (u : Adr) :
    (pre u).toNat + localSegmentsHolderIn segments u =
      (post u).toNat + localSegmentsHolderOut segments u +
        localSegmentsHolderLoss segments u := by
  induction chain with
  | nil balances =>
      simp [localSegmentsHolderIn, localSegmentsHolderOut,
        localSegmentsHolderLoss]
  | cons head rest ih =>
      have hhead := head.holder_eq u
      simp only [localSegmentsHolderIn, localSegmentsHolderOut,
        localSegmentsHolderLoss] at ih
      simp only [localSegmentsHolderIn, localSegmentsHolderOut,
        localSegmentsHolderLoss, List.map_cons, List.sum_cons]
      omega

end Weth10

end Blanc
