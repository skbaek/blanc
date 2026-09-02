import Blanc.Weth10FutureRedeemable

/-!
Finite any-order message-level redemption for the exact Blanc WETH10 runtime.

A *claim* is a holder, a natural amount, and a recipient.  Given a stable
boundary and a finite list of claims whose per-owner aggregate amounts are
covered by that boundary's booked balances, this module shows that **every
permutation** of the list can be paid out, one canonical redemption message at
a time, with an exact aggregate projection on booked balances and ETH.

Three things about the shape of the result are deliberate.

*Nothing about success is assumed.*  The induction never takes a premise of the
form "every successful prefix is admissible": at each step it *constructs* the
next message envelope out of the current state, feeds it to the sibling
redemption theorem, and re-establishes the admission record for the remaining
claims from that step's exact one-step effect.  The only inputs are the
target's non-precompile status, per-claim recipient facts, and the literal
per-owner aggregate bound.

*Repeated owners are aggregated, not forbidden.*  `ownerClaimTotal` sums the
amounts of **all** claims of an owner, so a list that books the same holder
twice is admissible exactly when the two amounts together fit.  Overbooking is
impossible by the shape of the condition rather than by a distinctness side
condition; `overbooked_not_admissible` records that.

*These messages are not mined.*  `RedemptionRun` is a chain of
`processMessageCall` results threaded through states.  It says nothing about
blocks, transactions, inclusion, ordering by a builder, or fees, and no reading
of it may claim otherwise.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## Claims and their aggregates -/

/-- One holder's request: pay `amount` of `owner`'s booked balance out to
`recipient` as ETH.  A claim is data, not a promise; admissibility below is
what makes it payable. -/
structure RedemptionClaim where
  owner : Adr
  amount : Nat
  recipient : Adr

/-- The additive fold every aggregate below is an instance of. -/
def claimSum (f : RedemptionClaim → Nat) : List RedemptionClaim → Nat
  | [] => 0
  | c :: cs => f c + claimSum f cs

@[simp] theorem claimSum_nil (f : RedemptionClaim → Nat) :
    claimSum f [] = 0 := rfl

@[simp] theorem claimSum_cons (f : RedemptionClaim → Nat)
    (c : RedemptionClaim) (cs : List RedemptionClaim) :
    claimSum f (c :: cs) = f c + claimSum f cs := rfl

theorem claimSum_append (f : RedemptionClaim → Nat)
    (cs ds : List RedemptionClaim) :
    claimSum f (cs ++ ds) = claimSum f cs + claimSum f ds := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, Nat.add_assoc]

/-- Reordering a claim list cannot change any of its aggregates. -/
theorem claimSum_perm {cs ds : List RedemptionClaim} (h : cs.Perm ds)
    (f : RedemptionClaim → Nat) : claimSum f cs = claimSum f ds := by
  induction h with
  | nil => rfl
  | cons c _ ih => simp [ih]
  | swap c d l => simp; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Total ETH the whole list pays out. -/
def claimTotal (cs : List RedemptionClaim) : Nat :=
  claimSum (fun c => c.amount) cs

/-- The amount booked against holder `u` by the list — summed over **every**
claim naming `u`, which is what makes a repeated owner impossible to
overbook. -/
def ownerClaimTotal (cs : List RedemptionClaim) (u : Adr) : Nat :=
  claimSum (fun c => if c.owner = u then c.amount else 0) cs

/-- The ETH the list delivers to `r`, summed over every claim paying `r`. -/
def recipientClaimTotal (cs : List RedemptionClaim) (r : Adr) : Nat :=
  claimSum (fun c => if c.recipient = r then c.amount else 0) cs

@[simp] theorem claimTotal_nil : claimTotal [] = 0 := rfl

@[simp] theorem claimTotal_cons (c : RedemptionClaim)
    (cs : List RedemptionClaim) :
    claimTotal (c :: cs) = c.amount + claimTotal cs := rfl

@[simp] theorem ownerClaimTotal_nil (u : Adr) : ownerClaimTotal [] u = 0 := rfl

@[simp] theorem ownerClaimTotal_cons (c : RedemptionClaim)
    (cs : List RedemptionClaim) (u : Adr) :
    ownerClaimTotal (c :: cs) u =
      (if c.owner = u then c.amount else 0) + ownerClaimTotal cs u := rfl

@[simp] theorem recipientClaimTotal_nil (r : Adr) :
    recipientClaimTotal [] r = 0 := rfl

@[simp] theorem recipientClaimTotal_cons (c : RedemptionClaim)
    (cs : List RedemptionClaim) (r : Adr) :
    recipientClaimTotal (c :: cs) r =
      (if c.recipient = r then c.amount else 0) +
        recipientClaimTotal cs r := rfl

theorem ownerClaimTotal_append (cs ds : List RedemptionClaim) (u : Adr) :
    ownerClaimTotal (cs ++ ds) u =
      ownerClaimTotal cs u + ownerClaimTotal ds u :=
  claimSum_append _ cs ds

theorem claimTotal_perm {cs ds : List RedemptionClaim} (h : cs.Perm ds) :
    claimTotal cs = claimTotal ds := claimSum_perm h _

theorem ownerClaimTotal_perm {cs ds : List RedemptionClaim} (h : cs.Perm ds)
    (u : Adr) : ownerClaimTotal cs u = ownerClaimTotal ds u :=
  claimSum_perm h _

theorem recipientClaimTotal_perm {cs ds : List RedemptionClaim}
    (h : cs.Perm ds) (r : Adr) :
    recipientClaimTotal cs r = recipientClaimTotal ds r :=
  claimSum_perm h _

/-! ## Admission

Every field below is a property of the *boundary state and the claim data
alone*.  None of them mentions an execution, a success, a prefix, or an
accounted history. -/

/-- A claim's recipient is one WETH10 can actually pay: a nonzero, code-free,
non-precompile account.  A holder redeeming to itself qualifies exactly when
the holder does.  The contract itself is excluded automatically rather than by
a field — see `ClaimAdmissible.recipient_ne_target`. -/
structure ClaimAdmissible
    (rules : ForkRules) (_ca : Adr) (w : State) (c : RedemptionClaim) : Prop where
  recipient_ne_zero : c.recipient ≠ 0
  recipient_not_precompile : ¬ rules.isPrecomp c.recipient
  recipient_code_free : (w.getCode c.recipient).toList = []

/-- A payable recipient is never the contract: at a stable boundary the
installed WETH10 runtime is 6313 bytes long, while every claim's recipient is
code-free.  Nothing has to assume this. -/
theorem ClaimAdmissible.recipient_ne_target
    {rules : ForkRules} {dp : DeployParams} {ca : Adr}
    {w : State} {c : RedemptionClaim}
    (hstable : Stable dp ca w) (hadm : ClaimAdmissible rules ca w c) :
    c.recipient ≠ ca := by
  intro hEq
  have hinstalled : (w.getCode ca).toList = weth10Code dp := by
    have h := hstable.code
    rw [weth10Code_compile dp] at h
    exact Option.some.inj h
  have hempty : (w.getCode ca).toList = [] := hEq ▸ hadm.recipient_code_free
  have hlen := weth10Code_length dp
  rw [hinstalled] at hempty
  rw [hempty] at hlen
  simp at hlen

/-- A whole list is admissible when each claim's recipient is payable and each
owner's **aggregate** booking fits inside that owner's booked balance. -/
structure ClaimsAdmissible (rules : ForkRules) (ca : Adr) (w : State)
    (cs : List RedemptionClaim) : Prop where
  recipients : ∀ c ∈ cs, ClaimAdmissible rules ca w c
  budget : ∀ u : Adr, ownerClaimTotal cs u ≤ bookedBalanceNat w ca u

/-- Overbooking is refused by the admission record itself: no list that books
an owner beyond that owner's booked balance is admissible, however its claims
are ordered or split. -/
theorem overbooked_not_admissible {rules : ForkRules} {ca : Adr} {w : State}
    {cs : List RedemptionClaim} {u : Adr}
    (h : bookedBalanceNat w ca u < ownerClaimTotal cs u) :
    ¬ ClaimsAdmissible rules ca w cs := fun hadm =>
  absurd (hadm.budget u) (Nat.not_le_of_lt h)

/-- Two claims on one owner are admissible only against their **sum**. -/
theorem ownerClaimTotal_repeated_owner
    (u r₁ r₂ : Adr) (a₁ a₂ : Nat) :
    ownerClaimTotal [⟨u, a₁, r₁⟩, ⟨u, a₂, r₂⟩] u = a₁ + a₂ := by
  simp [ownerClaimTotal]

/-- Admission is order-insensitive, which is what lets a single admission
record serve every permutation. -/
theorem ClaimsAdmissible.perm {rules : ForkRules} {ca : Adr} {w : State}
    {cs ds : List RedemptionClaim}
    (h : ClaimsAdmissible rules ca w cs) (hperm : cs.Perm ds) :
    ClaimsAdmissible rules ca w ds where
  recipients c hc := h.recipients c (hperm.mem_iff.mpr hc)
  budget u := by
    rw [← ownerClaimTotal_perm hperm u]
    exact h.budget u

/-! ## The canonical redemption envelope

The message below is built from the current state alone.  Its original state is
that same state, its authorization list is empty, its access sets are empty,
and its gas is the sibling development's closed runtime ceiling; nothing in it
records an execution. -/

/-- The fresh `withdrawTo` envelope this development hands to the sibling
redemption theorem at each step. -/
def canonicalRedemptionMessage
    (rules : ForkRules) (ca : Adr) (c : RedemptionClaim) (w : State) : Msg :=
  { benv :=
      { state := w
        createdAccounts := .ofList []
        stat :=
          { rules := rules
            chainId := 0
            origState := w
            blockGasLimit := 0
            blockHashes := []
            coinbase := 0
            number := 0
            baseFeePerGas := 0
            time := 0
            prevRandao := 0
            excessBlobGas := 0
            parentBeaconBlockRoot := 0 } }
    tenv :=
      { transientStorage := .empty
        stat :=
          { origin := c.owner
            gasPrice := 0
            gas := redemptionRuntimeCeiling c.amount
            accessListAddresses := .ofList []
            accessListStorageKeys := .ofList []
            blobVersionedHashes := []
            auths := []
            indexInBlock := none
            txHash := none } }
    caller := c.owner
    target := some ca
    currentTarget := ca
    gas := redemptionRuntimeCeiling c.amount
    value := 0
    data := withdrawToCalldata c.recipient c.amount
    codeAddress := some ca
    code := w.getCode ca
    depth := 1024
    shouldTransferValue := true
    isStatic := false
    accessedAddresses := .ofList []
    accessedStorageKeys := .ofList []
    disablePrecompiles := false }

/-- The constructed envelope is admissible.  Every field is discharged either
by the definition above, by the boundary's stability, or by the claim's own
recipient facts and the independently supplied non-precompile fact about the
contract. -/
theorem canonicalRedemptionMessage_admissible
    {rules : ForkRules} {dp : DeployParams} {ca : Adr}
    {w : State} {c : RedemptionClaim}
    (hca : ¬ rules.isPrecomp ca)
    (hstable : Stable dp ca w)
    (hadm : ClaimAdmissible rules ca w c) :
    AdmissibleRedemptionMessage rules dp ca c.owner c.recipient c.amount w
      (canonicalRedemptionMessage rules ca c w) where
  state_eq := rfl
  rules_eq := rfl
  target_eq := rfl
  currentTarget_eq := rfl
  codeAddress_eq := rfl
  code_eq := hstable.code
  installedCode_eq := rfl
  caller_eq := rfl
  value_eq := rfl
  depth_eq := rfl
  shouldTransferValue_eq := rfl
  isStatic_eq := rfl
  auths_eq := rfl
  disablePrecompiles_eq := rfl
  target_not_precompile := by simp [hca]
  recipient_ne_zero := hadm.recipient_ne_zero
  recipient_not_precompile := by simp [hadm.recipient_not_precompile]
  recipient_code_free := hadm.recipient_code_free
  original_storage_eq := rfl
  target_access :=
    (Classical.em
        (ca ∈ (canonicalRedemptionMessage rules ca c w).accessedAddresses)).elim
      .warm .cold
  recipient_access :=
    (Classical.em
        (c.recipient ∈
          (canonicalRedemptionMessage rules ca c w).accessedAddresses)).elim
      .warm .cold
  owner_storage_access :=
    (Classical.em
      ((ca, c.owner.toB256) ∈
        (canonicalRedemptionMessage rules ca c w).accessedStorageKeys)).elim
      .warm .cold
  recipient_account :=
    (Classical.em ((w.get c.recipient).Empty)).elim .empty .existing
  gas_bound := Nat.le_refl _
  data_eq := rfl
  selector_eq := withdrawToCalldata_selector _ _ _ rfl

/-! ## A message-level redemption sequence

`RedemptionRun` chains the sibling development's *exact one-step effect*: each
link is a fresh admissible envelope, a successful `processMessageCall`, and the
effect that call is proved to have.  It is a statement about messages and
states only.  No link is a transaction, a block, or an entry in an accounted
history, and nothing below may be read as saying these messages were mined. -/

/-- A finite chain of successful canonical redemptions paying `cs` in order,
carrying each step's constructed envelope and exact effect. -/
inductive RedemptionRun (rules : ForkRules) (dp : DeployParams) (ca : Adr) :
    List RedemptionClaim → State → State → Prop
  | nil (w : State) : RedemptionRun rules dp ca [] w w
  | cons {c : RedemptionClaim} {cs : List RedemptionClaim}
      {w mid post : State} {msg : Msg} {out : MsgCallOutput}
      (henv : AdmissibleRedemptionMessage
        rules dp ca c.owner c.recipient c.amount w msg)
      (message_eq : msg = canonicalRedemptionMessage rules ca c w)
      (hrun : processMessageCall msg = .ok (mid, out))
      (heffect : MessageRedemptionExactEffect
        dp ca c.owner c.recipient c.amount w mid out)
      (htail : RedemptionRun rules dp ca cs mid post) :
      RedemptionRun rules dp ca (c :: cs) w post

/-! ## The one-step preservation lemma

This is the engine of the induction.  The sibling's exact effect debits exactly
the paying owner, leaves every other booked balance alone, and preserves all
code; that is precisely enough to rebuild the admission record for the claims
that have not been paid yet — recipients stay payable and every remaining
owner's aggregate still fits. -/

/-- Paying the head claim preserves admission of the tail.  The owner's budget
shrinks by exactly the amount paid, so a repeated owner's remaining claims stay
within its remaining booked balance. -/
theorem ClaimsAdmissible.step
    {rules : ForkRules} {dp : DeployParams} {ca : Adr} {w post : State}
    {c : RedemptionClaim} {cs : List RedemptionClaim} {out : MsgCallOutput}
    (hadm : ClaimsAdmissible rules ca w (c :: cs))
    (heffect : MessageRedemptionExactEffect
      dp ca c.owner c.recipient c.amount w post out) :
    ClaimsAdmissible rules ca post cs where
  recipients c' hc' :=
    have hc : ClaimAdmissible rules ca w c' :=
      hadm.recipients c' (List.mem_cons_of_mem _ hc')
    { recipient_ne_zero := hc.recipient_ne_zero
      recipient_not_precompile := hc.recipient_not_precompile
      recipient_code_free := by
        rw [heffect.codePreserved]
        exact hc.recipient_code_free }
  budget u := by
    have hb := hadm.budget u
    rw [ownerClaimTotal_cons] at hb
    by_cases hu : c.owner = u
    · subst hu
      have hdebit := heffect.ownerDebit
      rw [if_pos (rfl : c.owner = c.owner)] at hb
      omega
    · have hne : u ≠ c.owner := fun h => hu h.symm
      have hother := heffect.otherBookedUnchanged u hne
      rw [if_neg hu] at hb
      omega

/-! ## The aggregate outcome -/

/-- Everything a finite claim list is promised at a stable boundary: the run
itself, a stable end state, the exact aggregate projection on booked balances
and ETH, code preservation, and — the reason the induction closes — the fact
that claims left over are still admissible at the end. -/
structure RedemptionOutcome (rules : ForkRules) (dp : DeployParams) (ca : Adr)
    (cs : List RedemptionClaim) (w post : State) : Prop where
  run : RedemptionRun rules dp ca cs w post
  stable : Stable dp ca post
  booked : ∀ v : Adr,
    bookedBalanceNat post ca v + ownerClaimTotal cs v = bookedBalanceNat w ca v
  contractEth : (post.bal ca).toNat + claimTotal cs = (w.bal ca).toNat
  otherEth : ∀ a : Adr, a ≠ ca →
    (post.bal a).toNat = (w.bal a).toNat + recipientClaimTotal cs a
  sumPreserved : sum post.bal = sum w.bal
  codePreserved : ∀ a : Adr, post.getCode a = w.getCode a
  remaining : ∀ es : List RedemptionClaim,
    ClaimsAdmissible rules ca w (cs ++ es) →
      ClaimsAdmissible rules ca post es

/-! ## The induction -/

/-- **Finite sequencing.** At a stable boundary, an admissible list of claims
is paid out in the order given.

The premises are the independently supplied non-precompile fact about the
contract, the boundary's stability, and the admission record — recipient facts
and the literal per-owner aggregate bound.  There is no premise about
successful prefixes, no envelope supplied from outside, and no accounted
history: each step's envelope is constructed by
`canonicalRedemptionMessage` from that step's own state. -/
theorem redeemClaims_run
    {rules : ForkRules} {dp : DeployParams} {ca : Adr}
    (hca : ¬ rules.isPrecomp ca) :
    ∀ (cs : List RedemptionClaim) (w : State),
      Stable dp ca w → ClaimsAdmissible rules ca w cs →
      ∃ post, RedemptionOutcome rules dp ca cs w post := by
  intro cs
  induction cs with
  | nil =>
      intro w hstable hadm
      exact ⟨w, .nil w, hstable, by simp, by simp, by simp, rfl,
        fun _ => rfl, fun es h => by simpa using h⟩
  | cons c cs ih =>
      intro w hstable hadm
      have hcadm : ClaimAdmissible rules ca w c :=
        hadm.recipients c List.mem_cons_self
      have henv := canonicalRedemptionMessage_admissible hca hstable hcadm
      have hq : c.amount ≤ bookedBalanceNat w ca c.owner := by
        have hb := hadm.budget c.owner
        rw [ownerClaimTotal_cons, if_pos rfl] at hb
        omega
      obtain ⟨mid, out, hrun, heffect⟩ :=
        hstable.messageRedemption_enabled_of_le hq henv
      obtain ⟨post, hout⟩ :=
        ih mid heffect.postStable (hadm.step heffect)
      refine ⟨post, .cons henv rfl hrun heffect hout.run, hout.stable, ?_, ?_, ?_,
        hout.sumPreserved.trans heffect.sumPreserved,
        fun a => (hout.codePreserved a).trans (heffect.codePreserved a), ?_⟩
      · intro v
        have hv := hout.booked v
        rw [ownerClaimTotal_cons]
        by_cases hu : c.owner = v
        · subst hu
          have hdebit := heffect.ownerDebit
          rw [if_pos rfl]
          omega
        · have hother := heffect.otherBookedUnchanged v (fun h => hu h.symm)
          rw [if_neg hu]
          omega
      · have hcontract := heffect.contractEthDebit
        have hv := hout.contractEth
        rw [claimTotal_cons]
        omega
      · intro a ha
        have hv := hout.otherEth a ha
        rw [recipientClaimTotal_cons]
        by_cases hr : c.recipient = a
        · subst hr
          have hcredit := heffect.recipientEthCredit
          rw [if_pos rfl]
          omega
        · have hkeep := heffect.otherEthUnchanged a ha (fun h => hr h.symm)
          rw [hkeep] at hv
          rw [if_neg hr]
          omega
      · intro es hes
        have hcons : ClaimsAdmissible rules ca w (c :: (cs ++ es)) := hes
        exact hout.remaining es (hcons.step heffect)

/-! ## Any order -/

/-- **The finite any-order corollary.** At a stable boundary carrying an
independently supplied `¬ rules.isPrecomp ca`, an admissible finite list
of claims is payable in **every** order: each permutation has its own
successful message-level redemption sequence, ending stable, with the exact
aggregate projection and the remaining claims still admissible.

Repeated owners are aggregated rather than forbidden: `ClaimsAdmissible`'s
budget field bounds each owner's *total* booking, so no ordering can overbook.
Nothing here asserts that these messages were included in a block. -/
theorem redeemClaims_anyOrder
    {rules : ForkRules} {dp : DeployParams} {ca : Adr} {w : State}
    {cs ds : List RedemptionClaim}
    (hca : ¬ rules.isPrecomp ca)
    (hstable : Stable dp ca w)
    (hadm : ClaimsAdmissible rules ca w cs)
    (hperm : cs.Perm ds) :
    ∃ post, RedemptionOutcome rules dp ca ds w post :=
  redeemClaims_run hca ds w hstable (hadm.perm hperm)

/-- Order does not matter economically either: two permutations of one
admissible list end at states with the same booked balances and the same ETH
balance at every address. -/
theorem redeemClaims_order_independent
    {rules : ForkRules} {dp : DeployParams} {ca : Adr} {w : State}
    {cs ds es : List RedemptionClaim}
    (hca : ¬ rules.isPrecomp ca)
    (hstable : Stable dp ca w)
    (hadm : ClaimsAdmissible rules ca w cs)
    (hd : cs.Perm ds) (he : cs.Perm es) :
    ∃ post post',
      RedemptionOutcome rules dp ca ds w post ∧
      RedemptionOutcome rules dp ca es w post' ∧
      (∀ v : Adr, bookedBalanceNat post ca v = bookedBalanceNat post' ca v) ∧
      (∀ a : Adr, (post.bal a).toNat = (post'.bal a).toNat) := by
  obtain ⟨post, hpost⟩ := redeemClaims_anyOrder hca hstable hadm hd
  obtain ⟨post', hpost'⟩ := redeemClaims_anyOrder hca hstable hadm he
  refine ⟨post, post', hpost, hpost', ?_, ?_⟩
  · intro v
    have h1 := hpost.booked v
    have h2 := hpost'.booked v
    have hsame : ownerClaimTotal ds v = ownerClaimTotal es v := by
      rw [← ownerClaimTotal_perm hd v, ownerClaimTotal_perm he v]
    omega
  · intro a
    by_cases ha : a = ca
    · subst ha
      have h1 := hpost.contractEth
      have h2 := hpost'.contractEth
      have hsame : claimTotal ds = claimTotal es := by
        rw [← claimTotal_perm hd, claimTotal_perm he]
      omega
    · have h1 := hpost.otherEth a ha
      have h2 := hpost'.otherEth a ha
      have hsame : recipientClaimTotal ds a = recipientClaimTotal es a := by
        rw [← recipientClaimTotal_perm hd a, recipientClaimTotal_perm he a]
      omega

/-- The two opposite orders of one admissible list, side by side. -/
theorem redeemClaims_reverse_order
    {rules : ForkRules} {dp : DeployParams} {ca : Adr}
    {w : State} {cs : List RedemptionClaim}
    (hca : ¬ rules.isPrecomp ca)
    (hstable : Stable dp ca w)
    (hadm : ClaimsAdmissible rules ca w cs) :
    ∃ post post',
      RedemptionOutcome rules dp ca cs w post ∧
      RedemptionOutcome rules dp ca cs.reverse w post' ∧
      (∀ v : Adr, bookedBalanceNat post ca v = bookedBalanceNat post' ca v) ∧
      (∀ a : Adr, (post.bal a).toNat = (post'.bal a).toNat) :=
  redeemClaims_order_independent hca hstable hadm (List.Perm.refl cs)
    (List.reverse_perm cs).symm

/-- Both orders of a two-claim list execute. -/
theorem redeemClaims_twoOrders
    {rules : ForkRules} {dp : DeployParams} {ca : Adr}
    {w : State} {c₁ c₂ : RedemptionClaim}
    (hca : ¬ rules.isPrecomp ca)
    (hstable : Stable dp ca w)
    (hadm : ClaimsAdmissible rules ca w [c₁, c₂]) :
    (∃ post, RedemptionOutcome rules dp ca [c₁, c₂] w post) ∧
      (∃ post, RedemptionOutcome rules dp ca [c₂, c₁] w post) :=
  ⟨redeemClaims_anyOrder hca hstable hadm (List.Perm.refl _),
    redeemClaims_anyOrder hca hstable hadm (List.Perm.swap c₂ c₁ [])⟩

/-- Two claims on the *same* owner are admissible exactly against their sum;
`redeemClaims_twoOrders` then pays them in either order. -/
theorem repeatedOwner_admissible
    {rules : ForkRules} {ca : Adr} {w : State}
    {u r₁ r₂ : Adr} {a₁ a₂ : Nat}
    (h₁ : ClaimAdmissible rules ca w ⟨u, a₁, r₁⟩)
    (h₂ : ClaimAdmissible rules ca w ⟨u, a₂, r₂⟩)
    (hbudget : a₁ + a₂ ≤ bookedBalanceNat w ca u) :
    ClaimsAdmissible rules ca w [⟨u, a₁, r₁⟩, ⟨u, a₂, r₂⟩] where
  recipients c hc := by
    rcases List.mem_cons.mp hc with h | h
    · exact h ▸ h₁
    · rcases List.mem_cons.mp h with h' | h'
      · exact h' ▸ h₂
      · exact absurd h' (List.not_mem_nil)
  budget v := by
    by_cases hv : u = v
    · subst hv
      simpa [ownerClaimTotal] using hbudget
    · simp [ownerClaimTotal, hv]

/-! ## A supplied everyone-list instance -/

/-- One full-balance self-contained claim per supplied holder.  The recipient
map is explicit because receiver admissibility is real theorem content. -/
def fullBalanceClaims (ca : Adr) (w : State)
    (holders : List Adr) (recipient : Adr → Adr) : List RedemptionClaim :=
  holders.map fun u => ⟨u, bookedBalanceNat w ca u, recipient u⟩

/-- With no duplicate holder, the aggregate claim for a listed owner is
exactly that owner's full booked balance; unlisted owners have zero claim. -/
theorem ownerClaimTotal_fullBalanceClaims
    {ca : Adr} {w : State} {holders : List Adr} {recipient : Adr → Adr}
    (hnodup : holders.Nodup) (u : Adr) :
    ownerClaimTotal (fullBalanceClaims ca w holders recipient) u =
      if u ∈ holders then bookedBalanceNat w ca u else 0 := by
  induction holders with
  | nil => simp [fullBalanceClaims, ownerClaimTotal]
  | cons v holders ih =>
      have hv : v ∉ holders := (List.nodup_cons.mp hnodup).1
      have htail : holders.Nodup := (List.nodup_cons.mp hnodup).2
      rw [fullBalanceClaims]
      simp only [List.map_cons, ownerClaimTotal_cons]
      change (if v = u then bookedBalanceNat w ca v else 0) +
          ownerClaimTotal (fullBalanceClaims ca w holders recipient) u =
        if u ∈ v :: holders then bookedBalanceNat w ca u else 0
      rw [ih htail]
      by_cases hvu : v = u
      · subst v
        simp [hv]
      · have huv : u ≠ v := fun h => hvu h.symm
        simp [hvu, huv]

/-- Any permutation of a duplicate-free supplied holder list's full-balance
claims runs successfully, provided its explicitly chosen recipients are
admissible.  This is the precise finite-list “everyone out” instance. -/
theorem redeemEveryoneList_anyOrder
    {rules : ForkRules} {dp : DeployParams} {ca : Adr} {w : State}
    {holders : List Adr} {recipient : Adr → Adr}
    {claims : List RedemptionClaim}
    (hca : ¬ rules.isPrecomp ca)
    (hstable : Stable dp ca w)
    (hnodup : holders.Nodup)
    (hrecipients : ∀ u ∈ holders,
      ClaimAdmissible rules ca w
        ⟨u, bookedBalanceNat w ca u, recipient u⟩)
    (hperm : (fullBalanceClaims ca w holders recipient).Perm claims) :
    ∃ post, RedemptionOutcome rules dp ca claims w post := by
  have hadm : ClaimsAdmissible rules ca w
      (fullBalanceClaims ca w holders recipient) := by
    refine ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_map.mp hc with ⟨u, hu, rfl⟩
      exact hrecipients u hu
    · intro u
      rw [ownerClaimTotal_fullBalanceClaims hnodup u]
      by_cases hu : u ∈ holders
      · simp [hu]
      · simp [hu]
  exact redeemClaims_anyOrder hca hstable hadm hperm

/-! ## The deployment-rooted instance -/

/-- A holder redeeming to itself: the recipient is the equally qualified
owner. -/
def selfClaim (u : Adr) (a : Nat) : RedemptionClaim := ⟨u, a, u⟩

/-- A self-paying claim is admissible on exactly the holder's own qualifying
facts. -/
theorem ClaimAdmissible.self {rules : ForkRules} {ca : Adr}
    {w : State} {u : Adr} {a : Nat}
    (hzero : u ≠ 0) (hprecomp : ¬ rules.isPrecomp u)
    (hcode : (w.getCode u).toList = []) :
    ClaimAdmissible rules ca w (selfClaim u a) where
  recipient_ne_zero := hzero
  recipient_not_precompile := hprecomp
  recipient_code_free := hcode

/-- **The flagship instance.** At any configured future of a verified
WETH10 deployment, every permutation of an admissible finite claim list has a
successful message-level redemption sequence.

The global non-precompile fact is supplied by the deployment root, not assumed
here, and the boundary's stability comes from the stability development.  This
remains a message/state-level statement: it does not claim a block step,
transaction inclusion, or that any of these messages was mined. -/
theorem deployment_reachable_redeemClaims_anyOrder
    {cfg : ChainConfig} {rules : ForkRules} {timestamp : Nat}
    {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {cs ds : List RedemptionClaim}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hrules : cfg.rulesAt timestamp = .ok rules)
    (hadm : ClaimsAdmissible rules ca future.state cs)
    (hperm : cs.Perm ds) :
    ∃ post, RedemptionOutcome rules dp ca ds future.state post :=
  redeemClaims_anyOrder (hroot.target_not_precompile hrules)
    (hroot.reachable_stable hfuture) hadm hperm

/-- The deployment-rooted full-balance instance for any supplied
duplicate-free holder list and admissible recipient map. -/
theorem deployment_reachable_redeemEveryoneList_anyOrder
    {cfg : ChainConfig} {rules : ForkRules} {timestamp : Nat}
    {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {holders : List Adr}
    {recipient : Adr → Adr} {claims : List RedemptionClaim}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hrules : cfg.rulesAt timestamp = .ok rules)
    (hnodup : holders.Nodup)
    (hrecipients : ∀ u ∈ holders,
      ClaimAdmissible rules ca future.state
        ⟨u, bookedBalanceNat future.state ca u, recipient u⟩)
    (hperm :
      (fullBalanceClaims ca future.state holders recipient).Perm claims) :
    ∃ post, RedemptionOutcome rules dp ca claims future.state post :=
  redeemEveryoneList_anyOrder (hroot.target_not_precompile hrules)
    (hroot.reachable_stable hfuture) hnodup hrecipients hperm

end Weth10

end Blanc
