import Blanc.Weth10Hardened

/-!
Hardened floor and the dormant-holder reduction.

The first result is the conservation goal's residual floor rewritten through
the collision-free attribution equality: a holder's checkpoint booked balance
is covered by its future booked balance plus the *hardened* outflow, the
sub-sum whose debits carry an attribution witness.

The rest is the ledger-level content of the dormant-holder corollary.  A
counted record that carries permanent outflow for `u` while `u` performs no
authorizing act is forced into exactly one shape: an allowance-branch debit at
a key whose owner word normalizes to `u`, governed by the *checkpoint* rather
than by any counted `approve` or `permit`.  Both authorizing roots are
excluded by `NoAuthorizingActBy`, the pair identification being the same
collision step the attribution equality consumes.

That surviving shape is the corollary's residual.  Excluding it needs the
value the runtime actually read at the debited key, which the endpoint
transport `AccountedHistory.allowanceTransported_of_compiled` never exposes:
that statement relates the checkpoint and the future only.  Measured against
it alone the residual travels as an explicit hypothesis of
`dormant_holder_balance_monotone_of_checkpointRooted`; nothing below assumes
it away.

The residual is then sharpened.  Reading a record's own allowance word back
out of the executed program needs the producing frame's root context, which
`CountedFrame.HasFrameOrigin` drops; the rooted-origin tower of
`Blanc.Weth10Hardened` supplies it, and
`CountedFrame.permanentOutflow_eq_zero_of_read_zero` then shows that a
delegated debit which read a zero word spends nothing.  That retires the
`attributionRootAt` residual in favour of a single read statement about the
counted ledger, carried by `dormant_holder_balance_monotone_of_zeroReads`.

The final part of the module discharges that read statement outright, so the
corollary stands with no residual hypothesis at all.  The read-sound transport
`AccountedHistory.allowanceTransportedSound_of_compiled` identifies each
record's recorded read with the replay of the ledger prefix strictly before
it, and an induction along the ledger keeps that replay at zero on every one
of the holder's own touched keys.  `AllowanceQuiescent` is the base; each of
the four writing visits either is an authorizing act of the holder — excluded
by `NoAuthorizingActBy` — or is a decrement the runtime bounded by the very
word it read. -/

namespace Blanc

open Jaune

namespace Weth10

/-! ## The hardened floor -/

/-- A holder's checkpoint booked balance is covered by its future booked
balance plus the hardened sub-sum of its permanent outflow. -/
theorem holderFlow_hardened_floor
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Weth10.Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history) :
    bookedBalanceNat checkpoint.state ca u <=
      bookedBalanceNat future.state ca u + hardenedOutflow history u := by
  rw [← permanentOutflow_eq_hardenedOutflow_of_noCollision hstable history hnc]
  exact holderFlow_residual_floor hstable history

/-! ## Frame-local caller projections

The counted record, its debit provenance and its allowance event are computed
from one entry context, so all three agree on the acting caller. -/

/-- Every retained debit provenance records the visiting frame's caller. -/
theorem primaryDebitProvenance_actualCaller {e : Sevm} {pre post : Devm}
    {debit : DebitProvenance}
    (hdebit : primaryDebitProvenance e pre post = some debit) :
    debit.actualCaller = e.caller := by
  simp only [primaryDebitProvenance] at hdebit
  split_ifs at hdebit <;> (cases hdebit; rfl)

/-- Every recorded allowance event records the visiting frame's caller. -/
theorem frameAllowanceEvent_caller {e : Sevm} {pre post : Devm}
    {event : AllowanceEvent}
    (hevent : frameAllowanceEvent e pre post = some event) :
    event.caller = e.caller := by
  simp only [frameAllowanceEvent] at hevent
  split_ifs at hevent <;> (cases hevent; rfl)

/-! ## The entry read behind a delegated debit

A record's rooted origin is what turns the ledger's recorded allowance word
back into a fact about the executed program: the compiled
`transferFrom`/`withdrawFrom` theorems need the producing frame's fresh entry
memory and its compiled code word, both of which `HasFrameOrigin` drops and
`HasRootedOrigin` retains.  The consequence below is purely frame-local: the
runtime's accepted finite arm bounds the requested amount by the word it read,
so a delegated debit that read zero spends zero and moves no balance. -/

/-- A retained delegated debit pins its invocation: only the two delegated
selectors record one, only a raw source word distinct from the caller's word
leaves the self-bypass arm, and the inspected key is the runtime's own. -/
private theorem delegatedKey_inv {e : Sevm} {pre post : Devm}
    {debit : DebitProvenance} {key : B256}
    (hdebit : primaryDebitProvenance e pre post = some debit)
    (hkey : delegatedKey? debit.branch = some key) :
    e.data.length.toB256 ≠ 0 ∧
      (Sevm.selector e = transferFromSelector ∨
        Sevm.selector e = withdrawFromSelector) ∧
      Sevm.argWord e 0 ≠ e.caller.toB256 ∧
      key = callerAllowanceRuntimeKey e := by
  have hdelegated : debit.branch = .delegated (callerAllowanceBranch e pre 2) →
      Sevm.argWord e 0 ≠ e.caller.toB256 ∧
        key = callerAllowanceRuntimeKey e := by
    intro hbranch
    rw [hbranch] at hkey
    by_cases hself : Sevm.argWord e 0 = e.caller.toB256
    · rw [show callerAllowanceBranch e pre 2 = .selfBypass by
        simp [callerAllowanceBranch, hself]] at hkey
      simp [delegatedKey?] at hkey
    · refine ⟨hself, ?_⟩
      simp only [callerAllowanceBranch, if_neg hself] at hkey
      split at hkey <;> simpa [delegatedKey?] using hkey.symm
  simp only [primaryDebitProvenance] at hdebit
  split_ifs at hdebit with h1 h2 h3 h4 h5
  all_goals (try cases hdebit)
  all_goals
    first
      | exact ⟨h1, Or.inl h3, hdelegated rfl⟩
      | exact ⟨h1, Or.inr h4, hdelegated rfl⟩
      | simp [delegatedKey?] at hkey

/-- The allowance event of a delegated invocation reports the exact word the
runtime read at its own entry state. -/
private theorem frameAllowanceEvent_spend_read
    {e : Sevm} {pre post : Devm} {event : AllowanceEvent}
    (hnonempty : e.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector e = transferFromSelector ∨
      Sevm.selector e = withdrawFromSelector)
    (hnotself : Sevm.argWord e 0 ≠ e.caller.toB256)
    (hevent : frameAllowanceEvent e pre post = some event) :
    event.visit.read? =
      some ((Devm.getStor pre e.currentTarget).get
        (callerAllowanceRuntimeKey e)) := by
  have hshape : frameAllowanceEvent e pre post = some
      { owner := Sevm.argWord e 0
        spender := e.caller.toB256
        caller := e.caller
        depth := e.depth
        visit :=
          let before :=
            (Devm.getStor pre e.currentTarget).get
              (callerAllowanceRuntimeKey e)
          if before = B256.max then .spendMax
          else .spendFinite before (before - Sevm.argWord e 2) } := by
    rcases hsel with h | h
    · simp [frameAllowanceEvent, hnonempty, h, hnotself,
        transferFromSelector_ne_approveSelector,
        transferFromSelector_ne_approveAndCallSelector,
        transferFromSelector_ne_permitSelector]
    · simp [frameAllowanceEvent, hnonempty, h, hnotself,
        withdrawFromSelector_ne_approveSelector,
        withdrawFromSelector_ne_approveAndCallSelector,
        withdrawFromSelector_ne_permitSelector,
        withdrawFromSelector_ne_transferFromSelector]
  rw [hshape] at hevent
  cases hevent
  by_cases hmax : (Devm.getStor pre e.currentTarget).get
      (callerAllowanceRuntimeKey e) = B256.max
  · simp [AllowanceVisit.read?, hmax]
  · simp [AllowanceVisit.read?, hmax]

/-- A rooted delegated invocation that read a zero allowance word requested a
zero amount: the accepted finite arm bounds the request by the word read, and
the maximum arm is impossible at a zero word. -/
private theorem argWord_two_toNat_eq_zero_of_read_zero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hroot : frame.IsRoot) (hexact : frame.exactInvocation dp ca)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector frame.sevm = transferFromSelector ∨
      Sevm.selector frame.sevm = withdrawFromSelector)
    (hnotself : Sevm.argWord frame.sevm 0 ≠ frame.sevm.caller.toB256)
    (hzero : (Devm.getStor frame.pre frame.sevm.currentTarget).get
      (callerAllowanceRuntimeKey frame.sevm) = 0) :
    (Sevm.argWord frame.sevm 2).toNat = 0 := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := hroot.1
      subst pc
      have hwf : Mem.Wf pre.memory := by rw [hroot.2]; exact Mem.wf_empty
      have hreads : Mem.Reads pre.memory [] := by
        rw [hroot.2]; exact Mem.reads_empty
      obtain ⟨corePre, houtcome⟩ :
          ∃ corePre, CallerAllowanceOutcome e pre corePre 2 := by
        rcases hsel with h | h
        · obtain ⟨corePre, houtcome, -⟩ :=
            (weth10_transferFrom_successEffect dp hwf hreads run
              hexact.2.2.2
              (by simpa only [transferFromSelector] using h) hnonempty).2
          exact ⟨corePre, houtcome⟩
        · obtain ⟨corePre, houtcome, -⟩ :=
            (weth10_withdrawFrom_successEffect dp hwf hreads run
              hexact.2.2.2
              (by simpa only [withdrawFromSelector] using h) hnonempty).2
          exact ⟨corePre, houtcome⟩
      obtain ⟨branch, haccepted⟩ := exists_callerAllowanceAccepted houtcome
      cases branch with
      | selfBypass => exact absurd haccepted.2 hnotself
      | maximum key =>
          obtain ⟨-, hkey, hmax⟩ := haccepted.2
          rw [hkey, hzero] at hmax
          exact absurd hmax (by decide)
      | finite key before after =>
          obtain ⟨-, hkey, hget, -, hle, -⟩ := haccepted.2
          rw [hkey, hzero] at hget
          rw [← hget] at hle
          have hnat := B256.toNat_le_toNat hle
          have hzeroNat : B256.toNat 0 = 0 := rfl
          rw [hzeroNat] at hnat
          exact Nat.le_zero.mp hnat

/-- Both delegated selectors record the requested word as their atom's
amount, so a zero request carries no permanent outflow. -/
private theorem outflow_eq_zero_of_argWord_two_toNat_zero
    {e : Sevm} {atom : FlowAtom} {u : Adr}
    (hnonempty : e.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector e = transferFromSelector ∨
      Sevm.selector e = withdrawFromSelector)
    (hprimary : primaryFlowAtom e = some atom)
    (hamount : (Sevm.argWord e 2).toNat = 0) :
    atom.outflow u = 0 := by
  have hzeroAtom : ∀ atom : FlowAtom,
      ((∃ raw src eth, atom = .redemption raw src eth 0) ∨
        ∃ rs rr s r, atom = .transfer rs rr s r 0) → atom.outflow u = 0 := by
    rintro _ (⟨raw, src, eth, rfl⟩ | ⟨rs, rr, s, r, rfl⟩)
    · by_cases hsrc : src = u <;>
        simp [FlowAtom.outflow, FlowAtom.holderFlow, HolderFlow.zero, hsrc]
    · by_cases hs : s = u <;> by_cases hr : r = u <;>
        simp [FlowAtom.outflow, FlowAtom.holderFlow, HolderFlow.zero, hs, hr]
  refine hzeroAtom atom ?_
  rw [← hamount]
  rcases hsel with h | h
  · have hchain : primaryFlowAtom e =
        (if Sevm.argWord e 1 = 0 then
          some (FlowAtom.redemption (Sevm.argWord e 0)
            (Sevm.argWord e 0).toAdr e.caller (Sevm.argWord e 2).toNat)
        else
          some (FlowAtom.transfer (Sevm.argWord e 0) (Sevm.argWord e 1)
            (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toAdr
            (Sevm.argWord e 2).toNat)) := by
      simp [primaryFlowAtom, hnonempty, h,
        transferFromSelector_ne_depositSelector,
        transferFromSelector_ne_depositToSelector,
        transferFromSelector_ne_depositToAndCallSelector,
        transferFromSelector_ne_transferSelector,
        transferFromSelector_ne_transferAndCallSelector]
    rw [hchain] at hprimary
    by_cases hto : Sevm.argWord e 1 = 0
    · rw [if_pos hto] at hprimary
      cases hprimary
      exact Or.inl ⟨_, _, _, rfl⟩
    · rw [if_neg hto] at hprimary
      cases hprimary
      exact Or.inr ⟨_, _, _, _, rfl⟩
  · have hchain : primaryFlowAtom e =
        some (FlowAtom.redemption (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
          (Sevm.argWord e 1).toAdr (Sevm.argWord e 2).toNat) := by
      simp [primaryFlowAtom, hnonempty, h,
        withdrawFromSelector_ne_depositSelector,
        withdrawFromSelector_ne_depositToSelector,
        withdrawFromSelector_ne_depositToAndCallSelector,
        withdrawFromSelector_ne_transferSelector,
        withdrawFromSelector_ne_transferAndCallSelector,
        withdrawFromSelector_ne_transferFromSelector,
        withdrawFromSelector_ne_withdrawSelector,
        withdrawFromSelector_ne_withdrawToSelector]
    rw [hchain] at hprimary
    cases hprimary
    exact Or.inl ⟨_, _, _, rfl⟩

/-- **The entry-read reduction.**  A rooted counted record whose own allowance
event reports a zero read carries no permanent outflow for a holder who takes
no direct act: the debit is either that holder's own act — excluded — or the
delegated arm, whose requested amount the runtime bounded by the zero word it
read. -/
theorem CountedFrame.permanentOutflow_eq_zero_of_read_zero
    {dp : DeployParams} {ca u : Adr} {record : CountedFrame}
    {event : AllowanceEvent}
    (horigin : record.HasRootedOrigin dp ca)
    (hself : record.authorizes u = false)
    (hevent : record.allowance = some event)
    (hread : ∀ value, event.visit.read? = some value → value = 0) :
    record.permanentOutflow u = 0 := by
  by_contra hout
  obtain ⟨frame, rfl, hroot, hexact⟩ := horigin
  obtain ⟨action, haction⟩ :
      ∃ action, (CountedFrame.ofFrame dp ca frame).action = some action := by
    cases haction : (CountedFrame.ofFrame dp ca frame).action with
    | none =>
        exact absurd
          (by rw [CountedFrame.permanentOutflow_eq, haction]) hout
    | some action => exact ⟨action, rfl⟩
  have hatomout : action.atom.outflow u ≠ 0 := by
    rw [CountedFrame.permanentOutflow_eq, haction] at hout
    exact hout
  obtain ⟨hprimary, -⟩ :=
    Exec.Frame.flowAction?_inv (dp := dp) (ca := ca) haction
  obtain ⟨debit, hdebit, hwitness⟩ :=
    primaryDebit_witness (pre := frame.pre) (post := frame.post)
      hprimary hatomout
  rcases hwitness with ⟨-, hcaller⟩ | ⟨ev, hev, -, hkey⟩
  · have hrecordCaller : (CountedFrame.ofFrame dp ca frame).caller = u := by
      show frame.sevm.caller = u
      rw [← primaryDebitProvenance_actualCaller hdebit]
      exact hcaller
    simp [CountedFrame.authorizes, hrecordCaller] at hself
  · have hevEq : ev = event := by
      have hrec : frameAllowanceEvent frame.sevm frame.pre frame.post =
          some event := hevent
      rw [hev] at hrec
      exact Option.some.inj hrec
    subst hevEq
    obtain ⟨hnonempty, hsel, hnotself, -⟩ := delegatedKey_inv hdebit hkey
    have hentry := frameAllowanceEvent_spend_read hnonempty hsel hnotself hev
    exact hatomout
      (outflow_eq_zero_of_argWord_two_toNat_zero hnonempty hsel hprimary
        (argWord_two_toNat_eq_zero_of_read_zero hroot hexact hnonempty hsel
          hnotself (hread _ hentry)))

/-! ## The dormant reduction

A counted record that carries permanent outflow for a dormant holder cannot
be that holder's own direct act, and cannot be governed by a counted
`approve` or `permit`: the first is excluded because the debit's actual caller
is the record's own caller, and the other two because the collision step
identifies the governing store's raw pair with the debit's own pair, whose
owner word normalizes to the holder.  Exactly one shape survives — an
allowance-branch debit at the holder's own key whose governing root is the
checkpoint. -/

/-- Under trace-local collision freedom, a counted record carrying permanent
outflow for a holder who performs no authorizing act — neither on this record
nor on any earlier one — records an allowance event whose owner word
normalizes to that holder and whose governing attribution root is the
checkpoint. -/
theorem CountedFrame.checkpointRooted_of_dormant
    {dp : DeployParams} {ca : Adr} (u : Adr)
    {record : CountedFrame} {recent : List CountedFrame}
    (horigin : record.HasFrameOrigin dp ca)
    (hrecent : ∀ other ∈ recent, other.HasFrameOrigin dp ca)
    (hcross : ∀ p ∈ touchedPairs recent, ∀ q ∈ touchedPairs [record],
      NoCollisionRel p q)
    (hself : record.authorizes u = false)
    (hearlier : ∀ other ∈ recent, other.authorizes u = false)
    (hout : record.permanentOutflow u ≠ 0) :
    ∃ event, record.allowance = some event ∧ event.owner.toAdr = u ∧
      attributionRootAt recent event.key = .checkpoint := by
  rcases horigin with ⟨frame, rfl⟩
  obtain ⟨action, haction⟩ :
      ∃ action, (CountedFrame.ofFrame dp ca frame).action = some action := by
    cases haction : (CountedFrame.ofFrame dp ca frame).action with
    | none =>
        exact absurd
          (by rw [CountedFrame.permanentOutflow_eq, haction]) hout
    | some action => exact ⟨action, rfl⟩
  have hatomout : action.atom.outflow u ≠ 0 := by
    rw [CountedFrame.permanentOutflow_eq, haction] at hout
    exact hout
  obtain ⟨hprimary, -⟩ :=
    Exec.Frame.flowAction?_inv (dp := dp) (ca := ca) haction
  obtain ⟨debit, hdebit, hwitness⟩ :=
    primaryDebit_witness (pre := frame.pre) (post := frame.post)
      hprimary hatomout
  rcases hwitness with ⟨-, hcaller⟩ | ⟨event, hevent, howner, hkey⟩
  · exfalso
    have hrecordCaller : (CountedFrame.ofFrame dp ca frame).caller = u := by
      show frame.sevm.caller = u
      rw [← primaryDebitProvenance_actualCaller hdebit]
      exact hcaller
    simp [CountedFrame.authorizes, hrecordCaller] at hself
  · refine ⟨event, hevent, howner, ?_⟩
    rcases attributionRootAt_cases recent event.key with
      hroot | ⟨other, hother, ev, hev, hevkey, hcase⟩
    · exact hroot
    · exfalso
      have hpair : (ev.owner, ev.spender) = (event.owner, event.spender) := by
        by_contra hne
        exact hcross (ev.owner, ev.spender)
          (mem_touchedPairs.mpr ⟨other, hother, ev, hev, rfl⟩)
          (event.owner, event.spender)
          (mem_touchedPairs.mpr
            ⟨CountedFrame.ofFrame dp ca frame, List.mem_cons_self,
              event, hevent, rfl⟩)
          hne hevkey
      have hownerEq : ev.owner = event.owner := congrArg Prod.fst hpair
      have hevOwner : ev.owner.toAdr = u := by rw [hownerEq]; exact howner
      have hotherDormant := hearlier other hother
      rcases hcase with ⟨⟨_, hvisit⟩, -⟩ | ⟨⟨_, hvisit⟩, -⟩
      · rcases hrecent other hother with ⟨otherFrame, rfl⟩
        have hclean : ev.owner = ev.caller.toB256 :=
          frameAllowanceEvent_approveStore_owner hev hvisit
        have hevCaller : ev.caller = u := by
          rw [← toAdr_toB256 ev.caller, ← hclean, hevOwner]
        have hotherCaller :
            (CountedFrame.ofFrame dp ca otherFrame).caller = u := by
          show otherFrame.sevm.caller = u
          rw [← frameAllowanceEvent_caller hev]
          exact hevCaller
        simp [CountedFrame.authorizes, hotherCaller] at hotherDormant
      · simp [CountedFrame.authorizes, hev, hvisit, hevOwner] at hotherDormant

/-! ## The ledger fold

The reduction is consumed one record at a time, with the same chronological
bookkeeping the attribution equality uses: the fold's accumulated `recent`
stream is the reversal of the ledger prefix already consumed. -/

/-- Chronological form of the dormant reduction: every record of a dormant
holder's ledger carries zero permanent outflow, provided the surviving
checkpoint-rooted shape is excluded. -/
private theorem ledgerOutflow_eq_zero_of_dormant_go
    {dp : DeployParams} {ca : Adr} (u : Adr) (whole : List CountedFrame)
    (horigins : ∀ record ∈ whole, record.HasFrameOrigin dp ca)
    (hdormant : ∀ record ∈ whole, record.authorizes u = false)
    (hpairs : (touchedPairs whole).Pairwise NoCollisionRel)
    (hcheckpoint : ∀ earlier record later,
      whole = earlier ++ record :: later →
      ∀ event, record.allowance = some event → event.owner.toAdr = u →
        attributionRootAt earlier.reverse event.key = .checkpoint →
        record.permanentOutflow u = 0) :
    ∀ rest recent : List CountedFrame, recent.reverse ++ rest = whole →
      ledgerOutflow u rest = 0 := by
  intro rest
  induction rest with
  | nil => intro _ _; rfl
  | cons record tail ih =>
      intro recent hchain
      have hmemWhole : ∀ other ∈ recent, other ∈ whole := by
        intro other hother
        rw [← hchain]
        exact List.mem_append_left _ (List.mem_reverse.mpr hother)
      have hrecordWhole : record ∈ whole := by
        rw [← hchain]
        exact List.mem_append_right _ List.mem_cons_self
      have hsplit : (touchedPairs recent.reverse ++
          touchedPairs (record :: tail)).Pairwise NoCollisionRel := by
        rw [← touchedPairs_append, hchain]
        exact hpairs
      obtain ⟨-, -, hcross⟩ := List.pairwise_append.mp hsplit
      have hhead : record.permanentOutflow u = 0 := by
        by_contra hout
        obtain ⟨event, hevent, howner, hroot⟩ :=
          CountedFrame.checkpointRooted_of_dormant u
            (horigins record hrecordWhole)
            (fun other hother => horigins other (hmemWhole other hother))
            (fun p hp q hq => by
              refine hcross p (mem_touchedPairs_reverse.mpr hp) q ?_
              rcases mem_touchedPairs.mp hq with ⟨other, hother, ev, hev, hq⟩
              rw [List.mem_singleton] at hother
              exact mem_touchedPairs.mpr ⟨other, by simp [hother], ev, hev, hq⟩)
            (hdormant record hrecordWhole)
            (fun other hother => hdormant other (hmemWhole other hother))
            hout
        exact hout
          (hcheckpoint recent.reverse record tail hchain.symm event hevent
            howner (by rwa [List.reverse_reverse]))
      show record.permanentOutflow u + ledgerOutflow u tail = 0
      rw [hhead, ih (record :: recent) (by simpa using hchain), Nat.add_zero]

/-- A dormant holder's public permanent outflow is zero, provided no counted
record debits that holder's balance through a checkpoint-governed allowance
branch.  The residual hypothesis is exactly the shape left standing by
`CountedFrame.checkpointRooted_of_dormant`. -/
theorem AccountedHistory.permanentOutflow_eq_zero_of_dormant
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history)
    (hdormant : NoAuthorizingActBy u history)
    (hcheckpoint : ∀ earlier record later,
      history.attributionLedger = earlier ++ record :: later →
      ∀ event, record.allowance = some event → event.owner.toAdr = u →
        attributionRootAt earlier.reverse event.key = .checkpoint →
        record.permanentOutflow u = 0) :
    (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut = 0 := by
  rw [← history.ledgerOutflow_eq_permanentOutflow]
  refine ledgerOutflow_eq_zero_of_dormant_go u history.attributionLedger
    history.ledgerMirrors.origins hdormant ?_ hcheckpoint
    history.attributionLedger [] (by simp)
  rw [← touchedAllowancePairs_eq_touchedPairs history]
  exact hnc

/-- The dormant-holder corollary, reduced to its checkpoint-rooted residual:
a dormant holder's booked balance never decreases across an authentic
collision-free history.

`_hquiet` is the premise the residual hypothesis consumes — a
checkpoint-governed allowance debit reads the checkpoint value, which
`AllowanceQuiescent` forces to zero — and so is unused in this reduction
itself.  The residual-free `dormant_holder_balance_monotone` below consumes
it for real. -/
theorem dormant_holder_balance_monotone_of_checkpointRooted
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Weth10.Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history)
    (_hquiet : AllowanceQuiescent ca u checkpoint.state)
    (hdormant : NoAuthorizingActBy u history)
    (hcheckpoint : ∀ earlier record later,
      history.attributionLedger = earlier ++ record :: later →
      ∀ event, record.allowance = some event → event.owner.toAdr = u →
        attributionRootAt earlier.reverse event.key = .checkpoint →
        record.permanentOutflow u = 0) :
    bookedBalanceNat checkpoint.state ca u <=
      bookedBalanceNat future.state ca u := by
  have hzero :=
    history.permanentOutflow_eq_zero_of_dormant hnc hdormant hcheckpoint
  have hfloor := holderFlow_residual_floor (u := u) hstable history
  omega

/-! ## The reduction to counted entry reads

`CountedFrame.permanentOutflow_eq_zero_of_read_zero` retires the
`attributionRootAt` residual entirely: the surviving shape of
`CountedFrame.checkpointRooted_of_dormant` is an allowance-branch debit at one
of the holder's own keys, and such a debit spends nothing as soon as the word
the runtime actually read there is known to be zero.  What remains is a single
statement about the counted ledger — every counted read at one of the holder's
own keys is zero — with no reference to attribution roots at all. -/

/-- A dormant holder's public permanent outflow is zero, provided every
counted allowance visit at one of that holder's own keys read a zero word. -/
theorem AccountedHistory.permanentOutflow_eq_zero_of_zeroReads
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history)
    (hdormant : NoAuthorizingActBy u history)
    (hreads : ∀ record ∈ history.attributionLedger, ∀ event,
      record.allowance = some event → event.owner.toAdr = u →
        ∀ value, event.visit.read? = some value → value = 0) :
    (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut = 0 := by
  refine history.permanentOutflow_eq_zero_of_dormant hnc hdormant
    (fun earlier record later hsplit event hevent howner _ => ?_)
  have hmem : record ∈ history.attributionLedger := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  exact CountedFrame.permanentOutflow_eq_zero_of_read_zero
    (history.rootedLedger record hmem) (hdormant record hmem) hevent
    (hreads record hmem event hevent howner)

/-- The dormant-holder corollary reduced to counted entry reads: a dormant
holder's booked balance never decreases across an authentic collision-free
history whose counted allowance visits all read zero at that holder's own
keys.

This is the same statement as `dormant_holder_balance_monotone_of_checkpointRooted`
with a different residual.  The residual here is a *read* statement about the
counted ledger, which is what the read-sound transport
`AccountedHistory.allowanceTransportedSound_of_compiled` speaks about: it
replays each record's own ledger prefix onto the state the reads were taken
from.  `AccountedHistory.zeroReads_of_dormant` below discharges the residual
from that transport, so this form is a waypoint rather than an endpoint.
`AllowanceQuiescent` is the base case of that replay and is carried there
rather than here. -/
theorem dormant_holder_balance_monotone_of_zeroReads
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Weth10.Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history)
    (hdormant : NoAuthorizingActBy u history)
    (hreads : ∀ record ∈ history.attributionLedger, ∀ event,
      record.allowance = some event → event.owner.toAdr = u →
        ∀ value, event.visit.read? = some value → value = 0) :
    bookedBalanceNat checkpoint.state ca u <=
      bookedBalanceNat future.state ca u := by
  have hzero :=
    history.permanentOutflow_eq_zero_of_zeroReads hnc hdormant hreads
  have hfloor := holderFlow_residual_floor (u := u) hstable history
  omega

/-! ## Writing visits at a dormant holder's own key -/

/-- Inversion of the recorded finite spend: only the two delegated selectors
record one, the raw source word left the self-bypass arm, and both recorded
words are the runtime's own. -/
private theorem frameAllowanceEvent_spendFinite_inv
    {e : Sevm} {pre post : Devm} {event : AllowanceEvent}
    {before after : B256}
    (hevent : frameAllowanceEvent e pre post = some event)
    (hvisit : event.visit = .spendFinite before after) :
    e.data.length.toB256 ≠ 0 ∧
      (Sevm.selector e = transferFromSelector ∨
        Sevm.selector e = withdrawFromSelector) ∧
      Sevm.argWord e 0 ≠ e.caller.toB256 ∧
      before = (Devm.getStor pre e.currentTarget).get
        (callerAllowanceRuntimeKey e) ∧
      after = before - Sevm.argWord e 2 := by
  unfold frameAllowanceEvent at hevent
  split at hevent
  · exact absurd hevent (by simp)
  · rename_i hne0
    split at hevent
    · cases hevent; exact absurd hvisit (by simp)
    · split at hevent
      · cases hevent; exact absurd hvisit (by simp)
      · split at hevent
        · rename_i hsel
          split at hevent
          · exact absurd hevent (by simp)
          · rename_i hnotself
            cases hevent
            refine ⟨hne0, by simpa using hsel, hnotself, ?_⟩
            split at hvisit
            · exact absurd hvisit (by simp)
            · cases hvisit
              exact ⟨rfl, rfl⟩
        · split at hevent
          · cases hevent
            split at hvisit <;> exact absurd hvisit (by simp)
          · split at hevent
            · cases hevent; exact absurd hvisit (by simp)
            · exact absurd hevent (by simp)

/-- Inversion of the recorded flash settlement: only `flashLoan` records one,
its written word is the committed post-state word at the repayment cell, and
its recorded read is that word plus the loan amount. -/
private theorem frameAllowanceEvent_flashFinite_inv
    {e : Sevm} {pre post : Devm} {event : AllowanceEvent}
    {before after : B256}
    (hevent : frameAllowanceEvent e pre post = some event)
    (hvisit : event.visit = .flashFinite before after) :
    e.data.length.toB256 ≠ 0 ∧
      Sevm.selector e = flashLoanSelector ∧
      after = (Devm.getStor post e.currentTarget).get
        (flashAllowanceRuntimeKey e) ∧
      before = after + Sevm.argWord e 2 ∧
      after ≠ B256.max := by
  unfold frameAllowanceEvent at hevent
  split at hevent
  · exact absurd hevent (by simp)
  · rename_i hne0
    split at hevent
    · cases hevent; exact absurd hvisit (by simp)
    · split at hevent
      · cases hevent; exact absurd hvisit (by simp)
      · split at hevent
        · split at hevent
          · exact absurd hevent (by simp)
          · cases hevent
            split at hvisit <;> exact absurd hvisit (by simp)
        · split at hevent
          · rename_i hsel
            cases hevent
            refine ⟨hne0, hsel, ?_⟩
            split at hvisit
            · exact absurd hvisit (by simp)
            · rename_i hmax
              cases hvisit
              exact ⟨rfl, rfl, hmax⟩
          · split at hevent
            · cases hevent; exact absurd hvisit (by simp)
            · exact absurd hevent (by simp)

/-- A rooted exact `flashLoan` invocation exposes its post-callback allowance
fork and the shared burn continuation.  This is the allowance-only slice of
`flashLoan_rawSuccessEffect`: the settlement decomposition never consults the
world state's installed code, which the rooted-origin tower deliberately does
not carry — only the flash-counter restoration does, and that is discarded
here. -/
private theorem exists_flashAllowanceOutcome
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hroot : frame.IsRoot) (hexact : frame.exactInvocation dp ca)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector frame.sevm = flashLoanSelector) :
    ∃ settle burn : Devm,
      FlashAllowanceOutcome frame.sevm settle burn ∧
      Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm burn flashBurn
        frame.post := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := hroot.1
      subst pc
      have hwf : Mem.Wf pre.memory := by rw [hroot.2]; exact Mem.wf_empty
      have hreads : Mem.Reads pre.memory [] := by
        rw [hroot.2]; exact Mem.reads_empty
      obtain ⟨bodyPre, -, -, -, -, hmemory, -, -, hbody⟩ :=
        exec_enters_weth10Nonpayable_logs run hexact.2.2.2 hsel hnonempty
          (flashLoan_mem_weth10Funcs dp)
      have hwfBody : Mem.Wf bodyPre.memory := by rw [hmemory]; exact hwf
      have hfreshBody : Mem.Reads bodyPre.memory [] := by
        rw [hmemory]; exact hreads
      obtain ⟨recipient, sc, g, inputSize, base, -, -, -, -, -, -, -, -, -, -,
        hstack, hmem, -, -, htail⟩ := of_flashLoan_toCall_frame dp hbody
      obtain ⟨hwfSc, hreadsSc⟩ := hmem [] hwfBody hfreshBody
      have htail' : Func.Run ((weth10 dp).main :: weth10Aux) e sc
          flashLoanSuccessTail post := by
        simpa only [flashLoanSuccessTail, flashLoanFromCall] using htail
      obtain ⟨mid, settle, -, -, -, -, -, -, hwfSettle,
        ⟨settleImg, hreadsSettle⟩, hsettle⟩ :=
        of_rawFlashLoanSuccessTail dp hstack hwfSc hreadsSc rfl htail'
      obtain ⟨burn, hburn, hallowance, -, -⟩ :=
        of_flashSettle_allowance dp hwfSettle hreadsSettle hsettle
      exact ⟨settle, burn, hallowance, hburn⟩

/-- **The write step.**  A counted record of a dormant holder writes zero at
that holder's own allowance key, provided its own recorded read there was
zero.  Exactly four visits write, and each is excluded or forced:

* `approveStore` records the clean `CALLER` word as owner, so an approve at
  `u`'s key is `u`'s own act, excluded by dormancy;
* `permitStore` is a committed successful `permit` for owner `u`, excluded by
  dormancy directly;
* `spendFinite` writes `before - amount`, and a delegated invocation that read
  a zero word requested a zero amount;
* `flashFinite` writes `before - amount` too, guarded by the settlement's own
  `amount ≤ before`, so a zero read forces a zero amount and a zero write.

The remaining three visits record no write at all. -/
private theorem written_eq_zero_of_read_zero
    {dp : DeployParams} {ca u : Adr} {record : CountedFrame}
    {event : AllowanceEvent} {value : B256}
    (horigin : record.HasRootedOrigin dp ca)
    (hself : record.authorizes u = false)
    (hevent : record.allowance = some event)
    (howner : event.owner.toAdr = u)
    (hread : ∀ v, event.visit.read? = some v → v = 0)
    (hwritten : event.visit.written? = some value) :
    value = 0 := by
  obtain ⟨frame, rfl, hroot, hexact⟩ := horigin
  have hev : frameAllowanceEvent frame.sevm frame.pre frame.post =
    some event := hevent
  cases hvisit : event.visit with
  | viewRead v =>
      rw [hvisit] at hwritten
      exact absurd hwritten (by simp [AllowanceVisit.written?])
  | approveStore v =>
      exfalso
      have hclean : event.owner = event.caller.toB256 :=
        frameAllowanceEvent_approveStore_owner hev hvisit
      have hcaller : event.caller = u := by
        rw [← toAdr_toB256 event.caller, ← hclean, howner]
      have hrecordCaller : (CountedFrame.ofFrame dp ca frame).caller = u := by
        show frame.sevm.caller = u
        rw [← frameAllowanceEvent_caller hev]
        exact hcaller
      simp [CountedFrame.authorizes, hrecordCaller] at hself
  | permitStore v =>
      exfalso
      simp [CountedFrame.authorizes, hevent, hvisit, howner] at hself
  | spendMax =>
      rw [hvisit] at hwritten
      exact absurd hwritten (by simp [AllowanceVisit.written?])
  | spendFinite before after =>
      obtain ⟨hne0, hsel, hnotself, hbefore, hafter⟩ :=
        frameAllowanceEvent_spendFinite_inv hev hvisit
      rw [hvisit] at hwritten hread
      simp only [AllowanceVisit.written?, Option.some.injEq] at hwritten
      have hzero : before = 0 := hread before rfl
      have hnat := argWord_two_toNat_eq_zero_of_read_zero hroot hexact hne0
        hsel hnotself (by rw [← hbefore]; exact hzero)
      have hamt : Sevm.argWord frame.sevm 2 = 0 :=
        B256.toNat_inj _ _ (by rw [hnat]; rfl)
      rw [← hwritten, hafter, hzero, hamt]
      exact B256.sub_self 0
  | flashMax =>
      rw [hvisit] at hwritten
      exact absurd hwritten (by simp [AllowanceVisit.written?])
  | flashFinite before after =>
      obtain ⟨hne0, hsel, hafterEq, hbefore, hmax⟩ :=
        frameAllowanceEvent_flashFinite_inv hev hvisit
      rw [hvisit] at hwritten hread
      simp only [AllowanceVisit.written?, Option.some.injEq] at hwritten
      have hzero : before = 0 := hread before rfl
      obtain ⟨settle, burn, houtcome, hburn⟩ :=
        exists_flashAllowanceOutcome hroot hexact hne0 hsel
      have hbranch : flashAllowanceBranchFromPost frame.sevm frame.post =
          .finite (flashAllowanceRuntimeKey frame.sevm)
            (after + Sevm.argWord frame.sevm 2) after := by
        simp [flashAllowanceBranchFromPost, ← hafterEq, hmax]
      have haccept := flashSettlement_reconstruction houtcome hburn
      rw [hbranch] at haccept
      obtain ⟨-, -, -, hle, hsub⟩ := haccept.2
      rw [← hbefore, hzero] at hle hsub
      have hnat := B256.toNat_le_toNat hle
      have hzeroNat : B256.toNat 0 = 0 := rfl
      rw [hzeroNat] at hnat
      have hamt : Sevm.argWord frame.sevm 2 = 0 :=
        B256.toNat_inj _ _ (by rw [Nat.le_zero.mp hnat]; rfl)
      rw [hamt, B256.sub_self] at hsub
      rw [← hwritten, hsub]

/-! ## The ledger invariant

The replay of every ledger prefix leaves a dormant holder's own touched
allowance keys at zero.  The base case is `AllowanceQuiescent`; each step
consumes the record's own recorded read, which the read-sound transport
identifies with the replay of the prefix strictly before it. -/

/-- Extending a replayed prefix by one record. -/
private theorem applyAllowanceLedger_append_singleton
    (pre : Stor) (left : List CountedFrame) (record : CountedFrame)
    (key : B256) :
    applyAllowanceLedger pre (left ++ [record]) key =
      match record.allowance with
      | some event =>
          if event.key = key then
            match event.visit.written? with
            | some value => value
            | none => applyAllowanceLedger pre left key
          else applyAllowanceLedger pre left key
      | none => applyAllowanceLedger pre left key := by
  unfold applyAllowanceLedger
  rw [List.reverse_append]
  cases hallow : record.allowance with
  | none => simp [lastAllowanceWriteAt, hallow]
  | some event =>
      by_cases hkey : event.key = key
      · cases hwrite : event.visit.written? with
        | some value => simp [lastAllowanceWriteAt, hallow, hkey, hwrite]
        | none => simp [lastAllowanceWriteAt, hallow, hkey, hwrite]
      · simp [lastAllowanceWriteAt, hallow, hkey]

/-- Trace-local collision freedom read as injectivity on touched pairs: two
touched pairs hashing to the same tagged key are the same pair. -/
private theorem eq_of_projectedAllowanceKey_eq :
    ∀ pairs : List (B256 × B256), pairs.Pairwise NoCollisionRel →
      ∀ p ∈ pairs, ∀ q ∈ pairs,
        projectedAllowanceKey p.1 p.2 = projectedAllowanceKey q.1 q.2 →
        p = q := by
  intro pairs
  induction pairs with
  | nil => intro _ p hp; cases hp
  | cons head tail ih =>
      intro hpairs p hp q hq hkey
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpairs
      rcases List.mem_cons.mp hp with rfl | hp'
      · rcases List.mem_cons.mp hq with rfl | hq'
        · rfl
        · by_contra hne
          exact hhead q hq' hne hkey
      · rcases List.mem_cons.mp hq with rfl | hq'
        · by_contra hne
          exact hhead p hp' (fun h => hne h.symm) hkey.symm
        · exact ih htail p hp' q hq' hkey

/-- Chronological form of the dormancy invariant.  Carried along the ledger
with the same bookkeeping the attribution equality uses, the invariant "the
replay of the consumed prefix is zero at every one of the holder's touched
keys" both discharges each record's own recorded read and survives that
record's own write. -/
private theorem zeroReads_go
    {dp : DeployParams} {ca u : Adr} (pre : Stor) (whole : List CountedFrame)
    (hrooted : ∀ record ∈ whole, record.HasRootedOrigin dp ca)
    (hdormant : ∀ record ∈ whole, record.authorizes u = false)
    (hpairs : (touchedPairs whole).Pairwise NoCollisionRel)
    (hsound : AllowanceEntryReadSound pre whole) :
    ∀ rest earlier : List CountedFrame, earlier ++ rest = whole →
      (∀ owner spender : B256, owner.toAdr = u →
        (owner, spender) ∈ touchedPairs whole →
        applyAllowanceLedger pre earlier
          (projectedAllowanceKey owner spender) = 0) →
      ∀ record ∈ rest, ∀ event, record.allowance = some event →
        event.owner.toAdr = u →
          ∀ value, event.visit.read? = some value → value = 0 := by
  intro rest
  induction rest with
  | nil => intro _ _ _ record hrecord; cases hrecord
  | cons head tail ih =>
      intro earlier hchain hinv record hrecord event hevent howner value hread
      have hsplit : whole = earlier ++ head :: tail := hchain.symm
      have hheadWhole : head ∈ whole := by
        rw [hsplit]
        exact List.mem_append_right _ List.mem_cons_self
      have hheadRead : ∀ ev, head.allowance = some ev → ev.owner.toAdr = u →
          ∀ v, ev.visit.read? = some v → v = 0 := by
        intro ev hev howner' v hv
        rw [hsound earlier head tail hsplit ev hev v hv]
        exact hinv ev.owner ev.spender howner'
          (mem_touchedPairs.mpr ⟨head, hheadWhole, ev, hev, rfl⟩)
      rcases List.mem_cons.mp hrecord with rfl | hrest
      · exact hheadRead event hevent howner value hread
      · refine ih (earlier ++ [head]) (by simpa using hchain) ?_ record hrest
          event hevent howner value hread
        intro owner spender howner' hmem
        rw [applyAllowanceLedger_append_singleton]
        cases hallow : head.allowance with
        | none => exact hinv owner spender howner' hmem
        | some ev =>
            dsimp only
            by_cases hkey : ev.key = projectedAllowanceKey owner spender
            · rw [if_pos hkey]
              have hpair : (ev.owner, ev.spender) = (owner, spender) :=
                eq_of_projectedAllowanceKey_eq _ hpairs _
                  (mem_touchedPairs.mpr ⟨head, hheadWhole, ev, hallow, rfl⟩) _
                  hmem hkey
              have hownerEq : ev.owner = owner := congrArg Prod.fst hpair
              have hevOwner : ev.owner.toAdr = u := by
                rw [hownerEq]
                exact howner'
              cases hwrite : ev.visit.written? with
              | none => exact hinv owner spender howner' hmem
              | some w =>
                  exact written_eq_zero_of_read_zero
                    (hrooted head hheadWhole) (hdormant head hheadWhole)
                    hallow hevOwner (hheadRead ev hallow hevOwner) hwrite
            · rw [if_neg hkey]
              exact hinv owner spender howner' hmem

/-! ## The residual, discharged

The read-sound transport turns every counted record's recorded allowance read
into the replay of the ledger prefix strictly before it, which the invariant
above pins at zero on a dormant holder's own touched keys.  That is exactly
the residual hypothesis of `dormant_holder_balance_monotone_of_zeroReads`. -/

/-- Every allowance visit at a dormant holder's own key read a zero word.
`AllowanceQuiescent` is the base of the replay and trace-local collision
freedom is what identifies a visited key with the holder's own raw pair. -/
theorem AccountedHistory.zeroReads_of_dormant
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Weth10.Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history)
    (hquiet : AllowanceQuiescent ca u checkpoint.state)
    (hdormant : NoAuthorizingActBy u history) :
    ∀ record ∈ history.attributionLedger, ∀ event,
      record.allowance = some event → event.owner.toAdr = u →
        ∀ value, event.visit.read? = some value → value = 0 := by
  have hpairs :
      (touchedPairs history.attributionLedger).Pairwise NoCollisionRel := by
    rw [← touchedAllowancePairs_eq_touchedPairs history]
    exact hnc
  refine zeroReads_go (checkpoint.state.getStor ca)
    history.attributionLedger history.rootedLedger hdormant hpairs
    (history.allowanceTransportedSound_of_compiled hstable).2
    history.attributionLedger [] (by simp) ?_
  intro owner spender howner _
  rw [applyAllowanceLedger_nil]
  exact hquiet owner spender howner

/-- **The dormant-holder corollary.**  A holder who performed no authorizing
act and held no allowance at the checkpoint cannot have lost a wei across an
authentic collision-free history. -/
theorem dormant_holder_balance_monotone
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Weth10.Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history)
    (hquiet : AllowanceQuiescent ca u checkpoint.state)
    (hdormant : NoAuthorizingActBy u history) :
    bookedBalanceNat checkpoint.state ca u <=
      bookedBalanceNat future.state ca u :=
  dormant_holder_balance_monotone_of_zeroReads hstable history hnc hdormant
    (history.zeroReads_of_dormant hstable hnc hquiet hdormant)

/-! ## The dormant fixture, consumed

`Blanc.Weth10Attribution`'s multi-step dormant scenario is a concrete counted
ledger: third-party mints and an incoming transfer to `u`, an unrelated
holder's approve and the spend that allowance authorizes, and a third party's
flash settlement.  Its dormancy lemma closes the corollary's ledger-side
premise, so the corollary applies to that ledger by plain application, with no
tactic in between.  The contrasting ledger — the same scenario with `u`'s own
approve inserted — refutes the very same premise. -/

/-- **The dormant fixture, run through the corollary.**  A history whose
counted ledger is the dormant scenario satisfies `NoAuthorizingActBy`, and
`dormant_holder_balance_monotone` then delivers the bare balance inequality
for `u`.

Read the scope exactly.  The two hypotheses that remain, `hstable` and
`hquiet`, are facts about the checkpoint *state*, and no ledger fixture can
supply either.  `history` is universally quantified here rather than
constructed: no synthetic ledger yields a real `AccountedHistory`, since that
record is inhabited only by a genuine execution.  What this statement does
show is that the fixture's ledger shape discharges the corollary's
ledger-side premise, and that the corollary then delivers monotonicity of `u`'s
booked balance from the checkpoint to the future. -/
theorem dormantFixture_balance_monotone
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} {u other w fl : Adr} {spW caWord : B256}
    (hstable : Weth10.Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history)
    (hquiet : AllowanceQuiescent ca u checkpoint.state)
    (hledger : history.attributionLedger = dormantLedger other u w fl spW caWord)
    (hother : other ≠ u) (hw : w ≠ u) (hsp : spW.toAdr ≠ u) (hfl : fl ≠ u) :
    bookedBalanceNat checkpoint.state ca u ≤
      bookedBalanceNat future.state ca u :=
  dormant_holder_balance_monotone hstable history hnc hquiet
    (dormantLedger_noAuthorizingActBy other u w fl spW caWord history hledger
      hother hw hsp hfl)

/-- The contrast, at the corollary's own altitude.  Insert `u`'s own approve
into the same scenario and `dormant_holder_balance_monotone`'s dormancy
premise is *refuted*, not merely unproved, so the corollary is inapplicable to
that history.  Nothing is claimed about the balances there: a refuted premise
leaves the conclusion open, and it would be dishonest to record it either
way. -/
theorem nonDormantFixture_no_dormancy_premise
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} {u other w fl : Adr}
    {spW caWord owU spU : B256}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hledger : history.attributionLedger =
      nonDormantApproveFrameByU u owU spU :: dormantLedger other u w fl spW caWord) :
    ¬ NoAuthorizingActBy u history :=
  nonDormantLedger_not_noAuthorizingActBy other u w fl spW caWord owU spU history hledger

end Weth10

end Blanc
