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
value the runtime actually read at the debited key, and the landed transport
`AccountedHistory.allowanceTransported_of_compiled` relates only the
checkpoint and the future endpoints, never a counted record's own entry
state.  Until an entry-state form of that transport exists, the residual
travels as an explicit hypothesis of
`dormant_holder_balance_monotone_of_checkpointRooted`; nothing below assumes
it away.
-/

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
`AllowanceQuiescent` forces to zero — and is unused until the entry-state form
of `AccountedHistory.allowanceTransported_of_compiled` lands. -/
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

end Weth10

end Blanc
