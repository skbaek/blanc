-- DripRealizedExec.lean : recursive execution replay for DRIP's realized
-- accounting (design unit U5: exec-core recursion and the exit handoff).
--
-- Every successful frame of an arbitrary retained execution is replayed as a
-- `RealizedChain`.  A frame executing DRIP itself contributes one head step
-- whose kind is *computed* from the frame's own fields (`opTag`), followed by
-- whatever its accepted exit callback recursively contributes; every foreign
-- frame contributes positive external credits or nothing.  The settlement
-- seams are the contract-neutral ones of `Blanc/ExecutionAccountingReplay.lean`
-- consumed at DRIP's own carrier.

import Blanc.DripRealizedHistory
import Blanc.ExecutionAccountingReplay

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Drip

/-! ## The frame-entry side spec

`dripSpec` is storage-only: its `Side` is `True` and its `Inv` ignores value and
balance.  The replay needs two balance facts at every frame — the world's
total is below the word bound, and a DRIP frame's in-flight value is already
inside the target balance — and both are ladder-shaped, so they ride the
generic frame ladder as a second `ContractSpec` instead of being re-threaded
by hand. -/

/-- The balance-only companion of `dripSpec`: the in-flight value is already
credited, and the world total cannot wrap. -/
def dripEntrySpec : ContractSpec where
  prog := runtime
  Inv := fun _ value balance => value.toNat ≤ balance.toNat
  Side := SumNof
  inv_forget := by
    intro _ _ _ _
    rw [B256.toNat_zero]
    exact Nat.zero_le _
  inv_mono := fun h hle => Nat.le_trans h hle
  inv_recv := by
    intro _ _ _ _ _ h
    omega
  side_le := by
    intro f g h hle
    unfold SumNof at h ⊢
    omega
  side_transfer := by
    intro st st' caller callee wad h_sub h_side
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := callee) h_sub h_nof with
      ⟨-, -, h_sum, -, -, -⟩
    show sum _ < 2 ^ 256
    rw [h_sum]
    exact h_nof
  side_addBal := by
    intro w a val h_bound _
    show sum _ < 2 ^ 256
    rw [sum_addBal_eq w a val h_bound]
    omega
  inv_transfer := by
    intro st st' caller callee ca wad value h_sub h_ne h_side h_inv
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := callee) h_sub h_nof with
      ⟨-, -, -, h_t_le, -, -⟩
    have h_mid : st'.bal ca = st.bal ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      rw [h_st']
      show ((st.setBal caller _).get ca).bal = (st.get ca).bal
      rw [State.setBal_get_ne h_ne]
    have h_ge :
        (st.bal ca).toNat ≤ ((st'.addBal callee wad).bal ca).toNat := by
      by_cases h_eq : callee = ca
      · have h_add : (st'.addBal callee wad).bal ca = st.bal ca + wad := by
          rw [h_eq]
          show ((st'.setBal ca (st'.bal ca + wad)).get ca).bal = _
          rw [State.setBal_get_self]
          show st'.bal ca + wad = _
          rw [h_mid]
        rw [h_add]
        have h_le_wad : wad.toNat ≤ (st.bal caller).toNat :=
          B256.toNat_le_toNat h_t_le
        have h_two :
            (st.bal ca).toNat + (st.bal caller).toNat ≤ sum st.bal :=
          add_le_sum_of_ne st.bal (fun hc => h_ne hc.symm)
        have h_nof' : B256.Nof (st.bal ca) wad := by
          unfold B256.Nof
          omega
        rw [B256.toNat_add_eq_of_nof _ _ h_nof']
        omega
      · have h_other : (st'.addBal callee wad).bal ca = st.bal ca := by
          show ((st'.setBal callee _).get ca).bal = _
          rw [State.setBal_get_ne h_eq]
          exact h_mid
        rw [h_other]
    exact Nat.le_trans h_inv h_ge
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub h_ne h_side _
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    have h_bal : ((st'.addBal ca wad).bal ca).toNat =
        (st.bal ca).toNat + wad.toNat :=
      of_transfer_bal_target h_sub h_ne h_nof
    show wad.toNat ≤ _
    omega
  inv_addBal := by
    intro w ca a val value h_bound _ h_inv
    have h_nof_a : B256.Nof (w.bal a) val := by
      unfold B256.Nof
      have := @le_sum w.bal a
      omega
    have h_ge : (w.bal ca).toNat ≤ ((w.addBal a val).bal ca).toNat := by
      by_cases h_eq : a = ca
      · subst h_eq
        show (w.bal a).toNat ≤
          ((w.setBal a (w.bal a + val)).get a).bal.toNat
        rw [State.setBal_get_self]
        change (w.bal a).toNat ≤ (w.bal a + val).toNat
        rw [B256.toNat_add_eq_of_nof _ _ h_nof_a]
        omega
      · show (w.bal ca).toNat ≤ ((w.setBal a _).get ca).bal.toNat
        rw [State.setBal_get_ne h_eq]
        exact Nat.le_refl _
    exact Nat.le_trans h_inv h_ge

/-- Every successful execution preserves the side spec: the world total never
rises, and the exit form of the invariant is vacuous. -/
theorem dripEntrySpec_preservesNoMem (ca : Adr) :
    dripEntrySpec.PreservesNoMem ca := by
  intro sevm pre post run _ precondition
  have effect := Exec.balance_effect run
  refine ⟨?_, ?_⟩
  · have side : sum pre.state.bal < 2 ^ 256 := precondition.side
    have noninc : sum post.state.bal ≤ sum pre.state.bal := effect
    show sum post.state.bal < 2 ^ 256
    omega
  · show (0 : B256).toNat ≤ _
    rw [B256.toNat_zero]
    exact Nat.zero_le _

/-! ## Entry boundary and the DRIP carrier -/

/-- Entry snapshot of a frame.  A frame executing `ca` is viewed immediately
*before* its message value was credited; every foreign frame at the ordinary
projection.  The balance offset is the shared `balanceEntry`, so the carrier's
entry law is the contract-neutral one. -/
noncomputable def execEntrySnapshot (coalition : Finset Adr) (ca : Adr)
    (sevm : Sevm) (state : State) : Snapshot :=
  { snapshot coalition ca state with
    balance := ExecutionAccountingReplay.balanceEntry ca sevm state }

theorem execEntrySnapshot_of_target_ne {coalition : Finset Adr} {ca : Adr}
    {sevm : Sevm} {state : State} (target_ne : sevm.currentTarget ≠ ca) :
    execEntrySnapshot coalition ca sevm state = snapshot coalition ca state := by
  unfold execEntrySnapshot ExecutionAccountingReplay.balanceEntry
  rw [if_neg target_ne]
  rfl

/-- The world a DRIP frame's value credit was applied to, reconstructed by
subtraction.  It is never claimed to be a retained world state; it exists so
the state-indexed write lemmas can be reused at the pre-credit boundary. -/
def precreditState (ca : Adr) (value : B256) (state : State) : State :=
  state.setBal ca (state.bal ca - value)

theorem precreditState_getStor (ca : Adr) (value : B256) (state : State) :
    (precreditState ca value state).getStor ca = state.getStor ca := by
  show ((state.setBal ca _).get ca).stor = (state.get ca).stor
  rw [State.setBal_get_stor]

theorem precreditState_bal {ca : Adr} {value : B256} {state : State}
    (credited : value.toNat ≤ (state.bal ca).toNat) :
    ((precreditState ca value state).bal ca).toNat =
      (state.bal ca).toNat - value.toNat := by
  show ((state.setBal ca (state.bal ca - value)).get ca).bal.toNat = _
  rw [State.setBal_get_self]
  exact B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat credited)

theorem execEntrySnapshot_of_target {coalition : Finset Adr} {ca : Adr}
    {sevm : Sevm} {state : State} (target : sevm.currentTarget = ca)
    (credited : sevm.value.toNat ≤ (state.bal ca).toNat) :
    execEntrySnapshot coalition ca sevm state =
      snapshot coalition ca (precreditState ca sevm.value state) := by
  unfold execEntrySnapshot ExecutionAccountingReplay.balanceEntry snapshot
    coalitionUnits
  rw [if_pos target, precreditState_getStor, precreditState_bal credited]

/-- One positive outside credit as a realized step. -/
theorem externalCredit_chain {coalition : Finset Adr} {ca : Adr}
    {pre post : State} {amount : Nat}
    (storage_eq : post.getStor ca = pre.getStor ca)
    (balance_eq : (post.bal ca).toNat = (pre.bal ca).toNat + amount)
    (positive : 0 < amount) :
    ∃ op : RealizedStep, op.kind = .externalCredit amount ∧
      op.pre = snapshot coalition ca pre ∧
      op.post = snapshot coalition ca post := by
  refine ⟨⟨snapshot coalition ca pre, .externalCredit amount,
    snapshot coalition ca post, ?_⟩, rfl, rfl, rfl⟩
  have postEq : snapshot coalition ca post =
      ⟨chiN (pre.getStor ca), rhoN (pre.getStor ca),
        coalitionUnits coalition ca pre, totalN (pre.getStor ca),
        (pre.bal ca).toNat + amount⟩ := by
    unfold snapshot coalitionUnits
    rw [storage_eq, balance_eq]
  rw [postEq]
  exact .externalCredit _ _ _ _ _ _ positive

/-- DRIP's realized accounting presented as a `ReplayCarrier`: the first
ledger-shaped consumer of the contract-neutral settlement seams outside the
family that motivated them. -/
noncomputable def carrier (coalition : Finset Adr) (ca : Adr) :
    ExecutionAccountingReplay.ReplayCarrier ca where
  Snap := Snapshot
  Step := RealizedStep
  Tag := Unit
  Replay := RealizedChain
  ofState := snapshot coalition ca
  frameEntry := execEntrySnapshot coalition ca
  nil := Chain.nil
  silent := by
    intro _ _ storage_eq balance_eq
    exact snapshot_eq_of_getStor_bal storage_eq (B256.toNat_inj _ _ balance_eq)
  credit := by
    intro _ pre post amount storage_eq balance_eq positive
    rcases externalCredit_chain (coalition := coalition) storage_eq balance_eq
        positive with ⟨op, _, preEq, postEq⟩
    refine ⟨[op], Chain.cons preEq ?_⟩
    rw [postEq]
    exact Chain.nil _
  entry_eq_ofState := by
    intro msg entry caller_ne value_zero transfer sum_nof
    have balance := ExecutionAccountingReplay.balanceEntry_eq_ofState
      caller_ne value_zero transfer sum_nof
    have storage : entry.state.getStor ca = msg.benv.state.getStor ca :=
      congrFun (benvAfterTransfer_getStor_eq transfer) ca
    unfold execEntrySnapshot
    rw [balance]
    unfold snapshot coalitionUnits
    rw [storage]

/-- Chains compose. -/
theorem Chain.append {scale : Nat} {fresh : Nat → Nat → Nat}
    {s m t : Snapshot} {left right : List (Step scale fresh)}
    (first : Chain scale fresh s left m) (second : Chain scale fresh m right t) :
    Chain scale fresh s (left ++ right) t := by
  induction first with
  | nil _ => exact second
  | cons entry _ ih => exact Chain.cons entry (ih second)

/-! ## Exit write lemmas -/

/-- The actual exit's four writes change only the caller's holder row.  The
row subtraction is exact because the runtime's ownership guard bounds it. -/
theorem coalitionUnits_exit_write (coalition : Finset Adr) (ca caller : Adr)
    {before after : State} {fresh now units : B256}
    (storage : after.getStor ca =
      ((((before.getStor ca).set chiSlot fresh).set rhoSlot now).set
        (pieSlot caller) ((before.getStor ca).get (pieSlot caller) - units)).set
          totalUnitsSlot ((before.getStor ca).get totalUnitsSlot - units))
    (rowLe : units ≤ (before.getStor ca).get (pieSlot caller)) :
    coalitionUnits coalition ca after +
        (if caller ∈ coalition then units.toNat else 0) =
      coalitionUnits coalition ca before := by
  classical
  have row : ∀ holder, pieN (after.getStor ca) holder +
        (if holder = caller then units.toNat else 0) =
      pieN (before.getStor ca) holder := by
    intro holder
    by_cases same : holder = caller
    · subst holder
      unfold pieN
      rw [storage, Stor.get_set_ne _ (pieSlot_ne_totalUnitsSlot caller).symm _,
        Stor.get_set_self, B256.toNat_sub_eq_of_le _ _ rowLe, if_pos rfl]
      have := B256.toNat_le_toNat rowLe
      omega
    · simp only [if_neg same, Nat.add_zero]
      unfold pieN
      rw [storage, Stor.get_set_ne _ (pieSlot_ne_totalUnitsSlot holder).symm _,
        Stor.get_set_ne _ (fun eq => same (pieSlot_injective eq).symm) _,
        Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder).symm _,
        Stor.get_set_ne _ (pieSlot_ne_chiSlot holder).symm _]
  unfold coalitionUnits
  simp_rw [← row]
  rw [Finset.sum_map_toList, Finset.sum_map_toList, Finset.sum_add_distrib,
    Finset.sum_ite_eq']

/-- Project the exact four-store exit image and the payout debit observed at
the child entry into the finite-coalition accounting relation.  `before` is the
frame's entry world and `after` the accepted callback's entry world. -/
theorem exit_write_realized_effect (coalition : Finset Adr) (ca caller : Adr)
    {before after : State} {fresh now units payout : B256} {elapsed : Nat}
    (storage : after.getStor ca =
      ((((before.getStor ca).set chiSlot fresh).set rhoSlot now).set
        (pieSlot caller) ((before.getStor ca).get (pieSlot caller) - units)).set
          totalUnitsSlot ((before.getStor ca).get totalUnitsSlot - units))
    (freshEq : fresh.toNat = freshNat (chiN (before.getStor ca)) elapsed)
    (timeEq : now.toNat = rhoN (before.getStor ca) + elapsed)
    (quote : payout.toNat = exitPayoutOf scale.toNat units.toNat
      (freshNat (chiN (before.getStor ca)) elapsed))
    (rowLe : units ≤ (before.getStor ca).get (pieSlot caller))
    (totalLe : units ≤ (before.getStor ca).get totalUnitsSlot)
    (funded : payout ≤ before.bal ca)
    (balance : after.bal ca = before.bal ca - payout) :
    Effect scale.toNat freshNat (snapshot coalition ca before)
      (.exit (decide (caller ∈ coalition)) caller units.toNat payout.toNat elapsed)
      (snapshot coalition ca after) := by
  classical
  have chi : chiN (after.getStor ca) =
      freshNat (chiN (before.getStor ca)) elapsed := by
    unfold chiN
    rw [storage, Stor.get_set_ne _ scalarSlots_distinct.2.1.symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot caller) _,
      Stor.get_set_ne _ scalarSlots_distinct.1.symm _, Stor.get_set_self]
    exact freshEq
  have rho : rhoN (after.getStor ca) =
      rhoN (before.getStor ca) + elapsed := by
    unfold rhoN
    rw [storage, Stor.get_set_ne _ scalarSlots_distinct.2.2.symm _,
      Stor.get_set_ne _ (pieSlot_ne_rhoSlot caller) _, Stor.get_set_self]
    exact timeEq
  have total : totalN (after.getStor ca) =
      totalN (before.getStor ca) - units.toNat := by
    unfold totalN
    rw [storage, Stor.get_set_self, B256.toNat_sub_eq_of_le _ _ totalLe]
  have bal : (after.bal ca).toNat = (before.bal ca).toNat - payout.toNat := by
    rw [balance, B256.toNat_sub_eq_of_le _ _ funded]
  have counted := coalitionUnits_exit_write coalition ca caller storage rowLe
  have totalLeNat : units.toNat ≤ totalN (before.getStor ca) :=
    B256.toNat_le_toNat totalLe
  have fundedNat : payout.toNat ≤ (before.bal ca).toNat :=
    B256.toNat_le_toNat funded
  change Effect scale.toNat freshNat
    ⟨chiN (before.getStor ca), rhoN (before.getStor ca),
      coalitionUnits coalition ca before, totalN (before.getStor ca),
      (before.bal ca).toNat⟩
    (.exit (decide (caller ∈ coalition)) caller units.toNat payout.toNat elapsed)
    ⟨chiN (after.getStor ca), rhoN (after.getStor ca),
      coalitionUnits coalition ca after, totalN (after.getStor ca),
      (after.bal ca).toNat⟩
  rw [chi, rho, total, bal]
  by_cases member : caller ∈ coalition
  · simp only [member, if_true] at counted
    have owned : units.toNat ≤ coalitionUnits coalition ca before := by omega
    have afterEq : coalitionUnits coalition ca after =
        coalitionUnits coalition ca before - units.toNat := by omega
    rw [afterEq]
    simp only [member, decide_true]
    exact .exitCounted _ _ _ _ _ _ _ _ _ owned totalLeNat fundedNat quote
  · simp only [member, if_false, Nat.add_zero] at counted
    rw [counted]
    simp only [member, decide_false]
    exact .exitOutside _ _ _ _ _ _ _ _ _ totalLeNat fundedNat quote

/-! ## The exit handoff

One successful deployed `exit` is split at the accepted callback's entry: the
head step runs from the frame's entry world to the child's post-transfer
entry world and is the whole DRIP-side effect (the four ledger writes and the
payout debit); everything after it is the callback's own retained execution,
whose end state is the frame's end state.  The child is handed over with the
exact data the deeper-frame induction hypothesis consumes. -/

/-- The retained accepted callback of one successful `exit` frame. -/
structure ExitHandoff (coalition : Finset Adr) (sevm : Sevm) (pre post : Devm) where
  childMsg : Msg
  entry : Benv
  child : Devm
  xl : Xlot
  filled : Xlot.Filled xl
  process : ProcessMessage childMsg xl (.ok child)
  childClean : child.error.isSome = false
  entryTransfer : childMsg.benvAfterTransfer = .ok entry
  targetNe : childMsg.currentTarget ≠ sevm.currentTarget
  depth : (initSevm (childMsg.withBenv entry)).depth < sevm.depth
  childPre : dripEntrySpec.Pre sevm.currentTarget
    (initSevm (childMsg.withBenv entry)) (initDevm (childMsg.withBenv entry))
  effect : Effect scale.toNat freshNat
    (snapshot coalition sevm.currentTarget pre.state)
    (.exit (decide (sevm.caller ∈ coalition)) sevm.caller
      (Sevm.dataWord sevm (32 * 0 + 4)).toNat
      (exitPayoutOf scale.toNat (Sevm.dataWord sevm (32 * 0 + 4)).toNat
        (freshNat (chiN (Devm.getStor pre sevm.currentTarget))
          (sevm.benvStat.time -
            Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat))
      (sevm.benvStat.time -
        Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat)
    (snapshot coalition sevm.currentTarget entry.state)
  postSnapshot : snapshot coalition sevm.currentTarget post.state =
    snapshot coalition sevm.currentTarget child.state

/-- Component form of `exit_exec_handoff`: the handoff built from any call
boundary `callPre` carrying the settled ledger, the entry code and balance, and
the destructured accepted payout. The returned handoff keeps the supplied
slot, child and message, so an actual `CALL` node can be matched against it. -/
theorem exit_handoff_of_components (coalition : Finset Adr) {sevm : Sevm}
    {pre post callPre callPost parent child : Devm} {xl : Xlot}
    {gasWord : B256} {delegated : Bool} {nextAddress : Adr}
    {childCode : ByteArray} {avail : Nat}
    (precondition : dripEntrySpec.Pre sevm.currentTarget sevm pre)
    (caller_ne : sevm.caller ≠ sevm.currentTarget) :
    let units := Sevm.dataWord sevm (32 * 0 + 4)
    let elapsed :=
      sevm.benvStat.time - Devm.getStorVal pre sevm.currentTarget rhoSlot
    let freshChi := (B256.rpow scale half rate elapsed.toNat *
      Devm.getStorVal pre sevm.currentTarget chiSlot) / scale
    let payout := (freshChi * units) / scale
    ¬ maxUnits < units →
    ¬ Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 < units →
    ¬ Devm.getStorVal pre sevm.currentTarget totalUnitsSlot < units →
    ¬ sevm.benvStat.time < Devm.getStorVal pre sevm.currentTarget rhoSlot →
    B256.RPowGuards scale half rate elapsed.toNat →
    B256.Nofm (Devm.getStorVal pre sevm.currentTarget chiSlot)
      (B256.rpow scale half rate elapsed.toNat) →
    ¬ maxChi < freshChi →
    Devm.getStor callPre sevm.currentTarget =
      ((((Devm.getStor pre sevm.currentTarget).set chiSlot freshChi).set
            rhoSlot sevm.benvStat.time).set sevm.caller.toB256
            (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 -
              units)).set totalUnitsSlot
        (Devm.getStorVal pre sevm.currentTarget totalUnitsSlot - units) →
    Devm.getCode callPre = Devm.getCode pre →
    Devm.getBal callPre = Devm.getBal pre →
    Devm.getStor post = Devm.getStor callPost →
    Devm.getBal post = Devm.getBal callPost →
    0 < sevm.depth →
    parent.state = callPre.state →
    Xlot.Filled xl →
    ProcessMessage
      (callMsg sevm parent
        (min gasWord.toNat (except64th avail) +
          (if payout.toNat = 0 then 0 else gCallStipend))
        payout sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
        ((callPre.memory.read 0 0).1) childCode delegated)
      xl (.ok child) →
    child.error.isSome = false →
    callPost.state = child.state →
    ∃ handoff : ExitHandoff coalition sevm pre post,
      handoff.xl = xl ∧ handoff.child = child ∧
      handoff.childMsg = callMsg sevm parent
        (min gasWord.toNat (except64th avail) +
          (if payout.toNat = 0 then 0 else gCallStipend))
        payout sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
        ((callPre.memory.read 0 0).1) childCode delegated := by
  intro units elapsedWord freshChiWord payoutWord hargCap hown hfund hclock
    hguards hnofm hcapChi storage codePre balPre postStor postBal hdepth
    parentState filled process clean callPostState
  set elapsed := (sevm.benvStat.time -
    Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat with elapsedDef
  set freshChi := (B256.rpow scale half rate elapsed *
    Devm.getStorVal pre sevm.currentTarget chiSlot) / scale with freshDef
  set units := Sevm.dataWord sevm (32 * 0 + 4) with unitsDef
  set payout := freshChi * units / scale with payoutDef
  set childMsg := callMsg sevm parent
    (min gasWord.toNat (except64th avail) +
      (if payout.toNat = 0 then 0 else gCallStipend))
    payout sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
    ((callPre.memory.read 0 0).1) childCode delegated with childMsgDef
  have recipient_ne : sevm.caller.toB256.toAdr ≠ sevm.currentTarget := by
    rw [toAdr_toB256]
    exact caller_ne
  rcases RunFrame.decompose process with
    ⟨error, _, _, failed⟩ | ⟨entry, result, transfer, _, _⟩
  · simp [Frame.ofCall, Frame.settleMsg, processMessage.settle] at failed
  have transfer' : childMsg.benvAfterTransfer = .ok entry := transfer
  rcases of_benvAfterTransfer (msg := childMsg) rfl transfer' with
    ⟨debit, sub, entryEq⟩
  have sub' : callPre.state.subBal sevm.currentTarget payout = some debit := by
    change parent.state.subBal _ _ = some debit at sub
    rwa [parentState] at sub
  have entryState : entry.state =
      debit.addBal sevm.caller.toB256.toAdr payout := by
    rw [entryEq]
    rfl
  have fields := of_state_transfer_fields
    (callee := sevm.caller.toB256.toAdr) sub'
  have entryStor : entry.state.getStor sevm.currentTarget =
      callPre.state.getStor sevm.currentTarget := by
    rw [entryState]
    exact fields.1 sevm.currentTarget
  have entryBalance : entry.state.bal sevm.currentTarget =
      pre.state.bal sevm.currentTarget - payout := by
    rw [entryState, fields.2.2.2.2 recipient_ne]
    exact congrArg (· - payout) (congrFun balPre sevm.currentTarget)
  have funded : payout ≤ pre.state.bal sevm.currentTarget := by
    have := fields.2.2.1
    rwa [show callPre.state.bal sevm.currentTarget =
      pre.state.bal sevm.currentTarget from congrFun balPre sevm.currentTarget]
      at this
  have htimele := le_of_not_gt hclock
  have timeEq : sevm.benvStat.time.toNat =
      rhoN (pre.state.getStor sevm.currentTarget) + elapsed := by
    have htimeleNat := B256.toNat_le_toNat htimele
    have := B256.toNat_sub_eq_of_le _ _ htimele
    unfold rhoN
    change sevm.benvStat.time.toNat =
      (Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat + elapsed
    omega
  have freshEq : freshChi.toNat =
      freshNat (chiN (pre.state.getStor sevm.currentTarget)) elapsed :=
    freshChi_toNat _ _ hguards hnofm
  have hscale : scale ≠ 0 := by decide +kernel
  have quote : payout.toNat = exitPayoutOf scale.toNat units.toNat
      (freshNat (chiN (pre.state.getStor sevm.currentTarget)) elapsed) := by
    have hnofPayout : B256.Nofm freshChi units := by
      unfold B256.Nofm
      exact lt_of_le_of_lt
        (Nat.mul_le_mul
          (B256.toNat_le_toNat (le_of_not_gt hcapChi))
          (B256.toNat_le_toNat (le_of_not_gt hargCap))) (by
            rw [maxChi_literal, maxUnits_literal]
            decide +kernel)
    rw [payoutDef, B256.toNat_div hscale,
      B256.toNat_mul_eq_of_nofm hnofPayout, freshEq]
    simp only [exitPayoutOf, Nat.mul_comm]
  have storage' : entry.state.getStor sevm.currentTarget =
      ((((pre.state.getStor sevm.currentTarget).set chiSlot freshChi).set rhoSlot
        sevm.benvStat.time).set (pieSlot sevm.caller)
          ((pre.state.getStor sevm.currentTarget).get (pieSlot sevm.caller) -
            units)).set totalUnitsSlot
              ((pre.state.getStor sevm.currentTarget).get totalUnitsSlot - units) := by
    rw [entryStor]
    exact storage
  have effect := exit_write_realized_effect coalition sevm.currentTarget
    sevm.caller storage' freshEq timeEq quote (le_of_not_gt hown)
    (le_of_not_gt hfund) funded entryBalance
  rw [quote] at effect
  have childPre : dripEntrySpec.Pre sevm.currentTarget
      (initSevm (childMsg.withBenv entry)) (initDevm (childMsg.withBenv entry)) := by
    apply ContractSpec.Pre.child_of_outbound_transfer
      (st := callPre.state) (st_mid := debit)
      (target := sevm.caller.toB256.toAdr) (value := payout)
    · show some (Devm.getCode callPre sevm.currentTarget).toList = _
      rw [codePre]
      exact precondition.code
    · show SumNof (Devm.getBal callPre)
      rw [balPre]
      exact precondition.side
    · show (0 : B256).toNat ≤ _
      rw [B256.toNat_zero]
      exact Nat.zero_le _
    · exact sub'
    · exact entryState
    · rfl
    · rfl
  have postSnapshot : snapshot coalition sevm.currentTarget post.state =
      snapshot coalition sevm.currentTarget child.state := by
    rw [← callPostState]
    exact snapshot_eq_of_getStor_bal
      (congrFun postStor sevm.currentTarget)
      (congrFun postBal sevm.currentTarget)
  exact ⟨{
    childMsg := childMsg
    entry := entry
    child := child
    xl := xl
    filled := filled
    process := process
    childClean := clean
    entryTransfer := transfer'
    targetNe := recipient_ne
    depth := by
      change sevm.depth - 1 < sevm.depth
      omega
    childPre := childPre
    effect := effect
    postSnapshot := postSnapshot }, rfl, rfl, rfl⟩


theorem exit_exec_handoff (coalition : Finset Adr) {sevm : Sevm}
    {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = exitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (precondition : dripEntrySpec.Pre sevm.currentTarget sevm pre)
    (caller_ne : sevm.caller ≠ sevm.currentTarget) :
    Nonempty (ExitHandoff coalition sevm pre post) := by
  have full := exit_exec_effect_full exc hcode hsel hnonempty hcanon
  unfold ExitPaysExactlyFull at full
  dsimp only at full
  rcases full with
    ⟨hargCap, -, -, hown, hfund, -, -, hclock, -, hguards, hnofm, hcapChi,
      callPre, callPost, guardPost, returnPre, storage, codePre, balPre, accepted,
      postStor, postBal, -⟩
  rcases accepted with
    ⟨gasWord, xs, parent, child, xl, delegated, nextAddress, childCode, avail, pc,
      -, -, -, -, -, hdepth, -, parentState, -, -, -, -, filled, process, clean,
      -, callPostState, -, -, -⟩
  obtain ⟨handoff, -, -, -⟩ := exit_handoff_of_components coalition
    precondition caller_ne hargCap hown hfund hclock hguards hnofm hcapChi
    storage codePre balPre postStor postBal hdepth parentState filled process
    clean callPostState
  exact ⟨handoff⟩

/-! ## The exclusive head tag

A zero-elapsed `drip` and a silent interval share both snapshots, so the kind
of a DRIP frame's head step cannot be read off its endpoints.  It is computed
from the frame's own fields instead. -/

/-- The exclusive tag of a target frame, computed from the frame's calldata,
caller, value and the elapsed time against its entry storage. -/
noncomputable def opTag (coalition : Finset Adr) (sevm : Sevm) (pre : Devm) : Kind :=
  let elapsed :=
    (sevm.benvStat.time - Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat
  let freshChi := freshNat (chiN (Devm.getStor pre sevm.currentTarget)) elapsed
  if sevm.data.length.toB256 = 0 then
    (if sevm.value = 0 then .silent else .externalCredit sevm.value.toNat)
  else if Sevm.selector sevm = dripSelector then .drip elapsed
  else if Sevm.selector sevm = joinSelector then
    .join (decide (sevm.caller ∈ coalition)) sevm.caller sevm.value.toNat
      (joinUnitsOf scale.toNat sevm.value.toNat freshChi) elapsed
  else if Sevm.selector sevm = exitSelector then
    .exit (decide (sevm.caller ∈ coalition)) sevm.caller
      (Sevm.dataWord sevm (32 * 0 + 4)).toNat
      (exitPayoutOf scale.toNat (Sevm.dataWord sevm (32 * 0 + 4)).toNat freshChi)
      elapsed
  else .silent

/-- The replay of one successful DRIP frame: one head step carrying the
computed tag from the pre-credit entry boundary, then the nested steps of its
accepted callback (empty for every selector but `exit`). -/
def TargetReplay (coalition : Finset Adr) (ca : Adr) (sevm : Sevm)
    (pre post : Devm) : Prop :=
  ∃ (op : RealizedStep) (nested : List RealizedStep),
    op.pre = execEntrySnapshot coalition ca sevm pre.state ∧
    op.kind = opTag coalition sevm pre ∧
    RealizedChain op.post nested (snapshot coalition ca post.state)

theorem TargetReplay.chain {coalition : Finset Adr} {ca : Adr} {sevm : Sevm}
    {pre post : Devm} (replay : TargetReplay coalition ca sevm pre post) :
    ∃ steps, RealizedChain (execEntrySnapshot coalition ca sevm pre.state) steps
      (snapshot coalition ca post.state) := by
  rcases replay with ⟨op, nested, preEq, _, tail⟩
  exact ⟨op :: nested, Chain.cons preEq tail⟩

/-- A head step with no nested callback. -/
theorem TargetReplay.single {coalition : Finset Adr} {ca : Adr} {sevm : Sevm}
    {pre post : Devm}
    (effect : Effect scale.toNat freshNat
      (execEntrySnapshot coalition ca sevm pre.state) (opTag coalition sevm pre)
      (snapshot coalition ca post.state)) :
    TargetReplay coalition ca sevm pre post :=
  ⟨⟨_, _, _, effect⟩, [], rfl, rfl, Chain.nil _⟩

theorem execEntrySnapshot_of_value_zero {coalition : Finset Adr} {ca : Adr}
    {sevm : Sevm} {state : State} (value : sevm.value = 0) :
    execEntrySnapshot coalition ca sevm state = snapshot coalition ca state := by
  unfold execEntrySnapshot ExecutionAccountingReplay.balanceEntry
  rw [value, B256.toNat_zero]
  split <;> rfl

/-! ## Views never move ETH

The two preview endpoints share one guarded entry into the fresh-index
machine.  Their effect theorems fix storage; the replay also needs the target
balance, which the same walk supplies: the machine keeps the entry world in
its `Frame`, and the selected return tail is call-free. -/

private theorem of_run_view_balance_eq {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    {cap route : B256}
    (view : route = routeConvertToAssets ∨ route = routeConvertToUnits)
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s
      (arg 0 +++ dup 0 ::: mstoreAt argumentWord +++ pushB256 cap ::: lt :::
        (.revert <?> (stageRoute route +++ Func.call freshStartSlot))) r) :
    Devm.getBal r = Devm.getBal entry := by
  refine run_prepend_elim _ (arg 0) ?_ run
  intro s1 hline1 run
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : Sevm.dataWord e (32 * 0 + 4) :: tail <<+ s1.stack :=
    prefix_of_cdl_val hp hline1
  refine run_prepend_elim _ [dup 0] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : Sevm.dataWord e (32 * 0 + 4) :: Sevm.dataWord e (32 * 0 + 4) ::
      tail <<+ s2.stack :=
    prefix_of_dup_val (of_run_singleton hline2) (by show_nth) hp1
  refine run_prepend_elim _ (mstoreAt argumentWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, frame3⟩ := frame2.mstoreAt hp2 hline3
  refine run_prepend_elim _ [pushB256 cap, lt] ?_ run
  intro s4 hline4 run
  have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
  have hp4 : (cap <? Sevm.dataWord e (32 * 0 + 4)) :: tail <<+ s4.stack := by
    rcases Line.of_run_cons hline4 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp3)
  obtain ⟨_, s5, hp5, hpop5, run⟩ := of_run_guard hp4 run
  have frame5 := frame4.of_popBurn hpop5
  unfold Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 route] ?_ run
  intro s6 hline6 run
  have frame6 := frame5.line (by line_inv) (by line_inv) (by line_inv) hline6
  have hp6 : route :: tail <<+ s6.stack := by
    rcases Line.of_run_cons hline6 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp5
  refine run_prepend_elim _ (mstoreAt routeWord) ?_ run
  intro s7 hline7 run
  obtain ⟨hp7, frame7⟩ := frame6.mstoreAt hp6 hline7
  obtain ⟨t8, image8, -, -, -, -, -, -, -, -, -, hmachine, frame8, hp8, run⟩ :=
    of_run_freshStart hlookup frame7 hp7 run
  have htag : scratch image8 routeWord = route := by
    rw [hmachine.1, scratch_setScratch_self]
  obtain ⟨t9, frame9, hp9, hroute⟩ := of_run_freshRoute hlookup frame8 hp8 run
  have tailEq : ∀ {after : Func}, Func.Inv Devm.getBal Devm.getBal after →
      Func.Run fs e t9 after r → Devm.getBal r = Devm.getBal entry := by
    intro after inv tailRun
    have htail : Devm.getBal t9 = Devm.getBal r :=
      Func.of_inv Devm.getBal Devm.getBal inv tailRun
    funext a
    exact (congrFun htail a).symm.trans
      (getBal_eq_of_state_eq frame9.state a).symm
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · exact tailEq (by func_inv) run
  · rcases view with rfl | rfl <;>
      exact absurd (htag.symm.trans htagE) (by decide +kernel)
  · exact tailEq (by func_inv) run
  · rcases view with rfl | rfl <;>
      exact absurd (htag.symm.trans htagD) (by decide +kernel)
  · rcases view with rfl | rfl <;>
      exact absurd (htag.symm.trans htagJ) (by decide +kernel)

/-- A successful deployed preview leaves the target balance in place. -/
theorem view_exec_balance_eq {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = convertToAssetsSelector ∨
      Sevm.selector sevm = convertToUnitsSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    Devm.getBal post = Devm.getBal pre := by
  have finish : ∀ {entry : Devm}, pre.state = entry.state →
      Devm.getBal post = Devm.getBal entry → Devm.getBal post = Devm.getBal pre := by
    intro entry hst hbal
    rw [hbal]
    funext a
    exact getBal_eq_of_state_eq hst.symm a
  rcases hsel with hsel | hsel
  · rcases exec_enters_convertToAssets exc hcode hsel hnonempty with
      ⟨-, -, entry, hst, hmm, -, -, hbody⟩
    have hentryMemory : entry.memory = Mem.empty := hmm.symm.trans hcanon
    have hframe : Frame [] entry entry :=
      ⟨by rw [hentryMemory]; exact Mem.wf_empty,
        by rw [hentryMemory]; exact Mem.reads_empty, rfl, rfl⟩
    unfold Drip.convertToAssets at hbody
    exact finish hst
      (of_run_view_balance_eq auxLookup_runtime (Or.inl rfl) hframe nil_pref hbody)
  · rcases exec_enters_convertToUnits exc hcode hsel hnonempty with
      ⟨-, -, entry, hst, hmm, -, -, hbody⟩
    have hentryMemory : entry.memory = Mem.empty := hmm.symm.trans hcanon
    have hframe : Frame [] entry entry :=
      ⟨by rw [hentryMemory]; exact Mem.wf_empty,
        by rw [hentryMemory]; exact Mem.reads_empty, rfl, rfl⟩
    unfold Drip.convertToUnits at hbody
    exact finish hst
      (of_run_view_balance_eq auxLookup_runtime (Or.inr rfl) hframe nil_pref hbody)

/-! ## The target frame, classified -/

private theorem selector_facts :
    joinSelector ≠ dripSelector ∧ exitSelector ≠ dripSelector ∧
    exitSelector ≠ joinSelector ∧
    convertToAssetsSelector ≠ dripSelector ∧
    convertToAssetsSelector ≠ joinSelector ∧
    convertToAssetsSelector ≠ exitSelector ∧
    convertToUnitsSelector ≠ dripSelector ∧
    convertToUnitsSelector ≠ joinSelector ∧
    convertToUnitsSelector ≠ exitSelector := by
  decide +kernel

/-- One head step from a single effect. -/
private theorem head_of_effect {coalition : Finset Adr} {ca : Adr}
    {sevm : Sevm} {pre post : Devm}
    (effect : Effect scale.toNat freshNat
      (execEntrySnapshot coalition ca sevm pre.state) (opTag coalition sevm pre)
      (snapshot coalition ca post.state)) :
    ∃ op : RealizedStep,
      op.pre = execEntrySnapshot coalition ca sevm pre.state ∧
      op.kind = opTag coalition sevm pre ∧
      op.post = snapshot coalition ca post.state :=
  ⟨⟨_, _, _, effect⟩, rfl, rfl, rfl⟩

/-- Every successful non-exit route of the deployed runtime is exactly one head
step from the pre-credit entry boundary to the frame's end, carrying the
frame's computed tag. -/
theorem exec_nonexit_head (coalition : Finset Adr) {sevm : Sevm}
    {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hcanon : pre.memory = Mem.empty)
    (precondition : dripEntrySpec.Pre sevm.currentTarget sevm pre)
    (hnotExit : sevm.data.length.toB256 = 0 ∨ Sevm.selector sevm ≠ exitSelector) :
    ∃ op : RealizedStep,
      op.pre = execEntrySnapshot coalition sevm.currentTarget sevm pre.state ∧
      op.kind = opTag coalition sevm pre ∧
      op.post = snapshot coalition sevm.currentTarget post.state := by
  have credited : sevm.value.toNat ≤ (pre.state.bal sevm.currentTarget).toNat :=
    precondition.inv.1 rfl
  obtain ⟨joinDrip, exitDrip, exitJoin, assetsDrip, assetsJoin, assetsExit,
    unitsDrip, unitsJoin, unitsExit⟩ := selector_facts
  by_cases hempty : sevm.data.length.toB256 = 0
  · have stateEq := (exec_receive exc hcode hempty).1
    by_cases hvalue : sevm.value = 0
    · have tag : opTag coalition sevm pre = .silent := by
        simp only [opTag, hempty, hvalue, if_true]
      apply head_of_effect
      rw [tag, execEntrySnapshot_of_value_zero hvalue, stateEq]
      exact .silent _
    · have tag : opTag coalition sevm pre = .externalCredit sevm.value.toNat := by
        simp only [opTag, hempty, hvalue, if_true, if_false]
      have positive : 0 < sevm.value.toNat := by
        rcases Nat.eq_zero_or_pos sevm.value.toNat with zero | positive
        · exact absurd (B256.toNat_inj _ _ (zero.trans B256.toNat_zero.symm)) hvalue
        · exact positive
      rcases externalCredit_chain (coalition := coalition)
          (ca := sevm.currentTarget)
          (pre := precreditState sevm.currentTarget sevm.value pre.state)
          (post := post.state) (amount := sevm.value.toNat)
          (by rw [precreditState_getStor, stateEq])
          (by rw [← stateEq, precreditState_bal credited]; omega)
          positive with ⟨op, kindEq, preEq, postEq⟩
      refine ⟨op, ?_, kindEq.trans tag.symm, postEq⟩
      rw [preEq, execEntrySnapshot_of_target rfl credited]
  · have member := exec_selector_mem exc hcode hempty
    simp only [selectors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with hsel | hsel | hsel | hsel | hsel
    · -- convertToAssets
      have tag : opTag coalition sevm pre = .silent := by
        simp only [opTag, hempty, hsel, assetsDrip, assetsJoin, assetsExit,
          if_false]
      have hvalue := (exec_enters_convertToAssets exc hcode hsel hempty).1
      have storage := (convertToAssets_exec_effect exc hcode hsel hempty
        hcanon).2.2.2.2.2.2.1
      have balance := view_exec_balance_eq exc hcode (Or.inl hsel) hempty hcanon
      apply head_of_effect
      rw [tag, execEntrySnapshot_of_value_zero hvalue,
        ← snapshot_eq_of_getStor_bal
          (congrFun storage.symm sevm.currentTarget)
          (congrFun balance sevm.currentTarget)]
      exact .silent _
    · -- exit
      rcases hnotExit with hnil | hne
      · exact absurd hnil hempty
      · exact absurd hsel hne
    · -- convertToUnits
      have tag : opTag coalition sevm pre = .silent := by
        simp only [opTag, hempty, hsel, unitsDrip, unitsJoin, unitsExit,
          if_false]
      have hvalue := (exec_enters_convertToUnits exc hcode hsel hempty).1
      have storage := (convertToUnits_exec_effect exc hcode hsel hempty
        hcanon).2.2.2.2.2.2.1
      have balance := view_exec_balance_eq exc hcode (Or.inr hsel) hempty hcanon
      apply head_of_effect
      rw [tag, execEntrySnapshot_of_value_zero hvalue,
        ← snapshot_eq_of_getStor_bal
          (congrFun storage.symm sevm.currentTarget)
          (congrFun balance sevm.currentTarget)]
      exact .silent _
    · -- drip
      have hvalue := (exec_enters_drip exc hcode hsel hempty).1
      refine ⟨⟨_, _, _,
        drip_exec_realized_effect coalition exc hcode hsel hempty hcanon⟩,
        ?_, ?_, rfl⟩
      · exact (execEntrySnapshot_of_value_zero hvalue).symm
      · simp only [opTag, hempty, hsel, if_false, if_true]
    · -- join
      rcases join_exec_effect exc hcode hsel hempty hcanon with
        ⟨assetCap, rowCap, totalCap, lower, _, clock, _, guards,
          fresh, units, freshEq, unitsEq, _, _, storageRun, _⟩
      rcases join_exec_nofm_and_balance exc hcode hsel hempty hcanon with
        ⟨freshNof, balanceRun⟩
      rcases join_source_word_facts (s := pre.state.getStor sevm.currentTarget)
          (caller := sevm.caller) assetCap rowCap totalCap lower guards freshNof
          freshEq unitsEq with ⟨freshNatEq, quote, rowNof, totalNof⟩
      have timeNat : sevm.benvStat.time.toNat =
          rhoN (pre.state.getStor sevm.currentTarget) +
            (sevm.benvStat.time -
              Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat := by
        have timeLe := le_of_not_gt clock
        have timeLeNat := B256.toNat_le_toNat timeLe
        have := B256.toNat_sub_eq_of_le _ _ timeLe
        unfold rhoN
        change sevm.benvStat.time.toNat =
          (Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat + _
        omega
      have before :=
        precreditState_getStor sevm.currentTarget sevm.value pre.state
      have effect := join_write_realized_effect coalition sevm.currentTarget
        sevm.caller
        (before := precreditState sevm.currentTarget sevm.value pre.state)
        (after := post.state) (fresh := fresh) (now := sevm.benvStat.time)
        (units := units) (value := sevm.value)
        (elapsed := (sevm.benvStat.time -
          Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat)
        (by rw [before]; exact storageRun)
        (by rw [before]; exact freshNatEq)
        (by rw [before]; exact timeNat)
        (by rw [before]; exact quote)
        (by rw [before]; exact rowNof)
        (by rw [before]; exact totalNof)
        (by
          rw [precreditState_bal credited]
          have := congrArg B256.toNat balanceRun
          change (post.state.bal sevm.currentTarget).toNat =
            (pre.state.bal sevm.currentTarget).toNat at this
          omega)
      rw [quote] at effect
      refine ⟨⟨_, _, _, effect⟩, ?_, ?_, rfl⟩
      · exact (execEntrySnapshot_of_target rfl credited).symm
      · simp only [opTag, hempty, hsel, joinDrip, if_false, if_true]
        rfl

/-- Every successful frame of the deployed runtime is one tagged head step
followed by the replay of its accepted exit callback, if it has one.  The
callback's replay is the only premise: it is supplied by the deeper-frame
induction hypothesis of the recursion below, never assumed of the child. -/
theorem exec_targetReplay (coalition : Finset Adr) {sevm : Sevm}
    {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hcanon : pre.memory = Mem.empty)
    (precondition : dripEntrySpec.Pre sevm.currentTarget sevm pre)
    (caller_ne : sevm.caller ≠ sevm.currentTarget)
    (exitNested : ∀ handoff : ExitHandoff coalition sevm pre post,
      ∃ nested, RealizedChain
        (snapshot coalition sevm.currentTarget handoff.entry.state) nested
        (snapshot coalition sevm.currentTarget handoff.child.state)) :
    TargetReplay coalition sevm.currentTarget sevm pre post := by
  by_cases hexit : sevm.data.length.toB256 ≠ 0 ∧ Sevm.selector sevm = exitSelector
  · obtain ⟨hempty, hsel⟩ := hexit
    obtain ⟨joinDrip, exitDrip, exitJoin, -, -, -, -, -, -⟩ := selector_facts
    have hvalue := (exec_enters_exit exc hcode hsel hempty).1
    obtain ⟨handoff⟩ := exit_exec_handoff coalition exc hcode hsel hempty
      hcanon precondition caller_ne
    rcases exitNested handoff with ⟨nested, chain⟩
    refine ⟨⟨_, _, _, handoff.effect⟩, nested, ?_, ?_, ?_⟩
    · exact (execEntrySnapshot_of_value_zero hvalue).symm
    · simp only [opTag, hempty, hsel, exitDrip, exitJoin, if_false, if_true]
    · rw [handoff.postSnapshot]
      exact chain
  · have hnotExit : sevm.data.length.toB256 = 0 ∨ Sevm.selector sevm ≠ exitSelector := by
      by_cases hnil : sevm.data.length.toB256 = 0
      · exact Or.inl hnil
      · exact Or.inr fun hsel => hexit ⟨hnil, hsel⟩
    rcases exec_nonexit_head coalition exc hcode hcanon precondition hnotExit with
      ⟨op, preEq, kindEq, postEq⟩
    refine ⟨op, [], preEq, kindEq, ?_⟩
    rw [postEq]
    exact Chain.nil _

/-- The recursion facts of an exit frame's filled payout child: it commits, is
foreign, keeps the side precondition and the installed code, is strictly
deeper, and starts and ends at the handoff's entry and child worlds. -/
theorem exitChild_facts (coalition : Finset Adr) {sevm : Sevm}
    {childMsg : Msg} {hentry : Benv} {child : Devm}
    {childPc : Nat} {childSevm : Sevm} {childPre : Devm} {childOut : Execution}
    (process : ProcessMessage childMsg
      (.some ⟨⟨childPc, childSevm, childPre⟩, childOut⟩) (.ok child))
    (childClean : child.error.isSome = false)
    (entryTransfer : childMsg.benvAfterTransfer = .ok hentry)
    (targetNe : childMsg.currentTarget ≠ sevm.currentTarget)
    (depth : (initSevm (childMsg.withBenv hentry)).depth < sevm.depth)
    (childPreH : dripEntrySpec.Pre sevm.currentTarget
      (initSevm (childMsg.withBenv hentry)) (initDevm (childMsg.withBenv hentry))) :
    ∃ childCommitted : Execution.commits childOut = true,
      childSevm.currentTarget ≠ sevm.currentTarget ∧
      dripEntrySpec.Pre sevm.currentTarget childSevm childPre ∧
      Prog.At runtime sevm.currentTarget childPc childSevm childPre ∧
      childSevm.depth < sevm.depth ∧
      execEntrySnapshot coalition sevm.currentTarget childSevm childPre.state =
        snapshot coalition sevm.currentTarget hentry.state ∧
      child.state = (Execution.committedPost childOut childCommitted).state := by
  have settles :=
    _root_.Blanc.ProcessMessage.settlementCommits_of_some_ok_clean
      process childClean
  have childCommitted :=
    Frame.raw_commits_of_settlementCommits settles
  have enter := (RunFrame.some_inv process).1
  rcases Frame.enter_run_inv enter with ⟨entry, transfer, childEvmEq⟩
  simp only [Frame.ofCall] at transfer childEvmEq
  have entryEq : entry = hentry :=
    Except.ok.inj (transfer.symm.trans entryTransfer)
  subst entry
  have childSevmEq : childSevm =
      initSevm (childMsg.withBenv hentry) :=
    congrArg (fun evm : Evm => evm.sta) childEvmEq
  have childPreEq : childPre =
      initDevm (childMsg.withBenv hentry) :=
    congrArg (fun evm : Evm => evm.dyna) childEvmEq
  have childTargetNe : childSevm.currentTarget ≠ sevm.currentTarget := by
    rw [childSevmEq]
    simpa [initSevm, Msg.withBenv] using targetNe
  have childPrecondition :
      dripEntrySpec.Pre sevm.currentTarget childSevm childPre := by
    rw [childSevmEq, childPreEq]
    exact childPreH
  have childAt : Prog.At runtime sevm.currentTarget childPc
      childSevm childPre :=
    ⟨childPrecondition.code,
      fun childTarget => (childTargetNe childTarget).elim⟩
  have childDepth : childSevm.depth < sevm.depth := by
    rw [childSevmEq]
    exact depth
  have startEq :
      execEntrySnapshot coalition sevm.currentTarget childSevm
          childPre.state =
        snapshot coalition sevm.currentTarget hentry.state := by
    rw [execEntrySnapshot_of_target_ne childTargetNe, childPreEq]
    rfl
  exact ⟨childCommitted, childTargetNe, childPrecondition, childAt, childDepth,
    startEq,
    _root_.Blanc.ProcessMessage.ok_state_eq_committedPost process childCommitted⟩

/-! ## The interpreter recursion -/

/-- T1.  Proof-indexed committed replay for one interpreter suffix.  The second
conjunct is the exclusivity clause: a frame executing DRIP itself opens with
exactly one step whose kind is the frame's computed tag. -/
def _root_.Blanc.Exec.CoreDripAccounting (coalition : Finset Adr) (ca : Adr)
    (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution) : Prop :=
  ∀ (_run : Exec pc sevm pre out)
    (committed : Execution.commits out = true),
    Prog.At runtime ca pc sevm pre →
    dripEntrySpec.Pre ca sevm pre →
    (sevm.currentTarget = ca → sevm.codeAddress = some ca) →
    (sevm.currentTarget = ca → sevm.caller ≠ ca) →
    (sevm.currentTarget = ca → pre.memory = Mem.empty) →
    ∃ steps : List RealizedStep,
      RealizedChain (execEntrySnapshot coalition ca sevm pre.state) steps
        (snapshot coalition ca (Execution.committedPost out committed).state) ∧
      (sevm.currentTarget = ca → ∃ op nested,
        steps = op :: nested ∧ op.kind = opTag coalition sevm pre)

end Drip

open Drip

/-- A failed raw execution cannot satisfy the committed replay premise. -/
theorem Exec.CoreDripAccounting.error
    {coalition : Finset Adr} {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {error : EvmError × Devm} :
    Exec.CoreDripAccounting coalition ca pc sevm pre (.error error) := by
  intro _ committed
  simp [Execution.commits] at committed

/-- T2.  The compiled DRIP frame handler.  Every route closes in one tagged
head step; `exit` then recurses into exactly its settlement-retained payout
child through `deeper`, and that child's replay is the nested tail. -/
theorem Exec.CoreDripAccounting.atTarget
    {coalition : Finset Adr} {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (_programRun : Prog.Run sevm pre runtime post)
    (target : sevm.currentTarget = ca)
    (deeper : ForallDeeperAt sevm.depth ca runtime
      (fun pc childSevm childPre childOut _ =>
        Exec.CoreDripAccounting coalition ca pc childSevm childPre childOut)) :
    Exec.CoreDripAccounting coalition ca 0 sevm pre (.ok post) := by
  subst ca
  intro run committed installed precondition _ caller canonical
  have hcode : sevm.code.toList = code := by
    have compiled := (installed.2 rfl).1
    rw [code_compile] at compiled
    exact Option.some.inj compiled
  have replay : TargetReplay coalition sevm.currentTarget sevm pre post := by
    apply exec_targetReplay coalition run hcode (canonical rfl) precondition
      (caller rfl)
    rintro ⟨childMsg, hentry, child, xl, filled, process, childClean,
      entryTransfer, targetNe, depth, childPreH, _, _⟩
    dsimp only
    rcases ExecutionTrace.exists_retainedXlot_of_filled filled with
      ⟨retained⟩
    cases retained with
    | none =>
        have childState :=
          _root_.Blanc.ProcessMessage.none_ok_state_eq_entry_of_clean
            process entryTransfer childClean
        refine ⟨[], ?_⟩
        rw [childState]
        exact Chain.nil _
    | @some childPc childSevm childPre childOut childRun =>
        obtain ⟨childCommitted, childTargetNe, childPrecondition, childAt,
            childDepth, startEq, childPost⟩ :=
          exitChild_facts coalition process childClean entryTransfer targetNe
            depth childPreH
        rcases deeper childPc childSevm childPre childOut childRun
            childDepth childAt childRun childCommitted childAt childPrecondition
            (fun childTarget => (childTargetNe childTarget).elim)
            (fun childTarget => (childTargetNe childTarget).elim)
            (fun childTarget => (childTargetNe childTarget).elim) with
          ⟨steps, chain, _⟩
        refine ⟨steps, ?_⟩
        rw [← startEq, childPost]
        exact chain
  rcases replay with ⟨op, nested, preEq, kindEq, tail⟩
  exact ⟨op :: nested, Chain.cons preEq tail, fun _ => ⟨op, nested, rfl, kindEq⟩⟩

/-- A foreign suffix's replay, stated at the ordinary projection. -/
private theorem foreign_conclusion
    {coalition : Finset Adr} {ca : Adr} {sevm : Sevm} {pre : Devm}
    {final : State} {steps : List RealizedStep}
    (target_ne : sevm.currentTarget ≠ ca)
    (chain : RealizedChain (snapshot coalition ca pre.state) steps
      (snapshot coalition ca final)) :
    ∃ steps : List RealizedStep,
      RealizedChain (execEntrySnapshot coalition ca sevm pre.state) steps
        (snapshot coalition ca final) ∧
      (sevm.currentTarget = ca → ∃ op nested,
        steps = op :: nested ∧ op.kind = opTag coalition sevm pre) := by
  refine ⟨steps, ?_, fun target => (target_ne target).elim⟩
  rw [execEntrySnapshot_of_target_ne target_ne]
  exact chain

/-- T3.  Foreign nonrecursive execution prefixes its projected accounting
change to the continuation replay. -/
theorem Exec.CoreDripAccounting.nextNone
    {coalition : Finset Adr} {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {n : Ninst} {inter : Devm} {out : Execution}
    (_at : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out)
    (target_ne : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreDripAccounting coalition ca (pc + n.size) sevm inter out) :
    Exec.CoreDripAccounting coalition ca pc sevm pre out := by
  intro _ committed installed precondition _ _ _
  have interPre : dripEntrySpec.Pre ca sevm inter :=
    _root_.Blanc.ContractSpec.Ninst.none_preserves_precond
      (c := dripEntrySpec) step target_ne precondition
  have installedInter : Prog.At runtime ca (pc + n.size) sevm inter :=
    ⟨interPre.code, fun target => (target_ne target).elim⟩
  have sumNof : sum pre.state.bal < 2 ^ 256 := precondition.side
  rcases (carrier coalition ca).ofStorageEqBalanceMono ()
      (_root_.Blanc.Ninst.foreignNone_getStor_eq step target_ne)
      (_root_.Blanc.Ninst.targetBalanceMono_of_none step target_ne sumNof) with
    ⟨headSteps, headReplay⟩
  rcases ih next committed installedInter interPre
      (fun target => (target_ne target).elim)
      (fun target => (target_ne target).elim)
      (fun target => (target_ne target).elim) with
    ⟨tailSteps, tailReplay, _⟩
  rw [execEntrySnapshot_of_target_ne target_ne] at tailReplay
  exact foreign_conclusion target_ne (Chain.append headReplay tailReplay)

/-- A foreign terminal instruction is the final projected accounting segment
of its frame. -/
theorem Exec.CoreDripAccounting.last
    {coalition : Finset Adr} {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {l : Linst} {out : Execution}
    (_at : Linst.At sevm.code pc l)
    (step : Linst.Run sevm pre l out)
    (target_ne : sevm.currentTarget ≠ ca) :
    Exec.CoreDripAccounting coalition ca pc sevm pre out := by
  intro _ committed _ precondition _ _ _
  cases out with
  | error error =>
      simp [Execution.commits] at committed
  | ok post =>
      have sumNof : sum pre.state.bal < 2 ^ 256 := precondition.side
      rcases (carrier coalition ca).ofStorageEqBalanceMono ()
          (congrFun (_root_.Blanc.Linst.getStor_eq step) ca)
          (_root_.Blanc.Linst.targetBalanceMono_of_foreign step target_ne
            sumNof) with
        ⟨steps, replay⟩
      exact foreign_conclusion target_ne replay

/-- Jump execution is world-state silent, so only its continuation
contributes accounting steps. -/
theorem Exec.CoreDripAccounting.jump
    {coalition : Finset Adr} {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {j : Jinst} {pc' : Nat} {inter : Devm} {out : Execution}
    (_at : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out)
    (target_ne : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreDripAccounting coalition ca pc' sevm inter out) :
    Exec.CoreDripAccounting coalition ca pc sevm pre out := by
  intro _ committed _ precondition _ _ _
  have stateEq : inter.state = pre.state := Jinst.preserves_state step
  have interPre : dripEntrySpec.Pre ca sevm inter :=
    precondition.state_eq stateEq
  have installedInter : Prog.At runtime ca pc' sevm inter :=
    ⟨interPre.code, fun target => (target_ne target).elim⟩
  rcases ih next committed installedInter interPre
      (fun target => (target_ne target).elim)
      (fun target => (target_ne target).elim)
      (fun target => (target_ne target).elim) with
    ⟨steps, replay, _⟩
  rw [execEntrySnapshot_of_target_ne target_ne, stateEq] at replay
  exact foreign_conclusion target_ne replay

/-- A foreign filled child is replayed recursively, transported through
complete CALL/CREATE settlement by the shared seam, and followed by the parent
continuation. -/
theorem Exec.CoreDripAccounting.nextSome
    {coalition : Finset Adr} {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {n : Ninst} {cevm : Evm} {raw : Execution} {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out)
    (target_ne : sevm.currentTarget ≠ ca)
    (ihChild : Exec.CoreDripAccounting coalition ca
      cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : Exec.CoreDripAccounting coalition ca
      (pc + n.size) sevm inter out) :
    Exec.CoreDripAccounting coalition ca pc sevm pre out := by
  cases n with
  | reg r =>
      simp [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at step
  | push xs length =>
      simp [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at step
  | exec x =>
      intro _ committed installed precondition _ _ _
      have xrun : Xinst.Run sevm pre x (.some ⟨cevm, raw⟩) (.ok inter) := by
        simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep,
          Xinst.Run] using step
      have hxrun := XStep.run_toStep.mp step
      cases spawnEq : Xinst.step sevm pre x with
      | done execution =>
          simp [spawnEq, XStep.Run] at hxrun
      | spawn frame resume =>
          simp only [spawnEq, XStep.Run] at hxrun
          obtain ⟨result, frameRun, resumeRun⟩ := hxrun
          cases result with
          | error error =>
              cases resume <;>
                simp [Resume.run, liftToExecution] at resumeRun
          | ok settled =>
              have enter := (RunFrame.some_inv frameRun).1
              have evmStep : Evm.step ⟨pc, sevm, pre⟩ =
                  .spawn frame resume (pc + 1) := by
                rw [Evm.step_next hat]
                simp only [Ninst.step_exec, spawnEq, XStep.toStep]
              obtain ⟨childPcZero, childGetCode, childCodeSource⟩ :=
                Evm.step_spawn_child evmStep enter
              have childAt : Prog.At runtime ca cevm.pc cevm.sta cevm.dyna := by
                refine ⟨?_, fun childTarget => ⟨?_, childPcZero⟩⟩
                · rw [childGetCode ca]
                  exact installed.1
                · have parentTargetNe :
                      sevm.currentTarget ≠ cevm.sta.currentTarget := by
                    rw [childTarget]
                    exact target_ne
                  have codeEq := childCodeSource parentTargetNe
                    (by rw [childTarget]
                        exact not_empty_of_compile installed.1)
                    (by rw [childTarget]
                        exact not_delegation_of_compile installed.1)
                  rw [codeEq, childTarget]
                  exact installed.1
              rcases Frame.enter_run_inv enter with
                ⟨entry, transfer, childEvmEq⟩
              have childDirect : cevm.sta.currentTarget = ca →
                  cevm.sta.codeAddress = some ca := by
                intro childTarget
                have innerTarget : frame.inner.currentTarget = ca := by
                  rw [← Frame.enter_run_currentTarget enter]
                  exact childTarget
                have parentTargetNe :
                    sevm.currentTarget ≠ frame.inner.currentTarget := by
                  rw [innerTarget]
                  exact target_ne
                have targetCodeNonempty :
                    pre.getCode frame.inner.currentTarget ≠ .empty := by
                  rw [innerTarget]
                  exact not_empty_of_compile installed.1
                have codeAddress :=
                  _root_.Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget
                    spawnEq parentTargetNe targetCodeNonempty
                    (by rw [innerTarget]
                        dsimp only [getDelegatedCodeAddress]
                        rw [if_neg
                          (not_delegation_of_compile installed.1)])
                have childCodeAddress :=
                  congrArg (fun evm : Evm => evm.sta.codeAddress) childEvmEq
                dsimp [initEvm, initSevm, Msg.withBenv] at childCodeAddress
                rw [childCodeAddress, codeAddress, innerTarget]
              have childCaller : cevm.sta.currentTarget = ca →
                  cevm.sta.caller ≠ ca := by
                intro childTarget
                have innerTarget : frame.inner.currentTarget = ca := by
                  rw [← Frame.enter_run_currentTarget enter]
                  exact childTarget
                have callerNe :=
                  _root_.Blanc.Xinst.step_spawn_caller_ne_of_target_eq
                    spawnEq target_ne innerTarget
                have childCallerEq :=
                  congrArg (fun evm : Evm => evm.sta.caller) childEvmEq
                dsimp [initEvm, initSevm, Msg.withBenv] at childCallerEq
                rw [childCallerEq]
                exact callerNe
              have childCanonical : cevm.sta.currentTarget = ca →
                  cevm.dyna.memory = Mem.empty := by
                intro _
                have childMemoryEq :=
                  congrArg (fun evm : Evm => evm.dyna.memory) childEvmEq
                exact childMemoryEq
              obtain ⟨childPrecondition, continuationOfPost⟩ :=
                _root_.Blanc.ContractSpec.Xinst.some_preserves_precond
                  (c := dripEntrySpec) xrun child target_ne precondition
              have childPost :
                  ifOk (dripEntrySpec.Post ca cevm.sta) raw := by
                cases raw with
                | error error => trivial
                | ok rawPost =>
                    have childAtZero :
                        Exec 0 cevm.sta cevm.dyna (.ok rawPost) := by
                      rw [← childPcZero]
                      exact child
                    exact dripEntrySpec_preservesNoMem ca cevm.sta cevm.dyna
                      rawPost childAtZero
                      (fun childTarget => (childAt.2 childTarget).1)
                      childPrecondition
              have interPre : dripEntrySpec.Pre ca sevm inter :=
                continuationOfPost childPost
              have installedInter :
                  Prog.At runtime ca (pc + 1) sevm inter :=
                ⟨interPre.code, fun target => (target_ne target).elim⟩
              have sumNof : sum pre.state.bal < 2 ^ 256 :=
                precondition.side
              have childBody :
                  ∀ childCommitted : Execution.commits raw = true, ∃ steps,
                    RealizedChain
                      (execEntrySnapshot coalition ca cevm.sta cevm.dyna.state)
                      steps
                      (snapshot coalition ca
                        (Execution.committedPost raw childCommitted).state) := by
                intro childCommitted
                rcases ihChild child childCommitted childAt childPrecondition
                    childDirect childCaller childCanonical with
                  ⟨steps, chain, _⟩
                exact ⟨steps, chain⟩
              rcases (carrier coalition ca).xinstForeignSome spawnEq frameRun
                  resumeRun.symm target_ne sumNof childBody with
                ⟨headSteps, headReplay⟩
              rcases ihNext next committed installedInter interPre
                  (fun target => (target_ne target).elim)
                  (fun target => (target_ne target).elim)
                  (fun target => (target_ne target).elim) with
                ⟨tailSteps, tailReplay, _⟩
              rw [execEntrySnapshot_of_target_ne target_ne] at tailReplay
              exact foreign_conclusion target_ne
                (Chain.append headReplay tailReplay)

/-- The complete interpreter recursion for committed DRIP accounting.  Every
at-target frame is discharged by the classified frame handler; all foreign
instruction cases preserve and compose the exact replay. -/
theorem Exec.coreDripAccounting (coalition : Finset Adr) {ca : Adr} :
    Exec.Fa (Exec.Wkn ca runtime
      (fun pc sevm pre out _ =>
        Exec.CoreDripAccounting coalition ca pc sevm pre out)) := by
  apply lift_core
    (ε := fun pc sevm pre out =>
      Exec.CoreDripAccounting coalition ca pc sevm pre out)
    (π := fun sevm pre post =>
      Exec.CoreDripAccounting coalition ca 0 sevm pre (.ok post))
    (analog := fun h => h)
    (ca := ca) (p := runtime)
  · intro sevm pre post run target deeper
    exact Exec.CoreDripAccounting.atTarget run target deeper
  · intro pc sevm pre error post target
    exact Exec.CoreDripAccounting.error
  · intro pc sevm pre noneAt targetNe
    exact Exec.CoreDripAccounting.error
  · intro pc sevm pre n error post hat step targetNe
    exact Exec.CoreDripAccounting.error
  · intro pc sevm pre n childEvm childOut error post
      hat step child targetNe ihChild
    exact Exec.CoreDripAccounting.error
  · intro pc sevm pre n inter out hat step next targetNe ihNext
    exact Exec.CoreDripAccounting.nextNone
      hat step next targetNe ihNext
  · intro pc sevm pre n childEvm childOut inter out
      hat step child next targetNe ihChild ihNext
    exact Exec.CoreDripAccounting.nextSome
      hat step child next targetNe ihChild ihNext
  · intro pc sevm pre j error post hat step targetNe
    exact Exec.CoreDripAccounting.error
  · intro pc sevm pre j pc' inter out
      hat step next targetNe ihNext
    exact Exec.CoreDripAccounting.jump
      hat step next targetNe ihNext
  · intro pc sevm pre l out hat step targetNe
    exact Exec.CoreDripAccounting.last hat step targetNe

/-! ## Consumption interface for the wrapper ladder -/

namespace Drip

/-- The side spec's world invariant is `dripSpec`'s code fact plus the word
bound on the world total; its ledger clause is vacuous. -/
theorem dripEntrySpec_stateInv {ca : Adr} {world : State}
    (inv : dripSpec.StateInv ca world) (sumNof : sum world.bal < 2 ^ 256) :
    dripEntrySpec.StateInv ca world := by
  refine ⟨inv.code, sumNof, ?_⟩
  show (0 : B256).toNat ≤ _
  rw [B256.toNat_zero]
  exact Nat.zero_le _

/-- Message readiness transfers from `dripSpec` to the side spec given the
word bound every retained chronology already carries. -/
theorem dripEntrySpec_messageRunReady {ca : Adr} {msg : Msg}
    (ready : dripSpec.MessageRunReady ca msg)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256) :
    dripEntrySpec.MessageRunReady ca msg :=
  ⟨⟨dripEntrySpec_stateInv ready.ready.state sumNof, ready.ready.nodel,
      ready.ready.code, ready.ready.codeAddress, ready.ready.ne,
      ready.ready.val0⟩,
    ready.codeOrForeign⟩

end Drip

/-- Instantiate the recursive interpreter theorem at the exact EVM root
selected by a successful message entry.  The result keeps the exclusivity
clause, so a root DRIP call is known to open with its computed tag. -/
theorem Exec.dripRealizedChain_of_messageRoot
    (coalition : Finset Adr) {ca : Adr} {msg : Msg} {entry : Benv}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (transfer : msg.benvAfterTransfer = .ok entry)
    (evmEq : (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entry))
    (committed : Execution.commits out = true)
    (ready : dripEntrySpec.MessageRunReady ca msg)
    (caller_ne : msg.currentTarget = ca → msg.caller ≠ ca) :
    ∃ steps : List RealizedStep,
      RealizedChain (execEntrySnapshot coalition ca sevm pre.state) steps
        (snapshot coalition ca (Execution.committedPost out committed).state) ∧
      (sevm.currentTarget = ca → ∃ op nested,
        steps = op :: nested ∧ op.kind = opTag coalition sevm pre) := by
  have precondition :=
    ContractSpec.Pre.of_inv_benvAfterTransfer
      ready.ready.ne ready.ready.val0 transfer ready.ready.state
  have pcEq := congrArg Evm.pc evmEq
  have sevmEq := congrArg Evm.sta evmEq
  have preEq := congrArg Evm.dyna evmEq
  dsimp only [initEvm] at pcEq sevmEq preEq
  subst pc
  subst sevm
  subst pre
  have installed : Prog.At runtime ca 0
      (initSevm (msg.withBenv entry))
      (initDevm (msg.withBenv entry)) := by
    refine ⟨precondition.code, ?_⟩
    intro target
    refine ⟨?_, rfl⟩
    rcases ready.codeOrForeign with call | foreign
    · exact ready.ready.code call
        (by simpa [initSevm, Msg.withBenv] using target)
    · exact False.elim (foreign
        (by simpa [initSevm, Msg.withBenv] using target))
  have direct :
      (initSevm (msg.withBenv entry)).currentTarget = ca →
        (initSevm (msg.withBenv entry)).codeAddress = some ca := by
    intro target
    rcases ready.codeOrForeign with call | foreign
    · exact ready.ready.codeAddress call
        (by simpa [initSevm, Msg.withBenv] using target)
    · exact False.elim (foreign
        (by simpa [initSevm, Msg.withBenv] using target))
  have caller :
      (initSevm (msg.withBenv entry)).currentTarget = ca →
        (initSevm (msg.withBenv entry)).caller ≠ ca := by
    intro target
    exact caller_ne (by simpa [initSevm, Msg.withBenv] using target)
  have all := Exec.coreDripAccounting coalition (ca := ca)
  have core := all 0 (initSevm (msg.withBenv entry))
    (initDevm (msg.withBenv entry)) out run installed
  exact core run committed installed precondition direct caller (fun _ => rfl)

end Blanc
