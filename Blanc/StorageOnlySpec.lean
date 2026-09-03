-- StorageOnlySpec.lean : the ladder adapter for a storage-determined invariant.

import Blanc.Ladder
import Blanc.Tactics
import Blanc.StaticStorage
import Blanc.BalanceAlgebra

/-!
# Contract specs whose invariant reads only storage

`ContractSpec` carries an invariant over three arguments — the contract's
storage, the callvalue in flight, and the contract's ETH balance — because a
wrapped-native-token contract's solvency claim needs all three.  A contract
whose invariant is a property of its storage alone still has to answer the
record's eight balance obligations, and every one of those answers is the same:
none of `addBal`, `subBal` or a value transfer moves the storage at any
address, so the invariant is carried by a rewrite.

`ContractSpec.ofStorageOnly` packages that argument once.  It also declines the
`nof`-class side condition, which a storage-determined invariant never needs.

`Blanc/Conserved.lean`'s `fmintSpec` predates this module and states the same
eight answers inline for `Stor.Conserved`; folding it onto this adapter belongs
to the fmint family rather than to a consumer.
-/

namespace Blanc

open Jaune

/-- The storage at `ca` is blind to a credit. -/
theorem getStor_addBal (w : Jaune.State) (ca a : Adr) (val : B256) :
    (w.addBal a val).getStor ca = w.getStor ca := by
  show ((w.setBal a _).get ca).stor = (w.get ca).stor
  rw [State.setBal_get_stor]

/-- The storage at `ca` is blind to a debit followed by a credit. -/
theorem getStor_subBal_addBal {st st' : Jaune.State} {caller callee ca : Adr}
    {wad : B256} (h_sub : st.subBal caller wad = some st') :
    (st'.addBal callee wad).getStor ca = st.getStor ca := by
  rcases State.of_subBal h_sub with ⟨-, h_st'⟩
  show ((st'.setBal callee _).get ca).stor = (st.get ca).stor
  rw [State.setBal_get_stor, h_st', State.setBal_get_stor]

/-- A contract whose invariant is determined by its own storage, packaged for
the generic execution ladder.  The callvalue and balance arguments are
discarded, so the four monotonicity fields are `id`-shaped and the four
world-movement fields are one storage rewrite each. -/
def ContractSpec.ofStorageOnly (p : Prog) (P : Stor → Prop) : ContractSpec where
  prog := p
  Inv := fun s _ _ => P s
  Side := fun _ => True
  inv_forget := id
  inv_mono := fun h _ => h
  inv_recv := fun h _ => h
  side_le := fun _ _ => trivial
  side_transfer := fun _ _ => trivial
  side_addBal := fun _ _ => trivial
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub _ _ h_inv
    show P _
    rw [getStor_subBal_addBal h_sub]
    exact h_inv
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub _ _ h_inv
    show P _
    rw [getStor_subBal_addBal h_sub]
    exact h_inv
  inv_addBal := by
    intro w ca a val v _ _ h_inv
    show P _
    rw [getStor_addBal]
    exact h_inv

/-- The frame-entry invariant of a storage-determined spec carries no
callvalue case: both branches of `PreInv` are the same proposition, so the
conjunction collapses.  Hoisted from fmint's `fmintSpec_preInv_iff`, which is
now this lemma. -/
theorem ContractSpec.ofStorageOnly_preInv_iff {p : Prog} {P : Stor → Prop}
    {ca : Adr} {sevm : Sevm} {devm : Devm} :
    (ContractSpec.ofStorageOnly p P).PreInv devm ca sevm ↔
      P (Devm.getStor devm ca) := by
  constructor
  · intro h
    by_cases h_ct : sevm.currentTarget = ca
    · exact h.1 h_ct
    · exact h.2 h_ct
  · exact fun h => ⟨fun _ => h, fun _ => h⟩

/-- The frame-exit invariant of a storage-determined spec is the storage
property outright. -/
theorem ContractSpec.ofStorageOnly_postInv_iff {p : Prog} {P : Stor → Prop}
    {ca : Adr} {devm : Devm} :
    (ContractSpec.ofStorageOnly p P).PostInv devm ca ↔
      P (Devm.getStor devm ca) := Iff.rfl

/-- Reduce a storage-determined spec's per-target obligation to the bare
storage implication: `Side` is trivial, `PreInv` and `PostInv` are the storage
property, and the deeper-frame hypothesis is discarded.  A target that consumes
the deeper-frame hypothesis — a re-entrant one — proves `FuncSoundNoMem`
directly instead.

Hoisted from fmint's `fmintSpec_funcSound`; the second consumer is the
WETH-backed PRORATA vault. -/
theorem ContractSpec.ofStorageOnly_funcSound {p : Prog} {P : Stor → Prop}
    {ca : Adr} {aux : List Func} (f : Func)
    (h_cons : ∀ {sevm : Sevm} {s r : Devm},
      Func.Run (p.main :: aux) sevm s f r →
      P (Devm.getStor s sevm.currentTarget) →
      P (Devm.getStor r sevm.currentTarget)) :
    (ContractSpec.ofStorageOnly p P).FuncSoundNoMem ca aux f := by
  intro sevm s r h_ct h_pre _ h_run
  subst h_ct
  exact ⟨trivial, h_cons h_run (ofStorageOnly_preInv_iff.mp h_pre.inv)⟩

/-- Discharge a target that never writes storage: `func_inv` shows the walk
leaves `Devm.getStor` alone at every account, and the invariant is transported
along that equality by its own `of_eq`.

Generic in the invariant — `h.of_eq` resolves from the type of `h` — so this
serves any storage-determined property with an `of_eq` transport, which is
every consumer of `ContractSpec.ofStorageOnly`.  Hoisted from fmint's
`simple_conserved`, which is now this tactic.

The tactic names `h` and `run` in the caller's context, so it is written with
`hygiene` off and only applies where those are the invariant hypothesis and the
run.  That is the calling convention of every per-target obligation below
`ofStorageOnly_funcSound`. -/
syntax "storage_silent" : tactic
set_option hygiene false in
macro_rules
| `(tactic| storage_silent) =>
  `(tactic| exact h.of_eq
              (congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run)
                sevm.currentTarget))

/-- Discharge a target that writes no storage but *does* make a `STATICCALL`.

`func_inv` cannot synthesise `Ninst.Hinv Devm.getStor Ninst.staticcall`, and
should not: `Stor` is a tree whose raw equality distinguishes redundant zero
entries, so entering interpreted code preserves the storage *observation*
rather than the representation.  `Blanc/StaticStorage.lean` supplies the
instance at `Devm.storageView`, and the invariant is transported along the
resulting pointwise equality by its own `of_get_eq`.

Prefer `storage_silent`, which is cheaper; reach for this one when the target
reads another contract through a static call, as every live-quoting ERC-4626
view does. -/
syntax "storage_silent_static" : tactic
set_option hygiene false in
macro_rules
| `(tactic| storage_silent_static) =>
  `(tactic| exact h.of_get_eq (fun key =>
              congrFun (congrFun
                (Func.of_inv Devm.storageView Devm.storageView (by func_inv) run)
                sevm.currentTarget) key))

@[simp] theorem ContractSpec.ofStorageOnly_prog {p : Prog} {P : Stor → Prop} :
    (ContractSpec.ofStorageOnly p P).prog = p := rfl

@[simp] theorem ContractSpec.ofStorageOnly_inv {p : Prog} {P : Stor → Prop}
    {s : Stor} {v b : B256} :
    (ContractSpec.ofStorageOnly p P).Inv s v b = P s := rfl

section ChildCall

open Jaune.Ninst Ninst

/-- **A child call, under the deeper-frame hypothesis.**  Any successful `call`
made from the contract's own frame preserves a storage-determined invariant,
provided every deeper frame does — which is exactly what `Exec.InvDepth`
supplies.  A re-entrant target is the only kind that consumes it.

The operands are arbitrary: a storage-determined invariant cannot see a value
transfer, so the lemma does not need to know one happened.  The parent's stack
shape comes back too, because a caller that keeps executing after the call
returns needs its own operands.

The induction hypothesis is applied at the child's initial machine: the value
transfer touches only balances, so the child enters with the parent's storage
and code at the contract address, and `Prog.At` needs the delegation argument —
a compiled program is never a delegation designator, so `accessDelegation`
resolves to the code itself.

Hoisted from fmint's `conserved_of_call`, which is now this lemma at
`Stor.Conserved`.  The second consumer is the WETH-backed PRORATA vault, whose
four ERC-4626 flows each call WETH. -/
theorem ContractSpec.ofStorageOnly_of_call {p : Prog} {P : Stor → Prop}
    {sevm : Sevm} {s sf : Devm} {g w v ii is oi os : B256} {xs : Stack}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget p
      ((ContractSpec.ofStorageOnly p P).PreWf sevm.currentTarget) ((ContractSpec.ofStorageOnly p P).Post sevm.currentTarget))
    (hp : (g :: w :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile p)
    (h_cons : P (Devm.getStor s sevm.currentTarget))
    (h_run : Ninst.Run sevm s call sf) :
    P (Devm.getStor sf sevm.currentTarget) ∧ ∃ b, ((b :: xs) <<+ sf.stack) := by
  rcases h_run with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, Except.assert] at h_run
  -- pop gas
  rcases eq1 : Devm.pop s with _ | ⟨gas1, devm1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e1 := (Devm.pop_of_pop eq1).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  rw [pref_head_unique hp (pref_append [gas1] devm1.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  -- pop callee
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;> simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have e2 := (Devm.pop_of_pop h_pop2).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  rw [pref_head_unique hp (pref_append [x2] devm2.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  -- pop value
  rcases eq3 : Devm.pop devm2 with _ | ⟨value, devm3⟩ <;> simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e3 := (Devm.pop_of_pop eq3).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rw [e3] at hp
  rw [pref_head_unique hp (pref_append [value] devm3.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  -- pop the four indices/sizes
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputIndex, devm4⟩ <;> simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat eq4 with ⟨x4, h_pop4⟩
  have e4 := h_pop4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  rw [e4] at hp
  rw [pref_head_unique hp (pref_append [x4] devm4.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩ <;> simp only [eq5] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat eq5 with ⟨x5, h_pop5⟩
  have e5 := h_pop5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e5
  rw [e5] at hp
  rw [pref_head_unique hp (pref_append [x5] devm5.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputIndex, devm6⟩ <;> simp only [eq6] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat eq6 with ⟨x6, h_pop6⟩
  have e6 := h_pop6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e6
  rw [e6] at hp
  rw [pref_head_unique hp (pref_append [x6] devm6.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  rcases eq7 : Devm.popToNat devm6 with _ | ⟨outputSize, devm7⟩ <;> simp only [eq7] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat eq7 with ⟨x7, h_pop7⟩
  have e7 := h_pop7.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e7
  rw [e7] at hp
  rw [pref_head_unique hp (pref_append [x7] devm7.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  -- state is unchanged by the seven pops
  have h_st7 : s.state = devm7.state :=
    ((Devm.pop_of_pop eq1).state).trans
      (((Devm.pop_of_pop h_pop2).state).trans
        (((Devm.pop_of_pop eq3).state).trans
          ((h_pop4.state).trans
            ((h_pop5.state).trans ((h_pop6.state).trans h_pop7.state)))))
  clear e1 e2 e3 e4 e5 e6 e7 eq1 eq2 eq3 eq4 eq5 eq6 eq7 h_pop2 h_pop4 h_pop5 h_pop6 h_pop7
  -- delegation resolution
  rcases hp11 : accessDelegation (addAccessedAddress devm7 callee) callee with
    ⟨dp, na, code0, dagc, devm9⟩
  simp only [hp11] at h_run
  have h_code0 :
      code0 = (accessDelegation (addAccessedAddress devm7 callee) callee).2.2.1 := by
    rw [hp11]
  have h_st9 : devm9.state = devm7.state := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
    dsimp at h
    rw [← h, accessDelegation_state]
    rfl
  have h_stk9 : devm9.stack = devm7.stack := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).stack) hp11
    dsimp at h
    rw [← h, accessDelegation_stack]
    rfl
  -- charge the call gas
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i devm10 eq16
  have h_st10 : devm9.state = devm10.state := (Devm.burn_of_chargeGas eq16).state
  have h_stk10 : devm9.stack = devm10.stack := (Devm.burn_of_chargeGas eq16).stack
  have h_st11 :
      (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = s.state := by
    show devm10.state = s.state
    rw [← h_st10, h_st9, ← h_st7]
  have h_stk11 :
      (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).stack
        = devm7.stack := by
    show devm10.stack = devm7.stack
    rw [← h_stk10, h_stk9]
  have h_st_devm7 : devm7.state = s.state := h_st7.symm
  clear h_st10 h_st9 h_stk10 h_stk9 eq16 h_st7
  -- static-context assertion
  split at h_run
  case h_1 => cases XStep.run_ofExcept_error h_run
  case h_2 =>
  split at h_run
  · -- insufficient balance : call fails, state unchanged
    split at h_run
    case h_1 => cases XStep.run_ofExcept_error h_run
    case h_2 =>
    rename_i devm12 eq20
    have h_ex := Except.ok.inj h_run.2
    rw [h_ex]
    constructor
    · rw [getStor_eq_of_state_eq (show ((devm12.withReturnData []).withGasLeft _).state
        = s.state by
          show devm12.state = s.state
          rw [← (Devm.push_of_push eq20).state]; exact h_st11)]
      exact h_cons
    · refine ⟨0, ?_⟩
      have h_stk := (Devm.push_of_push eq20).stack
      show (0 :: xs) <<+ ((devm12.withReturnData []).withGasLeft _).stack
      show (0 :: xs) <<+ devm12.stack
      rw [h_stk, h_stk11]
      exact pref_cons hp
  · -- balance is sufficient : the call goes through
    simp only [genericCall.step] at h_run
    split at h_run
    · -- depth limit reached : call fails, state unchanged
      simp only [Bind.bind, Except.bind] at h_run
      split at h_run
      case h_1 => cases XStep.run_ofExcept_error h_run
      case h_2 =>
      rename_i devm12 h_push
      have h_ex := Except.ok.inj h_run.2
      rw [h_ex]
      constructor
      · rw [getStor_eq_of_state_eq (show devm12.state = s.state by
          rw [← (Devm.push_of_push h_push).state]; exact h_st11)]
        exact h_cons
      · refine ⟨0, ?_⟩
        have h_stk := (Devm.push_of_push h_push).stack
        show (0 :: xs) <<+ devm12.stack
        rw [h_stk]
        show (0 :: xs) <<+ 0 ::
          ((devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).withReturnData
            []).stack
        rw [show ((devm10.memExtends [(inputIndex, inputSize),
          (outputIndex, outputSize)]).withReturnData []).stack
          = devm7.stack from h_stk11]
        exact pref_cons hp
    · -- the call is executed
      rename_i h_depth_ne
      simp only [XStep.Run] at h_run
      rcases h_run with ⟨ex', run_pm₀, h_split⟩
      -- name the child message and keep only the projections we need
      obtain ⟨childMsg, run_pm, hc_stv, hc_state, hc_caller, hc_value, hc_ct,
          hc_ca, hc_code, hc_depth⟩ :
          ∃ m : Msg, ProcessMessage m xl ex' ∧
            m.shouldTransferValue = true ∧ m.benv.state = s.state ∧
            m.caller = sevm.currentTarget ∧ m.value = value ∧
            m.currentTarget = callee ∧ m.codeAddress = some na ∧
            m.code = code0 ∧ m.depth = sevm.depth - 1 :=
        ⟨_, run_pm₀, rfl, h_st11, rfl, rfl, rfl, rfl, rfl, rfl⟩
      clear run_pm₀
      -- the sub-message result must be ok
      rcases ex' with err' | child
      · cases Resume.call_run_error h_split.symm
      have h_sf_state : sf.state = child.state := Resume.call_state h_split.symm
      rcases Resume.call_stack h_split.symm with ⟨b, h_sf_stack⟩
      -- the stack conclusion, once and for all: the resume pushes one flag on
      -- the parent's stack, which still carries `xs`
      have h_stack_out : ∃ b', (b' :: xs) <<+ sf.stack := by
        refine ⟨b, ?_⟩
        rw [h_sf_stack]
        show (b :: xs) <<+ b ::
          ((devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).withReturnData
            []).stack
        rw [show ((devm10.memExtends [(inputIndex, inputSize),
          (outputIndex, outputSize)]).withReturnData []).stack
          = devm7.stack from h_stk11]
        exact pref_cons hp
      refine ⟨?_, h_stack_out⟩
      -- unpack the process-message run
      obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp run_pm
      unfold FrameBody at hbody
      rcases eq_bt : childMsg.benvAfterTransfer with e | benv' <;>
        rw [eq_bt] at hbody
      · rw [hbody.2, processMessage.settle_error] at hset
        cases hset
      have run_ec : ExecuteCode (childMsg.withBenv benv') xl r0 := hbody
      -- the value transfer performed before the sub-message run
      rcases of_benvAfterTransfer hc_stv eq_bt with ⟨st_mid, h_sub, hB⟩
      rw [hc_state, hc_caller, hc_value] at h_sub
      rcases of_state_transfer_fields (callee := callee) h_sub with
        ⟨h_t_stor, h_t_code, -, -, -⟩
      have hBs : benv'.state = st_mid.addBal callee value := by
        rw [hB, hc_ct, hc_value]; rfl
      -- resolve the inner split : either rollback or a clean sub-message result
      obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
      subst h_r0
      rcases h_settle with ⟨h_err2, h_if⟩ | ⟨h_err2, h_if⟩
      · -- sub-message failed : state rolled back to the pre-transfer state
        rw [getStor_eq_of_state_eq (show sf.state = s.state by
          rw [h_sf_state, ← h_if]; exact hc_state)]
        exact h_cons
      -- sub-message succeeded
      have h_if' := h_if.symm
      subst h_if'
      have h_wb_ca : (childMsg.withBenv benv').codeAddress = some na := hc_ca
      rcases of_executeCode_someCode h_wb_ca run_ec with
        ⟨h_prec, h_xl_none, h_he⟩ | ⟨h_prec, ex''', h_xl_some, h_he⟩
      · -- callee is a precompile : no sub-execution, only the transfer
        have h_child_state : child.state = benv'.state := by
          have h := state_of_executePrecomp_ok h_he h_err2
          rw [h]; rfl
        have h_stor_eq : Devm.getStor sf sevm.currentTarget
            = Devm.getStor s sevm.currentTarget := by
          show (sf.state.get sevm.currentTarget).stor = (s.state.get sevm.currentTarget).stor
          rw [h_sf_state, h_child_state, hBs]
          exact h_t_stor sevm.currentTarget
        rw [h_stor_eq]
        exact h_cons
      · -- callee is a regular account : a sub-execution takes place
        rw [h_xl_some] at h_fill
        dsimp only [Xlot.Filled] at h_fill
        rcases ex''' with ⟨err3, d3⟩ | child3
        · -- sub-execution error : contradicts the clean sub-message result
          rcases of_handleError_err h_he with ⟨evm4, h_ok4, h_some4, -⟩ | ⟨e, h_err4⟩
          · have h_ok4 := Except.ok.inj h_ok4
            rw [← h_ok4] at h_some4
            exact absurd h_some4 h_err2
          · cases h_err4
        -- clean sub-execution : apply the induction hypothesis
        simp only [executeCode.handleError] at h_he
        have h_he := (Except.ok.inj h_he).symm
        subst h_he
        obtain ⟨ex_sub⟩ := h_fill
        -- projections of the sub-message's initial sevm/devm
        have h_sd_state : (initDevm (childMsg.withBenv benv')).state = benv'.state := rfl
        have h_ss_ct : (initSevm (childMsg.withBenv benv')).currentTarget = callee := hc_ct
        -- code at the contract's address is the fmint code
        have h_code_at :
            some ((initDevm (childMsg.withBenv benv')).getCode sevm.currentTarget).toList
              = Prog.compile p := by
          show some ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).code.toList
            = Prog.compile p
          rw [h_sd_state, hBs, h_t_code sevm.currentTarget]
          exact h_code
        -- the target program invariant for the sub-execution
        have h_at : Prog.At p sevm.currentTarget 0
            (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv')) := by
          refine ⟨h_code_at, ?_⟩
          intro h_eq_ct
          rw [h_ss_ct] at h_eq_ct
          refine ⟨?_, rfl⟩
          show some (initSevm (childMsg.withBenv benv')).code.toList = Prog.compile p
          have h_code_c : (initSevm (childMsg.withBenv benv')).code = code0 := hc_code
          rw [h_code_c, h_code0]
          have h_ad : (addAccessedAddress devm7 callee).state.getCode callee
              = s.getCode sevm.currentTarget := by
            show devm7.state.getCode callee = s.getCode sevm.currentTarget
            rw [h_st_devm7, h_eq_ct]; rfl
          have h_notdel : ¬ isValidDelegation
              ((addAccessedAddress devm7 callee).state.getCode callee) := by
            rw [h_ad]; exact not_delegation_of_compile h_code
          rw [accessDelegation_code_of_not h_notdel, h_ad]
          exact h_code
        -- the depth of the sub-execution is strictly smaller
        have h_depth_lt : (initSevm (childMsg.withBenv benv')).depth < sevm.depth := by
          have h_dep : (initSevm (childMsg.withBenv benv')).depth = sevm.depth - 1 := hc_depth
          rw [h_dep]; omega
        -- the precondition holds for the sub-message
        have h_gs : Devm.getStor (initDevm (childMsg.withBenv benv')) sevm.currentTarget
            = Devm.getStor s sevm.currentTarget := by
          show ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).stor
            = (s.state.get sevm.currentTarget).stor
          rw [h_sd_state, hBs]
          exact h_t_stor sevm.currentTarget
        have h_precond : (ContractSpec.ofStorageOnly p P).Pre sevm.currentTarget
            (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv')) := by
          refine ⟨h_code_at, trivial, ?_⟩
          apply ContractSpec.ofStorageOnly_preInv_iff.mpr
          rw [h_gs]
          exact h_cons
        -- apply the induction hypothesis
        have hpost : (ContractSpec.ofStorageOnly p P).Post sevm.currentTarget
            (initSevm (childMsg.withBenv benv')) child :=
          ih 0 (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv'))
            (.ok child) ex_sub h_depth_lt h_at ⟨h_precond, fun _ => Mem.wf_empty⟩
        have h_post_cons : P (Devm.getStor child sevm.currentTarget) :=
          ContractSpec.ofStorageOnly_postInv_iff.mp hpost.inv
        rw [getStor_eq_of_state_eq h_sf_state sevm.currentTarget]
        exact h_post_cons

end ChildCall

end Blanc
