import Blanc.Ladder

/-!
# Contract preservation over certified code semantics

This module is the sem-parametric counterpart of the ordinary contract
ladder.  The original `ContractSpec` remains in `Ladder.lean`; this namespace
uses the same invariant and balance slots with a `CodeSem` in place of a
source `Prog`.
-/

namespace Blanc

open Jaune

/-- A contract specification whose executable code is supplied by a certified
code semantics rather than by `Prog.compile`. -/
structure ContractSpecSem where
  sem : CodeSem
  Inv : Stor → B256 → B256 → Prop
  Side : (Adr → B256) → Prop
  inv_forget : ∀ {s : Stor} {v b : B256}, Inv s v b → Inv s 0 b
  inv_mono : ∀ {s : Stor} {v b b' : B256},
    Inv s v b → b.toNat ≤ b'.toNat → Inv s v b'
  inv_recv : ∀ {s : Stor} {v b b' : B256},
    Inv s 0 b → b'.toNat = b.toNat + v.toNat → Inv s v b'
  side_le : ∀ {f g : Adr → B256}, Side f → sum g ≤ sum f → Side g
  side_transfer : ∀ {st st' : Jaune.State} {caller callee : Adr} {wad : B256},
    st.subBal caller wad = some st' → Side st.bal →
    Side (st'.addBal callee wad).bal
  side_addBal : ∀ {w : Jaune.State} {a : Adr} {val : B256},
    sum w.bal + val.toNat < 2 ^ 256 → Side w.bal →
    Side (w.addBal a val).bal
  inv_transfer : ∀ {st st' : Jaune.State} {caller callee ca : Adr}
      {wad v : B256},
    st.subBal caller wad = some st' → caller ≠ ca → Side st.bal →
    Inv (st.getStor ca) v (st.bal ca) →
    Inv ((st'.addBal callee wad).getStor ca)
      v ((st'.addBal callee wad).bal ca)
  inv_recv_transfer : ∀ {st st' : Jaune.State} {caller ca : Adr} {wad : B256},
    st.subBal caller wad = some st' → caller ≠ ca → Side st.bal →
    Inv (st.getStor ca) 0 (st.bal ca) →
    Inv ((st'.addBal ca wad).getStor ca)
      wad ((st'.addBal ca wad).bal ca)
  inv_addBal : ∀ {w : Jaune.State} {ca a : Adr} {val v : B256},
    sum w.bal + val.toNat < 2 ^ 256 → Side w.bal →
    Inv (w.getStor ca) v (w.bal ca) →
    Inv ((w.addBal a val).getStor ca) v ((w.addBal a val).bal ca)

lemma code_eq_of_exec_sem {sem : CodeSem} {sevm' : Sevm} {devm' child : Devm}
    {wa : Adr}
    (ex_sub : Exec 0 sevm' devm' (.ok child))
    (h_code : some (devm'.getCode wa).toList = sem.image) :
    child.getCode wa = devm'.getCode wa := by
  have h_ne : (devm'.getCode wa).toList ≠ [] := by
    intro h_nil
    apply sem.ne_nil
    rw [← h_code, h_nil]
    rfl
  exact Exec.preserves_getCode ex_sub wa h_ne

namespace ContractSpecSem

variable (c : ContractSpecSem)

def PreInv (devm : Devm) (ca : Adr) (sevm : Sevm) : Prop :=
  (sevm.currentTarget = ca → c.Inv (Devm.getStor devm ca) sevm.value (devm.getBal ca)) ∧
  (sevm.currentTarget ≠ ca → c.Inv (Devm.getStor devm ca) 0 (devm.getBal ca))

def PostInv (devm : Devm) (ca : Adr) : Prop :=
  c.Inv (Devm.getStor devm ca) 0 (devm.getBal ca)

structure Pre (ca : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  code : some (devm.getCode ca).toList = c.sem.image
  side : c.Side devm.getBal
  inv : c.PreInv devm ca sevm

structure PreWf (ca : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  pre : c.Pre ca sevm devm
  wf : sevm.currentTarget = ca → Mem.Wf devm.memory

structure Post (ca : Adr) (_sevm : Sevm) (devm : Devm) : Prop where
  side : c.Side devm.getBal
  inv : c.PostInv devm ca

structure StateInv (ca : Adr) (w : Jaune.State) : Prop where
  code : some (w.getCode ca).toList = c.sem.image
  side : c.Side w.bal
  inv : c.Inv (w.getStor ca) 0 (w.bal ca)

def Sound (c : ContractSpecSem) (ca : Adr) : Prop :=
  ∀ {sevm pre post},
    CoveredFork sevm.benvStat.fork →
    c.sem.Run sevm pre post →
    sevm.currentTarget = ca →
    ( ∀ pc' sevm' pre' post',
        Exec pc' sevm' pre' (.ok post') →
        sevm'.depth < sevm.depth →
        CodeSem.At c.sem ca pc' sevm' pre' →
        CoveredFork sevm'.benvStat.fork →
        c.PreWf ca sevm' pre' →
        c.Post ca sevm' post' ) →
    Mem.Wf pre.memory →
    c.Pre ca sevm pre →
    c.Post ca sevm post

def SoundNoMem (c : ContractSpecSem) (ca : Adr) : Prop :=
  ∀ {sevm pre post},
    CoveredFork sevm.benvStat.fork →
    c.sem.Run sevm pre post →
    sevm.currentTarget = ca →
    ( ∀ pc' sevm' pre' post',
        Exec pc' sevm' pre' (.ok post') →
        sevm'.depth < sevm.depth →
        CodeSem.At c.sem ca pc' sevm' pre' →
        CoveredFork sevm'.benvStat.fork →
        c.PreWf ca sevm' pre' →
        c.Post ca sevm' post' ) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

def SoundWith (c : ContractSpecSem) (ca : Adr) (mw : Mem → Prop) : Prop :=
  ∀ {sevm pre post},
    CoveredFork sevm.benvStat.fork →
    c.sem.Run sevm pre post →
    sevm.currentTarget = ca →
    ( ∀ pc' sevm' pre' post',
        Exec pc' sevm' pre' (.ok post') →
        sevm'.depth < sevm.depth →
        CodeSem.At c.sem ca pc' sevm' pre' →
        CoveredFork sevm'.benvStat.fork →
        c.PreWf ca sevm' pre' →
        c.Post ca sevm' post' ) →
    mw pre.memory →
    c.Pre ca sevm pre →
    c.Post ca sevm post

def Preserves (c : ContractSpecSem) (ca : Adr) : Prop :=
  ∀ sevm pre post,
    CoveredFork sevm.benvStat.fork →
    Exec 0 sevm pre (.ok post) →
    (sevm.currentTarget = ca → some sevm.code.toList = c.sem.image) →
    (sevm.currentTarget = ca → Mem.Wf pre.memory) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

def PreservesNoMem (c : ContractSpecSem) (ca : Adr) : Prop :=
  ∀ sevm pre post,
    CoveredFork sevm.benvStat.fork →
    Exec 0 sevm pre (.ok post) →
    (sevm.currentTarget = ca → some sevm.code.toList = c.sem.image) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

theorem SoundNoMem.sound {c : ContractSpecSem} {ca : Adr}
    (h : c.SoundNoMem ca) : c.Sound ca :=
  fun hfork h_run h_ca h_ih _ h_pre => h hfork h_run h_ca h_ih h_pre

theorem SoundWith.soundNoMem {c : ContractSpecSem} {ca : Adr}
    (h : c.SoundWith ca (fun _ => True)) : c.SoundNoMem ca :=
  fun hfork h_run h_ca h_ih h_pre => h hfork h_run h_ca h_ih trivial h_pre

theorem PreservesNoMem.preserves {c : ContractSpecSem} {ca : Adr}
    (h : c.PreservesNoMem ca) : c.Preserves ca :=
  fun sevm pre post hfork exc h_code _ h_pre =>
    h sevm pre post hfork exc h_code h_pre

variable {c : ContractSpecSem}

/-- Once the frame has terminated the callvalue is no longer in flight.  This
is the `inv_forget` slot and nothing else. -/
lemma post_of_pre {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h : c.Pre ca sevm devm) : c.Post ca sevm devm := by
  refine ⟨h.side, ?_⟩
  by_cases hc : sevm.currentTarget = ca
  · exact c.inv_forget (h.inv.left hc)
  · exact h.inv.right hc

/-- A frame postcondition depends only on persistent world state. -/
lemma Post.of_state_eq {ca : Adr} {sevm sevm' : Sevm} {child post : Devm}
    (h : c.Post ca sevm' child) (hstate : post.state = child.state) :
    c.Post ca sevm post := by
  refine ⟨?_, ?_⟩
  · have hbal : post.getBal = child.getBal :=
      funext (getBal_eq_of_state_eq hstate)
    rw [hbal]
    exact h.side
  · show c.Inv (Devm.getStor post ca) 0 (post.getBal ca)
    rw [getStor_eq_of_state_eq hstate ca, getBal_eq_of_state_eq hstate ca]
    exact h.inv

lemma Pre.state_eq {wa sevm devm devm'}
    (h_pc : c.Pre wa sevm devm) (h_eq : devm'.state = devm.state) :
    c.Pre wa sevm devm' := by
  cases h_pc with
  | mk h_code h_nof h_solv =>
    have h_bal : devm'.getBal = devm.getBal := by
      funext a; simp [Devm.getBal, Devm.getAcct]; rw [h_eq]
    have h_stor : ∀ a, Devm.getStor devm' a = Devm.getStor devm a := by
      intro a; simp [Devm.getStor, Devm.getAcct]; rw [h_eq]
    constructor
    · have h_gc : devm'.getCode wa = devm.getCode wa := by
        simp [Devm.getCode, Devm.getAcct]; rw [h_eq]
      rw [h_gc]; exact h_code
    · rw [h_bal]; exact h_nof
    · cases h_solv with
      | intro hl hr =>
        constructor
        · intro h; rw [h_bal, h_stor wa]; exact hl h
        · intro h; rw [h_bal, h_stor wa]; exact hr h

lemma Pre.of_eqs {wa : Adr} {sevm : Sevm} {pre inter : Devm}
    (h_pc : c.Pre wa sevm pre)
    (h_code : inter.getCode wa = pre.getCode wa)
    (h_bal : inter.getBal = pre.getBal)
    (h_stor : Devm.getStor inter wa = Devm.getStor pre wa) :
    c.Pre wa sevm inter := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_code]; exact h_pc.code
  · rw [h_bal]; exact h_pc.side
  · intro h; rw [h_bal, h_stor]; exact h_pc.inv.left h
  · intro h; rw [h_bal, h_stor]; exact h_pc.inv.right h

/-- The precondition survives a value transfer that does not debit the
contract.  Slots: `side_transfer` and `inv_transfer`. -/
lemma Pre.transfer_state {ca : Adr} {sevm : Sevm} {pre inter : Devm}
    {caller callee : Adr} {wad : B256} {st_mid : Jaune.State}
    (h_pc : c.Pre ca sevm pre)
    (h_ne : caller ≠ ca)
    (h_sub : pre.state.subBal caller wad = some st_mid)
    (h_state : inter.state = st_mid.addBal callee wad) :
    c.Pre ca sevm inter := by
  rcases of_state_transfer_fields (callee := callee) h_sub with ⟨h_t_stor, h_t_code, -, -, -⟩
  have h_stor_eq : Devm.getStor inter ca = (st_mid.addBal callee wad).getStor ca := by
    show (inter.state.get ca).stor = _
    rw [h_state]; rfl
  have h_bal_eq : inter.getBal ca = (st_mid.addBal callee wad).bal ca := by
    show (inter.state.get ca).bal = _
    rw [h_state]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (inter.state.get ca).code.toList = _
    rw [h_state, h_t_code ca]; exact h_pc.code
  · show c.Side inter.state.bal
    rw [h_state]; exact c.side_transfer h_sub h_pc.side
  · intro h
    show c.Inv (Devm.getStor inter ca) sevm.value (inter.getBal ca)
    rw [h_stor_eq, h_bal_eq]
    exact c.inv_transfer h_sub h_ne h_pc.side (h_pc.inv.left h)
  · intro h
    show c.Inv (Devm.getStor inter ca) 0 (inter.getBal ca)
    rw [h_stor_eq, h_bal_eq]
    exact c.inv_transfer h_sub h_ne h_pc.side (h_pc.inv.right h)

lemma GenericCall.none_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_run : GenericCall sevm devm gas value caller target codeAddress stv
      isStatic ii is oi os code dp .none (.ok inter))
    (h_ne : stv = true → caller ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa sevm inter := by
  unfold GenericCall genericCall.step at h_run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  -- depth-zero early exit, push failed
  · cases h_run.2
  -- depth-zero early exit, push succeeded
  · rename_i h_push
    apply h_pc.state_eq
    rw [Except.ok.inj h_run.2, ← (Devm.push_of_push h_push).state]
    rfl
  -- a child frame was entered, but it settled without a sub-derivation
  · obtain ⟨r, hframe, hres⟩ := h_run
    obtain ⟨childMsg, hframe, hc_state, hc_stv, hc_caller, hc_value, hc_ct,
        hc_ca⟩ :
        ∃ m : Msg, ProcessMessage m .none r ∧
          m.benv.state = devm.state ∧ m.shouldTransferValue = stv ∧
          m.caller = caller ∧ m.value = value ∧ m.currentTarget = target ∧
          m.codeAddress = some codeAddress :=
      ⟨_, hframe, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rcases r with err | child
    · cases Resume.call_run_error hres.symm
    have h_inter_state : inter.state = child.state := Resume.call_state hres.symm
    obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hframe
    unfold FrameBody at hbody
    rcases eq_bt : childMsg.benvAfterTransfer with e | benv <;> rw [eq_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset
      cases hset
    have run_ec : ExecuteCode (childMsg.withBenv benv) .none r0 := hbody
    obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
    subst h_r0
    rcases h_settle with ⟨h_err2, h_child⟩ | ⟨h_err2, h_child⟩
    · apply h_pc.state_eq
      rw [h_inter_state, ← h_child]
      show childMsg.benv.state = devm.state
      exact hc_state
    · subst h_child
      have hc_ca2 : (childMsg.withBenv benv).codeAddress = some codeAddress := hc_ca
      rcases of_executeCode_someCode hc_ca2 run_ec with
        ⟨_, _, h_he⟩ | ⟨_, exn, h_xl_some, _⟩
      · have h_child_state : evm2.state = benv.state := by
          have h := state_of_executePrecomp_ok h_he h_err2
          rw [h]; rfl
        by_cases h_stv : stv = true
        · rcases of_benvAfterTransfer (hc_stv.trans h_stv) eq_bt with ⟨st_mid, h_sub, hB⟩
          rw [hc_state, hc_caller, hc_value] at h_sub
          have hBs : benv.state = st_mid.addBal target value := by
            rw [hB, hc_ct, hc_value]; rfl
          have h_state : inter.state = st_mid.addBal target value := by
            rw [h_inter_state, h_child_state, hBs]
          exact Pre.transfer_state h_pc (h_ne h_stv) h_sub h_state
        · have h_stv2 : ¬ childMsg.shouldTransferValue = true := by
            rw [hc_stv]; exact h_stv
          have h_benv : benv = childMsg.benv := of_benvAfterTransfer_no h_stv2 eq_bt
          apply h_pc.state_eq
          rw [h_inter_state, h_child_state, h_benv]
          exact hc_state
      · cases h_xl_some

lemma GenericCreate.none_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {endowment : B256} {newAddress : Adr} {memoryIndex memorySize : Nat}
    (h_run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize
      .none (.ok inter))
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa sevm inter := by
  unfold GenericCreate genericCreate.step at h_run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, Pure.pure,
    Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  -- init-code-size assertion failed
  · cases h_run.2
  -- static-context assertion failed
  · cases h_run.2
  -- balance / max-nonce / depth-zero early exit, push failed
  · cases h_run.2
  -- balance / max-nonce / depth-zero early exit, push succeeded
  · rename_i h_push
    apply h_pc.state_eq
    rw [Except.ok.inj h_run.2, ← (Devm.push_of_push h_push).state]
    rfl
  -- address-collision early exit, push failed
  · cases h_run.2
  -- address-collision early exit, push succeeded
  · rename_i h_push
    have h_state : inter.state = devm.state.incrNonce sevm.currentTarget := by
      rw [Except.ok.inj h_run.2, ← (Devm.push_of_push h_push).state]
      rfl
    refine Pre.of_eqs h_pc ?_ ?_ ?_
    · show (inter.state.get wa).code = (devm.state.get wa).code
      rw [h_state]
      exact State.incrNonce_get_code
    · funext b
      show (inter.state.get b).bal = (devm.state.get b).bal
      rw [h_state]
      exact State.incrNonce_get_bal
    · show (inter.state.get wa).stor = (devm.state.get wa).stor
      rw [h_state]
      exact State.incrNonce_get_stor
  -- a child frame was entered : impossible with an empty slot, since a create
  -- frame always runs interpreted code
  · exfalso
    obtain ⟨r, hframe, hres⟩ := h_run
    obtain ⟨childMsg, hframe, hc_ca⟩ :
        ∃ m : Msg, ProcessCreateMessage m .none r ∧ m.codeAddress = .none :=
      ⟨_, hframe, rfl⟩
    obtain ⟨r1, hpm, hset⟩ := ProcessCreateMessage.iff_processMessage.mp hframe
    obtain ⟨r0, hbody, hset1⟩ := ProcessMessage.iff_body.mp hpm
    unfold FrameBody at hbody
    rcases eq_bt : (processCreateMessage.msg childMsg).benvAfterTransfer with e | benv <;>
      rw [eq_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset1
      rw [hset1, processCreateMessage.settle_error] at hset
      rw [hset] at hres
      exact Resume.create_run_error hres.symm
    · have hca :
        ((processCreateMessage.msg childMsg).withBenv benv).codeAddress = .none := hc_ca
      obtain ⟨exn, h_xl, -⟩ := of_executeCode_noneCode hca hbody
      cases h_xl

lemma Xinst.none_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm} {x : Xinst}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_run : Xinst.Run sevm devm x .none (.ok inter))
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa sevm inter := by
  unfold Xinst.Run at h_run
  rcases Xinst.step_shapeCovered sevm devm x hfork with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, hcal, -, hs⟩ <;> rw [hs] at h_run
  · obtain ⟨-, hex⟩ := h_run
    rw [← hex] at hframe
    have hif : Devm.InstructionFrame devm inter := hframe
    exact h_pc.state_eq hif.state.symm
  · exact GenericCreate.none_preserves_precond h_run (h_pc.state_eq hf.state.symm)
  · refine GenericCall.none_preserves_precond h_run ?_ (h_pc.state_eq hf.state.symm)
    rintro hstv
    rcases hcal with ⟨-, rfl⟩ | ⟨hsf, -⟩
    · exact h_ne
    · rw [hsf] at hstv; cases hstv

/-- A successful nonrecursive instruction in a foreign frame preserves the
contract precondition.  This packages the register/push/executable split used
by proof-indexed interpreter recursions. -/
lemma Ninst.none_preserves_precond
    {wa : Adr} {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst}
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (target_ne : sevm.currentTarget ≠ wa)
    (precondition : c.Pre wa sevm pre) :
    c.Pre wa sevm inter := by
  cases n with
  | push xs le =>
      have hrun := (Step.run_ofExecution (xl := (.none : Xlot))).mp run
      rcases Except.bind_eq_ok hrun.2.symm with
        ⟨charged, charge, pushed⟩
      exact precondition.state_eq
        (((Devm.burn_of_chargeGas charge).state).trans
          ((Devm.push_of_push pushed).state)).symm
  | dupn imm =>
    have frame := Ninst.dupn_instructionFrame_effectRec
      (xl := .none) trivial run
    exact precondition.state_eq frame.state.symm
  | swapn imm =>
    have frame := Ninst.swapn_instructionFrame_effectRec
      (xl := .none) trivial run
    exact precondition.state_eq frame.state.symm
  | exchange imm =>
    have frame := Ninst.exchange_instructionFrame_effectRec
      (xl := .none) trivial run
    exact precondition.state_eq frame.state.symm
  | reg r =>
      have registerRun : Rinst.run ⟨pc, sevm, pre⟩ r = .ok inter := by
        exact ((Step.run_ofExecution (xl := (.none : Xlot))).mp run).2.symm
      by_cases store : r = Rinst.sstore
      · subst store
        have frame := Rinst.sstore_run_stateWriteFrame pc pre sevm
        rw [registerRun] at frame
        refine Pre.of_eqs precondition (frame.getCode_eq wa).symm ?_
          (sstore_preserves_getStor_ne registerRun target_ne)
        funext address
        exact (frame.getBal_eq address).symm
      · exact Pre.of_eqs precondition
          (Rinst.preserves_getCode registerRun wa)
          (Rinst.preserves_bal registerRun).symm
          (congrFun (Rinst.preserves_stor store registerRun) wa).symm
  | exec x =>
      apply Xinst.none_preserves_precond (x := x) hfork _ target_ne precondition
      exact XStep.run_toStep.mp run



-- the precondition carries over to the initial state of a sub-execution

-- the precondition carries over to the initial state of a sub-execution
-- started after a balance transfer from a sender that is not the contract
lemma Pre.child_of_transfer {ca : Adr} {sevm sevm' : Sevm} {devm devm' : Devm}
    {st st_mid : Jaune.State} {caller target : Adr} {value : B256}
    (h_pc : c.Pre ca sevm devm)
    (h_ct_ne : sevm.currentTarget ≠ ca)
    (h_ne : caller ≠ ca)
    (h_stor : (st.get ca).stor = (devm.state.get ca).stor)
    (h_code : (st.get ca).code = (devm.state.get ca).code)
    (h_bal : ∀ a, (st.get a).bal = (devm.state.get a).bal)
    (h_sub : st.subBal caller value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct' : sevm'.currentTarget = target)
    (h_val : sevm'.currentTarget = ca → sevm'.value = value) :
    c.Pre ca sevm' devm' := by
  have h_bal_st : st.bal = devm.getBal := by funext a; exact h_bal a
  have h_side_st : c.Side st.bal := by rw [h_bal_st]; exact h_pc.side
  rcases of_state_transfer_fields (callee := target) h_sub with
    ⟨h_t_stor, h_t_code, _, _, _⟩
  have h_inv_st : c.Inv (st.getStor ca) 0 (st.bal ca) := by
    show c.Inv (st.get ca).stor 0 (st.get ca).bal
    rw [h_stor, h_bal ca]
    exact h_pc.inv.right h_ct_ne
  have h_stor' : Devm.getStor devm' ca = (st_mid.addBal target value).getStor ca := by
    show (devm'.state.get ca).stor = _
    rw [h_state]; rfl
  have h_bal' : devm'.getBal ca = (st_mid.addBal target value).bal ca := by
    show (devm'.state.get ca).bal = _
    rw [h_state]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (devm'.state.get ca).code.toList = _
    rw [h_state, h_t_code ca, h_code]; exact h_pc.code
  · show c.Side devm'.state.bal
    rw [h_state]; exact c.side_transfer h_sub h_side_st
  · intro h_eq
    have h_t_ca : target = ca := h_ct'.symm.trans h_eq
    subst h_t_ca
    show c.Inv (Devm.getStor devm' target) sevm'.value (devm'.getBal target)
    rw [h_stor', h_bal', h_val h_eq]
    exact c.inv_recv_transfer h_sub h_ne h_side_st h_inv_st
  · intro h_ne_ct
    have h_t_ne : target ≠ ca := fun hc => h_ne_ct (h_ct'.trans hc)
    show c.Inv (Devm.getStor devm' ca) 0 (devm'.getBal ca)
    rw [h_stor', h_bal']
    exact c.inv_transfer h_sub h_ne h_side_st h_inv_st

/-- The child-frame precondition after an outbound value transfer from the
contract.  The caller supplies the invariant at the debited balance; the
contract record's receive law covers the self-call case. -/
lemma Pre.child_of_outbound_transfer
    {ca target : Adr} {sevm' : Sevm} {devm' : Devm}
    {st st_mid : Jaune.State} {value : B256}
    (h_code : some (st.getCode ca).toList = c.sem.image)
    (h_side : c.Side st.bal)
    (h_inv : c.Inv (st.getStor ca) 0 (st.bal ca - value))
    (h_sub : st.subBal ca value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct : sevm'.currentTarget = target)
    (h_value : sevm'.value = value) :
    c.Pre ca sevm' devm' := by
  rcases of_state_transfer_fields (callee := target) h_sub with
    ⟨h_t_stor, h_t_code, h_le, h_t_self, h_t_ne⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (devm'.state.get ca).code.toList = c.sem.image
    rw [h_state, h_t_code ca]
    exact h_code
  · show c.Side devm'.state.bal
    rw [h_state]
    exact c.side_transfer h_sub h_side
  · intro h_target
    have h_target' : target = ca := h_ct.symm.trans h_target
    have hbal : ((st_mid.addBal target value).get ca).bal =
        (st.get ca).bal := h_t_self h_target'
    show c.Inv (Devm.getStor devm' ca) sevm'.value (devm'.getBal ca)
    change c.Inv (devm'.state.get ca).stor sevm'.value
      (devm'.state.get ca).bal
    rw [h_state, h_value, h_t_stor ca, hbal]
    apply c.inv_recv h_inv
    have h_le_nat := B256.toNat_le_toNat h_le
    change (st.bal ca).toNat = (st.bal ca - value).toNat + value.toNat
    rw [B256.toNat_sub_eq_of_le _ _ h_le]
    omega
  · intro h_target
    have h_target' : target ≠ ca := fun h => h_target (h_ct.trans h)
    have hbal : ((st_mid.addBal target value).get ca).bal =
        (st.get ca).bal - value := h_t_ne h_target'
    show c.Inv (Devm.getStor devm' ca) 0 (devm'.getBal ca)
    change c.Inv (devm'.state.get ca).stor 0 (devm'.state.get ca).bal
    rw [h_state, h_t_stor ca, hbal]
    exact h_inv

-- the precondition carries over to the initial state of a sub-execution
-- started without a balance transfer
lemma Pre.child_of_eqs {wa : Adr} {sevm sevm' : Sevm} {devm devm' : Devm}
    (h_pc : c.Pre wa sevm devm)
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_state : devm'.state = devm.state)
    (h_val : sevm'.currentTarget = wa → sevm'.value = 0) :
    c.Pre wa sevm' devm' := by
  have h_solv := h_pc.inv.right h_ct_ne
  have h_stor' := getStor_eq_of_state_eq h_state wa
  have h_bal' := getBal_eq_of_state_eq h_state wa
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [getCode_eq_of_state_eq h_state wa]; exact h_pc.code
  · have h_bf : devm'.getBal = devm.getBal := funext (getBal_eq_of_state_eq h_state)
    rw [h_bf]; exact h_pc.side
  · intro h_eq; rw [h_val h_eq, h_stor', h_bal']; exact h_solv
  · intro _; rw [h_stor', h_bal']; exact h_solv

-- the precondition is restored after a successful sub-execution whose final
-- state satisfies the postcondition
lemma Pre.of_postcond {wa : Adr} {sevm sevm' : Sevm} {child inter devm' : Devm}
    (h_post : c.Post wa sevm' child)
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_code_pre : some (devm'.getCode wa).toList = c.sem.image)
    (h_code_eq : child.getCode wa = devm'.getCode wa)
    (h_stor : (inter.state.get wa).stor = (child.state.get wa).stor)
    (h_code : (inter.state.get wa).code = (child.state.get wa).code)
    (h_bal : ∀ a, (inter.state.get a).bal = (child.state.get a).bal) :
    c.Pre wa sevm inter := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (inter.state.get wa).code.toList = c.sem.image
    rw [h_code]
    show some (child.getCode wa).toList = c.sem.image
    rw [h_code_eq]
    exact h_code_pre
  · have h_bf : inter.getBal = child.getBal := by
      funext a; exact h_bal a
    rw [h_bf]; exact h_post.side
  · intro h_eq; exact absurd h_eq h_ct_ne
  · intro _
    have h_stor' : Devm.getStor inter wa = Devm.getStor child wa := h_stor
    have h_bal' : inter.getBal wa = child.getBal wa := h_bal wa
    rw [h_stor', h_bal']
    exact h_post.inv

lemma GenericCall.some_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {evm' : Evm} {exn' : Execution}
    (h_run : GenericCall sevm devm gas value caller target codeAddress stv
      isStatic ii is oi os code dp (.some ⟨evm', exn'⟩) (.ok inter))
    (ex_sub : Exec evm'.pc evm'.sta evm'.dyna exn')
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_ne : stv = true → caller ≠ wa)
    (h_tv : stv = false → target = wa → value = 0)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa evm'.sta evm'.dyna ∧
      (ifOk (c.Post wa evm'.sta) exn' → c.Pre wa sevm inter) := by
  unfold GenericCall genericCall.step at h_run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  -- the two depth-zero exits leave the slot empty
  · cases h_run.1
  · cases h_run.1
  -- the child frame was entered
  obtain ⟨r, hframe, hres⟩ := h_run
  obtain ⟨childMsg, hframe, hc_state, hc_stv, hc_caller, hc_value, hc_ct, hc_ca⟩ :
      ∃ m : Msg, ProcessMessage m (.some ⟨evm', exn'⟩) r ∧
        m.benv.state = devm.state ∧ m.shouldTransferValue = stv ∧
        m.caller = caller ∧ m.value = value ∧ m.currentTarget = target ∧
        m.codeAddress = some codeAddress :=
    ⟨_, hframe, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases r with err | child
  · cases Resume.call_run_error hres.symm
  have h_inter_state : inter.state = child.state := Resume.call_state hres.symm
  obtain ⟨henter, hr⟩ := RunFrame.some_inv hframe
  obtain ⟨benv, eq_bt, h_evm⟩ := Frame.enter_run_inv henter
  have hpc0 : evm'.pc = 0 := Frame.enter_run_pc henter
  -- projections of the sub-execution's initial machine
  have h_ds : evm'.dyna.state = benv.state := by rw [h_evm]; rfl
  have h_ct' : evm'.sta.currentTarget = target := by rw [h_evm]; exact hc_ct
  have h_v' : evm'.sta.value = value := by rw [h_evm]; exact hc_value
  -- the frame's settlement, unfolded
  have hr2 : processMessage.settle childMsg
      (executeCode.handleErrorWith childMsg.benv.stat.rules.stateGas exn')
      = .ok child := hr.symm
  rcases h_he : executeCode.handleErrorWith childMsg.benv.stat.rules.stateGas exn'
    with x | evm2
  · rw [h_he, processMessage.settle_error] at hr2
    cases hr2
  rw [h_he] at hr2
  unfold processMessage.settle at hr2
  dsimp only [bind, Except.bind] at hr2
  -- part 1 : the precondition holds for the sub-execution's initial state
  have h_pre1 : c.Pre wa evm'.sta evm'.dyna := by
    by_cases h_stv : stv = true
    · rcases of_benvAfterTransfer (hc_stv.trans h_stv) eq_bt with ⟨st_mid, h_sub, hB⟩
      rw [hc_state, hc_caller, hc_value] at h_sub
      have h_state : evm'.dyna.state = st_mid.addBal target value := by
        rw [h_ds, hB, hc_ct, hc_value]
        rfl
      exact Pre.child_of_transfer h_pc h_ct_ne (h_ne h_stv) rfl rfl (fun _ => rfl)
        h_sub h_state h_ct' (fun _ => h_v')
    · have h_stv2 : ¬ childMsg.shouldTransferValue = true := by rw [hc_stv]; exact h_stv
      have h_benv : benv = childMsg.benv := of_benvAfterTransfer_no h_stv2 eq_bt
      have h_state : evm'.dyna.state = devm.state := by
        rw [h_ds, h_benv]; exact hc_state
      apply Pre.child_of_eqs h_pc h_ct_ne h_state
      intro h_eq
      have h_sf : stv = false := by
        cases stv
        · rfl
        · exact absurd rfl h_stv
      rw [h_v']
      exact h_tv h_sf (h_ct'.symm.trans h_eq)
  refine ⟨h_pre1, ?_⟩
  -- part 2 : the precondition is restored after the call returns
  intro h_ifOk
  rcases exn' with ⟨err3, d3⟩ | child3
  · -- sub-execution ended in error : the parent state is rolled back
    rcases of_handleError_err h_he with ⟨evm2', h_ok2, h_some2, _⟩ | ⟨e, h_err2⟩
    · have h_eq2 : evm2 = evm2' := Except.ok.inj h_ok2
      subst h_eq2
      rw [if_pos h_some2] at hr2
      have h_child := Except.ok.inj hr2
      apply h_pc.state_eq
      rw [h_inter_state, ← h_child]
      show childMsg.benv.state = devm.state
      exact hc_state
    · cases h_err2
  · -- sub-execution succeeded
    rw [executeCode.handleErrorWith_ok] at h_he
    have h_eq2 : child3 = evm2 := Except.ok.inj h_he
    subst h_eq2
    have h_post : c.Post wa evm'.sta child3 := h_ifOk
    by_cases h_err : child3.error.isSome = true
    · -- the sub-execution set the error flag : the parent state is rolled back
      rw [if_pos h_err] at hr2
      have h_child := Except.ok.inj hr2
      apply h_pc.state_eq
      rw [h_inter_state, ← h_child]
      show childMsg.benv.state = devm.state
      exact hc_state
    · -- clean success : reconstruct the precondition from the postcondition
      rw [if_neg h_err] at hr2
      have h_child := Except.ok.inj hr2
      subst h_child
      exact Pre.of_postcond h_post h_ct_ne h_pre1.code
        (code_eq_of_exec_sem (hpc0 ▸ ex_sub) h_pre1.code)
        (congrArg (fun st => (st.get wa).stor) h_inter_state)
        (congrArg (fun st => (st.get wa).code) h_inter_state)
        (fun a => congrArg (fun st => (st.get a).bal) h_inter_state)


lemma GenericCreate.some_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {endowment : B256} {newAddress : Adr} {memoryIndex memorySize : Nat}
    {evm' : Evm} {exn' : Execution}
    (h_run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize
      (.some ⟨evm', exn'⟩) (.ok inter))
    (ex_sub : Exec evm'.pc evm'.sta evm'.dyna exn')
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa evm'.sta evm'.dyna ∧
      (ifOk (c.Post wa evm'.sta) exn' → c.Pre wa sevm inter) := by
  unfold GenericCreate genericCreate.step at h_run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, Pure.pure,
    Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  -- every childless outcome leaves the slot empty
  · cases h_run.1
  · cases h_run.1
  · cases h_run.1
  · cases h_run.1
  · cases h_run.1
  · cases h_run.1
  -- the child frame is entered
  rename_i h_coll
  push Not at h_coll
  obtain ⟨r, hframe, hres⟩ := h_run
  obtain ⟨devm5, childMsg, hframe, h_st5, hc_state, hc_caller, hc_value, hc_ct,
      hc_ca, hc_stv, hcoll5⟩ :
      ∃ (d5 : Devm) (m : Msg), ProcessCreateMessage m (.some ⟨evm', exn'⟩) r ∧
        d5.state = devm.state.incrNonce sevm.currentTarget ∧
        m.benv.state = d5.state ∧ m.caller = sevm.currentTarget ∧
        m.value = endowment ∧ m.currentTarget = newAddress ∧
        m.codeAddress = .none ∧ m.shouldTransferValue = true ∧
        (d5.state.get newAddress).code.size = 0 :=
    ⟨_, _, hframe, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h_coll.2.1⟩
  -- the new address cannot be the WETH address, whose code is nonempty
  have h_new_ne : newAddress ≠ wa := by
    intro hc
    subst hc
    apply c.sem.ne_nil
    rw [← h_pc.code]
    have h_code4 : (devm5.state.get newAddress).code = devm.getCode newAddress := by
      rw [h_st5]
      exact State.incrNonce_get_code
    rw [← h_code4]
    have h_nil : (devm5.state.get newAddress).code.toList = [] := by
      have h_len := ByteArray.size_eq_length_toList (devm5.state.get newAddress).code
      rw [hcoll5] at h_len
      cases h_toList : (devm5.state.get newAddress).code.toList
      · rfl
      · rw [h_toList] at h_len
        cases h_len
    rw [h_nil]
  -- the instruction succeeded, so the sub-message result must be ok
  rcases r with err | child
  · cases Resume.create_run_error hres.symm
  have h_inter_state : inter.state = child.state := Resume.create_state hres.symm
  obtain ⟨henter, hr⟩ := RunFrame.some_inv hframe
  have hpc0 : evm'.pc = 0 := Frame.enter_run_pc henter
  obtain ⟨benv', eq_bt, h_evm⟩ := Frame.enter_run_inv henter
  have hset : processCreateMessage.settle childMsg
      (processMessage.settle (processCreateMessage.msg childMsg)
        (executeCode.handleErrorWith
          (processCreateMessage.msg childMsg).benv.stat.rules.stateGas
          exn')) = .ok child := hr.symm
  rcases h_he : executeCode.handleErrorWith
      (processCreateMessage.msg childMsg).benv.stat.rules.stateGas exn'
    with x | evmB
  · rw [h_he, processMessage.settle_error, processCreateMessage.settle_error] at hset
    cases hset
  rw [h_he] at hset
  rcases hA : processMessage.settle (processCreateMessage.msg childMsg) (.ok evmB) with
    x | evmA
  · rw [hA, processCreateMessage.settle_error] at hset
    cases hset
  rw [hA] at hset
  unfold processMessage.settle at hA
  dsimp only [bind, Except.bind] at hA
  unfold processCreateMessage.settle at hset
  dsimp only [bind, Except.bind] at hset
  have h_ifB := hA
  have h_ifA := hset
  -- projections of the create message
  have hP_state : (processCreateMessage.msg childMsg).benv.state
      = (childMsg.benv.state.setStor childMsg.currentTarget Stor.empty).incrNonce
          childMsg.currentTarget := rfl
  have hP_caller : (processCreateMessage.msg childMsg).caller = sevm.currentTarget :=
    hc_caller
  have hP_value : (processCreateMessage.msg childMsg).value = endowment := hc_value
  have hP_stv : (processCreateMessage.msg childMsg).shouldTransferValue = true := hc_stv
  have h_ds : evm'.dyna.state = benv'.state := by rw [h_evm]; rfl
  have h_ct' : evm'.sta.currentTarget = newAddress := by rw [h_evm]; exact hc_ct
  -- the balance transfer performed before the sub-execution
  rcases of_benvAfterTransfer hP_stv eq_bt with ⟨st_mid, h_sub, hB⟩
  rw [hP_state, hP_caller, hP_value, hc_ct] at h_sub
  have h_base_stor :
      (((childMsg.benv.state.setStor newAddress Stor.empty).incrNonce newAddress).get wa).stor
        = (devm.state.get wa).stor := by
    rw [State.incrNonce_get_stor, State.setStor_get_stor_ne h_new_ne, hc_state, h_st5,
      State.incrNonce_get_stor]
  have h_base_code :
      (((childMsg.benv.state.setStor newAddress Stor.empty).incrNonce newAddress).get wa).code
        = (devm.state.get wa).code := by
    rw [State.incrNonce_get_code, State.setStor_get_code, hc_state, h_st5,
      State.incrNonce_get_code]
  have h_base_bal : ∀ a,
      (((childMsg.benv.state.setStor newAddress Stor.empty).incrNonce newAddress).get a).bal
        = (devm.state.get a).bal := by
    intro a
    rw [State.incrNonce_get_bal, State.setStor_get_bal, hc_state, h_st5,
      State.incrNonce_get_bal]
  -- part 1 : the precondition holds for the sub-execution's initial state
  have h_pre1 : c.Pre wa evm'.sta evm'.dyna := by
    have h_state : evm'.dyna.state = st_mid.addBal newAddress endowment := by
      rw [h_ds, hB]
      show st_mid.addBal childMsg.currentTarget childMsg.value = _
      rw [hc_ct, hc_value]
    apply Pre.child_of_transfer h_pc h_ct_ne h_ct_ne h_base_stor h_base_code h_base_bal
      h_sub h_state h_ct'
    intro hc
    exact absurd (h_ct'.symm.trans hc) h_new_ne
  refine ⟨h_pre1, ?_⟩
  -- part 2 : the precondition is restored after the create returns
  intro h_ifOk
  -- when the sub-message rolls back, the parent state is unchanged modulo the nonce
  have h_rb : child.state = childMsg.benv.state → c.Pre wa sevm inter := by
    intro h_cs
    refine Pre.of_eqs h_pc ?_ ?_ ?_
    · show (inter.state.get wa).code = (devm.state.get wa).code
      rw [h_inter_state, h_cs, hc_state, h_st5]
      exact State.incrNonce_get_code
    · funext b
      show (inter.state.get b).bal = (devm.state.get b).bal
      rw [h_inter_state, h_cs, hc_state, h_st5]
      exact State.incrNonce_get_bal
    · show (inter.state.get wa).stor = (devm.state.get wa).stor
      rw [h_inter_state, h_cs, hc_state, h_st5]
      exact State.incrNonce_get_stor
  have h_isNone_false : ∀ {dX : Devm}, dX.error.isSome = true → dX.error.isNone ≠ true := by
    intro dX h_some hc
    rw [Option.isNone_iff_eq_none] at hc
    rw [hc] at h_some
    cases h_some
  have h_isNone_true : ∀ {dX : Devm}, ¬ dX.error.isSome = true → dX.error.isNone = true := by
    intro dX h_ns
    rcases h_opt : dX.error with _ | v
    · rfl
    · rw [h_opt] at h_ns
      exact absurd rfl h_ns
  rcases exn' with ⟨err4, d4⟩ | child4
  · -- sub-execution ended in error : the parent state is rolled back
    rcases of_handleError_err h_he with ⟨evmB', h_okB, h_someB, _⟩ | ⟨e, h_errB⟩
    · have h_eqB : evmB = evmB' := Except.ok.inj h_okB
      subst h_eqB
      rw [if_pos h_someB] at h_ifB
      have h_A := Except.ok.inj h_ifB
      have h_someA : evmA.error.isSome = true := by
        rw [← h_A]
        exact h_someB
      rw [if_neg (h_isNone_false h_someA)] at h_ifA
      have h_child := Except.ok.inj h_ifA
      apply h_rb
      rw [← h_child]
      rfl
    · cases h_errB
  · -- sub-execution succeeded
    rw [executeCode.handleErrorWith_ok] at h_he
    have h_eqB : child4 = evmB := Except.ok.inj h_he
    subst h_eqB
    have h_post : c.Post wa evm'.sta child4 := h_ifOk
    by_cases h_errC : child4.error.isSome = true
    · -- the sub-execution set the error flag : the parent state is rolled back
      rw [if_pos h_errC] at h_ifB
      have h_A := Except.ok.inj h_ifB
      have h_someA : evmA.error.isSome = true := by
        rw [← h_A]
        exact h_errC
      rw [if_neg (h_isNone_false h_someA)] at h_ifA
      have h_child := Except.ok.inj h_ifA
      apply h_rb
      rw [← h_child]
      rfl
    · -- clean success
      rw [if_neg h_errC] at h_ifB
      have h_A := Except.ok.inj h_ifB
      subst h_A
      rw [if_pos (h_isNone_true h_errC)] at h_ifA
      rcases h_cc : processCreateMessage.chargeCodeGas childMsg.benv.stat.rules child4
        with ⟨errC, evmC⟩ | evmC
      · -- code-deposit gas charge failed
        simp only [h_cc] at h_ifA
        cases errC
        case halt reason =>
          have h_child := Except.ok.inj h_ifA
          apply h_rb
          rw [← h_child]
          cases hsg : childMsg.benv.stat.rules.stateGas <;> rfl
        all_goals cases h_ifA
      · -- code deposit succeeded : reconstruct the precondition
        simp only [h_cc] at h_ifA
        have h_child := Except.ok.inj h_ifA
        have h_stC : evmC.state = child4.state := chargeCodeGas_state_ok h_cc
        apply Pre.of_postcond h_post h_ct_ne h_pre1.code
          (code_eq_of_exec_sem (hpc0 ▸ ex_sub) h_pre1.code)
        · rw [h_inter_state, ← h_child, Devm.setCode_state, h_stC, hc_ct,
            State.setCode_get_stor]
        · rw [h_inter_state, ← h_child, Devm.setCode_state, h_stC, hc_ct,
            State.setCode_get_code_ne h_new_ne]
        · intro a
          rw [h_inter_state, ← h_child, Devm.setCode_state, h_stC, hc_ct,
            State.setCode_get_bal]


lemma Xinst.some_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm} {x : Xinst}
    {evm' : Evm} {exn' : Execution}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_run : Xinst.Run sevm devm x (.some ⟨evm', exn'⟩) (.ok inter))
    (ex_sub : Exec evm'.pc evm'.sta evm'.dyna exn')
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa evm'.sta evm'.dyna ∧
      (ifOk (c.Post wa evm'.sta) exn' → c.Pre wa sevm inter) := by
  unfold Xinst.Run at h_run
  rcases Xinst.step_shapeCovered sevm devm x hfork with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hfr, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hfr, -, hcal, -, hs⟩ <;> rw [hs] at h_run
  -- a childless outcome cannot fill the slot
  · cases h_run.1
  -- dispatched to the CREATE family
  · exact GenericCreate.some_preserves_precond h_run ex_sub h_ne
      (h_pc.state_eq hfr.state.symm)
  -- dispatched to the CALL family
  · refine GenericCall.some_preserves_precond h_run ex_sub h_ne ?_ ?_
      (h_pc.state_eq hfr.state.symm)
    · rintro hstv
      rcases hcal with ⟨-, rfl⟩ | ⟨hsf, -⟩
      · exact h_ne
      · rw [hsf] at hstv; cases hstv
    · rintro hsf ht
      rcases hcal with ⟨hst, -⟩ | ⟨-, rfl⟩
      · rw [hsf] at hst; cases hst
      · exact absurd ht h_ne


lemma Post.selfdestruct_delete {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h_ne : sevm.currentTarget ≠ ca) (h_pc : c.Pre ca sevm devm) :
    c.Post ca sevm
      (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget) := by
  have h_bal_self :
      (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getBal
        sevm.currentTarget = 0 := by
    show ((devm.state.setBal sevm.currentTarget 0).get sevm.currentTarget).bal = 0
    rw [State.setBal_get_self]; rfl
  have h_bal_ne : ∀ a, sevm.currentTarget ≠ a →
      (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getBal a =
        devm.getBal a := by
    intro a ha
    show ((devm.state.setBal sevm.currentTarget 0).get a).bal = (devm.state.get a).bal
    rw [State.setBal_get_ne ha]
  have h_stor_eq :
      Devm.getStor (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget) ca =
        Devm.getStor devm ca := by
    show ((devm.state.setBal sevm.currentTarget 0).get ca).stor = (devm.state.get ca).stor
    apply State.setBal_get_stor
  have h_dec :
      Decrease sevm.currentTarget (devm.getBal sevm.currentTarget) devm.getBal
        (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getBal := by
    intro a
    constructor
    · intro h_eq; subst h_eq
      rw [h_bal_self, B256.sub_self]
    · intro ha; exact (h_bal_ne a ha).symm
  have h_sum :
      sum devm.getBal - (devm.getBal sevm.currentTarget).toNat =
        sum (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getBal :=
    sum_sub_assoc h_dec (B256.le_of_toNat_le_toNat (Nat.le_refl _))
  refine ⟨c.side_le h_pc.side (by omega), ?_⟩
  show c.Inv (Devm.getStor (addAccountToDelete (devm.setBal sevm.currentTarget 0)
      sevm.currentTarget) ca) 0
    ((addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getBal ca)
  rw [h_stor_eq, h_bal_ne ca h_ne]
  exact h_pc.inv.right h_ne

lemma Linst.inv_postcond {wa : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_run : Linst.Run sevm pre l (.ok post))
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm pre) :
    c.Post wa sevm post := by
  cases l
  case stop =>
    dsimp [Linst.Run, Linst.run] at h_run
    injection h_run with h_eq; subst h_eq
    exact post_of_pre h_pc
  case return_ =>
    have h_bal : pre.getBal = post.getBal :=
      ((inferInstance : Linst.Hinv Devm.getBal Devm.getBal Linst.return_)).inv h_run
    have h_stor : Devm.getStor pre = Devm.getStor post :=
      ((inferInstance : Linst.Hinv Devm.getStor Devm.getStor Linst.return_)).inv h_run
    constructor
    · rw [← h_bal]; exact h_pc.side
    · show c.Inv (Devm.getStor post wa) 0 (post.getBal wa)
      have hb : post.getBal wa = pre.getBal wa := (congr_fun h_bal wa).symm
      have hs : Devm.getStor post wa = Devm.getStor pre wa := (congr_fun h_stor wa).symm
      rw [hb, hs]
      exact h_pc.inv.right h_ne
  case revert =>
    dsimp [Linst.Run, Linst.run] at h_run
    rcases Except.bind_eq_ok h_run with ⟨_, _, h2⟩
    rcases Except.bind_eq_ok h2 with ⟨_, _, h4⟩
    rcases Except.bind_eq_ok h4 with ⟨_, _, h6⟩
    contradiction
  case selfdestruct =>
    have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
    have hbal : sevm.benvStat.rules.bal = none :=
      BenvStat.bal_none_of_stateGas_none hsg
    dsimp [Linst.Run, Linst.run] at h_run
    rw [hsg] at h_run
    simp only [Devm.balReadAccount_of_bal_none hbal] at h_run
    rcases Except.bind_eq_ok h_run with ⟨⟨dest_a, devm1⟩, h_pop, h_run1⟩
    rcases Except.bind_eq_ok h_run1 with ⟨devm2, h_charge, h_run2⟩
    rcases Except.bind_eq_ok h_run2 with ⟨_, h_assert, h_run3⟩
    rcases Except.bind_eq_ok h_run3 with ⟨devm3, h_sub, h_run4⟩
    have h_sub_some : devm2.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal = some devm3 := by
      cases eq : devm2.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal
      · rw [eq] at h_sub; contradiction
      · rw [eq] at h_sub; injection h_sub with h; subst h; rfl
    have h_sub_st : devm2.state.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal = some devm3.state := by
      dsimp [Devm.subBal, Option.bind] at h_sub_some
      cases h : devm2.state.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal
      · rw [h] at h_sub_some; contradiction
      · rw [h] at h_sub_some; injection h_sub_some with h2; subst h2; rfl
    have h_bal2 : devm2.getBal = devm1.getBal := by
      ext a
      have h1 := chargeGas_getBal_eq h_charge a
      rw [h1]
      split
      · simp [Devm.getBal, Devm.getAcct]
        rw [addAccessedAddress_state]
      · rfl
    have h_pc1 : c.Pre wa sevm devm1 := by
      apply Pre.of_eqs h_pc
      · exact Devm.popToAdr_getCode_eq h_pop wa
      · ext a; exact Devm.popToAdr_getBal_eq h_pop a
      · exact congr_fun (Devm.popToAdr_getStor_eq h_pop).symm wa
    have h_pc2 : c.Pre wa sevm devm2 := by
      apply Pre.of_eqs h_pc1
      · have h_code : devm2.getCode = devm1.getCode := by
          funext a
          have h1 := chargeGas_getCode_eq h_charge a
          rw [h1]
          split <;> rfl
        exact congr_fun h_code wa
      · exact h_bal2
      · have h_stor : Devm.getStor devm2 = Devm.getStor devm1 := by
          have h1 := (chargeGas_getStor_eq h_charge).symm
          rw [h1]
          split <;> rfl
        exact congr_fun h_stor wa
    have h_pc3 : c.Pre wa sevm (devm3.addBal dest_a ((dest_a, devm1).2.getAcct sevm.currentTarget).bal) := by
      exact Pre.transfer_state h_pc2 h_ne h_sub_st rfl
    clear h_run h_run1 h_run2 h_run3
    by_cases hdel : sevm.currentTarget ∈ (devm3.addBal (dest_a, devm1).1 ((dest_a, devm1).2.getAcct sevm.currentTarget).bal).createdAccounts
    · simp only [hdel, ite_true] at h_run4
      rw [← Except.ok.inj h_run4]
      exact Post.selfdestruct_delete h_ne h_pc3
    · simp only [hdel, ite_false] at h_run4
      rw [← Except.ok.inj h_run4]
      exact post_of_pre h_pc3



theorem preserves_lift_sem (c : ContractSpecSem) (ca : Adr)
    (σ : Sevm → Devm → Prop)
    (σ_pre : ∀ {e : Sevm} {d : Devm}, σ e d → c.Pre ca e d)
    (σ_of_ne : ∀ {e : Sevm} {d : Devm},
      e.currentTarget ≠ ca → c.Pre ca e d → σ e d)
    (σ_of_wf : ∀ {e : Sevm} {d : Devm},
      Mem.Wf d.memory → c.Pre ca e d → σ e d)
    ( body :
      ∀ {sevm pre post},
        c.sem.Run sevm pre post →
        sevm.currentTarget = ca →
        ( ∀ pc' sevm' pre' post',
            Exec pc' sevm' pre' (.ok post') →
            sevm'.depth < sevm.depth →
            CodeSem.At c.sem ca pc' sevm' pre' →
            σ sevm' pre' ∧ CoveredFork sevm'.benvStat.fork →
            c.Post ca sevm' post' ) →
        σ sevm pre ∧ CoveredFork sevm.benvStat.fork →
        c.Post ca sevm post ) :
    ∀ sevm pre post,
      CoveredFork sevm.benvStat.fork →
      Exec 0 sevm pre (.ok post) →
      (sevm.currentTarget = ca → some sevm.code.toList = c.sem.image) →
      σ sevm pre →
      c.Post ca sevm post := by
  intro sevm devm exn hfork exc h_code h_pc
  apply lift_inv_sem ca c.sem (fun e d => σ e d ∧ CoveredFork e.benvStat.fork) (c.Post ca)
  · exact body
  · intro pc' sevm' pre' n' inter' h_at' h_run' h_ne' h_pc'
    obtain ⟨hσ, hfork'⟩ := h_pc'
    refine ⟨σ_of_ne h_ne' ?_, hfork'⟩
    replace hσ := σ_pre hσ
    cases n' with
    | push xs le =>
      have hrun := (Step.run_ofExecution (xl := (.none : Xlot))).mp h_run'
      rcases Except.bind_eq_ok hrun.2.symm with ⟨devm1, h_charge, h_push⟩
      exact hσ.state_eq
        (((Devm.burn_of_chargeGas h_charge).state).trans
          ((Devm.push_of_push h_push).state)).symm
    | dupn imm =>
      have frame := Ninst.dupn_instructionFrame_effectRec
        (xl := .none) trivial h_run'
      exact hσ.state_eq frame.state.symm
    | swapn imm =>
      have frame := Ninst.swapn_instructionFrame_effectRec
        (xl := .none) trivial h_run'
      exact hσ.state_eq frame.state.symm
    | exchange imm =>
      have frame := Ninst.exchange_instructionFrame_effectRec
        (xl := .none) trivial h_run'
      exact hσ.state_eq frame.state.symm
    | reg r =>
      have h_reg : Rinst.run ⟨pc', sevm', pre'⟩ r = .ok inter' := by
        exact ((Step.run_ofExecution (xl := (.none : Xlot))).mp h_run').2.symm
      by_cases h_ss : r = Rinst.sstore
      · subst h_ss
        have h_frame := Rinst.sstore_run_stateWriteFrame pc' pre' sevm'
        rw [h_reg] at h_frame
        refine Pre.of_eqs hσ (h_frame.getCode_eq ca).symm ?_
          (sstore_preserves_getStor_ne h_reg h_ne')
        funext b
        exact (h_frame.getBal_eq b).symm
      · exact Pre.of_eqs hσ (Rinst.preserves_getCode h_reg ca) (Rinst.preserves_bal h_reg).symm
          (congr_fun (Rinst.preserves_stor h_ss h_reg) ca).symm
    | exec x =>
      refine Xinst.none_preserves_precond (x := x) hfork' ?_ h_ne' hσ
      exact XStep.run_toStep.mp h_run'
  · intro pc' sevm' pre' n' evm'' exn'' inter' h_at' h_run' ex_sub' h_ne' h_pc'
    obtain ⟨hσ, hfork'⟩ := h_pc'
    cases n' with
    | push xs le =>
      have hrun := (Step.run_ofExecution
        (xl := (.some ⟨evm'', exn''⟩ : Xlot))).mp h_run'
      cases hrun.1
    | dupn imm =>
      have hrun := (Step.run_ofExecution
        (xl := (.some ⟨evm'', exn''⟩ : Xlot))).mp h_run'
      cases hrun.1
    | swapn imm =>
      have hrun := (Step.run_ofExecution
        (xl := (.some ⟨evm'', exn''⟩ : Xlot))).mp h_run'
      cases hrun.1
    | exchange imm =>
      have hrun := (Step.run_ofExecution
        (xl := (.some ⟨evm'', exn''⟩ : Xlot))).mp h_run'
      cases hrun.1
    | reg r =>
      have hrun := (Step.run_ofExecution
        (xl := (.some ⟨evm'', exn''⟩ : Xlot))).mp h_run'
      cases hrun.1
    | exec x =>
      have hx : Xinst.Run sevm' pre' x (.some ⟨evm'', exn''⟩) (.ok inter') := by
        exact XStep.run_toStep.mp h_run'
      have hfork_c := Xinst.Run.some_child_fork hx hfork'
      obtain ⟨h_child, h_back⟩ :=
        Xinst.some_preserves_precond (x := x) hfork' hx ex_sub' h_ne' (σ_pre hσ)
      exact ⟨⟨σ_of_wf (Xinst.some_child_wf hx) h_child, hfork_c⟩,
        fun h_if => ⟨σ_of_ne h_ne' (h_back h_if), hfork'⟩⟩
  · intro pc' sevm' pre' j' pc'' inter' h_at' h_run' h_ne' h_pc'
    obtain ⟨hσ, hfork'⟩ := h_pc'
    exact ⟨σ_of_ne h_ne'
      (Pre.state_eq (σ_pre hσ) (Jinst.preserves_state h_run')), hfork'⟩
  · intro pc' sevm' pre' l' post' h_at' h_run' h_ne' h_pc'
    obtain ⟨hσ, hfork'⟩ := h_pc'
    exact Linst.inv_postcond hfork' h_run' h_ne' (σ_pre hσ)
  · exact exc
  · exact ⟨(σ_pre h_pc).1, λ h => ⟨h_code h, rfl⟩⟩
  · exact ⟨h_pc, hfork⟩

theorem StateInv.incrNonce {wa a : Adr} {w : Jaune.State}
    (h : c.StateInv wa w) : c.StateInv wa (w.incrNonce a) := by
  have hbal : (w.incrNonce a).bal = w.bal := by
    funext b
    show ((w.incrNonce a).get b).bal = (w.get b).bal
    by_cases hb : b = a
    · subst hb; simp only [State.incrNonce, State.get_set_self]
    · simp only [State.incrNonce, State.get_set_ne _ (Ne.symm hb)]
  have hstor : (w.incrNonce a).getStor wa = w.getStor wa := by
    show ((w.incrNonce a).get wa).stor = (w.get wa).stor
    by_cases hb : wa = a
    · subst hb; simp only [State.incrNonce, State.get_set_self]
    · simp only [State.incrNonce, State.get_set_ne _ (Ne.symm hb)]
  have hcode : (w.incrNonce a).getCode wa = w.getCode wa := by
    show ((w.incrNonce a).get wa).code = (w.get wa).code
    by_cases hb : wa = a
    · subst hb; simp only [State.incrNonce, State.get_set_self]
    · simp only [State.incrNonce, State.get_set_ne _ (Ne.symm hb)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcode]; exact h.code
  · rw [hbal]; exact h.side
  · show c.Inv ((w.incrNonce a).getStor wa) 0 ((w.incrNonce a).bal wa)
    rw [hstor, hbal]; exact h.inv

-- `addBal` can only raise a balance: `code` (bal field only) survives, and both
-- the side condition and the invariant are moved by the `*_addBal` slots under
-- the pre-sum bound `sum w.bal + val < 2 ^ 256`, supplied by the caller's
-- wei-conservation argument (a bound on the *result* would not rule out a
-- wrap, so it is not enough).
theorem StateInv.addBal {ca a : Adr} {val : B256} {w : Jaune.State}
    (hsum : sum w.bal + val.toNat < 2 ^ 256)
    (h : c.StateInv ca w) : c.StateInv ca (w.addBal a val) := by
  refine ⟨?_, c.side_addBal hsum h.side, c.inv_addBal hsum h.side h.inv⟩
  show some (((w.addBal a val).get ca).code).toList = c.sem.image
  unfold State.addBal; rw [State.setBal_get_code]; exact h.code

-- `subBal` lowers a balance, so the side condition survives by `side_le`;
-- dropping `ca`'s balance could break the invariant, hence `a ≠ ca`.
theorem StateInv.subBal {ca a : Adr} {val : B256} {w w' : Jaune.State}
    (hne : a ≠ ca) (h_sub : w.subBal a val = some w')
    (h : c.StateInv ca w) : c.StateInv ca w' := by
  rcases State.of_subBal h_sub with ⟨h_le, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · show some (((w.setBal a (w.bal a - val)).get ca).code).toList = c.sem.image
    rw [State.setBal_get_code]; exact h.code
  · have hdec : Decrease a val w.bal (w.setBal a (w.bal a - val)).bal := by
      intro b; constructor
      · intro heq; subst heq
        show w.bal a - val = ((w.setBal a (w.bal a - val)).get a).bal
        rw [State.setBal_get_self]; rfl
      · intro hnb
        show w.bal b = ((w.setBal a (w.bal a - val)).get b).bal
        rw [State.setBal_get_ne hnb]; rfl
    have hsum := sum_sub_assoc hdec h_le
    exact c.side_le h.side (by omega)
  · show c.Inv (((w.setBal a (w.bal a - val)).get ca).stor) 0
      ((w.setBal a (w.bal a - val)).get ca).bal
    rw [State.setBal_get_stor, State.setBal_get_ne hne]; exact h.inv

-- Deleting a foreign account (`a ≠ ca`) removes its balance from the sum and
-- leaves `ca`'s code/balance/storage alone.
theorem StateInv.destroyAccount {ca a : Adr} {w : Jaune.State}
    (hne : a ≠ ca) (h : c.StateInv ca w) : c.StateInv ca (destroyAccount w a) := by
  have hget : (Jaune.destroyAccount w a).get ca = w.get ca :=
    State.get_erase_ne (Ne.symm hne)
  refine ⟨?_, ?_, ?_⟩
  · show some (((Jaune.destroyAccount w a).get ca).code).toList = c.sem.image
    rw [hget]; exact h.code
  · have h0 : ((Jaune.destroyAccount w a).get a).bal = 0 := by
      show (State.get (w.erase a) a).bal = 0
      unfold State.get
      rw [Std.TreeMap.getD_erase]; simp [Acct.nil]
    have hdec : Decrease a (w.bal a) w.bal (Jaune.destroyAccount w a).bal := by
      intro b; constructor
      · intro heq; subst heq
        show w.bal a - w.bal a = ((Jaune.destroyAccount w a).get a).bal
        rw [h0, B256.sub_self]
      · intro hnb
        show w.bal b = (State.get (w.erase a) b).bal
        rw [State.get_erase_ne (Ne.symm hnb)]; rfl
    have hsum := sum_sub_assoc hdec (le_refl _)
    exact c.side_le h.side (by omega)
  · show c.Inv (((Jaune.destroyAccount w a).get ca).stor) 0
      ((Jaune.destroyAccount w a).get ca).bal
    rw [hget]; exact h.inv

-- Folded form for the `accountsToDelete` set (post-linearization `foldl`).
-- This one is proved outright from the atomic lemma to exercise the pattern.
theorem StateInv.foldl_destroyAccount {wa : Adr} :
    ∀ {as : List Adr} {w : Jaune.State},
      (∀ a ∈ as, a ≠ wa) → c.StateInv wa w →
        c.StateInv wa (as.foldl Jaune.destroyAccount w)
  | [], _, _, h => h
  | a :: as, w, hne, h => by
    rw [List.foldl_cons]
    exact StateInv.foldl_destroyAccount
      (fun b hb => hne b (List.mem_cons_of_mem _ hb))
      (h.destroyAccount (hne a List.mem_cons_self))

-- `Devm.get{Bal,Stor,Code}` are by definition the corresponding `State.*`
-- projections of `devm.state`, so a `Post` plus code-preservation is exactly
-- `StateInv` on the underlying state.
lemma StateInv.of_postcond {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h_post : c.Post ca sevm devm)
    (h_code : some (devm.state.getCode ca).toList = c.sem.image) :
    c.StateInv ca devm.state :=
  ⟨h_code, h_post.side, h_post.inv⟩

-- The `StateInv` counterpart of `Pre.child_of_transfer`: it only ever consults
-- the parent's `code`/`side`/value-free invariant, which are exactly the three
-- fields of `StateInv`.  `caller ≠ ca` is required so the credited value keeps
-- the invariant when `target = ca`.
lemma Pre.of_inv_transfer {ca : Adr} {sevm' : Sevm} {devm' : Devm}
    {st st_mid : Jaune.State} {caller target : Adr} {value : B256}
    (h_inv : c.StateInv ca st)
    (h_ne : caller ≠ ca)
    (h_sub : st.subBal caller value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct' : sevm'.currentTarget = target)
    (h_val : sevm'.currentTarget = ca → sevm'.value = value) :
    c.Pre ca sevm' devm' := by
  rcases of_state_transfer_fields (callee := target) h_sub with ⟨-, h_t_code, -, -, -⟩
  have h_stor' : Devm.getStor devm' ca = (st_mid.addBal target value).getStor ca := by
    show (devm'.state.get ca).stor = _
    rw [h_state]; rfl
  have h_bal' : devm'.getBal ca = (st_mid.addBal target value).bal ca := by
    show (devm'.state.get ca).bal = _
    rw [h_state]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (devm'.state.get ca).code.toList = c.sem.image
    rw [h_state, h_t_code ca]; exact h_inv.code
  · show c.Side devm'.state.bal
    rw [h_state]; exact c.side_transfer h_sub h_inv.side
  · intro h_eq
    have h_t_ca : target = ca := h_ct'.symm.trans h_eq
    subst h_t_ca
    show c.Inv (Devm.getStor devm' target) sevm'.value (devm'.getBal target)
    rw [h_stor', h_bal', h_val h_eq]
    exact c.inv_recv_transfer h_sub h_ne h_inv.side h_inv.inv
  · intro _
    show c.Inv (Devm.getStor devm' ca) 0 (devm'.getBal ca)
    rw [h_stor', h_bal']
    exact c.inv_transfer h_sub h_ne h_inv.side h_inv.inv

-- No-transfer counterpart of `Pre.of_inv_transfer`: when no value moves,
-- the pre-state is the invariant state itself, and `PreSolvent` reduces to the
-- value-free solvency provided `value = 0` whenever the frame targets `wa`.
lemma Pre.of_inv_eqs {wa : Adr} {sevm : Sevm} {devm : Devm}
    (h_inv : c.StateInv wa devm.state)
    (h_val0 : sevm.currentTarget = wa → sevm.value = 0) :
    c.Pre wa sevm devm := by
  refine ⟨h_inv.code, h_inv.side, ?_, ?_⟩
  · intro h_eq
    rw [h_val0 h_eq]; exact h_inv.inv
  · intro _; exact h_inv.inv

-- The precondition for the sub-execution's initial `evm`, built directly from
-- the bare-state invariant across `benvAfterTransfer` (transfer / no-transfer).
lemma Pre.of_inv_benvAfterTransfer {wa : Adr} {msg : Msg} {benv : Benv}
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)
    (hb : msg.benvAfterTransfer = .ok benv)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.Pre wa (initSevm (msg.withBenv benv)) (initDevm (msg.withBenv benv)) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · rcases Blanc.of_benvAfterTransfer h_stv hb with ⟨st_mid, h_sub, hbenv⟩
    have hbs : (initDevm (msg.withBenv benv)).state
        = st_mid.addBal msg.currentTarget msg.value := by
      show benv.state = _; rw [hbenv]; rfl
    exact Pre.of_inv_transfer h_inv (h_ne h_stv) h_sub hbs rfl (fun _ => rfl)
  · have hbenv : benv = msg.benv := of_benvAfterTransfer_no h_stv hb
    have h_false : msg.shouldTransferValue = false := by
      cases hh : msg.shouldTransferValue
      · rfl
      · exact absurd hh h_stv
    have h_inv' : c.StateInv wa (initDevm (msg.withBenv benv)).state := by
      show c.StateInv wa benv.state; rw [hbenv]; exact h_inv
    exact Pre.of_inv_eqs h_inv' (fun he => h_val0 h_false he)

-- The post-transfer state itself still satisfies `StateInv`: the transfer only
-- credits `ca` or moves value between accounts other than `ca`, which is
-- exactly what `side_transfer` and `inv_transfer` say.
lemma StateInv.of_benvAfterTransfer {ca : Adr} {msg : Msg} {benv : Benv}
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (hb : msg.benvAfterTransfer = .ok benv)
    (h_inv : c.StateInv ca msg.benv.state) :
    c.StateInv ca benv.state := by
  by_cases h_stv : msg.shouldTransferValue = true
  · rcases Blanc.of_benvAfterTransfer h_stv hb with ⟨st_mid, h_sub, hbenv⟩
    have hbs : benv.state = st_mid.addBal msg.currentTarget msg.value := by
      rw [hbenv]; rfl
    rcases of_state_transfer_fields (callee := msg.currentTarget) h_sub with
      ⟨-, h_t_code, -, -, -⟩
    rw [hbs]
    exact ⟨by rw [show ((st_mid.addBal msg.currentTarget msg.value).getCode ca)
                   = ((st_mid.addBal msg.currentTarget msg.value).get ca).code from rfl,
                 h_t_code ca]; exact h_inv.code,
           c.side_transfer h_sub h_inv.side,
           c.inv_transfer h_sub (h_ne h_stv) h_inv.side h_inv.inv⟩
  · have hbenv : benv = msg.benv := Blanc.of_benvAfterTransfer_no h_stv hb
    rw [hbenv]; exact h_inv

lemma StateInv.setStor_ne {wa a : Adr} {s : Stor} {w : Jaune.State}
    (hne : a ≠ wa) (h : c.StateInv wa w) : c.StateInv wa (w.setStor a s) := by
  have hget : (w.setStor a s).get wa = w.get wa := by
    unfold State.setStor; exact State.get_set_ne _ hne _
  refine ⟨?_, ?_, ?_⟩
  · show some (((w.setStor a s).get wa).code).toList = c.sem.image
    rw [hget]; exact h.code
  · rw [State.setStor_bal]; exact h.side
  · show c.Inv (((w.setStor a s).get wa).stor) 0 ((w.setStor a s).get wa).bal
    rw [hget]; exact h.inv

-- Likewise for installing code at a foreign account.
lemma StateInv.setCode_ne {wa a : Adr} {cd : ByteArray} {w : Jaune.State}
    (hne : a ≠ wa) (h : c.StateInv wa w) : c.StateInv wa (w.setCode a cd) := by
  have hget : (w.setCode a cd).get wa = w.get wa := by
    unfold State.setCode; exact State.get_set_ne _ hne _
  refine ⟨?_, ?_, ?_⟩
  · show some (((w.setCode a cd).get wa).code).toList = c.sem.image
    rw [hget]; exact h.code
  · rw [State.setCode_bal]; exact h.side
  · show c.Inv (((w.setCode a cd).get wa).stor) 0 ((w.setCode a cd).get wa).bal
    rw [hget]; exact h.inv

/-! ### The message- and block-environment forms of the invariant

The generic counterparts of `Blanc.Msg.InvSolvent` and `Blanc.Benv.InvSolvent`. -/

structure MsgInv (c : ContractSpecSem) (wa : Adr) (msg : Msg) : Prop where
  (state : c.StateInv wa msg.benv.state)
  (nodel : Msg.NoDel wa msg)
  (code : msg.target.isNone = false → msg.currentTarget = wa →
    some msg.code.toList = c.sem.image)
  (codeAddress : msg.target.isNone = false → msg.currentTarget = wa →
    msg.codeAddress = some wa)
  (ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
  (val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)

structure BenvInv (c : ContractSpecSem) (wa : Adr) (benv : Benv) : Prop where
  (state : c.StateInv wa benv.state)
  (ca : wa ∉ benv.createdAccounts)

variable {c : ContractSpecSem}

lemma StateInv.of_exec_precond {wa : Adr} {sevm : Sevm} {pre post : Devm}
    (hp : c.Preserves wa)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_pc : c.Pre wa sevm pre)
    (h_code : sevm.currentTarget = wa → some sevm.code.toList = c.sem.image)
    (h_wf : sevm.currentTarget = wa → Mem.Wf pre.memory)
    (exc : Exec 0 sevm pre (.ok post)) :
    c.StateInv wa post.state := by
  have h_post : c.Post wa sevm post := hp sevm pre post hfork exc h_code h_wf h_pc
  apply StateInv.of_postcond h_post
  have h_ce : post.getCode wa = pre.getCode wa := code_eq_of_exec_sem exc h_pc.code
  show some (post.state.getCode wa).toList = c.sem.image
  rw [show post.state.getCode wa = post.getCode wa from rfl, h_ce]
  exact h_pc.code



-- Deep helper: one `processMessage` run preserves `c.StateInv` and never
-- self-destructs `wa`.  This is where the frame-level `exec_preserves_solvent` gets
-- lifted: `processMessage` = `benvAfterTransfer` (value transfer) then
-- `executeCode` (→ `exec (initEvm ·)`) with on-error rollback.  The `nof`
-- and `getCode` parts are already available through the relational-mirror
-- stacks (`ProcessMessage.preserves_nof`, `ProcessMessage.preserves_getCode_gen`); the
-- solvency part is the genuinely new content, obtained from `exec_preserves_solvent`
-- via `c.Post` and `StateInv.of_postcond`.  Still open.
theorem processMessage_preserves_inv {wa : Adr} {msg : Msg} {evm : Devm}
    (hfork : CoveredFork msg.benv.stat.fork)
    (hp : c.Preserves wa)
    (h_run : processMessage msg = .ok evm)
    (h_code : msg.currentTarget = wa → some msg.code.toList = c.sem.image)
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa evm.state := by
  obtain ⟨xl, hfill, hrel⟩ := of_processMessage msg (.ok evm) h_run
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hrel
  unfold FrameBody at hbody
  rcases h_bt : msg.benvAfterTransfer with e | benv <;> rw [h_bt] at hbody
  · rw [hbody.2, processMessage.settle_error] at hset
    cases hset
  have h_pc : c.Pre wa (initSevm (msg.withBenv benv)) (initDevm (msg.withBenv benv)) :=
    Pre.of_inv_benvAfterTransfer h_ne h_val0 h_bt h_inv
  have h_code' : (initSevm (msg.withBenv benv)).currentTarget = wa →
      some (initSevm (msg.withBenv benv)).code.toList = c.sem.image := h_code
  rcases r0 with x | evm'
  · rw [processMessage.settle_error] at hset
    cases hset
  unfold processMessage.settle at hset
  dsimp only [bind, Except.bind] at hset
  by_cases herr : evm'.error.isSome = true
  · -- sub-execution failed : state rolled back to the pre-transfer state
    rw [if_pos herr] at hset
    rw [Except.ok.inj hset]
    exact h_inv
  · -- clean success
    rw [if_neg herr] at hset
    have h_eq : evm' = evm := Except.ok.inj hset.symm
    subst h_eq
    rcases of_executeCode_cases hbody with ⟨adr, h_he⟩ | ⟨exn, h_xl, h_he⟩
    · -- precompile : the state is left untouched
      rw [state_of_executePrecomp_ok h_he herr]
      exact StateInv.of_benvAfterTransfer h_ne h_bt h_inv
    · -- interpreted code : hand off to the driver-level theorem
      subst h_xl
      obtain ⟨exc⟩ := hfill
      rw [exec_ok_of_handleError h_he herr] at exc
      have hfork_sevm : CoveredFork (initSevm (msg.withBenv benv)).benvStat.fork := by
        rw [initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat h_bt]
        exact hfork
      exact StateInv.of_exec_precond hp hfork_sevm h_pc h_code' (fun _ => Mem.wf_empty) exc


-- Overwriting the storage of a *foreign* account (`a ≠ wa`) preserves `c.StateInv`
-- (`wa`'s account is untouched, and `setStor` leaves every balance alone).

-- Create path.  `processCreateMessage` seeds the account being created
-- (`setStor .empty` + `incrNonce`, both at `currentTarget ≠ wa`), runs
-- `processMessage`, then on clean success charges code gas and installs the
-- returned code at `currentTarget`; the exceptional-halt and error paths roll
-- the state back to `msg.benv.state`.
-- `h_ct_ne` (the create address is fresh, hence `≠ wa`) subsumes both the
-- WETH-code condition and the `value = 0` condition: their premises are all
-- `currentTarget = wa`, so `h_ct_ne` discharges them vacuously.
theorem processCreateMessage_preserves_inv {wa : Adr} {msg : Msg} {evm : Devm}
    (hfork : CoveredFork msg.benv.stat.fork)
    (hp : c.Preserves wa)
    (h_run : processCreateMessage msg = .ok evm)
    (h_ct_ne : msg.currentTarget ≠ wa)
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa evm.state := by
  rw [processCreateMessage_eq] at h_run
  -- the seeded sub-message still satisfies the invariant (`currentTarget ≠ wa`)
  have h_inv_cm : c.StateInv wa (processCreateMessage.msg msg).benv.state := by
    show c.StateInv wa ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
      msg.currentTarget)
    exact StateInv.incrNonce (StateInv.setStor_ne h_ct_ne h_inv)
  rcases hpm : processMessage (processCreateMessage.msg msg) with x | evm2
  · rw [hpm, processCreateMessage.settle_error] at h_run
    cases h_run
  rw [hpm] at h_run
  have h_rest := h_run
  have hfork' : CoveredFork (processCreateMessage.msg msg).benv.stat.fork := by
    rw [processCreateMessage.msg_benvStat]; exact hfork
  have h_pm : c.StateInv wa evm2.state :=
    processMessage_preserves_inv hfork' hp hpm (fun h => absurd h h_ct_ne) h_ne
      (fun _ h => absurd h h_ct_ne) h_inv_cm
  unfold processCreateMessage.settle at h_rest
  dsimp only [bind, Except.bind] at h_rest
  by_cases herr : evm2.error.isNone = true
  · rw [if_pos herr] at h_rest
    rcases hcg : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm2
      with ⟨err, evm3⟩ | evm3
    · -- code-gas charge failed
      rw [hcg] at h_rest
      cases err
      case halt reason =>
        -- exceptional halt : state rolled back to `msg.benv.state`
        have hsg : msg.benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
        rw [hsg] at h_rest
        rw [← Except.ok.inj h_rest]; exact h_inv
      all_goals cases h_rest
    · -- clean success : install the returned code at `currentTarget ≠ wa`
      rw [hcg] at h_rest; dsimp only at h_rest
      rw [← Except.ok.inj h_rest, Devm.setCode_state, chargeCodeGas_state_ok hcg]
      exact StateInv.setCode_ne h_ct_ne h_pm
  · -- sub-message failed : state rolled back to `msg.benv.state`
    rw [if_neg herr] at h_rest
    rw [← Except.ok.inj h_rest]; exact h_inv

lemma setDelegationStep_preserves_inv {wa : Adr} {auth : Auth} {msg msg' : Msg}
    {refund refund' : B256}
    (h_run : setDelegationStep auth msg refund = .ok (msg', refund'))
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa msg'.benv.state := by
  unfold setDelegationStep at h_run
  split at h_run
  · injection h_run with h1; injection h1 with h_msg h_refund
    subst h_msg
    exact h_inv
  · split at h_run
    · injection h_run with h1; injection h1 with h_msg h_refund
      subst h_msg
      exact h_inv
    · split at h_run
      · injection h_run with h1; injection h1 with h_msg h_refund
        subst h_msg
        exact h_inv
      · contradiction
      · rename_i authority heq
        dsimp only at h_run
        split at h_run
        · injection h_run with h1; injection h1 with h_msg h_refund
          subst h_msg
          exact h_inv
        · split at h_run
          · injection h_run with h1; injection h1 with h_msg h_refund
            subst h_msg
            exact h_inv
          · injection h_run with h1; injection h1 with h_msg h_refund
            subst h_msg
            have h_code_ne : (msg.benv.state.getCode wa).toList ≠ [] := by
              intro h_empty
              exact (c.sem.ne_nil (by rw [← h_inv.code, h_empty])) rfl
            have h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa) :=
              c.sem.not_delegation h_inv.code
            have h_ne : authority ≠ wa := by
              intro h_eq
              subst authority
              by_cases h_empty : (msg.benv.state.get wa).code.isEmpty = true
              · have h_size : (msg.benv.state.get wa).code.size = 0 := by
                  simpa [ByteArray.isEmpty] using h_empty
                exact (ne_wa_of_code_size_zero h_code_ne h_size) rfl
              · have h_valid : isValidDelegation (msg.benv.state.get wa).code := by
                  simp_all
                exact h_not_del (by simpa [State.getCode] using h_valid)
            change c.StateInv wa ((msg.benv.state.setCode authority _).incrNonce authority)
            exact StateInv.incrNonce (StateInv.setCode_ne h_ne h_inv)

lemma setDelegationLoop_preserves_inv {wa : Adr} {auths : List Auth} {msg msg' : Msg}
    {refund refund' : B256}
    (h_run : setDelegationLoop auths msg refund = .ok (msg', refund'))
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa msg'.benv.state := by
  induction auths generalizing msg refund with
  | nil =>
    injection h_run with h1; injection h1 with h_msg h_refund
    subst h_msg
    exact h_inv
  | cons auth auths_tail ih =>
    unfold setDelegationLoop at h_run
    rcases Except.bind_eq_ok h_run with ⟨⟨msg1, refund1⟩, h_step, h_tail⟩
    exact ih h_tail (setDelegationStep_preserves_inv h_step h_inv)

lemma setDelegation_preserves_inv {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa msg'.benv.state := by
  unfold setDelegation at h_run
  dsimp [bind, Except.bind] at h_run
  apply Except.bind_eq_ok at h_run
  rcases h_run with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
  have h_eq_benv : msg_mid.benv = msg'.benv := by
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · simpa using congrArg Msg.benv (congrArg Prod.fst (Except.ok.inj h_rest))
  rw [← h_eq_benv]
  exact setDelegationLoop_preserves_inv h_loop h_inv


lemma MsgInv.pc {wa : Adr} {msg : Msg} {codeSrc : Adr → ByteArray}
    (h : c.MsgInv wa msg) :
    c.MsgInv wa
      (match getDelegatedCodeAddress msg.code with
      | none => msg
      | some dca =>
        { msg with
          disablePrecompiles := true,
          accessedAddresses := msg.accessedAddresses.insert dca,
          code := codeSrc dca,
          codeAddress := some dca }) := by
  split
  · exact h
  · rename_i dca h_dca
    refine ⟨h.state, ⟨h.nodel.ca, h.nodel.code⟩, ?_, ?_, h.ne, h.val0⟩
    · intro h_tgt h_ct
      have h_not_del : ¬ isValidDelegation msg.code :=
        c.sem.not_delegation
          (h.code (by simpa using h_tgt) (by simpa using h_ct))
      unfold getDelegatedCodeAddress at h_dca
      split at h_dca
      · rename_i h_del
        exact False.elim (h_not_del h_del)
      · contradiction
    · intro h_tgt h_ct
      have h_not_del : ¬ isValidDelegation msg.code :=
        c.sem.not_delegation
          (h.code (by simpa using h_tgt) (by simpa using h_ct))
      unfold getDelegatedCodeAddress at h_dca
      split at h_dca
      · rename_i h_del
        exact False.elim (h_not_del h_del)
      · contradiction

lemma setDelegation_preserves_msgInv {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h : c.MsgInv wa msg) :
    c.MsgInv wa msg' := by
  have h_run_orig := h_run
  have h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa) :=
    c.sem.not_delegation h.state.code
  refine ⟨setDelegation_preserves_inv h_run h.state,
    setDelegation_msg_noDel h_run h.nodel h_not_del, ?_, ?_, ?_, ?_⟩
  · intro h_tgt h_ct
    unfold setDelegation at h_run
    dsimp [bind, Except.bind] at h_run
    apply Except.bind_eq_ok at h_run
    rcases h_run with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
    rcases setDelegationLoop_fields h_loop with ⟨_, h_mid_tgt, h_mid_ct, _, _, h_mid_ca⟩
    have h_loop_equiv := setDelegationLoop_benv_equiv h_loop
    rcases h_loop_equiv with ⟨_, h_code⟩
    have h_code_ne : (msg.benv.state.getCode wa).toList ≠ [] := by
      intro h_empty
      exact (c.sem.ne_nil (by rw [← h.state.code, h_empty])) rfl
    have h_code_wa := h_code wa h_code_ne h_not_del
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · rename_i ca h_ca
      have h_msg' : msg' =
          { msg_mid with code := msg_mid.benv.state.getCode ca } := by
        exact (congrArg Prod.fst (Except.ok.inj h_rest)).symm
      subst msg'
      change some (msg_mid.benv.state.getCode ca).toList = c.sem.image
      change msg_mid.currentTarget = wa at h_ct
      rw [h_mid_ct] at h_ct
      have h_ca_wa : ca = wa := by
        have h_msg_tgt : msg.target.isNone = false := by
          change msg_mid.target.isNone = false at h_tgt
          rwa [h_mid_tgt] at h_tgt
        have h_msg_ca := h.codeAddress h_msg_tgt h_ct
        rw [h_mid_ca, h_msg_ca] at h_ca
        injection h_ca with h_eq
        exact h_eq.symm
      subst h_ca_wa
      rw [h_code_wa]
      exact h.state.code
  · intro h_tgt h_ct
    unfold setDelegation at h_run_orig
    dsimp [bind, Except.bind] at h_run_orig
    apply Except.bind_eq_ok at h_run_orig
    rcases h_run_orig with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
    rcases setDelegationLoop_fields h_loop with ⟨_, h_mid_tgt, h_mid_ct, _, _, h_mid_ca⟩
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · rename_i ca h_ca
      have h_msg' : msg' =
          { msg_mid with code := msg_mid.benv.state.getCode ca } := by
        exact (congrArg Prod.fst (Except.ok.inj h_rest)).symm
      subst msg'
      change msg_mid.codeAddress = some wa
      change msg_mid.currentTarget = wa at h_ct
      rw [h_mid_ct] at h_ct
      rw [h_mid_ca]
      apply h.codeAddress
      · change msg_mid.target.isNone = false at h_tgt
        rwa [h_mid_tgt] at h_tgt
      · exact h_ct
  · intro h_stv
    unfold setDelegation at h_run_orig
    dsimp [bind, Except.bind] at h_run_orig
    apply Except.bind_eq_ok at h_run_orig
    rcases h_run_orig with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
    rcases setDelegationLoop_fields h_loop with ⟨h_mid_caller, _, _, h_mid_stv, _, _⟩
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · rename_i ca h_ca
      have h_msg' : msg' =
          { msg_mid with code := msg_mid.benv.state.getCode ca } := by
        exact (congrArg Prod.fst (Except.ok.inj h_rest)).symm
      subst msg'
      change msg_mid.caller ≠ wa
      rw [h_mid_caller]
      apply h.ne
      change msg_mid.shouldTransferValue = true at h_stv
      rwa [h_mid_stv] at h_stv
  · intro h_stv h_ct
    unfold setDelegation at h_run_orig
    dsimp [bind, Except.bind] at h_run_orig
    apply Except.bind_eq_ok at h_run_orig
    rcases h_run_orig with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
    rcases setDelegationLoop_fields h_loop with ⟨_, _, h_mid_ct, h_mid_stv, h_mid_val, _⟩
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · rename_i ca h_ca
      have h_msg' : msg' =
          { msg_mid with code := msg_mid.benv.state.getCode ca } := by
        exact (congrArg Prod.fst (Except.ok.inj h_rest)).symm
      subst msg'
      change msg_mid.value = 0
      rw [h_mid_val]
      apply h.val0
      · change msg_mid.shouldTransferValue = false at h_stv
        rwa [h_mid_stv] at h_stv
      · change msg_mid.currentTarget = wa at h_ct
        rwa [h_mid_ct] at h_ct

theorem processMessageCall_preserves_inv {wa : Adr} {msg : Msg} {st' : Jaune.State}
    {out : MsgCallOutput}
    (hfork : CoveredFork msg.benv.stat.fork)
    (hp : c.Preserves wa)
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h_inv : c.MsgInv wa msg) :
    c.StateInv wa st' ∧ (∀ a ∈ out.accountsToDelete.toList, a ≠ wa) := by
  have hsg : msg.benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
  refine ⟨?_, processMessageCall_accountsToDelete_ne hfork h_run h_inv.nodel
    (c.sem.not_delegation h_inv.state.code)⟩
  unfold processMessageCall at h_run
  split at h_run
  · unfold processMessageCall.create at h_run
    dsimp only at h_run
    rw [hsg] at h_run
    dsimp only at h_run
    split at h_run
    · injection h_run with h_eq
      cases h_eq
      exact h_inv.state
    · rename_i h_col
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at h_col
      have h_ct : msg.currentTarget ≠ wa :=
        ne_wa_of_not_hasCodeOrNonce h_inv.nodel.code h_col.1
      revert h_run
      rcases h_evm : processCreateMessage msg with ⟨err⟩ | ⟨evm⟩
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        injection h_run
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        have h_pm := processCreateMessage_preserves_inv hfork hp h_evm h_ct
          h_inv.ne h_inv.state
        change (if evm.error.isNone = true then _ else _) = _ at h_run
        split at h_run
        · split at h_run
          · injection h_run
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
            rcases h_run with ⟨rfl, _⟩
            exact h_pm
        · simp only [id_eq, Except.ok.injEq, Prod.mk.injEq] at h_run
          rcases h_run with ⟨rfl, _⟩
          exact h_pm
  · rename_i h_target
    have h_target_false : msg.target.isNone = false := by
      cases ht : msg.target.isNone <;> simp [ht] at h_target ⊢
    unfold processMessageCall.call at h_run
    dsimp only at h_run
    rw [hsg] at h_run
    dsimp only at h_run
    split at h_run
    · simp only [bind, Except.bind] at h_run
      unfold Except.bimap at h_run
      split at h_run
      · injection h_run
      · rename_i evm h_evm
        split at h_evm
        · injection h_evm
        · rename_i evm' h_pm
          simp only [id_eq, Except.ok.injEq] at h_evm
          subst h_evm
          have h_pc : c.MsgInv wa
              (match getDelegatedCodeAddress msg.code with
              | none => msg
              | some dca =>
                { msg with
                  disablePrecompiles := true,
                  accessedAddresses := msg.accessedAddresses.insert dca,
                  code := msg.benv.state.getCode dca,
                  codeAddress := some dca }) :=
            MsgInv.pc (codeSrc := fun dca => msg.benv.state.getCode dca) h_inv
          have h_tgt_pc :
              (match getDelegatedCodeAddress msg.code with
              | none => msg
              | some dca =>
                { msg with
                  disablePrecompiles := true,
                  accessedAddresses := msg.accessedAddresses.insert dca,
                  code := msg.benv.state.getCode dca,
                  codeAddress := some dca }).target.isNone = false := by
            split <;> simpa using h_target_false
          have hfork' : CoveredFork               (match getDelegatedCodeAddress msg.code with
              | none => msg
              | some dca =>
                { msg with
                  disablePrecompiles := true,
                  accessedAddresses := msg.accessedAddresses.insert dca,
                  code := msg.benv.state.getCode dca,
                  codeAddress := some dca }).benv.stat.fork := by
            have hbenv :               (match getDelegatedCodeAddress msg.code with
              | none => msg
              | some dca =>
                { msg with
                  disablePrecompiles := true,
                  accessedAddresses := msg.accessedAddresses.insert dca,
                  code := msg.benv.state.getCode dca,
                  codeAddress := some dca }).benv = msg.benv := by split <;> rfl
            rw [hbenv]; exact hfork
          have h_evm_inv :=
            processMessage_preserves_inv hfork' hp h_pm
              (fun hct => h_pc.code h_tgt_pc hct)
              h_pc.ne h_pc.val0 h_pc.state
          split at h_run
          · split at h_run
            · injection h_run
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
              rcases h_run with ⟨rfl, _⟩
              exact h_evm_inv
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
            rcases h_run with ⟨rfl, _⟩
            exact h_evm_inv
    · rename_i h_col
      rcases h_del : setDelegation msg with ⟨err⟩ | ⟨⟨msgDelegation, val⟩⟩
      · simp only [h_del, bind, Except.bind] at h_run
        injection h_run
      · simp only [h_del, bind, Except.bind] at h_run
        have h_del_inv := setDelegation_preserves_msgInv h_del h_inv
        unfold Except.bimap at h_run
        split at h_run
        · injection h_run
        · rename_i evm h_evm
          split at h_evm
          · injection h_evm
          · rename_i evm' h_pm
            simp only [id_eq, Except.ok.injEq] at h_evm
            subst h_evm
            have h_pc : c.MsgInv wa
                (match getDelegatedCodeAddress msgDelegation.code with
                | none => msgDelegation
                | some dca =>
                  { msgDelegation with
                    disablePrecompiles := true,
                    accessedAddresses := msgDelegation.accessedAddresses.insert dca,
                    code := msgDelegation.benv.state.getCode dca,
                    codeAddress := some dca }) :=
              MsgInv.pc (codeSrc := fun dca => msgDelegation.benv.state.getCode dca) h_del_inv
            have h_del_fields := setDelegation_fields h_del
            have h_msgDelegation_target_false : msgDelegation.target.isNone = false := by
              rw [h_del_fields.2.1]
              exact h_target_false
            have h_tgt_pc :
                (match getDelegatedCodeAddress msgDelegation.code with
                | none => msgDelegation
                | some dca =>
                  { msgDelegation with
                    disablePrecompiles := true,
                    accessedAddresses := msgDelegation.accessedAddresses.insert dca,
                    code := msgDelegation.benv.state.getCode dca,
                    codeAddress := some dca }).target.isNone = false := by
              split <;> simpa using h_msgDelegation_target_false
            have hfork' : CoveredFork                 (match getDelegatedCodeAddress msgDelegation.code with
                | none => msgDelegation
                | some dca =>
                  { msgDelegation with
                    disablePrecompiles := true,
                    accessedAddresses := msgDelegation.accessedAddresses.insert dca,
                    code := msgDelegation.benv.state.getCode dca,
                    codeAddress := some dca }).benv.stat.fork := by
              have hbenv :                 (match getDelegatedCodeAddress msgDelegation.code with
                | none => msgDelegation
                | some dca =>
                  { msgDelegation with
                    disablePrecompiles := true,
                    accessedAddresses := msgDelegation.accessedAddresses.insert dca,
                    code := msgDelegation.benv.state.getCode dca,
                    codeAddress := some dca }).benv = msgDelegation.benv := by split <;> rfl
              have hstat : msgDelegation.benv.stat = msg.benv.stat :=
                setDelegation_benvStat h_del
              rw [hbenv, hstat]; exact hfork
            have h_evm_inv :=
              processMessage_preserves_inv hfork' hp h_pm
                (fun hct => h_pc.code h_tgt_pc hct)
                h_pc.ne h_pc.val0 h_pc.state
            split at h_run
            · split at h_run
              · injection h_run
              · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
                rcases h_run with ⟨rfl, _⟩
                exact h_evm_inv
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
              rcases h_run with ⟨rfl, _⟩
              exact h_evm_inv

/-! ### Transaction-level helper lemmas

The proof of `processTransaction_preserves_inv` factors into three local facts.
They are intentionally stated at the executable-definition boundary:

* a checked transaction sender cannot be the WETH account, since successful
  `checkTransaction` accepted the sender as an EOA/delegation account;
* `prepareMessage` packages the post-upfront-fee state into a message satisfying
  `c.MsgInv`;
* the final transaction gas credits are funded by the earlier upfront debit, so
  the two `addBal`s cannot overflow the global balance sum.

These are the intended follow-up proof obligations; with them available, the
main transaction invariant proof below is just definition inversion and
composition of already-proved message-level invariants. -/

lemma checkTransaction_sender_ne_of_inv {wa : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    (h_check :
      checkTransaction benv bout tx =
        .ok ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩)
    (h_inv : c.BenvInv wa benv) :
    sender ≠ wa := by
  intro hsender
  subst sender
  unfold checkTransaction at h_check
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨senderAddress, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, hg, h_check⟩
  have hs : senderAddress = wa := congrArg Prod.fst (Except.ok.inj h_check)
  subst senderAddress
  unfold checkTransactionSenderAccount at hg
  split at hg <;> try contradiction
  split at hg <;> try contradiction
  split at hg <;> try contradiction
  have h_no : ¬ ((benv.state.get wa).code.isEmpty ∨ isValidDelegation (benv.state.get wa).code) := by
    intro h
    rcases h with h_empty | h_del
    · have h_empty' : (benv.state.getCode wa).toList = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [← ByteArray.size_eq_length_toList]
        unfold ByteArray.isEmpty at h_empty; simp at h_empty; simpa [State.getCode] using congrArg ByteArray.size h_empty
      exact (c.sem.ne_nil (by rw [← h_inv.state.code, h_empty'])) rfl
    · exact c.sem.not_delegation h_inv.state.code h_del
  simp [checkTransactionSenderCode, h_no] at hg

lemma prepareMessage_preserves_inv {wa : Adr}
    {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h_prep : prepareMessage benv tenv tx = .ok msg)
    (h_state : c.StateInv wa benv.state)
    (h_ca : wa ∉ benv.createdAccounts)
    (h_origin_ne : tenv.stat.origin ≠ wa) :
    c.MsgInv wa msg := by
  -- `prepareMessage` sets `caller = tenv.stat.origin`,
  -- `shouldTransferValue = true`, and preserves `benv`.  In the call case, if
  -- `currentTarget = wa`, then the installed code/codeAddress are exactly WETH's
  -- code and `some wa`; in the create case `target.isNone = true`, so those
  -- conditional fields are vacuous.
  unfold prepareMessage at h_prep
  cases hrecv : tx.type.receiver? with
  | none =>
    simp [hrecv] at h_prep
    subst msg
    refine ⟨h_state, ⟨h_ca, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro h_empty
      exact (c.sem.ne_nil (by rw [← h_state.code, h_empty])) rfl
    · simp
    · simp
    · simpa using h_origin_ne
    · simp
  | some target =>
    simp [hrecv] at h_prep
    subst msg
    refine ⟨h_state, ⟨h_ca, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro h_empty
      exact (c.sem.ne_nil (by rw [← h_state.code, h_empty])) rfl
    · intro _ h_target
      change target = wa at h_target
      subst target
      simpa using h_state.code
    · intro _ h_target
      change target = wa at h_target
      subst target
      rfl
    · simpa using h_origin_ne
    · simp

lemma StateInv.add_transaction_gas_credits {wa : Adr}
    {baseState debitState postMsgState : Jaune.State}
    {benv : Benv} {tx : Tx}
    {sender : Adr} {effectiveGasPrice : Nat}
    {validationSender : Adr}
    {intrinsicGas calldataFloorGasCost refundCounter : Nat}
    {txOutput : MsgCallOutput}
    (h_validate :
      validateTransaction benv.stat.rules tx validationSender =
        .ok ⟨intrinsicGas, calldataFloorGasCost⟩)
    -- the upfront-fee modulus bound, in `benv` form: the caller derives it
    -- from `checkTransaction_upfront_lt_modulus` (whose `beginTransaction`
    -- environment is only defeq) and ascribes it here.
    (h_fee_lt :
      tx.gas * effectiveGasPrice +
        (if tx.isTypeThree = true then
          calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
        else 0) < 2 ^ 256)
    (h_debit :
      (baseState.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
          else
            0).toB256 =
        some debitState)
    (h_msg_sum : sum postMsgState.bal ≤ sum debitState.bal)
    (h_base_sum : sum baseState.bal < 2 ^ 256)
    (h_post : c.StateInv wa postMsgState) :
    c.StateInv wa
      ((postMsgState.addBal sender
          ((tx.gas -
              max (tx.gas - txOutput.gasLeft -
                min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
                calldataFloorGasCost) *
            effectiveGasPrice).toB256).addBal
        benv.stat.coinbase
          (max (tx.gas - txOutput.gasLeft -
              min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
              calldataFloorGasCost *
            (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256) := by
  have h_floor := validateTransaction_calldataFloorGasCost_le_gas h_validate
  have h_debit_sum := State.balSum_subBal h_debit
  dsimp only [State.balSum] at h_debit_sum
  rw [State.incrNonce_bal] at h_debit_sum
  have h_debit_exact := B256.toNat_toB256_of_lt h_fee_lt
  rw [h_debit_exact] at h_debit_sum
  have h_used_le :
      max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost ≤ tx.gas := by
    apply max_le
    · omega
    · exact h_floor
  have h_credits_le :
      (tx.gas -
          max (tx.gas - txOutput.gasLeft -
            min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
            calldataFloorGasCost) *
        effectiveGasPrice +
      max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost *
        (effectiveGasPrice - benv.stat.baseFeePerGas) ≤
      tx.gas * effectiveGasPrice := by
    apply le_trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left _
        (Nat.sub_le effectiveGasPrice benv.stat.baseFeePerGas)) _)
    rw [← Nat.add_mul, Nat.sub_add_cancel h_used_le]
  have h_refund_le :
      (((tx.gas -
          max (tx.gas - txOutput.gasLeft -
            min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
            calldataFloorGasCost) *
        effectiveGasPrice).toB256).toNat ≤
      (tx.gas -
          max (tx.gas - txOutput.gasLeft -
            min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
            calldataFloorGasCost) *
        effectiveGasPrice := by
    rw [B256.toNat_toB256]
    unfold Nat.lo
    exact Nat.mod_le _ _
  have h_tip_le :
      ((max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost *
        (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256).toNat ≤
      max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost *
        (effectiveGasPrice - benv.stat.baseFeePerGas) := by
    rw [B256.toNat_toB256]
    unfold Nat.lo
    exact Nat.mod_le _ _
  have h_sender_sum :
      sum postMsgState.bal +
        (((tx.gas -
            max (tx.gas - txOutput.gasLeft -
              min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
              calldataFloorGasCost) *
          effectiveGasPrice).toB256).toNat < 2 ^ 256 := by
    omega
  have h_sender_inv :=
    StateInv.addBal (a := sender) h_sender_sum h_post
  have h_growth := State.addBal_growth postMsgState sender
    ((tx.gas -
        max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost) *
      effectiveGasPrice).toB256
  dsimp only [State.BalGrowth, State.balSum] at h_growth
  apply StateInv.addBal
  · omega
  · exact h_sender_inv

theorem processTransaction_preserves_inv (wa : Adr)
    (hp : c.Preserves wa)
    (benv : Benv) (bout bout' : BlockOutput) (tx : Tx) (i : Nat) (st : Jaune.State)
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) : c.BenvInv wa (benv.withState st) := by
  unfold processTransaction at h_run
  -- `beginTransaction` only refreshes `stat.origState`, which no balance here
  -- reads; project it away so the state/fee terms stay in terms of `benv`.
  simp only [Benv.beginTransaction] at h_run
  rcases Except.bind_eq_ok h_run with ⟨bout0, hbout0, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨validationSender, hrec, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨gasInfo, hval, h_run⟩
  rcases gasInfo with ⟨intrinsicGas, calldataFloorGasCost⟩
  rcases Except.bind_eq_ok h_run with ⟨chk, hcheck, h_run⟩
  rcases chk with ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩
  rcases Except.bind_eq_ok h_run with ⟨state1, hsub, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨msg, hprep, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨pmout, hpm, h_run⟩
  rcases pmout with ⟨state2, txOutput⟩
  rw [Except.mapError_eq_ok_iff] at hval hpm
  rcases Except.bind_eq_ok h_run with ⟨refundCounter, hrefund, h_run⟩
  simp only at h_run
  rcases h_run with ⟨rfl, rfl⟩
  have hsender : sender ≠ wa :=
    -- `beginTransaction` leaves `state` and `createdAccounts` alone, which is
    -- all `InvSolvent` constrains, so the invariant transfers field-wise.
    checkTransaction_sender_ne_of_inv hcheck ⟨h_inv.state, h_inv.ca⟩
  -- `hsub` carries the `beginTransaction` stat record; its debit term is
  -- defeq (not syntactic) to the stated one, which is all `exact` needs.
  have hsub_some :
      (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
          else
            0).toB256 = some state1 :=
    Option.toExcept_eq_ok hsub
  have hstate1 : c.StateInv wa state1 :=
    StateInv.subBal hsender hsub_some (StateInv.incrNonce h_inv.state)
  have horigin :
      ({ transientStorage := Std.TreeMap.empty,
          stat :=
            { origin := sender, gasPrice := effectiveGasPrice,
              gas := tx.gas - intrinsicGas,
              accessListAddresses :=
                Std.HashSet.ofList (benv.stat.coinbase :: List.map Prod.fst tx.accessList),
              accessListStorageKeys :=
                Std.HashSet.ofList
                  (List.map
                    (fun x =>
                      match x with
                      | (adr, keys) => List.map (fun x => (adr, x)) keys)
                    tx.accessList).flatten,
              blobVersionedHashes := blobVersionedHashes, auths := tx.auths,
              indexInBlock := some i, txHash := some (getTxHash tx) } } :
            Tenv).stat.origin ≠ wa := by
    exact hsender
  have hmsg : c.MsgInv wa msg :=
    prepareMessage_preserves_inv hprep hstate1 (by simpa using h_inv.ca) horigin
  have hfork_msg : CoveredFork msg.benv.stat.fork := by
    rw [prepareMessage_benv hprep]
    exact hfork
  have hpm_inv := processMessageCall_preserves_inv hfork_msg hp hpm hmsg
  have hmsg_benv := prepareMessage_benv hprep
  have hsum_le : sum state2.bal ≤ sum state1.bal := by
    have hgas_msg : msg.benv.stat.rules.stateGas = none := by
      rw [prepareMessage_benv hprep]
      exact hfork.rules_stateGas_none
    have h := processMessageCall_sum_le hgas_msg hpm
    rw [hmsg_benv] at h
    exact h
  -- `hval`/`hcheck` carry the `beginTransaction` stat record; the gas-credit
  -- facts only read `rules`/`excessBlobGas`, which are defeq to `benv`'s.
  have hval_benv : validateTransaction benv.stat.rules tx validationSender =
      .ok ⟨intrinsicGas, calldataFloorGasCost⟩ := hval
  have hfee_benv : tx.gas * effectiveGasPrice +
        (if tx.isTypeThree = true then
          calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
        else 0) < 2 ^ 256 :=
    checkTransaction_upfront_lt_modulus hcheck
  have hcredits : c.StateInv wa
      ((state2.addBal sender
          ((tx.gas -
              max (tx.gas - txOutput.gasLeft -
                min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
                calldataFloorGasCost) *
            effectiveGasPrice).toB256).addBal
        benv.stat.coinbase
          (max (tx.gas - txOutput.gasLeft -
              min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
              calldataFloorGasCost *
            (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256) :=
    StateInv.add_transaction_gas_credits hval_benv hfee_benv hsub_some hsum_le
      h_sum hpm_inv.1
  refine ⟨?_, ?_⟩
  · -- on covered forks both settlements take the none lane; unfold to the
    -- matches, align `hsg` to their scrutinee form, and rewrite by it
    have hsg : benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
    simp only [settleSelfdestructs, settleTransactionGas, BenvStat.rules] at hsg ⊢
    simp only [hsg] at ⊢
    exact StateInv.foldl_destroyAccount hpm_inv.2 hcredits
  · simpa [Benv.withState] using h_inv.ca

theorem applyTransactions_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (txis : List (Nat × Tx)) (benv benv' : Benv) (bout bout' : BlockOutput)
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) : c.BenvInv wa benv' := by
  -- list induction over `txis`; each step is `processTransaction_preserves_inv`
  -- (note `processTransaction` threads `Benv`, so track `benv.state`).
  induction txis generalizing benv bout with
  | nil =>
    rw [applyTransactions] at h_run
    obtain ⟨hb, hbo⟩ := Prod.mk.inj (Except.ok.inj h_run)
    subst hb; exact h_inv
  | cons hd tl ih =>
    obtain ⟨i, tx⟩ := hd
    rw [applyTransactions] at h_run
    obtain ⟨⟨st, bout''⟩, h1, h2⟩ := Except.bind_eq_ok h_run
    have hstep := processTransaction_preserves_inv wa hp benv bout bout'' tx i st h1 h_sum h_inv hfork
    have hsum' : sum (benv.withState st).state.bal < 2 ^ 256 := by
      have := processTransaction_sum_le h1 hfork.rules_stateGas_none
      simpa [Benv.withState] using Nat.lt_of_le_of_lt this h_sum
    exact ih (benv.withState st) bout'' h2 hsum' hstep hfork

/-
(1) Difficulty: ★★☆☆☆
(2) Proof plan: unfold the two system-transaction wrappers, build
`c.MsgInv` for the resulting zero-value/no-transfer message from the
`c.BenvInv` hypothesis, and apply `processMessageCall_preserves_inv` and
`processMessageCall_sum_le`.  The wrapper only chooses the target's current
code and otherwise does not alter the starting state.
-/
lemma processUncheckedSystemTransaction_preserves_inv_sum_le (wa : Adr)
    (hp : c.Preserves wa)
    (benv : Benv) (target : Adr) (data : Bytes)
    (st : Jaune.State) (out : MsgCallOutput)
    (h_run : processUncheckedSystemTransaction benv target data = .ok ⟨st, out⟩)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) :
    c.StateInv wa st ∧ sum st.bal ≤ sum benv.state.bal := by
  dsimp [processUncheckedSystemTransaction, processSystemTransaction] at h_run
  -- The system transaction opens on `benv.beginTransaction`; that only
  -- refreshes `stat.origState`, so every field the invariant reads is defeq to
  -- the corresponding field of `benv`.
  have h_msg : c.MsgInv wa
      (processSystemTransactionMsg benv.beginTransaction
        (processSystemTransactionTenv benv.beginTransaction)
        target data (benv.state.getCode target)) := by
    refine ⟨h_inv.state, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨h_inv.ca, ?_⟩
      intro hnil
      have hnil' : (benv.state.getCode wa).toList = [] := by
        simpa only [processSystemTransactionMsg, Benv.beginTransaction] using hnil
      exact (c.sem.ne_nil (by
        rw [← h_inv.state.code, hnil'])) rfl
    · intro _ htarget
      simp only [processSystemTransactionMsg] at htarget ⊢
      subst target
      exact h_inv.state.code
    · intro _ htarget
      simp only [processSystemTransactionMsg] at htarget ⊢
      subst target
      rfl
    · simp [processSystemTransactionMsg]
    · simp [processSystemTransactionMsg]
  have hgas_msg : (processSystemTransactionMsg benv.beginTransaction
    (processSystemTransactionTenv benv.beginTransaction)
    target data (benv.state.getCode target)).benv.stat.rules.stateGas = none :=
    hfork.rules_stateGas_none
  have hsum := processMessageCall_sum_le hgas_msg h_run
  have hfork_msg : CoveredFork (processSystemTransactionMsg benv.beginTransaction
(processSystemTransactionTenv benv.beginTransaction)
target data (benv.state.getCode target)).benv.stat.fork := hfork
  exact ⟨(processMessageCall_preserves_inv hfork_msg hp h_run h_msg).1, hsum⟩

/-
(1) Difficulty: ★★★☆☆
(2) Proof plan: induct on `wds`, generalizing the starting state.  For the
head withdrawal, prove that
`(wd.amount * (10 ^ 9).toB256).toNat = wd.amount.toNat * 10 ^ 9`; the product
cannot wrap because a withdrawal amount is 64-bit.  The head/tail decomposition
of `wdsum` and the global bound then gives the exact pre-sum bound required by
`StateInv.addBal`.  Apply that lemma for the head and feed the resulting sum
identity (or `State.balSum_setBal`) and residual bound to the induction
hypothesis.
-/

lemma processWithdrawalsState_preserves_inv (wa : Adr)
    (st : Jaune.State) (wds : List Withdrawal)
    (h_bound : sum st.bal + wdsum wds < 2 ^ 256)
    (h_inv : c.StateInv wa st) :
    c.StateInv wa (processWithdrawalsState st wds) := by
  induction wds generalizing st with
  | nil => exact h_inv
  | cons wd wds ih =>
    have h_cons : wdsum (wd :: wds) = wd.amount.toNat * 10 ^ 9 + wdsum wds := by
      simp [wdsum]
    rw [h_cons] at h_bound
    have h_val : (wd.amount * (10 ^ 9).toB256).toNat =
        wd.amount.toNat * 10 ^ 9 := by
      have h9 : (10 : Nat) ^ 9 ↾ 256 = 10 ^ 9 := Nat.lo_eq_of_lt (by omega)
      rw [B256.toNat_mul, B256.toNat_toB256, h9, Nat.lo_eq_of_lt (by omega)]
    have h_step : processWithdrawalsState st (wd :: wds) =
        processWithdrawalsState
          (st.addBal wd.recipient (wd.amount * (10 ^ 9).toB256)) wds := rfl
    rw [h_step]
    have hb : sum st.bal + (wd.amount * (10 ^ 9).toB256).toNat < 2 ^ 256 := by
      rw [h_val]; exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right (wd.amount.toNat * 10 ^ 9) (wdsum wds)) (sum st.bal)) h_bound
    have h_sum := sum_addBal_eq st wd.recipient _ hb
    apply ih
    · rw [h_sum, h_val]; omega
    · exact StateInv.addBal hb h_inv

/-
(1) Difficulty: ★★☆☆☆
(2) Proof plan: induction on the request-contract list.  Each checked call
reduces, on its successful branch, to the corresponding unchecked system
transaction; the request-byte accumulation and BAL incorporation are pure
data plumbing.  Thread `createdAccounts` through `Benv.withState` and
compose the sum inequalities.
-/
lemma runRequestContracts_preserves_inv_sum_le (wa : Adr)
    (hp : c.Preserves wa)
    (idx : Nat) (contracts : List (UInt8 × Adr))
    (benv : Benv) (acc : List Bytes) (bal : BalBuilder)
    {st : Jaune.State} {acc' : List Bytes} {bal' : BalBuilder}
    (h_run : runRequestContracts idx contracts benv acc bal = .ok ⟨st, acc', bal'⟩)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) :
    c.StateInv wa st ∧ sum st.bal ≤ sum benv.state.bal := by
  induction contracts generalizing benv acc bal with
  | nil =>
    rw [runRequestContracts] at h_run
    simp only [Except.ok.injEq] at h_run
    obtain ⟨rfl, _, _⟩ := h_run
    exact ⟨h_inv.state, le_refl _⟩
  | cons hd tl ih =>
    obtain ⟨requestType, address⟩ := hd
    rw [runRequestContracts] at h_run
    obtain ⟨⟨state, output⟩, h1, h_run⟩ := Except.bind_eq_ok h_run
    have hu := processUncheckedSystemTransaction_preserves_inv_sum_le wa hp benv
      address [] state output (processCheckedSystemTransaction_to_unchecked h1)
      h_inv hfork
    have h_inv1 : c.BenvInv wa (benv.withState state) :=
      ⟨hu.1, by simpa [Benv.withState] using h_inv.ca⟩
    dsimp only at h_run
    have ih' := ih _ _ _ h_run h_inv1 hfork
    exact ⟨ih'.1, le_trans (by simpa [Benv.withState] using ih'.2) hu.2⟩

/-
(1) Difficulty: ★★☆☆☆
(2) Proof plan: invert `processGeneralPurposeRequests`.  Parsing deposits and
updating the request list do not touch state.  The request-contract fold is
`runRequestContracts_preserves_inv_sum_le`, applied at the decoded run.
-/
lemma processGeneralPurposeRequests_preserves_inv_sum_le (wa : Adr)
    (hp : c.Preserves wa)
    (benv : Benv) (bout : BlockOutput)
    (st : Jaune.State) (bout' : BlockOutput)
    (h_run : processGeneralPurposeRequests benv bout = .ok ⟨st, bout'⟩)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) :
    c.StateInv wa st ∧ sum st.bal ≤ sum benv.state.bal := by
  rw [processGeneralPurposeRequests, processGeneralPurposeRequestsAt] at h_run
  obtain ⟨depositRequests, _, h_run⟩ := Except.bind_eq_ok h_run
  dsimp only at h_run
  obtain ⟨⟨state, allRequests, bal⟩, h_contracts, h_run⟩ := Except.bind_eq_ok h_run
  obtain ⟨hst, _⟩ := Prod.mk.inj (Except.ok.inj h_run)
  subst hst
  exact runRequestContracts_preserves_inv_sum_le wa hp _ _ benv _ _
    h_contracts h_inv hfork

theorem applyBody_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (benv : Benv) (txs : List (Bytes ⊕ Tx)) (wds : List Withdrawal)
    (st : Jaune.State) (bout : BlockOutput)
    (h_run : applyBody benv txs wds = .ok ⟨st, bout⟩)
    (h_wds : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) : c.StateInv wa st := by
  rw [applyBody] at h_run
  simp only at h_run
  rcases Except.bind_eq_ok h_run with ⟨⟨stBeacon, outBeacon⟩, h_beacon, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨lastHash, h_lastHash, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨⟨stHistory, outHistory⟩, h_history, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨decodedTxs, h_decode, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨⟨benvTxs, boutTxs⟩, h_txs, h_requests⟩
  dsimp only at h_history h_txs h_requests
  rw [Except.mapError_eq_ok_iff] at h_beacon h_history
  have h_beacon_inv :=
    processUncheckedSystemTransaction_preserves_inv_sum_le wa hp benv
      beaconRootsAddress benv.stat.parentBeaconBlockRoot.toBytes
      stBeacon outBeacon h_beacon h_inv hfork
  have h_benv_beacon : c.BenvInv wa (benv.withState stBeacon) :=
    ⟨h_beacon_inv.1, by simpa [Benv.withState] using h_inv.ca⟩
  have h_history_inv :=
    processUncheckedSystemTransaction_preserves_inv_sum_le wa hp
      (benv.withState stBeacon) historyStorageAddress lastHash.toBytes
      stHistory outHistory h_history h_benv_beacon hfork
  have h_benv_history :
      c.BenvInv wa ((benv.withState stBeacon).withState stHistory) :=
    ⟨h_history_inv.1, by simpa [Benv.withState] using h_benv_beacon.ca⟩
  have h_hist_bound :
      sum ((benv.withState stBeacon).withState stHistory).state.bal < 2 ^ 256 := by
    have h_beacon_sum : sum stBeacon.bal ≤ sum benv.state.bal := h_beacon_inv.2
    have h_history_sum : sum stHistory.bal ≤ sum stBeacon.bal := by
      simpa [Benv.withState] using h_history_inv.2
    simp only [Benv.withState]
    omega
  have h_txs_inv : c.BenvInv wa benvTxs :=
    applyTransactions_preserves_inv wa hp decodedTxs.putIndex
      ((benv.withState stBeacon).withState stHistory) benvTxs
      _ boutTxs h_txs h_hist_bound h_benv_history hfork
  have h_txs_sum := applyTransactions_sum_le h_txs hfork.rules_stateGas_none
  dsimp [processWithdrawals] at h_requests
  have h_txs_bound : sum benvTxs.state.bal + wdsum wds < 2 ^ 256 := by
    have h_history_sum : sum stHistory.bal ≤ sum stBeacon.bal := by
      simpa [Benv.withState] using h_history_inv.2
    have h_txs_sum' : sum benvTxs.state.bal ≤ sum stHistory.bal := by
      simpa [Benv.withState] using h_txs_sum
    omega
  have h_wds_inv :=
    processWithdrawalsState_preserves_inv wa benvTxs.state wds
      h_txs_bound h_txs_inv.state
  have h_benv_wds : c.BenvInv wa
      (benvTxs.withState (processWithdrawalsState benvTxs.state wds)) :=
    ⟨h_wds_inv, by simpa [Benv.withState] using h_txs_inv.ca⟩
  have hfork_txs : CoveredFork benvTxs.stat.fork := by
    rw [applyTransactions_benvStat_eq h_txs]
    simpa [Benv.withState] using hfork
  -- `h_requests` still runs the request pass and the access-list check after
  -- the withdrawals; invert both binds, then the request pass is `h_req`.
  obtain ⟨⟨stReq, boutReq⟩, h_req, h_requests⟩ := Except.bind_eq_ok h_requests
  obtain ⟨_, _, h_requests⟩ := Except.bind_eq_ok h_requests
  simp only [Except.ok.injEq, Prod.mk.injEq] at h_requests
  obtain ⟨rfl, _⟩ := h_requests
  exact (processGeneralPurposeRequests_preserves_inv_sum_le wa hp
    (benvTxs.withState (processWithdrawalsState benvTxs.state wds))
    _ _ _ h_req h_benv_wds hfork_txs).1

-- The state transition preserves WETH solvency at whichever explicitly named
-- fork it runs. This is the general theorem, and it is general for a reason
-- rather than by luck: `applyBody_preserves_inv` never asks which fork it is
-- running at, because solvency is a statement about how value moves and no
-- fork rule moves value. Everything below -- Prague, an explicitly named
-- fork, a configured chain crossing Osaka and the BPO forks -- is an instance
-- of this one proof.

theorem stateTransitionAt_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (f : Fork)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionAt f ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state)
    (hfork : CoveredFork f) : c.StateInv wa ch'.state := by
  -- invert the typed core behind the byte-identical renderer adapter
  -- (`stateTransitionAt_eq_ok_iff`); the state change is `applyBody`, so
  -- this is `applyBody_preserves_inv` (the block-check helpers don't touch state).
  rw [stateTransitionAt_eq_ok_iff, stateTransitionE] at h_run
  obtain ⟨_, _, h_run⟩ := Except.bind_eq_ok h_run
  obtain ⟨_, _, h_run⟩ := Except.bind_eq_ok h_run
  dsimp only at h_run
  obtain ⟨⟨st, bout⟩, h_ab, h_run⟩ := Except.bind_eq_ok h_run
  dsimp only at h_run
  obtain ⟨_, _, h_run⟩ := Except.bind_eq_ok h_run
  obtain ⟨_, _, h_run⟩ := Except.bind_eq_ok h_run
  rw [← Except.ok.inj h_run]
  exact applyBody_preserves_inv wa hp (initBenv f ch block.header) block.txs
    block.wds st bout h_ab h_wds ⟨h_inv, AdrSet.not_mem_empty⟩ hfork



/-! ### The chain-level rungs -/

theorem stateTransitionUsing_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (cfg : ChainConfig) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionUsing cfg ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state)
    (hcov : ∀ (t : Nat) (f' : Fork), cfg.forkAt t = .ok f' → CoveredFork f') :
    c.StateInv wa ch'.state := by
  -- the configured entry point checks the chain identity first; the invariant
  -- needs neither that fact nor which fork the schedule picked, only that
  -- every fork it can pick is covered.
  rw [stateTransitionUsing] at h_run
  obtain ⟨_, _, h_run⟩ := Except.bind_eq_ok h_run
  obtain ⟨f, hf, h_run⟩ := Except.bind_eq_ok h_run
  have hfork : CoveredFork f := hcov _ _ (Except.mapError_eq_ok_iff.mp hf)
  exact stateTransitionAt_preserves_inv wa hp f ch ch' block h_run h_wds h_inv hfork

/-- Prague is the `f := .prague` instance, and `stateTransition` is
*definitionally* `stateTransitionAt .prague`. -/
theorem stateTransition_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state :=
  stateTransitionAt_preserves_inv wa hp .prague ch ch' block h_run h_wds h_inv
    CoveredFork.prague

/-- Chain-level induction over a configured chain: no sequence of valid blocks
can break the invariant, whatever covered schedule the chain follows and
whichever activations that sequence crosses. -/
theorem chainUsing_preserves_inv (wa : Adr) (hp : c.Preserves wa) (cfg : ChainConfig)
    (ch ch' : BlockChain) (h_reach : BlockChain.ReachUsing cfg ch ch')
    (h_inv : c.StateInv wa ch.state)
    (hcov : ∀ (t : Nat) (f' : Fork), cfg.forkAt t = .ok f' → CoveredFork f') :
    c.StateInv wa ch'.state := by
  induction h_reach with
  | refl => exact h_inv
  | step h_reach' h_bound h_st ih =>
    exact stateTransitionUsing_preserves_inv wa hp cfg _ _ _ h_st h_bound ih hcov

/-- The Prague corollary of the same induction. -/
theorem chain_preserves_inv (wa : Adr) (hp : c.Preserves wa) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state := by
  induction h_reach with
  | refl => exact h_inv
  | step h_reach' h_bound h_st ih =>
    exact stateTransition_preserves_inv wa hp _ _ _ h_st h_bound ih

/-- Preservation through RLP decoding and block-hash checks, at any explicitly
named fork. -/
theorem addBlockToChainAt_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (f : Fork) (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainAt f ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state)
    (hfork : CoveredFork f) : c.StateInv wa ch'.state := by
  -- invert the raw import through Jaune's own bridge, then one
  -- `stateTransitionAt_preserves_inv` step at the decoded block.
  obtain ⟨block, hash, h_rlp, h_size, h_st⟩ := addBlockToChainAt_eq_ok_inl h_run
  exact stateTransitionAt_preserves_inv wa hp f ch ch' block h_st
    (h_wds block hash h_rlp) h_inv hfork

/-- Block import on a configured chain validates the schedule and chain
identity before decoding; once decoding supplies the timestamp the configured
core delegates to the same canonical import. -/
theorem addBlockToChainUsing_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (cfg : ChainConfig) (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainUsing cfg ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state)
    (hcov : ∀ (t : Nat) (f' : Fork), cfg.forkAt t = .ok f' → CoveredFork f') :
    c.StateInv wa ch'.state := by
  unfold addBlockToChainUsing at h_run
  cases hE : addBlockToChainUsingE cfg ch rlp with
  | error failure =>
      rw [hE] at h_run
      simp [ImportOutcome.renderLegacy] at h_run
  | ok outcome =>
      rw [hE] at h_run
      cases outcome with
      | inr rejection =>
          simp [ImportOutcome.renderLegacy] at h_run
      | inl chResult =>
          simp only [ImportOutcome.renderLegacy, Except.ok.injEq,
            Sum.inl.injEq] at h_run
          subst chResult
          unfold addBlockToChainUsingE at hE
          obtain ⟨_, _, hE⟩ := Except.bind_eq_ok hE
          obtain ⟨_, _, hE⟩ := Except.bind_eq_ok hE
          split at hE
          · simp at hE
          · rename_i block hash h_decode
            obtain ⟨f, hf, hE⟩ := Except.bind_eq_ok hE
            obtain ⟨_, h_st⟩ := addBlockToChainCanonicalE_eq_ok_inl hE
            have hfork : CoveredFork f := hcov _ _ (Except.mapError_eq_ok_iff.mp hf)
            exact stateTransitionAt_preserves_inv wa hp f ch ch' block
              (stateTransitionAt_eq_ok_iff.mpr h_st)
              (h_wds block hash (rlpToBlock_eq_ok_iff.mpr h_decode)) h_inv hfork

/-- Prague is the `f := .prague` instance here too. -/
theorem addBlockToChain_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state :=
  addBlockToChainAt_preserves_inv wa hp .prague ch ch' rlp h_run h_wds h_inv
    CoveredFork.prague

theorem preserves_inv_sem (c : ContractSpecSem) (ca : Adr) (body : c.Sound ca) :
    c.Preserves ca := by
  intro sevm devm exn hfork exc h_code h_wf h_pc
  refine preserves_lift_sem c ca (c.PreWf ca) (fun h => h.pre)
    (fun h_ne h => ⟨h, fun hc => absurd hc h_ne⟩)
    (fun h_wf' h => ⟨h, fun _ => h_wf'⟩) ?_ sevm devm exn hfork exc h_code ⟨h_pc, h_wf⟩
  intro sevm' pre' post' h_run' h_eq' h_ih' h_pre'
  exact body h_pre'.2 h_run' h_eq'
    (fun pc'' sevm'' pre'' post'' hex hd hat hfork_n hpw =>
      h_ih' pc'' sevm'' pre'' post'' hex hd hat ⟨hpw, hfork_n⟩)
    (h_pre'.1.wf h_eq') h_pre'.1.pre

/-- The premise-free frame-level ladder: the same `lift_inv` plumbing at
`σ := c.Pre ca`, so no memory premise is manufactured anywhere and none
reaches the frame theorem.  The obligation's deeper-frame hypothesis is still
phrased at `PreWf`, which is strictly less than what this instantiation
delivers, so it is weakened on the way in. -/
theorem preserves_noMem_sem (c : ContractSpecSem) (ca : Adr) (body : c.SoundNoMem ca) :
    c.PreservesNoMem ca := by
  intro sevm devm exn hfork exc h_code h_pc
  refine preserves_lift_sem c ca (c.Pre ca) (fun h => h) (fun _ h => h)
    (fun _ h => h) ?_ sevm devm exn hfork exc h_code h_pc
  intro sevm' pre' post' h_run' h_eq' h_ih' h_pre'
  exact body h_pre'.2 h_run' h_eq'
    (fun pc'' sevm'' pre'' post'' hex hd hat hfork_n hpw =>
      h_ih' pc'' sevm'' pre'' post'' hex hd hat ⟨hpw.pre, hfork_n⟩)
    h_pre'.1

/-- The `exec` counterpart: with sufficiency proved in Jaune there is no fuel
to quantify away, so the hypothesis is a plain equation about the interpreter. -/
theorem exec_preserves_inv_sem (c : ContractSpecSem) (ca : Adr) (hp : c.Preserves ca)
    (sevm : Sevm) (pre post : Devm)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_run : exec ⟨0, sevm, pre⟩ = .ok post)
    (h_code : sevm.currentTarget = ca → some sevm.code.toList = c.sem.image)
    (h_wf : sevm.currentTarget = ca → Mem.Wf pre.memory)
    (h_pc : c.Pre ca sevm pre) : c.Post ca sevm post := by
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre (.ok post)).mpr h_run
  exact hp sevm pre post hfork exc h_code h_wf h_pc
/-- The `exec` counterpart of `PreservesNoMem`, with no memory premise. -/
theorem exec_preserves_noMem_sem (c : ContractSpecSem) (ca : Adr)
    (hp : c.PreservesNoMem ca)
    (sevm : Sevm) (pre post : Devm)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_run : exec ⟨0, sevm, pre⟩ = .ok post)
    (h_code : sevm.currentTarget = ca → some sevm.code.toList = c.sem.image)
    (h_pc : c.Pre ca sevm pre) : c.Post ca sevm post := by
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre (.ok post)).mpr h_run
  exact hp sevm pre post hfork exc h_code h_pc


end ContractSpecSem

end Blanc
