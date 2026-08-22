import Blanc.LidoCircuitBreakerHistory

/-!
# Registry integrity through arbitrary histories — frame join and history ladder

The Registry-mutating endpoints, the open-contract frame theorem, and the
specialization of the landed generic ladder up to chain reachability.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-! ## Worked example: the memory invariant inside a `FuncSound` obligation

Throwaway; delete it once the Registry-mutating endpoints land.  It witnesses
one thing: `ContractSpec.FuncSound` now hands a target `Mem.Wf` for its entry
state, so the target may take the write step that carrying a memory *image*
requires and that was unreachable at this altitude before.  `Mem.write`'s
growth branch reallocates to `ceil32 (n + ys.length)` and `Array.copyD` drops
whatever does not fit, so without the invariant a write silently truncates the
materialised array and destroys the image; `Mem.Reads.write` is exactly the
step the invariant buys, and here it is discharged from the obligation's own
hypotheses with no extra premise on the target. -/
private theorem funcSound_memWf_available
    {dp : DeployParams} {ca : Adr} {f : Func}
    (h : ∀ {sevm : Sevm} {s r : Devm},
      sevm.currentTarget = ca →
      (registrySpec dp).Pre ca sevm s →
      ( ∀ (img : Bytes) (n : Nat) (ys : Bytes),
          Mem.Reads s.memory img →
          Mem.Reads (s.memory.write n ys) (Bytes.writeAt img n ys) ) →
      Exec.InvDepth sevm.depth ca (registrySpec dp).prog
        ((registrySpec dp).PreWf ca) ((registrySpec dp).Post ca) →
      Func.Run ((registrySpec dp).prog.main :: aux) sevm s f r →
      (registrySpec dp).Post ca sevm r) :
    (registrySpec dp).FuncSound ca aux f := by
  intro sevm s r h_ct h_pre h_wf h_ih h_run
  exact h h_ct h_pre
    (fun _ n ys h_reads => Mem.Reads.write h_wf h_reads n ys) h_ih h_run

theorem registrySpec_sound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).Sound ca := by
  sorry

theorem registrySpec_preserves (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).Preserves ca :=
  ContractSpec.preserves_inv (registrySpec dp) ca (registrySpec_sound dp ca)

/-! ## Messages, transactions, blocks and histories -/

theorem processMessageCall_preserves_registryStable (dp : DeployParams)
    {ca : Adr} {msg : Msg} {st' : Jaune.State} {out : MsgCallOutput}
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h_inv : (registrySpec dp).MsgInv ca msg) :
    RegistryStable dp ca st' :=
  (registryStable_iff_stateInv dp ca st').mpr
    (ContractSpec.processMessageCall_preserves_inv (registrySpec_preserves dp ca) h_run h_inv).1

theorem processTransaction_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (benv : Benv) (bout bout' : BlockOutput) (tx : Tx) (i : Nat)
    (st : Jaune.State)
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_fresh : ca ∉ benv.createdAccounts)
    (h_stable : RegistryStable dp ca benv.state) :
    RegistryStable dp ca st :=
  (registryStable_iff_stateInv dp ca st).mpr
    (ContractSpec.processTransaction_preserves_inv ca (registrySpec_preserves dp ca) benv bout
      bout' tx i st h_run h_sum
      ⟨(registryStable_iff_stateInv dp ca benv.state).mp h_stable, h_fresh⟩).state

theorem applyTransactions_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (txis : List (Nat × Tx)) (benv benv' : Benv)
    (bout bout' : BlockOutput)
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_fresh : ca ∉ benv.createdAccounts)
    (h_stable : RegistryStable dp ca benv.state) :
    RegistryStable dp ca benv'.state :=
  (registryStable_iff_stateInv dp ca benv'.state).mpr
    (ContractSpec.applyTransactions_preserves_inv ca (registrySpec_preserves dp ca) txis benv
      benv' bout bout' h_run h_sum
      ⟨(registryStable_iff_stateInv dp ca benv.state).mp h_stable, h_fresh⟩).state

theorem stateTransitionWith_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (rules : ForkRules) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionWith rules ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_stable : RegistryStable dp ca ch.state) :
    RegistryStable dp ca ch'.state :=
  (registryStable_iff_stateInv dp ca ch'.state).mpr
    (ContractSpec.stateTransitionWith_preserves_inv ca (registrySpec_preserves dp ca) rules ch
      ch' block h_run h_wds ((registryStable_iff_stateInv dp ca ch.state).mp h_stable))

theorem stateTransitionUsing_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (cfg : ChainConfig) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionUsing cfg ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_stable : RegistryStable dp ca ch.state) :
    RegistryStable dp ca ch'.state :=
  (registryStable_iff_stateInv dp ca ch'.state).mpr
    (ContractSpec.stateTransitionUsing_preserves_inv ca (registrySpec_preserves dp ca) cfg ch
      ch' block h_run h_wds ((registryStable_iff_stateInv dp ca ch.state).mp h_stable))

theorem stateTransition_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_stable : RegistryStable dp ca ch.state) :
    RegistryStable dp ca ch'.state :=
  (registryStable_iff_stateInv dp ca ch'.state).mpr
    (ContractSpec.stateTransition_preserves_inv ca (registrySpec_preserves dp ca) ch ch' block
      h_run h_wds ((registryStable_iff_stateInv dp ca ch.state).mp h_stable))

/-- The headline configured-chain theorem: from an exact-runtime stable
checkpoint, every state reachable by the configured valid-chain relation is
still stable. -/
theorem chainUsing_preserves_registryStable (dp : DeployParams) (ca : Adr)
    (cfg : ChainConfig) (checkpoint future : BlockChain)
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    RegistryStable dp ca future.state :=
  (registryStable_iff_stateInv dp ca future.state).mpr
    (ContractSpec.chainUsing_preserves_inv ca (registrySpec_preserves dp ca) cfg checkpoint
      future reach ((registryStable_iff_stateInv dp ca checkpoint.state).mp stable))

theorem chain_preserves_registryStable (dp : DeployParams) (ca : Adr)
    (checkpoint future : BlockChain)
    (reach : BlockChain.Reach checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    RegistryStable dp ca future.state :=
  (registryStable_iff_stateInv dp ca future.state).mpr
    (ContractSpec.chain_preserves_inv ca (registrySpec_preserves dp ca) checkpoint future reach
      ((registryStable_iff_stateInv dp ca checkpoint.state).mp stable))

/-! ## The external-call transport lemma -/

/-- A compiled program is never an EIP-7702 delegation designator, so an
address holding one resolves no delegation.  This is the `getDelegatedCodeAddress`
face of `not_delegation_of_compile`; the ladder's `CALL`/`STATICCALL` inversions
state the code-selection disjunct in terms of the former. -/
private lemma getDelegatedCodeAddress_of_compile {p : Prog} {code : ByteArray}
    (h : some code.toList = Prog.compile p) :
    getDelegatedCodeAddress code = none := by
  dsimp only [getDelegatedCodeAddress]
  rw [if_neg (not_delegation_of_compile h)]

/-- **The child frame, and the induction hypothesis.**  The frame a `CALL` or a
`STATICCALL` opens from the contract's own frame preserves Registry coherence.

No premise restricts the callee.  A callee at some other address leaves
`sevm.currentTarget`'s storage alone because accounts are separate, and the
value transfer moves balances only; a callee that re-enters *this* contract at
*this* address runs the compiled runtime one level deeper, which is exactly the
case `ih` exists to discharge.  The delegation branch is resolved rather than
excluded: a designator cannot sit at the contract's own address, because that
address holds a compiled program.

Shared by the two operand shapes: `CALL` instantiates it with the popped value
and `isStatic := false`, `STATICCALL` with `value := 0` and
`isStatic := true`. -/
private lemma coherent_of_childFrame {dp : DeployParams} {sevm : Sevm}
    {s parent child : Devm} {xl : Xlot} {gas : Nat} {value : B256}
    {target : Adr} {del isStatic : Bool} {code : ByteArray} {cd : Bytes}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget (runtime dp)
      ((registrySpec dp).PreWf sevm.currentTarget)
      ((registrySpec dp).Post sevm.currentTarget))
    (h_depth : 0 < sevm.depth)
    (h_pstate : parent.state = s.state)
    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile (runtime dp))
    (h_coh : RegistryCoherent (Devm.getStor s sevm.currentTarget))
    (h_sel :
      (getDelegatedCodeAddress (s.getCode target) = none ∧
        code = s.getCode target ∧ del = false) ∨
      (∃ d, getDelegatedCodeAddress (s.getCode target) = some d ∧
        code = s.getCode d ∧ del = true))
    (h_fill : Xlot.Filled xl)
    (h_pm : ProcessMessage
      (callMsg sevm parent gas value sevm.currentTarget target target true isStatic cd code del)
      xl (.ok child)) :
    RegistryCoherent (Devm.getStor child sevm.currentTarget) := by
  -- name the child message and keep only the projections the walk needs
  obtain ⟨childMsg, h_pm, hc_state, hc_caller, hc_value, hc_ct, hc_ca, hc_code,
      hc_depth, hc_stv⟩ :
      ∃ m : Msg, ProcessMessage m xl (.ok child) ∧
        m.benv.state = s.state ∧
        m.caller = sevm.currentTarget ∧
        m.value = value ∧
        m.currentTarget = target ∧
        m.codeAddress = some target ∧
        m.code = code ∧
        m.depth = sevm.depth - 1 ∧
        m.shouldTransferValue = true :=
    ⟨_, h_pm, h_pstate, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- unpack the frame into transfer, code execution and settlement
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp h_pm
  unfold FrameBody at hbody
  rcases eq_bt : childMsg.benvAfterTransfer with e | benv' <;> rw [eq_bt] at hbody
  · rw [hbody.2, processMessage.settle_error] at hset
    cases hset
  have run_ec : ExecuteCode (childMsg.withBenv benv') xl r0 := hbody
  -- the value transfer performed before the sub-message run: balances only
  rcases of_benvAfterTransfer hc_stv eq_bt with ⟨st_mid, h_sub, hB⟩
  rw [hc_state, hc_caller, hc_value] at h_sub
  rcases of_state_transfer_fields (callee := target) h_sub with
    ⟨h_t_stor, h_t_code, -, -, -⟩
  have hBs : benv'.state = st_mid.addBal target value := by
    rw [hB, hc_ct, hc_value]; rfl
  -- resolve the settlement : rollback, or a clean sub-message result
  obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
  subst h_r0
  rcases h_settle with ⟨h_err2, h_if⟩ | ⟨h_err2, h_if⟩
  · -- the sub-message failed : the world rolled back to the pre-transfer state
    rw [getStor_eq_of_state_eq (show child.state = s.state by
      rw [← h_if]; exact hc_state)]
    exact h_coh
  · -- the sub-message succeeded
    have h_if' := h_if.symm
    subst h_if'
    have h_wb_ca : (childMsg.withBenv benv').codeAddress = some target := hc_ca
    rcases of_executeCode_someCode h_wb_ca run_ec with
      ⟨-, -, h_he⟩ | ⟨-, ex3, h_xl_some, h_he⟩
    · -- the callee is a precompile : no sub-execution, only the transfer
      have h_child_state : child.state = benv'.state := by
        have h := state_of_executePrecomp_ok h_he h_err2
        rw [h]; rfl
      have h_stor_eq : Devm.getStor child sevm.currentTarget
          = Devm.getStor s sevm.currentTarget := by
        show (child.state.get sevm.currentTarget).stor
          = (s.state.get sevm.currentTarget).stor
        rw [h_child_state, hBs]
        exact h_t_stor sevm.currentTarget
      rw [h_stor_eq]
      exact h_coh
    · -- the callee is a regular account : a sub-execution takes place
      rw [h_xl_some] at h_fill
      dsimp only [Xlot.Filled] at h_fill
      rcases ex3 with ⟨err3, d3⟩ | child3
      · -- a sub-execution error contradicts the clean sub-message result
        rcases of_handleError_err h_he with ⟨evm4, h_ok4, h_some4, -⟩ | ⟨e, h_err4⟩
        · have h_ok4 := Except.ok.inj h_ok4
          rw [← h_ok4] at h_some4
          exact absurd h_some4 h_err2
        · cases h_err4
      simp only [executeCode.handleError] at h_he
      have h_he := (Except.ok.inj h_he).symm
      subst h_he
      obtain ⟨ex_sub⟩ := h_fill
      have h_sd_state : (initDevm (childMsg.withBenv benv')).state = benv'.state := rfl
      have h_ss_ct : (initSevm (childMsg.withBenv benv')).currentTarget = target := hc_ct
      -- the contract's own code survives the transfer
      have h_code_at :
          some ((initDevm (childMsg.withBenv benv')).getCode sevm.currentTarget).toList
            = Prog.compile (runtime dp) := by
        show some ((initDevm (childMsg.withBenv benv')).state.get
          sevm.currentTarget).code.toList = Prog.compile (runtime dp)
        rw [h_sd_state, hBs, h_t_code sevm.currentTarget]
        exact h_code
      -- the target-program invariant for the sub-execution
      have h_at : Prog.At (runtime dp) sevm.currentTarget 0
          (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv')) := by
        refine ⟨h_code_at, ?_⟩
        intro h_eq_ct
        rw [h_ss_ct] at h_eq_ct
        refine ⟨?_, rfl⟩
        show some (initSevm (childMsg.withBenv benv')).code.toList
          = Prog.compile (runtime dp)
        have h_code_c : (initSevm (childMsg.withBenv benv')).code = code := hc_code
        have h_tc : s.getCode target = s.getCode sevm.currentTarget := by rw [h_eq_ct]
        rw [h_code_c]
        rcases h_sel with ⟨-, h_ce, -⟩ | ⟨d, h_some, -, -⟩
        · rw [h_ce, h_tc]; exact h_code
        · rw [h_tc, getDelegatedCodeAddress_of_compile h_code] at h_some
          cases h_some
      -- the sub-execution runs strictly deeper
      have h_depth_lt : (initSevm (childMsg.withBenv benv')).depth < sevm.depth := by
        have h_dep : (initSevm (childMsg.withBenv benv')).depth = sevm.depth - 1 := hc_depth
        rw [h_dep]; omega
      -- the precondition holds at the sub-message's initial machine
      have h_gs : Devm.getStor (initDevm (childMsg.withBenv benv')) sevm.currentTarget
          = Devm.getStor s sevm.currentTarget := by
        show ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).stor
          = (s.state.get sevm.currentTarget).stor
        rw [h_sd_state, hBs]
        exact h_t_stor sevm.currentTarget
      have h_inv : RegistryCoherent
          (Devm.getStor (initDevm (childMsg.withBenv benv')) sevm.currentTarget) := by
        rw [h_gs]; exact h_coh
      have h_precond : (registrySpec dp).Pre sevm.currentTarget
          (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv')) :=
        ⟨h_code_at, trivial, fun _ => h_inv, fun _ => h_inv⟩
      -- apply the induction hypothesis
      have hpost : (registrySpec dp).Post sevm.currentTarget
          (initSevm (childMsg.withBenv benv')) child :=
        ih 0 (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv'))
          (.ok child) ex_sub h_depth_lt h_at ⟨h_precond, fun _ => Mem.wf_empty⟩
      exact hpost.inv

/-- **The `CALL` transport lemma.**  One arbitrary `CALL` issued from the
contract's own frame preserves Registry coherence, and returns the parent's
stack shape so the caller's walk can resume.

The seven operands are arbitrary and no premise restricts the callee: the
target address, its code, the forwarded value and the memory windows are all
whatever the walk put on the stack.  The three ways the call can fail without
entering a frame — the balance guard, the depth guard, and a child frame that
settled with an error — are the inversion's first disjunct, which pins the
caller's world unchanged; the frame that does open is handed to
`coherent_of_childFrame`. -/
theorem coherent_of_call {dp : DeployParams} {sevm : Sevm} {s sf : Devm}
    {g w v ii is oi os : B256} {xs : Stack}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget (runtime dp)
      ((registrySpec dp).PreWf sevm.currentTarget)
      ((registrySpec dp).Post sevm.currentTarget))
    (hp : (g :: w :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile (runtime dp))
    (h_coh : RegistryCoherent (Devm.getStor s sevm.currentTarget))
    (h_run : Ninst.Run sevm s call sf) :
    RegistryCoherent (Devm.getStor sf sevm.currentTarget) ∧
      ∃ b, ((b :: xs) <<+ sf.stack) := by
  rcases of_run_call_val_with_depth_frame hp h_run with ⟨h_stk, h_world⟩ | h_enter
  · -- no frame opened : the caller's world is the one it entered the CALL with
    refine ⟨?_, 0, h_stk⟩
    rw [← h_world.getStor sevm.currentTarget]
    exact h_coh
  · obtain ⟨parent, child, xl, del, code, avail, pc, -, h_dep, h_sstk, h_pst,
      -, -, -, h_sel, h_fill, h_pm, -, -, h_sfst, -, -, h_sfstk⟩ := h_enter
    rw [h_sstk] at hp
    replace hp := cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
      (cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
        (cons_pref_cons_inv hp))))))
    refine ⟨?_, 1, ?_⟩
    · rw [getStor_eq_of_state_eq h_sfst sevm.currentTarget]
      exact coherent_of_childFrame ih h_dep h_pst h_code h_coh h_sel h_fill h_pm
    · rw [h_sfstk]
      exact pref_cons hp

/-- **The `STATICCALL` transport lemma.**  The same statement for the
six-operand static form, which carries no value word: the operands are gas,
target, input offset, input size, output offset and output size.  The frame it
opens is the same one, entered with `value = 0` and the static flag set, so the
child argument is shared verbatim. -/
theorem coherent_of_statcall {dp : DeployParams} {sevm : Sevm} {s sf : Devm}
    {g t ii is oi os : B256} {xs : Stack}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget (runtime dp)
      ((registrySpec dp).PreWf sevm.currentTarget)
      ((registrySpec dp).Post sevm.currentTarget))
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile (runtime dp))
    (h_coh : RegistryCoherent (Devm.getStor s sevm.currentTarget))
    (h_run : Ninst.Run sevm s statcall sf) :
    RegistryCoherent (Devm.getStor sf sevm.currentTarget) ∧
      ∃ b, ((b :: xs) <<+ sf.stack) := by
  rcases of_run_statcall_val_with_depth hp h_run with ⟨h_stk, h_world, -⟩ | h_enter
  · refine ⟨?_, 0, h_stk⟩
    rw [← h_world.getStor sevm.currentTarget]
    exact h_coh
  · obtain ⟨parent, child, xl, del, code, avail, h_dep, h_sstk, h_pst, -,
      h_sel, h_fill, h_pm, -, -, h_sfst, -, -, h_sfstk⟩ := h_enter
    rw [h_sstk] at hp
    replace hp := cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
      (cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv hp)))))
    refine ⟨?_, 1, ?_⟩
    · rw [getStor_eq_of_state_eq h_sfst sevm.currentTarget]
      exact coherent_of_childFrame ih h_dep h_pst h_code h_coh h_sel h_fill h_pm
    · rw [h_sfstk]
      exact pref_cons hp

end LidoCircuitBreaker

end Blanc
