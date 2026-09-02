import Blanc.LidoCircuitBreakerHistoryEndpoints

/-!
# Registry integrity through arbitrary histories — frame join and history ladder

The Registry-mutating endpoints, the open-contract frame theorem, and the
specialization of the landed generic ladder up to chain reachability.

Both Registry-mutating obligations are closed here, and with them
`registrySpec_sound`.  `pause`'s post-kernel continuation needs the contract's
own compiled program at the state that issues its two yields; the kernel
extraction now carries that code fact to the boundary before the event suffix,
and the suffix is peeled here to move it the rest of the way.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-! ## Walk-altitude plumbing: memory images and the contract's own code

Three bridges the two Registry-mutating endpoints need and the landed chain
does not supply.  None of them mentions the contract. -/

/-- Every machine memory has an image: its own materialised backing array.
`Mem.Reads` compares with `getD` on both sides, so the bytes past the array
are zero on both, and no well-formedness is needed to name the image. -/
private theorem mem_reads_data (μ : Mem) : Mem.Reads μ μ.data.toList := by
  intro index
  by_cases bound : index < μ.data.size <;>
    simp [Array.getD, bound, List.getD_eq_getElem?_getD]

/-- The run-level bridge from an `mstoreAt` fragment to `Mem.write`.  This is
the step the `Mem.Wf` binder buys: `Mem.write`'s growth branch reallocates to
`ceil32 (n + ys.length)` and `Array.copyD` drops whatever does not fit, so
without well-formedness a write silently truncates the materialised array and
destroys the image. -/
private theorem mstoreAt_image {sevm : Sevm} {pre post : Devm} {xs : Stack}
    {img : Bytes} {word value : B256}
    (hp : value :: xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (run : Line.Run sevm pre (mstoreAt word) post) :
    xs <<+ post.stack ∧ Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (Bytes.writeAt img (word * 32).toNat value.toBytes) := by
  rcases of_run_mstoreAt_val run hp with ⟨hp', hm⟩
  refine ⟨hp', ?_, ?_⟩
  · rw [hm]; exact hwf.write _ _
  · rw [hm]; exact Mem.Reads.write hwf hr _ _

/-- Successful-run code preservation for one nonterminal instruction, for
every instruction: the relational masters cover the `CALL` and `CREATE`
families too, so this needs no case analysis at the use site. -/
private theorem ninst_codePreserve (n : Ninst) :
    Ninst.Effect Devm.CodePreserve n :=
  Ninst.effect_of_effectRec codePreserve_refl_trans.1 codePreserve_refl_trans.2
    Ninst.codePreserve_effectRec Jinst.codePreserve_effect
    Linst.codePreserve_effect n

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
    {target cadr : Adr} {del isStatic : Bool} {code : ByteArray} {cd : Bytes}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget (runtime dp)
      ((registrySpec dp).PreWf sevm.currentTarget)
      ((registrySpec dp).Post sevm.currentTarget))
    (h_depth : 0 < sevm.depth)
    (h_pstate : parent.state = s.state)
    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile (runtime dp))
    (h_coh : RegistryCoherent (Devm.getStor s sevm.currentTarget))
    (h_sel :
      (getDelegatedCodeAddress (s.getCode target) = none ∧
        cadr = target ∧ code = s.getCode target ∧ del = false) ∨
      (∃ d, getDelegatedCodeAddress (s.getCode target) = some d ∧
        cadr = d ∧ code = s.getCode d ∧ del = true))
    (h_fill : Xlot.Filled xl)
    (h_pm : ProcessMessage
      (callMsg sevm parent gas value sevm.currentTarget target cadr true isStatic cd code del)
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
        m.codeAddress = some cadr ∧
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
    have h_wb_ca : (childMsg.withBenv benv').codeAddress = some cadr := hc_ca
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
        rcases h_sel with ⟨-, -, h_ce, -⟩ | ⟨d, h_some, -, -, -⟩
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
  · obtain ⟨parent, child, xl, del, na, code, avail, pc, -, h_dep, h_sstk,
      h_pst, -, -, -, h_sel, h_fill, h_pm, -, -, h_sfst, -, -, h_sfstk⟩ := h_enter
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
theorem coherent_of_staticcall {dp : DeployParams} {sevm : Sevm} {s sf : Devm}
    {g t ii is oi os : B256} {xs : Stack}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget (runtime dp)
      ((registrySpec dp).PreWf sevm.currentTarget)
      ((registrySpec dp).Post sevm.currentTarget))
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile (runtime dp))
    (h_coh : RegistryCoherent (Devm.getStor s sevm.currentTarget))
    (h_run : Ninst.Run sevm s staticcall sf) :
    RegistryCoherent (Devm.getStor sf sevm.currentTarget) ∧
      ∃ b, ((b :: xs) <<+ sf.stack) := by
  rcases of_run_staticcall_val_with_depth hp h_run with ⟨h_stk, h_world, -⟩ | h_enter
  · refine ⟨?_, 0, h_stk⟩
    rw [← h_world.getStor sevm.currentTarget]
    exact h_coh
  · obtain ⟨parent, child, xl, del, na, code, avail, h_dep, h_sstk, h_pst, -,
      h_sel, h_fill, h_pm, -, -, h_sfst, -, -, h_sfstk⟩ := h_enter
    rw [h_sstk] at hp
    replace hp := cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
      (cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv hp)))))
    refine ⟨?_, 1, ?_⟩
    · rw [getStor_eq_of_state_eq h_sfst sevm.currentTarget]
      exact coherent_of_childFrame ih h_dep h_pst h_code h_coh h_sel h_fill h_pm
    · rw [h_sfstk]
      exact pref_cons hp

/-! ## The two Registry-mutating endpoints

Both stage the shared kernel's four scratch words and tail-jump to it, so both
have to carry the memory invariant across a *writing* prefix before the landed
kernel chain will accept them. -/

/-- `setPauserSlot` is index 14, and `aux`'s fourteenth entry is the shared
Registry mutation kernel. -/
theorem get_setPauserSlot (dp : DeployParams) :
    ((runtime dp).main :: aux)[setPauserSlot]? = some setPauserKernel := rfl

private theorem coherent_of_stor_eq {s s' : Devm} {ct : Adr}
    (h : Devm.getStor s = Devm.getStor s')
    (hcoh : RegistryCoherent (Devm.getStor s ct)) :
    RegistryCoherent (Devm.getStor s' ct) := by
  rw [← congrFun h ct]; exact hcoh

private theorem wf_of_mem_eq {s s' : Devm} (h : s.memory = s'.memory)
    (hwf : Mem.Wf s.memory) : Mem.Wf s'.memory := by rw [← h]; exact hwf

/-- The calldata guard's own conclusion, in the Registry's vocabulary:
`checkNonAddress` clears exactly the words below `2 ^ 160`, which is
`canonicalAddress`.  This is the step that keeps a staged word inside the
domain on which the Registry slot functions are injective. -/
private theorem canonicalAddress_of_validAdr {w : B256} (h : ValidAdr w) :
    canonicalAddress w := by
  obtain ⟨a, rfl⟩ := h
  exact canonicalAddress_toB256 a

/-- Reading back the word just written at its own offset. -/
private theorem read_writeAt_self (img : Bytes) (word value : B256) :
    Bytes.toB256
      ((Bytes.writeAt img (word * 32).toNat value.toBytes).sliceD
        (word * 32).toNat 32 0) = value := by
  rw [show (32 : Nat) = value.toBytes.length from
      (B256.length_toBytes value).symm,
    Bytes.sliceD_writeAt]
  exact B256.toB256_toBytes value

/-- A later write at a strictly higher word leaves an earlier read alone. -/
private theorem read_writeAt_before {img : Bytes} (word other value : B256)
    {v : B256} (hoff : (word * 32).toNat + 32 ≤ (other * 32).toNat)
    (h : Bytes.toB256 (img.sliceD (word * 32).toNat 32 0) = v) :
    Bytes.toB256
      ((Bytes.writeAt img (other * 32).toNat value.toBytes).sliceD
        (word * 32).toNat 32 0) = v := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hoff]
  exact h

/-- The staging offsets, computed once rather than re-established at every use.

`mstoreAt w` writes at byte offset `w * 32`, and the staged words are the
literals `targetWord = 16`, `newPauserWord = 17`, `previousPauserWord = 18`
and `continuationWord = 19`.  So every "earlier word, later word" side
condition of `read_writeAt_before` along the register and unregister prologues
is one closed comparison between two byte offsets.  Each offset is settled
here by `rfl` and the comparison by `omega`, which keeps these side conditions
off any evaluation path and out of proof positions that carry a whole
dispatcher walk in their context. -/
private theorem target_before_newPauser :
    (targetWord * 32).toNat + 32 ≤ (newPauserWord * 32).toNat := by
  have hword : (targetWord * 32).toNat = 512 := rfl
  have hother : (newPauserWord * 32).toNat = 544 := rfl
  omega

/-- `targetWord` is staged two words below `previousPauserWord`. -/
private theorem target_before_previousPauser :
    (targetWord * 32).toNat + 32 ≤ (previousPauserWord * 32).toNat := by
  have hword : (targetWord * 32).toNat = 512 := rfl
  have hother : (previousPauserWord * 32).toNat = 576 := rfl
  omega

/-- `targetWord` is staged three words below `continuationWord`. -/
private theorem target_before_continuation :
    (targetWord * 32).toNat + 32 ≤ (continuationWord * 32).toNat := by
  have hword : (targetWord * 32).toNat = 512 := rfl
  have hother : (continuationWord * 32).toNat = 608 := rfl
  omega

/-- `newPauserWord` is staged one word below `previousPauserWord`. -/
private theorem newPauser_before_previousPauser :
    (newPauserWord * 32).toNat + 32 ≤ (previousPauserWord * 32).toNat := by
  have hword : (newPauserWord * 32).toNat = 544 := rfl
  have hother : (previousPauserWord * 32).toNat = 576 := rfl
  omega

/-- `newPauserWord` is staged two words below `continuationWord`. -/
private theorem newPauser_before_continuation :
    (newPauserWord * 32).toNat + 32 ≤ (continuationWord * 32).toNat := by
  have hword : (newPauserWord * 32).toNat = 544 := rfl
  have hother : (continuationWord * 32).toNat = 608 := rfl
  omega

/-- The branch flag the register prologue reads back is the literal `1`, so
the `iszero` it feeds cannot take the nonzero arm. -/
private theorem flag_one_ne_zero : (1 : B256) ≠ 0 :=
  fun h => B256.zero_ne_one h.symm

/-- **`registerPauser` preserves Registry coherence.**  The admin path stages
the target, the new pauser, a zero previous-pauser and the zero continuation
word, then tail-jumps to the shared kernel; the landed chain carries the
witness through the kernel, the event suffix and the whole register
continuation, including its checked-expiry panic arm.  Every guard arm is a
custom-error reverter, and each is storage-silent. -/
private theorem coherent_registerPauser (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    (hwf : Mem.Wf s.memory)
    (hcoh : RegistryCoherent (Devm.getStor s sevm.currentTarget))
    (hrun : Func.Run ((runtime dp).main :: aux) sevm s (registerPauser dp) r) :
    RegistryCoherent (Devm.getStor r sevm.currentTarget) := by
  have herror : ((runtime dp).main :: aux)[pausableZeroErrorSlot]? =
    some pausableZeroError := rfl
  have happend : ((runtime dp).main :: aux)[appendTargetSlot]? =
    some appendTarget := rfl
  have hafter : ((runtime dp).main :: aux)[afterOldPauserSlot]? =
    some afterOldPauser := rfl
  have hremove : ((runtime dp).main :: aux)[removeTargetSlot]? =
    some removeTarget := rfl
  have hfinish : ((runtime dp).main :: aux)[finishSetPauserSlot]? =
    some finishSetPauser := rfl
  have hregisterLookup : ((runtime dp).main :: aux)[registerAfterSetSlot]? =
    some registerAfterSet := rfl
  have hpauseLookup : ((runtime dp).main :: aux)[pauseAfterSetSlot]? =
    some pauseAfterSet := rfl
  have hpanicLookup := get_arithmeticPanicSlot dp
  simp only [registerPauser, requireStaticArgs, canonicalAddressArg,
    onlyAdmin, pushDeployWord] at hrun
  -- (1) the static-argument guard
  rcases of_run_next hrun with ⟨a₁, q₁, hrun⟩
  rcases of_run_next hrun with ⟨a₂, q₂, hrun⟩
  rcases of_run_next hrun with ⟨a₃, q₃, hrun⟩
  rcases of_run_branch_revert hrun with ⟨a₄, p₄, hrun⟩
  have hS : Devm.getStor s = Devm.getStor a₄ :=
    ((Ninst.Hinv.inv (f := Devm.getStor) q₁).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) q₂).trans
        (Ninst.Hinv.inv (f := Devm.getStor) q₃))).trans (PopBurn.Inv.inv p₄)
  have hM : s.memory = a₄.memory :=
    ((Ninst.Hinv.inv (f := Devm.memory) q₁).trans
      ((Ninst.Hinv.inv (f := Devm.memory) q₂).trans
        (Ninst.Hinv.inv (f := Devm.memory) q₃))).trans p₄.memory
  -- (2) the first canonical-address guard
  refine run_prepend_elim _ (arg 0 ++ checkNonAddress) ?_ hrun
  intro a₅ g₅ hrun
  obtain ⟨y₀, hy₀, hiff₀⟩ := prefix_of_argCheckNonAddress nil_pref g₅
  have hS := hS.trans (Line.of_inv Devm.getStor (by line_inv) g₅)
  have hM := hM.trans (Line.of_inv Devm.memory (by line_inv) g₅)
  rcases of_run_branch hrun with ⟨a₆, p₆, hrun⟩ | ⟨w₆, b₆, c₆, hw₆, pb₆, bb₆, hrun⟩
  case inr =>
    exact Coherent.call (get_emptyRevertSlot dp)
      (Coherent.of_storFixed StorFixed.revert) hrun
      (coherent_of_stor_eq
        (hS.trans ((PopBurn.Inv.inv pb₆).trans (Burn.Inv.inv bb₆))) hcoh)
  have hvalid₀ : ValidAdr (Sevm.argWord sevm 0) :=
    hiff₀.mp (popBurn_pref p₆ hy₀).1.symm
  have hS := hS.trans (PopBurn.Inv.inv p₆)
  have hM := hM.trans p₆.memory
  -- (3) the second canonical-address guard
  refine run_prepend_elim _ (arg 1 ++ checkNonAddress) ?_ hrun
  intro a₇ g₇ hrun
  obtain ⟨y₁, hy₁, hiff₁⟩ := prefix_of_argCheckNonAddress nil_pref g₇
  have hS := hS.trans (Line.of_inv Devm.getStor (by line_inv) g₇)
  have hM := hM.trans (Line.of_inv Devm.memory (by line_inv) g₇)
  rcases of_run_branch hrun with ⟨a₈, p₈, hrun⟩ | ⟨w₈, b₈, c₈, hw₈, pb₈, bb₈, hrun⟩
  case inr =>
    exact Coherent.call (get_emptyRevertSlot dp)
      (Coherent.of_storFixed StorFixed.revert) hrun
      (coherent_of_stor_eq
        (hS.trans ((PopBurn.Inv.inv pb₈).trans (Burn.Inv.inv bb₈))) hcoh)
  have hvalid₁ : ValidAdr (Sevm.argWord sevm 1) :=
    hiff₁.mp (popBurn_pref p₈ hy₁).1.symm
  have hS := hS.trans (PopBurn.Inv.inv p₈)
  have hM := hM.trans p₈.memory
  -- (4) the admin guard
  rcases of_run_next hrun with ⟨a₉, q₉, hrun⟩
  rcases of_run_next hrun with ⟨a₁₀, q₁₀, hrun⟩
  rcases of_run_next hrun with ⟨a₁₁, q₁₁, hrun⟩
  have hS := hS.trans
    ((Ninst.Hinv.inv (f := Devm.getStor) q₉).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) q₁₀).trans
        (Ninst.Hinv.inv (f := Devm.getStor) q₁₁)))
  have hM := hM.trans
    ((Ninst.Hinv.inv (f := Devm.memory) q₉).trans
      ((Ninst.Hinv.inv (f := Devm.memory) q₁₀).trans
        (Ninst.Hinv.inv (f := Devm.memory) q₁₁)))
  rcases of_run_branch hrun with ⟨a₁₂, p₁₂, hrun⟩ | ⟨w₁₂, b₁₂, c₁₂, hw₁₂, pb₁₂, bb₁₂, hrun⟩
  case inl =>
    exact Coherent.call rfl
      (Coherent.of_storFixed (storFixed_senderNotAdminError dp)) hrun
      (coherent_of_stor_eq (hS.trans (PopBurn.Inv.inv p₁₂)) hcoh)
  have hS := hS.trans ((PopBurn.Inv.inv pb₁₂).trans (Burn.Inv.inv bb₁₂))
  have hM := hM.trans (pb₁₂.memory.trans bb₁₂.memory)
  -- (5) the four staged scratch words
  have hwf₀ : Mem.Wf c₁₂.memory := wf_of_mem_eq hM hwf
  obtain ⟨img₀, hr₀⟩ : ∃ img, Mem.Reads c₁₂.memory img := ⟨_, mem_reads_data _⟩
  refine run_prepend_elim _ (arg 0) ?_ hrun
  intro t₁ ga₀ hrun
  have hpt₁ := prefix_of_arg (xs := ([] : Stack)) nil_pref ga₀
  have hmt₁ : c₁₂.memory = t₁.memory := Line.of_inv Devm.memory (by line_inv) ga₀
  have hS := hS.trans (Line.of_inv Devm.getStor (by line_inv) ga₀)
  refine run_prepend_elim _ (mstoreAt targetWord) ?_ hrun
  intro t₂ gm₀ hrun
  obtain ⟨hpt₂, hwft₂, hrt₂⟩ :=
    mstoreAt_image hpt₁ (wf_of_mem_eq hmt₁ hwf₀) (hmt₁ ▸ hr₀) gm₀
  have hS := hS.trans
    (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) gm₀)
  refine run_prepend_elim _ (arg 1) ?_ hrun
  intro t₃ ga₁ hrun
  have hpt₃ := prefix_of_arg hpt₂ ga₁
  have hmt₃ : t₂.memory = t₃.memory := Line.of_inv Devm.memory (by line_inv) ga₁
  have hS := hS.trans (Line.of_inv Devm.getStor (by line_inv) ga₁)
  refine run_prepend_elim _ (mstoreAt newPauserWord) ?_ hrun
  intro t₄ gm₁ hrun
  obtain ⟨hpt₄, hwft₄, hrt₄⟩ :=
    mstoreAt_image hpt₃ (wf_of_mem_eq hmt₃ hwft₂) (hmt₃ ▸ hrt₂) gm₁
  have hS := hS.trans
    (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) gm₁)
  rcases of_run_next hrun with ⟨t₅, qz₀, hrun⟩
  have hpt₅ := prefix_of_push (of_run_pushB256 qz₀) hpt₄
  have hmt₅ : t₄.memory = t₅.memory := (of_run_pushB256 qz₀).memory
  have hS := hS.trans (Ninst.Hinv.inv (f := Devm.getStor) qz₀)
  refine run_prepend_elim _ (mstoreAt previousPauserWord) ?_ hrun
  intro t₆ gm₂ hrun
  obtain ⟨hpt₆, hwft₆, hrt₆⟩ :=
    mstoreAt_image hpt₅ (wf_of_mem_eq hmt₅ hwft₄) (hmt₅ ▸ hrt₄) gm₂
  have hS := hS.trans
    (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) gm₂)
  rcases of_run_next hrun with ⟨t₇, qz₁, hrun⟩
  have hpt₇ := prefix_of_push (of_run_pushB256 qz₁) hpt₆
  have hmt₇ : t₆.memory = t₇.memory := (of_run_pushB256 qz₁).memory
  have hS := hS.trans (Ninst.Hinv.inv (f := Devm.getStor) qz₁)
  refine run_prepend_elim _ (mstoreAt continuationWord) ?_ hrun
  intro t₈ gm₃ hrun
  obtain ⟨hpt₈, hwft₈, hrt₈⟩ :=
    mstoreAt_image hpt₇ (wf_of_mem_eq hmt₇ hwft₆) (hmt₇ ▸ hrt₆) gm₃
  have hS := hS.trans
    (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) gm₃)
  -- (6) the tail jump into the shared kernel
  rcases of_run_call hrun with ⟨body, k₀, hget, hburn, hrun⟩
  obtain rfl : setPauserKernel = body :=
    Option.some.inj ((get_setPauserSlot dp).symm.trans hget)
  have hS := hS.trans (Burn.Inv.inv hburn)
  have hwfk : Mem.Wf k₀.memory := wf_of_mem_eq hburn.memory hwft₈
  have hrk : Mem.Reads k₀.memory _ := hburn.memory ▸ hrt₈
  -- (7) the staged words, read back out of the image the kernel receives
  have hreadTarget :=
    read_writeAt_before targetWord continuationWord 0
      target_before_continuation
      (read_writeAt_before targetWord previousPauserWord 0
        target_before_previousPauser
        (read_writeAt_before targetWord newPauserWord (Sevm.argWord sevm 1)
          target_before_newPauser
          (read_writeAt_self img₀ targetWord
            (Sevm.argWord sevm 0))))
  have hreadNew :=
    read_writeAt_before newPauserWord continuationWord 0
      newPauser_before_continuation
      (read_writeAt_before newPauserWord previousPauserWord 0
        newPauser_before_previousPauser
        (read_writeAt_self
          (Bytes.writeAt img₀ (targetWord * 32).toNat
            (Sevm.argWord sevm 0).toBytes)
          newPauserWord (Sevm.argWord sevm 1)))
  have hreadCont := read_writeAt_self
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt img₀ (targetWord * 32).toNat
          (Sevm.argWord sevm 0).toBytes)
        (newPauserWord * 32).toNat (Sevm.argWord sevm 1).toBytes)
      (previousPauserWord * 32).toNat (B256.toBytes 0))
    continuationWord 0
  -- (8) the landed kernel chain
  obtain ⟨entries, hw⟩ := coherent_of_stor_eq hS hcoh
  have htarget0 : Sevm.argWord sevm 0 ≠ 0 :=
    (setPauser_run_extracts_nonzero_guard hwfk hrk hreadTarget herror hrun).1
  obtain ⟨trace, htrace⟩ :
      ∃ trace, setPauserSourceTrace entries (Sevm.argWord sevm 0)
        (Sevm.argWord sevm 1) = some trace := by
    cases hfind : findEntry entries (Sevm.argWord sevm 0) <;>
      by_cases hnew0 : Sevm.argWord sevm 1 = 0 <;>
      simp [setPauserSourceTrace, setPauser, htarget0, hfind, hnew0]
  rcases setPauser_run_extracts_sourceTrace hwfk hrk hreadTarget hreadNew
      hreadCont rfl hw (canonicalAddress_of_validAdr hvalid₀)
      (canonicalAddress_of_validAdr hvalid₁) herror happend hafter hremove
      hfinish hrun htrace with
    ⟨postRegistry, postImg, hwfPost, hrPost, htargetPost, hnewPost,
      hpreviousPost, hcontinuationPost, hstorPost, hwPost, -, hfinishRun⟩
  refine ⟨trace.postEntries, ?_⟩
  rcases finishSetPauser_run_split_continuation hwfPost hrPost hnewPost
      hpreviousPost htargetPost hcontinuationPost rfl hregisterLookup
      hpauseLookup hfinishRun with hregister | hpause
  · rcases hregister with
      ⟨-, registerPre, -, hwfRegister, hrRegister, hstorRegister, -,
        hregisterRun⟩
    have hwRegister : RegistryWitness
        (logicalStorageOfStor (Devm.getStor registerPre sevm.currentTarget))
        trace.postEntries := by
      rw [hstorRegister]; exact hwPost
    exact registerAfterSet_preserves_registry hwfRegister hrRegister
      hpreviousPost hnewPost rfl (hw.assignmentAt_canonical _)
      (canonicalAddress_of_validAdr hvalid₁) hwRegister hpanicLookup
      hregisterRun
  · exact (hpause.1 rfl).elim

/-- **The sixteenth dispatch obligation.**  `registerPauser` never yields to
foreign code, so the deeper-frame hypothesis is unused; what it does need, and
what the ladder now supplies, is the memory invariant at the body's entry. -/
theorem registerPauser_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux (registerPauser dp) := by
  intro sevm s r h_ct h_pre h_wf _ h_run
  subst h_ct
  exact ⟨trivial, coherent_registerPauser dp h_wf (h_pre.inv.1 rfl) h_run⟩

/-! ## `pause`'s post-kernel continuation

`pauseAfterSet` is the only body in the runtime that yields to arbitrary code,
and it does so twice.  Everything between the two yields is storage-silent, and
its own single persistent write is the caller's expiry cell — canonical for
free, because its key is built from the `CALLER` opcode. -/

theorem storFixed_pauseFailedError (dp : DeployParams) :
    StorFixed dp pauseFailedError := StorFixed.of_inv (by func_inv)

theorem storFixed_reentrantCallError (dp : DeployParams) :
    StorFixed dp reentrantCallError := StorFixed.of_inv (by func_inv)

theorem storFixed_revertReturnData (dp : DeployParams) :
    StorFixed dp Func.revertReturnData := StorFixed.of_inv (by func_inv)

/-- `bubbleRevertSlot` is index 13, and `aux`'s thirteenth entry is the
returndata bubble. -/
theorem get_bubbleRevertSlot (dp : DeployParams) :
    ((runtime dp).main :: aux)[bubbleRevertSlot]? = some Func.revertReturnData := rfl

/-- `Func.revertData`'s node count depends on a Keccak image, so the arithmetic
panic reverter is handled generically over the blob.  (The Endpoints module
proves the same fact for its own use; that copy is `private`.) -/
private theorem inv_prependStoresRev :
    ∀ (iws : List (B256 × Nat)) {rest : Func},
      Func.Inv Devm.getStor Devm.getStor rest →
      Func.Inv Devm.getStor Devm.getStor (prependStoresRev iws rest)
  | [], _, h => h
  | _ :: iws, _, h =>
      inv_prependStoresRev iws
        (next_inv Ninst.Hinv.inv
          (next_inv Ninst.Hinv.inv (next_inv Ninst.Hinv.inv h)))

private theorem storFixed_panicData {dp : DeployParams} (blob : Bytes) :
    StorFixed dp (Func.revertData blob) :=
  StorFixed.of_inv
    (inv_prependStoresRev _
      (next_inv Ninst.Hinv.inv
        (next_inv Ninst.Hinv.inv (last_inv Linst.Hinv.inv))))

/-- The heartbeat write shared by both `pauseExpiryFinish` arms: one expiry
cell, then the transient lock clear, then `STOP`. -/
private theorem coherent_pauseExpiryFinish (dp : DeployParams) :
    Coherent dp pauseExpiryFinish := by
  unfold pauseExpiryFinish storeHeartbeatExpiryFromStack
  refine Coherent.next (Coherent.next (Coherent.next ?_))
  exact Coherent.callerTagSstore
    (fun a _ _ hcoh => hcoh.expiry_set (canonicalAddress_toB256 a))
    (StorFixed.of_inv (by func_inv))

theorem coherent_pauseSuccess (dp : DeployParams) : Coherent dp pauseSuccess := by
  unfold pauseSuccess checkedHeartbeatExpiry
  refine Coherent.prepend (by line_inv) (Coherent.prepend (by line_inv)
    (Coherent.next (Coherent.prepend (by line_inv) (Coherent.next
      (Coherent.prepend (by line_inv) (Coherent.next
        (Coherent.prepend (by line_inv) (Coherent.next (Coherent.next
          (Coherent.branch ?_ ?_)))))))))) 
  · refine Coherent.next (Coherent.next (Coherent.next (Coherent.next
      (Coherent.next (Coherent.next (Coherent.next (Coherent.next
        (Coherent.branch (coherent_pauseExpiryFinish dp)
          (Coherent.call (get_arithmeticPanicSlot dp)
            (Coherent.of_storFixed (storFixed_panicData _)))))))))))
  · exact Coherent.next (coherent_pauseExpiryFinish dp)

theorem coherent_decodePausedResult (dp : DeployParams) :
    Coherent dp decodePausedResult := by
  unfold decodePausedResult
  refine Coherent.prepend (by line_inv) (Coherent.branch ?_
    (Coherent.call (get_emptyRevertSlot dp)
      (Coherent.of_storFixed StorFixed.revert)))
  refine Coherent.prepend (by line_inv) (Coherent.next (Coherent.next
    (Coherent.branch ?_ (Coherent.call rfl
      (Coherent.of_storFixed (storFixed_pauseFailedError dp))))))
  exact Coherent.next (Coherent.next
    (Coherent.branch
      (Coherent.call (get_emptyRevertSlot dp)
        (Coherent.of_storFixed StorFixed.revert))
      (coherent_pauseSuccess dp)))

/-- The contract's own compiled program survives one instruction. -/
private theorem code_of_ninst {dp : DeployParams} {ca : Adr} {sevm : Sevm}
    {s s' : Devm} {i : Ninst}
    (hcode : some (s.getCode ca).toList = Prog.compile (runtime dp))
    (h : Ninst.Run sevm s i s') :
    some (s'.getCode ca).toList = Prog.compile (runtime dp) := by
  have hne : (s.getCode ca).toList ≠ [] := by
    intro hc
    apply @Prog.compile_ne_nil (runtime dp)
    rw [← hcode, hc]
  rw [ninst_codePreserve i h ca hne]
  exact hcode

/-- `loadWord` pushes one word. -/
private theorem prefix_of_loadWord {sevm : Sevm} {s s' : Devm} {word : B256}
    {xs : Stack} (hp : xs <<+ s.stack)
    (run : Line.Run sevm s (loadWord word) s') :
    ∃ y, y :: xs <<+ s'.stack := by
  unfold loadWord at run
  rcases Line.of_run_cons run with ⟨u, q, run⟩
  rcases Line.of_run_cons run with ⟨u2, q2, hnil⟩
  cases hnil
  exact prefix_of_mload q2 (prefix_of_push (of_run_pushB256 q) hp)

private theorem code_of_getCode_eq {dp : DeployParams} {ca : Adr} {s s' : Devm}
    (h : Devm.getCode s = Devm.getCode s')
    (hcode : some (s.getCode ca).toList = Prog.compile (runtime dp)) :
    some (s'.getCode ca).toList = Prog.compile (runtime dp) := by
  rw [← congrFun h ca]; exact hcode

/-- **`pauseAfterSet` preserves Registry coherence across both of its yields.**

No premise restricts either callee.  The `CALL` forwards `pauseFor(uint256)`
to whatever address the pause target happens to be and the `STATICCALL` reads
`isPaused()` back from it; both are discharged by the deeper-frame transport
lemmas, which need only the contract's own compiled program at the yielding
state.  Between and after the yields the walk is storage-silent except for the
caller's own expiry cell, whose key comes from `CALLER` and is therefore
canonical by construction, and the transient lock, which `Devm.getStor` does
not see. -/
theorem coherent_pauseAfterSet {dp : DeployParams} {sevm : Sevm} {s r : Devm}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget (runtime dp)
      ((registrySpec dp).PreWf sevm.currentTarget)
      ((registrySpec dp).Post sevm.currentTarget))
    (hcode : some (s.getCode sevm.currentTarget).toList = Prog.compile (runtime dp))
    (hcoh : RegistryCoherent (Devm.getStor s sevm.currentTarget))
    (hrun : Func.Run ((runtime dp).main :: aux) sevm s pauseAfterSet r) :
    RegistryCoherent (Devm.getStor r sevm.currentTarget) := by
  simp only [pauseAfterSet] at hrun
  -- the callee-has-code guard
  refine run_prepend_elim _ (loadWord targetWord) ?_ hrun
  intro c₁ l₁ hrun
  have hC := coherent_of_stor_eq (Line.of_inv Devm.getStor (by line_inv) l₁) hcoh
  have hK := code_of_getCode_eq (Line.of_inv Devm.getCode (by line_inv) l₁) hcode
  rcases of_run_next hrun with ⟨c₂, q₂, hrun⟩
  rcases of_run_next hrun with ⟨c₃, q₃, hrun⟩
  rcases of_run_next hrun with ⟨c₄, q₄, hrun⟩
  have hC := coherent_of_stor_eq
    ((Ninst.Hinv.inv (f := Devm.getStor) q₂).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) q₃).trans
        (Ninst.Hinv.inv (f := Devm.getStor) q₄))) hC
  have hK := code_of_getCode_eq
    ((Ninst.Hinv.inv (f := Devm.getCode) q₂).trans
      ((Ninst.Hinv.inv (f := Devm.getCode) q₃).trans
        (Ninst.Hinv.inv (f := Devm.getCode) q₄))) hK
  rcases of_run_branch hrun with ⟨c₅, p₅, hrun⟩ | ⟨wg, bg, cg, hwg, pbg, bbg, hrun⟩
  case inr =>
    exact Coherent.call (get_emptyRevertSlot dp)
      (Coherent.of_storFixed StorFixed.revert) hrun
      (coherent_of_stor_eq ((PopBurn.Inv.inv pbg).trans (Burn.Inv.inv bbg)) hC)
  have hC := coherent_of_stor_eq (PopBurn.Inv.inv p₅) hC
  have hK := code_of_getCode_eq (getCode_of_state p₅.state) hK
  -- the outgoing `pauseFor(uint256)` argument window
  rcases of_run_next hrun with ⟨d₁, qpop, hrun⟩
  rcases of_run_next hrun with ⟨d₂, qsel, hrun⟩
  have hC := coherent_of_stor_eq
    ((Ninst.Hinv.inv (f := Devm.getStor) qpop).trans
      (Ninst.Hinv.inv (f := Devm.getStor) qsel)) hC
  have hK := code_of_getCode_eq
    ((Ninst.Hinv.inv (f := Devm.getCode) qpop).trans
      (Ninst.Hinv.inv (f := Devm.getCode) qsel)) hK
  refine run_prepend_elim _ (mstoreAt 8) ?_ hrun
  intro d₃ l₃ hrun
  refine run_prepend_elim _ (loadWord durationWord) ?_ hrun
  intro d₄ l₄ hrun
  refine run_prepend_elim _ (mstoreAt 9) ?_ hrun
  intro d₅ l₅ hrun
  have hC := coherent_of_stor_eq
    ((Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) l₃).trans
      ((Line.of_inv Devm.getStor (by line_inv) l₄).trans
        (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) l₅))) hC
  have hK := code_of_getCode_eq
    ((Line.of_inv Devm.getCode (by unfold mstoreAt; line_inv) l₃).trans
      ((Line.of_inv Devm.getCode (by line_inv) l₄).trans
        (Line.of_inv Devm.getCode (by unfold mstoreAt; line_inv) l₅))) hK
  refine run_prepend_elim _ (pushList [0, 0, 36, 0x11c, 0]) ?_ hrun
  intro d₆ l₆ hrun
  have hC := coherent_of_stor_eq (Line.of_inv Devm.getStor (by line_inv) l₆) hC
  have hK := code_of_getCode_eq (Line.of_inv Devm.getCode (by line_inv) l₆) hK
  refine run_prepend_elim _ (loadWord targetWord) ?_ hrun
  intro d₇ l₇ hrun
  have hC := coherent_of_stor_eq (Line.of_inv Devm.getStor (by line_inv) l₇) hC
  have hK := code_of_getCode_eq (Line.of_inv Devm.getCode (by line_inv) l₇) hK
  rcases of_run_next hrun with ⟨d₈, qgas, hrun⟩
  rcases of_run_next hrun with ⟨d₉, qcall, hrun⟩
  -- the seven `CALL` operands, read off the pushes that put them there
  rcases Line.of_run_cons l₆ with ⟨e₁, r₁, l₆'⟩
  rcases Line.of_run_cons l₆' with ⟨e₂, r₂, l₆'⟩
  rcases Line.of_run_cons l₆' with ⟨e₃, r₃, l₆'⟩
  rcases Line.of_run_cons l₆' with ⟨e₄, r₄, l₆'⟩
  rcases Line.of_run_cons l₆' with ⟨e₅, r₅, hnil⟩
  cases hnil
  obtain ⟨tw, hptw⟩ := prefix_of_loadWord
    (prefix_of_push (of_run_pushB256 r₅)
      (prefix_of_push (of_run_pushB256 r₄)
        (prefix_of_push (of_run_pushB256 r₃)
          (prefix_of_push (of_run_pushB256 r₂)
            (prefix_of_push (of_run_pushB256 r₁) nil_pref))))) l₇
  obtain ⟨gw, hgw⟩ := of_run_gas qgas
  have hC := coherent_of_stor_eq (Ninst.Hinv.inv (f := Devm.getStor) qgas) hC
  have hK := code_of_getCode_eq (Ninst.Hinv.inv (f := Devm.getCode) qgas) hK
  have hpcall : gw :: tw :: (0 : B256) :: (0x11c : B256) :: (36 : B256) ::
      (0 : B256) :: (0 : B256) :: ([] : Stack) <<+ d₈.stack := by
    simpa using prefix_of_push hgw hptw
  obtain ⟨hC, -⟩ := coherent_of_call ih hpcall hK hC qcall
  have hK := code_of_ninst hK qcall
  rcases of_run_next hrun with ⟨d₁₀, qiz, hrun⟩
  have hC := coherent_of_stor_eq (Ninst.Hinv.inv (f := Devm.getStor) qiz) hC
  have hK := code_of_getCode_eq (Ninst.Hinv.inv (f := Devm.getCode) qiz) hK
  rcases of_run_branch hrun with ⟨f₀, pf₀, hrun⟩ | ⟨wb, bb, cb, hwb, pbb, bbb, hrun⟩
  case inr =>
    exact Coherent.call (get_bubbleRevertSlot dp)
      (Coherent.of_storFixed (storFixed_revertReturnData dp)) hrun
      (coherent_of_stor_eq ((PopBurn.Inv.inv pbb).trans (Burn.Inv.inv bbb)) hC)
  have hC := coherent_of_stor_eq (PopBurn.Inv.inv pf₀) hC
  have hK := code_of_getCode_eq (getCode_of_state pf₀.state) hK
  -- the outgoing `isPaused()` argument window
  rcases of_run_next hrun with ⟨g₁, qsel2, hrun⟩
  have hC := coherent_of_stor_eq (Ninst.Hinv.inv (f := Devm.getStor) qsel2) hC
  have hK := code_of_getCode_eq (Ninst.Hinv.inv (f := Devm.getCode) qsel2) hK
  refine run_prepend_elim _ (mstoreAt 8) ?_ hrun
  intro g₂ m₂ hrun
  have hC := coherent_of_stor_eq
    (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) m₂) hC
  have hK := code_of_getCode_eq
    (Line.of_inv Devm.getCode (by unfold mstoreAt; line_inv) m₂) hK
  refine run_prepend_elim _ (pushList [32, 0, 4, 0x11c]) ?_ hrun
  intro g₃ m₃ hrun
  have hC := coherent_of_stor_eq (Line.of_inv Devm.getStor (by line_inv) m₃) hC
  have hK := code_of_getCode_eq (Line.of_inv Devm.getCode (by line_inv) m₃) hK
  refine run_prepend_elim _ (loadWord targetWord) ?_ hrun
  intro g₄ m₄ hrun
  have hC := coherent_of_stor_eq (Line.of_inv Devm.getStor (by line_inv) m₄) hC
  have hK := code_of_getCode_eq (Line.of_inv Devm.getCode (by line_inv) m₄) hK
  rcases of_run_next hrun with ⟨g₅, qgas2, hrun⟩
  rcases of_run_next hrun with ⟨g₆, qstat, hrun⟩
  rcases Line.of_run_cons m₃ with ⟨u₁, s₁, m₃'⟩
  rcases Line.of_run_cons m₃' with ⟨u₂, s₂, m₃'⟩
  rcases Line.of_run_cons m₃' with ⟨u₃, s₃, m₃'⟩
  rcases Line.of_run_cons m₃' with ⟨u₄, s₄, hnil2⟩
  cases hnil2
  obtain ⟨tw2, hptw2⟩ := prefix_of_loadWord
    (prefix_of_push (of_run_pushB256 s₄)
      (prefix_of_push (of_run_pushB256 s₃)
        (prefix_of_push (of_run_pushB256 s₂)
          (prefix_of_push (of_run_pushB256 s₁) nil_pref)))) m₄
  obtain ⟨gw2, hgw2⟩ := of_run_gas qgas2
  have hC := coherent_of_stor_eq (Ninst.Hinv.inv (f := Devm.getStor) qgas2) hC
  have hK := code_of_getCode_eq (Ninst.Hinv.inv (f := Devm.getCode) qgas2) hK
  have hpstat : gw2 :: tw2 :: (0x11c : B256) :: (4 : B256) :: (0 : B256) ::
      (32 : B256) :: ([] : Stack) <<+ g₅.stack := by
    simpa using prefix_of_push hgw2 hptw2
  obtain ⟨hC, -⟩ := coherent_of_staticcall ih hpstat hK hC qstat
  rcases of_run_next hrun with ⟨g₇, qiz2, hrun⟩
  have hC := coherent_of_stor_eq (Ninst.Hinv.inv (f := Devm.getStor) qiz2) hC
  rcases of_run_branch hrun with ⟨h₀, ph₀, hrun⟩ | ⟨wb2, bb2, cb2, hwb2, pbb2, bbb2, hrun⟩
  case inr =>
    exact Coherent.call (get_bubbleRevertSlot dp)
      (Coherent.of_storFixed (storFixed_revertReturnData dp)) hrun
      (coherent_of_stor_eq ((PopBurn.Inv.inv pbb2).trans (Burn.Inv.inv bbb2)) hC)
  exact coherent_decodePausedResult dp hrun
    (coherent_of_stor_eq (PopBurn.Inv.inv ph₀) hC)

/-- The landed kernel chain, consumed at `pause`'s continuation word.  Split
out of the endpoint walk so that the extraction lemma's own unification runs in
a small context; the endpoint supplies the staged image and the guard's
canonicality.

The event suffix is taken whole from
`finishSetPauser_run_split_continuation`, whose continuation arms carry the
contract's own compiled program across the suffix alongside its storage. -/
private theorem coherent_of_pauseKernelRun (dp : DeployParams)
    {sevm : Sevm} {k r : Devm} {img : Bytes} {target : B256}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget (runtime dp)
      ((registrySpec dp).PreWf sevm.currentTarget)
      ((registrySpec dp).Post sevm.currentTarget))
    (hwf : Mem.Wf k.memory)
    (hr : Mem.Reads k.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (htargetCanonical : canonicalAddress target)
    (hcode : some (k.getCode sevm.currentTarget).toList
      = Prog.compile (runtime dp))
    (hcoh : RegistryCoherent (Devm.getStor k sevm.currentTarget))
    (hrun : Func.Run ((runtime dp).main :: aux) sevm k setPauserKernel r) :
    RegistryCoherent (Devm.getStor r sevm.currentTarget) := by
  have herror : ((runtime dp).main :: aux)[pausableZeroErrorSlot]? =
    some pausableZeroError := rfl
  have happend : ((runtime dp).main :: aux)[appendTargetSlot]? =
    some appendTarget := rfl
  have hafter : ((runtime dp).main :: aux)[afterOldPauserSlot]? =
    some afterOldPauser := rfl
  have hremove : ((runtime dp).main :: aux)[removeTargetSlot]? =
    some removeTarget := rfl
  have hfinish : ((runtime dp).main :: aux)[finishSetPauserSlot]? =
    some finishSetPauser := rfl
  have hpauseLookup : ((runtime dp).main :: aux)[pauseAfterSetSlot]? =
    some pauseAfterSet := rfl
  have hregisterLookup : ((runtime dp).main :: aux)[registerAfterSetSlot]? =
    some registerAfterSet := rfl
  obtain ⟨entries, hw⟩ := hcoh
  have hzeroCanonical : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num
  have htarget0 : target ≠ 0 :=
    (setPauser_run_extracts_nonzero_guard hwf hr htargetRead herror hrun).1
  obtain ⟨trace, htrace⟩ :
      ∃ trace, setPauserSourceTrace entries target 0 = some trace := by
    cases hfind : findEntry entries target <;>
      simp [setPauserSourceTrace, setPauser, htarget0, hfind]
  rcases setPauser_run_extracts_sourceTrace hwf hr htargetRead hnewRead
      hcontRead rfl hw htargetCanonical hzeroCanonical
      herror happend hafter hremove hfinish hrun htrace with
    ⟨postRegistry, postImg, hwfPost, hrPost, htargetPost, hnewPost,
      hpreviousPost, hcontinuationPost, hstorPost, hwPost, hcodePost,
      hfinishRun⟩
  rcases finishSetPauser_run_split_continuation hwfPost hrPost hnewPost
      hpreviousPost htargetPost hcontinuationPost rfl hregisterLookup
      hpauseLookup hfinishRun with hregister | hpause
  · exact absurd hregister.1 flag_one_ne_zero
  rcases hpause with
    ⟨-, pausePre, -, -, -, hstorPause, hcodePause, hpauseRun⟩
  refine coherent_pauseAfterSet ih
    (code_of_getCode_eq (hcodePost.trans hcodePause) hcode)
    ⟨trace.postEntries, ?_⟩ hpauseRun
  rw [hstorPause]
  exact hwPost


/-- **`pause` preserves Registry coherence.**

Everything the endpoint does is discharged: the reentrancy lock, the
assignment and heartbeat guards, the five staged scratch words, the shared
kernel, the event suffix, and — through `coherent_pauseAfterSet` — the two
yields to arbitrary code and the caller's own expiry write.

The one fact the walk cannot recover from its own tail is the contract's own
compiled program at the state that issues the first `CALL`: that state sits
behind `setPauser_run_extracts_sourceTrace`'s existential, and it is the
extraction's code conclusion that carries it across. -/
theorem coherent_pause (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget (runtime dp)
      ((registrySpec dp).PreWf sevm.currentTarget)
      ((registrySpec dp).Post sevm.currentTarget))
    (hwf : Mem.Wf s.memory)
    (hcode : some (s.getCode sevm.currentTarget).toList = Prog.compile (runtime dp))
    (hcoh : RegistryCoherent (Devm.getStor s sevm.currentTarget))
    (hrun : Func.Run ((runtime dp).main :: aux) sevm s pause r) :
    RegistryCoherent (Devm.getStor r sevm.currentTarget) := by
  have herror : ((runtime dp).main :: aux)[pausableZeroErrorSlot]? =
    some pausableZeroError := rfl
  have happend : ((runtime dp).main :: aux)[appendTargetSlot]? =
    some appendTarget := rfl
  have hafter : ((runtime dp).main :: aux)[afterOldPauserSlot]? =
    some afterOldPauser := rfl
  have hremove : ((runtime dp).main :: aux)[removeTargetSlot]? =
    some removeTarget := rfl
  have hfinish : ((runtime dp).main :: aux)[finishSetPauserSlot]? =
    some finishSetPauser := rfl
  simp only [pause, requireStaticArgs, canonicalAddressArg] at hrun
  -- (1) the static-argument guard
  rcases of_run_next hrun with ⟨a₁, q₁, hrun⟩
  rcases of_run_next hrun with ⟨a₂, q₂, hrun⟩
  rcases of_run_next hrun with ⟨a₃, q₃, hrun⟩
  rcases of_run_branch_revert hrun with ⟨a₄, p₄, hrun⟩
  have hS : Devm.getStor s = Devm.getStor a₄ :=
    ((Ninst.Hinv.inv (f := Devm.getStor) q₁).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) q₂).trans
        (Ninst.Hinv.inv (f := Devm.getStor) q₃))).trans (PopBurn.Inv.inv p₄)
  have hM : s.memory = a₄.memory :=
    ((Ninst.Hinv.inv (f := Devm.memory) q₁).trans
      ((Ninst.Hinv.inv (f := Devm.memory) q₂).trans
        (Ninst.Hinv.inv (f := Devm.memory) q₃))).trans p₄.memory
  have hE : Devm.getCode s = Devm.getCode a₄ :=
    ((Ninst.Hinv.inv (f := Devm.getCode) q₁).trans
      ((Ninst.Hinv.inv (f := Devm.getCode) q₂).trans
        (Ninst.Hinv.inv (f := Devm.getCode) q₃))).trans (getCode_of_state p₄.state)
  -- (2) the canonical-address guard
  refine run_prepend_elim _ (arg 0 ++ checkNonAddress) ?_ hrun
  intro a₅ g₅ hrun
  obtain ⟨y₀, hy₀, hiff₀⟩ := prefix_of_argCheckNonAddress nil_pref g₅
  have hS := hS.trans (Line.of_inv Devm.getStor (by line_inv) g₅)
  have hM := hM.trans (Line.of_inv Devm.memory (by line_inv) g₅)
  have hE := hE.trans (Line.of_inv Devm.getCode (by line_inv) g₅)
  rcases of_run_branch hrun with ⟨a₆, p₆, hrun⟩ | ⟨w₆, b₆, c₆, hw₆, pb₆, bb₆, hrun⟩
  case inr =>
    exact Coherent.call (get_emptyRevertSlot dp)
      (Coherent.of_storFixed StorFixed.revert) hrun
      (coherent_of_stor_eq
        (hS.trans ((PopBurn.Inv.inv pb₆).trans (Burn.Inv.inv bb₆))) hcoh)
  have hvalid₀ : ValidAdr (Sevm.argWord sevm 0) :=
    hiff₀.mp (popBurn_pref p₆ hy₀).1.symm
  have hS := hS.trans (PopBurn.Inv.inv p₆)
  have hM := hM.trans p₆.memory
  have hE := hE.trans (getCode_of_state p₆.state)
  -- (3) the reentrancy lock
  rcases of_run_next hrun with ⟨b₁, r₁, hrun⟩
  rcases of_run_next hrun with ⟨b₂, r₂, hrun⟩
  rcases of_run_next hrun with ⟨b₃, r₃, hrun⟩
  have hS := hS.trans
    ((Ninst.Hinv.inv (f := Devm.getStor) r₁).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) r₂).trans
        (Ninst.Hinv.inv (f := Devm.getStor) r₃)))
  have hM := hM.trans
    ((Ninst.Hinv.inv (f := Devm.memory) r₁).trans
      ((Ninst.Hinv.inv (f := Devm.memory) r₂).trans
        (Ninst.Hinv.inv (f := Devm.memory) r₃)))
  have hE := hE.trans
    ((Ninst.Hinv.inv (f := Devm.getCode) r₁).trans
      ((Ninst.Hinv.inv (f := Devm.getCode) r₂).trans
        (Ninst.Hinv.inv (f := Devm.getCode) r₃)))
  rcases of_run_branch hrun with ⟨b₄, p₄', hrun⟩ | ⟨w₇, b₇, c₇, hw₇, pb₇, bb₇, hrun⟩
  case inl =>
    exact Coherent.call rfl
      (Coherent.of_storFixed (storFixed_reentrantCallError dp)) hrun
      (coherent_of_stor_eq (hS.trans (PopBurn.Inv.inv p₄')) hcoh)
  have hS := hS.trans ((PopBurn.Inv.inv pb₇).trans (Burn.Inv.inv bb₇))
  have hM := hM.trans (pb₇.memory.trans bb₇.memory)
  have hE := hE.trans
    ((getCode_of_state pb₇.state).trans (getCode_of_state bb₇.state))
  -- (4) the lock is set, then the assignment check
  rcases of_run_next hrun with ⟨c₁, t₁, hrun⟩
  rcases of_run_next hrun with ⟨c₂, t₂, hrun⟩
  rcases of_run_next hrun with ⟨c₃, t₃, hrun⟩
  have hS := hS.trans
    ((Ninst.Hinv.inv (f := Devm.getStor) t₁).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) t₂).trans
        (Ninst.Hinv.inv (f := Devm.getStor) t₃)))
  have hM := hM.trans
    ((Ninst.Hinv.inv (f := Devm.memory) t₁).trans
      ((Ninst.Hinv.inv (f := Devm.memory) t₂).trans
        (Ninst.Hinv.inv (f := Devm.memory) t₃)))
  have hE := hE.trans
    ((Ninst.Hinv.inv (f := Devm.getCode) t₁).trans
      ((Ninst.Hinv.inv (f := Devm.getCode) t₂).trans
        (Ninst.Hinv.inv (f := Devm.getCode) t₃)))
  refine run_prepend_elim _ (arg 0) ?_ hrun
  intro c₄ u₄ hrun
  refine run_prepend_elim _ (tagTop assignmentRegion) ?_ hrun
  intro c₅ u₅ hrun
  have hS := hS.trans
    ((Line.of_inv Devm.getStor (by line_inv) u₄).trans
      (Line.of_inv Devm.getStor (by unfold tagTop; line_inv) u₅))
  have hM := hM.trans
    ((Line.of_inv Devm.memory (by line_inv) u₄).trans
      (Line.of_inv Devm.memory (by unfold tagTop; line_inv) u₅))
  have hE := hE.trans
    ((Line.of_inv Devm.getCode (by line_inv) u₄).trans
      (Line.of_inv Devm.getCode (by unfold tagTop; line_inv) u₅))
  rcases of_run_next hrun with ⟨c₆, v₁, hrun⟩
  rcases of_run_next hrun with ⟨c₇, v₂, hrun⟩
  rcases of_run_next hrun with ⟨c₈, v₃, hrun⟩
  have hS := hS.trans
    ((Ninst.Hinv.inv (f := Devm.getStor) v₁).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) v₂).trans
        (Ninst.Hinv.inv (f := Devm.getStor) v₃)))
  have hM := hM.trans
    ((Ninst.Hinv.inv (f := Devm.memory) v₁).trans
      ((Ninst.Hinv.inv (f := Devm.memory) v₂).trans
        (Ninst.Hinv.inv (f := Devm.memory) v₃)))
  have hE := hE.trans
    ((Ninst.Hinv.inv (f := Devm.getCode) v₁).trans
      ((Ninst.Hinv.inv (f := Devm.getCode) v₂).trans
        (Ninst.Hinv.inv (f := Devm.getCode) v₃)))
  rcases of_run_branch hrun with ⟨c₉, p₉, hrun⟩ | ⟨w₈, b₈, c₁₀, hw₈, pb₈, bb₈, hrun⟩
  case inl =>
    exact Coherent.call rfl
      (Coherent.of_storFixed (storFixed_senderNotPauserError dp)) hrun
      (coherent_of_stor_eq (hS.trans (PopBurn.Inv.inv p₉)) hcoh)
  have hS := hS.trans ((PopBurn.Inv.inv pb₈).trans (Burn.Inv.inv bb₈))
  have hM := hM.trans (pb₈.memory.trans bb₈.memory)
  have hE := hE.trans
    ((getCode_of_state pb₈.state).trans (getCode_of_state bb₈.state))
  -- (5) the heartbeat-liveness check
  rcases of_run_next hrun with ⟨d₁, x₁, hrun⟩
  refine run_prepend_elim _ (tagTop expiryRegion) ?_ hrun
  intro d₂ x₂ hrun
  rcases of_run_next hrun with ⟨d₃, x₃, hrun⟩
  rcases of_run_next hrun with ⟨d₄, x₄, hrun⟩
  rcases of_run_next hrun with ⟨d₅, x₅, hrun⟩
  have hS := hS.trans
    ((Ninst.Hinv.inv (f := Devm.getStor) x₁).trans
      ((Line.of_inv Devm.getStor (by unfold tagTop; line_inv) x₂).trans
        ((Ninst.Hinv.inv (f := Devm.getStor) x₃).trans
          ((Ninst.Hinv.inv (f := Devm.getStor) x₄).trans
            (Ninst.Hinv.inv (f := Devm.getStor) x₅)))))
  have hM := hM.trans
    ((Ninst.Hinv.inv (f := Devm.memory) x₁).trans
      ((Line.of_inv Devm.memory (by unfold tagTop; line_inv) x₂).trans
        ((Ninst.Hinv.inv (f := Devm.memory) x₃).trans
          ((Ninst.Hinv.inv (f := Devm.memory) x₄).trans
            (Ninst.Hinv.inv (f := Devm.memory) x₅)))))
  have hE := hE.trans
    ((Ninst.Hinv.inv (f := Devm.getCode) x₁).trans
      ((Line.of_inv Devm.getCode (by unfold tagTop; line_inv) x₂).trans
        ((Ninst.Hinv.inv (f := Devm.getCode) x₃).trans
          ((Ninst.Hinv.inv (f := Devm.getCode) x₄).trans
            (Ninst.Hinv.inv (f := Devm.getCode) x₅)))))
  rcases of_run_branch hrun with ⟨d₆, p₆', hrun⟩ | ⟨w₉, b₉, c₁₁, hw₉, pb₉, bb₉, hrun⟩
  case inl =>
    exact Coherent.call rfl
      (Coherent.of_storFixed (storFixed_heartbeatExpiredError dp)) hrun
      (coherent_of_stor_eq (hS.trans (PopBurn.Inv.inv p₆')) hcoh)
  have hS := hS.trans ((PopBurn.Inv.inv pb₉).trans (Burn.Inv.inv bb₉))
  have hM := hM.trans (pb₉.memory.trans bb₉.memory)
  have hE := hE.trans
    ((getCode_of_state pb₉.state).trans (getCode_of_state bb₉.state))
  -- (6) the five staged scratch words
  have hwf₀ : Mem.Wf c₁₁.memory := wf_of_mem_eq hM hwf
  obtain ⟨img₀, hr₀⟩ : ∃ img, Mem.Reads c₁₁.memory img := ⟨_, mem_reads_data _⟩
  rcases of_run_next hrun with ⟨e₁, z₁, hrun⟩
  rcases of_run_next hrun with ⟨e₂, z₂, hrun⟩
  obtain ⟨dur, hpdur, -⟩ :=
    prefix_of_sload z₂ (prefix_of_push (of_run_pushB256 z₁) nil_pref)
  have hme₂ : c₁₁.memory = e₂.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) z₁).trans
      (Ninst.Hinv.inv (f := Devm.memory) z₂)
  have hS := hS.trans
    ((Ninst.Hinv.inv (f := Devm.getStor) z₁).trans
      (Ninst.Hinv.inv (f := Devm.getStor) z₂))
  have hE := hE.trans
    ((Ninst.Hinv.inv (f := Devm.getCode) z₁).trans
      (Ninst.Hinv.inv (f := Devm.getCode) z₂))
  refine run_prepend_elim _ (mstoreAt durationWord) ?_ hrun
  intro e₃ m₃ hrun
  obtain ⟨hp₃, hwf₃, hr₃⟩ :=
    mstoreAt_image hpdur (wf_of_mem_eq hme₂ hwf₀) (hme₂ ▸ hr₀) m₃
  have hS := hS.trans (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) m₃)
  have hE := hE.trans (Line.of_inv Devm.getCode (by unfold mstoreAt; line_inv) m₃)
  refine run_prepend_elim _ (arg 0) ?_ hrun
  intro e₄ m₄ hrun
  have hp₄ := prefix_of_arg hp₃ m₄
  have hme₄ : e₃.memory = e₄.memory := Line.of_inv Devm.memory (by line_inv) m₄
  have hS := hS.trans (Line.of_inv Devm.getStor (by line_inv) m₄)
  have hE := hE.trans (Line.of_inv Devm.getCode (by line_inv) m₄)
  refine run_prepend_elim _ (mstoreAt targetWord) ?_ hrun
  intro e₅ m₅ hrun
  obtain ⟨hp₅, hwf₅, hr₅⟩ :=
    mstoreAt_image hp₄ (wf_of_mem_eq hme₄ hwf₃) (hme₄ ▸ hr₃) m₅
  have hS := hS.trans (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) m₅)
  have hE := hE.trans (Line.of_inv Devm.getCode (by unfold mstoreAt; line_inv) m₅)
  rcases of_run_next hrun with ⟨e₆, z₆, hrun⟩
  have hp₆ := prefix_of_push (of_run_pushB256 z₆) hp₅
  have hme₆ : e₅.memory = e₆.memory := (of_run_pushB256 z₆).memory
  have hS := hS.trans (Ninst.Hinv.inv (f := Devm.getStor) z₆)
  have hE := hE.trans (Ninst.Hinv.inv (f := Devm.getCode) z₆)
  refine run_prepend_elim _ (mstoreAt newPauserWord) ?_ hrun
  intro e₇ m₇ hrun
  obtain ⟨hp₇, hwf₇, hr₇⟩ :=
    mstoreAt_image hp₆ (wf_of_mem_eq hme₆ hwf₅) (hme₆ ▸ hr₅) m₇
  have hS := hS.trans (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) m₇)
  have hE := hE.trans (Line.of_inv Devm.getCode (by unfold mstoreAt; line_inv) m₇)
  rcases of_run_next hrun with ⟨e₈, z₈, hrun⟩
  have hp₈ := prefix_of_push (of_run_pushB256 z₈) hp₇
  have hme₈ : e₇.memory = e₈.memory := (of_run_pushB256 z₈).memory
  have hS := hS.trans (Ninst.Hinv.inv (f := Devm.getStor) z₈)
  have hE := hE.trans (Ninst.Hinv.inv (f := Devm.getCode) z₈)
  refine run_prepend_elim _ (mstoreAt previousPauserWord) ?_ hrun
  intro e₉ m₉ hrun
  obtain ⟨hp₉, hwf₉, hr₉⟩ :=
    mstoreAt_image hp₈ (wf_of_mem_eq hme₈ hwf₇) (hme₈ ▸ hr₇) m₉
  have hS := hS.trans (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) m₉)
  have hE := hE.trans (Line.of_inv Devm.getCode (by unfold mstoreAt; line_inv) m₉)
  rcases of_run_next hrun with ⟨f₁, z₁₀, hrun⟩
  have hp₁₀ := prefix_of_push (of_run_pushB256 z₁₀) hp₉
  have hme₁₀ : e₉.memory = f₁.memory := (of_run_pushB256 z₁₀).memory
  have hS := hS.trans (Ninst.Hinv.inv (f := Devm.getStor) z₁₀)
  have hE := hE.trans (Ninst.Hinv.inv (f := Devm.getCode) z₁₀)
  refine run_prepend_elim _ (mstoreAt continuationWord) ?_ hrun
  intro f₂ m₁₁ hrun
  obtain ⟨hp₁₁, hwf₁₁, hr₁₁⟩ :=
    mstoreAt_image hp₁₀ (wf_of_mem_eq hme₁₀ hwf₉) (hme₁₀ ▸ hr₉) m₁₁
  have hS := hS.trans (Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) m₁₁)
  have hE := hE.trans (Line.of_inv Devm.getCode (by unfold mstoreAt; line_inv) m₁₁)
  -- (7) the tail jump into the shared kernel
  rcases of_run_call hrun with ⟨body, k₀, hget, hburn, hrun⟩
  obtain rfl : setPauserKernel = body :=
    Option.some.inj ((get_setPauserSlot dp).symm.trans hget)
  have hS := hS.trans (Burn.Inv.inv hburn)
  have hE := hE.trans (getCode_of_state hburn.state)
  have hwfk : Mem.Wf k₀.memory := wf_of_mem_eq hburn.memory hwf₁₁
  have hrk : Mem.Reads k₀.memory _ := hburn.memory ▸ hr₁₁
  have hcodek : some (k₀.getCode sevm.currentTarget).toList
      = Prog.compile (runtime dp) := code_of_getCode_eq hE hcode
  -- (8) the staged words, read back out of the image the kernel receives
  have hreadTarget :=
    read_writeAt_before targetWord continuationWord 1
      target_before_continuation
      (read_writeAt_before targetWord previousPauserWord 0
        target_before_previousPauser
        (read_writeAt_before targetWord newPauserWord 0
          target_before_newPauser
          (read_writeAt_self
            (Bytes.writeAt img₀ (durationWord * 32).toNat
              dur.toBytes)
            targetWord (Sevm.argWord sevm 0))))
  have hreadNew :=
    read_writeAt_before newPauserWord continuationWord 1
      newPauser_before_continuation
      (read_writeAt_before newPauserWord previousPauserWord 0
        newPauser_before_previousPauser
        (read_writeAt_self
          (Bytes.writeAt
            (Bytes.writeAt img₀ (durationWord * 32).toNat
              dur.toBytes)
            (targetWord * 32).toNat (Sevm.argWord sevm 0).toBytes)
          newPauserWord 0))
  have hreadCont := read_writeAt_self
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt img₀ (durationWord * 32).toNat
            dur.toBytes)
          (targetWord * 32).toNat (Sevm.argWord sevm 0).toBytes)
        (newPauserWord * 32).toNat (B256.toBytes 0))
      (previousPauserWord * 32).toNat (B256.toBytes 0))
    continuationWord 1
  -- (9) the landed kernel chain
  exact coherent_of_pauseKernelRun dp ih hwfk hrk hreadTarget hreadNew
    hreadCont (canonicalAddress_of_validAdr hvalid₀) hcodek
    (coherent_of_stor_eq hS hcoh) hrun

/-- **The seventeenth obligation.**  `pause` is the only endpoint that yields
to foreign code, so unlike `registerPauser` it consumes the deeper-frame
hypothesis; what it needs beside it is the memory invariant at the body's
entry and the contract's own compiled program. -/
theorem pause_funcSound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux pause := by
  intro sevm s r h_ct h_pre h_wf h_ih h_run
  subst h_ct
  exact ⟨trivial,
    coherent_pause dp h_ih h_wf h_pre.code (h_pre.inv.1 rfl) h_run⟩

theorem registrySpec_sound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).Sound ca :=
  registrySpec_sound_of_funcSound dp ca fun _ hp =>
    funcSound_of_mem_funcs dp ca (registerPauser_funcSound dp ca)
      (pause_funcSound dp ca) hp

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

/-! ## Reader-facing consequences of a stable future

`RegistryStable` is what the ladder carries; what a reader wants at the far end
of a history is its content.  The declarations below turn a stable world into
the facts that content supports — the installed runtime, an actual
`RegistryWitness`, the membership and index equivalences at an arbitrary
canonical target, and global count conservation — so that a caller never has to
unfold `RegistryCoherent` to use the headline theorem.

The witness is returned **existentially**, and deliberately so.  The entry list
at a future state need not be the checkpoint's: a callback re-entering the
contract as admin may legitimately register a pauser, which is exactly why the
invariant is existential in the list.  No declaration below states a same-list
claim, and none is derivable from what is proved here. -/

/-- The bridge between the two storage vocabularies.  The Registry results are
stated over `Devm.getStor post ca`, while a history-level world is a
`Jaune.State`.  The two lookups are the same function — `Devm.getStor d a`
is `(d.state.get a).stor` and `Jaune.State.getStor w a` is `(w.get a).stor` —
so a machine whose world state is `w` identifies them.  Only the world-state
field is set; nothing about the machine's stack, memory, gas or metadata
enters, and no execution is claimed to reach this machine. -/
private def registryView (w : Jaune.State) : Devm :=
  { (default : Devm) with
    world := { (default : Devm).world with state := w } }

/-- The bridge equation.  It holds by `rfl`, so it rewrites in either
direction. -/
private theorem registryView_getStor (w : Jaune.State) (a : Adr) :
    Devm.getStor (registryView w) a = w.getStor a := rfl

/-- **Consequence 1: the exact installed code.**  A stable world holds the
compiled runtime bytes at `ca`, spelled as the artifact rather than as a
`Prog.compile` obligation. -/
theorem RegistryStable.installedCode {dp : DeployParams} {ca : Adr}
    {w : Jaune.State} (stable : RegistryStable dp ca w) :
    (w.getCode ca).toList = lidoCircuitBreakerCode dp :=
  Option.some.inj (stable.code.trans (lidoCircuitBreakerCode_compile dp))

/-- **Consequence 2: an actual witness.**  The entry list is existential: it is
the list `ca`'s storage carries at `w`, not the one carried at any earlier
checkpoint. -/
theorem RegistryStable.witness {dp : DeployParams} {ca : Adr}
    {w : Jaune.State} (stable : RegistryStable dp ca w) :
    ∃ entries, RegistryWitness (logicalStorageOfStor (w.getStor ca)) entries :=
  stable.coherent

/-- `membershipEquivalence_registerPauser`, transported across the storage
bridge to a world state. -/
private theorem membership_of_witness {w : Jaune.State} {ca : Adr}
    {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor (w.getStor ca)) entries)
    {target : B256} (htarget : canonicalAddress target) :
    ((w.getStor ca).get (assignmentSlot target) ≠ 0 ↔
      target ∈ entries.map Prod.fst) ∧
    ((w.getStor ca).get (indexSlot target) ≠ 0 ↔
      target ∈ entries.map Prod.fst) ∧
    ∀ index pauser, findEntry entries target = some (index, pauser) →
      (w.getStor ca).get (assignmentSlot target) = pauser ∧
      (w.getStor ca).get (indexSlot target) = Nat.toB256 (index + 1) ∧
      targetAt entries index = target ∧
      ∀ otherIndex, otherIndex < entries.length →
        targetAt entries otherIndex = target → otherIndex = index := by
  rw [← registryView_getStor w ca] at hw ⊢
  exact membershipEquivalence_registerPauser hw htarget

/-- `globalCountConservation_registerPauser`, transported across the storage
bridge to a world state. -/
private theorem countConservation_of_witness {w : Jaune.State} {ca : Adr}
    {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor (w.getStor ca)) entries) :
    (∀ pauser, canonicalAddress pauser →
      (w.getStor ca).get (countSlot pauser) =
        Nat.toB256 (assignmentCount entries pauser)) ∧
    (w.getStor ca).get (countSlot 0) = 0 ∧
    (∑ pauser ∈ (entries.map Prod.snd).toFinset,
      ((w.getStor ca).get (countSlot pauser)).toNat) = entries.length := by
  rw [← registryView_getStor w ca] at hw ⊢
  exact globalCountConservation_registerPauser hw

/-- **Consequence 3: membership and index equivalence.**  At an arbitrary
canonical target, a nonzero assignment word, a nonzero index word and
membership in the witness list are the same fact, and a target the list does
contain sits at the unique array position its index word names. -/
theorem RegistryStable.membership {dp : DeployParams} {ca : Adr}
    {w : Jaune.State} (stable : RegistryStable dp ca w)
    {target : B256} (htarget : canonicalAddress target) :
    ∃ entries,
      RegistryWitness (logicalStorageOfStor (w.getStor ca)) entries ∧
      ((w.getStor ca).get (assignmentSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      ((w.getStor ca).get (indexSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      ∀ index pauser, findEntry entries target = some (index, pauser) →
        (w.getStor ca).get (assignmentSlot target) = pauser ∧
        (w.getStor ca).get (indexSlot target) = Nat.toB256 (index + 1) ∧
        targetAt entries index = target ∧
        ∀ otherIndex, otherIndex < entries.length →
          targetAt entries otherIndex = target → otherIndex = index := by
  obtain ⟨entries, hw⟩ := stable.coherent
  exact ⟨entries, hw, membership_of_witness hw htarget⟩

/-- **Consequence 4: global count conservation.**  Every canonical pauser's
count word is its multiplicity in the witness list, the zero pauser's count is
clear, and the live per-pauser counts sum to the array length. -/
theorem RegistryStable.countConservation {dp : DeployParams} {ca : Adr}
    {w : Jaune.State} (stable : RegistryStable dp ca w) :
    ∃ entries,
      RegistryWitness (logicalStorageOfStor (w.getStor ca)) entries ∧
      (∀ pauser, canonicalAddress pauser →
        (w.getStor ca).get (countSlot pauser) =
          Nat.toB256 (assignmentCount entries pauser)) ∧
      (w.getStor ca).get (countSlot 0) = 0 ∧
      (∑ pauser ∈ (entries.map Prod.snd).toFinset,
        ((w.getStor ca).get (countSlot pauser)).toNat) = entries.length := by
  obtain ⟨entries, hw⟩ := stable.coherent
  exact ⟨entries, hw, countConservation_of_witness hw⟩

/-! ### The same four facts, read off a reachable future

Each corollary takes the checkpoint's stability and a reachability witness and
concludes about `future.state` directly.  They are the headline theorem's
content in the form a reader consumes it. -/

/-- The compiled runtime is still the code installed at `ca` at every state the
configured valid-chain relation reaches. -/
theorem chainUsing_future_installedCode (dp : DeployParams) (ca : Adr)
    (cfg : ChainConfig) (checkpoint future : BlockChain)
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    (future.state.getCode ca).toList = lidoCircuitBreakerCode dp :=
  (chainUsing_preserves_registryStable dp ca cfg checkpoint future reach
    stable).installedCode

/-- Some ordered entry list witnesses every projected Registry region of `ca`'s
storage at the reached future.  The list is existential: a callback that
re-enters as admin may register a pauser, so it need not be the checkpoint's,
and no same-list claim is made. -/
theorem chainUsing_future_witness (dp : DeployParams) (ca : Adr)
    (cfg : ChainConfig) (checkpoint future : BlockChain)
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    ∃ entries,
      RegistryWitness (logicalStorageOfStor (future.state.getStor ca)) entries :=
  (chainUsing_preserves_registryStable dp ca cfg checkpoint future reach
    stable).witness

/-- Membership and index equivalence at an arbitrary canonical target, at the
reached future. -/
theorem chainUsing_future_membership (dp : DeployParams) (ca : Adr)
    (cfg : ChainConfig) (checkpoint future : BlockChain)
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state)
    {target : B256} (htarget : canonicalAddress target) :
    ∃ entries,
      RegistryWitness (logicalStorageOfStor (future.state.getStor ca)) entries ∧
      ((future.state.getStor ca).get (assignmentSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      ((future.state.getStor ca).get (indexSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      ∀ index pauser, findEntry entries target = some (index, pauser) →
        (future.state.getStor ca).get (assignmentSlot target) = pauser ∧
        (future.state.getStor ca).get (indexSlot target) =
          Nat.toB256 (index + 1) ∧
        targetAt entries index = target ∧
        ∀ otherIndex, otherIndex < entries.length →
          targetAt entries otherIndex = target → otherIndex = index :=
  (chainUsing_preserves_registryStable dp ca cfg checkpoint future reach
    stable).membership htarget

/-- Global count conservation at the reached future. -/
theorem chainUsing_future_countConservation (dp : DeployParams) (ca : Adr)
    (cfg : ChainConfig) (checkpoint future : BlockChain)
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    ∃ entries,
      RegistryWitness (logicalStorageOfStor (future.state.getStor ca)) entries ∧
      (∀ pauser, canonicalAddress pauser →
        (future.state.getStor ca).get (countSlot pauser) =
          Nat.toB256 (assignmentCount entries pauser)) ∧
      (future.state.getStor ca).get (countSlot 0) = 0 ∧
      (∑ pauser ∈ (entries.map Prod.snd).toFinset,
        ((future.state.getStor ca).get (countSlot pauser)).toNat) =
          entries.length :=
  (chainUsing_preserves_registryStable dp ca cfg checkpoint future reach
    stable).countConservation

/-- The Prague instance of `chainUsing_future_installedCode`. -/
theorem chain_future_installedCode (dp : DeployParams) (ca : Adr)
    (checkpoint future : BlockChain)
    (reach : BlockChain.Reach checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    (future.state.getCode ca).toList = lidoCircuitBreakerCode dp :=
  (chain_preserves_registryStable dp ca checkpoint future reach
    stable).installedCode

/-- The Prague instance of `chainUsing_future_witness`. -/
theorem chain_future_witness (dp : DeployParams) (ca : Adr)
    (checkpoint future : BlockChain)
    (reach : BlockChain.Reach checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    ∃ entries,
      RegistryWitness (logicalStorageOfStor (future.state.getStor ca)) entries :=
  (chain_preserves_registryStable dp ca checkpoint future reach stable).witness

/-- The Prague instance of `chainUsing_future_membership`. -/
theorem chain_future_membership (dp : DeployParams) (ca : Adr)
    (checkpoint future : BlockChain)
    (reach : BlockChain.Reach checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state)
    {target : B256} (htarget : canonicalAddress target) :
    ∃ entries,
      RegistryWitness (logicalStorageOfStor (future.state.getStor ca)) entries ∧
      ((future.state.getStor ca).get (assignmentSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      ((future.state.getStor ca).get (indexSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      ∀ index pauser, findEntry entries target = some (index, pauser) →
        (future.state.getStor ca).get (assignmentSlot target) = pauser ∧
        (future.state.getStor ca).get (indexSlot target) =
          Nat.toB256 (index + 1) ∧
        targetAt entries index = target ∧
        ∀ otherIndex, otherIndex < entries.length →
          targetAt entries otherIndex = target → otherIndex = index :=
  (chain_preserves_registryStable dp ca checkpoint future reach
    stable).membership htarget

/-- The Prague instance of `chainUsing_future_countConservation`. -/
theorem chain_future_countConservation (dp : DeployParams) (ca : Adr)
    (checkpoint future : BlockChain)
    (reach : BlockChain.Reach checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    ∃ entries,
      RegistryWitness (logicalStorageOfStor (future.state.getStor ca)) entries ∧
      (∀ pauser, canonicalAddress pauser →
        (future.state.getStor ca).get (countSlot pauser) =
          Nat.toB256 (assignmentCount entries pauser)) ∧
      (future.state.getStor ca).get (countSlot 0) = 0 ∧
      (∑ pauser ∈ (entries.map Prod.snd).toFinset,
        ((future.state.getStor ca).get (countSlot pauser)).toNat) =
          entries.length :=
  (chain_preserves_registryStable dp ca checkpoint future reach
    stable).countConservation

/-! ## Narrowing controls on the shared reachability vocabulary

Two obligations that no re-pinning can reach.

`BlockChain.Reach` and `BlockChain.ReachUsing` are `Blanc/Ladder.lean`'s, not
this family's: the history theorems are written in them but do not own them.
Their text is pinned outside this file, and so are the tokens their bodies
must still mention -- but a token net checks *presence*, so a narrowing that
only ADDS a premise to `step` leaves every required token exactly where it
was.  Re-taken digests would then carry it through, and the headline history
theorems would quietly become claims about the narrowed blocks alone.

The two controls below are the net that is not a recorded string.  Each
extends a reach chain by a block of which nothing whatever is assumed beyond
`step`'s own two premises, so a `step` that demanded anything further -- an
empty transaction list, a bound on the block's own contents, a restriction on
who may have authored it -- could not be applied, and the control would stop
compiling.  A digest survives being re-taken; a failed elaboration does not. -/

/-- **Narrowing control, the configured chain.**  A `ReachUsing` chain extends
by an arbitrary block.  `block` is universally quantified, and the only things
assumed of it are the no-overflow bound and the successful configured
transition, which are exactly `BlockChain.ReachUsing.step`'s own premises.

Any further premise added to that constructor breaks this control, because a
narrowed `step` is not applicable to an unconstrained `block`.  That is the
point: the reachable futures `chainUsing_preserves_registryStable` and the
four `chainUsing_future_*` corollaries quantify over are as wide as the
constructor lets them be, and this obligation is what holds them there. -/
theorem reachUsing_extends_by_arbitrary_block (cfg : ChainConfig)
    {checkpoint future extended : BlockChain} (block : Block)
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (h_bound : sum future.state.bal + wdsum block.wds < 2 ^ 256)
    (h_step : stateTransitionUsing cfg future block = .ok extended) :
    BlockChain.ReachUsing cfg checkpoint extended :=
  .step reach h_bound h_step

/-- **Narrowing control, the Prague chain.**  The same obligation at
`BlockChain.Reach`, at the same strength: its `step` carries the same two
premises over the unconfigured transition, so the same arbitrary `block`
discharges it and the same additive narrowing breaks it.

Both relations are held here rather than only the configured one, because
`chain_preserves_registryStable` and the four `chain_future_*` corollaries
read their futures off `Reach`, and a narrowing there would restrict them
without touching `ReachUsing` at all. -/
theorem reach_extends_by_arbitrary_block
    {checkpoint future extended : BlockChain} (block : Block)
    (reach : BlockChain.Reach checkpoint future)
    (h_bound : sum future.state.bal + wdsum block.wds < 2 ^ 256)
    (h_step : stateTransition future block = .ok extended) :
    BlockChain.Reach checkpoint extended :=
  .step reach h_bound h_step

/-! ## Anti-vacuity controls

Three checks that the results above have content.  Each one reads the fields
*inside* `RegistryWitness` — or exhibits a state satisfying them — rather than
restating a public header, so a `RegistryCoherent` weakened to something that
no longer yields a real witness, or a `RegistryWitness` field gutted to a
triviality, fails here rather than passing silently. -/

private theorem byteArray_mk_toArray_toList (bs : Bytes) :
    (ByteArray.mk bs.toArray).toList = bs := by
  rw [ByteArray.toList_eq_toList_data]

/-- A synthetic world holding the compiled runtime at `ca` over an all-zero
Registry.

**This is not a deployment.**  No constructor runs, no transaction executes,
and nothing here claims that any chain ever reaches this world — pairing it
with `ReachUsing.refl` would add nothing, because a zero-step reach carries no
execution.  Its only job is to exhibit one model of `RegistryStable`, so that
the history theorems above are not vacuously true. -/
def emptyRegistryWorld (dp : DeployParams) (ca : Adr) : Jaune.State :=
  Jaune.State.set (.empty : Jaune.State) ca
    { Acct.nil with code := ByteArray.mk (lidoCircuitBreakerCode dp).toArray }

private theorem emptyRegistryWorld_get (dp : DeployParams) (ca : Adr) :
    (emptyRegistryWorld dp ca).get ca =
      { Acct.nil with
        code := ByteArray.mk (lidoCircuitBreakerCode dp).toArray } :=
  Jaune.State.get_set_self _ _ _

/-- **Control 1, satisfiability.**  The all-zero Registry really does satisfy
every `RegistryWitness` field at the empty entry list: the length word, the
array words, the assignment, index and count words at every canonical
argument, and the zero-pauser count.  This is the whole structure, checked
field by field against `emptyWitness`, not a header. -/
theorem emptyRegistryWorld_witness (dp : DeployParams) (ca : Adr) :
    RegistryWitness
      (logicalStorageOfStor ((emptyRegistryWorld dp ca).getStor ca)) [] := by
  show RegistryWitness
    (logicalStorageOfStor ((emptyRegistryWorld dp ca).get ca).stor) []
  rw [emptyRegistryWorld_get]
  exact emptyWitness

/-- **Control 1, the invariant is inhabited.**  `RegistryStable` holds at the
synthetic world, so the frame, transaction, block and history theorems above
have a nonempty premise set.  Again: an exhibit, not a deployment. -/
theorem emptyRegistryWorld_registryStable (dp : DeployParams) (ca : Adr) :
    RegistryStable dp ca (emptyRegistryWorld dp ca) where
  code := by
    show some ((emptyRegistryWorld dp ca).get ca).code.toList = _
    rw [emptyRegistryWorld_get, lidoCircuitBreakerCode_compile]
    exact congrArg some (byteArray_mk_toArray_toList _)
  coherent := ⟨[], emptyRegistryWorld_witness dp ca⟩

/-- **Control 1, the fields at the exhibited world.**  The satisfying world's
Registry slots, read off the witness field by field: a clear length word, a
clear zero-pauser count, and clear assignment, index and count words at every
canonical argument.  Naming the fields is the point — a witness whose
`lengthWord`, `assignments`, `indices`, `counts` or `zeroCount` field had been
gutted could not supply these. -/
theorem emptyRegistryWorld_registryFields (dp : DeployParams) (ca : Adr) :
    ((emptyRegistryWorld dp ca).getStor ca).get arrayLengthSlot = 0 ∧
    ((emptyRegistryWorld dp ca).getStor ca).get (countSlot 0) = 0 ∧
    ∀ target, canonicalAddress target →
      ((emptyRegistryWorld dp ca).getStor ca).get (assignmentSlot target) = 0 ∧
      ((emptyRegistryWorld dp ca).getStor ca).get (indexSlot target) = 0 ∧
      ((emptyRegistryWorld dp ca).getStor ca).get (countSlot target) = 0 := by
  have hw := emptyRegistryWorld_witness dp ca
  have hzero : Nat.toB256 0 = (0 : B256) := rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa [logicalStorageOfStor, hzero] using hw.lengthWord
  · simpa [logicalStorageOfStor] using hw.zeroCount
  · intro target htarget
    refine ⟨?_, ?_, ?_⟩
    · simpa [logicalStorageOfStor, assignmentAt] using
        hw.assignments target htarget
    · simpa [logicalStorageOfStor, oneBasedIndexAt, hzero] using
        hw.indices target htarget
    · simpa [logicalStorageOfStor, assignmentCount, hzero] using
        hw.counts target htarget

/-- **Control 2, an arbitrary execution.**  The public frame theorem is applied
to an unconstrained successful execution rooted at the contract's own program:
the callee of every `CALL` and `STATICCALL` the run issues is unconstrained,
there is no non-reentrancy premise, no target-bytecode premise, and no
direct-call-only premise.  Beside the execution itself, the hypotheses are
exactly the three `ContractSpec.Preserves` carries: the contract's own compiled
program at the frame's root, memory well-formedness when the frame is the
contract's own, and the frame-entry precondition.

The conclusion reads fields: the length word, every array word below the
length, and the zero-pauser count are projected out of the post-witness.  A
witness whose `lengthWord`, `arrayWords` or `zeroCount` field had been gutted
could not supply them. -/
theorem arbitraryExec_post_registryFields (dp : DeployParams) (ca : Adr)
    (sevm : Sevm) (pre post : Devm)
    (hexec : Exec 0 sevm pre (.ok post))
    (hcode : sevm.currentTarget = ca →
      some sevm.code.toList = Prog.compile (runtime dp))
    (hwf : sevm.currentTarget = ca → Mem.Wf pre.memory)
    (hpre : (registrySpec dp).Pre ca sevm pre) :
    ∃ entries,
      RegistryWitness (logicalStorageOfStor (Devm.getStor post ca)) entries ∧
      (Devm.getStor post ca).get arrayLengthSlot = Nat.toB256 entries.length ∧
      (∀ index, index < entries.length →
        (Devm.getStor post ca).get (arrayEntrySlot (Nat.toB256 (index + 1))) =
          targetAt entries index) ∧
      (Devm.getStor post ca).get (countSlot 0) = 0 := by
  obtain ⟨entries, hw⟩ :=
    (registrySpec_preserves dp ca sevm pre post hexec hcode hwf hpre).inv
  refine ⟨entries, hw, ?_, ?_, ?_⟩
  · simpa [logicalStorageOfStor] using hw.lengthWord
  · intro index bound
    simpa [logicalStorageOfStor] using hw.arrayWords index bound
  · simpa [logicalStorageOfStor] using hw.zeroCount

/-- **Control 3, fields at an arbitrary reachable future.**  From nothing but a
stable checkpoint and a reachability witness, six `RegistryWitness` fields are
projected out at the future state — `targetsNodup`, `pausersValid`,
`lengthWord`, `arrayWords`, `counts` and `zeroCount` — together with the index
membership equivalence the assignment and index fields support.

Every conjunct is a field read, not a restatement of a public header, so
weakening `RegistryCoherent` to something that no longer yields a real witness
breaks this control. -/
theorem arbitraryFuture_registryFields (dp : DeployParams) (ca : Adr)
    (cfg : ChainConfig) (checkpoint future : BlockChain)
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state)
    (target : B256) (htarget : canonicalAddress target) :
    ∃ entries,
      (entries.map Prod.fst).Nodup ∧
      (∀ entry ∈ entries, nonzeroCanonicalAddress entry.2) ∧
      (future.state.getStor ca).get arrayLengthSlot =
        Nat.toB256 entries.length ∧
      (∀ index, index < entries.length →
        (future.state.getStor ca).get
            (arrayEntrySlot (Nat.toB256 (index + 1))) =
          targetAt entries index) ∧
      ((future.state.getStor ca).get (indexSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      (future.state.getStor ca).get (countSlot target) =
        Nat.toB256 (assignmentCount entries target) ∧
      (future.state.getStor ca).get (countSlot 0) = 0 := by
  obtain ⟨entries, hw⟩ :=
    (chainUsing_preserves_registryStable dp ca cfg checkpoint future reach
      stable).coherent
  refine ⟨entries, hw.targetsNodup, hw.pausersValid, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [logicalStorageOfStor] using hw.lengthWord
  · intro index bound
    simpa [logicalStorageOfStor] using hw.arrayWords index bound
  · exact (membership_of_witness hw htarget).2.1
  · simpa [logicalStorageOfStor] using hw.counts target htarget
  · simpa [logicalStorageOfStor] using hw.zeroCount

end LidoCircuitBreaker

end Blanc
