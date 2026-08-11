import Blanc.Weth10AllowanceArmsRedeem

/-!
The delegated redemption arms of the allowance-region transport.

`withdrawFrom` and the zero-recipient `transferFrom` are the two selectors
that compose both halves of the transport: the `spendCallerAllowanceThen`
wrapper, whose self/max/finite fork is the frame's own allowance record,
and a caller-owned redemption core, whose external value `CALL` may reenter
WETH10 and therefore contributes the committed child's counted stream.
The frame's ledger is `own :: inner`, and the storage side is the
chronological composition of the wrapper's singleton replay with the core's
child transport.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Carried memory observations

The allowance wrapper writes the two key words and the approval payload, so
the redemption core it reaches is entered with a different memory image than
the frame.  Only well-formedness and readability survive, and only those are
needed. -/

/-- Memory well-formedness and readability carried across a segment. -/
private def MemCarried (pre post : Devm) : Prop :=
  ∀ {img : Bytes}, Mem.Wf pre.memory → Mem.Reads pre.memory img →
    Mem.Wf post.memory ∧ ∃ out, Mem.Reads post.memory out

private theorem MemCarried.of_eq {pre post : Devm}
    (h : pre.memory = post.memory) : MemCarried pre post := by
  intro img hwf hreads
  rw [← h]
  exact ⟨hwf, img, hreads⟩

private theorem MemCarried.trans {pre mid post : Devm}
    (h₁ : MemCarried pre mid) (h₂ : MemCarried mid post) :
    MemCarried pre post := by
  intro img hwf hreads
  rcases h₁ hwf hreads with ⟨hwfMid, out, hreadsMid⟩
  exact h₂ hwfMid hreadsMid

/-! ## Counted internal calls with observations

The counted mirror of `Exec.Frame.CompiledCursor.enterCallSilent`: a
generated internal source call is push/jump/jumpdest only, so reaching the
called body burns gas and changes nothing else. -/

/-! ## The allowance wrapper's own lines -/

private def spendOwnerEqLine : Line := arg 0 ++ [Ninst.caller, Ninst.eq]

private def spendAllowanceLoadLine : Line :=
  arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
    allowanceKeyFromMemory ++
    [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++ isMax

private def spendAllowanceCheckLine (amount : B256) : Line :=
  arg amount ++ [Ninst.swap 0] ++ balanceTooSmall

private def spendAllowanceStoreLine : Line :=
  [Ninst.sub, Ninst.dup 0, Ninst.swap 1, Ninst.sstore]

private def spendAllowanceAfterStoreLine : Line :=
  arg 0 ++ [Ninst.swap 0, Ninst.caller] ++ emitApproval ++
    [Ninst.pop, Ninst.pop]

/-- The allowance loader exposes the exact tagged runtime key, the loaded
allowance, and the max-allowance flag, and carries the memory image. -/
private theorem spendAllowanceLoadLine_effect
    {e : Sevm} {s r : Devm} {img : Bytes}
    (hwf : Mem.Wf s.memory)
    (hreads : Mem.Reads s.memory img)
    (run : Line.Run e s spendAllowanceLoadLine r) :
    ∃ allowance : B256,
      allowance = (Devm.getStor s e.currentTarget).get
        (callerAllowanceRuntimeKey e) ∧
      (((~~~ allowance) =? 0) :: allowance ::
        callerAllowanceRuntimeKey e :: []) <<+ r.stack ∧
      Mem.Wf r.memory ∧ ∃ out, Mem.Reads r.memory out := by
  let keyLine : Line :=
    arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
      allowanceKeyFromMemory
  unfold spendAllowanceLoadLine at run
  rcases of_run_append keyLine run with ⟨sk, hkeyLine, runKey⟩
  have hmemTail : sk.memory = r.memory :=
    Line.of_inv Devm.memory (by line_inv) runKey
  have hkey : Line.Run e s
      (arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
        allowanceKeyFromMemory) sk := by
    simpa only [keyLine] using hkeyLine
  obtain ⟨hpKey, hwfKey, out, hreadsKey⟩ :=
    of_callerAllowanceKeyPrefix hwf hreads hkey
  rcases Line.of_run_cons runKey with ⟨si1, hdupKey, runKey1⟩
  have hpI1 : callerAllowanceRuntimeKey e ::
      callerAllowanceRuntimeKey e :: [] <<+ si1.stack :=
    prefix_of_dup_val hdupKey (by show_nth) hpKey
  rcases Line.of_run_cons runKey1 with ⟨si2, hload, runKey2⟩
  rcases prefix_of_sload hload hpI1 with ⟨allowance, hpI2, hallowanceRead⟩
  rcases Line.of_run_cons runKey2 with ⟨si3, hdupAllowance, runKey3⟩
  have hpI3 : allowance :: allowance ::
      callerAllowanceRuntimeKey e :: [] <<+ si3.stack :=
    prefix_of_dup_val hdupAllowance (by show_nth) hpI2
  unfold isMax at runKey3
  rcases Line.of_run_cons runKey3 with ⟨si4, hnot, runKey4⟩
  have hpI4 : (~~~ allowance) :: allowance ::
      callerAllowanceRuntimeKey e :: [] <<+ si4.stack :=
    prefix_of_not hnot hpI3
  rcases Line.of_run_cons runKey4 with ⟨si5, hiszeroMax, hnilInspect⟩
  cases hnilInspect
  have hpLoad : ((~~~ allowance) =? 0) :: allowance ::
      callerAllowanceRuntimeKey e :: [] <<+ r.stack :=
    prefix_of_iszero hiszeroMax hpI4
  have hstorKey : Devm.getStor s = Devm.getStor si1 :=
    (Line.of_inv Devm.getStor (by line_inv) hkey).trans
      (Ninst.Hinv.inv (f := Devm.getStor) hdupKey)
  refine ⟨allowance, ?_, hpLoad, ?_, out, ?_⟩
  · rw [hallowanceRead]
    change (Devm.getStor si1 e.currentTarget).get
      (callerAllowanceRuntimeKey e) = _
    rw [← congrFun hstorKey e.currentTarget]
  · rw [← hmemTail]
    exact hwfKey
  · rw [← hmemTail]
    exact hreadsKey

/-- Local copy of the compiled module's private approval-tail memory walk. -/
private theorem spendAllowanceAfterStoreLine_memory
    {e : Sevm} {pre post : Devm} {reduced : B256} {img : Bytes}
    (hp : reduced :: [] <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory img)
    (run : Line.Run e pre spendAllowanceAfterStoreLine post) :
    Mem.Wf post.memory ∧ ∃ out, Mem.Reads post.memory out := by
  unfold spendAllowanceAfterStoreLine at run
  rcases of_run_append (arg 0) run with ⟨s₁, howner, run⟩
  have hp₁ : Sevm.argWord e 0 :: reduced :: [] <<+ s₁.stack :=
    prefix_of_arg hp howner
  rcases Line.of_run_cons run with ⟨s₂, hswap, run⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord e 0, reduced] [reduced, Sevm.argWord e 0] :=
    Stack.swapCore_zero
  have hp₂ : reduced :: Sevm.argWord e 0 :: [] <<+ s₂.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp₁
  rcases Line.of_run_cons run with ⟨s₃, hcaller, run⟩
  have hp₃ : e.caller.toB256 :: reduced :: Sevm.argWord e 0 :: [] <<+
      s₃.stack := prefix_of_push (of_run_caller hcaller) hp₂
  rcases of_run_append emitApproval run with ⟨s₄, hemit, run⟩
  have hmemory : pre.memory = s₃.memory :=
    (Line.of_inv Devm.memory (by line_inv) howner).trans
      ((Ninst.Hinv.inv (f := Devm.memory) hswap).trans
        (of_run_caller hcaller).memory)
  have hwf₃ : Mem.Wf s₃.memory := by
    rw [← hmemory]
    exact hwf
  have hreads₃ : Mem.Reads s₃.memory img := by
    rw [← hmemory]
    exact hreads
  obtain ⟨_hp, _hlogs, _hstor, _hbal, _hcode, _houtput,
      hwf₄, out, hreads₄⟩ :=
    emitApproval_effect hp₃ hwf₃ hreads₃ hemit
  rcases Line.of_run_cons run with ⟨s₅, hpop₁, run⟩
  rcases Line.of_run_cons run with ⟨s₆, hpop₂, hnil⟩
  cases hnil
  have hmemoryPost : s₄.memory = post.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) hpop₁).trans
      (Ninst.Hinv.inv (f := Devm.memory) hpop₂)
  rw [← hmemoryPost]
  exact ⟨hwf₄, out, hreads₄⟩

/-! ## The wrapper's storage fork at the counted altitude

`CallerAllowanceOutcome` states the same fork at the `Func.Run` altitude,
but its witness state is not the counted cursor's, so the walk is redone
here.  Only the executing contract's storage is tracked: the logs and the
finite path's coverage bound play no part in allowance transport. -/

/-- The exact self/max/finite storage fork of the allowance wrapper. -/
private def SpendStorageFork (e : Sevm) (pre corePre : Devm)
    (amountArg : B256) : Prop :=
  (Sevm.argWord e 0 = e.caller.toB256 ∧
      Devm.getStor corePre e.currentTarget =
        Devm.getStor pre e.currentTarget) ∨
    (Sevm.argWord e 0 ≠ e.caller.toB256 ∧
      (((Devm.getStor pre e.currentTarget).get
            (callerAllowanceRuntimeKey e) = B256.max ∧
          Devm.getStor corePre e.currentTarget =
            Devm.getStor pre e.currentTarget) ∨
        (∃ allowance : B256,
          allowance ≠ B256.max ∧
          (Devm.getStor pre e.currentTarget).get
              (callerAllowanceRuntimeKey e) = allowance ∧
          Devm.getStor corePre e.currentTarget =
            (Devm.getStor pre e.currentTarget).set
              (callerAllowanceRuntimeKey e)
              (allowance - Sevm.argWord e amountArg))))

/-- Follow the actual successful allowance wrapper to its internal core
while retaining the storage fork, the installed code, and the memory
observations the core needs; the counted, allowance-tracking mirror of
`Exec.Frame.CompiledCursor.enterSpendCallerAllowanceThenWithObservations`. -/
private theorem Exec.Frame.CountedCursor.enterSpendCallerAllowanceThenFork
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {amount : B256} {nextSlot : Nat}
    {final : Devm} {img : Bytes}
    (cursor : frame.CountedCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux))
      (spendCallerAllowanceThen amount nextSlot) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (hallowanceError :
      (f₀ :: aux)[allowanceErrorSlot]? =
        some (Func.revWith "WETH: request exceeds allowance"))
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img) :
    ∃ body,
      (f₀ :: aux)[nextSlot]? = some body ∧
      ∃ bodyCursor : frame.CountedCursor dp ca (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        Mem.Wf bodyCursor.pre.memory ∧
        (∃ out, Mem.Reads bodyCursor.pre.memory out) ∧
        Devm.getCode cursor.pre = Devm.getCode bodyCursor.pre ∧
        SpendStorageFork frame.sevm cursor.pre bodyCursor.pre amount := by
  unfold spendCallerAllowanceThen at cursor
  rcases cursor.peelChildlessLine (line := spendOwnerEqLine)
      (by simp [spendOwnerEqLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨callerBranchCursor, hcallerLine⟩
  have hcallerPrefix :
      [frame.sevm.caller.toB256 =? Sevm.argWord frame.sevm 0] <<+
        callerBranchCursor.pre.stack := by
    unfold spendOwnerEqLine at hcallerLine
    rcases of_run_append (arg 0) hcallerLine with ⟨afterArg, harg, hrest⟩
    rcases Line.of_run_cons hrest with ⟨afterCaller, hcaller, heqLine⟩
    rcases Line.of_run_cons heqLine with ⟨afterEq, heq, hnil⟩
    cases hnil
    exact prefix_of_eq heq
      (prefix_of_push (of_run_caller hcaller) (prefix_of_arg nil_pref harg))
  have hcallerStor : Devm.getStor cursor.pre =
      Devm.getStor callerBranchCursor.pre :=
    Line.of_inv Devm.getStor (by unfold spendOwnerEqLine; line_inv)
      hcallerLine
  have hcallerCode : Devm.getCode cursor.pre =
      Devm.getCode callerBranchCursor.pre :=
    Line.of_inv Devm.getCode (by unfold spendOwnerEqLine; line_inv)
      hcallerLine
  have hcallerMem : MemCarried cursor.pre callerBranchCursor.pre :=
    MemCarried.of_eq
      (Line.of_inv Devm.memory (by unfold spendOwnerEqLine; line_inv)
        hcallerLine)
  by_cases hself : Sevm.argWord frame.sevm 0 = frame.sevm.caller.toB256
  · -- the self-owner path bypasses the allowance read entirely
    have hflag : (frame.sevm.caller.toB256 =? Sevm.argWord frame.sevm 0) = 1 := by
      simp [B256.eqCheck, hself]
    rw [hflag] at hcallerPrefix
    rcases callerBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
        (by decide) hcallerPrefix with
      ⟨directCursor, _hdirectStack, hdirectSilent⟩
    rcases directCursor.enterCallSilent hcode with
      ⟨body, hget, bodyCursor, hbodySilent⟩
    obtain ⟨hwfBody, out, hreadsBody⟩ :=
      MemCarried.trans hcallerMem
        (MemCarried.trans (MemCarried.of_eq hdirectSilent.memory)
          (MemCarried.of_eq hbodySilent.memory)) hwf hreads
    refine ⟨body, hget, bodyCursor, hwfBody, ⟨out, hreadsBody⟩, ?_, ?_⟩
    · rw [hcallerCode, funext (getCode_eq_of_state_eq hdirectSilent.state),
        funext (getCode_eq_of_state_eq hbodySilent.state)]
    · refine Or.inl ⟨hself, ?_⟩
      rw [hcallerStor, funext (getStor_eq_of_state_eq hdirectSilent.state),
        funext (getStor_eq_of_state_eq hbodySilent.state)]
  · have hne : frame.sevm.caller.toB256 ≠ Sevm.argWord frame.sevm 0 :=
      fun h => hself h.symm
    have hflag : (frame.sevm.caller.toB256 =? Sevm.argWord frame.sevm 0) = 0 := by
      simp [B256.eqCheck, hne]
    rw [hflag] at hcallerPrefix
    rcases callerBranchCursor.selectBranchZeroSilent hcallerPrefix with
      ⟨allowanceCursor, _hallowanceStack, hallowanceSilent⟩
    have hentryStor : Devm.getStor cursor.pre =
        Devm.getStor allowanceCursor.pre := by
      rw [hcallerStor, funext (getStor_eq_of_state_eq hallowanceSilent.state)]
    have hentryCode : Devm.getCode cursor.pre =
        Devm.getCode allowanceCursor.pre := by
      rw [hcallerCode, funext (getCode_eq_of_state_eq hallowanceSilent.state)]
    obtain ⟨hwfLoad, imgLoad, hreadsLoad⟩ :=
      MemCarried.trans hcallerMem
        (MemCarried.of_eq hallowanceSilent.memory) hwf hreads
    rcases allowanceCursor.peelChildlessLine (line := spendAllowanceLoadLine)
        (by simp [spendAllowanceLoadLine, arg, cdl, mstoreAt,
          allowanceKeyFromMemory, pushList, isMax, NinstIsChildless,
          Ninst.pushB256]) with
      ⟨maxBranchCursor, hloadLine⟩
    obtain ⟨allowance, hallowanceVal, hloadPrefix, hwfMax, outMax, hreadsMax⟩ :=
      spendAllowanceLoadLine_effect hwfLoad hreadsLoad hloadLine
    have hloadStor : Devm.getStor allowanceCursor.pre =
        Devm.getStor maxBranchCursor.pre :=
      Line.of_inv Devm.getStor (by unfold spendAllowanceLoadLine; line_inv)
        hloadLine
    have hloadCode : Devm.getCode allowanceCursor.pre =
        Devm.getCode maxBranchCursor.pre :=
      Line.of_inv Devm.getCode (by unfold spendAllowanceLoadLine; line_inv)
        hloadLine
    by_cases hmax : allowance = B256.max
    · -- an infinite allowance is preserved
      have hmaxFlag : ((~~~ allowance) =? 0) = 1 := by
        rw [hmax, B256.not_max]
        simp [B256.eqCheck]
      rw [hmaxFlag] at hloadPrefix
      rcases maxBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
          (by decide) hloadPrefix with
        ⟨maxCursor, _hmaxStack, hmaxSilent⟩
      rcases maxCursor.peelChildlessLine (line := [Ninst.pop, Ninst.pop])
          (by simp [NinstIsChildless]) with
        ⟨coreCallCursor, hpopLine⟩
      rcases coreCallCursor.enterCallSilent hcode with
        ⟨body, hget, bodyCursor, hbodySilent⟩
      obtain ⟨hwfBody, out, hreadsBody⟩ :=
        MemCarried.trans (MemCarried.of_eq hmaxSilent.memory)
          (MemCarried.trans
            (MemCarried.of_eq
              (Line.of_inv Devm.memory (by line_inv) hpopLine))
            (MemCarried.of_eq hbodySilent.memory)) hwfMax hreadsMax
      have hstor : Devm.getStor cursor.pre = Devm.getStor bodyCursor.pre := by
        rw [hentryStor, hloadStor,
          funext (getStor_eq_of_state_eq hmaxSilent.state),
          Line.of_inv Devm.getStor (by line_inv) hpopLine,
          funext (getStor_eq_of_state_eq hbodySilent.state)]
      refine ⟨body, hget, bodyCursor, hwfBody, ⟨out, hreadsBody⟩, ?_, ?_⟩
      · rw [hentryCode, hloadCode,
          funext (getCode_eq_of_state_eq hmaxSilent.state),
          Line.of_inv Devm.getCode (by line_inv) hpopLine,
          funext (getCode_eq_of_state_eq hbodySilent.state)]
      · refine Or.inr ⟨fun h => hne h.symm, Or.inl ⟨?_, ?_⟩⟩
        · rw [congrFun hentryStor frame.sevm.currentTarget, ← hallowanceVal]
          exact hmax
        · rw [hstor]
    · -- a finite allowance is decremented at the tagged runtime key
      have hmaxFlag : ((~~~ allowance) =? 0) = 0 := by
        rw [B256.eqCheck, if_neg]
        intro hzero
        exact hmax (B256.eq_max_of_not_eq_zero hzero)
      rw [hmaxFlag] at hloadPrefix
      rcases maxBranchCursor.selectBranchZeroSilent hloadPrefix with
        ⟨finiteCursor, hfiniteStack, hfiniteSilent⟩
      rcases finiteCursor.peelChildlessLine
          (line := spendAllowanceCheckLine amount)
          (by simp [spendAllowanceCheckLine, arg, cdl, balanceTooSmall,
            NinstIsChildless, Ninst.pushB256]) with
        ⟨spendBranchCursor, hcheckLine⟩
      have hcheckStack :
          (allowance <? Sevm.argWord frame.sevm amount) :: allowance ::
            Sevm.argWord frame.sevm amount ::
            callerAllowanceRuntimeKey frame.sevm :: [] <<+
              spendBranchCursor.pre.stack := by
        unfold spendAllowanceCheckLine at hcheckLine
        rcases of_run_append (arg amount) hcheckLine with
          ⟨afterArg, hargRun, hrest⟩
        have hpArg : Sevm.argWord frame.sevm amount :: allowance ::
            callerAllowanceRuntimeKey frame.sevm :: [] <<+ afterArg.stack :=
          prefix_of_arg hfiniteStack hargRun
        rcases of_run_append [Ninst.swap 0] hrest with
          ⟨afterSwap, hswapLine, hguard⟩
        rcases Line.of_run_cons hswapLine with ⟨afterSwap', hswap, hnil⟩
        cases hnil
        have hswapCore : Stack.Swap (0 : Fin 16).val
            [Sevm.argWord frame.sevm amount, allowance,
              callerAllowanceRuntimeKey frame.sevm]
            [allowance, Sevm.argWord frame.sevm amount,
              callerAllowanceRuntimeKey frame.sevm] :=
          Stack.swapCore_zero
        have hpSwap : allowance :: Sevm.argWord frame.sevm amount ::
            callerAllowanceRuntimeKey frame.sevm :: [] <<+ afterSwap.stack :=
          Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpArg
        exact prefix_of_balanceTooSmall hpSwap hguard
      rcases spendBranchCursor.selectBranchLeftWithBurn
          (not_run_call_revWith hallowanceError) with
        ⟨successCursor, hcheckPopBy⟩
      have hcheckPop := Devm.PopBurn.of_popBurnBy hcheckPopBy
      have hpopStack := hcheckPop.stack
      simp only [Stack.Pop, Split, List.nil_append,
        List.cons_append] at hpopStack
      rw [hpopStack] at hcheckStack
      have hguardFlag : (allowance <? Sevm.argWord frame.sevm amount) = 0 :=
        pref_head_unique hcheckStack
          (pref_append [0] successCursor.pre.stack)
      rw [hguardFlag] at hcheckStack
      have hsuccessStack : allowance :: Sevm.argWord frame.sevm amount ::
          callerAllowanceRuntimeKey frame.sevm :: [] <<+
            successCursor.pre.stack := cons_pref_cons_inv hcheckStack
      rcases successCursor.peelChildlessLine
          (line := spendAllowanceStoreLine ++ spendAllowanceAfterStoreLine)
          (by simp [spendAllowanceStoreLine, spendAllowanceAfterStoreLine,
            arg, cdl, emitApproval, mstoreAt, logWith, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨coreCallCursor, hspendLine⟩
      rcases of_run_append spendAllowanceStoreLine hspendLine with
        ⟨afterStore, hstoreLine, hafterLine⟩
      unfold spendAllowanceStoreLine at hstoreLine
      rcases Line.of_run_cons hstoreLine with ⟨d1, hsub, hstore1⟩
      have hpD1 : (allowance - Sevm.argWord frame.sevm amount) ::
          callerAllowanceRuntimeKey frame.sevm :: [] <<+ d1.stack :=
        prefix_of_sub hsub hsuccessStack
      rcases Line.of_run_cons hstore1 with ⟨d2, hdup, hstore2⟩
      have hpD2 : (allowance - Sevm.argWord frame.sevm amount) ::
          (allowance - Sevm.argWord frame.sevm amount) ::
          callerAllowanceRuntimeKey frame.sevm :: [] <<+ d2.stack :=
        prefix_of_dup_val hdup (by show_nth) hpD1
      rcases Line.of_run_cons hstore2 with ⟨d3, hswap1, hstore3⟩
      have hswapCore1 : Stack.Swap (1 : Fin 16).val
          [allowance - Sevm.argWord frame.sevm amount,
            allowance - Sevm.argWord frame.sevm amount,
            callerAllowanceRuntimeKey frame.sevm]
          [callerAllowanceRuntimeKey frame.sevm,
            allowance - Sevm.argWord frame.sevm amount,
            allowance - Sevm.argWord frame.sevm amount] :=
        Stack.swapCore_succ Stack.swapCore_zero
      have hpD3 : callerAllowanceRuntimeKey frame.sevm ::
          (allowance - Sevm.argWord frame.sevm amount) ::
          (allowance - Sevm.argWord frame.sevm amount) :: [] <<+ d3.stack :=
        Stack.prefix_of_swap hswapCore1 (of_run_swap hswap1) hpD2
      rcases Line.of_run_cons hstore3 with ⟨d4, hsstore, hnilStore⟩
      cases hnilStore
      have hsetStore : Devm.getStor afterStore frame.sevm.currentTarget =
          (Devm.getStor d3 frame.sevm.currentTarget).set
            (callerAllowanceRuntimeKey frame.sevm)
            (allowance - Sevm.argWord frame.sevm amount) :=
        sstore_getStor_set hsstore hpD3
      have hpAfter : (allowance - Sevm.argWord frame.sevm amount) :: [] <<+
          afterStore.stack := prefix_of_sstore hsstore hpD3
      have hstorePre : Devm.getStor successCursor.pre = Devm.getStor d3 :=
        (Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hsub Line.Run.nil)).trans
          ((Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons hdup Line.Run.nil)).trans
            (Line.of_inv Devm.getStor (by line_inv)
              (Line.Run.cons hswap1 Line.Run.nil)))
      have hstoreMem : successCursor.pre.memory = afterStore.memory :=
        (Ninst.Hinv.inv (f := Devm.memory) hsub).trans
          ((Ninst.Hinv.inv (f := Devm.memory) hdup).trans
            ((Ninst.Hinv.inv (f := Devm.memory) hswap1).trans
              (Ninst.Hinv.inv (f := Devm.memory) hsstore)))
      have hstoreCode : Devm.getCode successCursor.pre =
          Devm.getCode afterStore :=
        Line.of_inv Devm.getCode (by line_inv)
          (show Line.Run frame.sevm successCursor.pre
            [Ninst.sub, Ninst.dup 0, Ninst.swap 1, Ninst.sstore] afterStore
            from hstoreLine)
      obtain ⟨hwfSuccess, imgSuccess, hreadsSuccess⟩ :=
        MemCarried.trans (MemCarried.of_eq hfiniteSilent.memory)
          (MemCarried.trans
            (MemCarried.of_eq
              (Line.of_inv Devm.memory (by line_inv) hcheckLine))
            (MemCarried.of_eq hcheckPop.memory)) hwfMax hreadsMax
      obtain ⟨hwfCall, outCall, hreadsCall⟩ :=
        spendAllowanceAfterStoreLine_memory hpAfter
          (by rw [← hstoreMem]; exact hwfSuccess)
          (show Mem.Reads afterStore.memory imgSuccess by
            rw [← hstoreMem]; exact hreadsSuccess)
          hafterLine
      rcases coreCallCursor.enterCallSilent hcode with
        ⟨body, hget, bodyCursor, hbodySilent⟩
      have hwfBody : Mem.Wf bodyCursor.pre.memory := by
        rw [← hbodySilent.memory]
        exact hwfCall
      have hreadsBody : Mem.Reads bodyCursor.pre.memory outCall := by
        rw [← hbodySilent.memory]
        exact hreadsCall
      have hpreStor : Devm.getStor cursor.pre = Devm.getStor d3 := by
        rw [hentryStor, hloadStor,
          funext (getStor_eq_of_state_eq hfiniteSilent.state),
          Line.of_inv Devm.getStor (by line_inv) hcheckLine,
          PopBurn.Inv.inv (f := Devm.getStor) hcheckPop, hstorePre]
      have hpostStor : Devm.getStor afterStore =
          Devm.getStor bodyCursor.pre := by
        rw [Line.of_inv Devm.getStor (by line_inv) hafterLine,
          funext (getStor_eq_of_state_eq hbodySilent.state)]
      refine ⟨body, hget, bodyCursor, hwfBody, ⟨outCall, hreadsBody⟩, ?_, ?_⟩
      · rw [hentryCode, hloadCode,
          funext (getCode_eq_of_state_eq hfiniteSilent.state),
          Line.of_inv Devm.getCode (by line_inv) hcheckLine,
          funext (fun a => getCode_eq_of_state_eq hcheckPop.state a),
          hstoreCode, Line.of_inv Devm.getCode (by line_inv) hafterLine,
          funext (getCode_eq_of_state_eq hbodySilent.state)]
      · refine Or.inr ⟨fun h => hne h.symm, Or.inr
          ⟨allowance, hmax, ?_, ?_⟩⟩
        · rw [congrFun hentryStor frame.sevm.currentTarget, ← hallowanceVal]
        · rw [← congrFun hpostStor frame.sevm.currentTarget, hsetStore,
            congrFun hpreStor frame.sevm.currentTarget]

/-! ## The delegated redemption core

The two delegated cores debit the *normalized owner argument* rather than
the caller, and burn-emit from that same word, so the shared caller-owned
walk of `Weth10AllowanceArmsRedeem` does not apply to them.  This is its
delegated counterpart, additionally parameterized over the send-failure
reverter slot, which the two cores do not share. -/

private def redeemFromCheckLine (ownerArg amountArg : B256) : Line :=
  loadArgBalanceAmount ownerArg amountArg ++ balanceTooSmall

private def redeemFromEventLine (ownerArg amountArg : B256) : Line :=
  addressArg ownerArg ++ arg amountArg ++ [Ninst.pushB256 0] ++
    emitTransfer ++ [Ninst.swap 0, Ninst.pop]

/-- The shared delegated redemption body: balance guard at the normalized
owner argument, debit, burn event, send-operand prefix, external value
`CALL`, success guard. -/
private def redeemFromBody (ownerArg amountArg : B256) (sendPrefix : Line)
    (errSlot : Nat) (success : Func) : Func :=
  redeemFromCheckLine ownerArg amountArg +++
  ((.call burnBalanceErrorSlot) <?>
    (debitLoadedBalance +++
      redeemFromEventLine ownerArg amountArg +++
      sendPrefix +++
      Ninst.call ::: Ninst.iszero :::
      ((.call errSlot) <?> success)))

private theorem withdrawFromCore_eq_redeemFromBody :
    withdrawFromCore =
      redeemFromBody 0 2 (redeemSendToArgPrefix 1) etherTransferErrorSlot
        (Func.last .stop) := rfl

private theorem transferFromZero_eq_redeemFromBody :
    transferFromZero =
      redeemFromBody 0 2 redeemSendToCallerPrefix ethTransferErrorSlot
        (redeemReturnTrueLine +++ Func.last .ret) := rfl

/-- The shared delegated redemption walk: the guarded debit writes a single
address-shaped balance key at the normalized owner argument, the external
value `CALL` is identified with a retained child message whose
allowance-region delta is supplied by the recursion hypothesis, and the
trailing success guard contributes neither counted records nor storage
writes. -/
private theorem Exec.Frame.CountedCursor.redeemFromAllowanceStorage
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {ownerArg amountArg target : B256} {sendPrefix successLine : Line}
    {successLast : Linst} {img : Bytes} {errSlot : Nat} {reason : String}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (redeemFromBody ownerArg amountArg sendPrefix errSlot
        (successLine +++ Func.last successLast)) frame.post)
    (herr : ((weth10 dp).main :: weth10Aux)[errSlot]? =
      some (Func.revWith reason))
    (htarget : frame.sevm.currentTarget = ca)
    (hstack : [] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img)
    (hcursorCode : some (cursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hsendChildless : ∀ n ∈ sendPrefix, NinstIsChildless n)
    (hsend : ∀ {sendPre callPre : Devm} {value : B256} {tail : Stack},
      value :: tail <<+ sendPre.stack →
      Line.Run frame.sevm sendPre sendPrefix callPre →
      ValueCallOperandPrefix frame.sevm sendPre callPre value target tail)
    (hsuccessChildless : ∀ n ∈ successLine, NinstIsChildless n)
    (hsuccessStor : Func.Inv Devm.getStor Devm.getStor
      (successLine +++ Func.last successLast))
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    ∀ key, InRegion .allowance key →
      (Devm.getStor frame.post ca).get key =
        applyAllowanceLedger (Devm.getStor cursor.pre ca)
          (Exec.attributionInner dp ca frame.run) key := by
  rcases frame with ⟨fpc, e, fpre, fout, frun, fcommitted⟩
  cases fout with
  | error err => simp [Execution.commits] at fcommitted
  | ok fpost =>
      intro key hkey
      have htargetE : e.currentTarget = ca := htarget
      -- the guarded balance check
      unfold redeemFromBody at cursor
      rcases cursor.peelChildlessLine
          (line := redeemFromCheckLine ownerArg amountArg)
          (by simp [redeemFromCheckLine, loadArgBalanceAmount, addressArg,
            normalizeAddress, pushAddressMask, balanceTooSmall, arg, cdl,
            NinstIsChildless, Ninst.pushB256]) with
        ⟨branchCursor, hcheck⟩
      unfold redeemFromCheckLine at hcheck
      rcases of_run_append (loadArgBalanceAmount ownerArg amountArg)
          hcheck with
        ⟨afterLoad, hload, hguard⟩
      rcases prefix_of_loadArgBalanceAmount ownerArg amountArg hstack
          hload with
        ⟨balance, owner, howner, _hbalance, hloadStack⟩
      have hkeyNe : owner ≠ key := by
        refine (allowanceRegion_ne_validAdr hkey ?_).symm
        rw [howner]
        exact normalizedAddress_valid (Sevm.argWord e ownerArg)
      have hguardStack : (balance <? Sevm.argWord e amountArg) :: balance ::
          Sevm.argWord e amountArg :: owner :: [] <<+
            branchCursor.pre.stack :=
        prefix_of_balanceTooSmall hloadStack hguard
      rcases branchCursor.selectBranchLeftWithBurn
          (not_run_call_revWith (burnBalanceError_lookup dp)) with
        ⟨successCursor, hbalancePopBy⟩
      have hbalancePop := Devm.PopBurn.of_popBurnBy hbalancePopBy
      have hpopStack := hbalancePop.stack
      simp only [Stack.Pop, Split, List.nil_append,
        List.cons_append] at hpopStack
      rw [hpopStack] at hguardStack
      have hflag : (balance <? Sevm.argWord e amountArg) = 0 :=
        pref_head_unique hguardStack (pref_append [0] successCursor.pre.stack)
      rw [hflag] at hguardStack
      have hsuccessStack : balance :: Sevm.argWord e amountArg ::
          owner :: [] <<+ successCursor.pre.stack :=
        cons_pref_cons_inv hguardStack
      have hcheckStor : Devm.getStor cursor.pre =
          Devm.getStor successCursor.pre :=
        (Line.of_inv Devm.getStor (by line_inv) hload).trans
          ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
            (PopBurn.Inv.inv hbalancePop))
      have hcheckCode : Devm.getCode cursor.pre =
          Devm.getCode successCursor.pre :=
        (Line.of_inv Devm.getCode (by line_inv) hload).trans
          ((Line.of_inv Devm.getCode (by line_inv) hguard).trans
            (funext (getCode_eq_of_state_eq hbalancePop.state)))
      have hcheckMem : cursor.pre.memory = successCursor.pre.memory :=
        (Line.of_inv Devm.memory (by line_inv) hload).trans
          ((Line.of_inv Devm.memory (by line_inv) hguard).trans
            hbalancePop.memory)
      -- the owner-key debit
      rcases successCursor.peelChildlessLine (line := debitLoadedBalance)
          (by simp [debitLoadedBalance, NinstIsChildless]) with
        ⟨afterDebitCursor, hdebit⟩
      have hdebitCode : Devm.getCode successCursor.pre =
          Devm.getCode afterDebitCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hdebit
      have hdebitMem : successCursor.pre.memory =
          afterDebitCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hdebit
      unfold debitLoadedBalance at hdebit
      rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
      have hpD1 : (balance - Sevm.argWord e amountArg) ::
          owner :: [] <<+ d1.stack :=
        prefix_of_sub hsub hsuccessStack
      rcases Line.of_run_cons hdebit1 with ⟨d2, hswap, hdebit2⟩
      have hswapCoreD : Stack.Swap (0 : Fin 16).val
          [balance - Sevm.argWord e amountArg, owner]
          [owner, balance - Sevm.argWord e amountArg] :=
        Stack.swapCore_zero
      have hpD2 : owner ::
          (balance - Sevm.argWord e amountArg) :: [] <<+ d2.stack :=
        Stack.prefix_of_swap hswapCoreD (of_run_swap hswap) hpD1
      rcases Line.of_run_cons hdebit2 with ⟨d3, hstore, hnilD⟩
      cases hnilD
      have hsetDebit : Devm.getStor afterDebitCursor.pre e.currentTarget =
          (Devm.getStor d2 e.currentTarget).set owner
            (balance - Sevm.argWord e amountArg) :=
        sstore_getStor_set hstore hpD2
      have hdebitStorPre : Devm.getStor successCursor.pre =
          Devm.getStor d2 :=
        (Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hsub Line.Run.nil)).trans
          (Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons hswap Line.Run.nil))
      -- the burn event and the send operands
      rcases afterDebitCursor.peelChildlessLine
          (line := redeemFromEventLine ownerArg amountArg)
          (by simp [redeemFromEventLine, addressArg, normalizeAddress,
            pushAddressMask, arg, cdl, emitTransfer, Blanc.transferFromLog,
            mstoreAt, logWith, NinstIsChildless, Ninst.pushB256]) with
        ⟨sendCursor, heventRun⟩
      unfold redeemFromEventLine at heventRun
      rcases of_run_append (addressArg ownerArg) heventRun with
        ⟨eventPre, hownerRun, htailRun⟩
      have hcallerStor : Devm.getStor afterDebitCursor.pre =
          Devm.getStor eventPre :=
        Line.of_inv Devm.getStor (by line_inv) hownerRun
      have hcallerCode : Devm.getCode afterDebitCursor.pre =
          Devm.getCode eventPre :=
        Line.of_inv Devm.getCode (by line_inv) hownerRun
      have hcallerMem : afterDebitCursor.pre.memory = eventPre.memory :=
        Line.of_inv Devm.memory (by line_inv) hownerRun
      have hownerStack : owner :: [] <<+ eventPre.stack := by
        rw [howner]
        exact prefix_of_addressArg nil_pref hownerRun
      have hwfEvent : Mem.Wf eventPre.memory := by
        rw [← hcallerMem, ← hdebitMem, ← hcheckMem]
        exact hwf
      have hreadsEvent : Mem.Reads eventPre.memory img := by
        rw [← hcallerMem, ← hdebitMem, ← hcheckMem]
        exact hreads
      obtain ⟨hsendStack, _heventLogs, heventStor, _heventBal, heventCode,
          _heventOutput, _hwfSend, _hreadsSend⟩ :=
        burnEventTail_effect_frame hownerStack hwfEvent hreadsEvent htailRun
      rcases sendCursor.peelChildlessLine (line := sendPrefix)
          hsendChildless with
        ⟨callCursor, hsendRun⟩
      have sendEvidence := hsend hsendStack hsendRun
      have hcallStor : Devm.getStor afterDebitCursor.pre =
          Devm.getStor callCursor.pre :=
        hcallerStor.trans (heventStor.symm.trans sendEvidence.storage)
      have hcallCode : Devm.getCode cursor.pre =
          Devm.getCode callCursor.pre :=
        hcheckCode.trans (hdebitCode.trans
          (hcallerCode.trans (heventCode.symm.trans sendEvidence.code)))
      have hpreCall : (Devm.getStor callCursor.pre e.currentTarget).get key =
          (Devm.getStor cursor.pre e.currentTarget).get key := by
        rw [← congrFun hcallStor e.currentTarget, hsetDebit,
          Stor.get_set_ne _ hkeyNe _,
          ← congrFun hdebitStorPre e.currentTarget,
          ← congrFun hcheckStor e.currentTarget]
      have hpreCallCa : (Devm.getStor callCursor.pre ca).get key =
          (Devm.getStor cursor.pre ca).get key := by
        rw [htargetE] at hpreCall
        exact hpreCall
      have hcallCodeAt : some (callCursor.pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        rw [← congrFun hcallCode ca]
        exact hcursorCode
      -- cross the external value CALL
      have hcallRun := callCursor.run
      cases hcallRun with
      | next hcompiled htailCompiled =>
          rename_i midD
          have hat : Ninst.At e.code callCursor.pc Ninst.call :=
            ninstAt_of_subcode_next callCursor.codeSlice
          obtain ⟨nextBoundary, nextSub⟩ :=
            Func.noPushBefore_next callCursor.codeSlice
              callCursor.codeBoundary
          rcases callCursor.parentPrefix with ⟨actionsBefore, hbefore⟩
          rcases Exec.Frame.advance_runCompiled_next
              (frame := ⟨fpc, e, fpre, .ok fpost, frun, fcommitted⟩)
              callCursor.current hbefore hat hcompiled with
            ⟨xl, continuation, selected, occurrence, hedge, _hnextPrefix⟩
          rcases hedge.exists_counted with ⟨counted, hcountedEdge⟩
          rcases occurrence with
            ⟨_opc, _ocurrent, _ocont, _obefore, _oselected, _oprefix, _oat,
              ofilled, ostep, _oprec, _oedge⟩
          have hstepAt : Ninst.StepRun callCursor.pc e callCursor.pre
              Ninst.call xl (.ok midD) :=
            Ninst.stepRun_pc_irrel (pc' := callCursor.pc)
              (by simp [Ninst.pcFree]) ostep
          -- the trailing guard excludes the reverter arm
          have htailPlain : Func.Run ((weth10 dp).main :: weth10Aux) e midD
              (Ninst.iszero ::: ((.call errSlot) <?>
                (successLine +++ Func.last successLast))) fpost :=
            Func.Run.of_runCompiled htailCompiled
          rcases of_run_next htailPlain with
            ⟨afterIszero, hiszeroRun, hbranchPlain⟩
          rcases of_run_branch_call_revWith herr
              hbranchPlain with
            ⟨afterGuard, hguardPop, _hsuccessRun⟩
          rcases sendEvidence.stack with ⟨gasWord, hcallStack⟩
          have hcall : Ninst.Run e callCursor.pre Ninst.call midD :=
            Ninst.Run.of_runCompiled hcompiled
          rcases of_run_call_val_with_depth_frame hcallStack hcall with
              hfailed | hsuccess
          · exfalso
            have htest := prefix_of_iszero hiszeroRun hfailed.1
            have hguardStack' := hguardPop.stack
            simp only [Stack.Pop, Split, List.nil_append,
              List.cons_append] at hguardStack'
            rw [hguardStack'] at htest
            have hzero : ((0 : B256) =? 0) = 0 :=
              pref_head_unique htest (pref_append [(0 : B256)] afterGuard.stack)
            rw [show ((0 : B256) =? 0) = 1 from by
              simp [B256.eqCheck]] at hzero
            exact B256.zero_ne_one hzero.symm
          · rcases hsuccess with
              ⟨callParent, child, xlRaw, hasDelegation, code, availableGas,
                rawPc, hrawStep, hdepthPos, _hcallStackEq, hparentState,
                _hparentMemory, _hparentLogs, _hparentOutput, hdelegation,
                hrawFilled, hprocess, hclean, _hresume, hmidState,
                _hreturnData, _hmidMemory, hmidStack⟩
            have halign := Ninst.StepRun.unique_exec_of_filled ofilled
              hrawFilled hstepAt hrawStep
            cases halign.1
            obtain ⟨retained⟩ := exists_retainedXlot_of_filled ofilled
            have hcommits : retained.RawCommits := by
              cases retained with
              | none => trivial
              | some retainedRun =>
                  exact Frame.raw_commits_of_settlementCommits
                    (ProcessMessage.settlementCommits_of_some_ok_clean
                      hprocess hclean)
            have hparent : callCursor.pre.state =
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  target.toAdr true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).benv.state := by
              simpa only [callMsg] using hparentState.symm
            have hmsgDepth :
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  target.toAdr true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).depth <
                  e.depth := by
              dsimp only [callMsg]
              omega
            have htargetCode :
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  target.toAdr true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).currentTarget =
                  ca →
                some code.toList = Prog.compile (weth10 dp) := by
              intro hct
              have htargetCa : target.toAdr = ca := by
                simpa only [callMsg] using hct
              exact callbackCode_eq_compiled_of_target_eq hcallCodeAt
                htargetCa hdelegation
            have childEffect :=
              ProcessMessageTrace.allowanceRegionDelta_of_forallDeeperAt
                (dp := dp) (ca := ca) (depth := e.depth)
                (parent := callCursor.pre)
                ⟨_, retained, hprocess⟩ hparent hmsgDepth hcallCodeAt
                htargetCode
                (by
                  intro hct
                  have htargetCa : target.toAdr = ca := by
                    simpa only [callMsg] using hct
                  simp only [callMsg, htargetCa])
                hdeeper
            -- the trailing guard is childless and storage neutral
            obtain ⟨htailNil, htailStor⟩ :=
              Exec.tailGuard_attributionInner_storage
                (dp := dp) (ca := ca) (_errReason := "")
                (rest := callParent.stack)
                continuation fcommitted htailCompiled nextSub nextBoundary
                hmidStack hsuccessChildless hsuccessStor
            -- the counted stream of the frame is exactly the child's
            have hprefixSplit := callCursor.countedPrefix.descendantCounted_eq
            change Exec.attributionInner dp ca frun =
              [] ++ Exec.attributionInner dp ca callCursor.current
                at hprefixSplit
            have hedgeSplit := hcountedEdge.descendantCounted_eq
            change Exec.attributionInner dp ca callCursor.current =
              counted ++ Exec.attributionInner dp ca continuation
                at hedgeSplit
            have hcountedEq :=
              Exec.Deriv.ParentStepCounted.selected_eq_retained_of_call
                hat ofilled hstepAt retained hcountedEdge
            have hinnerEq : Exec.attributionInner dp ca frun =
                retained.attributionStream dp ca := by
              rw [hprefixSplit, List.nil_append, hedgeSplit, hcountedEq,
                htailNil, List.append_nil]
            calc (Devm.getStor fpost ca).get key
                = (Devm.getStor midD ca).get key := by
                  rw [congrFun htailStor ca]
              _ = (Devm.getStor child ca).get key :=
                  congrArg (fun state : State => (state.getStor ca).get key)
                    hmidState
              _ = applyAllowanceLedger (Devm.getStor callCursor.pre ca)
                    (retained.attributionStream dp ca) key :=
                  childEffect.storage key hkey
              _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (retained.attributionStream dp ca) key :=
                  applyAllowanceLedger_congr hpreCallCa
              _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (Exec.attributionInner dp ca frun) key := by
                  rw [hinnerEq]

/-! ## The two delegated redemption arms

Each arm composes the wrapper's singleton replay with the core's child
transport: the frame's own record carries the wrapper's exact
self/max/finite allowance fork, and the committed send child's counted
stream is the frame's proper-descendant stream. -/

/-- Delegated `withdrawFrom` transports the allowance region: its own record
is the wrapper's exact allowance fork, the core's debit is address-shaped at
the normalized owner argument, and the committed send child's counted stream
is transported by the recursion hypothesis. -/
theorem Exec.Frame.allowanceRegionEffect_of_withdrawFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable withdrawFrom) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [withdrawFromSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨spendCursor, hnonpayableSilent⟩
  have hspendSilent : Devm.DispatchSilent frame.pre spendCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 withdrawFromCoreSlot) frame.post
    at spendCursor
  rcases spendCursor.enterSpendCallerAllowanceThenFork
      context.invocation.2.2.2 (allowanceError_lookup dp)
      (by rw [← hspendSilent.memory]; exact context.memory_wf)
      (by rw [← hspendSilent.memory]; exact context.memory_reads_empty) with
    ⟨body, hget, coreCursor, hwfCore, ⟨imgCore, hreadsCore⟩, hcodeCore,
      hfork⟩
  have hbody : body = withdrawFromCore := by
    simpa [weth10, weth10Aux, withdrawFromCoreSlot] using hget.symm
  subst body
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemFromBody 0 2 (redeemSendToArgPrefix 1) etherTransferErrorSlot
      (Func.last .stop)) frame.post at coreCursor
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hstorage := coreCursor.redeemFromAllowanceStorage
    (successLine := []) (target := Sevm.argWord frame.sevm 1)
    (etherTransferError_lookup dp) htarget nil_pref hwfCore hreadsCore
    (by
      rw [← congrFun hcodeCore ca,
        ← getCode_eq_of_state_eq hspendSilent.state ca]
      exact context.installed.1)
    (by simp [redeemSendToArgPrefix, pushList, arg, cdl, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToArgPrefix_effect 1 hp hrun)
    (by simp)
    (by func_inv)
    hdeeper
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hselector,
      withdrawFromSelector_ne_flashLoanSelector,
      withdrawFromSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotlast]
  have hpreStor : Devm.getStor frame.pre = Devm.getStor spendCursor.pre :=
    funext (getStor_eq_of_state_eq hspendSilent.state)
  rw [hstream]
  refine ⟨fun key hkey => ?_,
    Exec.installedCodeEq_committed frame.run frame.committed
      context.installed⟩
  have hmid : (Devm.getStor coreCursor.pre ca).get key =
      applyAllowanceLedger (Devm.getStor frame.pre ca)
        [CountedFrame.ofFrame dp ca frame] key := by
    rw [applyAllowanceLedger_singleton]
    rcases hfork with ⟨hself, hstorEq⟩ | ⟨hnself, hmaxOrFinite⟩
    · have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
        show frameAllowanceEvent frame.sevm frame.pre frame.post = none
        simp [frameAllowanceEvent, hnonempty, hselector,
          withdrawFromSelector_ne_approveSelector,
          withdrawFromSelector_ne_approveAndCallSelector,
          withdrawFromSelector_ne_permitSelector, hself]
      rw [htarget] at hstorEq
      rw [hown, hstorEq, ← congrFun hpreStor ca]
    · rcases hmaxOrFinite with
          ⟨hmaxGet, hstorEq⟩ |
          ⟨allowance, hneMax, hallowGet, hstorSet⟩
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = B256.max := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hmaxGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendMax } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector,
            withdrawFromSelector_ne_approveSelector,
            withdrawFromSelector_ne_approveAndCallSelector,
            withdrawFromSelector_ne_permitSelector, hnself, hbefore]
        rw [htarget] at hstorEq
        rw [hown]
        simp only [AllowanceVisit.written?, ite_self]
        rw [hstorEq, ← congrFun hpreStor ca]
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = allowance := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hallowGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendFinite allowance
                     (allowance - Sevm.argWord frame.sevm 2) } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector,
            withdrawFromSelector_ne_approveSelector,
            withdrawFromSelector_ne_approveAndCallSelector,
            withdrawFromSelector_ne_permitSelector, hnself, hbefore, hneMax]
        rw [htarget] at hstorSet
        rw [hown]
        simp only [AllowanceEvent.key, AllowanceVisit.written?]
        rw [hstorSet]
        by_cases hpk :
            projectedAllowanceKey (Sevm.argWord frame.sevm 0)
              frame.sevm.caller.toB256 = key
        · rw [if_pos hpk, ← hpk, ← callerAllowanceRuntimeKey_eq_projected]
          exact Stor.get_set_self _ _ _
        · have hne : callerAllowanceRuntimeKey frame.sevm ≠ key := by
            rw [callerAllowanceRuntimeKey_eq_projected]
            exact hpk
          rw [if_neg hpk, Stor.get_set_ne _ hne _, ← congrFun hpreStor ca]
  have hsplit := applyAllowanceLedger_append (Devm.getStor frame.pre ca)
    (Devm.getStor coreCursor.pre ca) [CountedFrame.ofFrame dp ca frame]
    (Exec.attributionInner dp ca frame.run) key hmid
  simp only [List.cons_append, List.nil_append] at hsplit
  rw [hsplit]
  exact hstorage key hkey

/-- Delegated `transferFrom` with a zero raw recipient word is a redemption
to the caller, and transports the allowance region exactly as delegated
`withdrawFrom` does. -/
theorem Exec.Frame.allowanceRegionEffect_of_transferFromZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hzero : Sevm.argWord frame.sevm 1 = 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable transferFrom) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [transferFromSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨spendCursor, hnonpayableSilent⟩
  have hspendSilent : Devm.DispatchSilent frame.pre spendCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 transferFromCoreSlot) frame.post
    at spendCursor
  rcases spendCursor.enterSpendCallerAllowanceThenFork
      context.invocation.2.2.2 (allowanceError_lookup dp)
      (by rw [← hspendSilent.memory]; exact context.memory_wf)
      (by rw [← hspendSilent.memory]; exact context.memory_reads_empty) with
    ⟨body, hget, coreCursor, hwfCore, ⟨imgCore, hreadsCore⟩, hcodeCore,
      hfork⟩
  have hbody : body = transferFromCore := by
    simpa [weth10, weth10Aux, transferFromCoreSlot] using hget.symm
  subst body
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ((arg 1 ++ [iszero]) +++ (transferFromZero <?> transferFromNonzero))
    frame.post at coreCursor
  rcases coreCursor.peelChildlessLine
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine⟩
  have htargetPrefix : [Sevm.argWord frame.sevm 1 =? 0] <<+
      targetBranchCursor.pre.stack := by
    rcases of_run_append (arg 1) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with ⟨afterZero, hzeroRun, hnil⟩
    cases hnil
    exact prefix_of_iszero hzeroRun (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 1 =? 0) = 1 := by
    simp [B256.eqCheck, hzero]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) htargetPrefix with
    ⟨zeroCursor, _hzeroStack, hbranchSilent⟩
  have hlineStor : Devm.getStor coreCursor.pre =
      Devm.getStor targetBranchCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv) htargetLine
  have hlineCode : Devm.getCode coreCursor.pre =
      Devm.getCode targetBranchCursor.pre :=
    Line.of_inv Devm.getCode (by line_inv) htargetLine
  have hlineMem : coreCursor.pre.memory = targetBranchCursor.pre.memory :=
    Line.of_inv Devm.memory (by line_inv) htargetLine
  have hcoreToZero : Devm.getStor coreCursor.pre =
      Devm.getStor zeroCursor.pre := by
    rw [hlineStor, funext (getStor_eq_of_state_eq hbranchSilent.state)]
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemFromBody 0 2 redeemSendToCallerPrefix ethTransferErrorSlot
      (redeemReturnTrueLine +++ Func.last .ret)) frame.post at zeroCursor
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hstorage := zeroCursor.redeemFromAllowanceStorage
    (target := frame.sevm.caller.toB256)
    (ethTransferError_lookup dp) htarget nil_pref
    (by rw [← hbranchSilent.memory, ← hlineMem]; exact hwfCore)
    (show Mem.Reads zeroCursor.pre.memory imgCore by
      rw [← hbranchSilent.memory, ← hlineMem]; exact hreadsCore)
    (by
      rw [← getCode_eq_of_state_eq hbranchSilent.state ca,
        ← congrFun hlineCode ca, ← congrFun hcodeCore ca,
        ← getCode_eq_of_state_eq hspendSilent.state ca]
      exact context.installed.1)
    (by simp [redeemSendToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToCallerPrefix_effect hp hrun)
    (by simp [redeemReturnTrueLine, mstoreAt, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by func_inv)
    hdeeper
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hselector,
      transferFromSelector_ne_flashLoanSelector,
      transferFromSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotlast]
  have hpreStor : Devm.getStor frame.pre = Devm.getStor spendCursor.pre :=
    funext (getStor_eq_of_state_eq hspendSilent.state)
  rw [hstream]
  refine ⟨fun key hkey => ?_,
    Exec.installedCodeEq_committed frame.run frame.committed
      context.installed⟩
  have hmid : (Devm.getStor zeroCursor.pre ca).get key =
      applyAllowanceLedger (Devm.getStor frame.pre ca)
        [CountedFrame.ofFrame dp ca frame] key := by
    rw [applyAllowanceLedger_singleton, ← congrFun hcoreToZero ca]
    rcases hfork with ⟨hself, hstorEq⟩ | ⟨hnself, hmaxOrFinite⟩
    · have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
        show frameAllowanceEvent frame.sevm frame.pre frame.post = none
        simp [frameAllowanceEvent, hnonempty, hselector,
          transferFromSelector_ne_approveSelector,
          transferFromSelector_ne_approveAndCallSelector,
          transferFromSelector_ne_permitSelector, hself]
      rw [htarget] at hstorEq
      rw [hown, hstorEq, ← congrFun hpreStor ca]
    · rcases hmaxOrFinite with
          ⟨hmaxGet, hstorEq⟩ |
          ⟨allowance, hneMax, hallowGet, hstorSet⟩
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = B256.max := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hmaxGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendMax } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector,
            transferFromSelector_ne_approveSelector,
            transferFromSelector_ne_approveAndCallSelector,
            transferFromSelector_ne_permitSelector, hnself, hbefore]
        rw [htarget] at hstorEq
        rw [hown]
        simp only [AllowanceVisit.written?, ite_self]
        rw [hstorEq, ← congrFun hpreStor ca]
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = allowance := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hallowGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendFinite allowance
                     (allowance - Sevm.argWord frame.sevm 2) } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector,
            transferFromSelector_ne_approveSelector,
            transferFromSelector_ne_approveAndCallSelector,
            transferFromSelector_ne_permitSelector, hnself, hbefore, hneMax]
        rw [htarget] at hstorSet
        rw [hown]
        simp only [AllowanceEvent.key, AllowanceVisit.written?]
        rw [hstorSet]
        by_cases hpk :
            projectedAllowanceKey (Sevm.argWord frame.sevm 0)
              frame.sevm.caller.toB256 = key
        · rw [if_pos hpk, ← hpk, ← callerAllowanceRuntimeKey_eq_projected]
          exact Stor.get_set_self _ _ _
        · have hne : callerAllowanceRuntimeKey frame.sevm ≠ key := by
            rw [callerAllowanceRuntimeKey_eq_projected]
            exact hpk
          rw [if_neg hpk, Stor.get_set_ne _ hne _, ← congrFun hpreStor ca]
  have hsplit := applyAllowanceLedger_append (Devm.getStor frame.pre ca)
    (Devm.getStor zeroCursor.pre ca) [CountedFrame.ofFrame dp ca frame]
    (Exec.attributionInner dp ca frame.run) key hmid
  simp only [List.cons_append, List.nil_append] at hsplit
  rw [hsplit]
  exact hstorage key hkey

/-! ## The read-sound delegated redemption walk

The same walk as `Exec.Frame.CountedCursor.redeemFromAllowanceStorage`,
against the strengthened carrier.  The key is no longer introduced up
front: the send child's entry-read soundness has to be re-based from the
`CALL` cursor's storage onto the walk's entry storage, and
`AllowanceEntryReadSound.append` consumes that re-basing as a statement
about *every* tagged key rather than one at a time.  The trailing guard is
childless here, so the whole inner stream is the child's and the re-basing
is the only new content. -/

/-- Read-sound sibling of
`Exec.Frame.CountedCursor.redeemFromAllowanceStorage`. -/
private theorem Exec.Frame.CountedCursor.redeemFromAllowanceSound
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {ownerArg amountArg target : B256} {sendPrefix successLine : Line}
    {successLast : Linst} {img : Bytes} {errSlot : Nat} {reason : String}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (redeemFromBody ownerArg amountArg sendPrefix errSlot
        (successLine +++ Func.last successLast)) frame.post)
    (herr : ((weth10 dp).main :: weth10Aux)[errSlot]? =
      some (Func.revWith reason))
    (htarget : frame.sevm.currentTarget = ca)
    (hstack : [] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img)
    (hcursorCode : some (cursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hsendChildless : ∀ n ∈ sendPrefix, NinstIsChildless n)
    (hsend : ∀ {sendPre callPre : Devm} {value : B256} {tail : Stack},
      value :: tail <<+ sendPre.stack →
      Line.Run frame.sevm sendPre sendPrefix callPre →
      ValueCallOperandPrefix frame.sevm sendPre callPre value target tail)
    (hsuccessChildless : ∀ n ∈ successLine, NinstIsChildless n)
    (hsuccessStor : Func.Inv Devm.getStor Devm.getStor
      (successLine +++ Func.last successLast))
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    (∀ key, InRegion .allowance key →
        (Devm.getStor frame.post ca).get key =
          applyAllowanceLedger (Devm.getStor cursor.pre ca)
            (Exec.attributionInner dp ca frame.run) key) ∧
      AllowanceEntryReadSound (Devm.getStor cursor.pre ca)
        (Exec.attributionInner dp ca frame.run) := by
  rcases frame with ⟨fpc, e, fpre, fout, frun, fcommitted⟩
  cases fout with
  | error err => simp [Execution.commits] at fcommitted
  | ok fpost =>
      have htargetE : e.currentTarget = ca := htarget
      -- the guarded balance check
      unfold redeemFromBody at cursor
      rcases cursor.peelChildlessLine
          (line := redeemFromCheckLine ownerArg amountArg)
          (by simp [redeemFromCheckLine, loadArgBalanceAmount, addressArg,
            normalizeAddress, pushAddressMask, balanceTooSmall, arg, cdl,
            NinstIsChildless, Ninst.pushB256]) with
        ⟨branchCursor, hcheck⟩
      unfold redeemFromCheckLine at hcheck
      rcases of_run_append (loadArgBalanceAmount ownerArg amountArg)
          hcheck with
        ⟨afterLoad, hload, hguard⟩
      rcases prefix_of_loadArgBalanceAmount ownerArg amountArg hstack
          hload with
        ⟨balance, owner, howner, _hbalance, hloadStack⟩
      have hkeyNe : ∀ key, InRegion .allowance key → owner ≠ key := by
        intro key hkey
        refine (allowanceRegion_ne_validAdr hkey ?_).symm
        rw [howner]
        exact normalizedAddress_valid (Sevm.argWord e ownerArg)
      have hguardStack : (balance <? Sevm.argWord e amountArg) :: balance ::
          Sevm.argWord e amountArg :: owner :: [] <<+
            branchCursor.pre.stack :=
        prefix_of_balanceTooSmall hloadStack hguard
      rcases branchCursor.selectBranchLeftWithBurn
          (not_run_call_revWith (burnBalanceError_lookup dp)) with
        ⟨successCursor, hbalancePopBy⟩
      have hbalancePop := Devm.PopBurn.of_popBurnBy hbalancePopBy
      have hpopStack := hbalancePop.stack
      simp only [Stack.Pop, Split, List.nil_append,
        List.cons_append] at hpopStack
      rw [hpopStack] at hguardStack
      have hflag : (balance <? Sevm.argWord e amountArg) = 0 :=
        pref_head_unique hguardStack (pref_append [0] successCursor.pre.stack)
      rw [hflag] at hguardStack
      have hsuccessStack : balance :: Sevm.argWord e amountArg ::
          owner :: [] <<+ successCursor.pre.stack :=
        cons_pref_cons_inv hguardStack
      have hcheckStor : Devm.getStor cursor.pre =
          Devm.getStor successCursor.pre :=
        (Line.of_inv Devm.getStor (by line_inv) hload).trans
          ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
            (PopBurn.Inv.inv hbalancePop))
      have hcheckCode : Devm.getCode cursor.pre =
          Devm.getCode successCursor.pre :=
        (Line.of_inv Devm.getCode (by line_inv) hload).trans
          ((Line.of_inv Devm.getCode (by line_inv) hguard).trans
            (funext (getCode_eq_of_state_eq hbalancePop.state)))
      have hcheckMem : cursor.pre.memory = successCursor.pre.memory :=
        (Line.of_inv Devm.memory (by line_inv) hload).trans
          ((Line.of_inv Devm.memory (by line_inv) hguard).trans
            hbalancePop.memory)
      -- the owner-key debit
      rcases successCursor.peelChildlessLine (line := debitLoadedBalance)
          (by simp [debitLoadedBalance, NinstIsChildless]) with
        ⟨afterDebitCursor, hdebit⟩
      have hdebitCode : Devm.getCode successCursor.pre =
          Devm.getCode afterDebitCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hdebit
      have hdebitMem : successCursor.pre.memory =
          afterDebitCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hdebit
      unfold debitLoadedBalance at hdebit
      rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
      have hpD1 : (balance - Sevm.argWord e amountArg) ::
          owner :: [] <<+ d1.stack :=
        prefix_of_sub hsub hsuccessStack
      rcases Line.of_run_cons hdebit1 with ⟨d2, hswap, hdebit2⟩
      have hswapCoreD : Stack.Swap (0 : Fin 16).val
          [balance - Sevm.argWord e amountArg, owner]
          [owner, balance - Sevm.argWord e amountArg] :=
        Stack.swapCore_zero
      have hpD2 : owner ::
          (balance - Sevm.argWord e amountArg) :: [] <<+ d2.stack :=
        Stack.prefix_of_swap hswapCoreD (of_run_swap hswap) hpD1
      rcases Line.of_run_cons hdebit2 with ⟨d3, hstore, hnilD⟩
      cases hnilD
      have hsetDebit : Devm.getStor afterDebitCursor.pre e.currentTarget =
          (Devm.getStor d2 e.currentTarget).set owner
            (balance - Sevm.argWord e amountArg) :=
        sstore_getStor_set hstore hpD2
      have hdebitStorPre : Devm.getStor successCursor.pre =
          Devm.getStor d2 :=
        (Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hsub Line.Run.nil)).trans
          (Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons hswap Line.Run.nil))
      -- the burn event and the send operands
      rcases afterDebitCursor.peelChildlessLine
          (line := redeemFromEventLine ownerArg amountArg)
          (by simp [redeemFromEventLine, addressArg, normalizeAddress,
            pushAddressMask, arg, cdl, emitTransfer, Blanc.transferFromLog,
            mstoreAt, logWith, NinstIsChildless, Ninst.pushB256]) with
        ⟨sendCursor, heventRun⟩
      unfold redeemFromEventLine at heventRun
      rcases of_run_append (addressArg ownerArg) heventRun with
        ⟨eventPre, hownerRun, htailRun⟩
      have hcallerStor : Devm.getStor afterDebitCursor.pre =
          Devm.getStor eventPre :=
        Line.of_inv Devm.getStor (by line_inv) hownerRun
      have hcallerCode : Devm.getCode afterDebitCursor.pre =
          Devm.getCode eventPre :=
        Line.of_inv Devm.getCode (by line_inv) hownerRun
      have hcallerMem : afterDebitCursor.pre.memory = eventPre.memory :=
        Line.of_inv Devm.memory (by line_inv) hownerRun
      have hownerStack : owner :: [] <<+ eventPre.stack := by
        rw [howner]
        exact prefix_of_addressArg nil_pref hownerRun
      have hwfEvent : Mem.Wf eventPre.memory := by
        rw [← hcallerMem, ← hdebitMem, ← hcheckMem]
        exact hwf
      have hreadsEvent : Mem.Reads eventPre.memory img := by
        rw [← hcallerMem, ← hdebitMem, ← hcheckMem]
        exact hreads
      obtain ⟨hsendStack, _heventLogs, heventStor, _heventBal, heventCode,
          _heventOutput, _hwfSend, _hreadsSend⟩ :=
        burnEventTail_effect_frame hownerStack hwfEvent hreadsEvent htailRun
      rcases sendCursor.peelChildlessLine (line := sendPrefix)
          hsendChildless with
        ⟨callCursor, hsendRun⟩
      have sendEvidence := hsend hsendStack hsendRun
      have hcallStor : Devm.getStor afterDebitCursor.pre =
          Devm.getStor callCursor.pre :=
        hcallerStor.trans (heventStor.symm.trans sendEvidence.storage)
      have hcallCode : Devm.getCode cursor.pre =
          Devm.getCode callCursor.pre :=
        hcheckCode.trans (hdebitCode.trans
          (hcallerCode.trans (heventCode.symm.trans sendEvidence.code)))
      have hpreCall : ∀ key, InRegion .allowance key →
          (Devm.getStor callCursor.pre e.currentTarget).get key =
            (Devm.getStor cursor.pre e.currentTarget).get key := by
        intro key hkey
        rw [← congrFun hcallStor e.currentTarget, hsetDebit,
          Stor.get_set_ne _ (hkeyNe key hkey) _,
          ← congrFun hdebitStorPre e.currentTarget,
          ← congrFun hcheckStor e.currentTarget]
      have hpreCallCa : ∀ key, InRegion .allowance key →
          (Devm.getStor callCursor.pre ca).get key =
            (Devm.getStor cursor.pre ca).get key := by
        rw [htargetE] at hpreCall
        exact hpreCall
      have hcallCodeAt : some (callCursor.pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        rw [← congrFun hcallCode ca]
        exact hcursorCode
      -- cross the external value CALL
      have hcallRun := callCursor.run
      cases hcallRun with
      | next hcompiled htailCompiled =>
          rename_i midD
          have hat : Ninst.At e.code callCursor.pc Ninst.call :=
            ninstAt_of_subcode_next callCursor.codeSlice
          obtain ⟨nextBoundary, nextSub⟩ :=
            Func.noPushBefore_next callCursor.codeSlice
              callCursor.codeBoundary
          rcases callCursor.parentPrefix with ⟨actionsBefore, hbefore⟩
          rcases Exec.Frame.advance_runCompiled_next
              (frame := ⟨fpc, e, fpre, .ok fpost, frun, fcommitted⟩)
              callCursor.current hbefore hat hcompiled with
            ⟨xl, continuation, selected, occurrence, hedge, _hnextPrefix⟩
          rcases hedge.exists_counted with ⟨counted, hcountedEdge⟩
          rcases occurrence with
            ⟨_opc, _ocurrent, _ocont, _obefore, _oselected, _oprefix, _oat,
              ofilled, ostep, _oprec, _oedge⟩
          have hstepAt : Ninst.StepRun callCursor.pc e callCursor.pre
              Ninst.call xl (.ok midD) :=
            Ninst.stepRun_pc_irrel (pc' := callCursor.pc)
              (by simp [Ninst.pcFree]) ostep
          -- the trailing guard excludes the reverter arm
          have htailPlain : Func.Run ((weth10 dp).main :: weth10Aux) e midD
              (Ninst.iszero ::: ((.call errSlot) <?>
                (successLine +++ Func.last successLast))) fpost :=
            Func.Run.of_runCompiled htailCompiled
          rcases of_run_next htailPlain with
            ⟨afterIszero, hiszeroRun, hbranchPlain⟩
          rcases of_run_branch_call_revWith herr
              hbranchPlain with
            ⟨afterGuard, hguardPop, _hsuccessRun⟩
          rcases sendEvidence.stack with ⟨gasWord, hcallStack⟩
          have hcall : Ninst.Run e callCursor.pre Ninst.call midD :=
            Ninst.Run.of_runCompiled hcompiled
          rcases of_run_call_val_with_depth_frame hcallStack hcall with
              hfailed | hsuccess
          · exfalso
            have htest := prefix_of_iszero hiszeroRun hfailed.1
            have hguardStack' := hguardPop.stack
            simp only [Stack.Pop, Split, List.nil_append,
              List.cons_append] at hguardStack'
            rw [hguardStack'] at htest
            have hzero : ((0 : B256) =? 0) = 0 :=
              pref_head_unique htest (pref_append [(0 : B256)] afterGuard.stack)
            rw [show ((0 : B256) =? 0) = 1 from by
              simp [B256.eqCheck]] at hzero
            exact B256.zero_ne_one hzero.symm
          · rcases hsuccess with
              ⟨callParent, child, xlRaw, hasDelegation, code, availableGas,
                rawPc, hrawStep, hdepthPos, _hcallStackEq, hparentState,
                _hparentMemory, _hparentLogs, _hparentOutput, hdelegation,
                hrawFilled, hprocess, hclean, _hresume, hmidState,
                _hreturnData, _hmidMemory, hmidStack⟩
            have halign := Ninst.StepRun.unique_exec_of_filled ofilled
              hrawFilled hstepAt hrawStep
            cases halign.1
            obtain ⟨retained⟩ := exists_retainedXlot_of_filled ofilled
            have hcommits : retained.RawCommits := by
              cases retained with
              | none => trivial
              | some retainedRun =>
                  exact Frame.raw_commits_of_settlementCommits
                    (ProcessMessage.settlementCommits_of_some_ok_clean
                      hprocess hclean)
            have hparent : callCursor.pre.state =
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  target.toAdr true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).benv.state := by
              simpa only [callMsg] using hparentState.symm
            have hmsgDepth :
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  target.toAdr true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).depth <
                  e.depth := by
              dsimp only [callMsg]
              omega
            have htargetCode :
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  target.toAdr true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).currentTarget =
                  ca →
                some code.toList = Prog.compile (weth10 dp) := by
              intro hct
              have htargetCa : target.toAdr = ca := by
                simpa only [callMsg] using hct
              exact callbackCode_eq_compiled_of_target_eq hcallCodeAt
                htargetCa hdelegation
            have childEffect :=
              ProcessMessageTrace.allowanceRegionDeltaSound_of_forallDeeperAt
                (dp := dp) (ca := ca) (depth := e.depth)
                (parent := callCursor.pre)
                ⟨_, retained, hprocess⟩ hparent hmsgDepth hcallCodeAt
                htargetCode
                (by
                  intro hct
                  have htargetCa : target.toAdr = ca := by
                    simpa only [callMsg] using hct
                  simp only [callMsg, htargetCa])
                hdeeper
            -- the trailing guard is childless and storage neutral
            obtain ⟨htailNil, htailStor⟩ :=
              Exec.tailGuard_attributionInner_storage
                (dp := dp) (ca := ca) (_errReason := "")
                (rest := callParent.stack)
                continuation fcommitted htailCompiled nextSub nextBoundary
                hmidStack hsuccessChildless hsuccessStor
            -- the counted stream of the frame is exactly the child's
            have hprefixSplit := callCursor.countedPrefix.descendantCounted_eq
            change Exec.attributionInner dp ca frun =
              [] ++ Exec.attributionInner dp ca callCursor.current
                at hprefixSplit
            have hedgeSplit := hcountedEdge.descendantCounted_eq
            change Exec.attributionInner dp ca callCursor.current =
              counted ++ Exec.attributionInner dp ca continuation
                at hedgeSplit
            have hcountedEq :=
              Exec.Deriv.ParentStepCounted.selected_eq_retained_of_call
                hat ofilled hstepAt retained hcountedEdge
            have hinnerEq : Exec.attributionInner dp ca frun =
                retained.attributionStream dp ca := by
              rw [hprefixSplit, List.nil_append, hedgeSplit, hcountedEq,
                htailNil, List.append_nil]
            -- the child's own entry-read soundness, re-based onto the walk's
            -- entry storage across the address-shaped debit
            have hchildRead : AllowanceEntryReadSound
                (Devm.getStor cursor.pre ca)
                (retained.attributionStream dp ca) := by
              have hrebased := AllowanceEntryReadSound.append
                (pre := Devm.getStor cursor.pre ca)
                (mid := Devm.getStor callCursor.pre ca)
                (left := []) (right := retained.attributionStream dp ca)
                (fun key hkey => by
                  rw [applyAllowanceLedger_nil]
                  exact hpreCallCa key hkey)
                (AllowanceEntryReadSound.nil _) childEffect.entryRead
              simpa only [List.nil_append] using hrebased
            refine ⟨fun key hkey => ?_, by rw [hinnerEq]; exact hchildRead⟩
            calc (Devm.getStor fpost ca).get key
                = (Devm.getStor midD ca).get key := by
                  rw [congrFun htailStor ca]
              _ = (Devm.getStor child ca).get key :=
                  congrArg (fun state : State => (state.getStor ca).get key)
                    hmidState
              _ = applyAllowanceLedger (Devm.getStor callCursor.pre ca)
                    (retained.attributionStream dp ca) key :=
                  childEffect.storage key hkey
              _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (retained.attributionStream dp ca) key :=
                  applyAllowanceLedger_congr (hpreCallCa key hkey)
              _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (Exec.attributionInner dp ca frun) key := by
                  rw [hinnerEq]

/-! ## The read-sound delegated redemption arms

Each arm composes the wrapper's singleton replay — the frame's own record,
carrying the wrapper's exact self/max/finite allowance fork — with the
core's read-sound child transport.  The record's own read is the frame's
entry word by construction, which is `AllowanceEntryReadSound.ofFrame`, and
the wrapper's replay clause is the landed arm's `hmid` hoisted out of the
per-key binder: its proof never depended on the key being tagged. -/

/-- Delegated `withdrawFrom` transports the allowance region read-soundly. -/
theorem Exec.Frame.allowanceRegionEffectSound_of_withdrawFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    AllowanceRegionEffectSound ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable withdrawFrom) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [withdrawFromSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨spendCursor, hnonpayableSilent⟩
  have hspendSilent : Devm.DispatchSilent frame.pre spendCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 withdrawFromCoreSlot) frame.post
    at spendCursor
  rcases spendCursor.enterSpendCallerAllowanceThenFork
      context.invocation.2.2.2 (allowanceError_lookup dp)
      (by rw [← hspendSilent.memory]; exact context.memory_wf)
      (by rw [← hspendSilent.memory]; exact context.memory_reads_empty) with
    ⟨body, hget, coreCursor, hwfCore, ⟨imgCore, hreadsCore⟩, hcodeCore,
      hfork⟩
  have hbody : body = withdrawFromCore := by
    simpa [weth10, weth10Aux, withdrawFromCoreSlot] using hget.symm
  subst body
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemFromBody 0 2 (redeemSendToArgPrefix 1) etherTransferErrorSlot
      (Func.last .stop)) frame.post at coreCursor
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hcoreCode : frame.pre.getCode ca = coreCursor.pre.getCode ca :=
    (getCode_eq_of_state_eq hspendSilent.state ca).trans
      (congrFun hcodeCore ca)
  obtain ⟨hstorage, hread⟩ := coreCursor.redeemFromAllowanceSound
    (successLine := []) (target := Sevm.argWord frame.sevm 1)
    (etherTransferError_lookup dp) htarget nil_pref hwfCore hreadsCore
    (by
      rw [← hcoreCode]
      exact context.installed.1)
    (by simp [redeemSendToArgPrefix, pushList, arg, cdl, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToArgPrefix_effect 1 hp hrun)
    (by simp)
    (by func_inv)
    hdeeper
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hselector,
      withdrawFromSelector_ne_flashLoanSelector,
      withdrawFromSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotlast]
  have hpreStor : Devm.getStor frame.pre = Devm.getStor spendCursor.pre :=
    funext (getStor_eq_of_state_eq hspendSilent.state)
  have hmid : ∀ key, InRegion .allowance key →
      (Devm.getStor coreCursor.pre ca).get key =
        applyAllowanceLedger (Devm.getStor frame.pre ca)
          [CountedFrame.ofFrame dp ca frame] key := by
    intro key _hkey
    rw [applyAllowanceLedger_singleton]
    rcases hfork with ⟨hself, hstorEq⟩ | ⟨hnself, hmaxOrFinite⟩
    · have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
        show frameAllowanceEvent frame.sevm frame.pre frame.post = none
        simp [frameAllowanceEvent, hnonempty, hselector,
          withdrawFromSelector_ne_approveSelector,
          withdrawFromSelector_ne_approveAndCallSelector,
          withdrawFromSelector_ne_permitSelector, hself]
      rw [htarget] at hstorEq
      rw [hown, hstorEq, ← congrFun hpreStor ca]
    · rcases hmaxOrFinite with
          ⟨hmaxGet, hstorEq⟩ |
          ⟨allowance, hneMax, hallowGet, hstorSet⟩
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = B256.max := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hmaxGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendMax } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector,
            withdrawFromSelector_ne_approveSelector,
            withdrawFromSelector_ne_approveAndCallSelector,
            withdrawFromSelector_ne_permitSelector, hnself, hbefore]
        rw [htarget] at hstorEq
        rw [hown]
        simp only [AllowanceVisit.written?, ite_self]
        rw [hstorEq, ← congrFun hpreStor ca]
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = allowance := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hallowGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendFinite allowance
                     (allowance - Sevm.argWord frame.sevm 2) } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector,
            withdrawFromSelector_ne_approveSelector,
            withdrawFromSelector_ne_approveAndCallSelector,
            withdrawFromSelector_ne_permitSelector, hnself, hbefore, hneMax]
        rw [htarget] at hstorSet
        rw [hown]
        simp only [AllowanceEvent.key, AllowanceVisit.written?]
        rw [hstorSet]
        by_cases hpk :
            projectedAllowanceKey (Sevm.argWord frame.sevm 0)
              frame.sevm.caller.toB256 = key
        · rw [if_pos hpk, ← hpk, ← callerAllowanceRuntimeKey_eq_projected]
          exact Stor.get_set_self _ _ _
        · have hne : callerAllowanceRuntimeKey frame.sevm ≠ key := by
            rw [callerAllowanceRuntimeKey_eq_projected]
            exact hpk
          rw [if_neg hpk, Stor.get_set_ne _ hne _, ← congrFun hpreStor ca]
  rw [hstream]
  exact (⟨⟨hmid, hcoreCode⟩,
      AllowanceEntryReadSound.ofFrame htarget
        (isFlashInvocation_eq_false_of_ownRecordLast hnotlast)⟩ :
    AllowanceRegionEffectSound ca frame.pre coreCursor.pre
      [CountedFrame.ofFrame dp ca frame]).append
    ⟨⟨hstorage, hcoreCode.symm.trans
        (Exec.installedCodeEq_committed frame.run frame.committed
          context.installed)⟩,
      hread⟩

/-- Delegated `transferFrom` with a zero raw recipient word transports the
allowance region read-soundly, exactly as delegated `withdrawFrom` does. -/
theorem Exec.Frame.allowanceRegionEffectSound_of_transferFromZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hzero : Sevm.argWord frame.sevm 1 = 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    AllowanceRegionEffectSound ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable transferFrom) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [transferFromSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨spendCursor, hnonpayableSilent⟩
  have hspendSilent : Devm.DispatchSilent frame.pre spendCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 transferFromCoreSlot) frame.post
    at spendCursor
  rcases spendCursor.enterSpendCallerAllowanceThenFork
      context.invocation.2.2.2 (allowanceError_lookup dp)
      (by rw [← hspendSilent.memory]; exact context.memory_wf)
      (by rw [← hspendSilent.memory]; exact context.memory_reads_empty) with
    ⟨body, hget, coreCursor, hwfCore, ⟨imgCore, hreadsCore⟩, hcodeCore,
      hfork⟩
  have hbody : body = transferFromCore := by
    simpa [weth10, weth10Aux, transferFromCoreSlot] using hget.symm
  subst body
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ((arg 1 ++ [iszero]) +++ (transferFromZero <?> transferFromNonzero))
    frame.post at coreCursor
  rcases coreCursor.peelChildlessLine
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine⟩
  have htargetPrefix : [Sevm.argWord frame.sevm 1 =? 0] <<+
      targetBranchCursor.pre.stack := by
    rcases of_run_append (arg 1) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with ⟨afterZero, hzeroRun, hnil⟩
    cases hnil
    exact prefix_of_iszero hzeroRun (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 1 =? 0) = 1 := by
    simp [B256.eqCheck, hzero]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) htargetPrefix with
    ⟨zeroCursor, _hzeroStack, hbranchSilent⟩
  have hlineStor : Devm.getStor coreCursor.pre =
      Devm.getStor targetBranchCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv) htargetLine
  have hlineCode : Devm.getCode coreCursor.pre =
      Devm.getCode targetBranchCursor.pre :=
    Line.of_inv Devm.getCode (by line_inv) htargetLine
  have hlineMem : coreCursor.pre.memory = targetBranchCursor.pre.memory :=
    Line.of_inv Devm.memory (by line_inv) htargetLine
  have hcoreToZero : Devm.getStor coreCursor.pre =
      Devm.getStor zeroCursor.pre := by
    rw [hlineStor, funext (getStor_eq_of_state_eq hbranchSilent.state)]
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemFromBody 0 2 redeemSendToCallerPrefix ethTransferErrorSlot
      (redeemReturnTrueLine +++ Func.last .ret)) frame.post at zeroCursor
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hzeroCode : frame.pre.getCode ca = zeroCursor.pre.getCode ca :=
    (getCode_eq_of_state_eq hspendSilent.state ca).trans
      ((congrFun hcodeCore ca).trans
        ((congrFun hlineCode ca).trans
          (getCode_eq_of_state_eq hbranchSilent.state ca)))
  obtain ⟨hstorage, hread⟩ := zeroCursor.redeemFromAllowanceSound
    (target := frame.sevm.caller.toB256)
    (ethTransferError_lookup dp) htarget nil_pref
    (by rw [← hbranchSilent.memory, ← hlineMem]; exact hwfCore)
    (show Mem.Reads zeroCursor.pre.memory imgCore by
      rw [← hbranchSilent.memory, ← hlineMem]; exact hreadsCore)
    (by
      rw [← hzeroCode]
      exact context.installed.1)
    (by simp [redeemSendToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToCallerPrefix_effect hp hrun)
    (by simp [redeemReturnTrueLine, mstoreAt, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by func_inv)
    hdeeper
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hselector,
      transferFromSelector_ne_flashLoanSelector,
      transferFromSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotlast]
  have hpreStor : Devm.getStor frame.pre = Devm.getStor spendCursor.pre :=
    funext (getStor_eq_of_state_eq hspendSilent.state)
  have hmid : ∀ key, InRegion .allowance key →
      (Devm.getStor zeroCursor.pre ca).get key =
        applyAllowanceLedger (Devm.getStor frame.pre ca)
          [CountedFrame.ofFrame dp ca frame] key := by
    intro key _hkey
    rw [applyAllowanceLedger_singleton, ← congrFun hcoreToZero ca]
    rcases hfork with ⟨hself, hstorEq⟩ | ⟨hnself, hmaxOrFinite⟩
    · have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
        show frameAllowanceEvent frame.sevm frame.pre frame.post = none
        simp [frameAllowanceEvent, hnonempty, hselector,
          transferFromSelector_ne_approveSelector,
          transferFromSelector_ne_approveAndCallSelector,
          transferFromSelector_ne_permitSelector, hself]
      rw [htarget] at hstorEq
      rw [hown, hstorEq, ← congrFun hpreStor ca]
    · rcases hmaxOrFinite with
          ⟨hmaxGet, hstorEq⟩ |
          ⟨allowance, hneMax, hallowGet, hstorSet⟩
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = B256.max := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hmaxGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendMax } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector,
            transferFromSelector_ne_approveSelector,
            transferFromSelector_ne_approveAndCallSelector,
            transferFromSelector_ne_permitSelector, hnself, hbefore]
        rw [htarget] at hstorEq
        rw [hown]
        simp only [AllowanceVisit.written?, ite_self]
        rw [hstorEq, ← congrFun hpreStor ca]
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = allowance := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hallowGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendFinite allowance
                     (allowance - Sevm.argWord frame.sevm 2) } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector,
            transferFromSelector_ne_approveSelector,
            transferFromSelector_ne_approveAndCallSelector,
            transferFromSelector_ne_permitSelector, hnself, hbefore, hneMax]
        rw [htarget] at hstorSet
        rw [hown]
        simp only [AllowanceEvent.key, AllowanceVisit.written?]
        rw [hstorSet]
        by_cases hpk :
            projectedAllowanceKey (Sevm.argWord frame.sevm 0)
              frame.sevm.caller.toB256 = key
        · rw [if_pos hpk, ← hpk, ← callerAllowanceRuntimeKey_eq_projected]
          exact Stor.get_set_self _ _ _
        · have hne : callerAllowanceRuntimeKey frame.sevm ≠ key := by
            rw [callerAllowanceRuntimeKey_eq_projected]
            exact hpk
          rw [if_neg hpk, Stor.get_set_ne _ hne _, ← congrFun hpreStor ca]
  rw [hstream]
  exact (⟨⟨hmid, hzeroCode⟩,
      AllowanceEntryReadSound.ofFrame htarget
        (isFlashInvocation_eq_false_of_ownRecordLast hnotlast)⟩ :
    AllowanceRegionEffectSound ca frame.pre zeroCursor.pre
      [CountedFrame.ofFrame dp ca frame]).append
    ⟨⟨hstorage, hzeroCode.symm.trans
        (Exec.installedCodeEq_committed frame.run frame.committed
          context.installed)⟩,
      hread⟩

end Weth10

end Blanc
