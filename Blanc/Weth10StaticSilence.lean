import Blanc.Weth10AllowanceAccounting
import Blanc.StaticStores

/-!
Static silence for the allowance region.

A committed `permit` frame performs one `STATICCALL` to address `1`.  Normally
that resolves synchronously as the ECRECOVER precompile and retains nothing,
but in-model an EIP-7702 delegation designator installed at address `1` admits
an *interpreted committed static child*, and such a child could in principle
retain counted WETH10 frames of its own — a nested view call into `ca`, for
any `ca`.  The allowance arms currently exclude that world by hypothesis
(`isPrecomp 1` plus `getDelegatedCodeAddress (pre.getCode 1) = none`), which
would thread two extra premises through the selector dispatcher into the
history-level statement and break the invariant that the trace-local
no-collision hypothesis is the sole hypothesis.

This module shows the world is harmless instead, in four steps.

* A *write-free* counted ledger — one whose records commit no allowance word —
  replays to its entry storage, so appending one leaves an
  `AllowanceRegionEffect` unchanged.
* Static propagates: every child spawned from a static context is static
  (`CREATE` cannot spawn at all under `assertDynamic`, and `callMsg` sets
  `isStatic := isStaticcall || sevm.isStatic`), and frame entry hands that flag
  straight to the interpreted child context.  A `STATICCALL` child is static
  whatever its parent was.
* Every WETH10 selector whose allowance visit commits a word — `approve`,
  `approveAndCall`, `permit`, `transferFrom`, `withdrawFrom`, `flashLoan` —
  dispatches to a body that executes an `SSTORE` on every committing path, and
  `SSTORE` clears `assertDynamic` before it commits.  So a committed exact
  WETH10 frame running under `STATIC` records `none` or a `.viewRead`.
* Hence the whole attribution stream of a static subtree is write-free.

`Blanc.Weth10.writeFreeLedger_staticcallCrossing` and
`Blanc.Weth10.AllowanceRegionEffect.snoc_writeFree` are the two lemmas the
`permit` arm consumes in place of its precompile hypotheses.  The `snoc`
form, rather than the `cons` form, is what the arm needs: `permit`'s
`approvePermit` store runs *after* the recovery `STATICCALL` returns, so
`Exec.frameContribution` places its own record behind that subtree.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## List-level transparency of a write-free ledger -/

/-- A counted-frame list is write-free when no record's allowance event
commits a storage word. -/
def WriteFreeLedger (ledger : List CountedFrame) : Prop :=
  ∀ frame ∈ ledger, ∀ event, frame.allowance = some event →
    event.visit.written? = none

theorem writeFreeLedger_nil : WriteFreeLedger [] := by
  intro frame hmem
  cases hmem

theorem WriteFreeLedger.append {left right : List CountedFrame}
    (hleft : WriteFreeLedger left) (hright : WriteFreeLedger right) :
    WriteFreeLedger (left ++ right) := by
  intro frame hmem
  rcases List.mem_append.mp hmem with h | h
  · exact hleft frame h
  · exact hright frame h

theorem WriteFreeLedger.cons {frame : CountedFrame} {rest : List CountedFrame}
    (hhead : ∀ event, frame.allowance = some event →
      event.visit.written? = none)
    (hrest : WriteFreeLedger rest) : WriteFreeLedger (frame :: rest) := by
  intro record hmem
  rcases List.mem_cons.mp hmem with rfl | h
  · exact hhead
  · exact hrest record h

theorem writeFreeLedger_singleton {frame : CountedFrame}
    (hhead : ∀ event, frame.allowance = some event →
      event.visit.written? = none) : WriteFreeLedger [frame] :=
  WriteFreeLedger.cons hhead writeFreeLedger_nil

theorem WriteFreeLedger.reverse {ledger : List CountedFrame}
    (h : WriteFreeLedger ledger) : WriteFreeLedger ledger.reverse := by
  intro frame hmem
  exact h frame (List.mem_reverse.mp hmem)

/-- A write-free walk records no last committed write at any key. -/
theorem lastAllowanceWriteAt_eq_none_of_writeFree
    {ledger : List CountedFrame} (hfree : WriteFreeLedger ledger)
    (key : B256) : lastAllowanceWriteAt ledger key = none := by
  induction ledger with
  | nil => rfl
  | cons frame rest ih =>
      have hframe : ∀ event, frame.allowance = some event →
          event.visit.written? = none :=
        hfree frame (List.mem_cons_self ..)
      have hrest : WriteFreeLedger rest := fun f hf =>
        hfree f (List.mem_cons_of_mem _ hf)
      cases hallow : frame.allowance with
      | none => simpa [lastAllowanceWriteAt, hallow] using ih hrest
      | some event =>
          have hwrite : event.visit.written? = none := hframe event hallow
          by_cases hkey : event.key = key
          · simpa [lastAllowanceWriteAt, hallow, hkey, hwrite] using ih hrest
          · simpa [lastAllowanceWriteAt, hallow, hkey] using ih hrest

/-- Replaying a write-free ledger is the identity on the entry storage. -/
theorem applyAllowanceLedger_writeFree
    (pre : Stor) {ledger : List CountedFrame} (key : B256)
    (hfree : WriteFreeLedger ledger) :
    applyAllowanceLedger pre ledger key = pre.get key := by
  unfold applyAllowanceLedger
  rw [lastAllowanceWriteAt_eq_none_of_writeFree hfree.reverse key]

/-- A write-free suffix is transparent to the ledger replay: the bridging
form the selector arms consume. -/
theorem applyAllowanceLedger_append_writeFree
    (pre : Stor) (left : List CountedFrame) {right : List CountedFrame}
    (key : B256) (hfree : WriteFreeLedger right) :
    applyAllowanceLedger pre (left ++ right) key =
      applyAllowanceLedger pre left key := by
  unfold applyAllowanceLedger
  rw [List.reverse_append, lastAllowanceWriteAt_append,
    lastAllowanceWriteAt_eq_none_of_writeFree hfree.reverse key]

/-- A write-free *prefix* is transparent to the ledger replay: the mirror
bridging form consumed by the arms whose own record follows a write-free
descendant stream. -/
theorem applyAllowanceLedger_writeFree_append
    (pre : Stor) {left : List CountedFrame} (right : List CountedFrame)
    (key : B256) (hfree : WriteFreeLedger left) :
    applyAllowanceLedger pre (left ++ right) key =
      applyAllowanceLedger pre right key := by
  unfold applyAllowanceLedger
  rw [List.reverse_append, lastAllowanceWriteAt_append,
    lastAllowanceWriteAt_eq_none_of_writeFree hfree.reverse key]
  cases lastAllowanceWriteAt right.reverse key <;> rfl

/-! ## Compiled bodies that cannot avoid a storage write -/

/-! `StoresOrHalts` and `StoresOrHalts.isStatic_eq_false` are
`Blanc/StaticStores.lean`, hoisted there once the WETH-backed PRORATA vault
became a second consumer.  Nothing in them named this contract. -/


/-! ## The writing WETH10 selectors all store -/

/-- Walk a body down to the first `SSTORE` on every branch, leaving the
guard arms that dispatch to an auxiliary slot. -/
syntax "stores_walk" : tactic
macro_rules
  | `(tactic| stores_walk) =>
    `(tactic|
        repeat' first
          | exact StoresOrHalts.store
          | apply StoresOrHalts.next
          | apply StoresOrHalts.branch)

/-- A guard arm dispatching to a constant `Error(string)` reverter never
runs, so it stores vacuously. -/
theorem storesOrHalts_revertWithSlot {fs : List Func} {k : Nat} {reason : String}
    (hget : fs[k]? = some (Func.revertWith reason)) :
    StoresOrHalts fs (Func.call k) :=
  .call hget (.never Func.not_run_revertWith)

theorem storesOrHalts_approve {fs : List Func} :
    StoresOrHalts fs approve := by
  unfold approve approvePrefix
  stores_walk

theorem storesOrHalts_approveAndCall {fs : List Func} :
    StoresOrHalts fs approveAndCall := by
  unfold approveAndCall approvePrefix
  stores_walk

theorem storesOrHalts_flashTokenErrorSlot (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux)
      (Func.call flashTokenErrorSlot) :=
  storesOrHalts_revertWithSlot (reason := "WETH: flash mint only WETH10")
    (by simp [weth10Aux, flashTokenErrorSlot, flashTokenError])

theorem storesOrHalts_individualLimitErrorSlot (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux)
      (Func.call individualLimitErrorSlot) :=
  storesOrHalts_revertWithSlot
    (reason := "WETH: individual loan limit exceeded")
    (by simp [weth10Aux, individualLimitErrorSlot, individualLimitError])

theorem storesOrHalts_allowanceErrorSlot (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux)
      (Func.call allowanceErrorSlot) :=
  storesOrHalts_revertWithSlot (reason := "WETH: request exceeds allowance")
    (by simp [weth10Aux, allowanceErrorSlot, allowanceError])

theorem storesOrHalts_burnBalanceErrorSlot (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux)
      (Func.call burnBalanceErrorSlot) :=
  storesOrHalts_revertWithSlot (reason := "WETH: burn amount exceeds balance")
    (by simp [weth10Aux, burnBalanceErrorSlot, burnBalanceError])

theorem storesOrHalts_expiredPermitErrorSlot (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux)
      (Func.call expiredPermitErrorSlot) :=
  storesOrHalts_revertWithSlot (reason := "WETH: Expired permit")
    (by simp [weth10Aux, expiredPermitErrorSlot, expiredPermitError])

theorem storesOrHalts_transferBalanceErrorSlot (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux)
      (Func.call transferBalanceErrorSlot) :=
  storesOrHalts_revertWithSlot
    (reason := "WETH: transfer amount exceeds balance")
    (by simp [weth10Aux, transferBalanceErrorSlot, transferBalanceError])

/-- Discharge the guard arms a `stores_walk` leaves behind. -/
syntax "stores_slots" : tactic
macro_rules
  | `(tactic| stores_slots) =>
    `(tactic|
        all_goals first
          | exact storesOrHalts_flashTokenErrorSlot _
          | exact storesOrHalts_individualLimitErrorSlot _
          | exact storesOrHalts_allowanceErrorSlot _
          | exact storesOrHalts_burnBalanceErrorSlot _
          | exact storesOrHalts_expiredPermitErrorSlot _
          | exact storesOrHalts_transferBalanceErrorSlot _)

theorem storesOrHalts_permit (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux) (permit dp) := by
  unfold permit
  stores_walk
  stores_slots

theorem storesOrHalts_transferFromCore (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux) transferFromCore := by
  unfold transferFromCore transferFromNonzero transferFromZero
    loadArgBalanceAmount balanceTooSmall debitLoadedBalance
  stores_walk
  stores_slots

theorem storesOrHalts_withdrawFromCore (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux) withdrawFromCore := by
  unfold withdrawFromCore loadArgBalanceAmount balanceTooSmall
    debitLoadedBalance
  stores_walk
  stores_slots

theorem storesOrHalts_transferFromCoreSlot (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux)
      (Func.call transferFromCoreSlot) :=
  .call (by simp [weth10Aux, transferFromCoreSlot])
    (storesOrHalts_transferFromCore dp)

theorem storesOrHalts_withdrawFromCoreSlot (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux)
      (Func.call withdrawFromCoreSlot) :=
  .call (by simp [weth10Aux, withdrawFromCoreSlot])
    (storesOrHalts_withdrawFromCore dp)

theorem storesOrHalts_transferFrom (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux) transferFrom := by
  unfold transferFrom spendCallerAllowanceThen
  stores_walk
  all_goals first
    | exact storesOrHalts_transferFromCoreSlot _
    | exact storesOrHalts_allowanceErrorSlot _

theorem storesOrHalts_withdrawFrom (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux) withdrawFrom := by
  unfold withdrawFrom spendCallerAllowanceThen
  stores_walk
  all_goals first
    | exact storesOrHalts_withdrawFromCoreSlot _
    | exact storesOrHalts_allowanceErrorSlot _

theorem storesOrHalts_flashLoan (dp : DeployParams) :
    StoresOrHalts ((weth10 dp).main :: weth10Aux) flashLoan := by
  unfold flashLoan
  stores_walk
  stores_slots

/-! ## Dispatch memberships for the writing selectors -/

theorem approve_mem_weth10Funcs (dp : DeployParams) :
    (approveSelector, nonpayable approve) ∈ weth10Funcs dp := by
  simp only [weth10Funcs, approveSelector]
  exact .tail _ <| .head _

theorem approveAndCall_mem_weth10Funcs (dp : DeployParams) :
    (approveAndCallSelector, nonpayable approveAndCall) ∈ weth10Funcs dp := by
  simp only [weth10Funcs, approveAndCallSelector]
  exact .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <|
    .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <|
    .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <|
    .tail _ <| .tail _ <| .tail _ <| .head _

theorem transferFrom_mem_weth10Funcs (dp : DeployParams) :
    (transferFromSelector, nonpayable transferFrom) ∈ weth10Funcs dp := by
  simp only [weth10Funcs, transferFromSelector]
  exact .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _

theorem withdrawFrom_mem_weth10Funcs (dp : DeployParams) :
    (withdrawFromSelector, nonpayable withdrawFrom) ∈ weth10Funcs dp := by
  simp only [weth10Funcs, withdrawFromSelector]
  exact .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <|
    .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <|
    .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _

/-! ## A static exact frame cannot run a writing selector -/

/-- An exact WETH10 frame whose dispatched body cannot avoid an `SSTORE`
runs in a dynamic context. -/
theorem Exec.Frame.isStatic_eq_false_of_storesOrHalts
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (hexact : Blanc.Weth10.Exec.Frame.exactInvocation dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, nonpayable body) ∈ weth10Funcs dp)
    (hstores : StoresOrHalts ((weth10 dp).main :: weth10Aux) body) :
    frame.sevm.isStatic = false := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error _ => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := hexact.1
      subst hpc
      rcases exec_enters_weth10Nonpayable_logs run hexact.2.2.2 rfl hnonempty
          hmem with
        ⟨_, _, _, _, _, _, _, _, hbody⟩
      exact hstores.isStatic_eq_false hbody

private theorem static_writing_selector_absurd
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (hexact : Blanc.Weth10.Exec.Frame.exactInvocation dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, nonpayable body) ∈ weth10Funcs dp)
    (hstores : StoresOrHalts ((weth10 dp).main :: weth10Aux) body)
    (hstatic : frame.sevm.isStatic = true) : False := by
  rw [Exec.Frame.isStatic_eq_false_of_storesOrHalts hexact hnonempty hmem
    hstores] at hstatic
  exact Bool.noConfusion hstatic

/-- The per-frame static fact: a committed exact WETH10 frame running under
`STATIC` records no writing allowance visit. -/
theorem frameAllowanceEvent_written_eq_none_of_static
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hexact : Blanc.Weth10.Exec.Frame.exactInvocation dp ca frame)
    (hstatic : frame.sevm.isStatic = true)
    {event : AllowanceEvent}
    (hevent :
      frameAllowanceEvent frame.sevm frame.pre frame.post = some event) :
    event.visit.written? = none := by
  unfold frameAllowanceEvent at hevent
  split at hevent
  · exact absurd hevent (by simp)
  · rename_i hnonempty
    split at hevent
    · exfalso
      rename_i hsel
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hsel
      rcases hsel with h | h
      · exact static_writing_selector_absurd (body := approve) hexact
          hnonempty (by rw [h]; exact approve_mem_weth10Funcs dp)
          storesOrHalts_approve hstatic
      · exact static_writing_selector_absurd (body := approveAndCall) hexact
          hnonempty (by rw [h]; exact approveAndCall_mem_weth10Funcs dp)
          storesOrHalts_approveAndCall hstatic
    · split at hevent
      · exfalso
        rename_i hsel
        exact static_writing_selector_absurd (body := permit dp) hexact
          hnonempty (by rw [hsel]; exact permit_mem_weth10Funcs dp)
          (storesOrHalts_permit dp) hstatic
      · split at hevent
        · exfalso
          rename_i hsel
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hsel
          rcases hsel with h | h
          · exact static_writing_selector_absurd (body := transferFrom) hexact
              hnonempty (by rw [h]; exact transferFrom_mem_weth10Funcs dp)
              (storesOrHalts_transferFrom dp) hstatic
          · exact static_writing_selector_absurd (body := withdrawFrom) hexact
              hnonempty (by rw [h]; exact withdrawFrom_mem_weth10Funcs dp)
              (storesOrHalts_withdrawFrom dp) hstatic
        · split at hevent
          · exfalso
            rename_i hsel
            exact static_writing_selector_absurd (body := flashLoan) hexact
              hnonempty (by rw [hsel]; exact flashLoan_mem_weth10Funcs dp)
              (storesOrHalts_flashLoan dp) hstatic
          · split at hevent
            · cases hevent
              rfl
            · exact absurd hevent (by simp)

/-! ## Write-freeness of a static subtree -/

/-- A static frame's own counted record, if it is counted at all, carries no
writing visit; so its whole contribution is write-free whenever its
descendant stream is. -/
theorem writeFreeLedger_frameContribution
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {inner : List CountedFrame}
    (hstatic : frame.sevm.isStatic = true)
    (hinner : WriteFreeLedger inner) :
    WriteFreeLedger (Exec.frameContribution dp ca frame inner) := by
  unfold Exec.frameContribution
  split
  · rename_i hexact
    have hown : ∀ event,
        (CountedFrame.ofFrame dp ca frame).allowance = some event →
          event.visit.written? = none := by
      intro event hallow
      exact frameAllowanceEvent_written_eq_none_of_static hexact hstatic hallow
    split
    · exact hinner.append (writeFreeLedger_singleton hown)
    · exact WriteFreeLedger.cons hown hinner
  · exact hinner

/-- Every counted record contributed by the proper descendants of a static
execution is non-writing. -/
theorem Exec.attributionInner_writeFree_of_static
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    sevm.isStatic = true →
      WriteFreeLedger (Exec.attributionInner dp ca run) := by
  induction run with
  | halt _ =>
      intro _
      rw [Exec.attributionInner]
      exact writeFreeLedger_nil
  | cont _ _ ih =>
      intro hstatic
      rw [Exec.attributionInner]
      exact ih hstatic
  | doneErr _ _ _ =>
      intro _
      rw [Exec.attributionInner]
      exact writeFreeLedger_nil
  | doneOk _ _ _ _ ih =>
      intro hstatic
      rw [Exec.attributionInner]
      exact ih hstatic
  | runErr _ _ _ _ _ =>
      intro _
      rw [Exec.attributionInner]
      exact writeFreeLedger_nil
  | runOk hstep henter child hr next ihchild ihnext =>
      intro hstatic
      have hchild := Blanc.Evm.step_run_isStatic hstep henter hstatic
      rw [Exec.attributionInner]
      refine WriteFreeLedger.append ?_ (ihnext hstatic)
      split
      · exact writeFreeLedger_frameContribution hchild (ihchild hchild)
      · exact writeFreeLedger_nil

/-- Every counted record contributed by a static execution — its own record
included — is non-writing. -/
theorem Exec.attributionStream_writeFree_of_static
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hstatic : sevm.isStatic = true) :
    WriteFreeLedger (Exec.attributionStream dp ca run) := by
  unfold Exec.attributionStream
  split
  · exact writeFreeLedger_frameContribution hstatic
      (Exec.attributionInner_writeFree_of_static run hstatic)
  · exact writeFreeLedger_nil

/-! ## The payoff -/

/-- Appending a write-free segment leaves an allowance-region transport
unchanged. -/
theorem AllowanceRegionEffect.append_writeFree
    {ca : Adr} {pre post : Devm} {left right : List CountedFrame}
    (h : AllowanceRegionEffect ca pre post left)
    (hfree : WriteFreeLedger right) :
    AllowanceRegionEffect ca pre post (left ++ right) := by
  refine ⟨fun key hregion => ?_, h.codeEq⟩
  rw [applyAllowanceLedger_append_writeFree _ left key hfree]
  exact h.storage key hregion

/-- Cons form: a frame whose own record already transports the region keeps
transporting it once a write-free descendant stream is appended. -/
theorem AllowanceRegionEffect.cons_writeFree
    {ca : Adr} {pre post : Devm} {own : CountedFrame}
    {rest : List CountedFrame}
    (h : AllowanceRegionEffect ca pre post [own])
    (hfree : WriteFreeLedger rest) :
    AllowanceRegionEffect ca pre post (own :: rest) := by
  simpa using h.append_writeFree hfree

/-- Prepending a write-free segment leaves an allowance-region transport
unchanged. -/
theorem AllowanceRegionEffect.writeFree_append
    {ca : Adr} {pre post : Devm} {left right : List CountedFrame}
    (hfree : WriteFreeLedger left)
    (h : AllowanceRegionEffect ca pre post right) :
    AllowanceRegionEffect ca pre post (left ++ right) := by
  refine ⟨fun key hregion => ?_, h.codeEq⟩
  rw [applyAllowanceLedger_writeFree_append _ right key hfree]
  exact h.storage key hregion

/-- Snoc form: a frame whose own record already transports the region keeps
transporting it once a write-free descendant stream is placed *ahead* of it.
This is what `permit` and any other own-record-last selector consume in place
of `AllowanceRegionEffect.cons_writeFree`. -/
theorem AllowanceRegionEffect.snoc_writeFree
    {ca : Adr} {pre post : Devm} {own : CountedFrame}
    {rest : List CountedFrame}
    (h : AllowanceRegionEffect ca pre post [own])
    (hfree : WriteFreeLedger rest) :
    AllowanceRegionEffect ca pre post (rest ++ [own]) :=
  h.writeFree_append hfree

/-! ## Read-side transparency of a write-free segment

`WriteFreeLedger` makes a segment invisible to the ledger *replay*.  The
three lemmas below make it invisible to the *entry-read clause* as well,
which is what an own-record-last arm needs once its carrier is strengthened
to `AllowanceRegionEffectSound`: a descendant stream placed ahead of the own
record neither moves the region nor shifts the prefix that any later record
replays over. -/

/-- Entry-read soundness inspects its entry storage only at projected
allowance keys, so two entry states agreeing there are interchangeable. -/
theorem AllowanceEntryReadSound.congr {pre pre' : Stor}
    {ledger : List CountedFrame}
    (hagree : ∀ key, InRegion .allowance key → pre.get key = pre'.get key)
    (hsound : AllowanceEntryReadSound pre ledger) :
    AllowanceEntryReadSound pre' ledger := by
  intro earlier record later hsplit event hevent v hread
  have hkey : InRegion .allowance event.key :=
    projectedAllowanceKey_region event.owner event.spender
  rw [← applyAllowanceLedger_congr (ledger := earlier) (hagree event.key hkey)]
  exact hsound earlier record later hsplit event hevent v hread

/-- A write-free segment placed ahead of a record that reads nothing leaves
the composite ledger's entry-read clause exactly the segment's own: the only
split putting the trailing record in the clause's position is vacuous, and
every split inside the segment replays over a transparent prefix. -/
theorem AllowanceEntryReadSound.snoc_writeFree {pre : Stor}
    {rest : List CountedFrame} {own : CountedFrame}
    (hfree : WriteFreeLedger rest)
    (hrest : AllowanceEntryReadSound pre rest)
    (hown : ∀ event, own.allowance = some event → event.visit.read? = none) :
    AllowanceEntryReadSound pre (rest ++ [own]) := by
  refine AllowanceEntryReadSound.append (mid := pre)
    (fun key _ => (applyAllowanceLedger_writeFree pre key hfree).symm) hrest ?_
  refine .singleton (fun event hevent v hread => ?_)
  rw [hown event hevent] at hread
  exact absurd hread (by simp)

/-- Read-sound snoc form: a frame whose own record already transports the
region and records no read keeps transporting it read-soundly once a
write-free, entry-read-sound descendant stream is placed *ahead* of it.  This
is what `permit` consumes in place of `AllowanceRegionEffect.snoc_writeFree`.
`flashLoan` cannot use it — its own record does record a read, reconstructed
from the committed post state — and takes the flash exemption instead. -/
theorem AllowanceRegionEffectSound.snoc_writeFree
    {ca : Adr} {pre post : Devm} {own : CountedFrame}
    {rest : List CountedFrame}
    (heffect : AllowanceRegionEffect ca pre post [own])
    (hfree : WriteFreeLedger rest)
    (hrest : AllowanceEntryReadSound (Devm.getStor pre ca) rest)
    (hown : ∀ event, own.allowance = some event → event.visit.read? = none) :
    AllowanceRegionEffectSound ca pre post (rest ++ [own]) :=
  { heffect.writeFree_append hfree with
    entryRead := .snoc_writeFree hfree hrest hown }

/-- The lemma the `permit` arm consumes in place of its two precompile
hypotheses: whatever the EIP-7702 delegation designator at address `1`
installs, the `STATICCALL` child's whole counted contribution is write-free,
because every counted frame it can retain runs under `STATIC` and WETH10's
writing selectors all execute an `SSTORE` on every committing path. -/
theorem writeFreeLedger_staticcallCrossing
    {dp : DeployParams} {ca : Adr}
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {f : Jaune.Frame} {rsm : Resume} {cevm : Evm} {raw : Execution}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.staticcall = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw) :
    WriteFreeLedger
      (if h : Blanc.Frame.settlementCommits f raw = true then
        Exec.frameContribution dp ca
          (Exec.Frame.ofRun child
            (Blanc.Frame.raw_commits_of_settlementCommits h))
          (Exec.attributionInner dp ca child)
       else []) := by
  have hstatic : cevm.sta.isStatic = true :=
    Blanc.Ninst.step_staticcall_run_isStatic hspawn henter
  split
  · exact writeFreeLedger_frameContribution hstatic
      (Exec.attributionInner_writeFree_of_static child hstatic)
  · exact writeFreeLedger_nil

/-- Stream form of the crossing: a committed `STATICCALL` child's whole
attribution stream is write-free. -/
theorem Exec.attributionStream_writeFree_of_staticcallChild
    {dp : DeployParams} {ca : Adr}
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {f : Jaune.Frame} {rsm : Resume} {cevm : Evm} {raw : Execution}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.staticcall = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw) :
    WriteFreeLedger (Exec.attributionStream dp ca child) :=
  Exec.attributionStream_writeFree_of_static child
    (Blanc.Ninst.step_staticcall_run_isStatic hspawn henter)

end Weth10

end Blanc
