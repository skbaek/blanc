import Blanc.Composition.UniswapV2PairWeth9XLegFactory
import Blanc.Composition.UniswapV2PairWeth9XLegLocked
import Blanc.Composition.UniswapV2PairWeth9XLegWeth
import Blanc.CallSpawnExact
import Blanc.Lift.CallSiteChildren
import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionTraceCalldata
import Blanc.LockExclusion

/-!
# X-leg quiescence: the other token's transfer child cannot lower the Pair's WETH9 balance

The Pair's swap (and burn, skim) pays the other token `X` first when WETH9 is `token1`: a `CALL` from a
Pair frame whose result `d0` is given by an arbitrary callee record (`Ninst.RunCompiled … (.exec .call)
d0`, which holds X's actual run as its filled slot).  `xleg_call` proves, at that one crossing:

* WETH9's code persists and WETH9's footprint invariant holds at `d0` over a universe extended by the
  keys X's run touches at WETH9;
* the Pair's booked WETH9 balance at `d0` is at least the one before, and its allowances stay zero.

Premises: the facts at the world before the call (WETH9 code and footprint, the Pair's allowances zero,
the Pair runtime with a **locked** model state, the factory runtime at the stored factory, `pair ≠ 0`,
the ether-supply bound), the callee is not WETH9, and HASH-T over the keys X's run touches
(`CallChildFresh`: WETH9 frame keys, Pair writer rows).  Nothing about WETH9's answers.

The argument: no committed non-static WETH9 frame of X's run has caller `pair` (caller fold: a WETH9
frame calls as WETH9, a Pair frame of X's run is locked and so has only static children,
`run_lockedBelow`, whose factory premise is `frame_factoryQuiet`); hence `run_weth_holder` over X's run,
transported across the crossing by the holder carrier (`holderCarrier`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9XLeg

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token Blanc.ExecutionTrace
  Blanc.ExecutionAccountingReplay Blanc.Composition.Weth9Token Blanc.Composition.Weth9TokenFrames
open Blanc.Lift.UniswapV2Pair (WriterRep WriterKey WriterFreshKeys WriterExtend pairEntry pairSem
  pairDerivKeys PairGood LockedBelow FactoryQuiet pairGood_of_keys)

/-! ## The keys X's run touches -/

/-- The WETH9 keys every WETH9 frame entered below a derivation may touch (rolled-back frames
included). -/
def wethRunKeys (ca : Adr) (D : Exec.Deriv) : List Key :=
  (Exec.rawFrameRoots D.exc).flatMap fun root =>
    if root.sevm.currentTarget = ca then frameKeys root.sevm else []

/-- The Pair writer rows every Pair frame entered below a derivation may touch. -/
noncomputable def pairRunKeys (pair : Adr) (D : Exec.Deriv) : List WriterKey :=
  (Exec.rawFrameRoots D.exc).flatMap fun root =>
    if root.sevm.currentTarget = pair then pairDerivKeys root else []

/-- **HASH-T for the child a `CALL` enters**: `P` holds of every derivation of the frame the
instruction spawns and enters. -/
def CallChildFresh (sevm : Sevm) (devm : Devm) (P : Exec.Deriv → Prop) : Prop :=
  ∀ {frame : Frame} {rsm : Resume} {cevm : Evm} {raw : Execution},
    Xinst.step sevm devm .call = .spawn frame rsm → frame.enter = .run cevm →
    ∀ child : Exec cevm.pc cevm.sta cevm.dyna raw, P ⟨cevm.pc, cevm.sta, cevm.dyna, raw, child⟩

/-! ## The entered `CALL` child -/

/-- What an entered `CALL` child is: pc `0`, the popped target, the caller's address as caller, the
caller's code map, the target's own code when it is no designator, short calldata, a covered fork,
and (for a code-bearing account) the caller's storage. -/
theorem call_child_facts {sevm : Sevm} {s : Devm} {f : Frame} {rsm : Resume} {cevm : Evm}
    (fork : CoveredFork sevm.benvStat.fork) (hx : Xinst.step sevm s .call = .spawn f rsm)
    (enter : f.enter = .run cevm) :
    ∃ g c v ii is oi os rest, s.stack = g :: c :: v :: ii :: is :: oi :: os :: rest ∧
      cevm.pc = 0 ∧ cevm.sta.currentTarget = c.toAdr ∧ cevm.sta.caller = sevm.currentTarget ∧
      (∀ a, cevm.dyna.getCode a = s.getCode a) ∧
      (getDelegatedCodeAddress (s.getCode c.toAdr) = none → cevm.sta.code = s.getCode c.toAdr) ∧
      cevm.sta.data.length < 2 ^ 256 ∧ CoveredFork cevm.sta.benvStat.fork ∧
      (∀ a, s.getCode a ≠ .empty → cevm.dyna.state.getStor a = s.state.getStor a) := by
  obtain ⟨g, c, v, ii, is, oi, os, rest, hstack⟩ := Xinst.step_call_spawn_stack fork hx
  have hn : Ninst.step ⟨0, sevm, s⟩ Ninst.call = .spawn f rsm 1 := by
    rw [Ninst.call, Ninst.step_exec]
    simp only [hx, XStep.toStep]
  obtain ⟨parent, dp, na, code, avail, -, -, -, -, source, hframe, -⟩ :=
    Ninst.step_call_spawn_exact hn hstack fork
  obtain ⟨benv, transfer, hcevm⟩ := Frame.enter_run_inv enter
  refine ⟨g, c, v, ii, is, oi, os, rest, hstack, Frame.enter_run_pc enter, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [Frame.enter_run_currentTarget enter, hframe]
    rfl
  · rw [hcevm, hframe]
    rfl
  · intro a
    rw [Frame.enter_run_getCode enter a]
    exact Xinst.step_spawn_getCode hx a
  · intro undelegated
    rw [Frame.enter_run_code enter, hframe]
    rcases source with ⟨-, -, rfl, -⟩ | ⟨d, delegated, -⟩
    · rfl
    · rw [undelegated] at delegated
      cases delegated
  · rw [Frame.enter_data_eq enter]
    exact Xinst.step_spawn_inner_data_length_lt fork.rules_stateGas_none hx
  · rw [Frame.enter_run_benvStat enter, Xinst.step_spawn_benvStat hx]
    exact fork
  · intro a ha
    obtain ⟨hstor, -⟩ := Xinst.step_spawn_world fork hx ha
    have protection : State.Protected f.inner.benv.state a := by
      right
      intro codeEmpty
      exact ha ((Xinst.step_spawn_getCode hx a).symm.trans
        (ByteArray.eq_empty_of_size_eq_zero codeEmpty))
    rw [hcevm]
    exact (benvAfterTransfer_ok_getStor transfer a (Or.inr protection)).trans hstor

/-- An installed code image is no delegation designator. -/
theorem undelegated_of_image {sem : CodeSem} {c : ByteArray} (h : some c.toList = sem.image) :
    getDelegatedCodeAddress c = none := by
  unfold getDelegatedCodeAddress
  simp only [sem.not_delegation h, ↓reduceIte]

/-! ## The holder carrier -/

/-- **The holder carrier**: a boundary is WETH9's footprint ledger over `U`; a replay says that a
holder `h` with no allowance keeps its balance from below and its zero allowances. -/
noncomputable def holderCarrier (ca : Adr) (U : Key → Prop) (h : Adr) : ReplayCarrier ca where
  Snap := Weth9.Ledger
  Step := Unit
  Tag := Unit
  Replay a _ b := (∀ g, weth9Book.allow a h g = 0) →
    weth9Book.bal a h ≤ weth9Book.bal b h ∧ ∀ g, weth9Book.allow b h g = 0
  ofState state := ledger U (state.getStor ca)
  frameEntry _ state := ledger U (state.getStor ca)
  nil _ := fun zero => ⟨Nat.le_refl _, zero⟩
  readsStorage := true
  silent := fun hstor _ => by rw [hstor rfl]
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_⟩
    show (∀ g, weth9Book.allow (ledger U (pre.getStor ca)) h g = 0) →
      weth9Book.bal (ledger U (pre.getStor ca)) h ≤ weth9Book.bal (ledger U (post.getStor ca)) h ∧
        ∀ g, weth9Book.allow (ledger U (post.getStor ca)) h g = 0
    rw [storage]
    exact fun zero => ⟨Nat.le_refl _, zero⟩
  entry_eq_ofState := by
    intro msg entry caller_ne _ transfer sum_nof
    show ledger U _ = ledger U _
    rw [benvAfterTransfer_getStor_eq_of_safe transfer sum_nof
      (fun ht _ => Or.inl (caller_ne ht))]

/-! ## The crossing -/

/-- The footprint precondition at a foreign frame, from its parts. -/
theorem foot_pre {ca : Adr} {U : Key → Prop} {sevm : Sevm} {d : Devm}
    (targetNe : sevm.currentTarget ≠ ca) (wethCode : d.getCode ca = Weth9.code)
    (foot : FootInv U (d.state.getStor ca) (d.state.bal ca)) (bound : sum d.state.bal < 2 ^ 256) :
    (footSpec U).Pre ca sevm d := by
  refine ⟨by rw [wethCode]; rfl, bound, fun h => (targetNe h).elim, fun _ => ?_⟩
  refine footSpec_inv.mpr ⟨foot.support, ?_⟩
  have backed := foot.backed
  rw [B256.toNat_zero]
  exact Nat.add_zero _ ▸ backed

/-- The footprint invariant at a foreign frame's precondition, over injective, apart keys. -/
theorem footInv_of_pre {ca : Adr} {U : Key → Prop} {sevm : Sevm} {d : Devm}
    (targetNe : sevm.currentTarget ≠ ca) (inj : KeyInj U) (apart : KeyApart U)
    (pre : (footSpec U).Pre ca sevm d) : FootInv U (d.state.getStor ca) (d.state.bal ca) := by
  obtain ⟨support, backed⟩ := footSpec_inv.mp (pre.inv.2 targetNe)
  rw [B256.toNat_zero, Nat.add_zero] at backed
  exact ⟨support, inj, apart, backed⟩

/-- **X-leg quiescence at one `CALL` crossing.**  A `CALL` from a Pair frame (`atPair`) to a callee
other than WETH9, given as an arbitrary callee record, from a world where WETH9's code and footprint
hold, the Pair's WETH9 allowances are zero, the Pair runtime holds a locked model state over rows `K`,
the factory runtime sits at that state's factory, `pair ≠ 0` and the ether supply fits a word: under
HASH-T over the keys the callee's run touches, WETH9's code and footprint (over an extended universe)
and the supply bound hold at the result, the Pair's booked WETH9 balance has not dropped, and its
allowances are still zero. -/
theorem xleg_call {ca pair : Adr} {U : Key → Prop} {K : WriterKey → Prop}
    {st : UniswapV2Pair.State} {sevm : Sevm} {devm d0 : Devm}
    (run : Ninst.RunCompiled sevm devm (.exec .call) d0)
    (fork : CoveredFork sevm.benvStat.fork) (atPair : sevm.currentTarget = pair)
    (callee : ∀ g c v ii is oi os rest,
      devm.stack = g :: c :: v :: ii :: is :: oi :: os :: rest → c.toAdr ≠ ca)
    (apart : pair ≠ ca) (wethCode : devm.getCode ca = Weth9.code)
    (foot : FootInv U (devm.state.getStor ca) (devm.state.bal ca))
    (zero : ∀ g, weth9Book.allow (ledger U (devm.state.getStor ca)) pair g = 0)
    (pairCode : devm.getCode pair = UniswapV2Pair.code)
    (rep : WriterRep K (devm.state.getStor pair) st) (locked : st.unlocked ≠ 1)
    (factoryCode : devm.getCode st.factory = UniswapV2Factory.code)
    (pairNonzero : pair ≠ 0) (bound : sum devm.state.bal < 2 ^ 256)
    (wethFresh : CallChildFresh sevm devm fun D => KeysFresh U (wethRunKeys ca D))
    (pairFresh : CallChildFresh sevm devm fun D => WriterFreshKeys K (pairRunKeys pair D)) :
    ∃ U' : Key → Prop, (∀ k, U k → U' k) ∧ d0.getCode ca = Weth9.code ∧
      FootInv U' (d0.state.getStor ca) (d0.state.bal ca) ∧ sum d0.state.bal < 2 ^ 256 ∧
      weth9Book.bal (ledger U (devm.state.getStor ca)) pair ≤
        weth9Book.bal (ledger U' (d0.state.getStor ca)) pair ∧
      ∀ g, weth9Book.allow (ledger U' (d0.state.getStor ca)) pair g = 0 := by
  have targetNe : sevm.currentTarget ≠ ca := by rw [atPair]; exact apart
  have wethImage : some (devm.state.getCode ca).toList = weth9Sem.image := by
    show some (devm.getCode ca).toList = _
    rw [wethCode]
    rfl
  have protection : State.Protected devm.state ca := State.Protected.of_image wethImage
  obtain ⟨xl, filled, steps⟩ := run
  have xrun : Xinst.Run sevm devm .call xl (.ok d0) := XStep.run_toStep.mp (steps 0)
  cases xl with
  | none =>
    have step0 := steps 0
    have preD0 := ContractSpecSem.Ninst.none_preserves_precond (c := footSpec U) fork step0
      targetNe (foot_pre targetNe wethCode foot bound)
    have storEq := Ninst.foreignNone_getStor_eq fork step0 targetNe protection
    refine ⟨U, fun _ h => h, code_eq_of_image preD0.code,
      footInv_of_pre targetNe foot.inj foot.apart preD0, preD0.side, ?_, ?_⟩
    · change weth9Book.bal (ledger U (Devm.getStor devm ca)) pair ≤
        weth9Book.bal (ledger U (Devm.getStor d0 ca)) pair
      rw [storEq]
    · change ∀ g, weth9Book.allow (ledger U (Devm.getStor d0 ca)) pair g = 0
      rw [storEq]
      exact zero
  | some slot =>
    obtain ⟨⟨cpc, csta, cdyna⟩, raw⟩ := slot
    obtain ⟨child⟩ := filled
    have hxrun := xrun
    cases spawnEq : Xinst.step sevm devm .call with
    | done execution =>
      simp only [Xinst.Run, XStep.Run, spawnEq, ExceptT.stM_eq, reduceCtorEq, false_and] at hxrun
    | spawn frame resume =>
    simp only [Xinst.Run, spawnEq, XStep.Run] at hxrun
    obtain ⟨result, frameRun, resumeRun⟩ := hxrun
    cases result with
    | error error =>
      cases resume <;> simp only [ExceptT.stM_eq, Resume.run, liftToExecution, Except.bind_error,
        reduceCtorEq] at resumeRun
    | ok settled =>
    have enter := (RunFrame.some_inv frameRun).1
    obtain ⟨g, c, v, ii, is, oi, os, rest, hstack, pc0, cTarget, cCaller, cGetCode, cCode, cData,
      cFork, cStor⟩ := call_child_facts fork spawnEq enter
    dsimp only at pc0 cTarget cCaller cGetCode cCode cData cFork cStor
    subst pc0
    have childTargetNe : csta.currentTarget ≠ ca := by
      rw [cTarget]
      exact callee g c v ii is oi os rest hstack
    -- WETH9's universe, extended by the keys X's run touches at WETH9
    have freshW := wethFresh spawnEq enter child
    have footW := foot.extend freshW
    have injW := footW.inj
    have preW := foot_pre targetNe wethCode footW bound
    obtain ⟨childPre, cont⟩ :=
      ContractSpecSem.Xinst.some_preserves_precond (c := footSpec (Key.extend U
        (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩))) fork xrun child targetNe preW
    have admittedW : Exec.FrameAdmitted ca (footEntry (Key.extend U
        (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩))) child := by
      intro root member target k hk
      exact Or.inr (List.mem_flatMap.mpr ⟨root, member, by rw [ite_eq_left target]; exact hk⟩)
    have childAt : weth9Sem.At ca 0 csta cdyna := ⟨childPre.code, fun t => (childTargetNe t).elim⟩
    have childBound : sum cdyna.state.bal < 2 ^ 256 := childPre.side
    have childPreWf : (footSpec (Key.extend U (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩))).PreWf
        ca csta cdyna := ⟨childPre, fun t => (childTargetNe t).elim⟩
    have preD0 : (footSpec (Key.extend U (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩))).Pre
        ca sevm d0 := by
      apply cont
      clear cont
      cases raw with
      | error e => trivial
      | ok post =>
        exact footSpec_preservesAdmitted ca injW csta cdyna post cFork child admittedW
          (fun t => (childTargetNe t).elim) (fun t => (childTargetNe t).elim) childPre
    -- The Pair's universe, extended by the rows X's run touches at the Pair
    have repP := rep.extend (pairFresh spawnEq enter child)
    have pairNonEmpty : devm.getCode pair ≠ .empty := by
      intro empty
      have nil := congrArg ByteArray.toList empty
      rw [pairCode] at nil
      exact UniswapV2Pair.pairSem.ne_nil rfl (nil.trans ByteArray.toList_empty)
    have repC := WriterRep.congr (s' := cdyna.state.getStor pair) (fun k => by rw [cStor pair pairNonEmpty]) repP
    have pairImage : some (devm.getCode pair).toList = pairSem.image := by
      rw [pairCode]
      rfl
    have factoryImage :
        some (devm.getCode st.factory).toList = UniswapV2Factory.factorySem.image := by
      rw [factoryCode]
      rfl
    have pfDistinct := pair_ne_factory pairCode factoryCode
    have runsOwn : ∀ {a : Adr} {sem : CodeSem}, some (devm.getCode a).toList = sem.image →
        csta.currentTarget = a → csta.code = devm.getCode a := by
      intro a sem image t
      have hc : c.toAdr = a := cTarget.symm.trans t
      rw [cCode (by rw [hc]; exact undelegated_of_image image), hc]
    have pairAt : pairSem.At pair 0 csta cdyna :=
      ⟨by rw [cGetCode]; exact pairImage, fun t => ⟨by rw [runsOwn pairImage t]; exact pairImage, rfl⟩⟩
    have admittedP : Exec.FrameAdmitted pair (pairEntry (WriterExtend K
        (pairRunKeys pair ⟨0, csta, cdyna, raw, child⟩))) child := by
      intro root member target
      have entry := LockExclusion.rawFrameRoots_entry child cFork member
      have freshOut : Exec.FreshEntry root.sevm root.devm ∧ root.devm.output = [] := by
        unfold Exec.rawFrameRoots at member
        rcases List.mem_cons.mp member with rfl | deeper
        · exact ⟨enteredCondition_fresh enter, enteredCondition_output enter⟩
        · exact ⟨Exec.rawFrameDescendants_entered enteredCondition_fresh child root deeper,
            Exec.rawFrameDescendants_entered (E := fun _ pre => pre.output = []) enteredCondition_output
              child root deeper⟩
      refine ⟨freshOut.1, freshOut.2, Exec.rawFrameRoots_data_bound child cData cFork root member,
        Exec.derivEntry_of_deriv entry.1 (pairGood_of_keys fun k hk => Or.inr ?_)⟩
      exact List.mem_flatMap.mpr ⟨root, member, by rw [ite_eq_left target]; exact hk⟩
    -- No committed non-static WETH9 frame of X's run is the Pair's
    have noOwnOf : ∀ committed : Execution.commits raw = true,
        ∀ f ∈ Exec.committedFrames child, f.sevm.currentTarget = ca →
          f.sevm.isStatic = false → f.sevm.caller ≠ pair := by
      intro committed
      have rootMem : Exec.Frame.ofRun child committed ∈ Exec.committedFrames child := by
        rw [Exec.committedFrames, dite_eq_left committed]
        exact List.mem_cons_self
      have quietCT := frame_factoryQuiet pairNonzero (Exec.Frame.ofRun child committed) rfl cFork
        (by show cdyna.getCode pair = _; rw [cGetCode]; exact pairCode)
        (by show cdyna.getCode st.factory = _; rw [cGetCode]; exact factoryCode)
        (fun t => (runsOwn pairImage t).trans pairCode)
        (fun t => (runsOwn factoryImage t).trans factoryCode)
        (fun _ hc => (pfDistinct (atPair.symm.trans (cCaller.symm.trans hc))).elim)
      have quiet : FactoryQuiet st.factory pair (Exec.committedFrames child) := by
        intro D member t ns hc
        have h : D.sevm.isStatic = true := quietCT D member t hc
        rw [ns] at h
        cases h
      have lockedC := run_lockedBelow repC.inj repC.apart child committed cFork pairAt admittedP
        childBound (fun _ h => h) repC locked quiet
      have childrenStatic : ∀ G ∈ Exec.committedFrames child, G.sevm.currentTarget = pair →
          ∀ c' ∈ Exec.childFrames G.run, c'.sevm.isStatic = true := by
        intro G member t c' hc'
        cases hs : G.sevm.isStatic
        · exact lockedC G member t hs c' hc'
        · exact Exec.childFrames_isStatic G.run hs c' hc'
      have framesOk : ∀ f ∈ Exec.committedFrames child,
          FrameOk ca (Key.extend U (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩)) f := by
        intro f member
        rw [Exec.committedFrames, dite_eq_left committed] at member
        rcases List.mem_cons.mp member with rfl | deeper
        · exact ⟨childPreWf, childAt, fun t => (childTargetNe t).elim, cFork⟩
        · exact weth9_framesOk ca injW _ _ _ _ child childAt child committed cFork childAt
            admittedW childPreWf (fun t => (childTargetNe t).elim) f deeper
      have wethChildren : ∀ G ∈ Exec.committedFrames child, G.sevm.currentTarget = ca →
          ∀ c' ∈ Exec.childFrames G.run, c'.sevm.caller = ca := by
        intro G member t c' hc'
        have ok := framesOk G member
        obtain ⟨image, pcZero⟩ := ok.at_.2 t
        have at₀ := ok.at_
        have fork' := ok.fork
        obtain ⟨pc', sevm', pre', out', run', committed'⟩ := G
        dsimp only at pcZero image at₀ fork' t hc' ⊢
        subst pcZero
        cases out' with
        | error e => simp only [Execution.commits, Bool.false_eq_true] at committed'
        | ok post =>
          rw [← t]
          exact Exec.childFrames_caller_of_callKinds (root := ⟨0, sevm', pre', .ok post, run'⟩)
            (fun chain instruction =>
              weth9_spawnKinds ca run' (weth9Sem.correct run' image) t fork' at₀ _ chain _
                instruction)
            run' (.refl _) c' hc'
      have fold := Exec.descendantFrames_callerTarget_of_children (p := pair) (ca := ca)
        (Q := fun s => s.isStatic = true) child
        (by
          intro which c' hc' _ _
          rcases which with atP | atW
          · exact childrenStatic _ rootMem atP c' hc'
          · exact (childTargetNe atW).elim)
        (by
          intro G member which c' hc' _ cl
          have member' : G ∈ Exec.committedFrames child := by
            rw [Exec.committedFrames, dite_eq_left committed]
            exact List.mem_cons_of_mem _ member
          rcases which with atP | atW
          · exact childrenStatic G member' atP c' hc'
          · exact absurd (cl.symm.trans (wethChildren G member' atW c' hc')) apart)
      intro f member t ns hc
      rw [Exec.committedFrames, dite_eq_left committed] at member
      rcases List.mem_cons.mp member with rfl | deeper
      · exact childTargetNe t
      · have h : f.sevm.isStatic = true := fold f deeper t hc
        rw [ns] at h
        cases h
    -- Transport across the crossing with the holder carrier
    obtain ⟨_, transport, -⟩ := (holderCarrier ca (Key.extend U
        (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩)) pair).xinstForeignSome_observed
      (ReplayObservation.trivial _) spawnEq frameRun resumeRun.symm targetNe fork (fun _ => protection)
      bound child (by
        intro committed
        refine ⟨[], ?_, ?_⟩
        · intro zeroC
          exact run_weth_holder injW child committed cFork childAt admittedW childBound childPreWf
            (fun t => (childTargetNe t).elim) (noOwnOf committed) zeroC
        · exact (List.flatMap_eq_nil_iff.mpr fun _ _ => rfl).symm)
    have zeroW : ∀ g, weth9Book.allow (ledger (Key.extend U
        (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩)) (devm.state.getStor ca)) pair g = 0 := by
      rw [ledger_extend foot freshW]
      exact zero
    obtain ⟨balLe, zeroD0⟩ := transport zeroW
    refine ⟨_, fun _ h => Or.inl h, code_eq_of_image preD0.code,
      footInv_of_pre targetNe injW footW.apart preD0, preD0.side, ?_, zeroD0⟩
    rw [← ledger_extend foot freshW]
    exact balLe

end Blanc.Composition.UniswapV2PairWeth9XLeg
