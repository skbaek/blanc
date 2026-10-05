import Blanc.Lift.UniswapV2Pair.SwapCallback
import Blanc.Lift.UniswapV2Pair.SwapFrontTyped
import Blanc.Lift.UniswapV2Pair.LockedSupply

/-! The swap front's three optional external calls as source turns. Each actual CALL step of
the same derivation is consumed by `mutable_call_turns` with the lock-free supply
`lockedPairSupply`: nested Pair frames run while the Pair is locked. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The transported invariant of the swap front between two external calls: the typed frame
keeps the context, its current state is the locked finite representation of the actual Pair
storage, the Pair code and the frame's output are unchanged, and the source logs extend
with the raw logs. -/
structure SwapFrontState (U : WriterKey → Prop) (pair : Adr) (ctx : Context)
    (current : Checkpoint) (b : Devm) (F : Frame) (w : Devm) : Prop where
  context : F.context = ctx
  rep : LockedRep U F.current.state (w.getStor pair)
  code : w.getCode pair = b.getCode pair
  output : w.output = b.output
  logs : ∃ (added : List PendingLog) (L : List Log), F.current.logs = current.logs ++ added ∧
    w.logs = b.logs ++ L ∧ added.map (PendingLog.rawWith (lockedOwnedRaw pair)) = L.map some

theorem SwapFrontState.beginResume {U : WriterKey → Prop} {pair : Adr} {ctx : Context}
    {current : Checkpoint} {b : Devm} {F : Frame} {w : Devm}
    (h : SwapFrontState U pair ctx current b F w) (request : Request) :
    SwapFrontState U pair ctx current b (F.beginResume request) w :=
  ⟨h.context, h.rep, h.code, h.output, h.logs⟩

/-- What every external call of the swap frame consumes: the lock-free supply under a
trace-local universe `U` and admission of every raw Pair frame of the derivation. -/
structure SwapCallEnv (U : WriterKey → Prop) (D : Exec.Deriv) (sevm : Sevm) (sem : CodeSem) :
    Prop where
  supply : PairFrameSupply sevm.currentTarget (LockedRep U) (LockedGood U) LockedAuth
    (lockedOwnedRaw sevm.currentTarget)
  image : sem.image = some code.toList
  fork : CoveredFork sevm.benvStat.fork
  good : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = sevm.currentTarget → LockedGood U F

/-- One actual mutable CALL step of the swap frame, consumed whole. -/
theorem swapMutableCall_step {U : WriterKey → Prop} {D : Exec.Deriv} {sevm : Sevm}
    {sem : CodeSem} {ctx : Context} {current : Checkpoint} {b : Devm} {F : Frame} {w pre d : Devm}
    {request : Request}
    (env : SwapCallEnv U D sevm sem)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (inv : SwapFrontState U sevm.currentTarget ctx current b F w)
    (pair : ctx.pair = sevm.currentTarget) (time : ctx.timestamp = sevm.benvStat.time)
    (nonstatic : ctx.isStatic = false) (kind : request.kind = .call)
    (call : StepIn D sevm pre (.exec .call) d)
    (preStor : pre.getStor sevm.currentTarget = w.getStor sevm.currentTarget)
    (preCode : pre.getCode sevm.currentTarget = w.getCode sevm.currentTarget)
    (preLogs : pre.logs = w.logs) (postOutput : d.output = w.output) :
    ∃ (turns : List MutableTurn) (c : Checkpoint) (rets : List ChildReturn),
      ExactTurns F request 0 (mutableTranscript turns .done)
        { complete := true, frame := { F with current := c }, childReturns := rets } ∧
      (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
        LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
      SwapFrontState U sevm.currentTarget ctx current b { F with current := c } d := by
  have repCongr : ∀ st (s s' : Stor), (∀ k, s'.get k = s.get k) →
      LockedRep U st s → LockedRep U st s' := fun _ _ _ same rep => LockedRep.congr same rep
  have nonemptyList : (b.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  obtain ⟨turns, c, added, rets, exact, auth, rep', logs', ⟨L, raw, images⟩, _⟩ :=
    mutable_call_turns (frame := F) (request := request) env.supply repCongr sem env.image call
      (Or.inl rfl) (by rw [inv.context, pair])
      (by unfold externalStatic; rw [inv.context, nonstatic, kind]; rfl)
      (by rw [preCode, inv.code]; exact installed) (by rw [preStor]; exact inv.rep)
      (by rw [inv.context, time]) env.fork env.good
  obtain ⟨added0, L0, logs0, raw0, images0⟩ := inv.logs
  refine ⟨turns, c, rets, exact, auth, ⟨inv.context, rep', ?_, postOutput.trans inv.output,
    added0 ++ added, L0 ++ L, ?_, ?_, ?_⟩⟩
  · rw [Lift.StepIn.codePreserve call sevm.currentTarget
      (by rw [preCode, inv.code]; exact nonemptyList), preCode, inv.code]
  · rw [logs', logs0, List.append_assoc]
  · rw [raw, preLogs, raw0, List.append_assoc]
  · rw [List.map_append, List.map_append, images0, images]

private theorem swap_pos_of_ne {a : B256} (h : a ≠ 0) : a > 0 := by
  apply B256.lt_of_toNat_lt_toNat
  have ne : a.toNat ≠ 0 := fun e => h (B256.toNat_inj _ _ (e.trans rfl))
  change 0 < a.toNat
  omega

/-- The optional transfer of `amount1Out`, as the typed `afterSwapTransfer0`. -/
theorem swapTransfer1_phase {U : WriterKey → Prop} {D : Exec.Deriv} {sevm : Sevm}
    {sem : CodeSem} {ctx : Context} {current : Checkpoint} {b : Devm} {F : Frame} {w w' : Devm}
    {L : List B256} {M M' : Mem} {p p' toWord token rho : B256} {locals : SwapLocals}
    (env : SwapCallEnv U D sevm sem)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (pair : ctx.pair = sevm.currentTarget) (time : ctx.timestamp = sevm.benvStat.time)
    (nonstatic : ctx.isStatic = false)
    (inv : SwapFrontState U sevm.currentTarget ctx current b F w)
    (opt : SwapTransferOpt D sevm w L M p locals.amount1Out toWord token rho w' M' p') :
    ∃ (F' : Frame) (T : Transcript → Transcript) (R : List ChildReturn) (turns : List MutableTurn),
      SwapFrontReaches (F.afterSwapTransfer0 locals) T R (F'.afterSwapTransfer1 locals) ∧
      SwapFrontState U sevm.currentTarget ctx current b F' w' ∧
      (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
        LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
      ((locals.amount1Out = 0 ∧ T = id) ∨ (locals.amount1Out ≠ 0 ∧
        T = fun tail => .next (swapTransferReply w'.returnData) (mutableTranscript turns .done) tail)) := by
  rcases opt with ⟨zero, rfl, rfl, rfl⟩ | ⟨nonzero, call, rfl, rfl⟩
  · have skip : F.afterSwapTransfer0 locals = F.afterSwapTransfer1 locals := by
      unfold Frame.afterSwapTransfer0
      rw [zero]
      simp only [show ¬ ((0 : B256) > 0) from by decide, ite_false]
    refine ⟨F, id, [], [], ?_, inv, (fun _ _ _ absent => by cases absent), Or.inl ⟨zero, rfl⟩⟩
    rw [skip]
    exact SwapFrontReaches.refl _
  · obtain ⟨⟨forwarded, callGas, step⟩, _, _, output, _, accepted⟩ := call
    let request := requestFor .swapTransfer1 locals.token1
      (.transfer locals.recipient locals.amount1Out)
    obtain ⟨turns, c, rets, exact, auth, state⟩ :=
      swapMutableCall_step (request := request) env installed inv pair time nonstatic rfl step
        rfl rfl rfl output
    have suspend : F.afterSwapTransfer0 locals = .suspended F request (.swapTransfer1 locals) := by
      unfold Frame.afterSwapTransfer0
      simp only [swap_pos_of_ne nonzero, ite_true]
      rfl
    refine ⟨({ F with current := c } : Frame).beginResume request, _, rets ++ [], turns, ?_,
      state.beginResume request, auth, Or.inr ⟨nonzero, rfl⟩⟩
    rw [suspend]
    refine SwapFrontReaches.call exact rfl rfl (fun absent => by cases absent) ?_
    rw [swap_resume_transfer1 accepted]
    exact SwapFrontReaches.refl _

/-- The optional transfer of `amount0Out`, as the first segment after the lock. -/
theorem swapTransfer0_phase {U : WriterKey → Prop} {D : Exec.Deriv} {sevm : Sevm}
    {sem : CodeSem} {ctx : Context} {current : Checkpoint} {b : Devm} {F : Frame} {w w' : Devm}
    {L : List B256} {M M' : Mem} {p p' toWord token rho : B256} {locals : SwapLocals}
    (env : SwapCallEnv U D sevm sem)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (pair : ctx.pair = sevm.currentTarget) (time : ctx.timestamp = sevm.benvStat.time)
    (nonstatic : ctx.isStatic = false)
    (inv : SwapFrontState U sevm.currentTarget ctx current b F w)
    (opt : SwapTransferOpt D sevm w L M p locals.amount0Out toWord token rho w' M' p') :
    ∃ (F' : Frame) (T : Transcript → Transcript) (R : List ChildReturn) (turns : List MutableTurn),
      SwapFrontReaches
        (if locals.amount0Out > 0 then
          F.suspend .swapTransfer0 locals.token0 (.transfer locals.recipient locals.amount0Out)
            (.swapTransfer0 locals)
        else F.afterSwapTransfer0 locals) T R (F'.afterSwapTransfer0 locals) ∧
      SwapFrontState U sevm.currentTarget ctx current b F' w' ∧
      (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
        LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
      ((locals.amount0Out = 0 ∧ T = id) ∨ (locals.amount0Out ≠ 0 ∧
        T = fun tail => .next (swapTransferReply w'.returnData) (mutableTranscript turns .done) tail)) := by
  rcases opt with ⟨zero, rfl, rfl, rfl⟩ | ⟨nonzero, call, rfl, rfl⟩
  · refine ⟨F, id, [], [], ?_, inv, (fun _ _ _ absent => by cases absent), Or.inl ⟨zero, rfl⟩⟩
    rw [zero]
    simp only [show ¬ ((0 : B256) > 0) from by decide, ite_false]
    exact SwapFrontReaches.refl _
  · obtain ⟨⟨forwarded, callGas, step⟩, _, _, output, _, accepted⟩ := call
    let request := requestFor .swapTransfer0 locals.token0
      (.transfer locals.recipient locals.amount0Out)
    obtain ⟨turns, c, rets, exact, auth, state⟩ :=
      swapMutableCall_step (request := request) env installed inv pair time nonstatic rfl step
        rfl rfl rfl output
    refine ⟨({ F with current := c } : Frame).beginResume request, _, rets ++ [], turns, ?_,
      state.beginResume request, auth, Or.inr ⟨nonzero, rfl⟩⟩
    simp only [swap_pos_of_ne nonzero, ite_true]
    refine SwapFrontReaches.call exact rfl rfl (fun absent => by cases absent) ?_
    rw [swap_resume_transfer0 accepted]
    exact SwapFrontReaches.refl _

private theorem swap_tAAB_getStor (base : Devm) (a x : Adr) :
    Devm.getStor (temporalAccountAccessBase base a) x = Devm.getStor base x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem swap_tAAB_getCode (base : Devm) (a x : Adr) :
    (temporalAccountAccessBase base a).getCode x = base.getCode x := by
  unfold temporalAccountAccessBase
  split <;> rfl

/-- The conditional callback, as the typed `afterSwapTransfer1`, up to the `balance0`
suspension. -/
theorem swapCallback_phase {U : WriterKey → Prop} {D : Exec.Deriv} {sevm : Sevm}
    {sem : CodeSem} {ctx : Context} {current : Checkpoint} {b : Devm} {F : Frame} {w w' : Devm}
    {L : List B256} {M M' : Mem} {q toWord a0 a1 len start : B256} {locals : SwapLocals}
    (env : SwapCallEnv U D sevm sem)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (pair : ctx.pair = sevm.currentTarget) (time : ctx.timestamp = sevm.benvStat.time)
    (nonstatic : ctx.isStatic = false)
    (inv : SwapFrontState U sevm.currentTarget ctx current b F w)
    (data : locals.data = sevm.data.sliceD start.toNat len.toNat 0)
    (opt : SwapCallbackOpt D sevm w L M q toWord a0 a1 len start w' M') :
    ∃ (F' : Frame) (T : Transcript → Transcript) (R : List ChildReturn) (turns : List MutableTurn),
      SwapFrontReaches (F.afterSwapTransfer1 locals) T R
        (.suspended F' (requestFor .swapBalance0 locals.token0 (.balanceOf ctx.pair))
          (.swapBalance0 locals)) ∧
      SwapFrontState U sevm.currentTarget ctx current b F' w' ∧
      (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
        LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
      ((len = 0 ∧ T = id) ∨ (len ≠ 0 ∧
        T = fun tail => .next (swapCallbackReply w'.returnData) (mutableTranscript turns .done) tail)) := by
  have dataLen : locals.data.length = len.toNat := by
    rw [data]
    exact List.length_sliceD _ _ _ _
  rcases opt with ⟨zero, rfl, rfl⟩ | ⟨nonzero, call, rfl⟩
  · have empty : ¬ locals.data.length > 0 := by
      rw [dataLen, zero]
      decide
    have skip : F.afterSwapTransfer1 locals =
        .suspended F (requestFor .swapBalance0 locals.token0 (.balanceOf ctx.pair))
          (.swapBalance0 locals) := by
      unfold Frame.afterSwapTransfer1
      simp only [empty, ite_false]
      rw [Frame.suspend, inv.context]
    refine ⟨F, id, [], [], ?_, inv, (fun _ _ _ absent => by cases absent), Or.inl ⟨zero, rfl⟩⟩
    rw [skip]
    exact SwapFrontReaches.refl _
  · unfold SwapCallbackCall at call
    obtain ⟨_, ⟨gas, callGas, step⟩, _, flag, flag0, post⟩ := call
    let request := requestFor .swapCallback locals.recipient
      (.callback F.context.sender locals.amount0Out locals.amount1Out locals.data)
    obtain ⟨turns, c, rets, exact, auth, state⟩ :=
      swapMutableCall_step (request := request) env installed inv pair time nonstatic rfl step
        (swap_tAAB_getStor _ _ _) (swap_tAAB_getCode _ _ _) (temporalAccountAccessBase_logs _ _)
        ((post.settled flag0).2.trans (temporalAccountAccessBase_output _ _))
    have present : locals.data.length > 0 := by
      rw [dataLen]
      have ne : len.toNat ≠ 0 := fun e => nonzero (B256.toNat_inj _ _ (e.trans rfl))
      omega
    have suspend : F.afterSwapTransfer1 locals = .suspended F request (.swapCallback locals) := by
      unfold Frame.afterSwapTransfer1
      simp only [present, ite_true]
      rfl
    have resume := swap_resume_callback (frame := ({ F with current := c } : Frame)) (locals := locals)
      (out := w'.returnData)
    refine ⟨({ F with current := c } : Frame).beginResume request, _, rets ++ [], turns, ?_,
      state.beginResume request, auth, Or.inr ⟨nonzero, rfl⟩⟩
    rw [suspend]
    refine SwapFrontReaches.call exact rfl rfl (fun absent => by cases absent) ?_
    change SwapFrontReaches (resumeSegment ({ F with current := c } : Frame)
      (requestFor .swapCallback locals.recipient (.callback ({ F with current := c } : Frame).context.sender
        locals.amount0Out locals.amount1Out locals.data)) (.swapCallback locals)
      (swapCallbackReply w'.returnData)) _ _ _
    rw [resume, Frame.suspend]
    change SwapFrontReaches (.suspended _ (requestFor .swapBalance0 locals.token0 (.balanceOf F.context.pair))
      (.swapBalance0 locals)) _ _ _
    rw [inv.context]
    exact SwapFrontReaches.refl _

end Blanc.Lift.UniswapV2Pair
