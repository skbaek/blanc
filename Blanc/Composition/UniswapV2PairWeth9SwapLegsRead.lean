import Blanc.Composition.UniswapV2PairWeth9SwapLegsCall
import Blanc.Lift.UniswapV2Pair.SwapForwardAccept

/-!
# The swap's post-callback WETH9 `balanceOf` STATICCALL, as a function of the call gas

The second post-callback balance query stages `balanceOf(pair)` at the free pointer and runs
`GAS; STATICCALL` against the (already warmed) token.  As for the transfer leg
(`UniswapV2PairWeth9SwapLegsCall`), everything the STATICCALL leaves except its gas is fixed by
the world, and `wethBalanceCall … cg` is the result at call gas `cg`, built as the static crossing
`Ninst.runCompiled_staticcall_child` builds it.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## The static crossing with a known child -/

/-- A `STATICCALL` to a non-precompile callee whose entered child halts cleanly resumes in
`callChildPost`.  The static sibling of `Ninst.runCompiled_call_zero_child`. -/
lemma Ninst.runCompiled_staticcall_child {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {cpost : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_stk : devm.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩)
        tw.toAdr) tw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost tw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_room : s.length < 1024)
    (h_exec : exec (initEvm (staticcallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs tw.toAdr dadr iiw.toNat isw.toNat code dp)) = .ok cpost)
    (h_error : cpost.error = none) :
    Ninst.RunCompiled sevm devm (.exec .staticcall)
      (callChildPost (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
        cpost oiw.toNat osw.toNat) := by
  let p := callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat
  let msg := staticcallSpawnMsg sevm p mcs tw.toAdr dadr iiw.toNat isw.toNat code dp
  have hbt : msg.benvAfterTransfer = .ok msg.benv :=
    Msg.benvAfterTransfer_of_value_zero rfl
  let child := initEvm (msg.withBenv msg.benv)
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  have hexec : exec child = .ok cpost := by
    simpa only [child, msg, p, staticcallSpawnMsg, callMsg, Msg.withBenv] using h_exec
  have hsettle : (Frame.ofCall msg).settle (exec child) = .ok cpost := by
    rw [hexec, Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
    simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, h_error,
      Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind]
  have hdi := accessDelegation_inv h_del
  have hpstack : p.stack.length < 1024 := by
    change d1.stack.length < 1024
    rw [hdi.1]
    exact h_room
  have hres : Resume.run (.call p oiw.toNat osw.toNat)
      ((Frame.ofCall msg).settle (exec child)) =
        .ok (callChildPost p cpost oiw.toNat osw.toNat) := by
    rw [hsettle, Resume.run_call_ok (by rw [h_error]; rfl) hpstack]
    rfl
  exact Ninst.runCompiled_exec_run
    (Xinst.step_staticcall_spawn hfork h_stk h_ext h_del h_acc h_split h_gas h_depth) henter hres

/-! ## The balance query at call gas `cg` -/

section Balance

variable (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256)

/-- The token as the query reads it. -/
def balTok : Adr := (swapTokenWord t).toAdr

/-- What stays on the stack under the six `STATICCALL` operands. -/
def balRest : List B256 := (p + 36) :: 0x70a08231 :: swapTokenWord t :: S

/-- The `STATICCALL` state at call gas `cg` (the record's staged state). -/
def balCallState (cg : Nat) : Devm :=
  St (temporalAccountAccessBase B (balTok t)) (cg.toB256 :: swapTokenWord t :: p :: 36 :: p :: 32 ::
    balRest S p t) (swapBalanceRequest M p sevm.currentTarget) cg

/-- The popped state (gas `g` left). -/
def balPopped (g : Nat) : Devm :=
  (temporalAccountAccessBase B (balTok t)).setMach ⟨balRest S p t,
    swapBalanceRequest M p sevm.currentTarget, g, (temporalAccountAccessBase B (balTok t)).stateGas⟩

/-- The popped state with the callee warmed. -/
def balWarm (g : Nat) : Devm := addAccessedAddress (balPopped sevm B S M p t g) (balTok t)

/-- The windows' expansion charge. -/
def balExt : Nat :=
  (balPopped sevm B S M p t 0).extCost [⟨p.toNat, (36 : B256).toNat⟩, ⟨p.toNat, (32 : B256).toNat⟩]

/-- The callee's access charge. -/
def balAcc : Nat := accessCost (balTok t) (temporalAccountAccessBase B (balTok t)).accessedAddresses + 0

/-- The call/forwarded gas pair at call gas `cg`. -/
def balSplit (cg : Nat) : Nat × Nat :=
  calculateMsgCallGas 0 cg cg (balExt sevm B S M p t) (balAcc B t)

/-- The parent the child returns to, charged `k` from gas `g`. -/
def balParent (g k : Nat) : Devm :=
  callSpawnParent (balWarm sevm B S M p t g) k p.toNat (36 : B256).toNat p.toNat (32 : B256).toNat

/-- The child message, forwarding `f`. -/
def balMsg (g k f : Nat) : Msg :=
  staticcallSpawnMsg sevm (balParent sevm B S M p t g k) f (balTok t) (balTok t) p.toNat
    (36 : B256).toNat (B.state.getCode (balTok t)) false

/-- WETH9's charge for the child's `balanceOf` frame. -/
def balUsed : Nat :=
  weth9BalanceGas (initSevm (balMsg sevm B S M p t 0 0 0)) (initDevm (balMsg sevm B S M p t 0 0 0))

/-- The resumed parent at popped gas `g`, charge `k`, forwarded `f`, child gas left `r`. -/
def wethBalanceCallAt (g k f r : Nat) : Devm :=
  callChildPost (balParent sevm B S M p t g k)
    (weth9BalancePost (initSevm (balMsg sevm B S M p t g k f)) (initDevm (balMsg sevm B S M p t g k f)) r)
    p.toNat (32 : B256).toNat

/-- **The swap's WETH9 `balanceOf` STATICCALL at call gas `cg`.** -/
def wethBalanceCall (cg : Nat) : Devm :=
  wethBalanceCallAt sevm B S M p t cg ((balSplit sevm B S M p t cg).1 + balExt sevm B S M p t)
    (balSplit sevm B S M p t cg).2 ((balSplit sevm B S M p t cg).2 - balUsed sevm B S M p t)

/-- The gas-free skeleton. -/
def wethBalanceSkel : Devm :=
  callChildPost (balParent sevm B S M p t 0 0)
    (weth9BalancePost (initSevm (balMsg sevm B S M p t 0 0 0)) (initDevm (balMsg sevm B S M p t 0 0 0)) 0)
    p.toNat (32 : B256).toNat

theorem balMsg_sevm (g k f : Nat) :
    initSevm (balMsg sevm B S M p t g k f) =
      { initSevm (balMsg sevm B S M p t 0 0 0) with gas := f } := rfl

theorem balMsg_devm (g k f : Nat) :
    initDevm (balMsg sevm B S M p t g k f) =
      St (initDevm (balMsg sevm B S M p t 0 0 0)) [] Mem.empty f := rfl

end Balance

section BalanceReframe

variable (s : Sevm) (f : Nat)

theorem weth9BalancePost_reframe (d : Devm) (f' r : Nat) :
    weth9BalancePost { s with gas := f } (St d [] Mem.empty f') r = weth9BalancePost s d r := by
  simp only [weth9BalancePost, wordTailPost, weth9BalanceAnswer, afterSload_gasField,
    dataWord_gasField, selector_gasField, St, afterSload_setMach, Devm.getStorVal_setMach,
    Devm.setMach_setMach, Devm.stateGas_setMach, afterSload_stateGas]

theorem weth9BalanceGas_reframe (d : Devm) (f' : Nat) :
    weth9BalanceGas { s with gas := f } (St d [] Mem.empty f') = weth9BalanceGas s d := by
  simp only [weth9BalanceGas, dataWord_gasField, St, Devm.setMach_accessedStorageKeys]
  rfl

theorem wordTailPost_gasLeft (b : Devm) (v r sel : B256) (μ : Mem) (g g' : Nat) :
    wordTailPost b v r sel μ g = (wordTailPost b v r sel μ g').withGasLeft g := rfl

end BalanceReframe

section BalanceSkel

variable (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256)

theorem weth9BalancePost_gasLeft' (s : Sevm) (d : Devm) (r r' : Nat) :
    weth9BalancePost s d r = (weth9BalancePost s d r').withGasLeft r :=
  wordTailPost_gasLeft _ _ _ _ _ r r'

theorem balParent_eq (g k : Nat) :
    balParent sevm B S M p t g k = (balParent sevm B S M p t 0 0).withGasLeft (g - k) := by
  unfold balParent balWarm balPopped
  rw [addAccessedAddress_setMach_gas _ _ _ g 0, callSpawnParent_withGasLeft _ g k 0]

theorem wethBalanceCallAt_eq (g k f r : Nat) :
    wethBalanceCallAt sevm B S M p t g k f r =
      (wethBalanceSkel sevm B S M p t).withGasLeft (g - k + r) := by
  unfold wethBalanceCallAt wethBalanceSkel
  rw [balMsg_sevm, balMsg_devm, weth9BalancePost_reframe, balParent_eq,
    weth9BalancePost_gasLeft' _ _ r 0, callChildPost_withGasLeft]

end BalanceSkel

section BalanceSpec

theorem callChildPost_stack (P c : Devm) (oi os : Nat) :
    (callChildPost P c oi os).stack = 1 :: P.stack := rfl

theorem callChildPost_gasLeft (P c : Devm) (oi os : Nat) :
    (callChildPost P c oi os).gasLeft = P.gasLeft + c.gasLeft := rfl

theorem temporalAccountAccessBase_state (B : Devm) (a : Adr) :
    (temporalAccountAccessBase B a).state = B.state := by
  unfold temporalAccountAccessBase
  split <;> rfl

/-- A one-word call's argument word. -/
theorem dataWord_oneWord {e : Sevm} {sel w : B256} (h : e.data = abiSelectorBytes sel ++ w.toBytes) :
    Sevm.dataWord e 4 = w ∧ e.data.length = 36 := by
  have l4 := abiSelectorBytes_length sel
  refine ⟨?_, ?_⟩
  · unfold Sevm.dataWord
    rw [h, show (4 : B256).toNat = 4 from rfl, List.sliceD,
      List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
      List.takeD_eq_take 0 (by simp only [B256.length_toBytes]; omega),
      List.take_of_length_le (by simp only [B256.length_toBytes]; omega), B256.toB256_toBytes]
  · rw [h]
    simp only [List.length_append, B256.length_toBytes, l4]

variable {sevm : Sevm} {B : Devm} {S : List B256} {M : Mem} {p t : B256}

theorem balCallState_pop (cg : Nat) :
    (balCallState sevm B S M p t cg).setMach
      ⟨balRest S p t, (balCallState sevm B S M p t cg).memory,
        (balCallState sevm B S M p t cg).gasLeft, (balCallState sevm B S M p t cg).stateGas⟩ =
      balPopped sevm B S M p t cg := by
  unfold balCallState balPopped
  exact St_setMach_pop _ _ _ _ _

theorem bal_accessDelegation (cg : Nat) (hcode : B.state.getCode (balTok t) = Weth9.code) :
    accessDelegation (addAccessedAddress (balPopped sevm B S M p t cg) (balTok t)) (balTok t) =
      ⟨false, balTok t, B.state.getCode (balTok t), 0, balWarm sevm B S M p t cg⟩ := by
  unfold accessDelegation balWarm balPopped
  rw [addAccessedAddress_setMach_state, temporalAccountAccessBase_state]
  dsimp only
  rw [hcode, Weth9.getDelegatedCodeAddress_code]

/-- The child message's calldata: `balanceOf(pair)`. -/
theorem balMsg_data (g k f : Nat) (wf : Mem.Wf M) (width : p.toNat + 260 < 2 ^ 256) :
    (balMsg sevm B S M p t g k f).data =
      abiSelectorBytes 0x70a08231 ++ sevm.currentTarget.toB256.toBytes := by
  have h := swapBalanceRequest_read (pair := sevm.currentTarget) wf width
  rw [mem_read_fst] at h
  have e : ExternalOperation.encode (.balanceOf sevm.currentTarget) =
      abiSelectorBytes 0x70a08231 ++ sevm.currentTarget.toB256.toBytes := by
    simp only [ExternalOperation.encode, encodeWords, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rfl
  rw [← e, ← h]
  unfold balMsg staticcallSpawnMsg
  change (balParent sevm B S M p t g k).memory.data.sliceD p.toNat (36 : B256).toNat 0 = _
  unfold balParent balWarm balPopped
  rw [callSpawnParent_memory_data, addAccessedAddress_setMach_memory,
    show (36 : B256).toNat = 36 from rfl]

/-- **The swap's WETH9 `balanceOf` STATICCALL at the call gas WETH9's charge fixes.**  WETH9's
code at the token, no precompile there, call depth left, a well-formed request memory, and room for
WETH9's view after the 63/64 rule: the STATICCALL resumes with the success flag, the pair's WETH9
balance word as the reply, and `cg` less the access charge, the expansion and WETH9's charge. -/
theorem wethBalanceCall_spec {cg : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hcode : B.state.getCode (balTok t) = Weth9.code) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp (balTok t) = false)
    (hroom : S.length < 1018) (wf : Mem.Wf M) (width : p.toNat + 260 < 2 ^ 256)
    (hgw : cg < 2 ^ 256)
    (hcharge : balAcc B t + balExt sevm B S M p t ≤ cg)
    (hfwd : balUsed sevm B S M p t ≤ except64th (cg - balExt sevm B S M p t - balAcc B t)) :
    Ninst.RunCompiled sevm (balCallState sevm B S M p t cg) (.exec .staticcall)
        (wethBalanceCall sevm B S M p t cg) ∧
      (wethBalanceCall sevm B S M p t cg).stack = 1 :: balRest S p t ∧
      (wethBalanceCall sevm B S M p t cg).returnData =
        (B.getStorVal (balTok t) (Weth9.balSlot sevm.currentTarget)).toBytes ∧
      (wethBalanceCall sevm B S M p t cg).gasLeft =
        cg - (balAcc B t + balExt sevm B S M p t + balUsed sevm B S M p t) := by
  generalize hext : balExt sevm B S M p t = ext at hcharge hfwd ⊢
  generalize hacc : balAcc B t = acc at hcharge hfwd ⊢
  generalize hused : balUsed sevm B S M p t = used at hfwd ⊢
  generalize hfw : except64th (cg - ext - acc) = fwd at hfwd
  have hfwle : fwd ≤ cg - ext - acc := by rw [← hfw]; unfold except64th; omega
  have hsplit : balSplit sevm B S M p t cg = ⟨fwd + acc, fwd⟩ := by
    unfold balSplit
    rw [hext, hacc]
    unfold calculateMsgCallGas
    simp only [show ¬ cg < acc + ext from by omega, ↓reduceIte, hfw]
    rw [Nat.min_eq_right (by omega), Nat.add_zero]
  -- the child
  have hdata := balMsg_data (sevm := sevm) (B := B) (S := S) (t := t) cg (fwd + acc + ext) fwd wf width
  obtain ⟨hw4, hlen⟩ := dataWord_oneWord (e := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
    hdata
  have hsel := selector_eq_of_data_eq_abiSelectorBytes_append
    (sevm := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) (selected := 0x70a08231)
    (by decide) hdata
  have hUsed : weth9BalanceGas (initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
      (initDevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) = used := by
    rw [← hused, balMsg_sevm, balMsg_devm, weth9BalanceGas_reframe]
    rfl
  have hrun := weth9_balanceOf_runExact_post
    (sevm := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
    (pre := initDevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) (G := fwd - used)
    hfork rfl hsel (by omega) (by omega) rfl rfl
    (by
      rw [hUsed]
      change fwd = fwd - used + used
      omega)
  have hexec := (exec_iff_exec_eq 0 _ _ _).mp (Weth9.exec_of_runExact
    (sevm := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) hcode hfork hrun)
  have hcross := Ninst.runCompiled_staticcall_child
    (devm := balCallState sevm B S M p t cg) (gw := cg.toB256) (tw := swapTokenWord t)
    (iiw := p) (isw := 36) (oiw := p) (osw := 32) (s := balRest S p t) (dp := false)
    (dadr := balTok t) (code := B.state.getCode (balTok t)) (dgc := 0)
    (d1 := balWarm sevm B S M p t cg) (ext := ext) (acc := acc) (mcc := fwd + acc) (mcs := fwd)
    (cpost := weth9BalancePost (initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
      (initDevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) (fwd - used))
    hfork rfl ?ext ?del ?acc ?split ?gas hdepth hprec ?room hexec
    (by rw [weth9BalancePost_error]; rfl)
  case ext =>
    rw [← hext, balCallState_pop]
    exact setMach_extCost _ _ _ _ _ _ _
  case del =>
    rw [balCallState_pop]
    exact bal_accessDelegation cg hcode
  case acc => rw [← hacc]; rfl
  case split =>
    unfold balWarm balPopped
    rw [B256.toNat_toB256_of_lt hgw, addAccessedAddress_setMach_gasLeft, ← hsplit]
    unfold balSplit
    rw [hext, hacc]
  case gas =>
    unfold balWarm balPopped
    rw [addAccessedAddress_setMach_gasLeft]
    change fwd + acc + ext ≤ cg
    omega
  case room =>
    simp only [balRest, List.length_cons]
    omega
  have hd : wethBalanceCall sevm B S M p t cg =
      callChildPost (callSpawnParent (balWarm sevm B S M p t cg) (fwd + acc + ext) p.toNat
        (36 : B256).toNat p.toNat (32 : B256).toNat)
        (weth9BalancePost (initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
          (initDevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) (fwd - used))
        p.toNat (32 : B256).toNat := by
    unfold wethBalanceCall wethBalanceCallAt
    rw [hsplit, hext, hused]
    rfl
  rw [hd]
  refine ⟨hcross, ?_, ?_, ?_⟩
  · rw [callChildPost_stack, callSpawnParent_stack]
    unfold balWarm balPopped
    rw [addAccessedAddress_setMach_stack]
  · rw [callChildPost_returnData, weth9BalancePost_output]
    unfold weth9BalanceAnswer
    rw [hw4, toAdr_toB256]
    unfold Devm.getStorVal Devm.getAcct
    change (((balParent sevm B S M p t cg (fwd + acc + ext)).state.get (balTok t)).stor.get
      (Weth9.balSlot sevm.currentTarget)).toBytes = _
    unfold balParent balWarm balPopped
    rw [callSpawnParent_state, addAccessedAddress_setMach_state, temporalAccountAccessBase_state]
  · rw [callChildPost_gasLeft, callSpawnParent_gasLeft, weth9BalancePost_gasLeft]
    unfold balWarm balPopped
    rw [addAccessedAddress_setMach_gasLeft]
    change cg - (fwd + acc + ext) + (fwd - used) = cg - (acc + ext + used)
    omega

end BalanceSpec

end Blanc.Composition.UniswapV2PairWeth9Joint
