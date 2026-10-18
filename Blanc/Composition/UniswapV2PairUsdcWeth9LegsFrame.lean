import Blanc.Composition.UniswapV2PairUsdcWeth9LegsImpl
import Blanc.Composition.UniswapV2PairUsdcWeth9LegsProxy
import Blanc.Lift.Usdc.Impl.Jumps
import Blanc.Lift.Usdc.Proxy.Jumps
import Blanc.Lift.Usdc.Proxy.Check
import Blanc.Lift.Usdc.HistorySlotsCore

/-!
# The USDC `transfer` frame through the proxy, gas-exact (U9a)

The proxy frame's prefix walk (`proxyPreW`), its `DELEGATECALL` (`dlg_step`) into the
implementation's `transfer` frame (`implXferW`, made an execution by `lift_exact`), and the
delegate tail (`dTailW`), composed into one execution of the proxy's code with an exact charge.
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc

theorem dMsg_sevm (sevm : Sevm) (b : Devm) (Y : Nat) :
    initSevm (dMsg sevm b Y) = { initSevm (dMsg sevm b 0) with gas := dFwd sevm b Y } := rfl

theorem dMsg_devm (sevm : Sevm) (b : Devm) (Y : Nat) :
    initDevm (dMsg sevm b Y) = St (initDevm (dMsg sevm b 0)) [] Mem.empty (dFwd sevm b Y) := rfl

/-- The implementation `transfer` charge at the proxy's child (gas-free). -/
noncomputable abbrev childXferCost (sevm : Sevm) (b : Devm) : Nat :=
  (implXferW (initSevm (dMsg sevm b 0)) (initDevm (dMsg sevm b 0))).1

/-- **The child `transfer` frame runs to its `RETURN`** with `dFwd Y - childXferCost` gas left. -/
theorem child_xfer_exec {sevm : Sevm} {b : Devm} {Y : Nat} (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = false)
    (hcode : (pBase sevm b).state.getCode (dI sevm b) = Impl.code)
    (facts : XferFacts (initSevm (dMsg sevm b Y)) (initDevm (dMsg sevm b 0)))
    (hfwd : childXferCost sevm b + 415 ≤ dFwd sevm b Y) :
    exec (initEvm (dMsg sevm b Y)) = .ok (implXferPost (initSevm (dMsg sevm b Y))
      (initDevm (dMsg sevm b 0)) (dFwd sevm b Y - childXferCost sevm b)) := by
  have hc : (implXferW (initSevm (dMsg sevm b Y)) (initDevm (dMsg sevm b 0))).1 =
      childXferCost sevm b := by
    rw [dMsg_sevm, implXferW_gas]
  have fork' : CoveredFork (initSevm (dMsg sevm b Y)).benvStat.fork := fork
  have static' : (initSevm (dMsg sevm b Y)).isStatic = false := by
    show (false || sevm.isStatic) = false
    rw [static]; rfl
  have run := (implXferW (initSevm (dMsg sevm b Y)) (initDevm (dMsg sevm b 0))).2 fork' static' facts
    (dFwd sevm b Y - childXferCost sevm b) (by omega)
  rw [hc, Nat.sub_add_cancel (by omega), ← dMsg_devm] at run
  have hex := lift_exact Impl.cert_check Impl.jumps_ok hcode fork' ⟨_, rfl, run⟩
  exact (exec_iff_exec_eq _ _ _ _).mp hex

/-- The delegate tail's charge reads the base only through the memory image. -/
theorem dTailW_base (sevm : Sevm) (D D' : Devm) (R : List B256) (M : Mem) (w : B256) :
    (dTailW sevm D R M w).1 = (dTailW sevm D' R M w).1 := by
  unfold dTailW
  simp only [St.extCost_eq (M := M) rfl]

theorem implXferPost_gasLeft (s : Sevm) (b : Devm) (G : Nat) : (implXferPost s b G).gasLeft = G := rfl

theorem implXferPost_output (s : Sevm) (b : Devm) (G : Nat) :
    (implXferPost s b G).output = (Nat.toB256 1).toBytes := by
  show (B256.eqCheck (B256.eqCheck (Bytes.toB256 [1]) 0) 0).toBytes = _
  decide

theorem memRead_withOutput_error (d : Devm) (i n : Nat) (o : Bytes) :
    ((d.memRead i n).2.withOutput o).error = d.error := rfl

theorem addLog_error (d : Devm) (l : Log) : (d.addLog l).error = d.error := rfl

theorem implXferPost_error (s : Sevm) (b : Devm) (G : Nat) : (implXferPost s b G).error = b.error := by
  unfold implXferPost
  rw [memRead_withOutput_error, St_error]
  unfold e93Post e93Debited e37Pre
  rw [addLog_error, afterSstore_error, afterSload_error, afterSload_error, afterSstore_error,
    afterSload_error, afterSload_error, afterSload_error, afterSload_error, afterSload_error,
    afterSload_error]

theorem ceil32_mod (n : Nat) : ceil32 n % 32 = 0 := by
  unfold ceil32; split <;> omega

theorem pMem_size (sevm : Sevm) : (pMem sevm).size % 32 = 0 ∧ 96 ≤ (pMem sevm).size := by
  have h96 : (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes).size = 96 := by
    rw [Mem.size_write_word_at]; rfl
  unfold pMem
  rcases hbs : sevm.data.sliceD (Bytes.toB256 [0]).toNat (Nat.toB256 sevm.data.length).toNat 0 with
    _ | ⟨x, xs⟩
  · have h0 : (Bytes.toB256 [0]).toNat = 0 := rfl
    rw [Mem.size_write_of_le (by rw [h96, h0, List.length_nil]; omega), h96]
    omega
  · rw [Mem.size_write_cons, h96]
    split
    · omega
    · have := Blanc.Lift.Witness.ceil32_ge ((Bytes.toB256 [0]).toNat + (x :: xs).length)
      exact ⟨ceil32_mod _, by omega⟩

theorem dParent_memory (sevm : Sevm) (b : Devm) (Y : Nat) :
    (dParent sevm b Y).memory = (pMem sevm).extends [⟨(Bytes.toB256 [0]).toNat,
      (Nat.toB256 sevm.data.length).toNat⟩, ⟨(Bytes.toB256 [0]).toNat, (Bytes.toB256 [0]).toNat⟩] := rfl

theorem dParent_size (sevm : Sevm) (b : Devm) (Y : Nat) :
    (dParent sevm b Y).memory.size % 32 = 0 ∧ 32 ≤ (dParent sevm b Y).memory.size := by
  rw [dParent_memory]
  obtain ⟨h32, h96⟩ := pMem_size sevm
  show memExtsSize (pMem sevm).size _ % 32 = 0 ∧ 32 ≤ memExtsSize (pMem sevm).size _
  have hge := Blanc.Lift.memExtsSize_ge (pMem sevm).size [⟨(Bytes.toB256 [0]).toNat,
      (Nat.toB256 sevm.data.length).toNat⟩, ⟨(Bytes.toB256 [0]).toNat, (Bytes.toB256 [0]).toNat⟩]
  refine ⟨?_, by omega⟩
  simp only [memExtsSize]
  exact memExtSize_mod_32 (memExtSize_mod_32 h32)

/-- The child's calldata is the proxy frame's. -/
theorem dMsg_data (sevm : Sevm) (b : Devm) (Y : Nat) (hlen : sevm.data.length < 2 ^ 256) :
    (initSevm (dMsg sevm b Y)).data = sevm.data := by
  show (dParent sevm b Y).memory.data.sliceD (Bytes.toB256 [0]).toNat
    (Nat.toB256 sevm.data.length).toNat 0 = sevm.data
  rw [dParent_memory]
  show (pMem sevm).data.sliceD _ _ 0 = _
  have key := Blanc.Lift.Usdc.Proxy.Mem.read_write_zero' (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes)
    (sevm.data.sliceD 0 (Nat.toB256 sevm.data.length).toNat 0)
  rw [List.length_sliceD, B256.toNat_toB256_of_lt hlen, Bytes.sliceD_zero_length rfl] at key
  unfold pMem
  have h0 : (Bytes.toB256 [0]).toNat = 0 := rfl
  rw [h0, B256.toNat_toB256_of_lt hlen, Bytes.sliceD_zero_length rfl]
  exact key

/-- `XferFacts` reads the message only through its value, calldata, caller and target, and the base
only through the storage. -/
theorem XferFacts.transport {s s' : Sevm} {b b' : Devm} (f : XferFacts s b) (hv : s'.value = s.value)
    (hd : s'.data = s.data) (hc : s'.caller = s.caller) (ht : s'.currentTarget = s.currentTarget)
    (hs : ∀ a, Devm.getStor b' a = Devm.getStor b a) : XferFacts s' b' := by
  have hdw : Sevm.dataWord s' = Sevm.dataWord s := by
    funext i; unfold Sevm.dataWord; rw [hd]
  have hgv : ∀ a k, b'.getStorVal a k = b.getStorVal a k := fun a k => by
    rw [gsv, gsv, hs]
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := f
  have hkC : kC s' = kC s := by unfold kC; rw [hc]
  have hxT : xTo s' = xTo s := by unfold xTo; rw [hdw]
  have hxV : xVal s' = xVal s := by unfold xVal; rw [hdw]
  refine ⟨by rw [hv]; exact f1, by rw [hd]; exact f2, by rw [hd]; exact f3, by rw [hdw]; exact f4,
    by rw [hgv, ht]; exact f5, by rw [hgv, ht, hkC]; exact f6, by rw [hgv, ht, hxT]; exact f7,
    by rw [hc]; exact f8, by rw [hxT]; exact f9, by rw [hgv, ht, hkC, hxV]; exact f10, ?_, ?_⟩
  · rw [hgv, ht, hkC, hxV, hxT, hs]; exact f11
  · rw [hgv, ht, hkC, hxV, hxT, hs]; exact f12

/-! ## The proxy frame of `transfer` -/

section Frame

variable (sevm : Sevm) (pre : Devm)

/-- The word the implementation's `transfer` returns. -/
abbrev xferWord : B256 := B256.eqCheck (B256.eqCheck (Bytes.toB256 [1]) 0) 0

/-- The delegate tail's charge (it reads only the parent's memory image). -/
noncomputable abbrev frameTail : Nat :=
  (dTailW sevm (dParent sevm pre 0) (pRest sevm pre) (dParent sevm pre 0).memory xferWord).1

/-- The gas at `_delegate`'s `DELEGATECALL` when `X` is left at the end. -/
noncomputable abbrev frameY (X : Nat) : Nat :=
  X + frameTail sevm pre + dAcc sevm pre + dExt sevm pre + childXferCost sevm pre

/-- **The exact charge of a USDC `transfer` frame through the proxy.** -/
noncomputable def proxyXferCost : Nat :=
  (proxyPreW sevm pre 0xa9059cbb).1 +
    (frameTail sevm pre + dAcc sevm pre + dExt sevm pre + childXferCost sevm pre)

/-- The child's halting state in the frame with `X` left at the end. -/
noncomputable abbrev frameChild (X : Nat) : Devm :=
  implXferPost (initSevm (dMsg sevm pre (frameY sevm pre X))) (initDevm (dMsg sevm pre 0))
    (dFwd sevm pre (frameY sevm pre X) - childXferCost sevm pre)

/-- The delegate tail's charge for a returned word `w`. -/
noncomputable abbrev tailW (w : B256) : Nat :=
  (dTailW sevm (dParent sevm pre 0) (pRest sevm pre) (dParent sevm pre 0).memory w).1

/-- The proxy frame's halting state: the child `C` resumed at `DELEGATECALL` gas `Y`, its word `w`
returned, `X` left. -/
noncomputable def proxyPost (Y X : Nat) (C : Devm) (w : B256) : Devm :=
  ((St (callChildPost (dParent sevm pre Y) C (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat)
      (1 :: 1 :: pRest sevm pre) (dRetMem (dParent sevm pre Y).memory w) X).memRead
    (Bytes.toB256 [0]).toNat (Nat.toB256 w.toBytes.length).toNat).2.withOutput w.toBytes

/-- The proxy frame of `transfer`'s halting state with `X` left. -/
noncomputable abbrev proxyXferPost (X : Nat) : Devm :=
  proxyPost sevm pre (frameY sevm pre X) X (frameChild sevm pre X) xferWord

end Frame

theorem proxyPost_gasLeft (sevm : Sevm) (pre : Devm) (Y X : Nat) (C : Devm) (w : B256) :
    (proxyPost sevm pre Y X C w).gasLeft = X := by
  unfold proxyPost; rw [Devm.withOutput_gasLeft, Devm.memRead_snd_gasLeft]; rfl

theorem proxyPost_output (sevm : Sevm) (pre : Devm) (Y X : Nat) (C : Devm) (w : B256) :
    (proxyPost sevm pre Y X C w).output = w.toBytes := by
  unfold proxyPost; rw [Devm.withOutput_output]

theorem proxyPost_state (sevm : Sevm) (pre : Devm) (Y X : Nat) (C : Devm) (w : B256) :
    (proxyPost sevm pre Y X C w).state = C.state := by
  unfold proxyPost
  rw [Devm.withOutput_state, Devm.memRead_state]
  exact (callChildPost_facts_zero (dParent sevm pre Y) C (Bytes.toB256 [0]).toNat
    (Bytes.toB256 [0]).toNat rfl).2.2.2.1

/-- **The USDC proxy frame, gas-exact, for any implementation child**: under the proxy's branch
facts for selector `s`, the implementation's code behind the slot, gas below `2 ^ 256` at the
`DELEGATECALL`, and a clean child run `C` that charges `cc` of what it is forwarded and returns the
word `w`, the proxy's code runs to `RETURN` with exactly `X` left and returns `w`. -/
theorem proxy_frame_run {sevm : Sevm} {pre C : Devm} {X cc : Nat} {s w : B256}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (pf : ProxyFacts sevm pre s)
    (hcode : (pBase sevm pre).state.getCode (dI sevm pre) = Impl.code)
    (hprec : sevm.benvStat.rules.isPrecomp (dI sevm pre) = false)
    (hY : X + tailW sevm pre w + dAcc sevm pre + dExt sevm pre + cc < 2 ^ 256)
    (hcc : cc ≤ dFwd sevm pre (X + tailW sevm pre w + dAcc sevm pre + dExt sevm pre + cc))
    (hexec : exec (initEvm (dMsg sevm pre (X + tailW sevm pre w + dAcc sevm pre + dExt sevm pre + cc))) =
      .ok C)
    (herr : C.error = none) (hout : C.output = w.toBytes)
    (hgasC : C.gasLeft = dFwd sevm pre (X + tailW sevm pre w + dAcc sevm pre + dExt sevm pre + cc) - cc) :
    SFunc.RunExact Proxy.cert.prog sevm
      (St pre [] Mem.empty (X + ((proxyPreW sevm pre s).1 +
        (tailW sevm pre w + dAcc sevm pre + dExt sevm pre + cc))))
      Proxy.t_0000_c0
      (.halted (proxyPost sevm pre (X + tailW sevm pre w + dAcc sevm pre + dExt sevm pre + cc) X C w)) := by
  generalize hYd : X + tailW sevm pre w + dAcc sevm pre + dExt sevm pre + cc = Y at hY hcc hexec hgasC ⊢
  have step := dlg_step fork depth hY (by omega)
    (by rw [hcode]; exact Blanc.Lift.Usdc.impl_undelegated) hprec hexec herr
  obtain ⟨hstk, hmem, hgas, -, -⟩ := callChildPost_facts_zero (dParent sevm pre Y)
    C (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat rfl
  have hle : dFwd sevm pre Y ≤ Y - dExt sevm pre - dAcc sevm pre := by
    simp only [dFwd, except64th]; omega
  have hgas' : (callChildPost (dParent sevm pre Y) C
      (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat).gasLeft = X + tailW sevm pre w := by
    rw [hgas, UniswapV2PairWeth9Joint.callSpawnParent_gasLeft, hgasC]
    show Y - _ + _ = _
    omega
  have hD := St.self hstk hmem
  rw [hgas', UniswapV2PairWeth9Joint.callSpawnParent_stack] at hD
  have tail := (dTailW sevm (callChildPost (dParent sevm pre Y) C
      (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat) (pRest sevm pre)
      (dParent sevm pre Y).memory w).2
    (by rw [UniswapV2PairWeth9Joint.callChildPost_returnData, hout])
    (dParent_size sevm pre _).1 (dParent_size sevm pre _).2
    (by simp only [pRest, List.length_cons, List.length_nil]; omega) X
  rw [dTailW_base sevm _ (dParent sevm pre 0)] at tail
  have hD' : callChildPost (dParent sevm pre Y) C
      (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat =
      St (callChildPost (dParent sevm pre Y) C
        (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat) (1 :: pRest sevm pre)
        (dParent sevm pre Y).memory
        (X + (dTailW sevm (dParent sevm pre 0) (pRest sevm pre)
          (dParent sevm pre Y).memory w).1) := hD
  rw [← hD'] at tail
  have h := (proxyPreW sevm pre s).2 fork pf Y _ (SFunc.RunExact.next step tail)
  rw [show Y + (proxyPreW sevm pre s).1 = X + ((proxyPreW sevm pre s).1 +
    (tailW sevm pre w + dAcc sevm pre + dExt sevm pre + cc)) by omega] at h
  exact h

/-- **The USDC proxy frame of `transfer`, gas-exact**: under the proxy's and the implementation's
branch facts, the implementation's code behind the slot, gas enough for the child under the 63/64
rule, and gas below `2 ^ 256` at the `DELEGATECALL`, the proxy's code runs to `RETURN` with exactly
`X` left, returns the word `1`, and ends in the child's world. -/
theorem proxy_xfer_run {sevm : Sevm} {pre : Devm} {X : Nat} (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = false) (depth : sevm.depth ≠ 0) (hlen : sevm.data.length < 2 ^ 256)
    (pf : ProxyFacts sevm pre 0xa9059cbb) (xf : XferFacts sevm pre)
    (hcode : (pBase sevm pre).state.getCode (dI sevm pre) = Impl.code)
    (hprec : sevm.benvStat.rules.isPrecomp (dI sevm pre) = false)
    (hfwd : childXferCost sevm pre + 415 ≤ dFwd sevm pre (frameY sevm pre X))
    (hY : frameY sevm pre X < 2 ^ 256) :
    SFunc.RunExact Proxy.cert.prog sevm (St pre [] Mem.empty (X + proxyXferCost sevm pre))
      Proxy.t_0000_c0 (.halted (proxyXferPost sevm pre X)) := by
  have hexec := child_xfer_exec (sevm := sevm) (b := pre) (Y := frameY sevm pre X) fork static hcode
    (xf.transport rfl (dMsg_data sevm pre _ hlen) rfl rfl (fun a => by
      show Devm.getStor (pBase sevm pre) a = _
      rw [Blanc.afterSload_getStor, Blanc.afterSload_getStor])) hfwd
  have herr : (frameChild sevm pre X).error = none := by
    rw [implXferPost_error]; rfl
  exact proxy_frame_run fork depth pf hcode hprec hY (Nat.le_trans (Nat.le_add_right _ _) hfwd) hexec herr
    (by rw [implXferPost_output]; rfl) (implXferPost_gasLeft _ _ _)

end Blanc.Composition.UsdcLive
