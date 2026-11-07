import Blanc.Lift.Usdc.TransferLiveFrame
import Blanc.Lift.CoinFrame
import Blanc.Lift.InvWalkLegacy

/-!
# A USDC proxy frame lands where its implementation child lands

`proxy_lands`: under the proxy's fallback facts, a clean implementation child run with reply `w` and
ledger `σ'` makes the proxy frame's `FrameLands`, whichever implementation is behind the slot. The
charge is the proxy's own plus the child's, at the frame's actual gas, so no charge need be free of
the message's gas field. `proxyFacts_of_sel` gives the fallback facts from the selector and the caller.
-/

namespace Blanc.Composition.UsdcLive

open Blanc.Lift.AccumulatedWalk
open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc

local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- `proxy_frame_run` for any undelegated code behind the slot. -/
theorem proxy_frame_any {sevm : Sevm} {pre C : Devm} {X cc : Nat} {s w : B256}
    (fork : ShanghaiOnwards sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (pf : ProxyFacts sevm pre s)
    (hundel : getDelegatedCodeAddress ((pBase sevm pre).state.getCode (dI sevm pre)) = none)
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
  have step := dlg_step fork depth hY (by omega) hundel hprec hexec herr
  obtain ⟨hstk, hmem, hgas, -, -⟩ := callChildPost_facts_zero (dParent sevm pre Y)
    C (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat rfl
  have hle : dFwd sevm pre Y ≤ Y - dExt sevm pre - dAcc sevm pre := by
    simp only [dFwd, except64th]; omega
  have hgas' : (callChildPost (dParent sevm pre Y) C
      (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat).gasLeft = X + tailW sevm pre w := by
    rw [hgas, Blanc.callSpawnParent_gasLeft, hgasC]
    show Y - _ + _ = _
    omega
  have hD := St.self hstk hmem
  rw [hgas', Blanc.callSpawnParent_stack] at hD
  have tail := (dTailW sevm (callChildPost (dParent sevm pre Y) C
      (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat) (pRest sevm pre)
      (dParent sevm pre Y).memory w).2
    (by rw [Blanc.Lift.callChildPost_returnData, hout])
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

/-- The gas at `_delegate`'s `DELEGATECALL` in a frame with the entry's gas. -/
noncomputable abbrev frameYAt (sevm : Sevm) (pre : Devm) (s : B256) : Nat :=
  pre.gasLeft - (proxyPreW sevm pre s).1

theorem proxyPost_getCode (sevm : Sevm) (pre : Devm) (Y X : Nat) (C : Devm) (w : B256) (a : Adr) :
    (proxyPost sevm pre Y X C w).getCode a = C.getCode a :=
  congrArg (fun st => State.getCode st a) (proxyPost_state sevm pre Y X C w)

theorem proxyPost_getStor (sevm : Sevm) (pre : Devm) (Y X : Nat) (C : Devm) (w : B256) (a : Adr) :
    Devm.getStor (proxyPost sevm pre Y X C w) a = Devm.getStor C a :=
  congrArg (fun st => State.getStor st a) (proxyPost_state sevm pre Y X C w)

theorem dMsg_getCode (sevm : Sevm) (b : Devm) (Y : Nat) (a : Adr) :
    (initDevm (dMsg sevm b Y)).getCode a = b.getCode a := by
  show (pBase sevm b).getCode a = _
  rw [afterSload_getCode, afterSload_getCode]

theorem dMsg_getStor (sevm : Sevm) (b : Devm) (Y : Nat) (a : Adr) :
    Devm.getStor (initDevm (dMsg sevm b Y)) a = Devm.getStor b a := by
  show Devm.getStor (pBase sevm b) a = _
  rw [afterSload_getStor, afterSload_getStor]

theorem dMsg_created (sevm : Sevm) (b : Devm) (Y : Nat) :
    (initDevm (dMsg sevm b Y)).createdAccounts = b.createdAccounts := by
  show (pBase sevm b).createdAccounts = _
  rw [afterSload_createdAccounts, afterSload_createdAccounts]

theorem afterSload2_error (sevm : Sevm) (b : Devm) :
    (pBase sevm b).error = b.error := by
  rw [afterSload_error, afterSload_error]

theorem proxyPost_error (sevm : Sevm) (pre : Devm) (Y X : Nat) (C : Devm) (w : B256) :
    (proxyPost sevm pre Y X C w).error = (pBase sevm pre).error := rfl

theorem proxyPost_created (sevm : Sevm) (pre : Devm) (Y X : Nat) (C : Devm) (w : B256) :
    (proxyPost sevm pre Y X C w).createdAccounts = C.createdAccounts := rfl

theorem proxyPost_refund (sevm : Sevm) (pre : Devm) (Y X : Nat) (C : Devm) (w : B256) :
    (proxyPost sevm pre Y X C w).refundCounter = pre.refundCounter + C.refundCounter := by
  have e : (proxyPost sevm pre Y X C w).refundCounter = (pBase sevm pre).refundCounter + C.refundCounter := rfl
  rw [e, afterSload_refundCounter, afterSload_refundCounter]

/-- **A proxy frame lands where its implementation child lands.** -/
theorem proxy_lands {sevm : Sevm} {pre C : Devm} {u : Nat} {s w : B256} {σ' : Stor} {R : Prop}
    (fork : ShanghaiOnwards sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (pf : ProxyFacts sevm pre s)
    (hundel : getDelegatedCodeAddress ((pBase sevm pre).state.getCode (dI sevm pre)) = none)
    (hprec : sevm.benvStat.rules.isPrecomp (dI sevm pre) = false)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hG : pre.gasLeft < 2 ^ 256)
    (hc : (proxyPreW sevm pre s).1 + (tailW sevm pre w + dAcc sevm pre + dExt sevm pre + u) ≤ pre.gasLeft)
    (hu : u ≤ dFwd sevm pre (frameYAt sevm pre s))
    (hexec : exec (initEvm (dMsg sevm pre (frameYAt sevm pre s))) = .ok C)
    (herr : C.error = none) (hout : C.output = w.toBytes)
    (hgasC : C.gasLeft = dFwd sevm pre (frameYAt sevm pre s) - u)
    (hk : Keeps (initSevm (dMsg sevm pre (frameYAt sevm pre s)))
      (initDevm (dMsg sevm pre (frameYAt sevm pre s))) C)
    (hst : Devm.getStor C sevm.currentTarget = σ') (hr : R → 0 ≤ C.refundCounter) :
    ∃ post, FrameLands Proxy.cert.prog sevm pre post
      ((proxyPreW sevm pre s).1 + (tailW sevm pre w + dAcc sevm pre + dExt sevm pre + u)) w σ' R := by
  have hYeq : pre.gasLeft - ((proxyPreW sevm pre s).1 +
      (tailW sevm pre w + dAcc sevm pre + dExt sevm pre + u)) + tailW sevm pre w + dAcc sevm pre +
        dExt sevm pre + u = frameYAt sevm pre s := by
    unfold frameYAt
    omega
  generalize hXd : pre.gasLeft - ((proxyPreW sevm pre s).1 +
      (tailW sevm pre w + dAcc sevm pre + dExt sevm pre + u)) = X at hYeq
  have run := proxy_frame_any (X := X) (cc := u) fork depth pf hundel hprec
    (by rw [hYeq]; unfold frameYAt; omega) (by rw [hYeq]; exact hu) (by rw [hYeq]; exact hexec) herr hout
    (by rw [hYeq]; exact hgasC)
  rw [pre_eq_St hs hm (by omega)] at run
  rw [hYeq] at run
  refine ⟨_, ⟨⟨Proxy.t_0000_c0, rfl, run⟩, ?_, proxyPost_output .., ⟨fun a => ?_, fun a ha => ?_, ?_, ?_⟩, ?_,
    fun r => ?_⟩⟩
  · rw [proxyPost_gasLeft]; omega
  · rw [proxyPost_getCode, hk.code a]; exact dMsg_getCode ..
  · rw [proxyPost_getStor, hk.other a ha]; exact dMsg_getStor ..
  · rw [proxyPost_error]; exact afterSload2_error ..
  · rw [proxyPost_created, hk.created]; exact dMsg_created ..
  · rw [proxyPost_getStor]; exact hst
  · have h0 := hr r
    rw [proxyPost_refund]
    omega

/-- The proxy's fallback facts for a selector that is no admin entry, from a caller that is no admin. -/
theorem proxyFacts_of_sel {sevm : Sevm} {b : Devm} {s : B256} (hshort : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256) (hsel : Blanc.Sevm.selector sevm = s)
    (n1 : B256.eqCheck (Bytes.toB256 [54, 89, 207, 230]) s = 0)
    (n2 : B256.eqCheck (Bytes.toB256 [79, 30, 242, 134]) s = 0)
    (n3 : B256.eqCheck (Bytes.toB256 [92, 96, 218, 27]) s = 0)
    (n4 : B256.eqCheck (Bytes.toB256 [143, 40, 57, 112]) s = 0)
    (n5 : B256.eqCheck (Bytes.toB256 [248, 81, 164, 64]) s = 0)
    (hadm : sevm.caller ≠ (b.getStorVal sevm.currentTarget pKA).toAdr) : ProxyFacts sevm b s := by
  refine ⟨short_of_len hshort hcd, ?_, n1, n2, n3, n4, n5, ?_⟩
  · rw [legacy_selector_word]; exact hsel
  · rw [ff20_and_word, ff20_and_word, toAdr_toB256]
    exact eqCheck_ne fun e => hadm (Adr.toB256_inj e)

/-! ## The proxy's charge -/

theorem memExt96_le {n : Nat} (h : n ≤ 100) : memExtSize 96 0 n ≤ 128 := by
  unfold memExtSize
  split
  · omega
  · have : ceilDiv n 32 ≤ 4 := by unfold ceilDiv; split <;> omega
    have h3 : ceilDiv 96 32 = 3 := by decide
    rw [h3, Nat.zero_add]
    omega

section Charges

variable (sevm : Sevm) (b : Devm) (ret : B256) (S : List B256) (M : Mem)

theorem p8W_le : (p8W sevm b ret S M).1 ≤ 2200 := by
  unfold p8W; dsimp only; xcost []

theorem p14W_le : (p14W sevm b ret S M).1 ≤ 2200 := by
  unfold p14W; dsimp only; xcost []

theorem p31W_le : (p31W sevm b ret S M).1 ≤ 100 := by
  unfold p31W; dsimp only; xcost []

theorem p22W_le : (p22W sevm b ret S M).1 ≤ 2500 := by
  unfold p22W; dsimp only; xcost [p8W_le, p31W_le]

theorem proxyPreW_le (s : B256) (hlen : sevm.data.length ≤ 100) : (proxyPreW sevm b s).1 ≤ 5500 := by
  have hcopy : gasCopy * ceilDiv (Nat.toB256 sevm.data.length).toNat 32 ≤ 12 := by
    rw [B256.toNat_toB256_of_lt (by omega)]
    have : ceilDiv sevm.data.length 32 ≤ 4 := by
      unfold ceilDiv; split <;> omega
    have hg : gasCopy = 3 := rfl
    rw [hg]; omega
  have hext : ∀ (D : Devm) (R : List B256) (G : Nat),
      (St D R (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes) G).extCost
        [((Bytes.toB256 [0]).toNat, (Nat.toB256 sevm.data.length).toNat)] ≤ 12 := by
    intro D R G
    rw [B256.toNat_toB256_of_lt (by omega), show (Bytes.toB256 [0]).toNat = 0 from rfl]
    have hle := Jaune.calculateMemoryGasCost_mono
      (memExt96_le (n := sevm.data.length) hlen)
    have h128 : calculateMemoryGasCost 128 = 12 := by decide
    have hsz : ((St D R (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes) G).memory).size = 96 := by
      show (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes).size = 96
      rw [Mem.size_write_word_at]; rfl
    unfold Devm.extCost
    simp only [memExtsSize, hsz]
    omega
  unfold proxyPreW; dsimp only; xcost [p22W_le, p14W_le, hcopy, hext]

theorem dTailW_le (D : Devm) (R : List B256) (w : B256) (h32 : M.size % 32 = 0) (hge : 32 ≤ M.size) :
    (dTailW sevm D R M w).1 ≤ 100 := by
  have hext : ∀ (D : Devm) (S : List B256) (g : Nat),
      (St D S M g).extCost [((Bytes.toB256 [0]).toNat, (Nat.toB256 w.toBytes.length).toNat)] ≤ 0 := by
    intro D S g
    refine le_of_eq (Devm.extCost_zero_of_le h32 ?_)
    rw [B256.length_toBytes]
    exact hge
  have hcopy : gReturnDataCopy * ceilDiv (Nat.toB256 w.toBytes.length).toNat 32 ≤ 3 := by
    rw [B256.length_toBytes]; decide
  unfold dTailW; dsimp only; xcost [hcopy, hext]

end Charges

end Blanc.Composition.UsdcLive
