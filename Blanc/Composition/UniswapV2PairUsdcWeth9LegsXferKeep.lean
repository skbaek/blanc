import Blanc.Composition.UniswapV2PairUsdcWeth9LegsXfer
import Blanc.Composition.UniswapV2PairWeth9SwapLiveFacts

/-!
# What the Pair's USDC `transfer` CALL keeps (U9b)

`usdcTransferCall` is an explicit post: the proxy's `DELEGATECALL` into the implementation, whose
`transfer` reads and writes storage at the proxy only and moves no value.  So the resumed parent's
world agrees with the staged world `W` off the token's storage: every other account's storage, every
code and every balance (`usdcTransferCall_keeps`).
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Composition.UniswapV2PairWeth9Joint

theorem setStorVal_state_bal (d : Devm) (adr : Adr) (k v : B256) (a : Adr) :
    (d.setStorVal adr k v).state.bal a = d.state.bal a := by
  show ((d.state.setStorVal adr k v).get a).bal = (d.state.get a).bal
  by_cases h : adr = a
  · subst h
    rw [State.setStorVal_get_self]
  · rw [State.setStorVal_get_ne _ h]

theorem afterSstore_bal (sevm : Sevm) (b : Devm) (k v : B256) (a : Adr) :
    (afterSstore sevm b k v).state.bal a = b.state.bal a := by
  unfold afterSstore
  split <;> exact setStorVal_state_bal _ _ _ _ _

theorem implXferPost_state (s : Sevm) (b : Devm) (G : Nat) :
    (implXferPost s b G).state =
      (e93Post s (e37Pre s b (xTo s)) (xVal s) (xTo s) s.caller.toB256).state := by
  unfold implXferPost
  rw [Devm.withOutput_state, Devm.memRead_state]
  exact St_state _ _ _ _

theorem addLog_state' (d : Devm) (l : Log) : (d.addLog l).state = d.state := rfl

theorem addLog_getStor' (d : Devm) (l : Log) (a : Adr) :
    Devm.getStor (d.addLog l) a = Devm.getStor d a := rfl

section Keep

variable (sevm : Sevm) (W : Devm) (L : List B256) (M : Mem) (p amount toWord token rho : B256)

/-- The implementation child's halting world, as the base the transfer's post is built on. -/
theorem usdcTransferCall_state (cg : Nat) :
    ∃ (s : Sevm) (b : Devm), s.currentTarget = (tokenMask token).toAdr ∧
      s.caller = sevm.currentTarget ∧
      (Mem.Wf M → 128 ≤ p.toNat → p.toNat + 164 < 2 ^ 256 →
        (Sevm.dataWord s 4).toAdr = toWord.toAdr) ∧ b.state = W.state ∧
      (usdcTransferCall sevm W L M p amount toWord token rho cg).state =
        (e93Post s (e37Pre s b (xTo s)) (xVal s) (xTo s) s.caller.toB256).state := by
  refine ⟨initSevm (dMsg (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2)) (uChildB sevm W L M p amount toWord token rho)
      (frameY (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2)) (uChildB sevm W L M p amount toWord token rho)
      ((xferSplit W L M p amount toWord token rho cg).2 - usdcUsed sevm W L M p amount toWord token rho))),
    initDevm (dMsg (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2)) (uChildB sevm W L M p amount toWord token rho) 0),
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold xferMsg
    rw [callChildMsg_zero]
    rfl
  · unfold xferMsg
    rw [callChildMsg_zero]
    rfl
  · intro wf lower width
    have hdata := xferMsg_data (sevm := sevm) (W := W) (L := L) (M := M) (p := p) (amount := amount)
      (toWord := toWord) (token := token) (rho := rho) cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2 wf lower width
    obtain ⟨hw4, -, hlen⟩ := dataWord_twoWords (e := initSevm (xferMsg sevm W L M p amount toWord
      token rho cg ((xferSplit W L M p amount toWord token rho cg).1 +
        xferExt W L M p amount toWord token rho) (xferSplit W L M p amount toWord token rho cg).2)) hdata
    have hd := dMsg_data (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2)) (uChildB sevm W L M p amount toWord token rho)
      (frameY (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2)) (uChildB sevm W L M p amount toWord token rho)
      ((xferSplit W L M p amount toWord token rho cg).2 - usdcUsed sevm W L M p amount toWord token rho))
      (by rw [hlen]; decide)
    have hw : Sevm.dataWord (initSevm (dMsg (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2)) (uChildB sevm W L M p amount toWord token rho)
      (frameY (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2)) (uChildB sevm W L M p amount toWord token rho)
      ((xferSplit W L M p amount toWord token rho cg).2 - usdcUsed sevm W L M p amount toWord token rho))))
      4 = Sevm.dataWord (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2)) 4 := by
      unfold Sevm.dataWord; rw [hd]
    rw [hw, hw4, mask_toAdr]
  · show (pBase _ _).state = _
    rw [Blanc.Composition.UsdcToken.pBase_state]
    show (initDevm (xferMsg sevm W L M p amount toWord token rho 0 0 0)).state = _
    unfold xferMsg
    rw [callChildMsg_zero, vcsm_state]
    unfold xferParent xferWarm xferPopped
    rw [callSpawnParent_state, addAccessedAddress_setMach_state]
  · unfold usdcTransferCall usdcTransferCallAt
    rw [(callChildPost_facts_zero _ _ _ (B256.toNat 0) rfl).2.2.2.1, proxyPost_state]
    exact implXferPost_state _ _ _

/-- **The Pair's USDC `transfer` CALL keeps the world off the token's storage**: at any call gas,
every other account's storage, every code and every balance of the resumed parent are the staged
world's. -/
theorem usdcTransferCall_keeps (cg : Nat) :
    (∀ a, a ≠ (tokenMask token).toAdr →
      (usdcTransferCall sevm W L M p amount toWord token rho cg).state.getStor a = W.state.getStor a) ∧
    (∀ a, (usdcTransferCall sevm W L M p amount toWord token rho cg).state.getCode a =
      W.state.getCode a) ∧
    (∀ a, (usdcTransferCall sevm W L M p amount toWord token rho cg).state.bal a = W.state.bal a) := by
  obtain ⟨s, b, ht, -, -, hb, hs⟩ := usdcTransferCall_state sevm W L M p amount toWord token rho cg
  rw [hs, ← hb]
  refine ⟨fun a ha => ?_, fun a => ?_, fun a => ?_⟩
  · have ne : s.currentTarget ≠ a := by rw [ht]; exact Ne.symm ha
    change Devm.getStor (e93Post s (e37Pre s b (xTo s)) (xVal s) (xTo s) s.caller.toB256) a =
      Devm.getStor b a
    unfold e93Post e93Debited e37Pre
    simp only [addLog_getStor', afterSstore_getStor_ne _ _ _ _ _ ne, afterSload_getStor]
  · unfold e93Post e93Debited e37Pre
    simp only [addLog_state', UniswapV2PairWeth9Joint.afterSstore_getCode, UniswapV2PairWeth9Joint.afterSload_state]
  · unfold e93Post e93Debited e37Pre
    simp only [addLog_state', afterSstore_bal, UniswapV2PairWeth9Joint.afterSload_state]

/-- **At the token, the transfer writes only the two balance words**: any storage word of the token
off the Pair's and the recipient's balance slots is the staged world's (given the staged request's
layout, which fixes the recipient the child decodes). -/
theorem usdcTransferCall_tokenStor (cg : Nat) {k : B256} (wf : Mem.Wf M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 164 < 2 ^ 256) (kPair : k ≠ balSlot sevm.currentTarget)
    (kTo : k ≠ balSlot toWord.toAdr) :
    ((usdcTransferCall sevm W L M p amount toWord token rho cg).state.getStor
      (tokenMask token).toAdr).get k = (W.state.getStor (tokenMask token).toAdr).get k := by
  obtain ⟨s, b, ht, hc, hw, hb, hs⟩ := usdcTransferCall_state sevm W L M p amount toWord token rho cg
  have hw := hw wf lower width
  rw [hs, ← hb, ← ht]
  have e1 : ky' s.caller.toB256 = balSlot sevm.currentTarget := by
    unfold ky' balSlot
    rw [word_ff20, Jaune.toAdr_toB256, hc, lit9]
  have e2 : ky' (xTo s) = balSlot toWord.toAdr := by
    unfold ky' balSlot
    rw [word_ff20, xTo_toAdr, hw, lit9]
  change (Devm.getStor (e93Post s (e37Pre s b (xTo s)) (xVal s) (xTo s) s.caller.toB256)
    s.currentTarget).get k = (Devm.getStor b s.currentTarget).get k
  unfold e93Post e93Debited e37Pre
  rw [e1, e2]
  simp only [addLog_getStor', afterSstore_getStor_self, afterSload_getStor,
    Stor.get_set_ne _ (Ne.symm kTo), Stor.get_set_ne _ (Ne.symm kPair)]

end Keep

end Blanc.Composition.UsdcLive

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint

/-- WETH9's `transfer` post: its world is the transfer tail's (shared by the swap and burn rows). -/
theorem weth9TransferPost_state (s : Sevm) (b : Devm) (G : Nat) :
    (weth9TransferPost s b G).state = (xferTailPost s (Weth9.pB1 s b s.caller) s.caller
      (Sevm.dataWord s 4).toAdr (Sevm.dataWord s 36)).state := by
  unfold weth9TransferPost transferWrapperPost
  rw [Devm.withOutput_state, Devm.memRead_state]
  exact St_state _ _ _ _

end Blanc.Composition.UniswapV2PairUsdcWeth9
