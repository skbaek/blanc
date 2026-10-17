import Blanc.Composition.UniswapV2PairUsdcWeth9LegsCall
import Blanc.Composition.UniswapV2PairWeth9SwapLegsCall

/-!
# The Pair's USDC `transfer` CALL, as a function of the call gas (U9a)

The USDC analogue of `wethTransferCall`: `_safeTransfer`'s staged `CALL` (the token-neutral
`xferCallState`, `xferParent`, `xferMsg`, `xferExt`, `xferAcc`, `xferSplit`) into the USDC proxy,
whose child frame is the gas-exact proxy frame of `transfer` (`usdc_transfer_live`), with its
exact charge `proxyXferCost` and its explicit post `proxyXferPost`.  Neither reads the child
message's gas, so the result's gas-free columns are fixed by the world (`usdcTransferCallAt_eq`).
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken

section Transfer

variable (sevm : Sevm) (W : Devm) (L : List B256) (M : Mem) (p amount toWord token rho : B256)

/-- The child frame's environment (gas-free). -/
abbrev uChildS : Sevm := initSevm (xferMsg sevm W L M p amount toWord token rho 0 0 0)

/-- The child frame's base (gas-free). -/
abbrev uChildB : Devm := initDevm (xferMsg sevm W L M p amount toWord token rho 0 0 0)

/-- USDC's exact charge for the child's `transfer` frame through the proxy. -/
noncomputable def usdcUsed : Nat :=
  proxyXferCost (uChildS sevm W L M p amount toWord token rho) (uChildB sevm W L M p amount toWord token rho)

/-- The gas USDC's child frame needs forwarded. -/
noncomputable def usdcBudget : Nat :=
  usdcXferBudget (uChildS sevm W L M p amount toWord token rho) (uChildB sevm W L M p amount toWord token rho)

/-- The resumed parent, at popped gas `g`, charge `k`, forwarded `f`, child gas left `r`. -/
noncomputable def usdcTransferCallAt (g k f r : Nat) : Devm :=
  callChildPost (xferParent W L M p amount toWord token rho g k)
    (proxyXferPost (initSevm (xferMsg sevm W L M p amount toWord token rho g k f))
      (uChildB sevm W L M p amount toWord token rho) r)
    (p + 164).toNat (0 : B256).toNat

/-- **The Pair's USDC `transfer` CALL at call gas `cg`.** -/
noncomputable def usdcTransferCall (cg : Nat) : Devm :=
  usdcTransferCallAt sevm W L M p amount toWord token rho cg
    ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
    (xferSplit W L M p amount toWord token rho cg).2
    ((xferSplit W L M p amount toWord token rho cg).2 - usdcUsed sevm W L M p amount toWord token rho)

/-- The gas-free skeleton of the Pair's USDC `transfer` CALL. -/
noncomputable def usdcTransferSkel : Devm :=
  callChildPost (xferParent W L M p amount toWord token rho 0 0)
    (proxyXferPost (uChildS sevm W L M p amount toWord token rho)
      (uChildB sevm W L M p amount toWord token rho) 0)
    (p + 164).toNat (0 : B256).toNat

theorem usdcTransferCallAt_eq (g k f r : Nat) :
    usdcTransferCallAt sevm W L M p amount toWord token rho g k f r =
      (usdcTransferSkel sevm W L M p amount toWord token rho).withGasLeft (g - k + r) := by
  unfold usdcTransferCallAt usdcTransferSkel
  rw [xferMsg_sevm, proxyXferPost_gasField, xferParent_eq, proxyXferPost_reframe _ _ r,
    callChildPost_withGasLeft]

end Transfer

/-! ## Reading the child message -/

/-- A long-enough message with the `transfer` selector asks `transfer` of its argument words. -/
theorem usdcOp_of_transfer {e : Sevm} (len : 68 ≤ e.data.length)
    (sel : Blanc.Sevm.selector e = 0xa9059cbb) :
    usdcOp e = .transfer (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36).toNat := by
  have bal : ¬ (36 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0x70a08231) := by
    rintro ⟨-, h⟩; rw [sel] at h; exact absurd h (by decide)
  unfold usdcOp
  rw [ite_eq_right bal, ite_eq_left ⟨len, sel⟩]

/-- A `transfer` frame touches only the caller's and the destination's balance keys. -/
theorem frameKeys_transfer {e : Sevm} {d : Adr} {v : Nat}
    (sel : Blanc.Sevm.selector e = 0xa9059cbb) (dec : decodeCall e = some (.transfer d v)) :
    ∀ k ∈ frameKeys e, k = .bal e.caller ∨ k = .bal d := by
  intro k hk
  have hv : viewKeys e = [] := by
    simp only [viewKeys, sel]
    simp only [show ¬ ((0xa9059cbb : B256) = 0x70a08231 ∨ (0xa9059cbb : B256) = 0xfe575a87) from by decide,
      show ¬ ((0xa9059cbb : B256) = 0xdd62ed3e) from by decide,
      show ¬ ((0xa9059cbb : B256) = 0x7ecebe00) from by decide,
      show ¬ ((0xa9059cbb : B256) = 0xe94a0102) from by decide,
      show ¬ ((0xa9059cbb : B256) = 0xaa271e1a) from by decide,
      show ¬ ((0xa9059cbb : B256) = 0x8a6db9c3) from by decide, ↓reduceIte]
  simp only [frameKeys, hv, dec, Option.map_some, Option.getD_some, List.nil_append, Call.keys,
    List.mem_cons, List.not_mem_nil, or_false] at hk
  exact hk

theorem mask_toAdr (x : B256) :
    ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& x).toAdr = x.toAdr := by
  rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = Bytes.toB256 [0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff] by decide, Blanc.ff20_and_word, Jaune.toAdr_toB256]

theorem proxyPost_error (sevm : Sevm) (pre : Devm) (Y X : Nat) (C : Devm) (w : B256) :
    (proxyPost sevm pre Y X C w).error = pre.error := by
  unfold proxyPost
  rw [Devm.withOutput_error, Devm.memRead_error, St_error]
  show (pBase sevm pre).error = _
  unfold pBase
  rw [afterSload_error, afterSload_error]

/-! ## The crossing -/

section TransferSpec

variable {sevm : Sevm} {W : Devm} {L : List B256} {M : Mem} {p amount toWord token rho : B256}

theorem usdc_accessDelegation (cg : Nat)
    (hcode : W.state.getCode (tokenMask token).toAdr = Proxy.code) :
    accessDelegation (addAccessedAddress (xferPopped W L M p amount toWord token rho cg)
        (tokenMask token).toAdr) (tokenMask token).toAdr =
      ⟨false, (tokenMask token).toAdr, W.state.getCode (tokenMask token).toAdr, 0,
        xferWarm W L M p amount toWord token rho cg⟩ := by
  unfold accessDelegation xferWarm xferPopped
  rw [addAccessedAddress_setMach_state]
  dsimp only
  rw [hcode, Blanc.Lift.Usdc.proxy_undelegated]

/-- **The Pair's USDC `transfer` CALL, at the call gas USDC's own charge fixes.**  From the staged
`CALL` state with the whole remaining gas `cg` as the gas word: USDC installed at the token with its
footprint invariant, the token not a precompile, two levels of call depth left (the Pair's `CALL`
and the proxy's `DELEGATECALL`), the Pair and the recipient tracked, the Pair not USDC's admin, the
transfer's ledger conditions and the Pair's balance covering the amount, and the child's budget
after the 63/64 rule: the `CALL` resumes with the success flag, USDC's `true` reply, and `cg` less
the access charge, the expansion and USDC's exact charge. -/
theorem usdcTransferCall_spec {U : Key → Prop} {cg : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (inst : UsdcInstalled (tokenMask token).toAdr W.state)
    (finv : FootInv U (W.state.getStor (tokenMask token).toAdr))
    (hstatic : sevm.isStatic = false) (hdepth : 2 ≤ sevm.depth)
    (hprec : sevm.benvStat.rules.isPrecomp (tokenMask token).toAdr = false)
    (hroom : L.length < 1016)
    (wf : Mem.Wf M) (lower : 128 ≤ p.toNat) (width : p.toNat + 164 < 2 ^ 256)
    (kPair : U (.bal sevm.currentTarget)) (kTo : U (.bal toWord.toAdr))
    (notAdmin : sevm.currentTarget ≠ adminOf W.state (tokenMask token).toAdr)
    (ok : UsdcTransferOk (ledger U (W.state.getStor (tokenMask token).toAdr)) sevm.currentTarget
      toWord.toAdr amount.toNat)
    (hle : amount.toNat ≤ (ledger U (W.state.getStor (tokenMask token).toAdr)).bal sevm.currentTarget)
    (hgw : cg < 2 ^ 256)
    (hcharge : xferAcc W token + xferExt W L M p amount toWord token rho ≤ cg)
    (hfwd : usdcBudget sevm W L M p amount toWord token rho ≤
      except64th (cg - xferExt W L M p amount toWord token rho - xferAcc W token)) :
    Ninst.RunCompiled sevm (xferCallState W L M p amount toWord token rho cg) (.exec .call)
        (usdcTransferCall sevm W L M p amount toWord token rho cg) ∧
      (usdcTransferCall sevm W L M p amount toWord token rho cg).stack =
        1 :: xferRest L p amount toWord token rho ∧
      (usdcTransferCall sevm W L M p amount toWord token rho cg).returnData = (1 : B256).toBytes ∧
      (usdcTransferCall sevm W L M p amount toWord token rho cg).gasLeft =
        cg - (xferAcc W token + xferExt W L M p amount toWord token rho +
          usdcUsed sevm W L M p amount toWord token rho) := by
  have hbu : usdcUsed sevm W L M p amount toWord token rho ≤ usdcBudget sevm W L M p amount toWord token rho := by
    unfold usdcUsed usdcBudget usdcXferBudget; omega
  generalize hext : xferExt W L M p amount toWord token rho = ext at hcharge hfwd ⊢
  generalize hacc : xferAcc W token = acc at hcharge hfwd ⊢
  generalize hused : usdcUsed sevm W L M p amount toWord token rho = used at hbu ⊢
  generalize hbud : usdcBudget sevm W L M p amount toWord token rho = bud at hfwd hbu
  generalize hfw : except64th (cg - ext - acc) = fwd at hfwd
  have hfwle : fwd ≤ cg - ext - acc := by rw [← hfw]; unfold except64th; omega
  have hsplit : xferSplit W L M p amount toWord token rho cg = ⟨fwd + acc, fwd⟩ := by
    unfold xferSplit
    rw [hext, hacc]
    unfold calculateMsgCallGas
    simp only [show ¬ cg < acc + ext from by omega, ↓reduceIte, hfw]
    rw [Nat.min_eq_right (by omega), Nat.add_zero]
  have hmsg : xferMsg sevm W L M p amount toWord token rho cg (fwd + acc + ext) fwd =
      valueCallSpawnMsg sevm (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
        (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
        (W.state.getCode (tokenMask token).toAdr) false := by
    unfold xferMsg
    rw [callChildMsg_zero]
  have hdata := xferMsg_data (sevm := sevm) (W := W) (L := L) (M := M) (p := p) (amount := amount)
    (toWord := toWord) (token := token) (rho := rho)
    cg (fwd + acc + ext) fwd wf lower width
  obtain ⟨hw4, hw36, hlen⟩ := dataWord_twoWords
    (e := initSevm (xferMsg sevm W L M p amount toWord token rho cg (fwd + acc + ext) fwd)) hdata
  have hsel := selector_eq_of_data_eq_abiSelectorBytes_append
    (sevm := initSevm (xferMsg sevm W L M p amount toWord token rho cg (fwd + acc + ext) fwd))
    (selected := 0xa9059cbb) (by decide) (by rw [show (initSevm (xferMsg sevm W L M p amount toWord
      token rho cg (fwd + acc + ext) fwd)).data = (xferMsg sevm W L M p amount toWord token rho cg
      (fwd + acc + ext) fwd).data from rfl, hdata, List.append_assoc])
  -- the child frame
  have hS := xferMsg_sevm sevm W L M p amount toWord token rho cg (fwd + acc + ext) fwd
  have hB := xferMsg_devm sevm W L M p amount toWord token rho cg (fwd + acc + ext) fwd
  have hstate : (uChildB sevm W L M p amount toWord token rho).state = W.state := by
    show (initDevm (xferMsg sevm W L M p amount toWord token rho 0 0 0)).state = _
    unfold xferMsg
    rw [callChildMsg_zero, vcsm_state]
    unfold xferParent xferWarm xferPopped
    rw [callSpawnParent_state, addAccessedAddress_setMach_state]
  have hdst : (Sevm.dataWord (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      (fwd + acc + ext) fwd)) 4).toAdr = toWord.toAdr := by
    rw [hw4, mask_toAdr]
  have hv : (Sevm.dataWord (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      (fwd + acc + ext) fwd)) 36).toNat = amount.toNat := by rw [hw36]
  have hcaller : (initSevm (xferMsg sevm W L M p amount toWord token rho cg (fwd + acc + ext)
      fwd)).caller = sevm.currentTarget := by rw [hmsg]; rfl
  have hop := usdcOp_of_transfer (by omega) hsel
  rw [hdst, hv] at hop
  have hvalue : (initSevm (xferMsg sevm W L M p amount toWord token rho cg (fwd + acc + ext)
      fwd)).value = 0 := by rw [hmsg]; rfl
  have dec := decodeCall_transfer hsel (by omega) hvalue
  rw [hdst, hv] at dec
  have hprox : W.state.getCode (tokenMask token).toAdr = Proxy.code :=
    code_of_at (d := W) inst.proxy
  have live := usdc_transfer_live (P := (tokenMask token).toAdr) (U := U)
    (sevm := initSevm (xferMsg sevm W L M p amount toWord token rho cg (fwd + acc + ext) fwd))
    (pre := uChildB sevm W L M p amount toWord token rho) (G := fwd)
    (dst := toWord.toAdr) (v := amount.toNat)
    (by rw [hmsg]; rfl) (by rw [hstate, hmsg]; rfl)
    (fun k hk => by
      rcases frameKeys_transfer hsel dec k hk with rfl | rfl
      · rw [hcaller]; exact kPair
      · exact kTo)
    (by omega) (by rw [hcaller, hstate]; exact notAdmin)
    (fun d v h => by
      rw [hop] at h
      obtain ⟨rfl, rfl⟩ := Blanc.Lift.Token.Op.transfer.inj h
      rw [hcaller, hstate]; exact ok)
    (by rw [hmsg]; exact hfork) hvalue (by rw [hmsg]; show (false || sevm.isStatic) = false; rw [hstatic]; rfl)
    (by rw [hstate]; exact inst) (by rw [hstate]; exact finv) hop
    (by rw [hcaller, hstate]; exact hle)
    (by
      have e : usdcXferBudget (initSevm (xferMsg sevm W L M p amount toWord token rho cg
          (fwd + acc + ext) fwd)) (uChildB sevm W L M p amount toWord token rho) = bud := by
        rw [← hbud, hS]
        unfold usdcBudget usdcXferBudget
        rw [proxyXferCost_gasField, childXferCost_gasField]
      rw [e]; exact hfwd)
    (by omega) (by rw [hmsg]; show sevm.depth - 1 ≠ 0; omega)
  obtain ⟨post, ⟨crun⟩, hgasP, -, -, -, hpost⟩ := live
  have hcost : proxyXferCost (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      (fwd + acc + ext) fwd)) (uChildB sevm W L M p amount toWord token rho) = used := by
    rw [← hused, hS, proxyXferCost_gasField]; rfl
  rw [hcost] at hgasP hpost
  rw [← hB] at crun
  have hexec := (exec_iff_exec_eq 0 _ _ _).mp ⟨crun⟩
  -- the crossing
  have hcross := Ninst.runCompiled_call_zero_child
    (devm := xferCallState W L M p amount toWord token rho cg) (gw := cg.toB256)
    (cw := tokenMask token) (iiw := p + 164) (isw := 68) (oiw := p + 164) (osw := 0)
    (s := xferRest L p amount toWord token rho) (dp := false) (dadr := (tokenMask token).toAdr)
    (code := W.state.getCode (tokenMask token).toAdr) (dgc := 0)
    (d1 := xferWarm W L M p amount toWord token rho cg) (ext := ext) (acc := acc)
    (mcc := fwd + acc) (mcs := fwd) (stmid := xferMid sevm W L M p amount toWord token rho)
    (cpost := post)
    hfork rfl ?ext ?del ?acc ?split ?gas (by omega) hprec ?room ?sub ?exec ?err
  case ext =>
    rw [← hext, xferCallState_pop]
    exact setMach_extCost _ _ _ _ _ _ _
  case del =>
    rw [xferCallState_pop]
    exact usdc_accessDelegation cg hprox
  case acc => rw [← hacc]; rfl
  case split =>
    unfold xferWarm xferPopped
    rw [B256.toNat_toB256_of_lt hgw, addAccessedAddress_setMach_gasLeft, ← hsplit]
    unfold xferSplit
    rw [hext, hacc]
  case gas =>
    unfold xferWarm xferPopped
    rw [addAccessedAddress_setMach_gasLeft]
    change fwd + acc + ext ≤ cg
    omega
  case room =>
    simp only [xferRest, List.length_cons]
    omega
  case sub =>
    unfold xferMid xferWarm xferPopped
    rw [addAccessedAddress_setMach_state, addAccessedAddress_setMach_state]
    unfold State.subBal
    simp only [show ¬ W.state.bal sevm.currentTarget < 0 from B256.not_lt.mpr (B256.zero_le _),
      ↓reduceIte]
  case exec => exact hexec
  case err =>
    rw [hpost, proxyPost_error]
    rfl
  have hd : usdcTransferCall sevm W L M p amount toWord token rho cg =
      callChildPost (callSpawnParent (xferWarm W L M p amount toWord token rho cg) (fwd + acc + ext)
        (p + 164).toNat (68 : B256).toNat (p + 164).toNat (0 : B256).toNat) post
        (p + 164).toNat (0 : B256).toNat := by
    unfold usdcTransferCall usdcTransferCallAt
    rw [hsplit, hext, hused]
    dsimp only
    rw [hpost]
    rfl
  rw [hd]
  obtain ⟨hstk, -, hgas, -, -⟩ := callChildPost_facts_zero (callSpawnParent
    (xferWarm W L M p amount toWord token rho cg) (fwd + acc + ext) (p + 164).toNat
    (68 : B256).toNat (p + 164).toNat (0 : B256).toNat) post (p + 164).toNat (0 : B256).toNat rfl
  refine ⟨hcross, ?_, ?_, ?_⟩
  · rw [hstk, callSpawnParent_stack]
    unfold xferWarm xferPopped
    rw [addAccessedAddress_setMach_stack]
  · rw [callChildPost_returnData, hpost, proxyPost_output]
    rfl
  · rw [hgas, callSpawnParent_gasLeft]
    unfold xferWarm xferPopped
    rw [addAccessedAddress_setMach_gasLeft]
    change cg - (fwd + acc + ext) + post.gasLeft = cg - (acc + ext + used)
    omega

end TransferSpec

end Blanc.Composition.UsdcLive
