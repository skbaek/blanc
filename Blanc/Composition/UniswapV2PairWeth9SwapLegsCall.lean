import Blanc.Lift.CallMessageFacts
import Blanc.Lift.CalldataWords
import Blanc.Composition.UniswapV2PairWeth9SwapLegsRun
import Blanc.Lift.GasField
import Blanc.Lift.ExactWalkCallChild
import Blanc.Lift.Weth9.LiveTx
import Blanc.Lift.UniswapV2Pair.SwapForwardFront

/-!
# The swap's WETH9 `transfer` CALL, as a function of the call gas

`_safeTransfer` stages a 68-byte `transfer(to, amount)` window and runs `GAS; CALL`, so the call
state's gas word is all the gas left, `cg`.  Everything the CALL leaves except its gas is fixed
by the world: the parent's access charge and memory expansion, the child message (which differs
across `cg` only in its `gas`), and WETH9's transfer run (`weth9TransferPost`, which never reads
gas).  `wethTransferCall … cg` is that result, built exactly as the zero-value `CALL` crossing
`Ninst.runCompiled_call_zero_child` builds it.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.GasField

section Transfer

variable (sevm : Sevm) (W : Devm) (L : List B256) (M : Mem) (p amount toWord token rho : B256)

/-- The token word as the `CALL` reads it. -/
def tokenMask (token : B256) : B256 := token &&& 0xffffffffffffffffffffffffffffffffffffffff

/-- What stays on the stack under the seven `CALL` operands. -/
def xferRest : List B256 :=
  (68 + (p + 164)) :: tokenMask token :: 96 :: 0 :: amount :: toWord :: token :: rho :: L

/-- The `CALL` state at call gas `cg` (the record's staged state). -/
def xferCallState (cg : Nat) : Devm :=
  St W (cg.toB256 :: tokenMask token :: 0 :: (p + 164) :: 68 :: (p + 164) :: 0 ::
    xferRest L p amount toWord token rho) (safeTransfer_dynamicCallMemory M p amount toWord) cg

/-- The `CALL` state with its operands popped (gas `g` left). -/
def xferPopped (g : Nat) : Devm :=
  W.setMach ⟨xferRest L p amount toWord token rho, safeTransfer_dynamicCallMemory M p amount toWord,
    g, W.stateGas⟩

/-- The popped state with the callee warmed. -/
def xferWarm (g : Nat) : Devm :=
  addAccessedAddress (xferPopped W L M p amount toWord token rho g) (tokenMask token).toAdr

/-- The memory-expansion charge of the input/output windows. -/
def xferExt : Nat :=
  (xferPopped W L M p amount toWord token rho 0).extCost
    [⟨(p + 164).toNat, (68 : B256).toNat⟩, ⟨(p + 164).toNat, (0 : B256).toNat⟩]

/-- The callee's access charge. -/
def xferAcc : Nat := accessCost (tokenMask token).toAdr W.accessedAddresses + 0

/-- The call/forwarded gas pair of the `CALL` at call gas `cg`. -/
def xferSplit (cg : Nat) : Nat × Nat :=
  calculateMsgCallGas 0 cg cg (xferExt W L M p amount toWord token rho) (xferAcc W token)

/-- The parent the child returns to, charged `k` from gas `g`. -/
def xferParent (g k : Nat) : Devm :=
  callSpawnParent (xferWarm W L M p amount toWord token rho g) k
    (p + 164).toNat (68 : B256).toNat (p + 164).toNat (0 : B256).toNat

/-- The world the child message starts from (the zero-value debit). -/
def xferMid : Jaune.State :=
  (xferWarm W L M p amount toWord token rho 0).state.setBal sevm.currentTarget
    ((xferWarm W L M p amount toWord token rho 0).state.bal sevm.currentTarget - 0)

/-- The child message, forwarding `f`. -/
def xferMsg (g k f : Nat) : Msg :=
  callChildMsg sevm (xferParent W L M p amount toWord token rho g k) f 0 (tokenMask token).toAdr
    (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
    (W.state.getCode (tokenMask token).toAdr) false (xferMid sevm W L M p amount toWord token rho)

/-- WETH9's charge for the child's `transfer` frame (gas-free; see `xferUsedAt_eq`). -/
def xferUsedAt (g k f : Nat) : Nat :=
  Weth9.transferGas (initSevm (xferMsg sevm W L M p amount toWord token rho g k f))
    (initDevm (xferMsg sevm W L M p amount toWord token rho g k f))

/-- WETH9's charge for the child's `transfer` frame. -/
def xferUsed : Nat := xferUsedAt sevm W L M p amount toWord token rho 0 0 0

/-- The resumed parent, at popped gas `g`, charge `k`, forwarded `f`, child gas left `r`. -/
def wethTransferCallAt (g k f r : Nat) : Devm :=
  callChildPost (xferParent W L M p amount toWord token rho g k)
    (weth9TransferPost (initSevm (xferMsg sevm W L M p amount toWord token rho g k f))
      (initDevm (xferMsg sevm W L M p amount toWord token rho g k f)) r)
    (p + 164).toNat (0 : B256).toNat

/-- **The swap's WETH9 `transfer` CALL at call gas `cg`**: the parent resumed with WETH9's
transfer post. -/
def wethTransferCall (cg : Nat) : Devm :=
  wethTransferCallAt sevm W L M p amount toWord token rho cg
    ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
    (xferSplit W L M p amount toWord token rho cg).2
    ((xferSplit W L M p amount toWord token rho cg).2 - xferUsed sevm W L M p amount toWord token rho)

theorem xferMsg_sevm (g k f : Nat) :
    initSevm (xferMsg sevm W L M p amount toWord token rho g k f) =
      { initSevm (xferMsg sevm W L M p amount toWord token rho 0 0 0) with gas := f } := rfl

theorem xferMsg_devm (g k f : Nat) :
    initDevm (xferMsg sevm W L M p amount toWord token rho g k f) =
      St (initDevm (xferMsg sevm W L M p amount toWord token rho 0 0 0)) [] Mem.empty f := rfl

end Transfer

section GasField

variable (s : Sevm) (f : Nat)









theorem transferGas_gasField (pre : Devm) :
    Weth9.transferGas { s with gas := f } pre = Weth9.transferGas s pre := by
  simp only [Weth9.transferGas, Weth9.xferGasSelf, Weth9.xfTailGas, Weth9.tT1, Weth9.tT2,
    Weth9.tT3, Weth9.tV1, Weth9.tV2, Weth9.pB1, sloadCost_gasField, sstoreCost_gasField,
    afterSload_gasField, afterSstore_gasField]
  rfl



theorem selector_gasField : Sevm.selector { s with gas := f } = Sevm.selector s := rfl

theorem addLog_setMach' (b : Devm) (m : Mach) (l : Log) :
    (b.setMach m).addLog l = (b.addLog l).setMach m := rfl

theorem addLog_stateGas' (b : Devm) (l : Log) : (b.addLog l).stateGas = b.stateGas := rfl

theorem weth9TransferPost_reframe (d : Devm) (f' r : Nat) :
    weth9TransferPost { s with gas := f } (St d [] Mem.empty f') r = weth9TransferPost s d r := by
  simp only [weth9TransferPost, transferWrapperPost, xferTailPost, transferBodyMem, Weth9.tT1,
    Weth9.tT2, Weth9.tT3, Weth9.tV1, Weth9.tV2, Weth9.pB1, afterSload_gasField,
    afterSstore_gasField, dataWord_gasField, selector_gasField, St, afterSload_setMach,
    afterSstore_setMach, Devm.getStorVal_setMach, addLog_setMach', Devm.setMach_setMach,
    Devm.stateGas_setMach, addLog_stateGas', afterSload_stateGas, afterSstore_stateGas]

end GasField


section Reframe

theorem transferWrapperPost_gasLeft (b : Devm) (sel : B256) (M : Mem) (G G' : Nat) :
    transferWrapperPost b sel M G = (transferWrapperPost b sel M G').withGasLeft G := rfl

theorem weth9TransferPost_gasLeft' (s : Sevm) (d : Devm) (r r' : Nat) :
    weth9TransferPost s d r = (weth9TransferPost s d r').withGasLeft r :=
  transferWrapperPost_gasLeft _ _ _ r r'



theorem addAccessedAddress_setMach_gas (W : Devm) (S : List B256) (M : Mem) (g g' : Nat)
    (sg : StateGasMeter) (a : Adr) :
    addAccessedAddress (W.setMach ⟨S, M, g, sg⟩) a =
      (addAccessedAddress (W.setMach ⟨S, M, g', sg⟩) a).withGasLeft g := rfl

theorem callSpawnParent_withGasLeft (d : Devm) (x c c' ii is oi os : Nat) :
    callSpawnParent (d.withGasLeft x) c ii is oi os =
      (callSpawnParent d c' ii is oi os).withGasLeft (x - c) := rfl

end Reframe

section Transfer3

variable (sevm : Sevm) (W : Devm) (L : List B256) (M : Mem) (p amount toWord token rho : B256)

theorem xferParent_eq (g k : Nat) :
    xferParent W L M p amount toWord token rho g k =
      (xferParent W L M p amount toWord token rho 0 0).withGasLeft (g - k) := by
  unfold xferParent xferWarm xferPopped
  rw [addAccessedAddress_setMach_gas _ _ _ g 0, callSpawnParent_withGasLeft _ g k 0]

/-- The gas-free skeleton of the swap's WETH9 `transfer` CALL. -/
def wethTransferSkel : Devm :=
  callChildPost (xferParent W L M p amount toWord token rho 0 0)
    (weth9TransferPost (initSevm (xferMsg sevm W L M p amount toWord token rho 0 0 0))
      (initDevm (xferMsg sevm W L M p amount toWord token rho 0 0 0)) 0)
    (p + 164).toNat (0 : B256).toNat

theorem wethTransferCallAt_eq (g k f r : Nat) :
    wethTransferCallAt sevm W L M p amount toWord token rho g k f r =
      (wethTransferSkel sevm W L M p amount toWord token rho).withGasLeft (g - k + r) := by
  unfold wethTransferCallAt wethTransferSkel
  rw [xferMsg_sevm, xferMsg_devm, weth9TransferPost_reframe, xferParent_eq,
    weth9TransferPost_gasLeft' _ _ r 0, callChildPost_withGasLeft]

end Transfer3


section CallHelpers

theorem setMach_extCost (W : Devm) (S : List B256) (M : Mem) (g g' : Nat) (sg : StateGasMeter)
    (l : List (Nat × Nat)) :
    (W.setMach ⟨S, M, g, sg⟩).extCost l = (W.setMach ⟨S, M, g', sg⟩).extCost l := rfl

theorem addAccessedAddress_setMach_gasLeft (W : Devm) (m : Mach) (a : Adr) :
    (addAccessedAddress (W.setMach m) a).gasLeft = m.gasLeft := rfl

theorem addAccessedAddress_setMach_state (W : Devm) (m : Mach) (a : Adr) :
    (addAccessedAddress (W.setMach m) a).state = W.state := rfl

theorem addAccessedAddress_setMach_stack (W : Devm) (m : Mach) (a : Adr) :
    (addAccessedAddress (W.setMach m) a).stack = m.stack := rfl

theorem St_setMach_pop (W : Devm) (S S' : List B256) (M : Mem) (g : Nat) :
    (St W S M g).setMach ⟨S', (St W S M g).memory, (St W S M g).gasLeft, (St W S M g).stateGas⟩ =
      W.setMach ⟨S', M, g, W.stateGas⟩ := rfl

section Msg

variable (sevm : Sevm) (P : Devm) (f : Nat) (v : B256) (c d : Adr) (ii is : Nat) (code : ByteArray)
  (dp : Bool)

theorem vcsm_data : (initSevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).data =
    (valueCallSpawnMsg sevm P f v c d ii is code dp).data := rfl
end Msg

theorem callSpawnParent_state (d : Devm) (c ii is oi os : Nat) :
    (callSpawnParent d c ii is oi os).state = d.state := rfl







end CallHelpers

section TransferSpec

theorem xferCallState_pop (W : Devm) (L : List B256) (M : Mem) (p amount toWord token rho : B256)
    (cg : Nat) :
    (xferCallState W L M p amount toWord token rho cg).setMach
      ⟨xferRest L p amount toWord token rho,
        (xferCallState W L M p amount toWord token rho cg).memory,
        (xferCallState W L M p amount toWord token rho cg).gasLeft,
        (xferCallState W L M p amount toWord token rho cg).stateGas⟩ =
      xferPopped W L M p amount toWord token rho cg := by
  unfold xferCallState xferPopped
  exact St_setMach_pop _ _ _ _ _

variable {sevm : Sevm} {W : Devm} {L : List B256} {M : Mem} {p amount toWord token rho : B256}

theorem xfer_accessDelegation (cg : Nat)
    (hcode : W.state.getCode (tokenMask token).toAdr = Weth9.code) :
    accessDelegation (addAccessedAddress (xferPopped W L M p amount toWord token rho cg)
        (tokenMask token).toAdr) (tokenMask token).toAdr =
      ⟨false, (tokenMask token).toAdr, W.state.getCode (tokenMask token).toAdr, 0,
        xferWarm W L M p amount toWord token rho cg⟩ := by
  unfold accessDelegation xferWarm xferPopped
  rw [addAccessedAddress_setMach_state]
  dsimp only
  rw [hcode, Weth9.getDelegatedCodeAddress_code]

/-- The child message's calldata: `transfer(to, amount)` read out of the staged window. -/
theorem xferMsg_data (g k f : Nat) (wf : Mem.Wf M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 164 < 2 ^ 256) :
    (xferMsg sevm W L M p amount toWord token rho g k f).data =
      abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount.toBytes := by
  rw [← safeTransfer_dynamicCall_data wf lower width, mem_read_fst]
  unfold xferMsg
  rw [callChildMsg_zero]
  change (xferParent W L M p amount toWord token rho g k).memory.data.sliceD (p + 164).toNat
    (68 : B256).toNat 0 = _
  unfold xferParent xferWarm xferPopped
  rw [callSpawnParent_memory_data, addAccessedAddress_setMach_memory,
    show (68 : B256).toNat = 68 from rfl]

/-- **The swap's WETH9 `transfer` CALL, at the call gas WETH9's own charge fixes.**  From the
staged `CALL` state with the whole remaining gas `cg` as the gas word: WETH9's code at the token,
no precompile there, call depth left, the pair's WETH9 balance covering the amount, and enough
gas for the access, the window and WETH9's run (with its `SSTORE` sentry) after the 63/64 rule,
the `CALL` resumes with the success flag, WETH9's `true` reply, and `cg` less the access charge,
the expansion and WETH9's charge. -/
theorem wethTransferCall_spec {cg : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hcode : W.state.getCode (tokenMask token).toAdr = Weth9.code)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp (tokenMask token).toAdr = false)
    (hroom : L.length < 1016)
    (wf : Mem.Wf M) (lower : 128 ≤ p.toNat) (width : p.toNat + 164 < 2 ^ 256)
    (hle : amount ≤ W.getStorVal (tokenMask token).toAdr (Weth9.balSlot sevm.currentTarget))
    (hgw : cg < 2 ^ 256)
    (hcharge : xferAcc W token + xferExt W L M p amount toWord token rho ≤ cg)
    (hfwd : xferUsed sevm W L M p amount toWord token rho + gCallStipend ≤
      except64th (cg - xferExt W L M p amount toWord token rho - xferAcc W token)) :
    Ninst.RunCompiled sevm (xferCallState W L M p amount toWord token rho cg) (.exec .call)
        (wethTransferCall sevm W L M p amount toWord token rho cg) ∧
      (wethTransferCall sevm W L M p amount toWord token rho cg).stack =
        1 :: xferRest L p amount toWord token rho ∧
      (wethTransferCall sevm W L M p amount toWord token rho cg).returnData = (1 : B256).toBytes ∧
      (wethTransferCall sevm W L M p amount toWord token rho cg).gasLeft =
        cg - (xferAcc W token + xferExt W L M p amount toWord token rho +
          xferUsed sevm W L M p amount toWord token rho) := by
  -- the call/forward split
  generalize hext : xferExt W L M p amount toWord token rho = ext at hcharge hfwd ⊢
  generalize hacc : xferAcc W token = acc at hcharge hfwd ⊢
  generalize hused : xferUsed sevm W L M p amount toWord token rho = used at hfwd ⊢
  generalize hfw : except64th (cg - ext - acc) = fwd at hfwd
  have hfwle : fwd ≤ cg - ext - acc := by rw [← hfw]; unfold except64th; omega
  have hsplit : xferSplit W L M p amount toWord token rho cg = ⟨fwd + acc, fwd⟩ := by
    unfold xferSplit
    rw [hext, hacc]
    unfold calculateMsgCallGas
    simp only [show ¬ cg < acc + ext from by omega, ↓reduceIte, hfw]
    rw [Nat.min_eq_right (by omega), Nat.add_zero]
  -- the child message and its run
  have hmsg : xferMsg sevm W L M p amount toWord token rho cg (fwd + acc + ext) fwd =
      valueCallSpawnMsg sevm (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
        (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
        (W.state.getCode (tokenMask token).toAdr) false := by
    unfold xferMsg
    rw [callChildMsg_zero]
  have hdata := xferMsg_data (sevm := sevm) (W := W) (L := L) (M := M) (p := p) (amount := amount)
    (toWord := toWord) (token := token) (rho := rho)
    cg (fwd + acc + ext) fwd wf lower width
  rw [hmsg] at hdata
  obtain ⟨hw4, hw36, hlen⟩ := dataWord_twoWords (e := initSevm (valueCallSpawnMsg sevm
    (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
    (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
    (W.state.getCode (tokenMask token).toAdr) false)) hdata
  have hsel := selector_eq_of_data_eq_abiSelectorBytes_append
    (sevm := initSevm (valueCallSpawnMsg sevm
    (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
    (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
    (W.state.getCode (tokenMask token).toAdr) false)) (selected := 0xa9059cbb)
    (by decide) (by rw [vcsm_data, hdata, List.append_assoc])
  -- WETH9's run in the child
  have hUsed : Weth9.transferGas (initSevm (xferMsg sevm W L M p amount toWord token rho cg
      (fwd + acc + ext) fwd)) (initDevm (xferMsg sevm W L M p amount toWord token rho cg
      (fwd + acc + ext) fwd)) = used := by
    rw [← hused, xferMsg_sevm, xferMsg_devm, transferGas_gasField, Weth9Token.transferGas_St]
    rfl
  rw [hmsg] at hUsed
  have hrun := weth9_transfer_runExact_post
    (sevm := initSevm (valueCallSpawnMsg sevm
      (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
      (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
      (W.state.getCode (tokenMask token).toAdr) false))
    (pre := initDevm (valueCallSpawnMsg sevm
      (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
      (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
      (W.state.getCode (tokenMask token).toAdr) false)) (G := fwd - used)
    (by rw [vcsm_benvStat]; exact hfork) (by rw [vcsm_isStatic, hstatic]; rfl)
    (by rw [vcsm_value]) (hsel.trans Weth9.trSel_eq.symm) (by omega) (by omega)
    (vcsm_stack ..) (vcsm_memory ..)
    (by
      rw [hw36, vcsm_currentTarget, vcsm_caller]
      unfold Devm.getStorVal Devm.getAcct at hle ⊢
      rw [vcsm_state]
      unfold xferParent xferWarm xferPopped
      rw [callSpawnParent_state, addAccessedAddress_setMach_state]
      exact hle)
    (by rw [vcsm_gasLeft, hUsed]; omega)
    (by unfold gCallStipend at hfwd ⊢; omega)
  have hexec := (exec_iff_exec_eq 0 _ _ _).mp (Weth9.exec_of_runExact
    (by rw [vcsm_code]; exact hcode) (by rw [vcsm_benvStat]; exact hfork) hrun)
  -- the crossing
  have hcross := Ninst.runCompiled_call_zero_child
    (devm := xferCallState W L M p amount toWord token rho cg) (gw := cg.toB256)
    (cw := tokenMask token) (iiw := p + 164) (isw := 68) (oiw := p + 164) (osw := 0)
    (s := xferRest L p amount toWord token rho) (dp := false) (dadr := (tokenMask token).toAdr)
    (code := W.state.getCode (tokenMask token).toAdr) (dgc := 0)
    (d1 := xferWarm W L M p amount toWord token rho cg) (ext := ext) (acc := acc)
    (mcc := fwd + acc) (mcs := fwd) (stmid := xferMid sevm W L M p amount toWord token rho)
    (cpost := weth9TransferPost (initSevm (valueCallSpawnMsg sevm
      (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
      (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
      (W.state.getCode (tokenMask token).toAdr) false)) (initDevm (valueCallSpawnMsg sevm
      (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
      (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
      (W.state.getCode (tokenMask token).toAdr) false)) (fwd - used))
    hfork rfl ?ext ?del ?acc ?split ?gas hdepth hprec ?room ?sub ?exec ?err
  case ext =>
    rw [← hext, xferCallState_pop]
    exact setMach_extCost _ _ _ _ _ _ _
  case del =>
    rw [xferCallState_pop]
    exact xfer_accessDelegation cg hcode
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
  case exec =>
    rw [callChildMsg_zero]
    exact hexec
  case err => rw [weth9TransferPost_error, vcsm_error]
  have hd : wethTransferCall sevm W L M p amount toWord token rho cg =
      callChildPost (callSpawnParent (xferWarm W L M p amount toWord token rho cg) (fwd + acc + ext)
        (p + 164).toNat (68 : B256).toNat (p + 164).toNat (0 : B256).toNat)
        (weth9TransferPost (initSevm (valueCallSpawnMsg sevm
          (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
          (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
          (W.state.getCode (tokenMask token).toAdr) false)) (initDevm (valueCallSpawnMsg sevm
          (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
          (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
          (W.state.getCode (tokenMask token).toAdr) false)) (fwd - used))
        (p + 164).toNat (0 : B256).toNat := by
    unfold wethTransferCall wethTransferCallAt
    rw [hsplit, hext, hused]
    dsimp only
    rw [hmsg]
    rfl
  rw [hd]
  obtain ⟨hstk, -, hgas, -, -⟩ := callChildPost_facts_zero (callSpawnParent
    (xferWarm W L M p amount toWord token rho cg) (fwd + acc + ext) (p + 164).toNat
    (68 : B256).toNat (p + 164).toNat (0 : B256).toNat) (weth9TransferPost (initSevm
    (valueCallSpawnMsg sevm (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
      (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
      (W.state.getCode (tokenMask token).toAdr) false)) (initDevm (valueCallSpawnMsg sevm
      (xferParent W L M p amount toWord token rho cg (fwd + acc + ext)) fwd 0
      (tokenMask token).toAdr (tokenMask token).toAdr (p + 164).toNat (68 : B256).toNat
      (W.state.getCode (tokenMask token).toAdr) false)) (fwd - used))
    (p + 164).toNat (0 : B256).toNat rfl
  refine ⟨hcross, ?_, ?_, ?_⟩
  · rw [hstk, callSpawnParent_stack]
    unfold xferWarm xferPopped
    rw [addAccessedAddress_setMach_stack]
  · rw [callChildPost_returnData, weth9TransferPost_output]
  · rw [hgas, callSpawnParent_gasLeft, weth9TransferPost_gasLeft]
    unfold xferWarm xferPopped
    rw [addAccessedAddress_setMach_gasLeft]
    change cg - (fwd + acc + ext) + (fwd - used) = cg - (acc + ext + used)
    omega

end TransferSpec

end Blanc.Composition.UniswapV2PairWeth9Joint
