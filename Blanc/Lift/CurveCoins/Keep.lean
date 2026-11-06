import Blanc.Lift.ForeignKeep
import Blanc.Lift.HistIdentityCall
import Blanc.Lift.InvWalkLegacy
import Blanc.Lift.Usdc.ImplV2.Check
import Blanc.Lift.Usdc.ImplV2_1.Check
import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.Dai.Check
import Blanc.Lift.UsdtFrames
import Blanc.Lift.Usdc.ProxyRawCallers
import Blanc.Lift.Usdc.ProxyForward
import Blanc.OwnerDiscipline

/-!
# A coin frame on `transfer`, `transferFrom` or `balanceOf` enters no frame

For each coin's certified code, a frame (of any outcome) whose calldata selector is one of the three the
pool sends decodes no external instruction on its own chain: the dispatcher sends the reach to the
selector's wrapper, whose closure lies in a decided exec-free set. The sets are the largest exec-free
reference-closed sets of each certificate, so what they leave out is what can call out:
`rescueERC20` (USDC), the library calls and `permit`-family signature checks (V2_2), `permit` (DAI), and
USDT's deprecated forwards, which enter as the named premise `flag20 (slot 10) = 0`.

Nothing here assumes a storage value but that one flag, and no fit premise. The lane premise is
`rules.stateGas = none` alone.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc Blanc.Lift

/-- The selectors the pool sends a coin: `transfer`, `transferFrom`, `balanceOf`. -/
def PoolCoinSel (s : B256) : Prop := s = 0xa9059cbb ∨ s = 0x23b872dd ∨ s = 0x70a08231

/-- Chain nodes of a frame decode no external instruction. -/
abbrev ChainNoExec {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out) : Prop :=
  ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N → ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)

section Usdc

def v2Free : List Nat := [1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 22, 24, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 68, 69, 74, 75, 77, 78, 79, 80, 81, 82, 83, 85, 86, 88, 89, 90, 93, 94, 96, 97, 98, 99, 100, 101, 102, 105, 106, 107, 108, 110, 112, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]

theorem v2Free_execFree : ExecFreeSet Usdc.ImplV2.cert.prog v2Free = true := by decide +kernel

/-- **FiatTokenV2 on the pool's selectors enters no frame.** -/
theorem usdcV2_noExec {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Usdc.ImplV2.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : PoolCoinSel (Blanc.Sevm.selector sevm)) : ChainNoExec run :=
  noExec_of_reach Usdc.ImplV2.cert_check rfl rfl run hcode hsg fun T h t => by
    change Reach _ _ _ ⟨_, Usdc.ImplV2.t_0000_c0, []⟩ T at h
    repeat rstepN h t
    rbranchE h t v2Free_execFree
    repeat rstepN h t
    rbranchE h t v2Free_execFree
    iterate 4 rstepN h t
    rw [shr_selector_word] at h
    rcases sel with s | s | s <;> rw [s] at h <;> repeat rdispE h t v2Free_execFree

def v2_1Free : List Nat := [1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 72, 73, 75, 76, 77, 78, 79, 80, 81, 82, 84, 86, 87, 88, 91, 92, 94, 95, 96, 98, 99, 100, 102, 103, 104, 105, 106, 108, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]

theorem v2_1Free_execFree : ExecFreeSet Usdc.ImplV2_1.cert.prog v2_1Free = true := by decide +kernel

/-- **FiatTokenV2_1 on the pool's selectors enters no frame.** -/
theorem usdcV2_1_noExec {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Usdc.ImplV2_1.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : PoolCoinSel (Blanc.Sevm.selector sevm)) : ChainNoExec run :=
  noExec_of_reach Usdc.ImplV2_1.cert_check rfl rfl run hcode hsg fun T h t => by
    change Reach _ _ _ ⟨_, Usdc.ImplV2_1.t_0000_c0, []⟩ T at h
    repeat rstepN h t
    rbranchE h t v2_1Free_execFree
    repeat rstepN h t
    rbranchE h t v2_1Free_execFree
    iterate 4 rstepN h t
    rw [shr_selector_word] at h
    rcases sel with s | s | s <;> rw [s] at h <;> repeat rdispE h t v2_1Free_execFree

def v22Free : List Nat := [1, 2, 3, 4, 5, 6, 7, 10, 12, 13, 14, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 29, 31, 32, 33, 35, 36, 37, 38, 39, 40, 42, 44, 45, 46, 47, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 85, 86, 92, 93, 96, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 112, 113, 115, 116, 119, 120, 122, 123, 124, 126, 127, 128, 130, 131, 133, 134, 135, 137, 139, 140, 141, 143, 144, 145, 146, 147, 148, 150, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]

theorem v22Free_execFree : ExecFreeSet Usdc.Impl.cert.prog v22Free = true := by decide +kernel

/-- **FiatTokenV2_2 on the pool's selectors enters no frame.** -/
theorem usdc22_noExec {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Usdc.Impl.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : PoolCoinSel (Blanc.Sevm.selector sevm)) : ChainNoExec run :=
  noExec_of_reach Usdc.Impl.cert_check rfl rfl run hcode hsg fun T h t => by
    change Reach _ _ _ ⟨_, Usdc.Impl.t_0000_c0, []⟩ T at h
    repeat rstepN h t
    rbranchE h t v22Free_execFree
    repeat rstepN h t
    rbranchE h t v22Free_execFree
    iterate 4 rstepN h t
    rw [shr_selector_word] at h
    rcases sel with s | s | s <;> rw [s] at h <;> repeat rdispE h t v22Free_execFree

end Usdc

section Dai

def daiFree : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]

theorem daiFree_execFree : ExecFreeSet Dai.cert.prog daiFree = true := by decide +kernel

/-- **DAI on the pool's selectors enters no frame.** -/
theorem dai_noExec {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Dai.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : PoolCoinSel (Blanc.Sevm.selector sevm)) : ChainNoExec run :=
  noExec_of_reach Dai.cert_check rfl rfl run hcode hsg fun T h t => by
    change Reach _ _ _ ⟨_, Dai.t_0000_c0, []⟩ T at h
    repeat rstepN h t
    rbranchE h t daiFree_execFree
    repeat rstepN h t
    rbranchE h t daiFree_execFree
    iterate 4 rstepN h t
    rw [shr_selector_word] at h
    rcases sel with s | s | s <;> rw [s] at h <;> repeat rdispE h t daiFree_execFree

end Dai

section Usdt

def usdtFree : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 40, 41, 42, 44, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 67, 68, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 86, 87, 88, 90, 91, 92, 93, 94]

theorem usdtFree_execFree : ExecFreeSet Usdt.cert.prog usdtFree = true := by decide +kernel

/-- The branch on `deprecated`: the forwarding arm contradicts the flag, the other lies in the set. -/
macro "rdeprecated " h:ident t:ident c:ident hdep:ident : tactic => `(tactic|
  (rcases rr_branch $h $t with ⟨$c, _, $h:ident⟩ | ⟨$c, _, $h:ident⟩
   · exfalso
     simp only [afterSloadH_getStor, afterSloadH_getStorVal, gsv, show Bytes.toB256 [10] = 10 from by decide] at $c:ident
     rw [show (Bytes.toB256 [255] &&& (Devm.getStor _ _).get 10 /
       B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 from $hdep] at $c:ident
     exact absurd $c (by decide)
   · exact Reach.false_of_execFree usdtFree_execFree $h $t (by decide)
       (fun _ hs => absurd hs List.not_mem_nil)))

section Reach

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {R : Exec.Deriv} {T : Conf}

/-- `transfer`'s body, not deprecated. -/
theorem usdt_e39_reach {v t' ret : B256} (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (h : Reach (StepIn R) Usdt.cert.prog sevm ⟨St b (v :: t' :: ret :: S) M G, Usdt.t_14f4_c39, []⟩ T)
    (t : AtExec T) : False := by
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rdeprecated h t c hdep

/-- `transferFrom`'s body, not deprecated. -/
theorem usdt_e23_reach {v t' r ret : B256} (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (h : Reach (StepIn R) Usdt.cert.prog sevm ⟨St b (v :: t' :: r :: ret :: S) M G, Usdt.t_0ebd_c23, []⟩ T)
    (t : AtExec T) : False := by
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rdeprecated h t c hdep

/-- `balanceOf`'s body, not deprecated. -/
theorem usdt_e33_reach {a ret : B256} (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (h : Reach (StepIn R) Usdt.cert.prog sevm ⟨St b (a :: ret :: S) M G, Usdt.t_1239_c33, []⟩ T)
    (t : AtExec T) : False := by
  repeat rstepS h t bal
  rdeprecated h t c hdep

end Reach

/-- Enter wrapper callee `k` (tree `g`), whose continuation lies in the set, from a reach `h`. -/
macro "rinto " h:ident t:ident k:num g:term : tactic => `(tactic|
  (have h' := rr_callInto (k := $k) (g := $g) usdtFree_execFree rfl (by decide)
     (fun _ hs => absurd hs List.not_mem_nil) $h $t
   clear $h
   obtain ⟨_, _, $h:ident, e⟩ := h'
   subst e
   replace $t:ident := AtExec.below.1 $t))

/-- **TetherToken on the pool's selectors, not deprecated, enters no frame.** -/
theorem usdt_noExec {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Usdt.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor pre sevm.currentTarget).get 10) = 0)
    (sel : PoolCoinSel (Blanc.Sevm.selector sevm)) : ChainNoExec run :=
  noExec_of_reach Usdt.cert_check rfl rfl run hcode hsg fun T h t => by
    change Reach _ _ _ ⟨_, Usdt.t_0000_c0, []⟩ T at h
    iterate 7 rstepN h t
    rbranchE h t usdtFree_execFree
    iterate 7 rstepN h t
    rw [legacy_selector_word] at h
    rcases sel with s | s | s <;> rw [s] at h <;> repeat rdispE h t usdtFree_execFree
    · repeat rstepN h t
      rbranchE h t usdtFree_execFree
      repeat rstepN h t
      rinto h t 39 Usdt.t_14f4_c39
      exact usdt_e39_reach bal (by simpa only [St_getStor] using hdep) h t
    · repeat rstepN h t
      rbranchE h t usdtFree_execFree
      repeat rstepN h t
      rinto h t 23 Usdt.t_0ebd_c23
      exact usdt_e23_reach bal (by simpa only [St_getStor] using hdep) h t
    · repeat rstepN h t
      rbranchE h t usdtFree_execFree
      repeat rstepN h t
      rinto h t 33 Usdt.t_1239_c33
      exact usdt_e33_reach bal (by simpa only [St_getStor] using hdep) h t

end Usdt

section Frames

/-- **What a pool's coin frame keeps, from its code**: a committed frame on the pool's selectors whose
chain decodes no external instruction keeps the foreign world. -/
theorem frameKeeps_of_noExec (c : Exec.Frame) (hpc : c.pc = 0)
    (hsg : c.sevm.benvStat.rules.stateGas = none)
    (h : ∀ {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out),
      c.sevm = sevm → c.pre = pre → ChainNoExec run) : FrameKeepsForeign c := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at hpc hsg h
  subst hpc
  exact frameKeepsForeign_of_noExec _ hsg (h run rfl rfl)

theorem dai_frameKeeps (c : Exec.Frame) (hpc : c.pc = 0) (hcode : c.sevm.code = Dai.code)
    (hsg : c.sevm.benvStat.rules.stateGas = none)
    (sel : PoolCoinSel (Blanc.Sevm.selector c.sevm)) : FrameKeepsForeign c :=
  frameKeeps_of_noExec c hpc hsg fun run e _ => dai_noExec run (e ▸ hcode) (e ▸ hsg) (e ▸ sel)

/-- **`deprecated` is the operator power USDT's keep names**: TetherToken's slot `10` flag clear at the
frame's entry. While it is set, these selectors forward to an owner-chosen address, about which
nothing holds. -/
theorem usdt_frameKeeps (c : Exec.Frame) (hpc : c.pc = 0) (hcode : c.sevm.code = Usdt.code)
    (hsg : c.sevm.benvStat.rules.stateGas = none) (bal : c.sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor c.pre c.sevm.currentTarget).get 10) = 0)
    (sel : PoolCoinSel (Blanc.Sevm.selector c.sevm)) : FrameKeepsForeign c :=
  frameKeeps_of_noExec c hpc hsg fun run e p =>
    usdt_noExec run (e ▸ hcode) (e ▸ hsg) (e ▸ bal) (by subst e; subst p; exact hdep) (e ▸ sel)

/-- The three FiatToken versions in the pool's span. -/
def UsdcVersion (C : ByteArray) : Prop :=
  C = Usdc.ImplV2.code ∨ C = Usdc.ImplV2_1.code ∨ C = Usdc.Impl.code

theorem UsdcVersion.not_delegation {C : ByteArray} (h : UsdcVersion C) : ¬ isValidDelegation C := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- **USDC's implementation word names one of the three versions** (the proxy admin's power, at one
state). -/
def UsdcImplAt (d : Devm) (t : Adr) : Prop :=
  UsdcVersion (d.getCode (d.getStorVal t Usdc.implSlot).toAdr)

theorem usdcVersion_noExec {C : ByteArray} (hC : UsdcVersion C) {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec 0 sevm pre out) (hcode : sevm.code = C)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : PoolCoinSel (Blanc.Sevm.selector sevm)) : ChainNoExec run := by
  rcases hC with rfl | rfl | rfl
  · exact usdcV2_noExec run hcode hsg sel
  · exact usdcV2_1_noExec run hcode hsg sel
  · exact usdc22_noExec run hcode hsg sel

/-- **A committed USDC proxy frame on the pool's selectors keeps the foreign world**, given its
implementation word at entry names one of the three versions. Whoever the caller is: the admin's dispatch
reverts on these selectors. -/
theorem usdc_frameKeeps (c : Exec.Frame) (hpc : c.pc = 0) (hcode : c.sevm.code = Usdc.Proxy.code)
    (hsg : c.sevm.benvStat.rules.stateGas = none) (bal : c.sevm.benvStat.rules.bal = none)
    (hsize : c.sevm.data.length < 2 ^ 256)
    (hI : UsdcImplAt c.pre c.sevm.currentTarget)
    (sel : PoolCoinSel (Blanc.Sevm.selector c.sevm)) : FrameKeepsForeign c := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at hpc hcode hsg bal hsize hI sel
  subst hpc
  refine frameKeepsForeign_of_roots _ hsg fun r hr => ?_
  simp only [Exec.rawFrameRoots, List.mem_cons] at hr
  rcases hr with rfl | hr
  · rfl
  refine Exec.rawFrameDescendants_at (root := ⟨0, sevm, pre, out, run⟩) ?_ run (.refl _) r hr
  intro nodePc nextPc nodeSevm nodePre nodeOut raw frame rsm cevm nrun chain step enter child D hD
  obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
  have env : nodeSevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  subst env
  obtain ⟨f, K, ⟨rfl, delegated⟩ | ⟨rfl, -, hw⟩⟩ := Usdc.Proxy.proxy_nodeH run hcode hsg bal chain hat
  swap
  · rw [Usdc.dispatchWord_eq_selector] at hw
    rcases sel with s | s | s <;> rw [s] at hw <;> exact absurd hw (by decide)
  obtain ⟨-, b', gas, S, M, G, tail, hstate, -, input⟩ := delegated
  change nodePre = _ at input
  subst input
  have hslotCode : (St b' (gas :: pre.getStorVal nodeSevm.currentTarget Usdc.implSlot :: 0 ::
      nodeSevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (nodeSevm.data.sliceD 0 nodeSevm.data.length.toB256.toNat 0)) G).getCode
        (pre.getStorVal nodeSevm.currentTarget Usdc.implSlot).toAdr =
      pre.getCode (pre.getStorVal nodeSevm.currentTarget Usdc.implSlot).toAdr := by
    rw [St_getCode]
    simp only [Devm.getCode, Devm.getAcct, hstate]
  have hcC := Xinst.step_delegatecall_spawn_code hx rfl (by rw [hslotCode]; exact hI.not_delegation)
  obtain ⟨target, -, -, -, data⟩ := Xinst.step_delegatecall_spawn_St_noStateGas hsg hx
  obtain ⟨benv, -, childEq⟩ := Frame.enter_run_inv enter
  subst childEq
  have hdata : frame.inner.data = nodeSevm.data := by
    rw [data]
    have read : ((M.write 0 (nodeSevm.data.sliceD 0 nodeSevm.data.length.toB256.toNat 0)).read 0
        nodeSevm.data.length.toB256.toNat).1 =
        nodeSevm.data.sliceD 0 nodeSevm.data.length.toB256.toNat 0 := by
      by_cases empty : nodeSevm.data.sliceD 0 nodeSevm.data.length.toB256.toNat 0 = []
      · have length := congrArg List.length empty
        simp only [List.length_sliceD, List.length_nil] at length
        rw [empty, length]
        rfl
      · simpa only [List.length_sliceD] using Mem.read_write_zero M empty
    rw [show (0 : B256).toNat = 0 from rfl, read, B256.toNat_toB256_of_lt hsize]
    exact Bytes.sliceD_zero_length rfl
  have hnil := Exec.rawFrameDescendants_eq_nil_of_noExec child (usdcVersion_noExec
    (C := frame.inner.code) (by rw [hcC, hslotCode]; exact hI) child rfl
    (by rw [Frame.enter_run_benvStat enter, Xinst.step_spawn_benvStat hx]; exact hsg)
    (by
      have e : (initEvm (frame.inner.withBenv benv)).sta.data = nodeSevm.data := hdata
      simpa only [Blanc.Sevm.selector, Sevm.dataWord, e] using sel))
  simp only [Exec.rawFrameRoots, hnil, List.mem_singleton] at hD
  subst hD
  exact target

end Frames

end Blanc.Lift.CurveCoins
