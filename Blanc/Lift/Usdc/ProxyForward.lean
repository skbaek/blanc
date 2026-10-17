import Blanc.Lift.Usdc.ProxyHalt
import Blanc.Lift.Usdc.SpawnExact
import Blanc.Lift.CallSiteChildren
import Blanc.Lift.CallChildren
import Blanc.Lift.RetainedTargetCompleteness
import Blanc.CallSpawnExact
import Jaune.MulDiv

/-!
# The proxy frame theorems (C2)

`proxy_forwards` (non-admin caller), `proxy_admin_rule` (admin caller) and the C2 control
`proxy_forwards_control`, from the certificate walk `proxy_reach` (`ProxyReach.lean`): every node of a
pc-0 proxy frame that decodes an external instruction sits at `_delegate`'s `DELEGATECALL` (non-admin)
or at `upgradeToAndCall`'s `CALL` to the proxy itself (admin), with its operands.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.Proxy

theorem adminOf_eq (w : Devm) (P : Adr) :
    adminOf w.state P = (w.getStorVal P adminSlot).toAdr := rfl

/-- **The external instructions of a proxy frame.**  Every node of the chain of a pc-0 frame running
the proxy code that decodes an external instruction `x` is at `_delegate`'s `DELEGATECALL` (caller
not the admin word) or at `upgradeToAndCall`'s `CALL` to the proxy (admin caller). -/
theorem proxy_node {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) :
    ∃ (f : SFunc) (K : List SFunc), (x = .delegatecall ∧ DelegateConf sevm pre ⟨N.devm, .next (.exec x) f, K⟩) ∨
      (x = .call ∧ SelfCallConf sevm pre ⟨N.devm, .next (.exec x) f, K⟩ ∧
        dispatchWord sevm = Bytes.toB256 [0x4f, 0x1e, 0xf2, 0x86]) := by
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix cert_check
    (R := ⟨0, sevm, pre, out, run⟩) rfl codeEq fork chain
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hat
  have hT : AtExec (κ.conf N.devm) := ⟨x, g, hf⟩
  change Reach _ _ _ ⟨pre, t_0000_c0, []⟩ _ at reach
  have hstart : (⟨pre, t_0000_c0, []⟩ : Conf) =
      ⟨St pre pre.stack pre.memory pre.gasLeft, t_0000_c0, []⟩ := by
    rw [← St.self' pre]
  rw [hstart] at reach
  have hconf : κ.conf N.devm = ⟨N.devm, .next (.exec x) g, κ.K.map Cont.f⟩ := by
    show (⟨N.devm, κ.f, κ.K.map Cont.f⟩ : Conf) = _
    rw [hf]
  rw [hconf] at reach hT
  refine ⟨g, κ.K.map Cont.f, ?_⟩
  rcases proxy_reach (fun h => StepIn.toRun h) fork reach hT with hd | ⟨hs, hw⟩
  · have hx : x = .delegatecall := by
      obtain ⟨-, _, _, _, _, _, _, -, hf', -⟩ := hd
      simp only [SFunc.next.injEq, Ninst.exec.injEq] at hf'
      exact hf'.1
    exact .inl ⟨hx, hd⟩
  · have hx : x = .call := by
      obtain ⟨-, ⟨_, hf'⟩, -⟩ := hs
      simp only [SFunc.next.injEq, Ninst.exec.injEq] at hf'
      exact hf'.1
    exact .inr ⟨hx, hs, hw⟩

theorem getStorVal_eq_state (w : Devm) (a : Adr) (k : B256) :
    w.getStorVal a k = (w.state.getStor a).get k := rfl

theorem getCode_eq_state (w : Devm) (a : Adr) : w.getCode a = w.state.getCode a := rfl

theorem getCode_St (b : Devm) (S : List B256) (M : Mem) (G : Nat) (a : Adr) :
    (St b S M G).getCode a = b.getCode a := rfl

theorem getCode_of_state {b b' : Devm} (h : b'.state = b.state) (a : Adr) :
    b'.getCode a = b.getCode a := by
  simp only [Devm.getCode, Devm.getAcct, h]

/-- **The `DELEGATECALL` child of a non-admin proxy frame.**  Every committed child runs at the
proxy's storage with the implementation's code address and code, the frame's caller, value and static
flag, and the first `calldatasize mod 2²⁵⁶` bytes of the calldata. -/
theorem proxy_child {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork)
    {I : Adr} (slot : (pre.state.getStor sevm.currentTarget).get implSlot = I.toB256)
    (notAdmin : sevm.caller ≠ adminOf pre.state sevm.currentTarget)
    (undelegated : getDelegatedCodeAddress (pre.state.getCode I) = none) :
    ∀ c ∈ Exec.childFrames run, c.sevm.currentTarget = sevm.currentTarget ∧
      c.sevm.codeAddress = some I ∧ c.sevm.caller = sevm.caller ∧ c.sevm.value = sevm.value ∧
      c.sevm.data = sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0 ∧
      c.sevm.isStatic = sevm.isStatic ∧ c.sevm.code = pre.state.getCode I := by
  intro c member
  obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) c member
  obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeFork : CoveredFork N.sevm.benvStat.fork := by rw [sevmEq]; exact fork
  obtain ⟨g, K, ⟨rfl, hd⟩ | ⟨-, hs, -⟩⟩ := proxy_node run codeEq fork chain hat
  swap
  · exact (notAdmin (by rw [adminOf_eq]; exact hs.1)).elim
  obtain ⟨-, b', w, S, M, G, rest, hstate, -, hdev⟩ := hd
  change N.devm = _ at hdev
  have hv : pre.getStorVal sevm.currentTarget implSlot = I.toB256 := slot
  rw [hv] at hdev
  have hstack : N.devm.stack = w :: I.toB256 :: (0 :: sevm.data.length.toB256 :: 0 :: 0 :: S) := by
    rw [hdev]; rfl
  have nodeCode : N.devm.getCode I = pre.state.getCode I := by
    rw [hdev, getCode_St, getCode_of_state hstate]; rfl
  obtain ⟨hT, hA, hC, hV, hS, hK, ii, is, oi, os, s', hrest, hD⟩ :=
    Xinst.step_delegatecall_spawn_exact nodeFork hx hstack
      (by rw [toAdr_toB256, nodeCode]; exact undelegated)
  simp only [List.cons.injEq] at hrest
  obtain ⟨rfl, rfl, -, -, -⟩ := hrest
  rw [toAdr_toB256] at hA hK
  obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv enter
  subst hcevm
  rw [childEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show f.inner.currentTarget = _
    rw [hT, sevmEq]
  · show f.inner.codeAddress = _
    exact hA
  · show f.inner.caller = _
    rw [hC, sevmEq]
  · show f.inner.value = _
    rw [hV, sevmEq]
  · show f.inner.data = _
    rw [hD, hdev, St.memory, show (0 : B256).toNat = 0 from rfl]
    have key := Mem.read_write_zero' M (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)
    rw [List.length_sliceD] at key
    exact key
  · show f.inner.isStatic = _
    rw [hS, sevmEq]
  · show f.inner.code = _
    rw [hK, nodeCode]

/-- **C2 control.**  With the slot naming `J ≠ I`, no committed child runs `I`'s address. -/
theorem proxy_forwards_control {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (codeEq : sevm.code = Proxy.code)
    (fork : CoveredFork sevm.benvStat.fork) {I J : Adr}
    (slot : (pre.state.getStor sevm.currentTarget).get implSlot = J.toB256) (ne : J ≠ I)
    (notAdmin : sevm.caller ≠ adminOf pre.state sevm.currentTarget)
    (undelegated : getDelegatedCodeAddress (pre.state.getCode J) = none)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp J) :
    ∀ c ∈ Exec.childFrames run, c.sevm.codeAddress ≠ some I := by
  intro c member hc
  have hJ := (proxy_child run codeEq fork slot notAdmin undelegated c member).2.1
  exact ne (Option.some.inj (hJ.symm.trans hc))

/-- solc 0.4's selector extraction, `div(calldataload(0), 2^224) & 0xffffffff`, is
`Sevm.selector`'s `>>> 224` (the proof of `Blanc.Lift.Weth9.sel_extract`; hoist candidate). -/
theorem dispatchWord_eq_selector (sevm : Sevm) : dispatchWord sevm = Blanc.Sevm.selector sevm := by
  unfold dispatchWord Blanc.Sevm.selector
  rw [show Bytes.toB256 [0x00] = (0 : B256) from by decide]
  generalize Sevm.dataWord sevm 0 = x
  have hP : (Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toNat = 2 ^ 224 := by decide
  have hm : (Bytes.toB256 [0xff, 0xff, 0xff, 0xff]).toNat = 2 ^ 32 - 1 := by decide
  have hP0 : Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ≠ 0 := by decide
  apply B256.toNat_inj
  rw [B256.toNat_and, B256.toNat_div hP0, hP, hm, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  rcases x with ⟨⟨x3, x2⟩, lo⟩
  have h1 : B256.shiftRight ((x3, x2), lo) 224 = ((0 : B128), B128.shiftRight (x3, x2) 96) := by
    simp only [B256.shiftRight, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.reduceLT, Nat.reduceSub]; rfl
  have h2 : B128.shiftRight (x3, x2) 96 = ((0 : UInt64), x3 >>> (32 : UInt64)) := by
    simp only [B128.shiftRight]; rfl
  change B256.toNat ((x3, x2), lo) / 2 ^ 224 % 2 ^ 32 = B256.toNat (B256.shiftRight ((x3, x2), lo) 224)
  rw [h1, h2]
  have e1 : B256.toNat ((x3, x2), lo) = B128.toNat (x3, x2) * 2 ^ 128 + lo.toNat :=
    B256.toNat_eq _
  have e2 : B128.toNat (x3, x2) = x3.toNat * 2 ^ 64 + x2.toNat := B128.toNat_eq _
  have e3 : B256.toNat ((0 : B128), ((0 : UInt64), x3 >>> (32 : UInt64))) =
      B128.toNat (0 : B128) * 2 ^ 128 + B128.toNat ((0 : UInt64), x3 >>> (32 : UInt64)) :=
    B256.toNat_eq _
  have e4 : B128.toNat ((0 : UInt64), x3 >>> (32 : UInt64)) =
      (0 : UInt64).toNat * 2 ^ 64 + (x3 >>> (32 : UInt64)).toNat := B128.toNat_eq _
  have e5 : (x3 >>> (32 : UInt64)).toNat = x3.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have h3 := UInt64.toNat_lt x3
  have h2' := UInt64.toNat_lt x2
  have hlo := B128.toNat_lt (x := lo)
  simp only [B128.toNat_zero, UInt64.toNat_zero] at h3 h2' e3 e4
  omega

/-- **C2, the admin rule.**  A pc-0 proxy frame whose caller is the admin word spawns no
`DELEGATECALL`: its committed children are self-calls (`upgradeToAndCall`), and a frame whose
selector is none of `upgradeTo`/`upgradeToAndCall`/`changeAdmin` has no committed child and leaves
the proxy's storage unchanged. -/
theorem proxy_admin_exec {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork)
    (admin : sevm.caller = adminOf pre.state sevm.currentTarget) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        x = .call ∧ Blanc.Sevm.selector sevm = 0x4f1ef286 ∧
          ∃ (g : B256) (S : List B256), N.devm.stack = g :: sevm.currentTarget.toB256 :: S := by
  intro N chain x hat
  obtain ⟨g, K, ⟨-, hd⟩ | ⟨rfl, hs, hw⟩⟩ := proxy_node run codeEq fork chain hat
  · exact (hd.1 (by rw [← adminOf_eq]; exact admin)).elim
  · refine ⟨rfl, ?_, hs.2.2⟩
    rw [← dispatchWord_eq_selector, hw]
    decide

theorem proxy_admin_children {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork)
    (admin : sevm.caller = adminOf pre.state sevm.currentTarget) :
    ∀ c ∈ Exec.childFrames run, c.sevm.currentTarget = sevm.currentTarget ∧
      c.sevm.caller = sevm.currentTarget := by
  intro c member
  obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) c member
  obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeFork : CoveredFork N.sevm.benvStat.fork := by rw [sevmEq]; exact fork
  obtain ⟨rfl, -, w, S, hstack⟩ := proxy_admin_exec run codeEq fork admin N chain x hat
  obtain ⟨g', t, v, ii, is, oi, os, rest, hs7⟩ := Xinst.step_call_spawn_stack nodeFork hx
  have same := hstack.symm.trans hs7
  simp only [List.cons.injEq] at same
  obtain ⟨-, ht, -⟩ := same
  have hn : Ninst.step ⟨N.pc, N.sevm, N.devm⟩ Ninst.call = .spawn f rsm (N.pc + 1) := by
    rw [Ninst.call, Ninst.step_exec]
    simp only [hx, XStep.toStep]
  obtain ⟨_, _, _, _, _, -, -, -, -, -, hframe, -⟩ := Ninst.step_call_spawn_exact hn hs7 nodeFork
  obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv enter
  subst hcevm
  rw [childEq]
  have hcaller := Xinst.step_call_spawn_caller hx
  subst hframe
  refine ⟨?_, ?_⟩
  · show t.toAdr = _
    rw [← ht, toAdr_toB256]
  · show N.sevm.currentTarget = _
    rw [sevmEq]

theorem proxy_admin_rule {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork)
    (admin : sevm.caller = adminOf pre.state sevm.currentTarget) :
    (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .call) ∧
    (∀ c ∈ Exec.childFrames run, c.sevm.currentTarget = sevm.currentTarget ∧
      c.sevm.caller = sevm.currentTarget) ∧
    (Blanc.Sevm.selector sevm ∉ [0x3659cfe6, 0x4f1ef286, 0x8f283970] →
      Exec.childFrames run = [] ∧
      ∀ post, out = .ok post →
        post.state.getStor sevm.currentTarget = pre.state.getStor sevm.currentTarget) := by
  refine ⟨fun N chain x hat => (proxy_admin_exec run codeEq fork admin N chain x hat).1,
    proxy_admin_children run codeEq fork admin, fun hsel => ⟨?_, ?_⟩⟩
  · apply Exec.childFrames_eq_nil_of_free ⟨0, sevm, pre, out, run⟩
    intro node chain x hat
    obtain ⟨-, hs, -⟩ := proxy_admin_exec run codeEq fork admin node chain x hat
    exact hsel (by rw [hs]; decide)
  · intro post hout
    subst hout
    obtain ⟨f, hf0, hrun⟩ := lift_sound cert_check codeEq fork run
    obtain rfl : f = t_0000_c0 := Option.some.inj (hf0.symm.trans rfl)
    rw [St.self' pre] at hrun
    rcases proxy_halt (P := Ninst.Run) (fun h => h) fork hrun with ⟨notAdmin, -⟩ | ⟨-, hw⟩
    · exact (notAdmin (by rw [← adminOf_eq]; exact admin)).elim
    rw [dispatchWord_eq_selector] at hw
    rcases hw with hw | hw | hw | hstor
    · exact (hsel (by rw [hw]; decide)).elim
    · exact (hsel (by rw [hw]; decide)).elim
    · exact (hsel (by rw [hw]; decide)).elim
    · exact congrFun hstor sevm.currentTarget

end Blanc.Lift.Usdc
