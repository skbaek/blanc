import Blanc.Lift.Usdc.HistorySlots
import Blanc.Lift.ReachSilentTail

/-!
# Code facts behind USDC's family obligations (U6h1)

The contract-side facts the family ladder's instance (`HistoryFamily.lean`) consumes:

* `proxy_tail`: after the proxy's external instruction (`_delegate`'s `DELEGATECALL`, or
  `upgradeToAndCall`'s `CALL`) the frame ends in the resumed state and decodes no further external
  instruction (`silent_after_exec` over the proxy certificate's decided checks);
* `impl_exec_kind`: an implementation node decodes `CALL`, or `DELEGATECALL` naming the library;
* `decodeCall_not_getter`: a decoded implementation message is no proxy getter;
* `impl_whole_law`: the family laws at a good ledger, keeping the node clause, for a successful
  implementation frame other than `rescueERC20`;
* the three runtimes are pairwise distinct.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.Token

/-! ## The three runtimes are distinct -/

theorem proxy_ne_impl : Proxy.code ≠ Impl.code := fun h =>
  absurd (congrArg ByteArray.size h) (by decide +kernel)

theorem lib_ne_impl : Lib.code ≠ Impl.code := fun h =>
  absurd (congrArg ByteArray.size h) (by decide +kernel)

theorem lib_ne_proxy : Lib.code ≠ Proxy.code := fun h =>
  absurd (congrArg ByteArray.size h) (by decide +kernel)

/-! ## The proxy's silent tails -/

/-- The proxy's exec-free entries. -/
def proxyExecFree : List Nat := [8, 9, 10, 12, 14, 15, 17, 18, 20, 22, 25, 31, 32]

/-- The proxy's silent entries. -/
def proxySilent : List Nat := [8, 10, 12, 14, 15, 18, 20, 22, 31, 32]

theorem proxy_execFree : ExecFreeSet Proxy.cert.prog proxyExecFree = true := by decide

theorem proxy_silentSet : SilentSet Proxy.cert.prog proxySilent = true := by decide

theorem proxy_contsIn : ∀ f ∈ Proxy.cert.prog, f.contsIn proxyExecFree proxySilent = true := by
  decide

theorem proxy_execSilent : ∀ f ∈ Proxy.cert.prog, f.nodesSatisfy (ExecSilent proxySilent) = true := by
  decide

/-- **The proxy's tail.**  After any external instruction of a successful proxy frame, the frame
ends in the resumed state and decodes no further external instruction. -/
theorem proxy_tail {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) :
    ∀ N', Exec.Deriv.ParentStep N' N → post.state = N'.devm.state ∧
      ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) :=
  silent_after_exec Proxy.cert_check proxy_execFree proxy_silentSet proxy_contsIn proxy_execSilent
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl codeEq fork rfl chain hat

/-! ## Implementation nodes and messages -/

/-- An implementation node decodes `CALL`, or `DELEGATECALL` whose address operand is the
library's. -/
theorem impl_exec_kind {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) :
    x = .call ∨ (x = .delegatecall ∧ ∀ (g a : B256) (rest : List B256),
      N.devm.stack = g :: a :: rest → a = usdcLib.toB256) := by
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix certL_check
    (F := ⟨0, sevm, pre, out, run⟩) rfl codeEq fork chain
  have frames := Cursor.framesSat_of_reachable certL_framesSat certL_framesSat_head reach
  have hP := ok.framesSat_exec frames hat
  have kind := ok.execsSatisfy (Cursor.execsSatisfy_of_reachable impl_kinds reach) hat
  cases x with
  | call => exact .inl rfl
  | delegatecall =>
      simp only [implP, beq_iff_eq] at hP
      have hw := ok.stack_const hP
      refine .inr ⟨rfl, fun g a rest hs => ?_⟩
      rw [hs] at hw
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hw
      exact hw
  | _ => simp only [implKinds, reduceCtorEq, beq_iff_eq, Bool.or_eq_true, or_self] at kind

/-- A decoded implementation message is no proxy getter (`admin()`, `implementation()` are not
among the implementation's selectors). -/
theorem decodeCall_not_getter {e : Sevm} {c : Call} (h : decodeCall e = some c) : ¬ adminGetter e := by
  obtain ⟨r, hr, hsel, -⟩ := decodeCall_some h
  have sels : ∀ r ∈ rows, r.sel ≠ 0xf851a440 ∧ r.sel ≠ 0x5c60da1b := by decide
  intro getter
  rcases getter with g | g
  · exact (sels r hr).1 (hsel.trans g)
  · exact (sels r hr).2 (hsel.trans g)

/-- **The whole-frame family laws at a good ledger.**  A successful non-static implementation
frame other than `rescueERC20`, entered by a caller other than the admin word at a good ledger,
commits the book's step on its message, keeps the proxy's two slots, and decodes only
`DELEGATECALL`s. -/
theorem impl_whole_law {P : Adr} {U : Key → Prop} (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Impl.code) (target : sevm.currentTarget = P)
    (codeAddr : sevm.codeAddress = some usdcImpl) (fork : CoveredFork sevm.benvStat.fork)
    (nonstatic : sevm.isStatic = false) (keys : ∀ k ∈ frameKeys sevm, U k)
    (lib : some (pre.state.getCode usdcLib).toList = libSem.image)
    (notAdmin : sevm.caller ≠ adminOf pre.state P) (good : (ledger U (pre.state.getStor P)).Good)
    (notRescue : Blanc.Sevm.selector sevm ≠ rescueSelector) :
    (usdcBookS P).step (ledger U (pre.state.getStor P)) sevm =
        some (ledger U (post.state.getStor P)) ∧
      (post.state.getStor P).get implSlot = (pre.state.getStor P).get implSlot ∧
      (post.state.getStor P).get adminSlot = (pre.state.getStor P).get adminSlot ∧
      ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall := by
  obtain ⟨c, dec⟩ := impl_decodes run codeEq fork
  have whole : ∀ fam, ImplStepLaw fam → fam c →
      (usdcBookS P).step (ledger U (pre.state.getStor P)) sevm =
          some (ledger U (post.state.getStor P)) ∧
        (post.state.getStor P).get implSlot = (pre.state.getStor P).get implSlot ∧
        (post.state.getStor P).get adminSlot = (pre.state.getStor P).get adminSlot ∧
        ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
          ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall := fun fam law hc => by
    obtain ⟨step, hi, ha, nodes⟩ :=
      law run codeEq target codeAddr fork nonstatic inj apart keys lib notAdmin c dec hc
    exact ⟨step, hi, ha, fun N chain x hat => (nodes N chain x hat).1⟩
  rcases call_family_cases c with h | h | h | h | h | h | ⟨t, d, v, rfl⟩
  · exact whole _ implStepLaw_famTransfer h
  · exact whole _ impl_signed_law h
  · exact whole _ implStepLaw_famAdmin h
  · exact whole _ impl_view_law (by cases c <;> first | rfl | exact h.elim)
  · exact (impl_initRevert run codeEq target codeAddr fork nonstatic inj apart keys lib notAdmin
      good c dec h).elim
  · exact (impl_initV2Revert run codeEq target codeAddr fork nonstatic inj apart keys lib notAdmin
      good c dec (by cases c <;> first | exact .inl rfl | exact .inr ⟨_, rfl⟩ | exact h.elim)).elim
  · exact (notRescue (decodeCall_rescue dec)).elim

end Blanc.Lift.Usdc
