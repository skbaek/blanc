import Blanc.Lift.StaticSilent
import Blanc.Lift.UniswapV2Pair.StaticViewClassify
import Jaune.MessageExecution

/-!
# The Pair never answers `isValidSignature` (Pair side of A11)

`not_staticAnswered_pair`: no static child message to an account holding the certified Pair
runtime, outside the precompile range, answers calldata that begins with the EIP-1271 selector
`isValidSignature(bytes32,bytes)` (`0x1626ba7e`).  The child runs the Pair's code from program
counter zero on a fresh frame, so `staticView_bytecode_inv` classifies it as one of the Pair's
views, and no view has that selector (`staticView_selector_ne_erc1271`).

The statement is the contract-neutral `NoStaticAnswer` predicate
(`Blanc.Lift.StaticSilent`); the USDC library side takes it as the hypothesis
`hsilent` (amendment A11).  Proved here, in the Pair's stratum, from the moved
U7a proof.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.Lift

/-- No static view of the Pair has the EIP-1271 selector. -/
theorem staticView_selector_ne_erc1271 (v : StaticView) :
    v.selector ≠ 0x1626ba7e := by
  rcases v with ((s | s | s) | s | _ | s | _ | _) <;> (try cases s) <;> decide

/-- **The Pair answers no `isValidSignature` call.**  A static child message to an account
holding the Pair's runtime, whose code address is not a precompile, with calldata beginning
with `0x1626ba7e`, never settles cleanly. -/
theorem not_staticAnswered_pair : NoStaticAnswer code 0x1626ba7e := by
  intro sevm b t input out codeEq notPrecompile fork sel
  rintro ⟨parent, child, xl, dp, na, ccode, gas, -, delegation, filled, process, clean, -⟩
  rcases delegation with ⟨-, hna, hc, hdp⟩ | ⟨d, designated, -, -, -⟩
  swap
  · rw [codeEq] at designated
    rw [show getDelegatedCodeAddress code = none by decide +kernel] at designated
    cases designated
  rw [hna, hc, hdp, codeEq] at process
  generalize hmsg : callMsg sevm parent gas 0 sevm.currentTarget t t true true input
    code false = msg at process
  have hstat : msg.benv.stat = sevm.benvStat := by rw [← hmsg]; rfl
  cases transfer : msg.benvAfterTransfer with
  | error e =>
    have enter : (Jaune.Frame.ofCall msg).enter =
        .done ((Jaune.Frame.ofCall msg).settleMsg (.error e)) := by
      unfold Jaune.Frame.enter Jaune.Frame.ofCall
      rw [transfer]
    unfold ProcessMessage RunFrame at process
    rw [enter] at process
    cases process.2
  | ok benv =>
    have stat := benvAfterTransfer_stat transfer
    have enter := Jaune.MessageExecution.frameEnter_eq_run_afterTransfer_of_notPrecompile msg benv t
      transfer (by rw [← hmsg]; rfl) (by rw [stat, hstat]; exact notPrecompile)
    have process' := process
    unfold ProcessMessage RunFrame at process
    rw [enter] at process
    obtain ⟨raw, slot, -⟩ := process
    subst slot
    obtain ⟨run⟩ := filled
    have commits := Jaune.Frame.raw_commits_of_settlementCommits
      (ProcessMessage.settlementCommits_of_some_ok_clean
        (pc := 0) (sevm := initSevm (msg.withBenv benv)) (pre := initDevm (msg.withBenv benv))
        process' clean)
    cases raw with
    | error e => cases commits
    | ok post =>
      have bstat : benv.stat = sevm.benvStat := stat.trans hstat
      have run' : Exec 0 (initSevm (msg.withBenv benv))
          (St (initDevm (msg.withBenv benv)) [] Mem.empty (msg.withBenv benv).gas) (.ok post) := by
        have e : initDevm (msg.withBenv benv) =
            St (initDevm (msg.withBenv benv)) [] Mem.empty (msg.withBenv benv).gas :=
          St.self rfl rfl
        rw [← e]
        exact run
      obtain ⟨-, -, view, hv⟩ := staticView_bytecode_inv
        (sevm := initSevm (msg.withBenv benv))
        (by rw [← hmsg]; rfl) (by show CoveredFork benv.stat.fork; rw [bstat]; exact fork)
        (by rw [← hmsg]; show (true || sevm.isStatic) = true; rfl) run'
      have hdata : (initSevm (msg.withBenv benv)).data = input := by rw [← hmsg]; rfl
      exact staticView_selector_ne_erc1271 view (hv.symm.trans (sel _ hdata))

end Blanc.Lift.UniswapV2Pair
