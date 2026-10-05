import Blanc.Lift.UniswapV2Pair.MintCanonical
import Blanc.Lift.LocalStorage

/-!
# Canonical mint frame: foreign storage

The mint callee (certificate entry 41) and every entry it reaches are storage-local (the only
external call is `STATICCALL`, no `SELFDESTRUCT`), so a successful raw mint run leaves the
complete storage of every account other than the Pair unchanged.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The mint callee entry and every certificate entry it reaches. -/
def mintCalleeEntries : List Nat :=
  [9, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 41, 56, 58, 59, 60, 62, 65, 66, 68, 69,
    70, 72, 74]

theorem mintCalleeEntries_storLocal : Blanc.Lift.StorLocalSet cert.prog mintCalleeEntries = true := by
  decide +kernel

/-- Every successful raw mint run keeps the complete storage of every foreign account. -/
theorem mint_bytecode_foreign_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a := by
  intro a foreign
  obtain ⟨f, entry, derived⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, calleePost, publicPost, _, callee, _, _, halted, _, stor, _⟩ :=
    mintPc0_return_inv fork selector derived
  have postEq := Outcome.halted.inj halted
  subst postEq
  rw [stor a]
  exact Blanc.Lift.SFunc.Run.foreignStor_of_storLocal mintCalleeEntries_storLocal fork
    (by decide +kernel) (by decide +kernel) (callee.mono Blanc.Lift.StepIn.toRun) (Ne.symm foreign)

/-- The canonical mint frame together with the foreign-storage silence of the same run. -/
theorem mint_bytecode_exact_consumes_own {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (inj : WriterInj (mintTraceUniverse K ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))
    (apart : WriterApart (mintTraceUniverse K ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)) :
    (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) ∧
    (let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      let ctx := writerContext sevm invocation
      let recipient := (Sevm.dataWord sevm 4).toAdr
      sevm.value = 0 ∧ sevm.isStatic = false ∧
      ∃ (out0 out1 outF : Bytes), MintObservedSteps root current sevm out0 out1 outF ∧
        let balance0 := Bytes.toB256 (out0.take 32)
        let balance1 := Bytes.toB256 (out1.take 32)
        let feeTo := (Bytes.toB256 (outF.take 32)).toAdr
        ∃ (views0 views1 viewsF : List StaticViewTurn) (final : Frame) (rets : List ChildReturn)
          (K' : WriterKey → Prop) (liquidity : Nat) (fee : FeeResult) (feeLogs : List Log)
          (added : List PendingLog),
          ExactConsumes (startTyped current ctx (.mint recipient))
            (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
              (.next (feeObservedResult out1) (staticViewTranscript views1 .done)
                (.next (feeObservedResult outF) (staticViewTranscript viewsF .done) .done)))
            { status := .success (encodeWords [liquidity.toB256]), frame := final,
              remaining := .done, childReturns := rets } ∧
          final.checkpoint = current ∧ final.context = ctx ∧
          final.current.state.unlocked = 1 ∧
          (∀ k, K' k → mintTraceUniverse K root k) ∧
          WriterRep K' (post.getStor sevm.currentTarget) final.current.state ∧
          mintFee { current.state with unlocked := 0 } feeTo current.state.reserve0.val
            current.state.reserve1.val = .ok fee ∧
          ((fee.events = [] ∧ feeLogs = []) ∨ ∃ L : B256, L ≠ 0 ∧
            fee.events = [.transfer 0 feeTo L] ∧
            feeLogs = [lpMintRawLog sevm.currentTarget feeTo L]) ∧
          post.logs = b.logs ++ feeLogs ++
            (if fee.state.totalSupply = 0 then
              [lpMintRawLog sevm.currentTarget (0 : B256).toAdr 1000] else []) ++
            [lpMintRawLog sevm.currentTarget recipient liquidity.toB256,
              ⟨sevm.currentTarget, [updateSyncTopic], encodeWords [balance0, balance1]⟩,
              ⟨sevm.currentTarget, [mintEventTopic, sevm.caller.toB256],
                (balance0 - current.state.reserve0.val.toB256).toBytes ++
                  (balance1 - current.state.reserve1.val.toB256).toBytes⟩] ∧
          final.current.logs = current.logs ++ added ∧
          (∃ L : List Log, post.logs = b.logs ++ L ∧
            added.map (PendingLog.rawWith (mintOwnedRaw sevm.currentTarget)) = L.map some) ∧
          post.output = encodeWords [liquidity.toB256] ∧
          (∀ picked ∈ views0 ++ views1 ++ viewsF,
            Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
            picked.1.frame.sevm.currentTarget = sevm.currentTarget ∧
            picked.1.frame.sevm.isStatic = true) ∧
          MintViewProvenance root sevm.currentTarget current.state.token0 views0 ∧
          MintViewProvenance root sevm.currentTarget current.state.token1 views1 ∧
          MintViewProvenance root sevm.currentTarget current.state.factory viewsF) := by
  exact ⟨mint_bytecode_foreign_storage codeEq fork selector run,
    mint_bytecode_exact_consumes invocation rep sem image installed codeEq fork selector run
      inj apart⟩

end Blanc.Lift.UniswapV2Pair
