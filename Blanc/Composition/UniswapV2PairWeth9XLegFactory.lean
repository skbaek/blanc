import Blanc.Composition.UniswapV2FactoryQuiet
import Blanc.Lift.RetainedTargetCompleteness

/-!
# The factory never re-enters an installed Pair, below one frame (derivation level)

The frame-level sibling of `pair_history_factoryQuiet`: below a committed frame that starts at pc `0`
with the Pair runtime installed at `pair ≠ 0` and the factory runtime installed at `factory`, no
committed non-static frame at `pair` has the factory as caller, provided the frame itself does not.
The argument is UF2's, over one derivation: own code below the frame (`Exec.descendantFrames_ownCode`),
the factory's children are static, at `0` or at a codeless address (`factory_children_fresh`), and a
Pair frame calls only as `pair` (`Exec.childFrames_caller_of_callKinds`).

Consumed by the X-leg quiescence of the WETH9 = token1 liveness rows: the nested Pair frames inside the
other token's transfer child are consumed in the locked mode of `PositionalConsumes.segInv`, which
needs this fact (the Pair's `initialize` is not lock-guarded).
-/

namespace Blanc.Composition.UniswapV2PairWeth9XLeg

open Jaune Blanc Blanc.Lift

private theorem own_spawns {ca : Adr} {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true)
    (undelegated : ∀ f ∈ c.prog, f.execsSatisfy Xinst.notDelegatecall = true) :
    OwnSpawns ca code := fun hpc hcode _ fork chain hat =>
  let ⟨_, reach, ok⟩ := cursor_of_parentPrefix checked hpc hcode fork chain
  ok.exec_spawn_undelegated (Cursor.execsSatisfy_of_reachable undelegated reach) hat

/-- The Pair and factory runtimes differ, so their installed addresses do. -/
theorem pair_ne_factory {d : Devm} {pair factory : Adr}
    (pairCode : d.getCode pair = UniswapV2Pair.code)
    (factoryCode : d.getCode factory = UniswapV2Factory.code) : pair ≠ factory := by
  intro same
  have codes : UniswapV2Pair.code = UniswapV2Factory.code := by
    rw [← pairCode, ← factoryCode, same]
  have lengths := UniswapV2Pair.code_toList_length
  rw [codes, UniswapV2Factory.code_toList_length] at lengths
  exact absurd lengths (by decide)

/-- One frame with both runtimes in place: each of its direct children is static whenever it
targets `pair` with the factory as caller. -/
theorem callerChildren_of_ownCode {pair factory : Adr} (pairNonzero : pair ≠ 0)
    (distinct : pair ≠ factory) (G : Exec.Frame)
    (pairOwn : OwnCodeAt pair UniswapV2Pair.code G)
    (factoryOwn : OwnCodeAt factory UniswapV2Factory.code G) :
    CallerChildren factory pair (fun s => s.isStatic = true) G.sevm (Exec.childFrames G.run) := by
  have pairNonempty : UniswapV2Pair.code.toList ≠ [] := UniswapV2Pair.pairSem.ne_nil rfl
  intro which c child target caller
  cases staticG : G.sevm.isStatic
  · obtain ⟨pairAt, pcZero, fork, runsPair⟩ := pairOwn
    rcases which with atFactory | atPair
    · obtain ⟨-, pcZero', fork', runsFactory⟩ := factoryOwn
      obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
      dsimp only at pcZero' fork' runsFactory atFactory pairAt child ⊢
      subst pcZero'
      rcases UniswapV2Factory.factory_children_fresh run (runsFactory atFactory) fork' c child with
        static | zero | empty
      · exact static
      · exact absurd (target.symm.trans zero) pairNonzero
      · rw [target, pairAt] at empty
        exact absurd empty pairNonempty
    · obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
      dsimp only at pcZero fork runsPair atPair child ⊢
      subst pcZero
      have callers := Exec.childFrames_caller_of_callKinds
        (root := ⟨0, sevm, pre, out, run⟩)
        (fun chain hat => by
          obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix UniswapV2Pair.cert_check rfl
            (runsPair atPair) fork chain
          exact ok.exec_call_or_staticcall (Cursor.callOnly_of_reach (by decide +kernel) reach)
            hat)
        run (.refl _) c child
      rw [callers, atPair] at caller
      exact absurd caller distinct
  · exact Exec.childFrames_isStatic G.run staticG c child

/-- **H1 below one frame.**  Below a committed frame `G` that starts at pc `0` on a covered fork with
the Pair runtime at `pair ≠ 0` and the factory runtime at `factory` installed (and running whichever
of the two it targets), every committed frame at `pair` called by the factory is static, provided
`G` itself is. -/
theorem frame_factoryQuiet {pair factory : Adr} (pairNonzero : pair ≠ 0) (G : Exec.Frame)
    (pcZero : G.pc = 0) (fork : CoveredFork G.sevm.benvStat.fork)
    (pairCode : G.pre.getCode pair = UniswapV2Pair.code)
    (factoryCode : G.pre.getCode factory = UniswapV2Factory.code)
    (pairRuns : G.sevm.currentTarget = pair → G.sevm.code = UniswapV2Pair.code)
    (factoryRuns : G.sevm.currentTarget = factory → G.sevm.code = UniswapV2Factory.code)
    (rootQuiet : CallerTarget factory pair (fun s => s.isStatic = true) G.sevm) :
    ∀ F ∈ Exec.committedFrames G.run,
      CallerTarget factory pair (fun s => s.isStatic = true) F.sevm := by
  have distinct := pair_ne_factory pairCode factoryCode
  have pairOwnRoot : OwnCodeAt pair UniswapV2Pair.code G := ⟨pairCode, pcZero, fork, pairRuns⟩
  have factoryOwnRoot : OwnCodeAt factory UniswapV2Factory.code G :=
    ⟨factoryCode, pcZero, fork, factoryRuns⟩
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
  dsimp only at pcZero fork pairCode factoryCode pairRuns factoryRuns rootQuiet ⊢
  subst pcZero
  have pairOwn := Exec.descendantFrames_ownCode (UniswapV2Pair.pairSem.ne_nil rfl)
    (UniswapV2Pair.pairSem.not_delegation rfl) (own_spawns UniswapV2Pair.cert_check (by decide +kernel)) run
    (R := ⟨0, sevm, pre, out, run⟩) (.refl _) rfl fork pairCode pairRuns
  have factoryOwn := Exec.descendantFrames_ownCode (UniswapV2Factory.factorySem.ne_nil rfl)
    (UniswapV2Factory.factorySem.not_delegation rfl) (own_spawns UniswapV2Factory.cert_check (by decide +kernel)) run
    (R := ⟨0, sevm, pre, out, run⟩) (.refl _) rfl fork factoryCode factoryRuns
  have below := Exec.descendantFrames_callerTarget_of_children run
    (callerChildren_of_ownCode pairNonzero distinct ⟨0, sevm, pre, out, run, committed⟩
      pairOwnRoot factoryOwnRoot)
    (fun D member => callerChildren_of_ownCode pairNonzero distinct D
      (pairOwn D member) (factoryOwn D member))
  intro F member
  rcases (Exec.Frame.mem_committedFrames (F := ⟨0, sevm, pre, out, run, committed⟩)).mp member
    with rfl | deeper
  · exact rootQuiet
  · exact below F deeper

end Blanc.Composition.UniswapV2PairWeth9XLeg
