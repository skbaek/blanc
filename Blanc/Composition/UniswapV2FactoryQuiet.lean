import Blanc.Lift.UniswapV2Factory.CallShape
import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.Lift.CallChildren
import Blanc.ExecutionSettledOwnCode
import Blanc.Lift.CallRestriction

/-!
# The factory never re-enters an installed Pair (H1)

`pair_history_factoryQuiet`: over a configured history whose checkpoint has the Pair runtime installed at
`pair ≠ 0` and the `UniswapV2Factory` runtime installed at `st₀.factory ≠ systemAddress`, no settled
non-static frame at `pair` has the factory as caller.  This is the `factoryQuiet` hypothesis of
`pair_token_joint` (design amendments A3, A4, A8).

The argument is the weakened caller fold `settledFrames_callerTarget_of_children` with property "static":

* no settled root has the factory as caller (`settledRoots_caller_ne_of_code`, EIP-3607 on the installed
  factory code and `st₀.factory ≠ systemAddress`);
* every settled frame at the factory or at `pair` runs its installed code from pc `0`, and both codes
  stay installed at every settled frame's entry (`settled_ownCode`; neither runtime can `DELEGATECALL` or
  `CALLCODE`);
* a non-static Pair frame calls only as `pair` (its certificate spawns by `CALL`/`STATICCALL` only), and
  `pair` is not the factory (the two installed runtimes differ);
* a non-static factory frame's children are static, at `0`, or at an address with no code when the frame
  began (`factory_children_fresh`), and `pair` is neither.
-/

namespace Blanc.Composition.UniswapV2FactoryQuiet

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift

private theorem own_spawns {ca : Adr} {code : ByteArray} {c : Cert} (checked : Cert.check code c = true)
    (undelegated : ∀ f ∈ c.prog, f.execsSatisfy Xinst.notDelegatecall = true) :
    OwnSpawns ca code := fun hpc hcode _ fork chain hat =>
  let ⟨_, reach, ok⟩ := cursor_of_parentPrefix checked hpc hcode fork chain
  ok.exec_spawn_undelegated (Cursor.execsSatisfy_of_reachable undelegated reach) hat

/-- **H1: the factory never re-enters the Pair.**  Over a configured history whose checkpoint has the
Pair runtime installed at `pair ≠ 0` and the `UniswapV2Factory` runtime installed at
`st₀.factory ≠ systemAddress`, every settled non-static frame at `pair` has a caller other than the
factory. -/
theorem pair_history_factoryQuiet {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {st₀ : UniswapV2Pair.State} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (pairNonzero : pair ≠ 0) (factoryNotSystem : st₀.factory ≠ systemAddress) :
    ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory := by
  have pairCode : checkpoint.state.getCode pair = UniswapV2Pair.code := bytes_eq_of_image installed
  have factoryCode : checkpoint.state.getCode st₀.factory = UniswapV2Factory.code :=
    bytes_eq_of_image factoryInstalled
  have pairNonempty : UniswapV2Pair.code.toList ≠ [] := UniswapV2Pair.pairSem.ne_nil rfl
  have pairNondel : ¬ isValidDelegation UniswapV2Pair.code := UniswapV2Pair.pairSem.not_delegation rfl
  have factoryNonempty : UniswapV2Factory.code.toList ≠ [] := UniswapV2Factory.factorySem.ne_nil rfl
  have factoryNondel : ¬ isValidDelegation UniswapV2Factory.code :=
    UniswapV2Factory.factorySem.not_delegation rfl
  have distinct : pair ≠ st₀.factory := by
    intro same
    have codes : UniswapV2Pair.code = UniswapV2Factory.code := by
      rw [← pairCode, ← factoryCode, same]
    have lengths := UniswapV2Pair.code_toList_length
    rw [codes, UniswapV2Factory.code_toList_length] at lengths
    exact absurd lengths (by decide)
  have pairOwn := trace.settled_ownCode pairNonempty pairNondel
    (own_spawns UniswapV2Pair.cert_check (by decide +kernel)) pairCode
  have factoryOwn := trace.settled_ownCode factoryNonempty factoryNondel
    (own_spawns UniswapV2Factory.cert_check (by decide +kernel)) factoryCode
  have fold := trace.settledFrames_callerTarget_of_children (p := st₀.factory) (ca := pair)
    (Q := fun s => s.isStatic = true)
    (fun R member _ caller =>
      absurd caller (trace.settledRoots_caller_ne_of_code factoryNonempty factoryNondel factoryCode
        factoryNotSystem R member))
    (by
      intro G member which c child target caller
      cases staticG : G.sevm.isStatic
      · obtain ⟨pairAt, pcZero, fork, -⟩ := pairOwn G member
        rcases which with atFactory | atPair
        · obtain ⟨-, pcZero', fork', runsFactory⟩ := factoryOwn G member
          obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
          dsimp only at pcZero' fork' runsFactory atFactory pairAt child ⊢
          subst pcZero'
          rcases UniswapV2Factory.factory_children_fresh run (runsFactory atFactory) fork' c child with
            static | zero | empty
          · exact static
          · exact absurd (target.symm.trans zero) pairNonzero
          · rw [target, pairAt] at empty
            exact absurd empty pairNonempty
        · obtain ⟨-, -, -, runsPair⟩ := pairOwn G member
          obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
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
      · exact Exec.childFrames_isStatic G.run staticG c child)
  intro G member target static caller
  have quiet : G.sevm.isStatic = true := fold G member target caller
  rw [static] at quiet
  cases quiet

end Blanc.Composition.UniswapV2FactoryQuiet
