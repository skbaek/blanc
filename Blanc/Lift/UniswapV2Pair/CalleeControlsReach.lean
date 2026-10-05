import Blanc.Lift.UniswapV2Pair.CalleeControls
import Blanc.Lift.UniswapV2Pair.Creation.DeployInit

/-!
# U6: premise-free `sync` liveness is false on the configured family

The configured family `ConfiguredWorld` is what the Pair's actual deployment and
initialization produce (U8): the certified runtime installed at `pair`, and at `pair` exactly
the storage `initializedStor` that `initialize` writes over the constructor's storage
(`initialize_reaches_configured`, from the same raw run `pair_initialized` consumes). The token
accounts are pre-existing accounts that deployment and initialization never touch, so their
code is not constrained.

`SyncLive` is the weakest premise-free liveness shape for `sync`: SOME frame at `pair` running
the Pair code on a covered fork with the `sync` selector has SOME successful pc-zero run from
the world. `sync_liveness_refuted` proves `¬ ∀ w pair, ConfiguredWorld w pair → SyncLive w pair`
with the concrete member `reachWorld`: `token0` at `0x2000` holds `revertingCode`, and `0x2000`
is a precompile under none of the covered forks. Any liveness statement that implies `SyncLive`
on the family (in particular every "every accepted `sync` at a configured state has a
successful run" whose accepted frames are nonempty) is refuted with it. The refutation consumes
`sync_no_success_of_reverting_token0`.

Disclosure: the family is defined by the storage image, not by an existential deployment
execution; `initialize_reaches_configured` is the universal direction (every successful
initialize from constructor storage lands in the family). No initialize execution is built.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc.Lift.UniswapV2Pair.Creation

/-- A packed address write names the written address. -/
private theorem addressSlotWriteWord_toAdr (raw : B256) (t : Adr) :
    (addressSlotWriteWord raw t.toB256).toAdr = t := by
  have read := addressSlotReadWord_write_of_clean raw t.toB256
    (by rw [addressSlotReadWord_eq_toAdr_toB256, toAdr_toB256])
  rw [addressSlotReadWord_eq_toAdr_toB256] at read
  have adr := congrArg B256.toAdr read
  rw [toAdr_toB256, toAdr_toB256] at adr
  exact adr

/-- The Pair storage after deployment by `factory` at `self` and `initialize(token0, token1)`:
the constructor's storage with the two packed token writes. -/
def initializedStor (chainWord : B256) (self factory token0 token1 : Adr) : Stor :=
  let s := ctorStor chainWord self factory Stor.empty
  (s.set 6 (addressSlotWriteWord (s.get 6) token0.toB256)).set 7
    (addressSlotWriteWord (s.get 7) token1.toB256)

/-- The configured family: the certified runtime at `pair`, and the storage deployment and
initialization produce there. -/
def ConfiguredWorld (w : Devm) (pair : Adr) : Prop :=
  w.getCode pair = code ∧
    ∃ chainWord factory token0 token1, w.getStor pair = initializedStor chainWord pair factory token0 token1

/-- Premise-free `sync` liveness at a world: some `sync` frame at `pair` succeeds. -/
def SyncLive (w : Devm) (pair : Adr) : Prop :=
  ∃ (sevm : Sevm) (G : Nat) (post : Devm), sevm.currentTarget = pair ∧ sevm.code = code ∧
    CoveredFork sevm.benvStat.fork ∧ Blanc.Sevm.selector sevm = 0xfff6cae9 ∧
    Nonempty (Exec 0 sevm (St w [] Mem.empty G) (.ok post))

/-- **Deployment and initialization reach the family.** A successful pc-zero `initialize` run
(the run `pair_initialized` consumes) at a pair holding the certified runtime and the
constructor's storage ends in a configured world. -/
theorem initialize_reaches_configured {chainWord : B256} {factory : Adr}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (hstor : Devm.getStor b sevm.currentTarget =
      ctorStor chainWord sevm.currentTarget factory Stor.empty)
    (installed : b.getCode sevm.currentTarget = code)
    (representable : sevm.data.length < 2 ^ 256) (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ConfiguredWorld post sevm.currentTarget := by
  have rep := ctorStor_rep chainWord sevm.currentTarget factory
  rw [← hstor] at rep
  obtain ⟨_, _, _, _, _, result⟩ :=
    initialize_bytecode_refines_source (current := ⟨State.empty factory
      (domainSeparator chainWord sevm.currentTarget), [], []⟩) (invocation := [])
      rep representable freshOutput codeEq fork selector run
  refine ⟨?_, chainWord, factory, initializeToken0 sevm, initializeToken1 sevm, ?_⟩
  · have kept := Exec.preserves_getCode run sevm.currentTarget
      (by
        change (b.getCode sevm.currentTarget).toList ≠ []
        rw [installed, ByteArray.toList_eq_toList_data]
        decide)
    exact kept.trans installed
  · have storage := result.storage
    rw [storage]
    unfold initializePublicStorage initializedStor
    change ((Devm.getStor b sevm.currentTarget).set 6 (addressSlotWriteWord
      ((Devm.getStor b sevm.currentTarget).get 6) (initializeToken0 sevm).toB256)).set 7
      (addressSlotWriteWord ((Devm.getStor b sevm.currentTarget).get 7)
        (initializeToken1 sevm).toB256) = _
    rw [hstor]

/-- The member's pair and reverting `token0`. -/
private def reachPair : Adr := 0x1000
private def reachToken : Adr := 0x2000

/-- A configured world whose `token0` holds `revertingCode`. -/
def reachWorld : Devm :=
  (default : Devm).withState
    ((((default : Devm).state.setStor reachPair
      (initializedStor 1 reachPair 0x4000 reachToken 0x3000)).setCode reachPair code).setCode
        reachToken revertingCode)

private theorem reachWorld_acct (a : Adr) : reachWorld.getAcct a =
    ((((default : Devm).state.setStor reachPair
      (initializedStor 1 reachPair 0x4000 reachToken 0x3000)).setCode reachPair code).setCode
        reachToken revertingCode).get a := rfl

/-- **The member is configured**, and its `token0` holds `revertingCode` outside every covered
fork's precompile set. -/
theorem reachWorld_configured :
    ConfiguredWorld reachWorld reachPair ∧
      (reachWorld.getStorVal reachPair 6).toAdr = reachToken ∧
      reachWorld.getCode reachToken = revertingCode ∧
      ∀ f, CoveredFork f → ¬ (Fork.ruleSet f).isPrecomp reachToken := by
  have ne : reachToken ≠ reachPair := by decide
  have pairAcct : reachWorld.getAcct reachPair =
      { (((default : Devm).state.setStor reachPair
          (initializedStor 1 reachPair 0x4000 reachToken 0x3000)).get reachPair) with
        code := code } := by
    rw [reachWorld_acct]
    unfold State.setCode
    rw [State.get_set_ne _ ne, State.get_set_self]
  have pairStor : reachWorld.getStor reachPair = initializedStor 1 reachPair 0x4000 reachToken 0x3000 := by
    unfold Devm.getStor
    rw [pairAcct]
    change (((default : Devm).state.setStor reachPair _).get reachPair).stor = _
    unfold State.setStor
    rw [State.get_set_self]
  refine ⟨⟨?_, 1, 0x4000, reachToken, 0x3000, pairStor⟩, ?_, ?_, ?_⟩
  · unfold Devm.getCode
    rw [pairAcct]
  · change ((reachWorld.getStor reachPair).get 6).toAdr = reachToken
    rw [pairStor]
    unfold initializedStor
    rw [Stor.get_set_ne _ (by decide : (7 : B256) ≠ 6), Stor.get_set_self,
      addressSlotWriteWord_toAdr]
  · unfold Devm.getCode
    rw [reachWorld_acct]
    unfold State.setCode
    rw [State.get_set_self]
  · intro f covered
    exact covered.cases (motive := fun f => ¬ (Fork.ruleSet f).isPrecomp reachToken)
      (by decide) (by decide) (by decide) (by decide)

/-- **Premise-free `sync` liveness is false on the configured family.** -/
theorem sync_liveness_refuted :
    ¬ ∀ w pair, ConfiguredWorld w pair → SyncLive w pair := by
  intro live
  obtain ⟨configured, token0, tokenCode, notPrecompile⟩ := reachWorld_configured
  obtain ⟨sevm, G, post, target, codeEq, fork, selector, ⟨run⟩⟩ := live _ _ configured
  rw [← target] at token0
  exact sync_no_success_of_reverting_token0 codeEq fork selector token0 tokenCode
    (notPrecompile _ fork) run

end Blanc.Lift.UniswapV2Pair
