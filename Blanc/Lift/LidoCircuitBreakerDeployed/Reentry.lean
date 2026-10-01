import Blanc.Lift.LidoCircuitBreakerDeployed.History
import Blanc.Lift.LidoCircuitBreakerDeployed.ReentryCheck
import Blanc.ExecutionEntryAccounting
import Blanc.LockExclusion

/-!
# The Registry invariant at every spawning node of a Lido frame

`pause` (entry 13) is the only CircuitBreaker code that spawns: one `CALL`
(`pauseFor`) and one `STATICCALL` (`isPaused`); its callee may re-enter the
contract.  The generic entry-invariant ladder (`Blanc/ExecutionEntryAccounting.lean`)
needs, per contract, `RegInv` at every node of a successful frame that decodes an
external instruction (`SpawnEntry`).  This module proves it from the stateful
prefix lift `reach_of_parentPrefix`: any such node is reached from entry `0` by a
synthetic prefix; the dispatcher hands it to a selector wrapper
(`Reach.gotoTree`); every wrapper but `pause`'s is exec-free
(`execFreeEntries_set`); in `pause`, the walk of `entry13_regInv` is replayed on
the prefix up to the `CALL` (`setPauser(t, 0)` crossed as a big-step callee by
`entry32Spec`), and from the `CALL` to the `STATICCALL` only register steps run
(`Reach.lastExec`), after the `CALL`'s child has kept the invariant
(`post_of_call_self_with`).
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker

/-- The deeper-frame hypothesis at a child lying among `R`'s raw frame roots. -/
def CallDeeper (R : Exec.Deriv) (sevm : Sevm) : Prop :=
  ∀ pc' sevm' pre' post' (child : Exec pc' sevm' pre' (.ok post')),
    InRoots R _ _ _ _ child →
    sevm'.depth < sevm.depth →
    lidoSpec.sem.At sevm.currentTarget pc' sevm' pre' →
    CoveredFork sevm'.benvStat.fork →
    lidoSpec.PreWf sevm.currentTarget sevm' pre' →
    lidoSpec.Post sevm.currentTarget sevm' post'

/-- **`RegInv` at the external instructions of the `pause` body (entry 13)**,
reached by a synthetic prefix inside a root derivation `R`: from the entry witness,
well-formed memory and the `setPauser(t, 0)` keys, the `CALL` state and the
`STATICCALL` state keep the Registry invariant. -/
theorem entry13_reach {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {t ra : B256} {xs : List B256} {T : Conf} {entries : List Entry}
    (hfork : CoveredFork sevm.benvStat.fork)
    (ihQ : CallDeeper R sevm)
    (hmem : MemOK M)
    (hw : RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries)
    (hcode : some (b.getCode sevm.currentTarget).toList = lidoSpec.sem.image)
    (ht : canonicalAddress t)
    (hkeys : t ≠ 0 → RegistryKeysFaithful (2 ^ 160) (setPauserKeys entries t 0))
    (run : Reach (StepIn R) prog sevm ⟨St b (t :: ra :: xs) M G, t_05ac_c13, []⟩ T)
    (hT : AtExec T) :
    RegInv (Devm.getStor T.d sevm.currentTarget) := by
  unfold t_05ac_c13 at run
  obtain ⟨G1, run⟩ := rr_dest run hT
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_tload (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  rcases rr_branch run hT with ⟨-, G2, run⟩ | ⟨-, G2, run⟩
  · exact (Reach.false_of_execFree execFreeEntries_set run hT (by decide) (by simp only [List.not_mem_nil,
    IsEmpty.forall_iff, implies_true])).elim
  unfold t_05e8_c13 at run
  obtain ⟨G3, run⟩ := rr_dest run hT
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_tload (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_or (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_tstore hfork (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun s1)
  rw [ff20_and_canonical ht] at run
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  try dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_keccak (StepIn.toRun s1)
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (Bytes.toB256 [3] : B256) = 3 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl] at run
  have hscr := scratch_mapSlot hmem.1 hmem.2 t 3
  rw [hscr.1, hscr.2.1] at run
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_sload hfork (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_caller (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_eq (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  rcases rr_branch run hT with ⟨-, G4, run⟩ | ⟨-, G4, run⟩
  · exact (Reach.false_of_execFree execFreeEntries_set run hT (by decide) (by simp only [List.not_mem_nil,
    IsEmpty.forall_iff, implies_true])).elim
  unfold t_0673_c13 at run
  obtain ⟨G5, run⟩ := rr_dest run hT
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_caller (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_keccak (StepIn.toRun s1)
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (Bytes.toB256 [2] : B256) = 2 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl] at run
  have hscr2 := scratch_mapSlot hscr.2.2.1 hscr.2.2.2 sevm.caller.toB256 2
  rw [hscr2.1, hscr2.2.1] at run
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_sload hfork (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_timestamp (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_lt (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  rcases rr_branch run hT with ⟨-, G6, run⟩ | ⟨-, G6, run⟩
  · exact (Reach.false_of_execFree execFreeEntries_set run hT (by decide) (by simp only [List.not_mem_nil,
    IsEmpty.forall_iff, implies_true])).elim
  unfold t_06ba_c13 at run
  obtain ⟨G7, run⟩ := rr_dest run hT
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_sload hfork (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  try dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨G8, D32, r32, run⟩ :=
    rr_callOver execFreeEntries_set (g := t_0934_c32) rfl (by decide) run hT
  rw [show (Bytes.toB256 [] : B256) = 0 from rfl, show (Bytes.toB256 [3] : B256) = 3 from rfl,
    show (Bytes.toB256 [0x06, 0xce] : B256) = 0x6ce from rfl] at r32
  obtain ⟨hinv2, hcode2, b2, M2, G9, rfl⟩ :=
    (entry32Spec 0x6ce) hfork ⟨hscr2.2.2.1, hscr2.2.2.2⟩
      (by simp only [afterSload_getStor, getStor_setTransVal]; exact hw) ht hkeys
      (r32.mono StepIn.toRun)
  unfold t_06ce_c13 at run
  obtain ⟨G10, run⟩ := rr_dest run hT
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_mload (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  try dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_mload (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨⟨v, hv⟩, hst⟩ := extcodesize_step hfork (StepIn.toRun s1)
  rw [St.self (d := d1) hv rfl] at run
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  rcases rr_branch run hT with ⟨-, G11, run⟩ | ⟨-, G11, run⟩
  · exact (Reach.false_of_execFree execFreeEntries_set run hT (by decide) (by simp only [List.not_mem_nil,
    IsEmpty.forall_iff, implies_true])).elim
  unfold t_0733_c13 at run
  obtain ⟨G12, run⟩ := rr_dest run hT
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun s1)
  obtain ⟨d1', s1, run⟩ := rr_next run hT
  obtain ⟨gw, _, rfl⟩ := ri_gas (StepIn.toRun s1)
  rcases Reach.exec run with rfl | ⟨sf, hcall, run⟩
  · show RegInv (Devm.getStor d1 sevm.currentTarget)
    rw [getStor_eq_of_state_eq hst]
    exact hinv2
  -- the `CALL`: the child is admitted, the caller's state satisfies `Pre`'s pieces
  have hpost : lidoSpec.Post sevm.currentTarget sevm sf := by
    refine ContractSpecSem.post_of_call_self_with (c := lidoSpec) (Q := InRoots R)
      (run := hcall) hfork rfl
      (fun pc' sevm' pre' post' child hq hd hat hf hpw =>
        ihQ pc' sevm' pre' post' child hq hd hat hf hpw)
      (St_pref _ _ _ _) ?_ trivial (zero_le_B256 _) ?_
    · have hc := congrFun hcode2 sevm.currentTarget
      rw [getStor_St_code] at hc
      rw [getStor_St_code, getCode_eq_of_state_eq hst, hc]
      simpa only [afterSload_getCode, getCode_setTransVal] using hcode
    · show RegInv (Devm.getStor d1 sevm.currentTarget)
      rw [getStor_eq_of_state_eq hst]
      exact hinv2
  have hinvF : RegInv (Devm.getStor sf sevm.currentTarget) := hpost.2
  obtain ⟨flag, hsf⟩ := call_stack hfork (StepIn.toRun hcall)
  rw [St.self (d := sf) hsf rfl] at run
  -- from the `CALL` to the `STATICCALL`: register steps only, then nothing external
  exact Reach.lastExec (ok := regSilent) (E := execFreeEntries)
    (Ψ := fun d => RegInv (Devm.getStor d sevm.currentTarget)) execFreeEntries_set
    (fun hn h hΨ => by
      rw [getStor_eq_of_state_eq (Ninst.Run.state_of_regSilent hn (StepIn.toRun h))]
      exact hΨ)
    (fun pop hΨ => by rw [getStor_eq_of_state_eq pop.state.symm]; exact hΨ)
    (fun burn hΨ => by rw [getStor_eq_of_state_eq burn.state.symm]; exact hΨ)
    run hT (by decide) (by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]) hinvF

private instance : Inhabited SFunc := ⟨.undefined⟩

/-- **`RegInv` at the external instructions reached through the `pause` wrapper
(entry 49)**: decoder 7 is crossed as a big-step callee (`entry7_ret`), the body
13 is entered and walked by `entry13_reach`, and nothing after it is external. -/
theorem pause_wrapper_reach {R : Exec.Deriv} {sevm : Sevm} {d : Devm} {T : Conf}
    (hfork : CoveredFork sevm.benvStat.fork) (ihQ : CallDeeper R sevm)
    (hA : EntryAt lidoA sevm d) (hmem : MemOK d.memory)
    (hpre : lidoSpec.Pre sevm.currentTarget sevm d)
    (run : Reach (StepIn R) prog sevm ⟨d, t_0208_c49, []⟩ T) (hT : AtExec T) :
    RegInv (Devm.getStor T.d sevm.currentTarget) := by
  obtain ⟨entries, hwit⟩ : RegInv (Devm.getStor d sevm.currentTarget) := hpre.inv.left rfl
  have hAe := hA entries hwit
  rw [St.self (d := d) rfl rfl] at run
  unfold t_0208_c49 at run
  obtain ⟨G1, run⟩ := rr_dest run hT
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_calldatasize (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨G2, D7, r7, run⟩ :=
    rr_callOver execFreeEntries_set (g := t_0fec_c7) rfl (by decide) run hT
  have r7 := r7.mono StepIn.toRun
  rw [show (Bytes.toB256 [0x04] : B256) = 4 from rfl] at r7
  obtain ⟨ht, G3, rfl⟩ := entry7_ret r7
  unfold t_0216_c49 at run
  obtain ⟨G4, run⟩ := rr_dest run hT
  obtain ⟨d1, s1, run⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨G5, T', r13, rfl⟩ :=
    rr_callInto execFreeEntries_set (g := t_05ac_c13) rfl (by decide) (by simp only [List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]) run hT
  exact entry13_reach (T := T') hfork ihQ hmem hwit hpre.code ht (fun ht0 => hAe.2 ⟨ht0, ht⟩)
    r13 hT

/-- **`RegInv` at every external instruction reached in a Lido frame** entered at
the dispatcher: the dispatcher keeps the state and `MemOK` into one selector
wrapper; only the `pause` wrapper reaches an external instruction. -/
theorem lido_frame_reach {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {T : Conf}
    (hfork : CoveredFork sevm.benvStat.fork) (ihQ : CallDeeper R sevm)
    (hA : EntryAt lidoA sevm pre) (hmem : MemOK pre.memory)
    (hpre : lidoSpec.Pre sevm.currentTarget sevm pre)
    (run : Reach (StepIn R) prog sevm ⟨pre, t_0000_c0, []⟩ T) (hT : AtExec T) :
    RegInv (Devm.getStor T.d sevm.currentTarget) := by
  obtain ⟨k, hk, g, d', hg, ⟨hs, hm⟩, rest⟩ :=
    Reach.gotoTree (ok := instMemSafe) (Ψ := fun d => d.state = pre.state ∧ MemOK d.memory)
      (fun _ => rfl)
      (fun hn h hΨ => by
        obtain ⟨hs', hm'⟩ := memSafe_step hn (StepIn.toRun h)
        exact ⟨hs'.trans hΨ.1, hm' hΨ.2⟩)
      (fun pop hΨ => ⟨pop.state.symm.trans hΨ.1, pop.memory ▸ hΨ.2⟩)
      (fun burn hΨ => ⟨burn.state.symm.trans hΨ.1, burn.memory ▸ hΨ.2⟩)
      run hT entry0_gotoTree ⟨rfl, hmem⟩
  by_cases h49 : k = 49
  · subst h49
    rw [show prog[49]? = some t_0208_c49 from rfl] at hg
    cases hg
    have hA' : EntryAt lidoA sevm d' := by
      unfold EntryAt
      rw [getStor_eq_of_state_eq hs]
      exact hA
    exact pause_wrapper_reach hfork ihQ hA' hm (hpre.state_eq hs) rest hT
  · have hkE : k ∈ execFreeEntries := by
      simp only [wrapperEntries, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      all_goals first | exact absurd rfl h49 | decide
    exact (Reach.false_of_execFree execFreeEntries_set rest hT
      (ExecFreeSet.lookup execFreeEntries_set hkE hg) (by simp only [List.not_mem_nil,
        IsEmpty.forall_iff, implies_true])).elim

/-! ## The three obligations of the entry-invariant ladder -/

/-- The deeper-frame hypothesis, at the children of a Lido frame, from the frame
theorem: a raw frame root of a pc-`0` frame is itself entered at pc `0`. -/
theorem callDeeper_of_admitted {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (hfork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted sevm.currentTarget (lidoFrameEntry lidoA) run) :
    CallDeeper ⟨0, sevm, pre, .ok post, run⟩ sevm := by
  intro pc' sevm' pre' post' child hq _ hat hf hpw
  have hroot : (⟨pc', sevm', pre', .ok post', child⟩ : Exec.Deriv) ∈ Exec.rawFrameRoots run :=
    hq _ (Exec.mem_rawFrameRoots_self child)
  obtain ⟨hpc, -⟩ := LockExclusion.rawFrameRoots_entry run hfork hroot
  dsimp only at hpc
  subst hpc
  exact lidoSpec_preservesAdmitted_mem lidoWriterSpecsM sevm.currentTarget sevm' pre' post' hf
    child (admitted.mono fun r hr => hq r hr) (fun target => (hat.2 target).1) hpw.wf hpw.pre

/-- Lido frames spawn only by `CALL`/`STATICCALL` (the certificate cursor). -/
theorem lido_spawnKinds (ca : Adr) : SpawnKinds ca lidoSpec.sem := by
  intro sevm pre post run hrun _ fork _ node chain x hat
  obtain ⟨κ, -, ok⟩ := cursor_of_parentPrefix cert_check
    (F := ⟨0, sevm, pre, .ok post, run⟩) rfl hrun.1 fork chain
  exact ok.exec_call_or_staticcall hat

/-- **The Lido spawn obligation**: `RegInv` at every spawning node of a successful
Lido frame, from `RegInv` at its entry. -/
theorem lido_spawnEntry (ca : Adr) :
    SpawnEntry ca lidoSpec.sem (lidoFrameEntry lidoA) (fun s => RegInv s) := by
  intro sevm pre post run hrun target fork installed admitted _ hI node chain x hat
  subst target
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix cert_check
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl hrun.1 fork chain
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hat
  have hT : AtExec (κ.conf node.devm) := ⟨x, g, hf⟩
  obtain ⟨hfresh, hloc, hA⟩ := admitted.root rfl
  have hmem : MemOK pre.memory := by rw [hfresh.2]; exact memOK_empty
  have hpre : lidoSpec.Pre sevm.currentTarget sevm pre :=
    ⟨installed.1, trivial, ⟨fun _ => hI, fun h => (h rfl).elim⟩⟩
  have hsevm : node.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  change Reach _ _ _ ⟨pre, t_0000_c0, []⟩ _ at reach
  have h := lido_frame_reach fork (callDeeper_of_admitted run fork admitted) hA hmem hpre
    reach hT
  exact h

/-- A successful Lido frame keeps `RegInv` (the frame theorem). -/
theorem lido_framePreserves (ca : Adr) :
    FramePreserves ca lidoSpec.sem (lidoFrameEntry lidoA) (fun s => RegInv s) := by
  intro sevm pre post run hrun target fork installed admitted _ hI
  subst target
  obtain ⟨hfresh, -, -⟩ := admitted.root rfl
  have hpost := lidoSpec_preservesAdmitted_mem lidoWriterSpecsM sevm.currentTarget sevm pre
    post fork run admitted (fun _ => (installed.2 rfl).1)
    (fun _ => by rw [hfresh.2]; exact Mem.wf_empty)
    ⟨installed.1, trivial, ⟨fun _ => hI, fun h => (h rfl).elim⟩⟩
  exact hpost.inv

end Blanc.Lift.LidoCircuitBreakerDeployed
