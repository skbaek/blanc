import Blanc.Lift.ReachLine
import Blanc.Lift.RunPWalk
import Blanc.Lift.InvWalkStep
import Blanc.Lift.UniswapV2Pair.SwapFront

/-! Actual historical token loads and recipient checks before the optimistic transfers. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

section Raw
variable {P : Sevm → Devm → Ninst → Devm → Prop}
  (project : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {T : Conf}
include project

private theorem swap_raw_recipient_join {flag : B256}
    (run : Reach P cert.prog sevm ⟨St b (flag :: R) M G, t_0854_c4, []⟩ T)
    (target : AtExec T) :
    flag ≠ 0 ∧ ∃ gas, Reach P cert.prog sevm ⟨St b R M gas, t_08bf_c4, []⟩ T := by
  unfold t_0854_c4 at run
  obtain ⟨_, run⟩ := rr_dest run target
  obtain ⟨_, step, run⟩ := rr_next run target
  obtain ⟨_, rfl⟩ := ri_push (project step)
  rcases rr_branch run target with ⟨_, _, failed⟩ | ⟨nonzero, gas, run⟩
  · exact (Reach.false_of_execFree (by decide : ExecFreeSet cert.prog [] = true)
      failed target (by decide : t_0859_c4.execFreeIn [] = true)
      (fun _ member => by cases member)).elim
  · exact ⟨nonzero, gas, run⟩

/-- A raw reach through the literal token reads derives both actual recipient checks and
retains the cached token words at the optimistic-transfer branch. Only BAL-none is needed
for the historical SLOAD successors; no success, commitment or guard premise is assumed. -/
theorem swap_raw_recipient_guardsH {r1 r0 len start toWord a1 a0 rho : B256}
    (bal : sevm.benvStat.rules.bal = none)
    (run : Reach P cert.prog sevm
      ⟨St b (r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: rho :: R) M G,
        t_07ef_c3, []⟩ T)
    (target : AtExec T) :
    (b.getStorVal sevm.currentTarget 6).toAdr ≠ toWord.toAdr ∧
    (b.getStorVal sevm.currentTarget 7).toAdr ≠ toWord.toAdr ∧
    ∃ gas, Reach P cert.prog sevm
      ⟨St (afterSloadH sevm (afterSloadH sevm b 6) 7)
        ((b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
         (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
         0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: rho :: R) M gas,
        t_08bf_c4, []⟩ T := by
  have maskWord (word : B256) :
      (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& word = word.toAdr.toB256 :=
    ff20_and_word word
  have recipient : toWord &&& (0xffffffffffffffffffffffffffffffffffffffff : B256) =
      toWord.toAdr.toB256 := by
    rw [B256.and_comm]
    exact ff20_and_word _
  unfold t_07ef_c3 at run
  obtain ⟨_, run⟩ := rr_dest run target
  change Reach _ _ _ ⟨_, swapTokenLoadLine.foldr SFunc.next (.branchTo t_0823_c3 4), []⟩ T at run
  obtain ⟨d, line, run⟩ := Reach.split_nexts project swapTokenLoadLine
    (by intro n member x equal; subst n; simp only [swapTokenLoadLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) run target
  obtain ⟨_, state⟩ := swapTokenLoadLine_invH bal line
  simp only [show Bytes.toB256 [6] = (6 : B256) from rfl,
    show Bytes.toB256 [7] = (7 : B256) from rfl,
    show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255] =
      (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl,
    getStorVal_afterSloadH, maskWord, recipient] at state
  subst d
  rcases rr_branchTo run target with ⟨eq0, _, run⟩ | ⟨jump0, tree, _, lookup, run⟩
  swap
  · rw [show cert.prog[4]? = some t_0854_c4 from rfl] at lookup
    cases lookup
    obtain ⟨nonzero, _, _⟩ := swap_raw_recipient_join project run target
    exact absurd (eq_zero_of_iszero_ne_zero nonzero) jump0
  change Reach _ _ _ ⟨_, swapRecipient1Line.foldr SFunc.next t_0854_c4, []⟩ T at run
  obtain ⟨d, line, run⟩ := Reach.split_nexts project swapRecipient1Line
    (by intro n member x equal; subst n; simp only [swapRecipient1Line,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) run target
  obtain ⟨_, state⟩ := swapRecipient1Line_inv line
  simp only [show Bytes.toB256 [255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255] =
      (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl,
    maskWord, toAdr_toB256] at state
  subst d
  obtain ⟨nonzero, gas, run⟩ := swap_raw_recipient_join project run target
  have ne0 := ne_of_eqCheck_eq_zero eq0
  have ne1 := ne_of_eqCheck_eq_zero (eq_zero_of_iszero_ne_zero nonzero)
  exact ⟨fun equal => ne0 (congrArg Adr.toB256 equal),
    fun equal => ne1 (congrArg Adr.toB256 equal.symm), gas, run⟩

end Raw
end Blanc.Lift.UniswapV2Pair
