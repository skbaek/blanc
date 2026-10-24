import Blanc.Lift.ReachLine
import Blanc.Lift.SelectorRoute
import Blanc.Lift.UniswapV2Pair.PairNoCallEntries

/-! Raw pc-zero routing to the Pair's six entries that can contain an external instruction. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The six public wrappers whose transitive regions can make external calls. -/
inductive PairCallEntry
  | sync | permit | skim | mint | burn | swap

def PairCallEntry.selector : PairCallEntry → B256
  | .sync => 0xfff6cae9
  | .permit => 0xd505accf
  | .skim => 0xbc25cf77
  | .mint => 0x6a627842
  | .burn => 0x89afcb44
  | .swap => 0x022c0d9f

def PairCallEntry.index : PairCallEntry → Nat
  | .sync => 78
  | .permit => 76
  | .skim => 80
  | .mint => 86
  | .burn => 83
  | .swap => 99

def PairCallEntry.tree : PairCallEntry → SFunc
  | .sync => t_067b_c78
  | .permit => t_05e2_c76
  | .skim => t_059f_c80
  | .mint => t_0469_c86
  | .burn => t_050a_c83
  | .swap => t_01be_c99

theorem PairCallEntry.lookup (entry : PairCallEntry) :
    cert.prog[entry.index]? = some entry.tree := by
  cases entry <;> rfl

private def callEntries : List PairCallEntry := [.sync, .permit, .skim, .mint, .burn, .swap]

private def quietIndex : PairNoCallEntry → Nat
  | .transfer => 85
  | .approve => 96
  | .transferFrom => 93
  | .initialize => 90
  | .decimals => 95
  | .minimumLiquidity => 79
  | .permitTypehash => 94
  | .domainSeparator => 89
  | .price0CumulativeLast => 91
  | .price1CumulativeLast => 92
  | .kLast => 88
  | .factory => 81
  | .token0 => 97
  | .token1 => 75
  | .name => 100
  | .symbol => 84
  | .totalSupply => 98
  | .balanceOf => 87
  | .nonces => 82
  | .allowance => 77
  | .getReserves => 101

private theorem quiet_lookup (entry : PairNoCallEntry) :
    cert.prog[quietIndex entry]? = some entry.tree := by
  cases entry <;> rfl

private def quietEntries : List PairNoCallEntry :=
  [.transfer, .approve, .transferFrom, .initialize, .decimals, .minimumLiquidity,
   .permitTypehash, .domainSeparator, .price0CumulativeLast, .price1CumulativeLast,
   .kLast, .factory, .token0, .token1, .name, .symbol, .totalSupply, .balanceOf,
   .nonces, .allowance, .getReserves]

private def rows : List (B256 × Nat) := t_002b_c0.selPairs ++ t_00f9_c0.selPairs

private theorem row_classify {p : B256 × Nat} (member : p ∈ rows) :
    p ∈ callEntries.map (fun entry => (entry.selector, entry.index)) ∨
      p.2 ∈ quietEntries.map quietIndex := by
  have checked : rows.all (fun p => decide
      (p ∈ callEntries.map (fun entry => (entry.selector, entry.index)) ∨
        p.2 ∈ quietEntries.map quietIndex)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp checked) p member)

section Raw
variable {P : Sevm → Devm → Ninst → Devm → Prop}
  (project : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {b : Devm} {G : Nat} {T : Conf}
include project

/-- The actual pc-zero prefix reaches its selector comparison without a success premise. -/
theorem pair_raw_reach_comparison
    (run : Reach P cert.prog sevm ⟨St b [] Mem.empty G, t_0000_c0, []⟩ T)
    (target : AtExec T) :
    ∃ gas, Reach P cert.prog sevm
      ⟨St b [Blanc.Sevm.selector sevm] getterInitMemory gas,
        if B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42])
          (Blanc.Sevm.selector sevm) = 0 then t_002b_c0 else t_00f9_c0, []⟩ T := by
  change Reach _ _ _ ⟨_, pairInitialLine.foldr SFunc.next
    (.branch t_000c_c0 t_0010_c0), []⟩ T at run
  obtain ⟨d, line, run⟩ := Reach.split_nexts project pairInitialLine
    (by intro n member x equal; subst n; simp only [pairInitialLine, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member) run target
  obtain ⟨_, rfl⟩ := pair_initial_line_state line
  rcases rr_branch run target with ⟨_, _, failed⟩ | ⟨_, _, run⟩
  · exact (Reach.false_of_execFree (by decide : ExecFreeSet cert.prog [] = true)
      failed target (by decide : t_000c_c0.execFreeIn [] = true)
      (fun _ member => by cases member)).elim
  obtain ⟨_, run⟩ := rr_dest run target
  change Reach _ _ _ ⟨_, pairSizeLine.foldr SFunc.next
    (.branch t_001a_c0 t_01b9_c0), []⟩ T at run
  obtain ⟨d, line, run⟩ := Reach.split_nexts project pairSizeLine
    (by intro n member x equal; subst n; simp only [pairSizeLine, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member) run target
  obtain ⟨_, rfl⟩ := pair_size_line_state line
  rcases rr_branch run target with ⟨_, _, run⟩ | ⟨_, _, failed⟩
  swap
  · exact (Reach.false_of_execFree (by decide : ExecFreeSet cert.prog [] = true)
      failed target (by decide : t_01b9_c0.execFreeIn [] = true)
      (fun _ member => by cases member)).elim
  change Reach _ _ _ ⟨_, pairSelectorLine.foldr SFunc.next
    (.branch t_002b_c0 t_00f9_c0), []⟩ T at run
  obtain ⟨d, line, run⟩ := Reach.split_nexts project pairSelectorLine
    (by intro n member x equal; subst n; simp only [pairSelectorLine, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member) run target
  obtain ⟨_, rfl⟩ := pair_selector_line_state rfl line
  rcases rr_branch run target with ⟨zero, gas, run⟩ | ⟨nonzero, gas, run⟩
  · exact ⟨gas, by simpa only [zero, ite_true] using run⟩
  · exact ⟨gas, by simpa only [ite_eq_right nonzero] using run⟩

/-- Every raw reach from pc zero to an external instruction passes through one of the six
call-capable public wrappers. The selected wrapper retains the actual world, initialized
memory, selector and empty continuation stack; no success or commitment is assumed. -/
theorem pair_raw_reach_call_selector
    (run : Reach P cert.prog sevm ⟨St b [] Mem.empty G, t_0000_c0, []⟩ T)
    (target : AtExec T) :
    ∃ entry : PairCallEntry, Blanc.Sevm.selector sevm = entry.selector ∧
      ∃ gas, Reach P cert.prog sevm
        ⟨St b [entry.selector] getterInitMemory gas, entry.tree, []⟩ T := by
  obtain ⟨gas, run⟩ := pair_raw_reach_comparison project run target
  let f := if B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42])
    (Blanc.Sevm.selector sevm) = 0 then t_002b_c0 else t_00f9_c0
  change Reach _ _ _ ⟨_, f, []⟩ T at run
  cases walk : f.selWalk (Blanc.Sevm.selector sevm) with
  | inl pair =>
    obtain ⟨c, j⟩ := pair
    have member := SFunc.selWalk_mem_pairs walk
    have inRows : (c, j) ∈ rows := by
      dsimp only [f] at member
      split at member
      · exact List.mem_append_left _ member
      · exact List.mem_append_right _ member
    obtain ⟨selector, g, gas, lookup, run⟩ := Reach.selWalk_inl project walk run target
    rcases row_classify inRows with active | quiet
    · obtain ⟨entry, _, equal⟩ := List.mem_map.mp active
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      rw [entry.lookup] at lookup
      cases lookup
      exact ⟨entry, selector, gas, selector ▸ run⟩
    · obtain ⟨entry, _, equal⟩ := List.mem_map.mp quiet
      change quietIndex entry = j at equal
      rw [← equal, quiet_lookup entry] at lookup
      cases lookup
      exact (Reach.false_of_execFree entry.region_closed run target entry.tree_free
        (fun _ member => by cases member)).elim
  | inr leaf =>
    have member := SFunc.selWalk_mem_leaves walk
    have inLeaves : leaf ∈ t_002b_c0.selLeaves ++ t_00f9_c0.selLeaves := by
      dsimp only [f] at member
      split at member
      · exact List.mem_append_left _ member
      · exact List.mem_append_right _ member
    have leaves : (t_002b_c0.selLeaves ++ t_00f9_c0.selLeaves).all
        (fun f => f.execFreeIn [32]) = true := by decide
    have free := (List.all_eq_true.mp leaves) leaf inLeaves
    obtain ⟨_, run⟩ := Reach.selWalk_inr project walk run target
    exact (Reach.false_of_execFree (by decide : ExecFreeSet cert.prog [32] = true)
      run target free (fun _ member => by cases member)).elim

end Raw
end Blanc.Lift.UniswapV2Pair
