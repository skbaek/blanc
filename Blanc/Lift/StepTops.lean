import Blanc.Lift.SymTransfer
import Blanc.StaticCallStorage

/-!
# The concrete top word of more instructions, and storage kept by a step

Companions of `Blanc/Lift/SymTransfer.lean`'s `run_*_top`: the word `CALLER`, `ADDRESS`,
`CALLDATALOAD`, `NOT`, `SHL`, `EXP`, `KECCAK256` and `SLOAD` leave on top, and the storage kept by
every successful step that is neither `SSTORE` nor a call or creation other than `STATICCALL`
(`Ninst.Run.getStor_of_storKeep`).  Contract-neutral.
-/

namespace Blanc.Lift.SymTransfer

open Jaune

variable {sevm : Sevm} {d d' : Devm} {x y : B256} {rest : List B256}

theorem run_caller_top (run : Ninst.Run sevm d (.reg .caller) d') :
    d'.stack = sevm.caller.toB256 :: d.stack := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  have h := (Devm.pushBurn_of_pushItem run).stack
  simpa only [Stack.Push, Split, List.singleton_append, List.cons_append, List.nil_append] using h

theorem run_address_top (run : Ninst.Run sevm d (.reg .address) d') :
    d'.stack = sevm.currentTarget.toB256 :: d.stack := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  have h := (Devm.pushBurn_of_pushItem run).stack
  simpa only [Stack.Push, Split, List.singleton_append, List.cons_append, List.nil_append] using h

theorem run_not_top (run : Ninst.Run sevm d (.reg .not) d') (hs : d.stack = x :: rest) :
    d'.stack = (~~~ x) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact unary_top run hs

theorem run_shl_top (run : Ninst.Run sevm d (.reg .shl) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = (y <<< x.toNat) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

/-- Pop one word, then continue: the popped word is the old top. -/
private theorem pop_head {d d1 : Devm} {w : B256} (h : Devm.pop d = .ok ⟨w, d1⟩)
    (hs : d.stack = x :: rest) : w = x ∧ d1.stack = rest ∧ d1.memory = d.memory := by
  have hp := Devm.pop_of_pop h
  have hs1 := hp.stack
  simp only [Stack.Pop, Split, List.cons_append, List.nil_append] at hs1
  rw [hs] at hs1
  simp only [List.cons.injEq] at hs1
  exact ⟨hs1.1.symm, hs1.2.symm, hp.memory.symm⟩

theorem run_exp_top (run : Ninst.Run sevm d (.reg .exp) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = B256.bexp x y :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  obtain ⟨⟨a, d1⟩, h1, e1⟩ := Except.bind_eq_ok run
  obtain ⟨⟨b, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok e2
  obtain ⟨rfl, hs1, -⟩ := pop_head h1 hs
  obtain ⟨rfl, hs2, -⟩ := pop_head h2 hs1
  have hp := (Devm.push_of_push h4).stack
  rw [hp, ← (Devm.burn_of_chargeGas h3).stack, hs2]
  rfl

theorem run_calldataload_top (run : Ninst.Run sevm d (.reg .calldataload) d')
    (hs : d.stack = x :: rest) :
    d'.stack = Bytes.toB256 (sevm.data.sliceD x.toNat 32 0) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  obtain ⟨⟨a, d1⟩, h1, e1⟩ := Except.bind_eq_ok run
  obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok e1
  obtain ⟨rfl, hs1, -⟩ := pop_head h1 hs
  have hp := (Devm.push_of_push h3).stack
  rw [hp, ← (Devm.burn_of_chargeGas h2).stack, hs1]
  rfl

/-- `KECCAK256` hashes the memory window its two operands name. -/
theorem run_keccak256_top (run : Ninst.Run sevm d (.reg .keccak256) d')
    (hs : d.stack = x :: y :: rest) :
    d'.stack = Bytes.keccak (d.memory.data.sliceD x.toNat y.toNat 0) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok run
  obtain ⟨⟨n, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok e2
  obtain ⟨a, hp1, hi⟩ := Devm.pop_of_popToNat_val h1
  obtain ⟨b, hp2, hn⟩ := Devm.pop_of_popToNat_val h2
  have hs1 := hp1.stack
  have hs2 := hp2.stack
  simp only [Stack.Pop, Split, List.cons_append, List.nil_append] at hs1 hs2
  rw [hs] at hs1
  simp only [List.cons.injEq] at hs1
  obtain ⟨rfl, hs1⟩ := hs1
  rw [← hs1] at hs2
  simp only [List.cons.injEq] at hs2
  obtain ⟨rfl, hs2⟩ := hs2
  subst hi hn
  have hp := (Devm.push_of_push h4).stack
  have hb := Devm.burn_of_chargeGas h3
  rw [hp]
  show Bytes.keccak (d3.memory.data.sliceD _ _ 0) :: (d3.withMemory _).stack = _
  rw [← hb.memory, ← hp2.memory, ← hp1.memory]
  show _ :: d3.stack = _
  rw [← hb.stack, ← hs2]

/-- `SLOAD` pushes the executing account's word at its operand. -/
theorem run_sload_top (run : Ninst.Run sevm d (.reg .sload) d') (hs : d.stack = x :: rest) :
    d'.stack = d.getStorVal sevm.currentTarget x :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  obtain ⟨⟨a, d1⟩, h1, e1⟩ := Except.bind_eq_ok run
  obtain ⟨rfl, hs1, -⟩ := pop_head h1 hs
  obtain ⟨d2, hst, h3⟩ : ∃ d2, (d2.state = d1.state ∧ d2.stack = d1.stack) ∧
      Devm.push ((Devm.balReadStorage sevm.benvStat.rules sevm.currentTarget a d2).getStorVal
        sevm.currentTarget a) (Devm.balReadStorage sevm.benvStat.rules sevm.currentTarget a d2) =
        .ok d' := by
    split at e1
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok e1
      exact ⟨d2, ⟨(Devm.burn_of_chargeGas h2).state.symm, (Devm.burn_of_chargeGas h2).stack.symm⟩, h3⟩
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok e1
      exact ⟨d2, ⟨(Devm.burn_of_chargeGas h2).state.symm, (Devm.burn_of_chargeGas h2).stack.symm⟩, h3⟩
  have hp := (Devm.push_of_push h3).stack
  rw [hp]
  show _ :: d2.stack = _
  rw [hst.2, hs1]
  have e1 := (Devm.pop_of_pop h1).state
  congr 1
  show (d2.state.get sevm.currentTarget).stor.get a = (d.state.get sevm.currentTarget).stor.get a
  rw [hst.1, ← e1]

/-- **A step that is neither `SSTORE` nor a call or creation other than `STATICCALL` keeps the
executing account's storage** (and every other account's).  `PUSH` is `Ninst.Run.getStor_push`. -/
theorem Ninst.Run.getStor_of_storKeep {n : Ninst} (hfork : CoveredFork sevm.benvStat.fork)
    (hn : (∃ r, n = .reg r ∧ r ≠ .sstore) ∨ n = .exec .staticcall)
    (run : Ninst.Run sevm d n d') : Devm.getStor d' = Devm.getStor d := by
  rcases hn with ⟨r, rfl, hr⟩ | rfl
  · rcases of_run_reg run with ⟨pc, rrun⟩
    exact (Rinst.preserves_stor hr rrun).symm
  · exact (Ninst.staticcall_inv_getStor_exact hfork run).symm

theorem Ninst.Run.getStor_push {bs : Bytes} {fits : bs.length ≤ 32}
    (run : Ninst.Run sevm d (.push bs fits) d') : Devm.getStor d' = Devm.getStor d := by
  have h := (Devm.pushBurn_of_run (Ninst.run_push_eq run)).state
  funext a
  show (d'.state.get a).stor = (d.state.get a).stor
  rw [h]

end Blanc.Lift.SymTransfer
