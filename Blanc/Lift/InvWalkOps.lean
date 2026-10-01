import Blanc.Lift.InvWalk
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.CopyLoop
import Blanc.Lift.Silent

/-!
# Inversion step lemmas for stack, environment and memory operations

Companions to `Blanc/Lift/ExactWalk.lean` and `Blanc/Lift/ExactWalkOps.lean` for
inverting successful single-step execution: binary operations (`SUB`, `GT`, `MUL`,
`DIV`, `MOD`, `OR`, `XOR`, `EXP`, `SHL`, `SHR`, `BYTE`), unary `NOT`, environment pushes
(`CALLVALUE`, `CALLDATASIZE`, `RETURNDATASIZE`, `GAS`, `CALLDATALOAD`), and
memory operations (`MLOAD`, `MSTORE`, `MSTORE8`, `CALLDATACOPY`, `CODECOPY`, with
numeral-offset forms), `ri_val` to name a successor's top word, the solc word-copy loop
inverted (`ric_copy_step`, `ric_copy_exit`), and the comparison-flag facts a failed guard
leaves (`toNat_le_of_gtCheck_eq_zero`, `toNat_ge_of_ltCheck_eq_zero`,
`eq_zero_of_iszero_ne_zero`).

Each lemma pairs with its forward counterpart: from a successful synthetic run of a
node at an `St b S M G` state, the successor is again an `St` over the base `b`.
-/

namespace Blanc.Lift

open Jaune

@[simp] theorem St.returnData {b : Devm} {S : List B256} {M : Mem} {G : Nat} :
    (St b S M G).returnData = b.returnData := rfl

@[simp] theorem St.memRead_fst {b : Devm} {S : List B256} {M : Mem} {G i sz : Nat} :
    ((St b S M G).memRead i sz).1 = (M.read i sz).1 := rfl

@[simp] theorem St.memRead_snd {b : Devm} {S : List B256} {M : Mem} {G i sz : Nat} :
    ((St b S M G).memRead i sz).2 = St b S (M.read i sz).2 G := rfl

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- Helper for three-operand popping steps. -/
theorem St.of_pop3 {d0 d1 d2 w0 w1 w2 : B256} {d : Devm}
    (h : Devm.PopBurn [w0, w1, w2] (St b (d0 :: d1 :: d2 :: S) M G) d) :
    d0 = w0 ∧ d1 = w1 ∧ d2 = w2 ∧ d = St b S M d.gasLeft := by
  have hs := h.stack
  simp only [Stack.Pop, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at hs
  have e := St.of_stackRel h
  rw [← hs.2.2.2] at e
  exact ⟨hs.1, hs.2.1, hs.2.2.1, e⟩

/-! ## Binary operations -/

/-- `SUB`, inverted. -/
theorem ri_sub {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .sub) d) :
    ∃ G', d = St b ((x - y) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := (· - ·)) (Devm.diffBurn_of_applyBinary run)

/-- `GT`, inverted. -/
theorem ri_gt {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .gt) d) :
    ∃ G', d = St b (B256.gtCheck x y :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := B256.gtCheck) (Devm.diffBurn_of_applyBinary run)

/-- `MUL`, inverted. -/
theorem ri_mul {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .mul) d) :
    ∃ G', d = St b ((x * y) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := (· * ·)) (Devm.diffBurn_of_applyBinary run)

/-- `DIV`, inverted. -/
theorem ri_div {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .div) d) :
    ∃ G', d = St b ((x / y) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := (· / ·)) (Devm.diffBurn_of_applyBinary run)

/-- `MOD`, inverted. -/
theorem ri_mod {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .mod) d) :
    ∃ G', d = St b ((x % y) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := (· % ·)) (Devm.diffBurn_of_applyBinary run)

/-- `OR`, inverted. -/
theorem ri_or {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .or) d) :
    ∃ G', d = St b ((x ||| y) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := (· ||| ·)) (Devm.diffBurn_of_applyBinary run)

/-- `XOR`, inverted. -/
theorem ri_xor {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .xor) d) :
    ∃ G', d = St b ((x ^^^ y) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := (· ^^^ ·)) (Devm.diffBurn_of_applyBinary run)

/-- `SHL`, inverted. -/
theorem ri_shl {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .shl) d) :
    ∃ G', d = St b ((y <<< x.toNat) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := fun x y => y <<< x.toNat) (Devm.diffBurn_of_applyBinary run)

/-- `SHR`, inverted. -/
theorem ri_shr {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .shr) d) :
    ∃ G', d = St b ((y >>> x.toNat) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := fun x y => y >>> x.toNat) (Devm.diffBurn_of_applyBinary run)

/-- `BYTE`, inverted. -/
theorem ri_byte {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .byte) d) :
    ∃ G', d = St b ((List.getD y.toBytes x.toNat 0).toB256 :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := fun x y => (List.getD y.toBytes x.toNat 0).toB256) (Devm.diffBurn_of_applyBinary run)

/-- `EXP`, inverted. -/
theorem ri_exp {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .exp) d) :
    ∃ G', d = St b (B256.bexp x y :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨base, s₁⟩, h1, run'⟩
  rcases Except.bind_eq_ok run' with ⟨⟨exponent, s₂⟩, h2, run''⟩
  rcases Except.bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  have p1 := Devm.pop_of_pop h1
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  have hp := Devm.push_of_push h4
  have hdb : Devm.DiffBurn [base, exponent] [B256.bexp base exponent] (St b (x :: y :: S) M G) d :=
    Devm.diffBurn_of_pop_of_pushBurn
      (Devm.pop_append p1 p2)
      (Devm.pushBurn_of_burn_of_push hb hp)
  exact St.of_diff (v := B256.bexp) ⟨base, exponent, hdb⟩

/-! ## Unary operations -/

/-- `NOT`, inverted. -/
theorem ri_not {x : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: S) M G) (.reg .not) d) :
    ∃ G', d = St b ((~~~ x) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff1 (v := (~~~ ·)) (Devm.diffBurn_of_applyUnary run)

/-! ## Environment pushes -/

/-- `CALLVALUE`, inverted. -/
theorem ri_callvalue {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg .callvalue) d) :
    ∃ G', d = St b (sevm.value :: S) M G' := by
  have hp := of_run_callvalue h
  have hs : d.stack = sevm.value :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `CALLDATASIZE`, inverted. -/
theorem ri_calldatasize {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg .calldatasize) d) :
    ∃ G', d = St b (sevm.data.length.toB256 :: S) M G' := by
  have hp := of_run_calldatasize h
  have hs : d.stack = sevm.data.length.toB256 :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `RETURNDATASIZE`, inverted. -/
theorem ri_returndatasize {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg .returndatasize) d) :
    ∃ G', d = St b (b.returnData.length.toB256 :: S) M G' := by
  have hp := of_run_returndatasize_val h
  have hs : d.stack = b.returnData.length.toB256 :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.returnData, St.stack, List.cons_append, List.nil_append] using
      this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `GAS`, inverted. -/
theorem ri_gas {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg .gas) d) :
    ∃ w G', d = St b (w :: S) M G' := by
  obtain ⟨w, hp⟩ := of_run_gas h
  have hs : d.stack = w :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨w, _, e⟩

/-- `CALLDATALOAD`, inverted. -/
theorem ri_calldataload {x : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: S) M G) (.reg .calldataload) d) :
    ∃ G', d = St b (Sevm.dataWord sevm x :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  have hpop := Devm.pop_of_pop h1
  have hb := Devm.burn_of_chargeGas h2
  have hpush : Devm.Push [Sevm.dataWord sevm si] s₂ d := Devm.push_of_push run₂
  have hdb : Devm.DiffBurn [si] [Sevm.dataWord sevm si] (St b (x :: S) M G) d :=
    Devm.diffBurn_of_pop_of_pushBurn hpop (Devm.pushBurn_of_burn_of_push hb hpush)
  exact St.of_diff1 (v := Sevm.dataWord sevm) ⟨si, hdb⟩

/-! ## Memory operations -/

/-- `MLOAD`, inverted. -/
theorem ri_mload {i : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: S) M G) (.reg .mload) d) :
    ∃ G', d = St b (Bytes.toB256 (M.read i.toNat 32).1 :: S) (M.read i.toNat 32).2 G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have hb := Devm.burn_of_chargeGas h2
  have hpb := Devm.popBurn_of_pop_of_burn p1 hb
  obtain ⟨rfl, hs₂⟩ := St.of_pop1 hpb
  rw [hs₂] at run₂
  simp only [St.memRead_fst, St.memRead_snd] at run₂
  have hp := Devm.push_of_push run₂
  have hs : d.stack = Bytes.toB256 (M.read i.toNat 32).1 :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel (S := S) (M := (M.read i.toNat 32).2) (G := s₂.gasLeft) hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `MSTORE`, inverted. -/
theorem ri_mstore {i v : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: v :: S) M G) (.reg .mstore) d) :
    ∃ G', d = St b S (M.write i.toNat v.toBytes) G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨i', s₁⟩, h1, run'⟩
  rcases Except.bind_eq_ok run' with ⟨⟨v', s₂⟩, h2, run''⟩
  rcases Except.bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  have hpb := Devm.popBurn_of_pop_of_burn (Devm.pop_append p1 p2) hb
  obtain ⟨rfl, rfl, hs₃⟩ := St.of_pop2 hpb
  rw [hs₃] at eq
  exact ⟨_, eq.symm⟩

/-- `MSTORE8`, inverted. -/
theorem ri_mstore8 {i v : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: v :: S) M G) (.reg .mstore8) d) :
    ∃ G', d = St b S (M.write i.toNat [v.2.2.toUInt8]) G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨i', s₁⟩, h1, run'⟩
  rcases Except.bind_eq_ok run' with ⟨⟨v', s₂⟩, h2, run''⟩
  rcases Except.bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  have hpb := Devm.popBurn_of_pop_of_burn (Devm.pop_append p1 p2) hb
  obtain ⟨rfl, rfl, hs₃⟩ := St.of_pop2 hpb
  rw [hs₃] at eq
  exact ⟨_, eq.symm⟩

/-- `CALLDATACOPY`, inverted. -/
theorem ri_calldatacopy {di si sz : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (di :: si :: sz :: S) M G) (.reg .calldatacopy) d) :
    ∃ G', d = St b S (M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0)) G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨di', s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨si', s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz', s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popToNat_val h3 with ⟨z, p3, rfl⟩
  have hb := Devm.burn_of_chargeGas h4
  injection h5 with eq
  have hpb := Devm.popBurn_of_pop_of_burn (Devm.pop_append p1 (Devm.pop_append p2 p3)) hb
  obtain ⟨rfl, rfl, rfl, hs₄⟩ := St.of_pop3 hpb
  rw [hs₄] at eq
  exact ⟨_, eq.symm⟩

/-- `CODECOPY`, inverted. -/
theorem ri_codecopy {di ci sz : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (di :: ci :: sz :: S) M G) (.reg .codecopy) d) :
    ∃ G', d = St b S (M.write di.toNat (sevm.code.sliceD ci.toNat sz.toNat (Linst.toUInt8 .stop))) G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨di', s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨ci', s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz', s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popToNat_val h3 with ⟨z, p3, rfl⟩
  have hb := Devm.burn_of_chargeGas h4
  injection h5 with eq
  have hpb := Devm.popBurn_of_pop_of_burn (Devm.pop_append p1 (Devm.pop_append p2 p3)) hb
  obtain ⟨rfl, rfl, rfl, hs₄⟩ := St.of_pop3 hpb
  rw [hs₄] at eq
  exact ⟨_, eq.symm⟩

/-- `MSTORE` at a numeral address, inverted. -/
theorem ri_mstore_nat {i v : B256} (inat : Nat) {d : Devm} (hi : i.toNat = inat)
    (h : Ninst.Run sevm (St b (i :: v :: S) M G) (.reg .mstore) d) :
    ∃ G', d = St b S (M.write inat v.toBytes) G' := by
  obtain ⟨G', hd⟩ := ri_mstore h
  rw [hi] at hd
  exact ⟨G', hd⟩

/-- `CALLDATACOPY` with numeral destination and size, inverted. -/
theorem ri_calldatacopy_nat {di si sz : B256} (dn zn : Nat) {d : Devm} (hi : di.toNat = dn)
    (hz : sz.toNat = zn)
    (h : Ninst.Run sevm (St b (di :: si :: sz :: S) M G) (.reg .calldatacopy) d) :
    ∃ G', d = St b S (M.write dn (sevm.data.sliceD si.toNat zn 0)) G' := by
  obtain ⟨G', hd⟩ := ri_calldatacopy h
  rw [hi, hz] at hd
  exact ⟨G', hd⟩

/-! ## Naming a successor's top word -/

/-- Name the top of an inverted step's successor: `ri_val (w := v) (by decide) (ri_add s)`
turns a computed top word into the literal `v`. -/
theorem ri_val {b d : Devm} {S : List B256} {M : Mem} {v w : B256} (hv : v = w)
    (h : ∃ G', d = St b (v :: S) M G') : ∃ G', d = St b (w :: S) M G' :=
  hv ▸ h

end Steps

/-! ## The solc word-copy loop, inverted -/

section CopyLoop

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {exit T : SFunc}

/-- One iteration of `copyLoopTree`, inverted (`i < len`): control enters entry `k` with
the destination word stored and the index advanced by 32. -/
theorem ric_copy_step {i src dst len : B256} (hlt : B256.ltCheck i len = 1)
    (hk : fs[k]? = some T) (hkC : k ∉ C)
    (run : SFunc.RunCut fs sevm C
      (St b (i :: src :: dst :: len :: R) M G)
      (copyLoopTree e0 e1 r0 r1 k exit) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b ((Bytes.toB256 [0x20] + i) :: src :: dst :: len :: R)
        (((M.read (i + src).toNat 32).2).write (i + dst).toNat
          (Bytes.toB256 (M.read (i + src).toNat 32).1).toBytes) G')
      T r := by
  unfold copyLoopTree at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (w := len) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (w := i) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  rw [hlt, show B256.eqCheck (1 : B256) 0 = 0 by decide] at run
  rcases ric_branch run with ⟨-, G7, run⟩ | ⟨hw, -⟩
  swap; · exact absurd hw (by decide)
  unfold copyBody at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_dup (w := src) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_dup (w := i) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_dup (w := dst) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_dup (w := i) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push s1
  exact ric_jump hkC hk run

/-- The exit of `copyLoopTree`, inverted (`i ≥ len`): control passes to `exit`. -/
theorem ric_copy_exit {i src dst len : B256} (hlt : B256.ltCheck i len = 0)
    (run : SFunc.RunCut fs sevm C
      (St b (i :: src :: dst :: len :: R) M G)
      (copyLoopTree e0 e1 r0 r1 k exit) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b (i :: src :: dst :: len :: R) M G')
      exit r := by
  unfold copyLoopTree at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (w := len) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (w := i) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  rw [hlt, show B256.eqCheck (0 : B256) 0 = 1 by decide] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, G7, run⟩
  · exact absurd hw (by decide)
  exact ⟨G7, run⟩

end CopyLoop

/-! ## Comparison flags -/

lemma toNat_le_of_gtCheck_eq_zero {x y : B256} (h : B256.gtCheck x y = 0) :
    x.toNat ≤ y.toNat := by
  unfold B256.gtCheck at h; split at h
  · cases h
  · rename_i hngt
    change ¬ y < x at hngt
    rw [B256.lt_iff_toNat_lt_toNat] at hngt
    omega

lemma toNat_ge_of_ltCheck_eq_zero {x y : B256} (h : B256.ltCheck x y = 0) :
    y.toNat ≤ x.toNat := by
  unfold B256.ltCheck at h; split at h
  · cases h
  · rename_i hnlt
    rw [B256.lt_iff_toNat_lt_toNat] at hnlt
    omega

lemma eq_zero_of_iszero_ne_zero {x : B256} (h : B256.eqCheck x 0 ≠ 0) : x = 0 := by
  unfold B256.eqCheck at h; split at h
  · assumption
  · contradiction

end Blanc.Lift

