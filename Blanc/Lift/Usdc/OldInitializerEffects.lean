import Blanc.Lift.Usdc.ImplV2.Check
import Blanc.Lift.Sound
import Blanc.Lift.RunPWalk
import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkProvenance
import Blanc.Lift.WriteSiteZero
import Blanc.Lift.SolcStorageReturn
import Blanc.Lift.WalkSteps

/-!
# Actual V2 initializeV2 write effects

The original successful fresh PC0 execution supplies the dispatcher, dynamic
ABI decode and compiled initializer route. Its same-provenance instruction
observations classify metadata, bounded modular name-payload and literal-zero
tail stores, and exclude external instructions. Short actual names therefore
preserve an explicitly supplied demanded-zero seed with fixed-key separation.
The only rule premise is `stateGas = none` (historical forks through
`HistFork.stateGas_none`, covered forks through
`CoveredFork.rules_stateGas_none`): the walk reads storage instructions by
their stack shape alone, under either access-list rule.
No historical seed, arbitrary nonzero administrative equality or hash-range
separation is asserted here.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite
open Blanc.Lift.SolcStorageReturn (ri_sload_any ri_sstore_any)

/-- The name length read by the actual V2 dynamic ABI wrapper. -/
def v2InitializerNameLength (sevm : Sevm) : Nat :=
  (Sevm.dataWord sevm (4 + Sevm.dataWord sevm 4)).toNat

/-- The actual initializer writes fixed metadata, literal zero, or an indexed
word of the accepted long name. Payload-key addition is modular. -/
def V2InitializerWriteClass (sevm : Sevm) (pre : Devm) (n : Ninst) : Prop :=
  n = .reg .sstore → ∀ key value rest,
    pre.stack = key :: value :: rest →
    key ∈ ([4, 15, 18] : List B256) ∨ value = 0 ∨
      (31 < v2InitializerNameLength sevm ∧ ∃ i : Nat,
        i < (v2InitializerNameLength sevm + 31) / 32 ∧
        key = ((4 : B256).toBytes).keccak + i.toB256)

private theorem v2Clear_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm pre
      ImplV2.t_54d2_c82 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧
      V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm pre ImplV2.t_54d2_c82 out := by
  refine SFunc.RunP.mono ?_ (SolcStorageClear.runP_zeroStores_noExec
    (back := [0x54, 0xd2]) (exit := [0x54, 0x41])
    (backBound := by decide) (exitBound := by decide) (k := 82)
    (fun step => StepIn.toRun step) rfl run)
  intro s d n d' step
  refine ⟨step.1, ?_, step.2.2⟩
  intro store key value rest stack
  exact Or.inr (Or.inl (step.2.1 store key value rest stack))

private theorem v2ClearEntry_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm pre
      ImplV2.t_54d1_c64 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧
      V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm pre ImplV2.t_54d1_c64 out := by
  unfold ImplV2.t_54d1_c64 at run ⊢
  cases run with
  | dest burn run => exact .dest burn (v2Clear_writeClass run)

private theorem v2NameTail_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm}
    {C : List Nat} {seg : Seg}
    (run : SFunc.RunCutP (StepIn R) ImplV2.cert.prog sevm C pre
      ImplV2.t_5435_c8 seg) :
    ∃ out, seg = .done out ∧ SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧
      V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm pre ImplV2.t_5435_c8 out := by
  cases seg with
  | «at» index middle =>
    unfold ImplV2.t_5435_c8 at run
    cases run with
    | dest burn run =>
      iterate 6
        obtain ⟨next, step, run⟩ := ric_nextP run
      cases run with
      | callRet dest lookup pop callee rest =>
        unfold ImplV2.t_5441_c8 at rest
        cases rest with
        | dest burn rest =>
          iterate 2
            obtain ⟨next, step, rest⟩ := ric_nextP rest
          cases rest
  | done out =>
    refine ⟨out, rfl, ?_⟩
    unfold ImplV2.t_5435_c8 at run ⊢
    cases run with
    | dest burn run =>
      refine .dest burn ?_
      iterate 6
        obtain ⟨next, step, run⟩ := ric_nextP run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      cases run with
      | callHalt dest lookup pop callee =>
        rw [show ImplV2.cert.prog[64]? = some ImplV2.t_54d1_c64 from rfl] at lookup
        cases lookup
        exact .callHalt dest rfl pop (v2ClearEntry_writeClass callee)
      | callRet dest lookup pop callee rest =>
        rw [show ImplV2.cert.prog[64]? = some ImplV2.t_54d1_c64 from rfl] at lookup
        cases lookup
        refine .callRet dest rfl pop (v2ClearEntry_writeClass callee) ?_
        unfold ImplV2.t_5441_c8 at rest ⊢
        cases rest with
        | dest burn rest =>
          refine .dest burn ?_
          iterate 2
            obtain ⟨next, step, rest⟩ := ric_nextP rest
            refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
          cases rest with
          | ret dest pop =>
            exact .ret dest pop

private def V2PayloadNext (sevm : Sevm) (payloadBase : B256) (p i : Nat) (S : List B256) : Seg → Prop
  | .done _ => True
  | .at k d => k = 86 ∧ ∃ b M G,
      d = St b ((p + v2InitializerNameLength sevm).toB256 ::
        (payloadBase + (i + 1).toB256) ::
        (p + 32 * (i + 1)).toB256 :: S) M G ∧
      i + 1 ≤ (v2InitializerNameLength sevm + 31) / 32

private theorem v2Payload_pass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G p i : Nat}
    {S : List B256} {seg : Seg} {payloadBase : B256}
    (hashEq : payloadBase = ((4 : B256).toBytes).keccak)
    (long : 31 < v2InitializerNameLength sevm)
    (lengthBound : v2InitializerNameLength sevm ≤ 2 ^ 32)
    (pointerBound : p ≤ 2 ^ 33)
    (index : i ≤ (v2InitializerNameLength sevm + 31) / 32)
    (run : SFunc.RunCutP (StepIn R) ImplV2.cert.prog sevm [86]
      (St b ((p + v2InitializerNameLength sevm).toB256 ::
        (payloadBase + i.toB256) :: (p + 32 * i).toB256 :: S) M G)
      ImplV2.t_54b6_c86 seg) :
    V2PayloadNext sevm payloadBase p i S seg ∧
    ∀ out : Outcome,
    (∀ b' M' G', seg = .at 86
      (St b' ((p + v2InitializerNameLength sevm).toB256 ::
        (payloadBase + (i + 1).toB256) ::
        (p + 32 * (i + 1)).toB256 :: S) M' G') →
      i + 1 ≤ (v2InitializerNameLength sevm + 31) / 32 →
      SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
        ImplV2.cert.prog sevm
        (St b' ((p + v2InitializerNameLength sevm).toB256 ::
          (payloadBase + (i + 1).toB256) ::
          (p + 32 * (i + 1)).toB256 :: S) M' G') ImplV2.t_54b6_c86 out) →
    (∀ o, seg = .done o → o = out) →

    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm
      (St b ((p + v2InitializerNameLength sevm).toB256 ::
        (payloadBase + i.toB256) :: (p + 32 * i).toB256 :: S) M G)
      ImplV2.t_54b6_c86 out := by
  have endBound : p + v2InitializerNameLength sevm < 2 ^ 256 := by omega
  have cursorBound : p + 32 * i < 2 ^ 256 := by omega
  unfold ImplV2.t_54b6_c86 at run ⊢
  cases run with
  | dest burn run =>
    refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .dest burn (rest out recur done)) ?_
    have shape := St.of_burn burn
    rw [shape] at run ⊢
    obtain ⟨next, step, run⟩ := ric_nextP run
    refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := ric_nextP run
    refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := ric_nextP run
    refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
    obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := ric_nextP run
    refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
    obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := ric_nextP run
    refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    cases run with
    | toSuccCut dest word nonzero member pop =>
      simp only [List.mem_singleton] at member
      omega
    | toSucc dest word nonzero notCut lookup pop run =>
      rw [show ImplV2.cert.prog[8]? = some ImplV2.t_5435_c8 from rfl] at lookup
      cases lookup
      obtain ⟨out', final, tail⟩ := v2NameTail_writeClass run
      refine ⟨by rw [final]; trivial, ?_⟩
      intro out recur done
      have equal := done out' final
      subst out
      exact .toSucc dest word nonzero rfl pop tail
    | toZero dest pop run =>
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .toZero dest pop (rest out recur done)) ?_
      obtain ⟨_, flag, shape⟩ := St.of_pop2 pop
      have compare : B256.gtCheck (p + v2InitializerNameLength sevm).toB256
          (p + 32 * i).toB256 ≠ 0 := by
        intro zero
        rw [zero] at flag
        exact (by decide : B256.eqCheck 0 0 ≠ 0) flag
      have less : (p + 32 * i).toB256 <
          (p + v2InitializerNameLength sevm).toB256 := by
        unfold B256.gtCheck at compare
        split at compare
        · assumption
        · exact (compare rfl).elim
      rw [B256.lt_iff_toNat_lt_toNat,
        B256.toNat_toB256_of_lt cursorBound,
        B256.toNat_toB256_of_lt endBound] at less
      have storeIndex : i < (v2InitializerNameLength sevm + 31) / 32 := by omega
      rw [shape] at run ⊢
      unfold ImplV2.t_54bf_c86 at run ⊢
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, ?_, by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      · intro _ key value rest stack
        have keyEq := (List.cons.inj stack).1
        exact Or.inr (Or.inr ⟨long, i, storeIndex, by rw [← hashEq]; exact keyEq.symm⟩)
      obtain ⟨_, _, rfl⟩ := ri_sstore_any (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
      have cursorNext : Bytes.toB256 [0x20] + (p + 32 * i).toB256 =
          (p + 32 * (i + 1)).toB256 := by
        apply B256.toNat_inj
        rw [B256.toNat_add, B256.toNat_toB256_of_lt cursorBound,
          B256.toNat_toB256_of_lt (by omega),
          show (Bytes.toB256 [0x20]).toNat = 32 from rfl,
          Nat.lo_eq_of_lt (by omega)]
        omega
      rw [cursorNext] at run ⊢
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
      have keyNext : Bytes.toB256 [0x01] +
          (payloadBase + i.toB256) =
          payloadBase + (i + 1).toB256 := by
        apply B256.toNat_inj
        rw [B256.toNat_add, B256.toNat_add, B256.toNat_add,
          B256.toNat_toB256_of_lt (by omega : i < 2 ^ 256),
          B256.toNat_toB256_of_lt (by omega : i + 1 < 2 ^ 256),
          show (Bytes.toB256 [0x01]).toNat = 1 from rfl,
          Nat.add_comm 1, Nat.lo_add_lo]
        congr 1
      rw [keyNext] at run ⊢
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine And.imp_right (fun (rest : ∀ _ : Outcome, _ → _ → _) out recur done => .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ (rest out recur done)) ?_
      obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
      cases run with
      | jumpCut dest member pop =>
        have shape := (St.of_pop1 pop).2
        refine ⟨⟨rfl, _, _, _, shape, by omega⟩, ?_⟩
        intro out recur done
        refine .jump dest rfl pop ?_
        rw [shape]
        exact recur _ _ _ (congrArg (Seg.at 86) shape) (by omega)
      | jump dest notCut lookup pop run =>
        exact (notCut (by simp only [List.mem_singleton])).elim

private theorem v2Payload_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G p i : Nat}
    {S : List B256} {out : Outcome} {payloadBase : B256}
    (hashEq : payloadBase = ((4 : B256).toBytes).keccak)
    (long : 31 < v2InitializerNameLength sevm)
    (lengthBound : v2InitializerNameLength sevm ≤ 2 ^ 32)
    (pointerBound : p ≤ 2 ^ 33)
    (index : i ≤ (v2InitializerNameLength sevm + 31) / 32)
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm
      (St b ((p + v2InitializerNameLength sevm).toB256 ::
        (payloadBase + i.toB256) :: (p + 32 * i).toB256 :: S) M G)
      ImplV2.t_54b6_c86 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm
      (St b ((p + v2InitializerNameLength sevm).toB256 ::
        (payloadBase + i.toB256) :: (p + 32 * i).toB256 :: S) M G)
      ImplV2.t_54b6_c86 out := by
  let observed := fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x
  let start := St b ((p + v2InitializerNameLength sevm).toB256 ::
    (payloadBase + i.toB256) :: (p + 32 * i).toB256 :: S) M G
  let I := fun d => ∃ j b' M' G',
    j ≤ (v2InitializerNameLength sevm + 31) / 32 ∧
    d = St b' ((p + v2InitializerNameLength sevm).toB256 ::
      (payloadBase + j.toB256) :: (p + 32 * j).toB256 :: S) M' G' ∧
    ∀ o, SFunc.RunP observed ImplV2.cert.prog sevm d ImplV2.t_54b6_c86 o →
      SFunc.RunP observed ImplV2.cert.prog sevm start ImplV2.t_54b6_c86 o
  have step : ∀ d, I d → ∀ seg,
      SFunc.RunCutP (StepIn R) ImplV2.cert.prog sevm [86] d ImplV2.t_54b6_c86 seg →
      match seg with
      | .at _ middle => I middle
      | .done o => SFunc.RunP observed ImplV2.cert.prog sevm start ImplV2.t_54b6_c86 o := by
    intro d inv seg cut
    obtain ⟨j, b', M', G', bound, rfl, continuation⟩ := inv
    have pass := v2Payload_pass hashEq long lengthBound pointerBound bound cut
    cases seg with
    | «at» k middle =>
      obtain ⟨rfl, b'', M'', G'', shape, nextBound⟩ := pass.1
      refine ⟨j + 1, b'', M'', G'', nextBound, shape, ?_⟩
      intro o rest
      apply continuation o
      exact pass.2 o (by intro b M G equal _; cases equal; exact rest)
        (by intro o equal; cases equal)
    | done o =>
      apply continuation o
      exact pass.2 o (by intro b M G equal _; cases equal)
        (by intro o equal; cases equal; rfl)
  exact SFunc.RunP.loop (k := 86) rfl I
    (fun o => SFunc.RunP observed ImplV2.cert.prog sevm start ImplV2.t_54b6_c86 o)
    step start out ⟨i, b, M, G, index, rfl, by intro o rest; exact rest⟩ run

private theorem v2NameLong_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G p : Nat}
    {oldEnd : B256} {S : List B256} {out : Outcome}
    (long : 31 < v2InitializerNameLength sevm)
    (lengthBound : v2InitializerNameLength sevm ≤ 2 ^ 32)
    (pointerBound : p ≤ 2 ^ 33)
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm
      (St b (p.toB256 :: ((4 : B256).toBytes).keccak ::
        (v2InitializerNameLength sevm).toB256 :: oldEnd :: 4 :: S) M G)
      ImplV2.t_54a4_c68 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm
      (St b (p.toB256 :: ((4 : B256).toBytes).keccak ::
        (v2InitializerNameLength sevm).toB256 :: oldEnd :: 4 :: S) M G)
      ImplV2.t_54a4_c68 out := by
  generalize hashAt : ((4 : B256).toBytes).keccak = payloadBase at run ⊢
  unfold ImplV2.t_54a4_c68 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    have shape := St.of_burn burn
    rw [shape] at run ⊢
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, ?_, by intro x impossible; cases impossible⟩ ?_
    · intro _ key value rest stack
      have keyEq := (List.cons.inj stack).1
      exact Or.inl (by rw [← keyEq]; exact List.mem_cons_self)
    obtain ⟨_, _, rfl⟩ := ri_sstore_any (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    cases run with
    | toSucc dest word nonzero lookup pop run =>
      have flag := (St.of_pop2 pop).2.1
      have zeroWord := eq_zero_of_iszero_ne_zero (flag ▸ nonzero)
      have zeroNat := congrArg B256.toNat zeroWord
      rw [B256.toNat_toB256_of_lt (by omega), B256.toNat_zero] at zeroNat
      omega
    | toZero dest pop run =>
      refine .toZero dest pop ?_
      have shape := (St.of_pop2 pop).2.2
      rw [shape] at run ⊢
      unfold ImplV2.t_54b3_c68 at run ⊢
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨gas, nextShape⟩ := ri_add (StepIn.toRun step)
      rw [toB256_add_toB256 (a := p) (b := v2InitializerNameLength sevm) (by omega)] at nextShape
      dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at nextShape
      subst next
      have sameHead : ImplV2.t_54b6_c68 = ImplV2.t_54b6_c86 := rfl
      rw [sameHead] at run ⊢
      have zeroWord : (0 : Nat).toB256 = (0 : B256) := rfl
      simpa only [zeroWord, Nat.mul_zero, Nat.add_zero, B256.add_zero] using
        (v2Payload_writeClass (R := R) (sevm := sevm) (p := p) (i := 0)
          (S := oldEnd :: 4 :: S) hashAt.symm long lengthBound pointerBound
          (Nat.zero_le _) (by simpa only [zeroWord, Nat.mul_zero, Nat.add_zero, B256.add_zero] using run))

private theorem v2Name_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G p : Nat}
    {S : List B256} {out : Outcome}
    (lengthBound : v2InitializerNameLength sevm ≤ 2 ^ 32)
    (pointerBound : p ≤ 2 ^ 33)
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm
      (St b ((v2InitializerNameLength sevm).toB256 :: p.toB256 :: 4 :: S) M G)
      ImplV2.t_5445_c68 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm
      (St b ((v2InitializerNameLength sevm).toB256 :: p.toB256 :: 4 :: S) M G)
      ImplV2.t_5445_c68 out := by
  unfold ImplV2.t_5445_c68 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    have shape := St.of_burn burn
    rw [shape] at run ⊢
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, _, _, rfl⟩ := ri_sload_any (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_mul (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_div (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_keccak (StepIn.toRun step)
    clear step
    have hashInput : ((M.write (Bytes.toB256 [0]).toNat (4 : B256).toBytes).read
        (Bytes.toB256 [0]).toNat (Bytes.toB256 [32]).toNat).1 = (4 : B256).toBytes := by
      exact Mem.read_write_zero M (by decide)
    rw [hashInput] at run ⊢
    generalize readMemory : ((M.write (Bytes.toB256 [0]).toNat (B256.toBytes 4)).read
      (Bytes.toB256 [0]).toNat (Bytes.toB256 [32]).toNat).2 = μ at run ⊢
    dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at run ⊢
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_div (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_lt (StepIn.toRun step)
    clear step
    have nextCut := rpw_next run
    clear run
    obtain ⟨next, step, run⟩ := nextCut
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    clear step
    cases run with
    | zero dest pop run =>
      refine .zero dest pop ?_
      have shape := (St.of_pop2 pop).2.2
      rw [shape] at run ⊢
      unfold ImplV2.t_5476_c68 at run ⊢
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_or (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, ?_, by intro x impossible; cases impossible⟩ ?_
      · intro _ key value rest stack
        have keyEq := (List.cons.inj stack).1
        exact Or.inl (by rw [← keyEq]; exact List.mem_cons_self)
      obtain ⟨_, _, rfl⟩ := ri_sstore_any (StepIn.toRun step)
      clear step
      have nextCut := rpw_next run
      clear run
      obtain ⟨next, step, run⟩ := nextCut
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
      clear step
      cases run with
      | jump dest lookup pop run =>
        rw [show ImplV2.cert.prog[8]? = some ImplV2.t_5435_c8 from rfl] at lookup
        cases lookup
        obtain ⟨out', final, tail⟩ :=
          v2NameTail_writeClass (SFunc.runP_iff_runCutP_nil.mp run)
        cases final
        exact .jump dest rfl pop tail
    | succ dest word nonzero pop run =>
      refine .succ dest word nonzero pop ?_
      obtain ⟨_, flag, shape⟩ := St.of_pop2 pop
      have less : Bytes.toB256 [0x1f] < (v2InitializerNameLength sevm).toB256 := by
        have nonzero' := flag ▸ nonzero
        unfold B256.ltCheck at nonzero'
        split at nonzero'
        · assumption
        · exact (nonzero' rfl).elim
      have long : 31 < v2InitializerNameLength sevm := by
        rw [B256.lt_iff_toNat_lt_toNat,
          B256.toNat_toB256_of_lt (by omega)] at less
        exact less
      rw [shape] at run ⊢
      exact v2NameLong_writeClass long lengthBound pointerBound run

/-- The actual domain helper has only memory, hash and environment operations.
No desired domain value is needed for the write classifier. -/
private theorem v2Domain_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm pre
      ImplV2.t_4904_c69 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧
      V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm pre ImplV2.t_4904_c69 out := by
  unfold ImplV2.t_4904_c69 at run ⊢
  cases run with
  | dest burn run =>
    refine SFunc.RunP.dest burn ?_
    iterate 74
      obtain ⟨next, step, run⟩ := rpw_next run
      refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    cases run with
    | ret dest pop => exact SFunc.RunP.ret dest pop

private theorem v2Terminal_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm pre ImplV2.t_36d3_c18 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm pre ImplV2.t_36d3_c18 out := by
  unfold ImplV2.t_36d3_c18 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    rename_i middle
    rw [St.self' middle] at run ⊢
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, ?_, by intro x impossible; cases impossible⟩ ?_
    · intro _ key value rest stack
      have keyEq := (List.cons.inj stack).1
      exact Or.inl (by rw [← keyEq]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    iterate 2
      obtain ⟨next, step, run⟩ := rpw_next run
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    rw [St.self' next] at run ⊢
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, _, _, rfl⟩ := ri_sload_any (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_or (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, ?_, by intro x impossible; cases impossible⟩ ?_
    · intro _ key value rest stack
      have keyEq := (List.cons.inj stack).1
      exact Or.inl (by rw [← keyEq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    cases run with
    | ret dest pop => exact .ret dest pop

private theorem v2DomainCaller_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm pre ImplV2.t_365e_c18 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm pre ImplV2.t_365e_c18 out := by
  unfold ImplV2.t_365e_c18 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    iterate 69
      obtain ⟨next, step, run⟩ := rpw_next run
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    cases run with
    | callHalt dest lookup pop callee =>
      rw [show ImplV2.cert.prog[69]? = some ImplV2.t_4904_c69 from rfl] at lookup
      cases lookup
      exact .callHalt dest rfl pop (v2Domain_writeClass callee)
    | callRet dest lookup pop callee rest =>
      rw [show ImplV2.cert.prog[69]? = some ImplV2.t_4904_c69 from rfl] at lookup
      cases lookup
      exact .callRet dest rfl pop (v2Domain_writeClass callee)
        (v2Terminal_writeClass rest)

private theorem v2Body_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G p : Nat}
    {S : List B256} {out : Outcome}
    (lengthBound : v2InitializerNameLength sevm ≤ 2 ^ 32)
    (pointerBound : p ≤ 2 ^ 33)
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm
      (St b ((v2InitializerNameLength sevm).toB256 :: p.toB256 :: S) M G)
      ImplV2.t_35f6_c18 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm
      (St b ((v2InitializerNameLength sevm).toB256 :: p.toB256 :: S) M G)
      ImplV2.t_35f6_c18 out := by
  unfold ImplV2.t_35f6_c18 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    have shape := St.of_burn burn
    rw [shape] at run ⊢
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, _, _, rfl⟩ := ri_sload_any (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    cases run with
    | zero dest pop run =>
      unfold ImplV2.t_3602_c18 at run
      iterate 37
        obtain ⟨next, step, run⟩ := rpw_next run
      exact (rpw_revert run).elim
    | succ dest word nonzero pop run =>
      refine .succ dest word nonzero pop ?_
      obtain ⟨_, flag, shape⟩ := St.of_pop2 pop
      have versionZero := eq_zero_of_iszero_ne_zero (flag ▸ nonzero)
      rw [shape] at run ⊢
      unfold ImplV2.t_3652_c18 at run ⊢
      cases run with
      | dest burn run =>
        refine .dest burn ?_
        have shape := St.of_burn burn
        rw [shape] at run ⊢
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
        cases run with
        | callHalt dest lookup pop callee =>
          rw [show ImplV2.cert.prog[68]? = some ImplV2.t_5445_c68 from rfl] at lookup
          cases lookup
          refine .callHalt dest rfl pop ?_
          have shape := (St.of_pop1 pop).2
          rw [shape] at callee ⊢
          exact v2Name_writeClass lengthBound pointerBound callee
        | callRet dest lookup pop callee rest =>
          rw [show ImplV2.cert.prog[68]? = some ImplV2.t_5445_c68 from rfl] at lookup
          cases lookup
          refine .callRet dest rfl pop ?_ (v2DomainCaller_writeClass rest)
          have shape := (St.of_pop1 pop).2
          rw [shape] at callee ⊢
          exact v2Name_writeClass lengthBound pointerBound callee

private theorem v2WrapperCall_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G p : Nat}
    {dummy four endpoint : B256} {S : List B256} {out : Outcome}
    (lengthBound : v2InitializerNameLength sevm ≤ 2 ^ 32)
    (pointerBound : p ≤ 2 ^ 33)
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm
      (St b (dummy :: (v2InitializerNameLength sevm).toB256 :: p.toB256 ::
        four :: endpoint :: S) M G) ImplV2.t_0c89_c106 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm
      (St b (dummy :: (v2InitializerNameLength sevm).toB256 :: p.toB256 ::
        four :: endpoint :: S) M G) ImplV2.t_0c89_c106 out := by
  unfold ImplV2.t_0c89_c106 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    have shape := St.of_burn burn
    rw [shape] at run ⊢
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    cases run with
    | callHalt dest lookup pop callee =>
      rw [show ImplV2.cert.prog[18]? = some ImplV2.t_35f6_c18 from rfl] at lookup
      cases lookup
      refine .callHalt dest rfl pop ?_
      have shape := (St.of_pop1 pop).2
      rw [shape] at callee ⊢
      exact v2Body_writeClass lengthBound pointerBound callee
    | callRet dest lookup pop callee rest =>
      rw [show ImplV2.cert.prog[18]? = some ImplV2.t_35f6_c18 from rfl] at lookup
      cases lookup
      unfold ImplV2.t_0470_c106 at rest ⊢
      cases rest with
      | dest burn rest =>
        cases rest with
        | last stop =>
          refine .callRet dest rfl pop ?_ (.dest burn (.last stop))
          have shape := (St.of_pop1 pop).2
          rw [shape] at callee ⊢
          exact v2Body_writeClass lengthBound pointerBound callee

private theorem v2WrapperTail_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {headEnd endpoint : B256} {S : List B256} {out : Outcome}
    (offsetBound : (Sevm.dataWord sevm 4).toNat ≤ 2 ^ 32)
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm
      (St b ((4 + Sevm.dataWord sevm 4) :: headEnd :: 4 :: endpoint :: S) M G)
      ImplV2.t_0c67_c106 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm
      (St b ((4 + Sevm.dataWord sevm 4) :: headEnd :: 4 :: endpoint :: S) M G)
      ImplV2.t_0c67_c106 out := by
  have lengthPointer : (4 + Sevm.dataWord sevm 4).toNat =
      4 + (Sevm.dataWord sevm 4).toNat := by
    rw [B256.toNat_add]
    exact Nat.lo_eq_of_lt (by change 4 + (Sevm.dataWord sevm 4).toNat < 2 ^ 256; omega)
  have payloadPointer : Bytes.toB256 [0x20] + (4 + Sevm.dataWord sevm 4) =
      (36 + (Sevm.dataWord sevm 4).toNat).toB256 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, lengthPointer, B256.toNat_toB256_of_lt (by omega),
      show (Bytes.toB256 [0x20]).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  unfold ImplV2.t_0c67_c106 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    have shape := St.of_burn burn
    rw [shape] at run ⊢
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨gas, nextShape⟩ := ri_add (StepIn.toRun step)
    rw [payloadPointer] at nextShape
    subst next
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_mul (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_or (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    cases run with
    | zero dest pop run =>
      unfold ImplV2.t_0c85_c106 at run
      iterate 2
        obtain ⟨next, step, run⟩ := rpw_next run
      exact (rpw_revert run).elim
    | succ dest word nonzero pop run =>
      refine .succ dest word nonzero pop ?_
      obtain ⟨_, flag, shape⟩ := St.of_pop2 pop
      have zero := eq_zero_of_iszero_ne_zero (flag ▸ nonzero)
      have lengthCmp : B256.gtCheck (Sevm.dataWord sevm (4 + Sevm.dataWord sevm 4))
          (Bytes.toB256 [0x01, 0, 0, 0, 0]) = 0 := by
        unfold B256.gtCheck at zero ⊢
        split_ifs at zero ⊢
        all_goals first
          | rfl
          | exact ((by decide : ((1 : B256) ||| 1) ≠ 0) zero).elim
      have lengthBound : v2InitializerNameLength sevm ≤ 2 ^ 32 :=
        toNat_le_of_gtCheck_eq_zero lengthCmp
      have lengthWord : Sevm.dataWord sevm (4 + Sevm.dataWord sevm 4) =
          (v2InitializerNameLength sevm).toB256 := (toB256_toNat _).symm
      rw [shape] at run ⊢
      rw [lengthWord] at run ⊢
      exact v2WrapperCall_writeClass (p := 36 + (Sevm.dataWord sevm 4).toNat)
        lengthBound (by omega) run

private theorem v2WrapperHead_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {available : B256} {S : List B256} {out : Outcome}
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm
      (St b (available :: 4 :: S) M G) ImplV2.t_0c3a_c106 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm
      (St b (available :: 4 :: S) M G) ImplV2.t_0c3a_c106 out := by
  unfold ImplV2.t_0c3a_c106 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    have shape := St.of_burn burn
    rw [shape] at run ⊢
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    cases run with
    | zero dest pop run =>
      unfold ImplV2.t_0c51_c106 at run
      iterate 2
        obtain ⟨next, step, run⟩ := rpw_next run
      exact (rpw_revert run).elim
    | succ dest word nonzero pop run =>
      refine .succ dest word nonzero pop ?_
      obtain ⟨_, flag, shape⟩ := St.of_pop2 pop
      have offsetBound : (Sevm.dataWord sevm 4).toNat ≤ 2 ^ 32 :=
        toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero (flag ▸ nonzero))
      rw [shape] at run ⊢
      unfold ImplV2.t_0c55_c106 at run ⊢
      cases run with
      | dest burn run =>
        refine .dest burn ?_
        have shape := St.of_burn burn
        rw [shape] at run ⊢
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
        cases run with
        | zero dest pop run =>
          unfold ImplV2.t_0c63_c106 at run
          iterate 2
            obtain ⟨next, step, run⟩ := rpw_next run
          exact (rpw_revert run).elim
        | succ dest word nonzero pop run =>
          refine .succ dest word nonzero pop ?_
          obtain ⟨_, flag, shape⟩ := St.of_pop2 pop
          have lengthWordInBounds := eq_zero_of_iszero_ne_zero (flag ▸ nonzero)
          rw [shape] at run ⊢
          exact v2WrapperTail_writeClass offsetBound run

private theorem v2Wrapper_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm pre ImplV2.t_0c24_c106 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm pre ImplV2.t_0c24_c106 out := by
  rw [St.self' pre] at run ⊢
  unfold ImplV2.t_0c24_c106 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    have shape := St.of_burn burn
    rw [shape] at run ⊢
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_calldatasize (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_lt (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    cases run with
    | zero dest pop run =>
      unfold ImplV2.t_0c36_c106 at run
      iterate 2
        obtain ⟨next, step, run⟩ := rpw_next run
      exact (rpw_revert run).elim
    | succ dest word nonzero pop run =>
      refine .succ dest word nonzero pop ?_
      obtain ⟨_, flag, shape⟩ := St.of_pop2 pop
      have headAvailable := eq_zero_of_iszero_ne_zero (flag ▸ nonzero)
      rw [shape] at run ⊢
      exact v2WrapperHead_writeClass run

private theorem v2Selector_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {S : List B256} {out : Outcome}
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm
      (St b (0xd608ea64 :: S) M G) ImplV2.t_002b_c0 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm
      (St b (0xd608ea64 :: S) M G) ImplV2.t_002b_c0 out := by
  unfold ImplV2.t_002b_c0 at run ⊢
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
  cases run with
  | succ dest word nonzero pop run =>
    have flagZero : B256.gtCheck (Bytes.toB256 [0xc2, 0x37, 0x10, 0x8f]) (0xd608ea64 : B256) = 0 := by decide
    exact (nonzero ((St.of_pop2 pop).2.1.symm.trans flagZero)).elim
  | zero dest pop run =>
    refine .zero dest pop ?_
    have shape := (St.of_pop2 pop).2.2
    rw [shape] at run ⊢
    unfold ImplV2.t_0036_c0 at run ⊢
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun step)
    obtain ⟨next, step, run⟩ := rpw_next run
    refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
    cases run with
    | zero dest pop run =>
      exact ((by decide : B256.gtCheck (Bytes.toB256 [0xe1, 0x56, 0x0f, 0xd3]) (0xd608ea64 : B256) ≠ 0) (St.of_pop2 pop).2.1).elim
    | succ dest word nonzero pop run =>
      refine .succ dest word nonzero pop ?_
      have shape := (St.of_pop2 pop).2.2
      rw [shape] at run ⊢
      unfold ImplV2.t_00a2_c0 at run ⊢
      cases run with
      | dest burn run =>
        refine .dest burn ?_
        have shape := St.of_burn burn
        rw [shape] at run ⊢
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun step)
        obtain ⟨next, step, run⟩ := rpw_next run
        refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
        cases run with
        | succ dest word nonzero pop run =>
          have flagZero : B256.gtCheck (Bytes.toB256 [0xd6, 0x08, 0xea, 0x64]) (0xd608ea64 : B256) = 0 := by decide
          exact (nonzero ((St.of_pop2 pop).2.1.symm.trans flagZero)).elim
        | zero dest pop run =>
          refine .zero dest pop ?_
          have shape := (St.of_pop2 pop).2.2
          rw [shape] at run ⊢
          unfold ImplV2.t_00ae_c0 at run ⊢
          obtain ⟨next, step, run⟩ := rpw_next run
          refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
          obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
          obtain ⟨next, step, run⟩ := rpw_next run
          refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
          obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
          obtain ⟨next, step, run⟩ := rpw_next run
          refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
          obtain ⟨_, rfl⟩ := ri_eq (StepIn.toRun step)
          obtain ⟨next, step, run⟩ := rpw_next run
          refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
          obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
          cases run with
          | toZero dest pop run =>
            exact ((by decide : B256.eqCheck (Bytes.toB256 [0xd6, 0x08, 0xea, 0x64]) (0xd608ea64 : B256) ≠ 0) (St.of_pop2 pop).2.1).elim
          | toSucc dest word nonzero lookup pop run =>
            rw [show ImplV2.cert.prog[106]? = some ImplV2.t_0c24_c106 from rfl] at lookup
            cases lookup
            exact .toSucc dest word nonzero rfl pop (v2Wrapper_writeClass run)

private theorem v2DataHead_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {S : List B256} {out : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0xd608ea64)
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm (St b S M G) ImplV2.t_001a_c0 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm (St b S M G) ImplV2.t_001a_c0 out := by
  unfold ImplV2.t_001a_c0 at run ⊢
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨gas, shape⟩ := ri_shr (StepIn.toRun step)
  have selectWord : Sevm.dataWord sevm (Bytes.toB256 [0]) >>>
      (Bytes.toB256 [0xe0]).toNat = (0xd608ea64 : B256) := selector
  rw [selectWord] at shape
  subst next
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
  cases run with
  | succ dest word nonzero pop run =>
    have flagZero : B256.gtCheck (Bytes.toB256 [0x8a, 0x6d, 0xb9, 0xc3])
        (0xd608ea64 : B256) = 0 := by decide
    exact (nonzero ((St.of_pop2 pop).2.1.symm.trans flagZero)).elim
  | zero dest pop run =>
    refine .zero dest pop ?_
    have shape := (St.of_pop2 pop).2.2
    rw [shape] at run ⊢
    exact v2Selector_writeClass run

private theorem v2Entry_writeClass
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {S : List B256} {out : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0xd608ea64)
    (run : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm (St b S M G) ImplV2.t_0000_c0 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm (St b S M G) ImplV2.t_0000_c0 out := by
  unfold ImplV2.t_0000_c0 at run ⊢
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_callvalue (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun step)
  obtain ⟨next, step, run⟩ := rpw_next run
  refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
  cases run with
  | zero dest pop run =>
    unfold ImplV2.t_000c_c0 at run
    iterate 2
      obtain ⟨next, step, run⟩ := rpw_next run
    exact (rpw_revert run).elim
  | succ dest word nonzero pop run =>
    refine .succ dest word nonzero pop ?_
    obtain ⟨_, flag, shape⟩ := St.of_pop2 pop
    have valueZero := eq_zero_of_iszero_ne_zero (flag ▸ nonzero)
    rw [shape] at run ⊢
    unfold ImplV2.t_0010_c0 at run ⊢
    cases run with
    | dest burn run =>
      refine .dest burn ?_
      have shape := St.of_burn burn
      rw [shape] at run ⊢
      obtain ⟨next, step, run⟩ := rpw_next run
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := rpw_next run
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := rpw_next run
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_calldatasize (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := rpw_next run
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_lt (StepIn.toRun step)
      obtain ⟨next, step, run⟩ := rpw_next run
      refine .next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun step)
      cases run with
      | succ dest word nonzero pop run =>
        unfold ImplV2.t_034c_c0 at run
        cases run with
        | dest burn run =>
          iterate 2
            obtain ⟨next, step, run⟩ := rpw_next run
          exact (rpw_revert run).elim
      | zero dest pop run =>
        refine .zero dest pop ?_
        have shape := (St.of_pop2 pop).2.2
        rw [shape] at run ⊢
        exact v2DataHead_writeClass selector run

/-- Observe the actual whole successful fresh V2 initializer: every real store
is classified and the same source route has no external instruction. -/
theorem implV2_initializeV2_observed
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (selector : Blanc.Sevm.selector sevm = 0xd608ea64) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
      V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x) ImplV2.cert.prog sevm pre post := by
  let R : Exec.Deriv := ⟨0, sevm, pre, .ok post, run⟩
  obtain ⟨entry, lookup, lifted⟩ := lift_sound_in_noStateGas ImplV2.cert_check code hsg run
  rw [show ImplV2.cert.prog[0]? = some ImplV2.t_0000_c0 from rfl] at lookup
  cases lookup
  have stateEq : St pre [] Mem.empty pre.gasLeft = pre := (St.self stack memory).symm
  have framed : SFunc.RunP (StepIn R) ImplV2.cert.prog sevm
      (St pre [] Mem.empty pre.gasLeft) ImplV2.t_0000_c0 (.halted post) :=
    stateEq.symm ▸ lifted
  have classified := v2Entry_writeClass selector framed
  have unframed : SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧
      V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x) ImplV2.cert.prog sevm pre
      ImplV2.t_0000_c0 (.halted post) :=
    Eq.mp (congrArg (fun d => SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧
      V2InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x) ImplV2.cert.prog sevm d
      ImplV2.t_0000_c0 (.halted post)) stateEq) classified
  exact ⟨_, rfl, unframed⟩

/-- The requested write classifier, projected from the same actual source run. -/
theorem implV2_initializeV2_writeClass
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (selector : Blanc.Sevm.selector sevm = 0xd608ea64) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
      V2InitializerWriteClass sevm d n) ImplV2.cert.prog sevm pre post := by
  exact SProg.RunP.mono (fun step => ⟨step.1, step.2.1⟩)
    (implV2_initializeV2_observed run code hsg stack memory selector)

private theorem v2Short_observation
    {K : B256 → Prop} {sevm frame : Sevm} {d : Devm} {n : Ninst}
    (observed : V2InitializerWriteClass sevm d n)
    (short : v2InitializerNameLength sevm ≤ 31)
    (separate : ∀ key, K key → key ∉ ([4, 15, 18] : List B256)) :
    GuardObs K False frame d n := by
  intro store key value rest shape tracked
  rcases observed store key value rest shape with fixed | zero | payload
  · exact (separate key tracked fixed).elim
  · rw [zero]
    exact Or.inr (Nat.zero_le _)
  · exact (by omega : ¬ 31 < v2InitializerNameLength sevm) payload.1 |>.elim

/-- A short actual decoded name has no payload-word stores. Fixed-key
separation therefore gives demanded-row nonincrease, even on a zero-tail alias. -/
theorem implV2_initializeV2_short_nonInc
    {K : B256 → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (selector : Blanc.Sevm.selector sevm = 0xd608ea64)
    (short : v2InitializerNameLength sevm ≤ 31)
    (separate : ∀ key, K key → key ∉ ([4, 15, 18] : List B256)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
      GuardObs K False s d n) ImplV2.cert.prog sevm pre post := by
  refine SProg.RunP.mono ?_
    (implV2_initializeV2_writeClass run code hsg stack memory selector)
  intro s d n d' step
  exact ⟨step.1, v2Short_observation step.2 short separate⟩

/-- The actual short-name initializer preserves an explicitly supplied
zero-row seed. External effects are excluded by the same successful source
route; no child-effect or nonzero administrative-word preservation is assumed. -/
theorem implV2_initializeV2_short_zero
    {K : B256 → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (selector : Blanc.Sevm.selector sevm = 0xd608ea64)
    (short : v2InitializerNameLength sevm ≤ 31)
    (separate : ∀ key, K key → key ∉ ([4, 15, 18] : List B256))
    (zero : ZeroSlots K sevm.currentTarget pre) :
    ZeroSlots K sevm.currentTarget post := by
  have observed : SProg.RunP (fun s d n d' =>
      StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
      GuardObs K False s d n ∧ ∀ x, n ≠ .exec x)
      ImplV2.cert.prog sevm pre post :=
    SProg.RunP.mono
      (fun step => ⟨step.1, v2Short_observation step.2.1 short separate, step.2.2⟩)
      (implV2_initializeV2_observed run code hsg stack memory selector)
  exact progRunP_zero_noExec (fun step => StepIn.toRun step.1)
    (fun step => step.2.1) (fun step => step.2.2) observed zero

end Blanc.Lift.Usdc
