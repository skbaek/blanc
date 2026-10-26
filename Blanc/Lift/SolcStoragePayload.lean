import Blanc.Lift.Basic
import Blanc.Lift.MemPotential
import Blanc.Lift.StepMemory
import Blanc.Lift.RunPWalk
import Blanc.Lift.InvWalkProvenance
import Blanc.Lift.InvWalk
import Blanc.Lift.InvWalkOps
import Blanc.Lift.VyperFrameLoop
import Blanc.Lift.VyperCallee
import Blanc.WordArithmetic

/-!
# Storage-payload memory loop template (V1 `initialize` component)

Contract-neutral source shape for the actual solc storage-string payload loop:
at iteration `i` the head stack is `[end, base + i, p + 32*i] ++ rest`, where
`end : B256` is arbitrary, `base : B256` is arbitrary (modular keys, never
assumed no-wrap), and `p : Nat` satisfies `p < 2^256`.

`count = (end.toNat - p + 31) / 32` uses `Nat` subtraction, NOT a decoded
length, so no initial pointer+length no-wrap premise is needed. The invariant
is `i <= count` AND `p + 32*i < 2^256`; the storing branch tests
`cursor < end` (hence `i < count`), and a successful `MLOAD` supplies
`cursor.toNat + 32 < 2^256` for the next cursor.

This module owns only the template: literal back/exit bytes (`<= 32`), the
loop table index `k`, and the actual exit `SFunc` tail stay parameters. No
endpoint is chosen here. It proves the read-window producer, one body
iteration, one head pass, and the loop fold; the exact initial
pointer/end producer (real string setter/wrapper) is explicitly outside this
component.
-/

namespace Blanc.Lift.SolcStoragePayload

open Jaune Blanc Blanc.Lift

/-- The real increment and back edge after the payload store. -/
def body (back : Bytes) (bound : back.length ≤ 32) (k : Nat) : SFunc :=
  .next (.reg (.dup 2)) (.next (.reg .mload)
    (.next (.reg (.dup 2)) (.next (.reg .sstore)
      (.next (.reg (.swap 1)) (.next (.push [0x20] (by decide))
        (.next (.reg .add) (.next (.reg (.swap 1))
          (.next (.reg (.swap 0)) (.next (.push [0x01] (by decide))
            (.next (.reg .add) (.next (.reg (.swap 0))
              (.next (.push back bound) (.jump k)))))))))))))

/-- The payload comparison head, retaining literal destination words. -/
def head (back exit : Bytes) (backBound : back.length ≤ 32)
    (exitBound : exit.length ≤ 32) (k : Nat) (tail : SFunc) : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .gt)
    (.next (.reg .iszero) (.next (.push exit exitBound)
      (.branch (body back backBound k) tail))))))

/-- Iteration count from the exact `fin` word and start `p` (`Nat` sub). -/
def count (fin : B256) (p : Nat) : Nat :=
  (fin.toNat - p + 31) / 32

/-- Read-window law for a step relation `P`: an `MLOAD` at `ptr` leaves room. -/
def ReadWindow (P : Sevm → Devm → Ninst → Devm → Prop) : Prop :=
  ∀ {s : Sevm} {d : Devm} {rest : List B256} {d' : Devm} {ptr : B256},
    d.stack = ptr :: rest → P s d (.reg .mload) d' → ptr.toNat + 32 < 2 ^ 256

/-- Per-store observation: literal zero, or a bounded modular payload key. -/
def StoreObs (fin : B256) (base : B256) (p : Nat) (_s : Sevm) (d : Devm)
    (n : Ninst) : Prop :=
  n = Ninst.reg Rinst.sstore →
    ∀ (key value : B256) (rest : List B256),
      d.stack = key :: value :: rest →
        value = 0 ∨ ∃ j : Nat, j < count fin p ∧ key = base + j.toB256

/-! ## Read-window producer from memory potential -/

variable {P : Sevm → Devm → Ninst → Devm → Prop}

/-- An `MLOAD` under `PotStep` leaves a full word in bounds: the poststate
memory covers `ptr.toNat + 32` (`run_mload_memory` + `memExtSize_access_le`)
and `Pot.size_lt` bounds it below `2^160 ≤ 2^256`. No additional gas bound
is assumed beyond the supplied poststate `Pot` (which itself contains one). -/
theorem readWindow_of_potStep
    (erase : ∀ {s : Sevm} {d : Devm} {n : Ninst} {d' : Devm},
      P s d n d' → Ninst.Run s d n d')
    {s : Sevm} {d d' : Devm} {rest : List B256} {ptr : B256}
    (hs : d.stack = ptr :: rest)
    (h : FreePtr.PotStep P s d (.reg .mload) d') :
    ptr.toNat + 32 < 2 ^ 256 := by
  obtain ⟨hrun, _, pot'⟩ := h
  have hmem := run_mload_memory hs (erase hrun)
  have hle : ptr.toNat + 32 ≤ d'.memory.size := by
    have hw := memExtSize_access_le d.memory.size ptr.toNat 32 (by decide)
    rw [hmem]
    exact hw
  have hlt : d'.memory.size < 2 ^ 160 := FreePtr.Pot.size_lt pot'
  have hcap : (2 : ℕ) ^ 160 ≤ 2 ^ 256 := by decide
  omega

/-- Every `PotStep` `MLOAD` satisfies the `ReadWindow` law. -/
theorem readWindow_potStep
    (erase : ∀ {s : Sevm} {d : Devm} {n : Ninst} {d' : Devm},
      P s d n d' → Ninst.Run s d n d') :
    ReadWindow (FreePtr.PotStep P) :=
  fun hs h => readWindow_of_potStep erase hs h

/-! ## Enrichment, invariant, and one body iteration -/

/-- Enriched step: same `P`, bounded-key-or-zero stores, no external exec. -/
def Enriched (P : Sevm → Devm → Ninst → Devm → Prop)
    (fin base0 : B256) (p : Nat) : Sevm → Devm → Ninst → Devm → Prop :=
  fun s d n d' => P s d n d' ∧ StoreObs fin base0 p s d n ∧ ∀ x, n ≠ Ninst.exec x

/-- Loop invariant at iteration `i`: in range, cursor in bounds, exact stack. -/
def Inv (fin base0 : B256) (p : Nat) (rest : List B256) (i : Nat)
    (d : Devm) : Prop :=
  i ≤ count fin p ∧ p + 32 * i < 2 ^ 256 ∧
    d.stack = fin :: (base0 + i.toB256) :: ((p + 32 * i).toB256) :: rest

/-- One body iteration: invert `dup2; mload; dup2; sstore` and the
increment suffix through the back-edge jump. The `SSTORE` pops exactly
`key`/`word` (`of_run_sstore`, stack only); the poststate is rebased with
`St.self'`, leaving its world, memory, and gas as the actual step
produced. The rebuilt enriched run maps any head continuation at the
landing state back to an enriched run of the whole body. -/
theorem body_case
    (erase : ∀ {s : Sevm} {d : Devm} {n : Ninst} {d' : Devm},
      P s d n d' → Ninst.Run s d n d')
    (rwin : ReadWindow P)
    {fs : List SFunc} {sevm : Sevm}
    {fin base0 : B256} {p : Nat} {rest : List B256}
    {k : Nat} {back : Bytes} {bound : back.length ≤ 32}
    {headTree : SFunc} (entry : fs[k]? = some headTree)
    {i : Nat} (hlt : i < count fin p) (hnow : p + 32 * i < 2 ^ 256)
    {pre : Devm} {sg : Seg} (hstack : pre.stack = fin :: (base0 + i.toB256) :: ((p + 32 * i).toB256) :: rest)
    (run : SFunc.RunCutP P fs sevm [k] pre (body back bound k) sg) :
    ∃ d', sg = Seg.at k d' ∧ Inv fin base0 p rest (i + 1) d' ∧
      ∀ {o}, SFunc.RunP (Enriched P fin base0 p) fs sevm d' headTree o →
        SFunc.RunP (Enriched P fin base0 p) fs sevm pre (body back bound k) o := by
  unfold body at run
  rw [St.self' pre, hstack] at run
  obtain ⟨m1, s1, run⟩ := ric_nextP run
  obtain ⟨G1, rfl⟩ := ri_dup (w := (p + 32 * i).toB256) rfl (erase s1)
  have hpre : pre = St pre (fin :: (base0 + i.toB256) :: ((p + 32 * i).toB256) :: rest)
      pre.memory pre.gasLeft :=
    St.self hstack rfl
  obtain ⟨m2, s2, run⟩ := ric_nextP run
  have hwin : ((p + 32 * i).toB256).toNat + 32 < 2 ^ 256 := rwin rfl s2
  obtain ⟨G2, rfl⟩ := ri_mload (erase s2)
  obtain ⟨m3, s3, run⟩ := ric_nextP run
  obtain ⟨G3, rfl⟩ := ri_dup (w := base0 + i.toB256) rfl (erase s3)
  obtain ⟨m4, s4, run⟩ := ric_nextP run
  obtain ⟨x, y, hpop⟩ := of_run_sstore (erase s4)
  simp only [Stack.Pop, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at hpop
  obtain ⟨rfl, rfl, hpost⟩ := hpop
  rw [St.self' m4, ← hpost] at run
  obtain ⟨m5, s5, run⟩ := ric_nextP run
  obtain ⟨G5, rfl⟩ := ri_swap (n := (1 : Fin 16)) rfl (erase s5)
  have hm4 : m4 = St m4 (fin :: (base0 + i.toB256) :: ((p + 32 * i).toB256) :: rest)
      m4.memory m4.gasLeft :=
    St.self hpost.symm rfl
  have s5' := hm4.symm ▸ s5
  obtain ⟨m6, s6, run⟩ := ric_nextP run
  obtain ⟨G6, rfl⟩ := ri_push (erase s6)
  obtain ⟨m7, s7, run⟩ := ric_nextP run
  obtain ⟨G7, rfl⟩ := ri_add (erase s7)
  obtain ⟨m8, s8, run⟩ := ric_nextP run
  obtain ⟨G8, rfl⟩ := ri_swap (n := (1 : Fin 16)) rfl (erase s8)
  obtain ⟨m9, s9, run⟩ := ric_nextP run
  obtain ⟨G9, rfl⟩ := ri_swap (n := (0 : Fin 16)) rfl (erase s9)
  obtain ⟨m10, s10, run⟩ := ric_nextP run
  obtain ⟨G10, rfl⟩ := ri_push (erase s10)
  obtain ⟨m11, s11, run⟩ := ric_nextP run
  obtain ⟨G11, rfl⟩ := ri_add (erase s11)
  obtain ⟨m12, s12, run⟩ := ric_nextP run
  obtain ⟨G12, rfl⟩ := ri_swap (n := (0 : Fin 16)) rfl (erase s12)
  obtain ⟨m13, s13, run⟩ := ric_nextP run
  obtain ⟨G13, rfl⟩ := ri_push (erase s13)
  cases run with
  | @jumpCut _ mid' _ d _ pop =>
    obtain ⟨rfl, e⟩ := St.of_pop1 pop
    have hcurNat : ((p + 32 * i).toB256).toNat = p + 32 * i :=
      B256.toNat_toB256_of_lt hnow
    have h32 : p + 32 * i + 32 < 2 ^ 256 := by omega
    have hkey : Bytes.toB256 [0x01] + (base0 + i.toB256)
        = base0 + (i + 1).toB256 := by
      apply B256.toNat_inj
      rw [B256.toNat_add, B256.toNat_add, B256.toNat_add,
        B256.toNat_toB256_of_lt (by omega : i < 2 ^ 256),
        B256.toNat_toB256_of_lt (by omega : i + 1 < 2 ^ 256),
        show (Bytes.toB256 [0x01]).toNat = 1 from rfl,
        Nat.add_comm 1, Nat.lo_add_lo]
      congr 1
    have hcur : Bytes.toB256 [0x20] + (p + 32 * i).toB256
        = (p + 32 * (i + 1)).toB256 := by
      have heq : p + 32 * (i + 1) = p + 32 * i + 32 := by omega
      rw [heq, B256.add_comm]
      exact toB256_add_0x20 h32
    have hred : (((((base0 + i.toB256) :: (p + 32 * i).toB256 :: rest).set
          (Fin.val (1 : Fin 16)) fin).set (Fin.val (1 : Fin 16))
          (Bytes.toB256 [0x20] + (p + 32 * i).toB256)).set
          (Fin.val (0 : Fin 16)) fin).set (Fin.val (0 : Fin 16))
          (Bytes.toB256 [0x01] + (base0 + i.toB256))
        = (Bytes.toB256 [0x01] + (base0 + i.toB256))
          :: (Bytes.toB256 [0x20] + (p + 32 * i).toB256) :: rest := rfl
    have hmid : mid'.stack
        = fin :: (base0 + (i + 1).toB256) :: ((p + 32 * (i + 1)).toB256) :: rest := by
      rw [e]
      simp only [St.stack]
      rw [hred, hkey, hcur]
    refine ⟨mid', rfl, ⟨?_, ?_, hmid⟩, ?_⟩
    · unfold count at hlt ⊢; omega
    · have heq : p + 32 * (i + 1) = p + 32 * i + 32 := by omega
      omega
    · intro o hr
      unfold body
      rw [hpre]
      refine SFunc.RunP.next ⟨s1, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s2, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s3, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s4, ?_, ?_⟩ ?_
      · intro _ key value r h
        simp only [St.stack, List.cons.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact Or.inr ⟨i, hlt, rfl⟩
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s5', ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s6, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s7, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s8, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s9, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s10, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s11, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s12, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨s13, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      exact SFunc.RunP.jump back.toB256 entry pop hr
  | jump _ nc _ _ _ => exact (nc (by simp only [List.mem_singleton])).elim

/-! ## Head pass and loop fold -/

/-- One head pass: invert the comparison head through the branch. The
storing arm derives `cursor < fin` (`gtCheck_iszero_eq`), hence `i < count`,
and delegates to `body_case`; the exit arm delegates to the exit
certificate. Each side rebuilds the enriched head run around its arm. -/
theorem head_case
    (erase : ∀ {s : Sevm} {d : Devm} {n : Ninst} {d' : Devm},
      P s d n d' → Ninst.Run s d n d')
    (rwin : ReadWindow P)
    {fs : List SFunc} {sevm : Sevm}
    {fin base0 : B256} {p : Nat} {rest : List B256}
    {k : Nat} {back exit : Bytes} {bound : back.length ≤ 32}
    {ebound : exit.length ≤ 32} {tail : SFunc}
    (entry : fs[k]? = some (head back exit bound ebound k tail))
    (exitCert : ∀ {d sg}, SFunc.RunCutP P fs sevm [k] d tail sg →
      ∃ o, sg = Seg.done o ∧
        SFunc.RunP (Enriched P fin base0 p) fs sevm d tail o)
    {i : Nat} {pre : Devm} {sg : Seg} (hinv : Inv fin base0 p rest i pre)
    (run : SFunc.RunCutP P fs sevm [k] pre
      (head back exit bound ebound k tail) sg) :
    (∃ d', sg = Seg.at k d' ∧ Inv fin base0 p rest (i + 1) d' ∧
      ∀ {o}, SFunc.RunP (Enriched P fin base0 p) fs sevm d'
          (head back exit bound ebound k tail) o →
        SFunc.RunP (Enriched P fin base0 p) fs sevm pre
          (head back exit bound ebound k tail) o) ∨
    (∃ o, sg = Seg.done o ∧
      SFunc.RunP (Enriched P fin base0 p) fs sevm pre
        (head back exit bound ebound k tail) o) := by
  obtain ⟨_, hnow, hstack⟩ := hinv
  unfold head at run
  cases run with
  | dest burn run =>
    have burn0 := burn
    rw [St.self' pre, hstack] at burn
    have eburn := St.of_burn burn
    rw [eburn] at run
    obtain ⟨m1, t1, run⟩ := ric_nextP run
    obtain ⟨G1, rfl⟩ := ri_dup (w := ((p + 32 * i).toB256)) rfl (erase t1)
    obtain ⟨m2, t2, run⟩ := ric_nextP run
    obtain ⟨G2, rfl⟩ := ri_dup (w := fin) rfl (erase t2)
    obtain ⟨m3, t3, run⟩ := ric_nextP run
    obtain ⟨G3, rfl⟩ := ri_gt (erase t3)
    obtain ⟨m4, t4, run⟩ := ric_nextP run
    obtain ⟨G4, rfl⟩ := ri_iszero (erase t4)
    obtain ⟨m5, t5, run⟩ := ric_nextP run
    obtain ⟨G5, rfl⟩ := ri_push (erase t5)
    have t1' := eburn.symm ▸ t1
    cases run with
    | @zero _ midB _ _ _ _ pop runB =>
      obtain ⟨_, hw, eb⟩ := St.of_pop2 pop
      have hstackB : midB.stack
          = fin :: (base0 + i.toB256) :: ((p + 32 * i).toB256) :: rest := by
        rw [eb]
        rfl
      have hltN : ((p + 32 * i).toB256).toNat < fin.toNat :=
        gtCheck_iszero_eq hw
      have hcurNat : ((p + 32 * i).toB256).toNat = p + 32 * i :=
        B256.toNat_toB256_of_lt hnow
      have hlt : i < count fin p := by
        unfold count
        omega
      obtain ⟨d', hseg, hinv', buildB⟩ :=
        body_case erase rwin entry hlt hnow hstackB runB
      refine Or.inl ⟨d', hseg, hinv', ?_⟩
      intro o hr
      refine SFunc.RunP.dest burn0 ?_
      refine SFunc.RunP.next ⟨t1', ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨t2, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨t3, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨t4, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨t5, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      exact SFunc.RunP.zero _ pop (buildB hr)
    | @succ _ _ _ _ _ _ _ hne pop runT =>
      obtain ⟨o, hseg, hrunT⟩ := exitCert runT
      refine Or.inr ⟨o, hseg, ?_⟩
      refine SFunc.RunP.dest burn0 ?_
      refine SFunc.RunP.next ⟨t1', ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨t2, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨t3, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨t4, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      refine SFunc.RunP.next ⟨t5, ?_, ?_⟩ ?_
      · intro h; cases h
      · intro x h; cases h
      exact SFunc.RunP.succ _ _ hne pop hrunT

/-- The loop fold: one head pass per iteration supplies every back edge and
`SFunc.RunP.loop` closes the loop, strengthening the whole head run with
the same pre-state and outcome. -/
theorem runP_enriched
    (erase : ∀ {s : Sevm} {d : Devm} {n : Ninst} {d' : Devm},
      P s d n d' → Ninst.Run s d n d')
    (rwin : ReadWindow P)
    {fs : List SFunc} {sevm : Sevm} {pre : Devm} {out : Outcome}
    {fin base0 : B256} {p : Nat} {rest : List B256}
    {k : Nat} {back exit : Bytes} {bound : back.length ≤ 32}
    {ebound : exit.length ≤ 32} {tail : SFunc}
    (entry : fs[k]? = some (head back exit bound ebound k tail))
    (exitCert : ∀ {d sg}, SFunc.RunCutP P fs sevm [k] d tail sg →
      ∃ o, sg = Seg.done o ∧
        SFunc.RunP (Enriched P fin base0 p) fs sevm d tail o)
    {i₀ : Nat} (h0 : Inv fin base0 p rest i₀ pre)
    (run : SFunc.RunP P fs sevm pre (head back exit bound ebound k tail) out) :
    SFunc.RunP (Enriched P fin base0 p) fs sevm pre
      (head back exit bound ebound k tail) out := by
  let I := fun d => ∃ i, Inv fin base0 p rest i d ∧
    ∀ o, SFunc.RunP (Enriched P fin base0 p) fs sevm d
        (head back exit bound ebound k tail) o →
      SFunc.RunP (Enriched P fin base0 p) fs sevm pre
        (head back exit bound ebound k tail) o
  have step : ∀ d, I d → ∀ sg, SFunc.RunCutP P fs sevm [k] d
      (head back exit bound ebound k tail) sg →
      match sg with
      | .at _ d' => I d'
      | .done o => SFunc.RunP (Enriched P fin base0 p) fs sevm pre
        (head back exit bound ebound k tail) o := by
    intro d ⟨i, hinv, cont⟩ sg hcut
    rcases head_case erase rwin entry exitCert hinv hcut with
      ⟨d', rfl, hinv', build⟩ | ⟨o, rfl, hr⟩
    · exact ⟨i + 1, hinv', fun o hr => cont o (build hr)⟩
    · exact cont o hr
  exact SFunc.RunP.loop (k := k) entry I
    (fun o => SFunc.RunP (Enriched P fin base0 p) fs sevm pre
      (head back exit bound ebound k tail) o)
    step pre out ⟨i₀, h0, fun o hr => hr⟩ run

end Blanc.Lift.SolcStoragePayload
