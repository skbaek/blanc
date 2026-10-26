import Blanc.Lift.Usdc.ImplV1.Cert
import Blanc.Lift.Sound
import Blanc.Lift.RunPWalk
import Blanc.Lift.InvWalk
import Blanc.Lift.InvWalkOps
import Blanc.Lift.MemMap
import Blanc.Lift.MemPotential
import Blanc.Lift.SolcStringAllocation
import Blanc.Lift.SolcAbiStringStaging
import Blanc.WordArithmetic

/-!
# Actual V1 `initialize` three-allocation staging into `call16` (component)

Source-bound leaf over the shared chaining in
`Blanc.Lift.SolcAbiStringStaging`. Actual source (verified by native read of
`Blanc/Lift/Usdc/ImplV1/Cert.lean`, lines 1057-1060):

* `t_0410_c60`: `dest; pop; push 0x0584; push 4; ...` (two string
  decode/allocation fragments, then tail `t_04a4_c60`);
* `t_04a4_c60`: third decode/allocation fragment, five static decodes, then
  `push 0x16b0; callNext 16 t_0584_c60`;
* `t_0584_c60 = dest; stop`, table entry `16` is `t_16b0_c16`.

The wrapper entry stack is the callvalue word atop the dispatcher residual;
`pop` drops it and `0x0584` (the `callNext 16` return tag) sits under
everything. Each allocation reads the free pointer at word `64`, writes the
next pointer back to `64`, stores the length header, and copies the payload.
No calldata boundschecks exist in the wrapper; all bounds come from the
successful post-`Pot` via the shared chaining. No new gas, profile,
endpoint, or hash premises.
-/

namespace Blanc.Lift.Usdc.OldInitializerV1Staging

open Jaune Blanc Blanc.Lift
open SolcStringAllocation SolcAbiStringStaging
open ImplV1

/-- Table entry `16` is the actual V1 initializer callee `t_16b0_c16`. -/
theorem entry16 : (Cert.prog cert)[16]? = some t_16b0_c16 := rfl

/-- The wrapper return tag kept under the staging stack. -/
def retTag : B256 := 0x0584

/-- First string-head address (absolute calldata offset 4). -/
def head1 : B256 := 4

/-- Second string-head address (absolute calldata offset 36). -/
def head2 : B256 := 36

/-- Third string-head address (absolute calldata offset 68). -/
def head3 : B256 := 68

/-- Byte mask used by the `decimals` static decode. -/
def mask8 : B256 := Bytes.toB256 [0xff]

/-- 20-byte address mask used by the four static decodes. -/
def mask20 : B256 := Bytes.toB256
  [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The actual wrapper head: prologue, then two dynamic-string fragments,
then the tail `t_04a4_c60`. -/
theorem t_0410_shape : ImplV1.t_0410_c60 =
    .dest (.next (.reg .pop) (.next (.push [0x05, 0x84] (by decide))
      (.next (.push [0x04] (by decide)) (.next (.reg (.dup 0))
      (.next (.reg .calldatasize) (.next (.reg .sub) (.next (.reg (.dup 1))
      (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.reg (.dup 0))
      (strFrag (rotFrag (strFrag ImplV1.t_04a4_c60))))))))))))) := rfl

/-- The actual wrapper tail: third dynamic-string fragment, five masked
static decodes, cleanup, then `callNext 16`. -/
theorem t_04a4_shape : ImplV1.t_04a4_c60 =
    rotFrag (strFrag (rotFrag (staticFrag [0xff] (by decide)
      (staticFrag [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)
      (staticFrag [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)
      (staticFrag [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)
      (staticFrag [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)
      (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop)
        (.next (.push [0x16, 0xb0] (by decide)) (.callNext 16 ImplV1.t_0584_c60))))))))))))
    := rfl

/-- ABI string length word of the head at `head`: the length sits at
`4 + W`, where `W` is the head word (B256 modular arithmetic). -/
def lenAt (sevm : Sevm) (head : B256) : B256 :=
  Sevm.dataWord sevm (4 + Sevm.dataWord sevm head)

/-- The payload bytes the wrapper copies for the head at `head`. -/
def payloadAt (sevm : Sevm) (head : B256) : Bytes :=
  sevm.data.sliceD (32 + (4 + Sevm.dataWord sevm head)).toNat (lenAt sevm head).toNat 0

private theorem lit4 : Bytes.toB256 [0x04] = (4 : B256) := by decide
private theorem lit584 : Bytes.toB256 [0x05, 0x84] = retTag := by decide
private theorem e36 : (32 : B256) + 4 = 36 := by decide
private theorem e68 : (32 : B256) + 36 = 68 := by decide
private theorem e100 : (32 : B256) + 68 = 100 := by decide
private theorem e132 : (32 : B256) + 100 = 132 := by decide
private theorem e164 : (32 : B256) + 132 = 164 := by decide
private theorem e196 : (32 : B256) + 164 = 196 := by decide
private theorem e228 : (32 : B256) + 196 = 228 := by decide

/-- **Actual V1 wrapper staging, with its rebuild.** Every `PotStep P` run of
the actual wrapper reaches the actual `callNext 16` node (tag `0x16b0` pushed
over the call-16 stack) with the derived three-allocation memory and
`Staged3` facts, and the whole state-silent prefix `Lifts`: a strengthened
run of the call node rebuilds a strengthened run of `t_0410_c60` with the same
pre-state and outcome. Same premises as `wrapper_strengthen`. -/
theorem wrapper_stage
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {cv : B256} {R : List B256} {M0 : Mem} {G0 : Nat}
    {p1 : B256} {out : Outcome}
    (hfp : memWord M0 64 = p1)
    (hp96 : 96 ≤ p1.toNat)
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
      (St b (cv :: R) M0 G0) ImplV1.t_0410_c60 out) :
    ∃ (p2 p3 : B256) (M3 : Mem) (G2 : Nat),
      M3 = allocMem (allocMem (allocMem M0 p1 (lenAt sevm head1) (payloadAt sevm head1))
        p2 (lenAt sevm head2) (payloadAt sevm head2)) p3 (lenAt sevm head3)
        (payloadAt sevm head3) ∧
      Staged3 M0 M3 p1 p2 p3 (nextWord p3 (lenAt sevm head3))
        (lenAt sevm head1) (lenAt sevm head2) (lenAt sevm head3) ∧
      let S_call := [mask20 &&& Sevm.dataWord sevm 228, mask20 &&& Sevm.dataWord sevm 196,
        mask20 &&& Sevm.dataWord sevm 164, mask20 &&& Sevm.dataWord sevm 132,
        mask8 &&& Sevm.dataWord sevm 100, p3, p2, p1, retTag] ++ R
      Lifts (FreePtr.PotStep P) ImplV1.cert.prog sevm (St b (cv :: R) M0 G0) ImplV1.t_0410_c60
        (St b (Bytes.toB256 [0x16, 0xb0] :: S_call) M3 G2) (.callNext 16 ImplV1.t_0584_c60) ∧
      SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
        (St b (Bytes.toB256 [0x16, 0xb0] :: S_call) M3 G2) (.callNext 16 ImplV1.t_0584_c60) out := by
  subst hfp
  have L : Lifts (FreePtr.PotStep P) ImplV1.cert.prog sevm (St b (cv :: R) M0 G0)
      ImplV1.t_0410_c60 (St b (cv :: R) M0 G0) ImplV1.t_0410_c60 := Lifts.refl
  rw [t_0410_shape] at run L
  obtain ⟨_, L, run⟩ := ldest L run
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_pop (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_calldatasize (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_sub (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_add (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  rw [lit4, lit584] at run L
  -- First string.
  obtain ⟨_, -, run, L2⟩ := strFrag_lift erase run
  replace L := L.trans L2
  obtain ⟨_, run, L2⟩ := rotFrag_lift erase run
  replace L := L.trans L2
  rw [e36] at run L
  -- Second string.
  obtain ⟨_, -, run, L2⟩ := strFrag_lift erase run
  replace L := L.trans L2
  rw [t_04a4_shape] at run L
  obtain ⟨_, run, L2⟩ := rotFrag_lift erase run
  replace L := L.trans L2
  rw [e68] at run L
  -- Third string.
  obtain ⟨_, hpost, run, L2⟩ := strFrag_lift erase run
  replace L := L.trans L2
  obtain ⟨_, run, L2⟩ := rotFrag_lift erase run
  replace L := L.trans L2
  rw [e100] at run L
  -- Five masked static heads.
  obtain ⟨_, run, L2⟩ := staticFrag_lift erase run
  replace L := L.trans L2
  rw [e132] at run L
  obtain ⟨_, run, L2⟩ := staticFrag_lift erase run
  replace L := L.trans L2
  rw [e164] at run L
  obtain ⟨_, run, L2⟩ := staticFrag_lift erase run
  replace L := L.trans L2
  rw [e196] at run L
  obtain ⟨_, run, L2⟩ := staticFrag_lift erase run
  replace L := L.trans L2
  rw [e228] at run L
  obtain ⟨_, run, L2⟩ := staticFrag_lift erase run
  replace L := L.trans L2
  -- Cleanup and the internal call.
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_pop (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_pop (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_pop (erase w.1)
  clear w
  obtain ⟨d, w, L, run⟩ := lstep L run rfl
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  exact ⟨_, _, _, _, rfl, stage3 hp96 (sliceD_length _ _ _) (sliceD_length _ _ _)
    (sliceD_length _ _ _) rfl rfl hpost, L, run⟩

/-- **Actual V1 wrapper staging into the real `call16`.** Any `PotStep P`
run of the actual wrapper `t_0410_c60` (entry stack: callvalue word over
the dispatcher residual `R`), from memory whose free pointer is `p1 ≥ 96`,
enters the actual callee `t_16b0_c16` with the derived stack (four masked
addresses, the masked `decimals`, the three allocated string pointers, the
return tag `0x0584`, then `R`) and the derived memory: three actual
allocations whose headers, pointer chain, bounds, ordered non-overlap and
prior-word survival are `Staged3`. Both outcomes of the actual internal call
are covered: the callee halts (and so does the run, with the same `out`), or
it returns and the actual continuation `t_0584_c60` produces `out`. Same `P`,
base state `b` and outcome throughout; no gas, profile, hash, length-range or
calldata-bounds premise. -/
theorem wrapper_strengthen
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {cv : B256} {R : List B256} {M0 : Mem} {G0 : Nat}
    {p1 : B256} {out : Outcome}
    (hfp : memWord M0 64 = p1)
    (hp96 : 96 ≤ p1.toNat)
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
      (St b (cv :: R) M0 G0) ImplV1.t_0410_c60 out) :
    ∃ (p2 p3 : B256) (M3 : Mem) (G3 : Nat),
      M3 = allocMem (allocMem (allocMem M0 p1 (lenAt sevm head1) (payloadAt sevm head1))
        p2 (lenAt sevm head2) (payloadAt sevm head2)) p3 (lenAt sevm head3)
        (payloadAt sevm head3) ∧
      Staged3 M0 M3 p1 p2 p3 (nextWord p3 (lenAt sevm head3))
        (lenAt sevm head1) (lenAt sevm head2) (lenAt sevm head3) ∧
      let S_call := [mask20 &&& Sevm.dataWord sevm 228, mask20 &&& Sevm.dataWord sevm 196,
        mask20 &&& Sevm.dataWord sevm 164, mask20 &&& Sevm.dataWord sevm 132,
        mask8 &&& Sevm.dataWord sevm 100, p3, p2, p1, retTag] ++ R
      ((∃ Dh, SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
          (St b S_call M3 G3) ImplV1.t_16b0_c16 (.halted Dh) ∧ out = .halted Dh) ∨
        (∃ Dr, SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
            (St b S_call M3 G3) ImplV1.t_16b0_c16 (.returned Dr) ∧
          SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm Dr
            ImplV1.t_0584_c60 out)) := by
  obtain ⟨p2, p3, M3, G2, hM, hS, L, run⟩ := wrapper_stage erase hfp hp96 run
  obtain ⟨G3, hcall⟩ := rpw_call entry16 run
  refine ⟨p2, p3, M3, G3, hM, hS, ?_⟩
  rcases hcall with ⟨D, callee, rest⟩ | ⟨D, callee, hout⟩
  · exact .inr ⟨D, callee, rest⟩
  · exact .inl ⟨D, callee, hout⟩

/-- The actual terminal continuation `t_0584_c60 = dest; stop` only halts. -/
theorem t_0584_halts {Q : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {d : Devm}
    {o : Outcome} (run : SFunc.RunP Q ImplV1.cert.prog sevm d ImplV1.t_0584_c60 o) :
    ∃ D, o = .halted D := by
  unfold ImplV1.t_0584_c60 at run
  cases run with
  | dest _ k =>
    cases k with
    | last _ => exact ⟨_, rfl⟩

end Blanc.Lift.Usdc.OldInitializerV1Staging
