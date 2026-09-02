-- LidoCircuitBreakerDeploymentLayout.lean : exact constructor layout evidence.
--
-- The executable offset metadata remains compiler-derived in
-- `LidoCircuitBreakerCode`.  This module proves its exact official coordinates
-- from kernel-checked compiler equations and list algebra.  No byte literal,
-- evaluator result, manifest row, or Python verdict enters a Lean premise.

import Blanc.DeploymentCompiled
import Blanc.LidoCircuitBreakerDeploy

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

open CreationArtifact
open DeploymentProof

/-! ## Stable reduction interface for the private constructor

The production helpers remain private.  These proof-valued equations expose
their exact reductions without publishing or duplicating an executable helper.
All downstream computation uses this namespace-owned interface. -/

set_option maxRecDepth 100000 in
set_option linter.defProp false in
/-- One-way proof certificate for the private constructor assembly.  This
belongs to the proof owner rather than the pre-existing executable owner so its
large equality type is elaborated only where deployment proofs are measured. -/
def DeploymentProof.lidoCircuitBreakerConstructorProgram_eq :
    lidoCircuitBreakerConstructorProgram =
      let prefixLength :=
        DeploymentProof.provisionalConstructorPrefixForProof.length
      DeploymentProof.constructorProgramForProof prefixLength
        (prefixLength + runtimeTemplateCode.length)
        runtimeTemplateCode.length := by
  rfl

namespace DeploymentProof

section ReductionCertificates

set_option linter.defProp false

def constructorRuntimeBaseForProof_eq :
    constructorRuntimeBaseForProof = constructorArgumentBytes := by
  rfl

def constructorEventScratchForProof_eq (runtimeLength : Nat) :
    constructorEventScratchForProof runtimeLength =
      ((constructorRuntimeBaseForProof + runtimeLength + 31) / 32) * 32 := by
  rfl

def pushFixedNatForProof_eq (value : Nat) :
    pushFixedNatForProof value =
      if value < 2 ^ 16 then
        Ninst.push [(value >>> 8).toUInt8, value.toUInt8] (by simp)
      else
        pushDeployWord (Nat.toB256 value) := by
  rfl

def pushCompactNatForProof_eq (value : Nat) :
    pushCompactNatForProof value = pushB256 (Nat.toB256 value) := by
  rfl

def loadArgumentIndexForProof_eq (index : Nat) :
    loadArgumentIndexForProof index =
      [pushCompactNatForProof (32 * index), Ninst.mload] := by
  rfl

def storeByteOffsetForProof_eq (offset : Nat) :
    storeByteOffsetForProof offset = [pushFixedNatForProof offset, Ninst.mstore] := by
  rfl

def constructorErrorForProof_eq (name : String) :
    constructorErrorForProof name =
      Func.revertSelector (customErrorData name) (by
        simp [customErrorData, B256.length_toBytes]) := by
  rfl

def patchArgumentIndexForProof_eq (field : ImmutableParameter) :
    patchArgumentIndexForProof field =
      match field with
      | .admin => 0
      | .minPauseDuration => 1
      | .maxPauseDuration => 2
      | .minHeartbeatInterval => 3
      | .maxHeartbeatInterval => 4 := by
  cases field <;> rfl

def patchFieldLineForProof_eq
    (runtimeBase : Nat) (field : ImmutableParameter) :
    patchFieldLineForProof runtimeBase field =
      (immutableWordOffsets field).flatMap fun offset =>
        loadArgumentIndexForProof (patchArgumentIndexForProof field) ++
          storeByteOffsetForProof (runtimeBase + offset) := by
  rfl

def patchRuntimeLineForProof_eq (runtimeBase : Nat) :
    patchRuntimeLineForProof runtimeBase =
      immutableParameters.flatMap (patchFieldLineForProof runtimeBase) := by
  rfl

def constructorBodyForProof_eq
    (runtimeOffset argsOffset runtimeLength : Nat) :
    constructorBodyForProof runtimeOffset argsOffset runtimeLength =
      let eventScratch := constructorEventScratchForProof runtimeLength
      pushFixedNatForProof (argsOffset + constructorArgumentBytes) :::
      codesize ::: lt :::
      ((.call 1) <?>
        (pushCompactNatForProof constructorArgumentBytes :::
          pushFixedNatForProof argsOffset :::
          pushCompactNatForProof 0 ::: codecopy :::
          loadArgumentIndexForProof 0 +++ checkNonAddress +++
          ((.call 1) <?>
            (loadArgumentIndexForProof 0 +++ iszero :::
              ((.call 2) <?>
                (loadArgumentIndexForProof 1 +++ iszero :::
                  ((.call 3) <?>
                    (loadArgumentIndexForProof 2 +++
                      loadArgumentIndexForProof 1 +++ gt :::
                      ((.call 4) <?>
                        (loadArgumentIndexForProof 3 +++ iszero :::
                          ((.call 5) <?>
                            (loadArgumentIndexForProof 4 +++
                              loadArgumentIndexForProof 3 +++ gt :::
                              ((.call 6) <?>
                                (loadArgumentIndexForProof 1 +++
                                  loadArgumentIndexForProof 5 +++ lt :::
                                  ((.call 7) <?>
                                    (loadArgumentIndexForProof 2 +++
                                      loadArgumentIndexForProof 5 +++ gt :::
                                      ((.call 8) <?>
                                        (loadArgumentIndexForProof 3 +++
                                          loadArgumentIndexForProof 6 +++ lt :::
                                          ((.call 9) <?>
                                            (loadArgumentIndexForProof 4 +++
                                              loadArgumentIndexForProof 6 +++ gt :::
                                              ((.call 10) <?>
                                                (pushFixedNatForProof runtimeLength :::
                                                  pushFixedNatForProof runtimeOffset :::
                                                  pushCompactNatForProof
                                                    constructorRuntimeBaseForProof :::
                                                  codecopy :::
                                                  patchRuntimeLineForProof
                                                    constructorRuntimeBaseForProof +++
                                                  loadArgumentIndexForProof 0 +++
                                                  pushB256
                                                    circuitBreakerInitializedEvent :::
                                                  logWith 1 1 4 +++
                                                  pushB256 0 :::
                                                  storeByteOffsetForProof
                                                    eventScratch +++
                                                  loadArgumentIndexForProof 5 +++
                                                  storeByteOffsetForProof
                                                    (eventScratch + 32) +++
                                                  pushB256
                                                    pauseDurationUpdatedEvent :::
                                                  logWith 0
                                                    (Nat.toB256
                                                      (eventScratch / 32)) 2 +++
                                                  loadArgumentIndexForProof 5 +++
                                                  pushB256 pauseDurationSlot :::
                                                  sstore :::
                                                  pushB256 0 :::
                                                  storeByteOffsetForProof
                                                    eventScratch +++
                                                  loadArgumentIndexForProof 6 +++
                                                  storeByteOffsetForProof
                                                    (eventScratch + 32) +++
                                                  pushB256
                                                    heartbeatIntervalUpdatedEvent :::
                                                  logWith 0
                                                    (Nat.toB256
                                                      (eventScratch / 32)) 2 +++
                                                  loadArgumentIndexForProof 6 +++
                                                  pushB256 heartbeatIntervalSlot :::
                                                  sstore :::
                                                  pushFixedNatForProof runtimeLength :::
                                                  pushCompactNatForProof
                                                    constructorRuntimeBaseForProof :::
                                                  Func.return_)))))))))))))))))))))) := by
  rfl

def constructorProgramForProof_eq
    (runtimeOffset argsOffset runtimeLength : Nat) :
    constructorProgramForProof runtimeOffset argsOffset runtimeLength =
      { main := callvalue ::: iszero :::
          (constructorBodyForProof runtimeOffset argsOffset runtimeLength <?>
            (.call 1))
        aux := [Func.revert,
          constructorErrorForProof "AdminZero",
          constructorErrorForProof "MinPauseDurationZero",
          constructorErrorForProof "MinPauseDurationExceedsMax",
          constructorErrorForProof "MinHeartbeatIntervalZero",
          constructorErrorForProof "MinHeartbeatIntervalExceedsMax",
          constructorErrorForProof "PauseDurationBelowMin",
          constructorErrorForProof "PauseDurationAboveMax",
          constructorErrorForProof "HeartbeatIntervalBelowMin",
          constructorErrorForProof "HeartbeatIntervalAboveMax"] } := by
  rfl

def provisionalConstructorPrefixForProof_eq :
    provisionalConstructorPrefixForProof =
      (Prog.compile
        (constructorProgramForProof 0 0 runtimeTemplateCode.length)).getD [] := by
  rfl

end ReductionCertificates

end DeploymentProof

/-! ## Small neutral list facts used by the closed layout certificate -/

private def patchAtOffsets
    (code : Bytes) (word : B256) (offsets : List Nat) : Bytes :=
  offsets.foldl (fun bs offset => Bytes.writeAt bs offset word.toBytes) code

private lemma Bytes.writeAt_append_middle
    {pre old suffix replacement : Bytes}
    (hlen : old.length = replacement.length) :
    Bytes.writeAt (pre ++ old ++ suffix) pre.length replacement =
      pre ++ replacement ++ suffix := by
  unfold Bytes.writeAt
  rw [List.takeD_eq_take _ (by simp)]
  simp only [List.append_assoc]
  rw [List.take_left]
  simp [List.drop_append, hlen]

private lemma Bytes.writeAt_append_middle_at
    {pre old suffix replacement : Bytes} {offset : Nat}
    (hprefix : pre.length = offset)
    (hlen : old.length = replacement.length) :
    Bytes.writeAt (pre ++ old ++ suffix) offset replacement =
      pre ++ replacement ++ suffix := by
  rw [← hprefix]
  exact Bytes.writeAt_append_middle hlen

private theorem differingByteOffsets_self (index : Nat) (xs : Bytes) :
    differingByteOffsets index xs xs = [] := by
  induction xs generalizing index with
  | nil => simp [differingByteOffsets]
  | cons x xs ih => simp [differingByteOffsets, ih]

private theorem differingByteOffsets_append
    (index : Nat) (xs ys xt yt : Bytes)
    (hlen : xs.length = ys.length) :
    differingByteOffsets index (xs ++ xt) (ys ++ yt) =
      differingByteOffsets index xs ys ++
        differingByteOffsets (index + xs.length) xt yt := by
  induction xs generalizing index ys with
  | nil =>
      cases ys with
      | nil => simp [differingByteOffsets]
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.cons_append, differingByteOffsets]
          rw [ih (index := index + 1) (ys := ys) hlen]
          by_cases hxy : x = y <;>
            simp [hxy, Nat.add_assoc, Nat.add_comm 1 xs.length]

private theorem differingByteOffsets_append_same
    (index : Nat) (pre xs ys : Bytes) :
    differingByteOffsets index (pre ++ xs) (pre ++ ys) =
      differingByteOffsets (index + pre.length) xs ys := by
  rw [differingByteOffsets_append index pre pre xs ys rfl,
    differingByteOffsets_self]
  rfl

private theorem differingByteOffsets_replicate_ne
    (index length : Nat) (x y : UInt8) (hxy : x ≠ y) :
    differingByteOffsets index (List.replicate length x)
        (List.replicate length y) =
      (List.range length).map (index + ·) := by
  induction length generalizing index with
  | zero => simp [differingByteOffsets]
  | succ length ih =>
      simp [List.replicate_succ, differingByteOffsets, hxy, ih,
        List.range_succ_eq_map]
      omega

/-! ## Exact runtime size and the compiler-owned marker worlds -/

/-- The parameter-neutral runtime copied by the constructor is exactly 4,282
bytes.  The proof uses successful compilation and compiler shape size; it does
not reduce or duplicate the emitted byte list. -/
theorem runtimeTemplateCode_length_exact : runtimeTemplateCode.length = 4282 := by
  unfold runtimeTemplateCode
  rw [Prog.length_compile (lidoCircuitBreakerCode_compile zeroDeployParams)]
  decide +kernel

private theorem runtimeTemplateCode_immutable_slices_zero :
    (runtimeTemplateCode.drop 174).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 1094).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 1833).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 1920).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 217).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 713).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 258).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 1961).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 508).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 1137).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 672).take 32 = (0 : B256).toBytes ∧
    (runtimeTemplateCode.drop 1178).take 32 = (0 : B256).toBytes := by
  decide +kernel

private theorem immutableMarkerPrograms_compile :
    Prog.compile (runtime (immutableMarkerParams .admin)) =
        some (patchAtOffsets runtimeTemplateCode B256.max
          [174, 1094, 1833, 1920]) ∧
    Prog.compile (runtime (immutableMarkerParams .minPauseDuration)) =
        some (patchAtOffsets runtimeTemplateCode B256.max [217, 713]) ∧
    Prog.compile (runtime (immutableMarkerParams .maxPauseDuration)) =
        some (patchAtOffsets runtimeTemplateCode B256.max [258, 1961]) ∧
    Prog.compile (runtime (immutableMarkerParams .minHeartbeatInterval)) =
        some (patchAtOffsets runtimeTemplateCode B256.max [508, 1137]) ∧
    Prog.compile (runtime (immutableMarkerParams .maxHeartbeatInterval)) =
        some (patchAtOffsets runtimeTemplateCode B256.max [672, 1178]) := by
  decide +kernel

private theorem markerCode_eq_patchAtOffsets
    (field : ImmutableParameter) (offsets : List Nat)
    (hcompile : Prog.compile (runtime (immutableMarkerParams field)) =
      some (patchAtOffsets runtimeTemplateCode B256.max offsets)) :
    lidoCircuitBreakerCode (immutableMarkerParams field) =
      patchAtOffsets runtimeTemplateCode B256.max offsets := by
  unfold lidoCircuitBreakerCode
  rw [hcompile]
  rfl

/-! ## The four two-occurrence immutable fields -/

private def twoWordChunks
    (bs : Bytes) (first second : Nat) : Bytes :=
  bs.take first ++ (bs.drop first).take 32 ++
    (bs.drop (first + 32)).take (second - (first + 32)) ++
    (bs.drop second).take 32 ++ bs.drop (second + 32)

private theorem twoWordChunks_eq
    (bs : Bytes) (first second : Nat) (hsep : first + 32 ≤ second) :
    twoWordChunks bs first second = bs := by
  unfold twoWordChunks
  rw [show second = first + 32 + (second - (first + 32)) by omega]
  simp [← List.take_add]

private def twoWordSegments
    (bs : Bytes) (first second : Nat) (word : B256) : Bytes :=
  bs.take first ++ word.toBytes ++
    (bs.drop (first + 32)).take (second - (first + 32)) ++
    word.toBytes ++ bs.drop (second + 32)

private theorem patchAtOffsets_twoWordSegments
    (bs : Bytes) (first second : Nat)
    (hsep : first + 32 ≤ second) (hlast : second + 32 ≤ bs.length) :
    patchAtOffsets (twoWordSegments bs first second 0) B256.max
        [first, second] =
      twoWordSegments bs first second B256.max := by
  have hprefix : (bs.take first).length = first := by
    rw [List.length_take, Nat.min_eq_left]
    omega
  have hgap :
      ((bs.drop (first + 32)).take
        (second - (first + 32))).length = second - (first + 32) := by
    rw [List.length_take]
    apply Nat.min_eq_left
    rw [List.length_drop]
    omega
  have hfirst :
      Bytes.writeAt (twoWordSegments bs first second 0) first
          B256.max.toBytes =
        bs.take first ++ B256.max.toBytes ++
          (bs.drop (first + 32)).take (second - (first + 32)) ++
          (0 : B256).toBytes ++ bs.drop (second + 32) := by
    unfold twoWordSegments
    simpa only [List.append_assoc] using Bytes.writeAt_append_middle_at
      (pre := bs.take first) (old := (0 : B256).toBytes)
      (suffix := (bs.drop (first + 32)).take
          (second - (first + 32)) ++
        (0 : B256).toBytes ++ bs.drop (second + 32))
      (replacement := B256.max.toBytes) hprefix
      (by rw [B256.length_toBytes, B256.length_toBytes])
  have hsecond :
      Bytes.writeAt
          (bs.take first ++ B256.max.toBytes ++
            (bs.drop (first + 32)).take (second - (first + 32)) ++
            (0 : B256).toBytes ++ bs.drop (second + 32))
          second B256.max.toBytes =
        twoWordSegments bs first second B256.max := by
    unfold twoWordSegments
    simpa only [List.append_assoc] using Bytes.writeAt_append_middle_at
      (pre := bs.take first ++ B256.max.toBytes ++
        (bs.drop (first + 32)).take (second - (first + 32)))
      (old := (0 : B256).toBytes) (suffix := bs.drop (second + 32))
      (replacement := B256.max.toBytes)
      (by
        simp only [List.length_append, hprefix, B256.length_toBytes, hgap]
        omega)
      (by rw [B256.length_toBytes, B256.length_toBytes])
  unfold patchAtOffsets
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hfirst, hsecond]

private theorem differingByteOffsets_twoWordSegments
    (bs : Bytes) (first second : Nat)
    (hsep : first + 32 ≤ second) (hlast : second + 32 ≤ bs.length) :
    differingByteOffsets 0 (twoWordSegments bs first second 0)
        (twoWordSegments bs first second B256.max) =
      wordByteOffsets [first, second] := by
  have hprefix : (bs.take first).length = first := by
    rw [List.length_take]
    apply Nat.min_eq_left
    omega
  have hgap :
      ((bs.drop (first + 32)).take
        (second - (first + 32))).length = second - (first + 32) := by
    rw [List.length_take]
    apply Nat.min_eq_left
    rw [List.length_drop]
    omega
  unfold twoWordSegments
  simp only [List.append_assoc]
  rw [differingByteOffsets_append_same]
  rw [differingByteOffsets_append
    (xs := (0 : B256).toBytes) (ys := B256.max.toBytes)
    (hlen := by rw [B256.length_toBytes, B256.length_toBytes])]
  rw [differingByteOffsets_append_same]
  rw [differingByteOffsets_append
    (xs := (0 : B256).toBytes) (ys := B256.max.toBytes)
    (hlen := by rw [B256.length_toBytes, B256.length_toBytes])]
  rw [differingByteOffsets_self]
  simp only [hprefix, hgap, B256.length_toBytes, Nat.zero_add]
  rw [show first + 32 + (second - (first + 32)) = second by omega]
  have hzero : (0 : B256).toBytes = List.replicate 32 0 := by
    decide +kernel
  have hmax : B256.max.toBytes = List.replicate 32 255 := by
    decide +kernel
  rw [hzero, hmax]
  repeat rw [differingByteOffsets_replicate_ne (hxy := by decide)]
  rfl

private theorem immutableWordOffsets_eq_two
    (field : ImmutableParameter) (first second : Nat)
    (hsep : first + 32 ≤ second)
    (hlast : second + 32 ≤ runtimeTemplateCode.length)
    (hsliceFirst :
      (runtimeTemplateCode.drop first).take 32 = (0 : B256).toBytes)
    (hsliceSecond :
      (runtimeTemplateCode.drop second).take 32 = (0 : B256).toBytes)
    (hcompile : Prog.compile (runtime (immutableMarkerParams field)) =
      some (patchAtOffsets runtimeTemplateCode B256.max [first, second]))
    (hruns : contiguousRunStarts (wordByteOffsets [first, second]) =
      [first, second]) :
    immutableWordOffsets field = [first, second] := by
  have hzero :
      runtimeTemplateCode =
        twoWordSegments runtimeTemplateCode first second 0 := by
    calc
      runtimeTemplateCode =
          twoWordChunks runtimeTemplateCode first second :=
        (twoWordChunks_eq runtimeTemplateCode first second hsep).symm
      _ = twoWordSegments runtimeTemplateCode first second 0 := by
        unfold twoWordChunks twoWordSegments
        rw [hsliceFirst, hsliceSecond]
  have hmarker :
      lidoCircuitBreakerCode (immutableMarkerParams field) =
        twoWordSegments runtimeTemplateCode first second B256.max := by
    calc
      lidoCircuitBreakerCode (immutableMarkerParams field) =
          patchAtOffsets runtimeTemplateCode B256.max [first, second] :=
        markerCode_eq_patchAtOffsets field [first, second] hcompile
      _ = patchAtOffsets
          (twoWordSegments runtimeTemplateCode first second 0)
          B256.max [first, second] :=
        congrArg (fun code =>
          patchAtOffsets code B256.max [first, second]) hzero
      _ = twoWordSegments runtimeTemplateCode first second B256.max :=
        patchAtOffsets_twoWordSegments runtimeTemplateCode first second
          hsep hlast
  unfold immutableWordOffsets
  calc
    contiguousRunStarts
          (differingByteOffsets 0 runtimeTemplateCode
            (lidoCircuitBreakerCode (immutableMarkerParams field))) =
        contiguousRunStarts
          (differingByteOffsets 0
            (twoWordSegments runtimeTemplateCode first second 0)
            (twoWordSegments runtimeTemplateCode first second B256.max)) := by
      exact congrArg contiguousRunStarts
        (congrArg₂ (differingByteOffsets 0) hzero hmarker)
    _ = contiguousRunStarts (wordByteOffsets [first, second]) := by
      rw [differingByteOffsets_twoWordSegments runtimeTemplateCode
        first second hsep hlast]
    _ = [first, second] := hruns

private theorem immutableWordOffsets_minPauseDuration_exact :
    immutableWordOffsets .minPauseDuration = [217, 713] := by
  rcases runtimeTemplateCode_immutable_slices_zero with
    ⟨_, _, _, _, h217, h713, _, _, _, _, _, _⟩
  rcases immutableMarkerPrograms_compile with ⟨_, hcompile, _, _, _⟩
  exact immutableWordOffsets_eq_two .minPauseDuration 217 713
    (by omega) (by rw [runtimeTemplateCode_length_exact]; omega)
    h217 h713 hcompile (by
      unfold contiguousRunStarts wordByteOffsets
      decide +kernel)

private theorem immutableWordOffsets_maxPauseDuration_exact :
    immutableWordOffsets .maxPauseDuration = [258, 1961] := by
  rcases runtimeTemplateCode_immutable_slices_zero with
    ⟨_, _, _, _, _, _, h258, h1961, _, _, _, _⟩
  rcases immutableMarkerPrograms_compile with ⟨_, _, hcompile, _, _⟩
  exact immutableWordOffsets_eq_two .maxPauseDuration 258 1961
    (by omega) (by rw [runtimeTemplateCode_length_exact]; omega)
    h258 h1961 hcompile (by
      unfold contiguousRunStarts wordByteOffsets
      decide +kernel)

private theorem immutableWordOffsets_minHeartbeatInterval_exact :
    immutableWordOffsets .minHeartbeatInterval = [508, 1137] := by
  rcases runtimeTemplateCode_immutable_slices_zero with
    ⟨_, _, _, _, _, _, _, _, h508, h1137, _, _⟩
  rcases immutableMarkerPrograms_compile with ⟨_, _, _, hcompile, _⟩
  exact immutableWordOffsets_eq_two .minHeartbeatInterval 508 1137
    (by omega) (by rw [runtimeTemplateCode_length_exact]; omega)
    h508 h1137 hcompile (by
      unfold contiguousRunStarts wordByteOffsets
      decide +kernel)

private theorem immutableWordOffsets_maxHeartbeatInterval_exact :
    immutableWordOffsets .maxHeartbeatInterval = [672, 1178] := by
  rcases runtimeTemplateCode_immutable_slices_zero with
    ⟨_, _, _, _, _, _, _, _, _, _, h672, h1178⟩
  rcases immutableMarkerPrograms_compile with ⟨_, _, _, _, hcompile⟩
  exact immutableWordOffsets_eq_two .maxHeartbeatInterval 672 1178
    (by omega) (by rw [runtimeTemplateCode_length_exact]; omega)
    h672 h1178 hcompile (by
      unfold contiguousRunStarts wordByteOffsets
      decide +kernel)

/-! ## The four-occurrence administrator immutable -/

private def fourWordChunks
    (bs : Bytes) (first second third fourth : Nat) : Bytes :=
  bs.take first ++ (bs.drop first).take 32 ++
    (bs.drop (first + 32)).take (second - (first + 32)) ++
    (bs.drop second).take 32 ++
    (bs.drop (second + 32)).take (third - (second + 32)) ++
    (bs.drop third).take 32 ++
    (bs.drop (third + 32)).take (fourth - (third + 32)) ++
    (bs.drop fourth).take 32 ++ bs.drop (fourth + 32)

private theorem fourWordChunks_eq
    (bs : Bytes) (first second third fourth : Nat)
    (hfirstSecond : first + 32 ≤ second)
    (hsecondThird : second + 32 ≤ third)
    (hthirdFourth : third + 32 ≤ fourth) :
    fourWordChunks bs first second third fourth = bs := by
  unfold fourWordChunks
  rw [← List.take_add, ← List.take_add]
  rw [show first + 32 + (second - (first + 32)) = second by omega]
  rw [← List.take_add, ← List.take_add]
  rw [show second + 32 + (third - (second + 32)) = third by omega]
  rw [← List.take_add, ← List.take_add]
  rw [show third + 32 + (fourth - (third + 32)) = fourth by omega]
  rw [← List.take_add]
  exact List.take_append_drop _ _

private def fourWordSegments
    (bs : Bytes) (first second third fourth : Nat) (word : B256) : Bytes :=
  bs.take first ++ word.toBytes ++
    (bs.drop (first + 32)).take (second - (first + 32)) ++
    word.toBytes ++
    (bs.drop (second + 32)).take (third - (second + 32)) ++
    word.toBytes ++
    (bs.drop (third + 32)).take (fourth - (third + 32)) ++
    word.toBytes ++ bs.drop (fourth + 32)

private theorem adminMarkerProgram_compile_segments :
    Prog.compile (runtime (immutableMarkerParams .admin)) =
      some (fourWordSegments runtimeTemplateCode 174 1094 1833 1920
        B256.max) := by
  decide +kernel

private theorem differingByteOffsets_fourWordSegments
    (bs : Bytes) (first second third fourth : Nat)
    (hfirstSecond : first + 32 ≤ second)
    (hsecondThird : second + 32 ≤ third)
    (hthirdFourth : third + 32 ≤ fourth)
    (hlast : fourth + 32 ≤ bs.length) :
    differingByteOffsets 0
        (fourWordSegments bs first second third fourth 0)
        (fourWordSegments bs first second third fourth B256.max) =
      wordByteOffsets [first, second, third, fourth] := by
  have hprefix : (bs.take first).length = first := by
    rw [List.length_take]
    apply Nat.min_eq_left
    omega
  have hgap₁ :
      ((bs.drop (first + 32)).take
        (second - (first + 32))).length = second - (first + 32) := by
    rw [List.length_take]
    apply Nat.min_eq_left
    rw [List.length_drop]
    omega
  have hgap₂ :
      ((bs.drop (second + 32)).take
        (third - (second + 32))).length = third - (second + 32) := by
    rw [List.length_take]
    apply Nat.min_eq_left
    rw [List.length_drop]
    omega
  have hgap₃ :
      ((bs.drop (third + 32)).take
        (fourth - (third + 32))).length = fourth - (third + 32) := by
    rw [List.length_take]
    apply Nat.min_eq_left
    rw [List.length_drop]
    omega
  unfold fourWordSegments
  simp only [List.append_assoc]
  rw [differingByteOffsets_append_same]
  rw [differingByteOffsets_append
    (xs := (0 : B256).toBytes) (ys := B256.max.toBytes)
    (hlen := by rw [B256.length_toBytes, B256.length_toBytes])]
  rw [differingByteOffsets_append_same]
  rw [differingByteOffsets_append
    (xs := (0 : B256).toBytes) (ys := B256.max.toBytes)
    (hlen := by rw [B256.length_toBytes, B256.length_toBytes])]
  rw [differingByteOffsets_append_same]
  rw [differingByteOffsets_append
    (xs := (0 : B256).toBytes) (ys := B256.max.toBytes)
    (hlen := by rw [B256.length_toBytes, B256.length_toBytes])]
  rw [differingByteOffsets_append_same]
  rw [differingByteOffsets_append
    (xs := (0 : B256).toBytes) (ys := B256.max.toBytes)
    (hlen := by rw [B256.length_toBytes, B256.length_toBytes])]
  rw [differingByteOffsets_self]
  simp only [hprefix, hgap₁, hgap₂, hgap₃, B256.length_toBytes,
    Nat.zero_add]
  rw [show first + 32 + (second - (first + 32)) = second by omega]
  rw [show second + 32 + (third - (second + 32)) = third by omega]
  rw [show third + 32 + (fourth - (third + 32)) = fourth by omega]
  have hzero : (0 : B256).toBytes = List.replicate 32 0 := by
    decide +kernel
  have hmax : B256.max.toBytes = List.replicate 32 255 := by
    decide +kernel
  rw [hzero, hmax]
  repeat rw [differingByteOffsets_replicate_ne (hxy := by decide)]
  rfl

private theorem immutableWordOffsets_admin_exact :
    immutableWordOffsets .admin = [174, 1094, 1833, 1920] := by
  rcases runtimeTemplateCode_immutable_slices_zero with
    ⟨h174, h1094, h1833, h1920, _, _, _, _, _, _, _, _⟩
  have hzero : runtimeTemplateCode =
      fourWordSegments runtimeTemplateCode 174 1094 1833 1920 0 := by
    calc
      runtimeTemplateCode =
          fourWordChunks runtimeTemplateCode 174 1094 1833 1920 :=
        (fourWordChunks_eq runtimeTemplateCode 174 1094 1833 1920
          (by omega) (by omega) (by omega)).symm
      _ = fourWordSegments runtimeTemplateCode 174 1094 1833 1920 0 := by
        unfold fourWordChunks fourWordSegments
        rw [h174, h1094, h1833, h1920]
  have hmarker :
      lidoCircuitBreakerCode (immutableMarkerParams .admin) =
        fourWordSegments runtimeTemplateCode 174 1094 1833 1920
          B256.max := by
    unfold lidoCircuitBreakerCode
    rw [adminMarkerProgram_compile_segments]
    rfl
  unfold immutableWordOffsets
  calc
    contiguousRunStarts
          (differingByteOffsets 0 runtimeTemplateCode
            (lidoCircuitBreakerCode (immutableMarkerParams .admin))) =
        contiguousRunStarts
          (differingByteOffsets 0
            (fourWordSegments runtimeTemplateCode 174 1094 1833 1920 0)
            (fourWordSegments runtimeTemplateCode 174 1094 1833 1920
              B256.max)) := by
      exact congrArg contiguousRunStarts
        (congrArg₂ (differingByteOffsets 0) hzero hmarker)
    _ = contiguousRunStarts
        (wordByteOffsets [174, 1094, 1833, 1920]) := by
      rw [differingByteOffsets_fourWordSegments runtimeTemplateCode
        174 1094 1833 1920 (by omega) (by omega) (by omega)
        (by rw [runtimeTemplateCode_length_exact]; omega)]
    _ = [174, 1094, 1833, 1920] := by
      unfold contiguousRunStarts wordByteOffsets
      decide +kernel

/-- Exact compiler-derived payload coordinates consumed by the constructor.
The conjunction order follows `immutableParameters` and therefore the source
order of `patchRuntimeLineForProof`. -/
theorem constructor_immutable_word_offsets_exact :
    immutableWordOffsets .admin = [174, 1094, 1833, 1920] ∧
    immutableWordOffsets .minPauseDuration = [217, 713] ∧
    immutableWordOffsets .maxPauseDuration = [258, 1961] ∧
    immutableWordOffsets .minHeartbeatInterval = [508, 1137] ∧
    immutableWordOffsets .maxHeartbeatInterval = [672, 1178] := by
  exact ⟨immutableWordOffsets_admin_exact,
    immutableWordOffsets_minPauseDuration_exact,
    immutableWordOffsets_maxPauseDuration_exact,
    immutableWordOffsets_minHeartbeatInterval_exact,
    immutableWordOffsets_maxHeartbeatInterval_exact⟩

/-! ## Constructor compiler and creation-layout identities -/

private theorem provisionalConstructorProgram_compiles :
    Prog.compiles (constructorProgramForProof 0 0 4282) = true := by
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [constructorProgramForProof_eq, constructorBodyForProof_eq,
    constructorEventScratchForProof_eq, patchRuntimeLineForProof_eq,
    patchFieldLineForProof_eq, patchArgumentIndexForProof_eq,
    loadArgumentIndexForProof_eq, storeByteOffsetForProof_eq,
    pushCompactNatForProof_eq, pushFixedNatForProof_eq,
    constructorErrorForProof_eq, constructorRuntimeBaseForProof_eq,
    immutableParameters, List.flatMap_cons, List.flatMap_nil,
    hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat]
  decide +kernel

/-- The first compiler pass has the same 616-byte shape as the final
constructor. -/
theorem provisionalConstructorPrefix_length_exact :
    provisionalConstructorPrefixForProof.length = 616 := by
  rw [provisionalConstructorPrefixForProof_eq]
  rw [runtimeTemplateCode_length_exact]
  have hcompile := Prog.compile_eq_some_getD_of_compiles
    (constructorProgramForProof 0 0 4282) provisionalConstructorProgram_compiles
  rw [Prog.length_compile hcompile]
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [constructorProgramForProof_eq, constructorBodyForProof_eq,
    constructorEventScratchForProof_eq, patchRuntimeLineForProof_eq,
    patchFieldLineForProof_eq, patchArgumentIndexForProof_eq,
    loadArgumentIndexForProof_eq, storeByteOffsetForProof_eq,
    pushCompactNatForProof_eq, pushFixedNatForProof_eq,
    constructorErrorForProof_eq, constructorRuntimeBaseForProof_eq,
    immutableParameters, List.flatMap_cons, List.flatMap_nil,
    hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat]
  decide +kernel

private theorem finalConstructorProgram_compiles :
    Prog.compiles (constructorProgramForProof 616 4898 4282) = true := by
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [constructorProgramForProof_eq, constructorBodyForProof_eq,
    constructorEventScratchForProof_eq, patchRuntimeLineForProof_eq,
    patchFieldLineForProof_eq, patchArgumentIndexForProof_eq,
    loadArgumentIndexForProof_eq, storeByteOffsetForProof_eq,
    pushCompactNatForProof_eq, pushFixedNatForProof_eq,
    constructorErrorForProof_eq, constructorRuntimeBaseForProof_eq,
    immutableParameters, List.flatMap_cons, List.flatMap_nil,
    hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat]
  decide +kernel

/-- Exact successful compilation of the table-bearing constructor prefix.
This is the compiler witness used by appended-runtime execution. -/
theorem lidoCircuitBreakerConstructorProgram_compile :
    Prog.compile lidoCircuitBreakerConstructorProgram =
      some lidoCircuitBreakerInitPrefix := by
  unfold lidoCircuitBreakerInitPrefix
  apply Prog.compile_eq_some_getD_of_compiles
  rw [DeploymentProof.lidoCircuitBreakerConstructorProgram_eq]
  rw [provisionalConstructorPrefix_length_exact,
    runtimeTemplateCode_length_exact]
  norm_num
  exact finalConstructorProgram_compiles

/-- Exact constructor prefix length, hence exact runtime and ABI coordinates. -/
theorem lidoCircuitBreakerInitPrefix_length_exact :
    lidoCircuitBreakerInitPrefix.length = 616 := by
  rw [Prog.length_compile lidoCircuitBreakerConstructorProgram_compile]
  rw [DeploymentProof.lidoCircuitBreakerConstructorProgram_eq]
  rw [provisionalConstructorPrefix_length_exact,
    runtimeTemplateCode_length_exact]
  norm_num
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [constructorProgramForProof_eq, constructorBodyForProof_eq,
    constructorEventScratchForProof_eq, patchRuntimeLineForProof_eq,
    patchFieldLineForProof_eq, patchArgumentIndexForProof_eq,
    loadArgumentIndexForProof_eq, storeByteOffsetForProof_eq,
    pushCompactNatForProof_eq, pushFixedNatForProof_eq,
    constructorErrorForProof_eq, constructorRuntimeBaseForProof_eq,
    immutableParameters, List.flatMap_cons, List.flatMap_nil,
    hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat]
  decide +kernel

/-- The official twelve-write patch plan reconstructs the exact official
runtime compiler artifact. -/
theorem patchRuntimeTemplate_official :
    patchRuntimeTemplate officialParams =
      lidoCircuitBreakerCode officialParams := by
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [patchRuntimeTemplate, runtimeImmutablePatches,
    immutableParameters, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, hadmin, hminPause, hmaxPause,
    hminHeartbeat, hmaxHeartbeat, ImmutableParameter.value]
  decide +kernel

/-- Exact code coordinate at which the seven-word constructor head begins. -/
theorem lidoCircuitBreakerCreationTemplate_length_exact :
    lidoCircuitBreakerCreationTemplate.length = 4898 := by
  simp [lidoCircuitBreakerCreationTemplate,
    lidoCircuitBreakerInitPrefix_length_exact,
    runtimeTemplateCode_length_exact]

/-- The frozen official input is exactly prefix, neutral runtime, then the
official seven-word ABI head. -/
theorem officialFullCreateInput_eq_layout :
    officialFullCreateInput =
      lidoCircuitBreakerInitPrefix ++ runtimeTemplateCode ++
        abiEncodeConstructorArgs officialConstructorArgs := by
  rfl

/-- Exact full official creation-input length observed by `CODESIZE`. -/
theorem officialFullCreateInput_length_exact :
    officialFullCreateInput.length = 5122 := by
  rw [officialFullCreateInput_eq_layout]
  simp [lidoCircuitBreakerInitPrefix_length_exact,
    runtimeTemplateCode_length_exact, abiEncodeConstructorArgs_length,
    constructorArgumentBytes]

end LidoCircuitBreaker

end Blanc
