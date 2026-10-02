import Blanc.ExecutionTraceCalldata

namespace Blanc.PrecompileOutputBound

open Jaune

/-- Successful precompile results carry less than a word-indexed length. -/
def ShortOutput : PrecompResult → Prop
  | .error _ _ => True
  | .ok _ bytes => bytes.length < 2^256

private theorem chargeGas_output (cost : Nat) (evm : Evm)
    (pr : Unit → PrecompResult) (h : ShortOutput (pr ())) :
    ShortOutput (PrecompResult.chargeGas cost evm pr) := by
  unfold PrecompResult.chargeGas
  split
  · exact h
  · exact True.intro

private theorem pack_length (bytes : Bytes) (n : Nat) :
    (bytes.pack n).length = n :=
  List.length_takeRightD n bytes 0

private theorem bnp_length (p : BNP) : p.toBytes.length = 64 := by
  simp only [BNP.toBytes, List.length_append, pack_length]

private theorem blsp_length (p : BLSP) : p.toBytes.length = 128 := by
  simp only [BLSP.toBytes, List.length_append, pack_length]

private theorem blsf2_length (p : BLSF2) : p.toBytes.length = 128 := by
  simp only [BLSF2.toBytes, List.length_append, pack_length]

private theorem blsp2_length (p : BLSP2) : p.toBytes.length = 256 := by
  simp only [BLSP2.toBytes, List.length_append, blsf2_length]

private theorem short_fixed {bytes : Bytes} (h : bytes.length ≤ 256) :
    bytes.length < 2^256 :=
  Nat.lt_of_le_of_lt h (by decide)

-- Follow only result constructors, conditionals and the gas wrapper.
-- Crypto intermediates remain opaque.
open _root_.Lean _root_.Lean.Elab.Tactic in
syntax "precomp_shape" : tactic

open _root_.Lean _root_.Lean.Elab.Tactic in
elab_rules : tactic
| `(tactic| precomp_shape) => do
  withoutRecover <| evalTactic (← `(tactic| try dsimp only []))
  withoutRecover <| evalTactic (← `(tactic|
    first
    | exact True.intro
    | (apply chargeGas_output; precomp_shape)
    | (change _ < 2^256
       apply short_fixed
       simp only [List.length_nil, List.length_append, B256.length_toBytes,
         bnp_length, blsp_length, blsp2_length]
       decide)
    | (split <;> precomp_shape)))

private theorem ecrecover_output (evm : Evm) : ShortOutput (executeEcrecover evm) := by
  unfold executeEcrecover
  precomp_shape

private theorem p256_output (evm : Evm) : ShortOutput (executeP256Verify evm) := by
  unfold executeP256Verify
  precomp_shape

private theorem sha256_output (evm : Evm) : ShortOutput (executeSha256 evm) := by
  unfold executeSha256
  precomp_shape

private theorem ripemd_output (evm : Evm) : ShortOutput (executeRipemd160 evm) := by
  unfold executeRipemd160
  precomp_shape

private theorem ecadd_output (evm : Evm) : ShortOutput (executeEcadd evm) := by
  unfold executeEcadd
  precomp_shape

private theorem ecmul_output (evm : Evm) : ShortOutput (executeEcmul evm) := by
  unfold executeEcmul
  precomp_shape

private theorem point_eval_output (evm : Evm) : ShortOutput (executePointEval evm) := by
  unfold executePointEval
  precomp_shape

private theorem g1add_output (evm : Evm) : ShortOutput (executeBls12G1Add evm) := by
  unfold executeBls12G1Add
  precomp_shape

private theorem g1msm_output (evm : Evm) : ShortOutput (executeBls12G1Msm evm) := by
  unfold executeBls12G1Msm
  precomp_shape

private theorem g2add_output (evm : Evm) : ShortOutput (executeBls12G2Add evm) := by
  unfold executeBls12G2Add
  precomp_shape

private theorem g2msm_output (evm : Evm) : ShortOutput (executeBls12G2Msm evm) := by
  unfold executeBls12G2Msm
  precomp_shape

private theorem g1map_output (evm : Evm) : ShortOutput (executeBls12MapFpToG1 evm) := by
  unfold executeBls12MapFpToG1
  precomp_shape

private theorem g2map_output (evm : Evm) : ShortOutput (executeBls12MapFp2ToG2 evm) := by
  unfold executeBls12MapFp2ToG2
  precomp_shape

private theorem identity_output (evm : Evm) (hi : evm.sta.data.length < 2^256) :
    ShortOutput (executeId evm) := by
  unfold executeId
  apply chargeGas_output
  exact hi

private theorem sliceToNat_lt (data : Bytes) (start width : Nat) :
    Bytes.sliceToNat data start width < 256^width := by
  unfold Bytes.sliceToNat
  split
  · exact Nat.pow_pos (by decide)
  · split
    · split
      · exact Nat.pow_pos (by decide)
      · apply Bytes.toNat_lt_of_length_le
        rw [List.takeD_length]
    · apply Bytes.toNat_lt_of_length_le
      rw [List.length_take]
      exact Nat.min_le_left _ _

private theorem modexp_output (evm : Evm) : ShortOutput (executeModexp evm) := by
  have hwidth : Bytes.sliceToNat evm.sta.data 64 32 < 2^256 := by
    simpa only [show (256 : Nat)^32 = 2^256 from by decide] using
      sliceToNat_lt evm.sta.data 64 32
  unfold executeModexp
  dsimp only
  split
  · exact True.intro
  · apply chargeGas_output
    split
    · exact short_fixed (by decide)
    · change List.length (if _ then _ else _) < 2^256
      split
      · rw [List.length_replicate]
        exact hwidth
      · rw [pack_length]
        exact hwidth

private def ShortPair : Except (EvmError × Nat) (Nat × Bytes) → Prop
  | .error _ => True
  | .ok v => v.2.length < 2^256

private theorem pair_bind {α : Type} (r : Except (EvmError × Nat) α)
    (f : α → Except (EvmError × Nat) (Nat × Bytes))
    (hf : ∀ v, ShortPair (f v)) : ShortPair (r >>= f) := by
  cases r with
  | error e => exact True.intro
  | ok v => exact hf v

private theorem bls_pairing_inner_output (data : Bytes) (cost : Nat) :
    ShortPair (executeBls12PairingInner data cost) := by
  unfold executeBls12PairingInner
  apply pair_bind
  intro result
  change List.length (if result = 1 then (1 : Nat).toB256.toBytes
    else (0 : Nat).toB256.toBytes) < 2^256
  split <;> rw [B256.length_toBytes] <;> decide

private theorem bn_pairing_inner_output (data : Bytes) (cost : Nat) :
    ShortPair (executePairingCheckInner data cost) := by
  unfold executePairingCheckInner
  split
  · exact True.intro
  · apply pair_bind
    intro result
    change List.length (if result = 1 then (1 : Nat).toB256.toBytes
      else (0 : Nat).toB256.toBytes) < 2^256
    split <;> rw [B256.length_toBytes] <;> decide

private theorem bls_pairing_output (evm : Evm) :
    ShortOutput (executeBls12Pairing evm) := by
  unfold executeBls12Pairing
  dsimp only
  split
  · exact True.intro
  · apply chargeGas_output
    have hp := bls_pairing_inner_output evm.sta.data
      (32600 * (evm.sta.data.length / 384) + 37700)
    split
    · rename_i cost output he
      rw [he] at hp
      exact hp
    · exact True.intro

private theorem bn_pairing_output (evm : Evm) :
    ShortOutput (executePairingCheck evm) := by
  unfold executePairingCheck
  apply chargeGas_output
  have hp := bn_pairing_inner_output evm.sta.data
    (34000 * (evm.sta.data.length / 192) + 45000)
  dsimp only
  split
  · rename_i cost output he
    rw [he] at hp
    exact hp
  · exact True.intro

private theorem compress_length {rounds : Nat} {h m : List UInt64}
    {t0 t1 : UInt64} {f : Bool} {bytes : Bytes}
    (hb : bCompress rounds h m t0 t1 f = some bytes) : bytes.length = 64 := by
  unfold bCompress at hb
  split at hb
  · split at hb
    · have he := Option.some.inj hb
      subst bytes
      simp only [List.length_flatten, List.map_map, Function.comp_def,
        List.takeD_length, List.map_const', List.sum_replicate_nat, Vector.length_toList]
    · cases hb
  · cases hb

private theorem blake2_output (evm : Evm) : ShortOutput (executeBlake2F evm) := by
  unfold executeBlake2F
  dsimp only
  split
  · exact True.intro
  · apply chargeGas_output
    split
    all_goals first
    | exact True.intro
    | (split
       · rename_i bytes he
         change bytes.length < 2^256
         rw [compress_length he]
         decide
       · exact True.intro)

/-- Every implemented precompile's successful output is short when its actual
input is short. Identity is the only branch requiring the input hypothesis. -/
theorem precompile_run_output (evm : Evm) (adr : Adr)
    (hi : evm.sta.data.length < 2^256) : ShortOutput (precompileRun evm adr) := by
  unfold precompileRun
  split <;> first
  | exact ecrecover_output evm
  | exact sha256_output evm
  | exact ripemd_output evm
  | exact identity_output evm hi
  | exact modexp_output evm
  | exact ecadd_output evm
  | exact ecmul_output evm
  | exact bn_pairing_output evm
  | exact blake2_output evm
  | exact point_eval_output evm
  | exact g1add_output evm
  | exact g1msm_output evm
  | exact g2add_output evm
  | exact g2msm_output evm
  | exact bls_pairing_output evm
  | exact g1map_output evm
  | exact g2map_output evm
  | exact p256_output evm
  | exact True.intro

/-- Both precompile outcome channels are bounded from the actual input and
frame seed. Exceptional results preserve that seed; successful results install
the output of the producer above. -/
theorem executePrecomp_output (evm : Evm) (adr : Adr)
    (hi : evm.sta.data.length < 2^256) (hs : evm.dyna.output.length < 2^256) :
    Execution.Rel (fun _ d => d.output.length < 2^256) evm.dyna (executePrecomp evm adr) := by
  have hp := precompile_run_output evm adr hi
  unfold executePrecomp applyPrecompResult
  cases hr : precompileRun evm adr with
  | error reason cost => exact hs
  | ok cost output =>
    rw [hr] at hp
    exact hp

end Blanc.PrecompileOutputBound
