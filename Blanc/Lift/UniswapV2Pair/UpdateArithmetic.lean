import Blanc.Lift.PackedWord
import Blanc.Lift.UniswapV2Pair.Layout
import Blanc.Lift.UniswapV2Pair.Cert
import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.ExactWalkCutOps

/-! Actual UQ112x112 helper routines used by the shared reserve update. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def uqEncodeWord (reserve : B256) : B256 :=
  reserveDiv112 * (reserveMask112 &&& reserve)

/-- The actual encoding helper returns to an arbitrary caller with its tail
preserved, after exactly 26 gas. -/
theorem uq_encode_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {reserve tag : B256}
    (room : R.length ≤ 1021) :
    SFunc.RunExact fs sevm (St b (reserve :: tag :: R) M (G + 26))
      t_2a57_c65 (.returned (St b (uqEncodeWord reserve :: R) M G)) := by
  unfold t_2a57_c65
  apply rx_dest
  apply rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := reserveDiv112) rfl (by simp only [List.length_cons]; omega)
  apply rx_mul rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  exact rx_ret

/-- Successful bytecode encoding has exactly the certified masked result. -/
theorem uq_encode_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {reserve tag : B256} {o : Outcome}
    (run : SFunc.Run fs sevm (St b (reserve :: tag :: R) M G) t_2a57_c65 o) :
    ∃ G', o = .returned (St b (uqEncodeWord reserve :: R) M G') := by
  have h := run.cut
  unfold t_2a57_c65 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mul hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩

def uqMask224 : B256 := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def uqDivWord (denominator numerator : B256) : B256 :=
  (numerator &&& uqMask224) / (denominator &&& reserveMask112)

/-- The actual division helper checks its masked denominator and returns the
quotient after exactly 64 gas. -/
theorem uq_div_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {den num tag : B256}
    (nonzero : den &&& reserveMask112 ≠ 0) (room : R.length ≤ 1016) :
    SFunc.RunExact fs sevm (St b (den :: num :: tag :: R) M (G + 64))
      t_2a7b_c66 (.returned (St b (uqDivWord den num :: R) M G)) := by
  unfold t_2a7b_c66 t_2ab4_c66
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := den) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := uqMask224) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := num) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := den &&& reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2ab4) rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ nonzero
  apply rx_dest
  apply rx_div rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (S' := tag :: 0 :: den :: num :: uqDivWord den num :: R) rfl
  apply rx_swap (S' := num :: 0 :: den :: tag :: uqDivWord den num :: R) rfl
  apply rx_pop
  apply rx_pop
  apply rx_pop
  exact rx_ret

/-- Any successful division derives the real nonzero guard and exact result. -/
theorem uq_div_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {den num tag : B256} {o : Outcome}
    (run : SFunc.Run fs sevm (St b (den :: num :: tag :: R) M G) t_2a7b_c66 o) :
    den &&& reserveMask112 ≠ 0 ∧
      ∃ G', o = .returned (St b (uqDivWord den num :: R) M G') := by
  have h := run.cut
  unfold t_2a7b_c66 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨_, _, h⟩ | ⟨nonzero, _, h⟩
  · exact False.elim (ric_undefined h)
  · unfold t_2ab4_c66 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_div hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨g, hg⟩ := ric_ret h
    exact ⟨nonzero, g, Seg.done.inj hg⟩

/-- The masked encoding agrees with the source UQ numerator for a uint112
cached reserve. -/
theorem uqEncodeWord_source {reserve : B256} (bounded : reserve.toNat < 2 ^ 112) :
    uqEncodeWord reserve = (reserve.toNat * 2 ^ 112).toB256 := by
  have productBound : reserve.toNat * 2 ^ 112 < 2 ^ 256 :=
    lt_trans (Nat.mul_lt_mul_of_pos_right bounded (by decide)) (by decide)
  unfold uqEncodeWord
  rw [B256.and_comm,
    show reserveMask112 = (2 ^ 112 - 1).toB256 from rfl,
    PackedWord.lowMask_eq_self_of_lt (by decide) bounded]
  apply B256.toNat_inj
  rw [B256.toNat_mul_mod,
    show reserveDiv112.toNat = 2 ^ 112 from rfl, Nat.mul_comm,
    Nat.mod_eq_of_lt productBound, B256.toNat_toB256_of_lt productBound]

/-- The helper quotient agrees with the unwrapped source division for its
bounded cached denominator and encoded numerator. -/
theorem uqDivWord_source {den num : B256} (denBound : den.toNat < 2 ^ 112)
    (numBound : num.toNat < 2 ^ 224) (nonzero : den ≠ 0) :
    uqDivWord den num = (num.toNat / den.toNat).toB256 := by
  unfold uqDivWord
  rw [show reserveMask112 = (2 ^ 112 - 1).toB256 from rfl,
    show uqMask224 = (2 ^ 224 - 1).toB256 from rfl,
    PackedWord.lowMask_eq_self_of_lt (by decide) numBound,
    PackedWord.lowMask_eq_self_of_lt (by decide) denBound]
  apply B256.toNat_inj
  rw [B256.toNat_div nonzero,
    B256.toNat_toB256_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (B256.toNat_lt num))]

/-- Actual TIMESTAMP/AND result at the shared update header. -/
def updateTimestampWord (timestamp : B256) : B256 := reserveMask32 &&& timestamp

/-- The unmasked word difference carried by the bytecode through the oracle
branch. The field mask is applied separately at every elapsed-time use. -/
def updateElapsedWord (raw timestamp : B256) : B256 :=
  updateTimestampWord timestamp - reserveTimestampRead raw

/-- Exact current-slot elapsed time. Cached reserve arguments do not occur in
this law and need not equal the currently stored reserves. -/
theorem updateElapsedWord_source {raw timestamp : B256} {last : Nat}
    (lastRead : (reserveTimestampRead raw).toNat = last) (lastBound : last < 2 ^ 32) :
    (updateElapsedWord raw timestamp &&& reserveMask32).toNat =
      (timestamp.toNat % 2 ^ 32 + 2 ^ 32 - last) % 2 ^ 32 := by
  have timestampRead : (updateTimestampWord timestamp).toNat = timestamp.toNat % 2 ^ 32 := by
    unfold updateTimestampWord
    rw [B256.and_comm, show reserveMask32 = (2 ^ 32 - 1).toB256 from rfl]
    exact PackedWord.lowMask_toNat timestamp (by decide)
  unfold updateElapsedWord
  rw [show reserveMask32 = (2 ^ 32 - 1).toB256 from rfl,
    PackedWord.lowMask_sub_toNat (by decide) (by rw [lastRead]; exact lastBound),
    timestampRead, lastRead]

/-- Mandated modular statement control: timestamp zero after the maximal
uint32 timestamp contributes one elapsed second. -/
theorem update_timestamp_wrap_control :
    (((0 : B256) - (2 ^ 32 - 1).toB256) &&& reserveMask32).toNat = 1 := by
  decide

end Blanc.Lift.UniswapV2Pair
