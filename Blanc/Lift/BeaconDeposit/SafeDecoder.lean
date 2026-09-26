import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.BeaconDeposit.DepositDecode
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.Quiet

namespace Blanc.Lift.BeaconDeposit

def bodySet : List Nat := [3, 4, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26]

theorem bodySet_noHalt : NoHaltSet prog bodySet = true := by
  decide +kernel

end Blanc.Lift.BeaconDeposit
/-!
# Safety segment W: the `deposit` wrapper and ABI decoder, inverted

A successful run of the `deposit` wrapper (entry 32) passes every decoder guard — the calldata is
`DepositDecodable` — calls the body (entry 7) from the frozen argument stack over `mem0`, and
halts by the `STOP` at the return tag `0x01b8`, whose post state has the body's storage and logs.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeDecoder
/-- **Decoder inversion (`t_00a4_c32`, about 200 nodes).**

Proof sketch.  Walk the wrapper's straight lines by `cases` (as `safe_dispatch`); each of the
decoder's `JUMPI` guards (head size `CDS - 4 ≥ 0x80`, per tail the four comparisons of
`TailDecodable`) has its failing arm end in `PUSH 0 DUP REVERT`, which has no successful
`Linst.Run`, so each comparison word is `0`/nonzero as `DepositDecodable` states (read the
words through `B256.ltCheck`/`gtCheck` and `toNat`; `hcd` keeps `CALLDATASIZE` exact).  The
`callNext 7 t_01b8_c32` node is `.callRet` (the body only returns: `.callHalt` would need the
body to halt successfully, and the body has no successful halting leaf — or keep both cases and
note `callHalt` gives `.halted` directly, which the statement also covers by taking the body's
result); the pushed words are `depositArgStack sevm [sel]` (`DepositArgs.lean`).  `t_01b8_c32`
is `JUMPDEST; STOP`: `Burn.world` and `Linst.world_of_ok` (`Quiet.lean`). -/
theorem safe_decoder {sevm : Sevm} {b post : Devm} {sel : B256} {G : Nat}
    (hcd : sevm.data.length < 2 ^ 256)
    (run : SFunc.Run prog sevm (St b [sel] mem0 G) t_00a4_c32 (.halted post)) :
    DepositDecodable sevm ∧ ∃ G' d,
      SFunc.Run prog sevm (St b (depositArgStack sevm [sel]) mem0 G') t_0304_c7 (.returned d) ∧
      (∀ a, Devm.getStor post a = Devm.getStor d a) ∧ post.logs = d.logs := by
  have hlen : sevm.data.length.toB256.toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  have hmax : (Nat.toB256 (2 ^ 32)).toNat = 2 ^ 32 := by decide
  have hmaxword : Bytes.toB256 [0x01, 0, 0, 0, 0] = Nat.toB256 (2 ^ 32) := by decide
  have h80 : (Bytes.toB256 [0x80] : B256).toNat = 128 := by decide
  have h4b : Bytes.toB256 [0x04] = (4 : B256) := by decide
  have h20b : Bytes.toB256 [0x20] = (32 : B256) := by decide
  have h1b : Bytes.toB256 [0x01] = (1 : B256) := by decide
  have hret_tag : Bytes.toB256 [0x01, 0xb8] = (0x01b8 : B256) := by decide
  have h36b : (4 : B256) + 32 = (36 : B256) := by decide
  have h68b : (36 : B256) + 32 = (68 : B256) := by decide
  have h100b : (68 : B256) + 32 = (100 : B256) := by decide
  have run := run.cut

  -- Tree 1: t_00a4_c32 (head guard: CDS - 4 ≥ 0x80)
  unfold t_00a4_c32 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  rw [hret_tag] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  rw [h4b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_calldatasize s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_dup (w := sevm.data.length.toB256 - 4) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G12, run⟩ | ⟨hw_head, G12, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_head := eq_zero_of_iszero_ne_zero hw_head

  -- Tree 2: t_00ba_c32 (offset 0 guard 1: argOff 0 ≤ 2^32)
  unfold t_00ba_c32 at run
  obtain ⟨G13, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_add s1
  rw [B256.add_comm, B256.sub_add_cancel] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_add s1
  rw [h36b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_calldataload s1
  have hoff0 : Sevm.dataWord sevm 4 = argOff sevm 0 := by
    unfold argOff; rw [show (4 : B256) + 32 * Nat.toB256 0 = (4 : B256) by decide]
  rw [hoff0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_dup (w := argOff sevm 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G27, run⟩ | ⟨hw_off0_1, G27, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off0_1 := eq_zero_of_iszero_ne_zero hw_off0_1
  have ht0_1 : (argOff sevm 0).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_off0_1
    rwa [hmaxword, hmax] at h

  -- Tree 3: t_00d5_c32 (offset 0 guard 2: 4 + argOff 0 + 32 ≤ CDS)
  unfold t_00d5_c32 at run
  obtain ⟨G28, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_dup (w := sevm.data.length.toB256) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s1
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G33, rfl⟩ := ri_dup (w := (4 : B256) + argOff sevm 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G38, run⟩ | ⟨hw_off0_2, G38, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off0_2 := eq_zero_of_iszero_ne_zero hw_off0_2
  have ht0_2 : (4 + argOff sevm 0 + 32).toNat ≤ sevm.data.length := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_off0_2
    rwa [hlen] at h

  -- Arithmetic: 132 ≤ CDS
  have hhead : 132 ≤ sevm.data.length := by
    have hwrap0 : (4 : B256).toNat + (argOff sevm 0).toNat < 2 ^ 256 := by
      have : (4 : B256).toNat = 4 := by decide
      have := ht0_1; omega
    have h4_off : ((4 : B256) + argOff sevm 0).toNat = 4 + (argOff sevm 0).toNat := by
      rw [toNat_add_of_lt hwrap0, show (4 : B256).toNat = 4 by decide]
    have hwrap1 : ((4 : B256) + argOff sevm 0).toNat + (32 : B256).toNat < 2 ^ 256 := by
      rw [h4_off, show (32 : B256).toNat = 32 by decide]
      have := ht0_1; omega
    have h36le : 36 ≤ sevm.data.length := by
      have := ht0_2
      rw [toNat_add_of_lt hwrap1, h4_off, show (32 : B256).toNat = 32 by decide] at this
      omega
    have h4le : 4 ≤ sevm.data.length := by omega
    have hsub : (sevm.data.length.toB256 - 4).toNat = sevm.data.length - 4 := by
      rw [toNat_sub_of_toNat_le]
      · rw [hlen, show (4 : B256).toNat = 4 by decide]
      · rw [hlen, show (4 : B256).toNat = 4 by decide]; exact h4le
    have hge := toNat_ge_of_ltCheck_eq_zero hguard_head
    rw [h80, hsub] at hge
    omega

  -- Tree 4: t_00e7_c32 (len 0 guards: argLen 0 ≤ 2^32 and argPtr 0 + argLen 0 ≤ CDS)
  unfold t_00e7_c32 at run
  obtain ⟨G39, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G40, rfl⟩ := ri_dup (w := (4 : B256) + argOff sevm 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G41, rfl⟩ := ri_calldataload s1
  have hlen0 : Sevm.dataWord sevm ((4 : B256) + argOff sevm 0) = argLen sevm 0 := rfl
  rw [hlen0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_push s1
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_add s1
  have hptr0 : (32 : B256) + ((4 : B256) + argOff sevm 0) = argPtr sevm 0 := rfl
  rw [hptr0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G45, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G46, rfl⟩ := ri_dup (w := sevm.data.length.toB256) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G47, rfl⟩ := ri_push s1
  rw [h1b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G48, rfl⟩ := ri_dup (w := argLen sevm 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G49, rfl⟩ := ri_mul s1
  rw [mul_one_b256] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G50, rfl⟩ := ri_dup (w := argPtr sevm 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G51, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G52, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G53, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G54, rfl⟩ := ri_dup (w := argLen sevm 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G55, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G56, rfl⟩ := ri_or s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G57, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G58, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G59, run⟩ | ⟨hw_len0, G59, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_len0 := eq_zero_of_iszero_ne_zero hw_len0
  obtain ⟨hguard_len0_1, hguard_len0_2⟩ := B256.of_or_eq_zero hguard_len0
  have ht0_3 : (argLen sevm 0).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_len0_1
    rwa [hmaxword, hmax] at h
  have ht0_4 : (argPtr sevm 0 + argLen sevm 0).toNat ≤ sevm.data.length := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_len0_2
    rwa [hlen] at h
  have ht0 : TailDecodable sevm 0 := ⟨ht0_1, ht0_2, ht0_3, ht0_4⟩

  -- Tree 5: t_0109_c32 (tail 1, offset guard 1: argOff 1 ≤ 2^32)
  unfold t_0109_c32 at run
  obtain ⟨G60, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G61, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G62, rfl⟩ := ri_swap (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G63, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G64, rfl⟩ := ri_swap (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G65, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G66, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G67, rfl⟩ := ri_push s1
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G68, rfl⟩ := ri_dup (w := (36 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G69, rfl⟩ := ri_add s1
  rw [h68b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G70, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G71, rfl⟩ := ri_calldataload s1
  have hoff1 : Sevm.dataWord sevm 36 = argOff sevm 1 := by
    unfold argOff; rw [show (4 : B256) + 32 * Nat.toB256 1 = 36 by decide]
  rw [hoff1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G72, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G73, rfl⟩ := ri_dup (w := argOff sevm 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G74, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G75, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G76, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G77, run⟩ | ⟨hw_off1_1, G77, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off1_1 := eq_zero_of_iszero_ne_zero hw_off1_1
  have ht1_1 : (argOff sevm 1).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_off1_1
    rwa [hmaxword, hmax] at h

  -- Tree 6: t_0127_c32 (tail 1, offset guard 2: 4 + argOff 1 + 32 ≤ CDS)
  unfold t_0127_c32 at run
  obtain ⟨G78, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G79, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G80, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G81, rfl⟩ := ri_dup (w := sevm.data.length.toB256) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G82, rfl⟩ := ri_push s1
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G83, rfl⟩ := ri_dup (w := (4 : B256) + argOff sevm 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G84, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G85, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G86, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G87, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G88, run⟩ | ⟨hw_off1_2, G88, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off1_2 := eq_zero_of_iszero_ne_zero hw_off1_2
  have ht1_2 : (4 + argOff sevm 1 + 32).toNat ≤ sevm.data.length := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_off1_2
    rwa [hlen] at h

  -- Tree 7: t_0139_c32 (len 1 guards: argLen 1 ≤ 2^32 and argPtr 1 + argLen 1 ≤ CDS)
  unfold t_0139_c32 at run
  obtain ⟨G89, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G90, rfl⟩ := ri_dup (w := (4 : B256) + argOff sevm 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G91, rfl⟩ := ri_calldataload s1
  have hlen1 : Sevm.dataWord sevm ((4 : B256) + argOff sevm 1) = argLen sevm 1 := rfl
  rw [hlen1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G92, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G93, rfl⟩ := ri_push s1
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G94, rfl⟩ := ri_add s1
  have hptr1 : (32 : B256) + ((4 : B256) + argOff sevm 1) = argPtr sevm 1 := rfl
  rw [hptr1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G95, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G96, rfl⟩ := ri_dup (w := sevm.data.length.toB256) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G97, rfl⟩ := ri_push s1
  rw [h1b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G98, rfl⟩ := ri_dup (w := argLen sevm 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G99, rfl⟩ := ri_mul s1
  rw [mul_one_b256] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G100, rfl⟩ := ri_dup (w := argPtr sevm 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G101, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G102, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G103, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G104, rfl⟩ := ri_dup (w := argLen sevm 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G105, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G106, rfl⟩ := ri_or s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G107, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G108, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G109, run⟩ | ⟨hw_len1, G109, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_len1 := eq_zero_of_iszero_ne_zero hw_len1
  obtain ⟨hguard_len1_1, hguard_len1_2⟩ := B256.of_or_eq_zero hguard_len1
  have ht1_3 : (argLen sevm 1).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_len1_1
    rwa [hmaxword, hmax] at h
  have ht1_4 : (argPtr sevm 1 + argLen sevm 1).toNat ≤ sevm.data.length := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_len1_2
    rwa [hlen] at h
  have ht1 : TailDecodable sevm 1 := ⟨ht1_1, ht1_2, ht1_3, ht1_4⟩

  -- Tree 8: t_015b_c32 (tail 2, offset guard 1: argOff 2 ≤ 2^32)
  unfold t_015b_c32 at run
  obtain ⟨G110, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G111, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G112, rfl⟩ := ri_swap (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G113, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G114, rfl⟩ := ri_swap (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G115, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G116, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G117, rfl⟩ := ri_push s1
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G118, rfl⟩ := ri_dup (w := (68 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G119, rfl⟩ := ri_add s1
  rw [h100b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G120, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G121, rfl⟩ := ri_calldataload s1
  have hoff2 : Sevm.dataWord sevm 68 = argOff sevm 2 := by
    unfold argOff; rw [show (4 : B256) + 32 * Nat.toB256 2 = 68 by decide]
  rw [hoff2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G122, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G123, rfl⟩ := ri_dup (w := argOff sevm 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G124, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G125, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G126, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G127, run⟩ | ⟨hw_off2_1, G127, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off2_1 := eq_zero_of_iszero_ne_zero hw_off2_1
  have ht2_1 : (argOff sevm 2).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_off2_1
    rwa [hmaxword, hmax] at h

  -- Tree 9: t_0179_c32 (tail 2, offset guard 2: 4 + argOff 2 + 32 ≤ CDS)
  unfold t_0179_c32 at run
  obtain ⟨G128, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G129, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G130, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G131, rfl⟩ := ri_dup (w := sevm.data.length.toB256) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G132, rfl⟩ := ri_push s1
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G133, rfl⟩ := ri_dup (w := (4 : B256) + argOff sevm 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G134, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G135, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G136, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G137, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G138, run⟩ | ⟨hw_off2_2, G138, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off2_2 := eq_zero_of_iszero_ne_zero hw_off2_2
  have ht2_2 : (4 + argOff sevm 2 + 32).toNat ≤ sevm.data.length := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_off2_2
    rwa [hlen] at h

  -- Tree 10: t_018b_c32 (len 2 guards: argLen 2 ≤ 2^32 and argPtr 2 + argLen 2 ≤ CDS)
  unfold t_018b_c32 at run
  obtain ⟨G139, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G140, rfl⟩ := ri_dup (w := (4 : B256) + argOff sevm 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G141, rfl⟩ := ri_calldataload s1
  have hlen2 : Sevm.dataWord sevm ((4 : B256) + argOff sevm 2) = argLen sevm 2 := rfl
  rw [hlen2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G142, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G143, rfl⟩ := ri_push s1
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G144, rfl⟩ := ri_add s1
  have hptr2 : (32 : B256) + ((4 : B256) + argOff sevm 2) = argPtr sevm 2 := rfl
  rw [hptr2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G145, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G146, rfl⟩ := ri_dup (w := sevm.data.length.toB256) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G147, rfl⟩ := ri_push s1
  rw [h1b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G148, rfl⟩ := ri_dup (w := argLen sevm 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G149, rfl⟩ := ri_mul s1
  rw [mul_one_b256] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G150, rfl⟩ := ri_dup (w := argPtr sevm 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G151, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G152, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G153, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G154, rfl⟩ := ri_dup (w := argLen sevm 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G155, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G156, rfl⟩ := ri_or s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G157, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G158, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G159, run⟩ | ⟨hw_len2, G159, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_len2 := eq_zero_of_iszero_ne_zero hw_len2
  obtain ⟨hguard_len2_1, hguard_len2_2⟩ := B256.of_or_eq_zero hguard_len2
  have ht2_3 : (argLen sevm 2).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_len2_1
    rwa [hmaxword, hmax] at h
  have ht2_4 : (argPtr sevm 2 + argLen sevm 2).toNat ≤ sevm.data.length := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_len2_2
    rwa [hlen] at h
  have ht2 : TailDecodable sevm 2 := ⟨ht2_1, ht2_2, ht2_3, ht2_4⟩

  have hdec : DepositDecodable sevm := ⟨hhead, ht0, ht1, ht2⟩

  -- Tree 11: t_01ad_c32 (restage arguments and callNext 7 t_01b8_c32)
  unfold t_01ad_c32 at run
  obtain ⟨G160, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G161, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G162, rfl⟩ := ri_swap (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G163, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G164, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G165, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G166, rfl⟩ := ri_calldataload s1
  have hroot : Sevm.dataWord sevm 100 = argRoot sevm := rfl
  rw [hroot] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G167, rfl⟩ := ri_push s1
  change SFunc.RunCut prog sevm []
    (St b (Bytes.toB256 [0x03, 0x04] :: depositArgStack sevm [sel]) mem0 G167)
    (SFunc.callNext 7 t_01b8_c32) (.done (.halted post)) at run

  -- Call inversion
  obtain ⟨G', ⟨D, hrun_body, hrun_cont⟩ | ⟨D, hrun_body, heq⟩⟩ :=
    ric_call (k := 7) (hk := (show prog[7]? = some t_0304_c7 from rfl)) run
  · unfold t_01b8_c32 at hrun_cont
    cases hrun_cont with
    | dest hburn hlast =>
        cases hlast with
        | last hstop =>
            have hburn_w := Burn.world hburn
            have hstop_w := Linst.world_of_ok (by decide) hstop
            have hstor : ∀ a, Devm.getStor post a = Devm.getStor D a := by
              intro a
              rw [hstop_w.1, hburn_w.1]
            have hlogs : post.logs = D.logs := by
              rw [hstop_w.2, hburn_w.2]
            exact ⟨hdec, G', D, hrun_body, hstor, hlogs⟩
  · exact (SFunc.RunP.not_halted_entry (k := 7) bodySet_noHalt (by decide) rfl hrun_body rfl).elim

end Blanc.Lift.BeaconDeposit

