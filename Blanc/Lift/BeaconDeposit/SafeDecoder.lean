import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.BeaconDeposit.DepositDecode
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.Quiet
import Blanc.Lift.WalkInvKit
import Blanc.Lift.WalkKitSupport

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
words through `B256.ltCheck`/`gtCheck` and `toNat`; the modular `CALLDATASIZE` word is
bounded by the full length, and the original guards justify its subtraction). The
`callNext 7 t_01b8_c32` node is `.callRet` (the body only returns: `.callHalt` would need the
body to halt successfully, and the body has no successful halting leaf — or keep both cases and
note `callHalt` gives `.halted` directly, which the statement also covers by taking the body's
result); the pushed words are `depositArgStack sevm [sel]` (`DepositArgs.lean`).  `t_01b8_c32`
is `JUMPDEST; STOP`: `Burn.world` and `Linst.world_of_ok` (`Quiet.lean`). -/
theorem safe_decoder_effects_any_data {sevm : Sevm} {b post : Devm}
    {sel : B256} {G : Nat}
    (run : SFunc.Run prog sevm (St b [sel] mem0 G) t_00a4_c32 (.halted post)) :
    DepositDecodable sevm ∧ ∃ G' d,
      SFunc.Run prog sevm (St b (depositArgStack sevm [sel]) mem0 G')
        t_0304_c7 (.returned d) ∧
      (∀ a, Devm.getStor post a = Devm.getStor d a) ∧
      post.logs = d.logs ∧ post.output = d.output := by
  have hlen_le : sevm.data.length.toB256.toNat ≤ sevm.data.length := by
    rw [B256.toNat_toB256]
    exact Nat.mod_le _ _
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
  winv 2
  rw [hret_tag] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  rw [h4b] at run
  winv 8
  rcases ric_branch run with ⟨-, G12, run⟩ | ⟨hw_head, G12, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_head := eq_zero_of_iszero_ne_zero hw_head

  -- Tree 2: t_00ba_c32 (offset 0 guard 1: argOff 0 ≤ 2^32)
  unfold t_00ba_c32 at run
  winv 3
  rw [B256.add_comm, B256.sub_add_cancel] at run
  winv 2
  rw [h20b] at run
  winv 2
  rw [h36b] at run
  winv 2
  have hoff0 : Sevm.dataWord sevm 4 = argOff sevm 0 := by
    unfold argOff; rw [show (4 : B256) + 32 * Nat.toB256 0 = (4 : B256) by decide]
  rw [hoff0] at run
  winv 5
  rcases ric_branch run with ⟨-, G27, run⟩ | ⟨hw_off0_1, G27, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off0_1 := eq_zero_of_iszero_ne_zero hw_off0_1
  have ht0_1 : (argOff sevm 0).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_off0_1
    rwa [hmaxword, hmax] at h

  -- Tree 3: t_00d5_c32 (offset 0 guard 2: 4 + argOff 0 + 32 ≤ CDS)
  unfold t_00d5_c32 at run
  winv 5
  rw [h20b] at run
  winv 5
  rcases ric_branch run with ⟨-, G38, run⟩ | ⟨hw_off0_2, G38, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off0_2 := eq_zero_of_iszero_ne_zero hw_off0_2
  have ht0_2_word := toNat_le_of_gtCheck_eq_zero hguard_off0_2
  have ht0_2 : (4 + argOff sevm 0 + 32).toNat ≤ sevm.data.length :=
    ht0_2_word.trans hlen_le

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
    have h36le : 36 ≤ sevm.data.length.toB256.toNat := by
      have := ht0_2_word
      rw [toNat_add_of_lt hwrap1, h4_off, show (32 : B256).toNat = 32 by decide] at this
      omega
    have h4le : 4 ≤ sevm.data.length.toB256.toNat := by omega
    have hsub : (sevm.data.length.toB256 - 4).toNat = sevm.data.length.toB256.toNat - 4 := by
      rw [toNat_sub_of_toNat_le]
      · rfl
      · exact h4le
    have hge := toNat_ge_of_ltCheck_eq_zero hguard_head
    rw [h80, hsub] at hge
    omega

  -- Tree 4: t_00e7_c32 (len 0 guards: argLen 0 ≤ 2^32 and argPtr 0 + argLen 0 ≤ CDS)
  unfold t_00e7_c32 at run
  winv 3
  have hlen0 : Sevm.dataWord sevm ((4 : B256) + argOff sevm 0) = argLen sevm 0 := rfl
  rw [hlen0] at run
  winv 2
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_add s1
  have hptr0 : (32 : B256) + ((4 : B256) + argOff sevm 0) = argPtr sevm 0 := rfl
  rw [hptr0] at run
  winv 3
  rw [h1b] at run
  winv 2
  rw [mul_one_b256] at run
  winv 9
  rcases ric_branch run with ⟨-, G59, run⟩ | ⟨hw_len0, G59, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_len0 := eq_zero_of_iszero_ne_zero hw_len0
  obtain ⟨hguard_len0_1, hguard_len0_2⟩ := B256.of_or_eq_zero hguard_len0
  have ht0_3 : (argLen sevm 0).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_len0_1
    rwa [hmaxword, hmax] at h
  have ht0_4 : (argPtr sevm 0 + argLen sevm 0).toNat ≤ sevm.data.length := by
    exact (toNat_le_of_gtCheck_eq_zero hguard_len0_2).trans hlen_le
  have ht0 : TailDecodable sevm 0 := ⟨ht0_1, ht0_2, ht0_3, ht0_4⟩

  -- Tree 5: t_0109_c32 (tail 1, offset guard 1: argOff 1 ≤ 2^32)
  unfold t_0109_c32 at run
  winv 8
  rw [h20b] at run
  winv 2
  rw [h68b] at run
  winv 2
  have hoff1 : Sevm.dataWord sevm 36 = argOff sevm 1 := by
    unfold argOff; rw [show (4 : B256) + 32 * Nat.toB256 1 = 36 by decide]
  rw [hoff1] at run
  winv 5
  rcases ric_branch run with ⟨-, G77, run⟩ | ⟨hw_off1_1, G77, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off1_1 := eq_zero_of_iszero_ne_zero hw_off1_1
  have ht1_1 : (argOff sevm 1).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_off1_1
    rwa [hmaxword, hmax] at h

  -- Tree 6: t_0127_c32 (tail 1, offset guard 2: 4 + argOff 1 + 32 ≤ CDS)
  unfold t_0127_c32 at run
  winv 5
  rw [h20b] at run
  winv 5
  rcases ric_branch run with ⟨-, G88, run⟩ | ⟨hw_off1_2, G88, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off1_2 := eq_zero_of_iszero_ne_zero hw_off1_2
  have ht1_2 : (4 + argOff sevm 1 + 32).toNat ≤ sevm.data.length := by
    exact (toNat_le_of_gtCheck_eq_zero hguard_off1_2).trans hlen_le

  -- Tree 7: t_0139_c32 (len 1 guards: argLen 1 ≤ 2^32 and argPtr 1 + argLen 1 ≤ CDS)
  unfold t_0139_c32 at run
  winv 3
  have hlen1 : Sevm.dataWord sevm ((4 : B256) + argOff sevm 1) = argLen sevm 1 := rfl
  rw [hlen1] at run
  winv 2
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G94, rfl⟩ := ri_add s1
  have hptr1 : (32 : B256) + ((4 : B256) + argOff sevm 1) = argPtr sevm 1 := rfl
  rw [hptr1] at run
  winv 3
  rw [h1b] at run
  winv 2
  rw [mul_one_b256] at run
  winv 9
  rcases ric_branch run with ⟨-, G109, run⟩ | ⟨hw_len1, G109, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_len1 := eq_zero_of_iszero_ne_zero hw_len1
  obtain ⟨hguard_len1_1, hguard_len1_2⟩ := B256.of_or_eq_zero hguard_len1
  have ht1_3 : (argLen sevm 1).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_len1_1
    rwa [hmaxword, hmax] at h
  have ht1_4 : (argPtr sevm 1 + argLen sevm 1).toNat ≤ sevm.data.length := by
    exact (toNat_le_of_gtCheck_eq_zero hguard_len1_2).trans hlen_le
  have ht1 : TailDecodable sevm 1 := ⟨ht1_1, ht1_2, ht1_3, ht1_4⟩

  -- Tree 8: t_015b_c32 (tail 2, offset guard 1: argOff 2 ≤ 2^32)
  unfold t_015b_c32 at run
  winv 8
  rw [h20b] at run
  winv 2
  rw [h100b] at run
  winv 2
  have hoff2 : Sevm.dataWord sevm 68 = argOff sevm 2 := by
    unfold argOff; rw [show (4 : B256) + 32 * Nat.toB256 2 = 68 by decide]
  rw [hoff2] at run
  winv 5
  rcases ric_branch run with ⟨-, G127, run⟩ | ⟨hw_off2_1, G127, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off2_1 := eq_zero_of_iszero_ne_zero hw_off2_1
  have ht2_1 : (argOff sevm 2).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_off2_1
    rwa [hmaxword, hmax] at h

  -- Tree 9: t_0179_c32 (tail 2, offset guard 2: 4 + argOff 2 + 32 ≤ CDS)
  unfold t_0179_c32 at run
  winv 5
  rw [h20b] at run
  winv 5
  rcases ric_branch run with ⟨-, G138, run⟩ | ⟨hw_off2_2, G138, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_off2_2 := eq_zero_of_iszero_ne_zero hw_off2_2
  have ht2_2 : (4 + argOff sevm 2 + 32).toNat ≤ sevm.data.length := by
    exact (toNat_le_of_gtCheck_eq_zero hguard_off2_2).trans hlen_le

  -- Tree 10: t_018b_c32 (len 2 guards: argLen 2 ≤ 2^32 and argPtr 2 + argLen 2 ≤ CDS)
  unfold t_018b_c32 at run
  winv 3
  have hlen2 : Sevm.dataWord sevm ((4 : B256) + argOff sevm 2) = argLen sevm 2 := rfl
  rw [hlen2] at run
  winv 2
  rw [h20b] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G144, rfl⟩ := ri_add s1
  have hptr2 : (32 : B256) + ((4 : B256) + argOff sevm 2) = argPtr sevm 2 := rfl
  rw [hptr2] at run
  winv 3
  rw [h1b] at run
  winv 2
  rw [mul_one_b256] at run
  winv 9
  rcases ric_branch run with ⟨-, G159, run⟩ | ⟨hw_len2, G159, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hguard_len2 := eq_zero_of_iszero_ne_zero hw_len2
  obtain ⟨hguard_len2_1, hguard_len2_2⟩ := B256.of_or_eq_zero hguard_len2
  have ht2_3 : (argLen sevm 2).toNat ≤ 2 ^ 32 := by
    have h := toNat_le_of_gtCheck_eq_zero hguard_len2_1
    rwa [hmaxword, hmax] at h
  have ht2_4 : (argPtr sevm 2 + argLen sevm 2).toNat ≤ sevm.data.length := by
    exact (toNat_le_of_gtCheck_eq_zero hguard_len2_2).trans hlen_le
  have ht2 : TailDecodable sevm 2 := ⟨ht2_1, ht2_2, ht2_3, ht2_4⟩

  have hdec : DepositDecodable sevm := ⟨hhead, ht0, ht1, ht2⟩

  -- Tree 11: t_01ad_c32 (restage arguments and callNext 7 t_01b8_c32)
  unfold t_01ad_c32 at run
  winv 7
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
            cases Except.ok.inj hstop
            have hburn_w := Burn.world hburn
            have hstor : ∀ a, Devm.getStor post a = Devm.getStor D a := by
              intro a
              rw [hburn_w.1]
            exact ⟨hdec, G', D, hrun_body, hstor, hburn_w.2, hburn.output.symm⟩
  · exact (SFunc.RunP.not_halted_entry (k := 7) bodySet_noHalt (by decide) rfl hrun_body rfl).elim

theorem safe_decoder_any_data {sevm : Sevm} {b post : Devm} {sel : B256} {G : Nat}
    (run : SFunc.Run prog sevm (St b [sel] mem0 G) t_00a4_c32 (.halted post)) :
    DepositDecodable sevm ∧ ∃ G' d,
      SFunc.Run prog sevm (St b (depositArgStack sevm [sel]) mem0 G') t_0304_c7 (.returned d) ∧
      (∀ a, Devm.getStor post a = Devm.getStor d a) ∧ post.logs = d.logs := by
  obtain ⟨hdec, G', d, hrun, hstor, hlogs, -⟩ := safe_decoder_effects_any_data run
  exact ⟨hdec, G', d, hrun, hstor, hlogs⟩

/-- Bounded compatibility projection of the original decoder walk. -/
theorem safe_decoder {sevm : Sevm} {b post : Devm} {sel : B256} {G : Nat}
    (hcd : sevm.data.length < 2 ^ 256)
    (run : SFunc.Run prog sevm (St b [sel] mem0 G) t_00a4_c32 (.halted post)) :
    DepositDecodable sevm ∧ ∃ G' d,
      SFunc.Run prog sevm (St b (depositArgStack sevm [sel]) mem0 G') t_0304_c7 (.returned d) ∧
      (∀ a, Devm.getStor post a = Devm.getStor d a) ∧ post.logs = d.logs := by
  exact (fun _ : sevm.data.length < 2 ^ 256 => safe_decoder_any_data run) hcd

end Blanc.Lift.BeaconDeposit
