import Blanc.Lift.Usdc.V1ApproveReach
import Blanc.Lift.HistCursorCuts
import Blanc.Lift.HistAccessWalk
import Blanc.Lift.WalkSteps
import Blanc.Lift.FreePtrMem
import Blanc.Lift.CommittedFrameLogs
import Blanc.ExecutionSettledReceiptLogs

/-!
# Actual V1 approve writes and their retained Approval logs

The value and event come from the same original execution occurrence. No
caller exclusion, event absence or historical allowance invariant is assumed.
-/
namespace Blanc.Lift.Usdc.V1ApproveRetainedLog

open Jaune Blanc Blanc.Lift

/-- The Approval topic embedded in the certified V1 runtime. -/
def approvalTopic : B256 :=
  0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925

private def approvalLine : List Ninst :=
  [.reg .pop, .reg (.dup 4),
    .push [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] (by decide),
    .reg .and, .reg .caller,
    .push [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] (by decide),
    .reg .and,
    .push [0x8c,0x5b,0xe1,0xe5,0xeb,0xec,0x7d,0x5b,0xd1,0x4f,0x71,0x42,
      0x7d,0x1e,0x84,0xf3,0xdd,0x03,0x14,0xc0,0xf7,0xb2,0x29,0x1e,
      0x5b,0x20,0x0a,0xc8,0xc7,0xc3,0xb9,0x25] (by decide),
    .reg (.dup 6), .push [0x40] (by decide), .reg .mload,
    .reg (.dup 0), .reg (.dup 2), .reg (.dup 1), .reg .mstore,
    .push [0x20] (by decide), .reg .add, .reg (.swap 1), .reg .pop,
    .reg .pop, .push [0x40] (by decide), .reg .mload, .reg (.dup 0),
    .reg (.swap 1), .reg .sub, .reg (.swap 0)]

private def afterLog : SFunc :=
  [.push [0x01] (by decide), .reg (.swap 2), .reg .pop, .reg .pop,
    .reg .pop, .reg (.swap 2), .reg (.swap 1), .reg .pop, .reg .pop].foldr
    SFunc.next .ret

private def approveStore : SFunc :=
  .next (.reg .sstore) (approvalLine.foldr SFunc.next (.next (.reg (.log 3)) afterLog))

/-- Full stack and exact remaining source at the actual approve store. -/
private def StoreConf (sevm : Sevm) (spender : Adr) (value : B256) (T : Conf) : Prop :=
  ∃ x z S,
    T.d.stack = mapSlot spender.toB256 (mapSlot sevm.caller.toB256 10) ::
      value :: value :: spender.toB256 :: x :: z :: value :: spender.toB256 :: S ∧
    T.f = approveStore ∧
    FreePtr.FpWord (fun _ => 128) (some 0) T.d.memory

private theorem body_storeConf {observe : Conf → Conf → Prop}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {x z value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (a.toB256 :: x :: z :: value :: a.toB256 :: S) M G, ImplV1.t_0e61_c10, K⟩ T)
    (fp : FreePtr.FpWord (fun _ => 128) (some 0) M)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    StoreConf sevm a value T := by
  have fpEnd : FreePtr.FpWord (fun _ => 128) (some 0)
      ((((((M.write 0 sevm.caller.toB256.toBytes).write 32 (10 : B256).toBytes).read
        0 64).2.write 0 a.toB256.toBytes).write 32
        (mapSlot sevm.caller.toB256 10).toBytes).read 0 64).2 := by
    have h1 := FreePtr.FpWord.write (o := 0) (ys := sevm.caller.toB256.toBytes)
      (by simp only [FreePtr.Miss64, B256.length_toBytes]; omega) fp
    have h2 := FreePtr.FpWord.write (o := 32) (ys := (10 : B256).toBytes)
      (by simp only [FreePtr.Miss64, B256.length_toBytes]; omega) h1
    have h3 := FreePtr.FpWord.extends [(0, 64)] h2
    have h4 := FreePtr.FpWord.write (o := 0) (ys := a.toB256.toBytes)
      (by simp only [FreePtr.Miss64, B256.length_toBytes]; omega) h3
    have h5 := FreePtr.FpWord.write (o := 32)
      (ys := (mapSlot sevm.caller.toB256 10).toBytes)
      (by simp only [FreePtr.Miss64, B256.length_toBytes]; omega) h4
    exact FreePtr.FpWord.extends [(0, 64)] h5
  unfold ImplV1.t_0e61_c10 at run
  orsd
  iterate 8 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next_linked erase run hT
    (input := sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run firstHash
  rw [Mem.read_two_word_writes_at_raw] at run firstHash
  have run := run.withPrefix
  iterate 6 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · refine ⟨x, z, S, rfl, rfl, ?_⟩
    simpa only [St.memory, mapSlot, show Bytes.toB256 [10] = (10 : B256) from rfl] using fpEnd
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The actual dispatcher fixes the written amount and retains the store suffix. -/
private theorem approve_storeConf {observe : Conf → Conf → Prop}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b S M G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    StoreConf sevm (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) T := by
  unfold ImplV1.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_000d_c0 at run
  iterate 7 orsx
  have word := (dispatchWord_eq_selector sevm).trans selected
  unfold Proxy.dispatchWord at word
  rw [word] at run
  obtain ⟨-, g, G1, hg, run⟩ := ObservedReach.selWalk_inlS erase V1ApproveReach.route_approve run hT
  rw [show ImplV1.cert.prog[54]? = some ImplV1.t_0220_c54 from rfl] at hg
  cases hg
  unfold ImplV1.t_0220_c54 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_022c_c54 at run
  orsd
  iterate 14 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_word] at run
  iterate 20 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[10]? = some ImplV1.t_0d83_c10 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV1.t_026b_c54], f.sstoreFreeIn [] = true := by
    intro f hf
    have same := List.mem_singleton.mp hf
    subst f
    decide +kernel
  unfold ImplV1.t_0d83_c10 at run
  orsd
  iterate 4 orsx
  orsld
  iterate 11 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_0da1_c10 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_0e01_c10 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [3] = (3 : B256) from rfl,
    show Bytes.toB256 [4] = (4 : B256) from rfl,
    show Bytes.toB256 [32] = (32 : B256) from rfl,
    show Bytes.toB256 [64] = (64 : B256) from rfl,
    show Bytes.toB256 [128] = (128 : B256) from rfl,
    show (32 : B256) + 4 = 36 from rfl,
    show (32 : B256) + 0 = 32 from rfl,
    show (32 : B256) + 32 = 64 from rfl,
    show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr] at run
  have h0 : FreePtr.FpWord (fun _ => 128) (some 0) (M.write 64 (128 : B256).toBytes) :=
    FreePtr.FpWord.store (by decide +kernel)
  have h1 := FreePtr.FpWord.write (o := 0) (ys := sevm.caller.toB256.toBytes)
    (by simp only [FreePtr.Miss64, B256.length_toBytes]; omega) h0
  have h2 := FreePtr.FpWord.write (o := 32) (ys := (3 : B256).toBytes)
    (by simp only [FreePtr.Miss64, B256.length_toBytes]; omega) h1
  have h3 := FreePtr.FpWord.extends [(0, 64)] h2
  have h4 := FreePtr.FpWord.write (o := 0)
    (ys := (Sevm.dataWord sevm 4).toAdr.toB256.toBytes)
    (by simp only [FreePtr.Miss64, B256.length_toBytes]; omega) h3
  have h5 := FreePtr.FpWord.write (o := 32) (ys := (3 : B256).toBytes)
    (by simp only [FreePtr.Miss64, B256.length_toBytes]; omega) h4
  have h6 := FreePtr.FpWord.extends [(0, 64)] h5
  exact body_storeConf erase run h6 hT cont

/-- The exact event operands and payload of the original successful approve suffix. -/
private theorem approvalLine_inverse {sevm : Sevm} {b : Devm}
    {spender : Adr} {value x z : B256} {S : List B256} {M : Mem} {G : Nat} {d : Devm}
    (fp : FreePtr.FpWord (fun _ => 128) (some 0) M)
    (run : Line.Run sevm
      (St b (value :: spender.toB256 :: x :: z :: value :: spender.toB256 :: S) M G)
      approvalLine d) :
    ∃ M' G',
      d = St b (128 :: 32 :: approvalTopic :: sevm.caller.toB256 :: spender.toB256 ::
        spender.toB256 :: x :: z :: value :: spender.toB256 :: S) M' G' ∧
      (M'.read 128 32).1 = value.toBytes := by
  obtain ⟨size, word, -⟩ := fp 0 rfl
  unfold approvalLine at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_caller step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mload step
  rw [show (M.read (Bytes.toB256 [0x40]).toNat 32).1.toB256 = (128 : B256) from word] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  have sizeRead : 96 ≤ (M.read 64 32).2.size := size.trans (memExtSize_ge _ 64 32)
  have preserved := FreePtr.memWord64_write (μ := (M.read 64 32).2)
    (o := 128) (ys := value.toBytes) sizeRead (Or.inr (Or.inr (by decide)))
  have again : memWord ((M.read 64 32).2.write 128 value.toBytes) 64 = 128 :=
    preserved.2.trans word
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  rw [show Bytes.toB256 [0x20] + (128 : B256) = (160 : B256) from rfl] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mload step
  rw [show ((((M.read (Bytes.toB256 [0x40]).toNat 32).2).write
    (128 : B256).toNat value.toBytes).read (Bytes.toB256 [0x40]).toNat 32).1.toB256 =
      (128 : B256) from again] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sub step
  rw [show (160 : B256) - 128 = 32 from rfl] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
  cases run
  refine ⟨_, _, rfl, ?_⟩
  have readValue := (Mem.memWord_write_word (M.read 64 32).2 128 value).1
  have bytes := congrArg B256.toBytes readValue
  rw [memWord] at bytes
  have length : ((((M.read 64 32).2.write 128 value.toBytes).read 128 32).1).length = 32 := by
    simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
  rw [Bytes.toBytes_toB256_of_length length] at bytes
  exact bytes

/-- The exact Approval datum for the executing V1 frame and written value. -/
def approvalLog (sevm : Sevm) (value : B256) : Log :=
  ⟨sevm.currentTarget,
    [approvalTopic, sevm.caller.toB256, (Sevm.dataWord sevm 4).toAdr.toB256], value.toBytes⟩

private theorem store_cursor {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0x095ea7b3)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ κ, CursorOK ImplV1.code ImplV1.cert node κ ∧
      StoreConf root.sevm (Sevm.dataWord root.sevm 4).toAdr
        (Sevm.dataWord root.sevm 36) (κ.conf node.devm) := by
  obtain ⟨decoded, -, -⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
    ImplV1.cert.prog root.sevm ⟨root.devm, ImplV1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  exact ⟨κ, ok, approve_storeConf (fun h => StepIn.toRun h) selected walk ⟨g, tree⟩⟩

private theorem storeConf_emitsApproval {N : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK ImplV1.code ImplV1.cert N κ) {spender : Adr} {value : B256}
    (geometry : StoreConf N.sevm spender value (κ.conf N.devm)) {post : Devm}
    (success : N.exn = .ok post) (committed : Execution.commits N.exn = true)
    (hsg : N.sevm.benvStat.rules.stateGas = none)
    (bal : N.sevm.benvStat.rules.bal = none) :
    (⟨N.sevm.currentTarget, [approvalTopic, N.sevm.caller.toB256, spender.toB256],
      value.toBytes⟩ : Log) ∈ post.logs := by
  obtain ⟨x, z, S, stack, tree, fp⟩ := geometry
  let cut : CursorStateAt ImplV1.code ImplV1.cert N approveStore N.devm
      (mapSlot spender.toB256 (mapSlot N.sevm.caller.toB256 10) ::
        value :: value :: spender.toB256 :: x :: z :: value :: spender.toB256 :: S)
      N.devm.memory (κ.conf N.devm).K :=
    ⟨N, κ, .refl N, rfl, rfl, ok, tree,
      ⟨N.devm.gasLeft, by rw [← stack]; exact (St.self' N.devm).symm⟩, rfl⟩
  obtain ⟨stored⟩ := cut.lineH ImplV1.cert_check success hsg [.reg .sstore] rfl
    (by intro n member y; simp only [List.mem_singleton] at member
        subst n; intro impossible; cases impossible)
    (by
      intro G d run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_sstoreH hsg bal step
      cases run
      exact ⟨_, rfl⟩)
  obtain ⟨L, cursorL, path, _, sameSevm, sameExn, placed, logTree, line, _, _⟩ :=
    cursor_nexts_line_cont_free_forwardH ImplV1.cert_check stored.placed approvalLine
      (.next (.reg (.log 3)) afterLog) stored.tree (stored.exn_eq.trans success)
      (by rw [stored.sevm_eq]; exact hsg)
  obtain ⟨G, readyState⟩ := stored.state
  rw [stored.sevm_eq, readyState] at line
  obtain ⟨M, G', logState, payload⟩ := approvalLine_inverse fp line
  have env : L.sevm = N.sevm := sameSevm.trans stored.sevm_eq
  have outcome : L.exn = .ok post := sameExn.trans (stored.exn_eq.trans success)
  obtain ⟨A, _, edge, _, primitive, _, _, _⟩ :=
    cursor_next_forwardH ImplV1.cert_check placed logTree outcome (env ▸ hsg)
  have logRun := primitive.toRun
  rw [env, logState] at logRun
  obtain ⟨_, afterLogEq⟩ := ri_log3 logRun
  have afterEnv : A.sevm = N.sevm := (Cursor.parentStep_sevm edge).trans env
  have afterOutcome : A.exn = .ok post :=
    (show A.exn = L.exn by cases edge <;> rfl).trans outcome
  have committedA : Execution.commits A.exn = true := by
    rw [afterOutcome, ← success]; exact committed
  have finalPost : Execution.committedPost A.exn committedA = post := by
    generalize hout : A.exn = out at committedA ⊢
    have equal := hout.symm.trans afterOutcome
    cases equal
    rfl
  have logs := Exec.committed_logs_noStateGas A.exc committedA (afterEnv ▸ hsg) rfl rfl
  rw [finalPost] at logs
  have appended := congrArg Devm.logs afterLogEq
  simp only [show (128 : B256).toNat = 128 from rfl,
    show (32 : B256).toNat = 32 from rfl] at appended
  rw [payload] at appended
  rw [logs]
  apply List.mem_append_left
  rw [appended]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- An actual V1 approve write binds its calldata amount to the same exact Approval
in the committing frame's endpoint. The full source suffix is proved from pc zero. -/
theorem approve_write_emits {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (committed : Execution.commits (.ok post) = true)
    (code : sevm.code = ImplV1.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) (selected : Sevm.selector sevm = 0x095ea7b3)
    {node : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value = Sevm.dataWord sevm 36 ∧ approvalLog sevm write.value ∈ post.logs := by
  obtain ⟨κ, ok, geometry⟩ := store_cursor rfl code hsg chain selected found
  have originalGeometry := geometry
  obtain ⟨-, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨x, z, S, storedStack, -, -⟩ := geometry
  have valueEq : write.value = Sevm.dataWord sevm 36 :=
    (List.cons.inj (List.cons.inj (stack.symm.trans storedStack)).2).1
  have env : node.sevm = sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  have outcome : node.exn = .ok post := Exec.Deriv.ParentPrefix.exn_eq chain
  have actualGeometry : StoreConf node.sevm (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36) (κ.conf node.devm) := by
    rw [env]; exact originalGeometry
  have retained : Execution.commits node.exn = true := by rw [outcome]; exact committed
  have event := storeConf_emitsApproval ok actualGeometry outcome retained (env ▸ hsg) (env ▸ bal)
  rw [env] at event
  refine ⟨valueEq, ?_⟩
  simpa only [approvalLog, valueEq] using event

/-- The same actual write/event result in the retained-frame carrier. Selected
historical rule facts remain explicit; they are not event-absence premises. -/
theorem frame_approve_write_emits {frame : Exec.Frame}
    (pc : frame.pc = 0) (code : frame.sevm.code = ImplV1.code)
    (hsg : frame.sevm.benvStat.rules.stateGas = none)
    (bal : frame.sevm.benvStat.rules.bal = none)
    (selected : Sevm.selector frame.sevm = 0x095ea7b3) {node : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv frame) node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value = Sevm.dataWord frame.sevm 36 ∧
      approvalLog frame.sevm write.value ∈ frame.post.logs := by
  rcases frame with ⟨pc, sevm, pre, out, run, committed⟩
  dsimp only [Exec.Frame.rootDeriv] at pc chain
  subst pc
  cases out with
  | error err => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post => exact approve_write_emits run committed code hsg bal selected chain found

end Blanc.Lift.Usdc.V1ApproveRetainedLog
