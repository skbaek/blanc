import Blanc.Lift.UniswapV2Pair.SafeTransferWalk

/-! Skim's helper57 (safeTransfer) inverse at a moved free pointer.

The initializer, ordered copy and CALL are consumed from SafeTransferWalk's public
pointer-generic API (`safeTransfer_dynamicCall_post_inv`), which also fixes the CALL's
success word. Only the post-CALL decoder walk remains here: the public returned-helper
theorem does not expose the CALL's success flag, which skim's commit/precompile
discharge needs on the same step. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune


/-- The literal tree after helper57's CALL: keep the flag, then branch on the reply width. -/
def skimTransferReplyTree : SFunc :=
  .next (.reg (.swap 1)) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .returndatasize)
    (.next (.reg (.dup 0)) (.next (.push [0x00] (by decide)) (.next (.reg (.dup 1))
      (.next (.reg .eq) (.next (.push [0x21, 0x43] (by decide))
        (.branch t_2122_c57 t_2143_c57)))))))))

/-- After the CALL, an empty reply keeps memory and the sentinel96; a nonempty reply
allocates its full returndata at the actual free pointer (modular pointer bump). -/
theorem skimTransferReply_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {d : Devm} {R : List B256} {V : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {flag endWord tokenM y z amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 16 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St d (flag :: endWord :: tokenM :: y :: z :: amount :: toWord :: tokenWord :: rho :: R) V G)
      skimTransferReplyTree r) :
    let len := d.returnData.length.toB256
    let ptr := Bytes.toB256 (V.read 64 32).1
    let V2 := (V.read 64 32).2.write 64 (ptr + ((len + 63) &&& ~~~(31 : B256))).toBytes
    let V3 := V2.write ptr.toNat len.toBytes
    let allocated := V3.write (ptr + 32).toNat (d.returnData.sliceD 0 len.toNat 0)
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St d (len :: (if len = 0 then 96 else ptr) :: flag :: y :: z :: amount :: toWord ::
        tokenWord :: rho :: R) (if len = 0 then V else allocated) residual) t_2148_c16 r := by
  dsimp only
  have h := run
  unfold skimTransferReplyTree at h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_eq (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl] at h
  by_cases empty : d.returnData.length.toB256 = 0
  · rw [empty, show B256.eqCheck 0 0 = (1 : B256) from rfl] at h
    rcases ric_branchP h with ⟨zero, _, _⟩ | ⟨_, _, body⟩
    · exact ((by decide : (1 : B256) ≠ 0) zero).elim
    · unfold t_2143_c57 at body
      obtain ⟨_, body⟩ := ric_destP body
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
      simp only [empty, ite_true]
      exact ⟨_, body⟩
  · have flag0 : B256.eqCheck d.returnData.length.toB256 0 = 0 := ite_eq_right empty
    rw [flag0] at h
    rcases ric_branchP h with ⟨_, _, body⟩ | ⟨nonzero, _, _⟩
    · simp only [empty, ite_false]
      unfold t_2122_c57 at body
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_mload (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_not (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_add (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_and (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_add (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_add (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body
      obtain ⟨_, _, rfl⟩ := ri_returndatacopy (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      cases body with
      | jumpCut _ cut _ => exact (notCut cut).elim
      | jump _ _ lookup pop tail =>
        change some t_2148_c16 = _ at lookup
        cases lookup
        obtain ⟨_, eq⟩ := St.of_pop1 pop
        rw [eq] at tail
        exact ⟨_, tail⟩
    · exact (nonzero rfl).elim

/-- The literal guard-and-cleanup tail of helper57 at entry 17: a nonzero flag
returns past the five helper locals; a zero flag reverts. -/
theorem skimTransferCheck_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat}
    {flag a x y z w rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm []
      (St b (flag :: a :: x :: y :: z :: w :: rho :: R) M G) t_2176_c17 (.done (.returned out))) :
    flag ≠ 0 ∧ ∃ residual, out = St b R M residual := by
  have h := run
  unfold t_2176_c17 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨positive, _, body⟩
  · exact (failed.false_of_noOk (by decide : t_217b_c17.noOk = true)).elim
  · refine ⟨positive, ?_⟩
    unfold t_21e1_c17 at body
    obtain ⟨_, body⟩ := ric_destP body
    obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
    obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
    obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
    obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
    obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
    cases body with
    | ret _ pop =>
      obtain ⟨_, eq⟩ := St.of_pop1 pop
      exact ⟨_, eq⟩

/-- The helper's reply decoder: a returned run derives the CALL's success flag and the
optional-bool acceptance on the actual memory words, then returns past the helper locals. -/
theorem skimTransferDecode_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat}
    {x ptr success y z value toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm []
      (St b (x :: ptr :: success :: y :: z :: value :: toWord :: tokenWord :: rho :: R) M G)
      t_2148_c16 (.done (.returned out))) :
    success ≠ 0 ∧ (∃ M' residual, out = St b R M' residual) ∧
      (Bytes.toB256 (M.read ptr.toNat 32).1 = 0 ∨
        (32 ≤ (Bytes.toB256 (M.read ptr.toNat 32).1).toNat ∧
          Bytes.toB256 (M.read (32 + ptr).toNat 32).1 ≠ 0)) := by
  have h := run
  unfold t_2148_c16 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := success) rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := success) rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  by_cases failed : success = 0
  · rw [failed, show B256.eqCheck 0 0 = (1 : B256) from by decide] at h
    cases h with
    | toZero _ pop _ =>
      obtain ⟨_, bad, _⟩ := St.of_pop2 pop
      exact ((by decide : (1 : B256) ≠ 0) bad).elim
    | toSucc _ _ _ _ lookup pop tail =>
      change some t_2176_c17 = _ at lookup
      cases lookup
      obtain ⟨_, _, eq⟩ := St.of_pop2 pop
      rw [eq] at tail
      exact ((skimTransferCheck_inv project tail).1 rfl).elim
  · have flag : B256.eqCheck success 0 = 0 := ite_eq_right failed
    rw [flag] at h
    refine ⟨failed, ?_⟩
    cases h with
    | toSucc _ _ nonzero _ _ pop _ =>
      obtain ⟨_, rfl, _⟩ := St.of_pop2 pop
      exact (nonzero rfl).elim
    | toZero _ pop tail =>
      obtain ⟨_, _, eq⟩ := St.of_pop2 pop
      rw [eq] at tail
      unfold t_2155_c16 at tail
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_pop (project hd)
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_mload (project hd)
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_push (project hd)
      by_cases empty : Bytes.toB256 (M.read ptr.toNat 32).1 = 0
      · rw [empty, show B256.eqCheck 0 0 = (1 : B256) from by decide] at tail
        cases tail with
        | toZero _ pop _ =>
          obtain ⟨_, bad, _⟩ := St.of_pop2 pop
          exact ((by decide : (1 : B256) ≠ 0) bad).elim
        | toSucc _ _ _ _ lookup pop body =>
          change some t_2176_c17 = _ at lookup
          cases lookup
          obtain ⟨_, _, eq⟩ := St.of_pop2 pop
          rw [eq] at body
          obtain ⟨_, residual, result⟩ := skimTransferCheck_inv project body
          exact ⟨⟨_, residual, result⟩, Or.inl empty⟩
      · have flag1 : B256.eqCheck (Bytes.toB256 (M.read ptr.toNat 32).1) 0 = 0 :=
          ite_eq_right empty
        rw [flag1] at tail
        cases tail with
        | toSucc _ _ nonzero _ _ pop _ =>
          obtain ⟨_, rfl, _⟩ := St.of_pop2 pop
          exact (nonzero rfl).elim
        | toZero _ pop body =>
          obtain ⟨_, _, eq⟩ := St.of_pop2 pop
          rw [eq] at body
          unfold t_215e_c16 at body
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_add (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_mload (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body
          obtain ⟨_, rfl⟩ := ri_dup (w := Bytes.toB256 (M.read ptr.toNat 32).1) rfl (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_lt (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
          rcases ric_branchP body with ⟨_, _, failed⟩ | ⟨positive, _, head⟩
          · exact (failed.false_of_noOk (by decide : t_216f_c16.noOk = true)).elim
          · have width := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero positive)
            unfold t_2173_c16 at head
            obtain ⟨_, head⟩ := ric_destP head
            obtain ⟨_, hd, head⟩ := ric_nextP head; obtain ⟨_, rfl⟩ := ri_pop (project hd)
            obtain ⟨_, hd, head⟩ := ric_nextP head; obtain ⟨_, rfl⟩ := ri_mload (project hd)
            obtain ⟨nonzero, residual, result⟩ := skimTransferCheck_inv project head
            exact ⟨⟨_, residual, result⟩, Or.inr ⟨width, nonzero⟩⟩

/-- A returned pointer-generic helper57 run at a free pointer `p` carried by the actual
memory (`PtrMem`): the SAME P-step CALL with canonical transfer calldata at `p+164`, its
nonzero success flag, the optional-bool acceptance of its full reply, and the returned
frame. Child effects stay opaque in `d`. -/
theorem skimTransfer_flag_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat} {n : Nat}
    {p amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem p n M) (low : 128 ≤ p.toNat) (high : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.RunP P cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 (.returned out)) :
    ∃ (forwarded : B256) (callGas : Nat) (V : Mem) (d : Devm),
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (64 + p + 100) :: 68 :: (64 + p + 100) :: 0 :: (68 + (64 + p + 100)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount ::
        toWord :: tokenWord :: rho :: R) V callGas) (.exec .call) d ∧
      (V.read (p.toNat + 164) 68).1 = abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++
          amount.toBytes ∧
      (∃ flag rest, d.stack = flag :: rest ∧ flag ≠ 0) ∧
      d.output = b.output ∧ d.returnData.length < 2 ^ 256 ∧
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      ∃ M' residual, out = St d R M' residual := by
  have nat64 : (64 + p).toNat = p.toNat + 64 := by
    rw [B256.add_comm, B256.toNat_add_eq_of_nof p 64 (by change p.toNat + 64 < 2 ^ 256; omega)]
    rfl
  have nat164 : (p + 164).toNat = p.toNat + 164 :=
    B256.toNat_add_eq_of_nof p 164 (by change p.toNat + 164 < 2 ^ 256; omega)
  have shape : 64 + p + 100 = p + 164 := by
    apply B256.toNat_inj
    rw [B256.toNat_add_eq_of_nof (64 + p) 100 (by change (64 + p).toNat + 100 < 2 ^ 256; rw [nat64]; omega),
      nat64, nat164]
    change p.toNat + 64 + 100 = p.toNat + 164
    omega
  rw [shape]
  obtain ⟨forwarded, callGas, d, step, tail, stack, memory, output, width, postMem, fit⟩ :=
    safeTransfer_dynamicCall_post_inv project fork mem low high (by decide : 71 ∉ ([] : List Nat))
      (by decide : 16 ∉ ([] : List Nat)) (by decide : 17 ∉ ([] : List Nat))
      ((SFunc.runP_iff_runCutP_nil (P := P)).mp run)
  have calldata := safeTransfer_dynamicCall_data (amount := amount) (toWord := toWord) mem.wf low
    (by omega : p.toNat + 164 < 2 ^ 256)
  rw [nat164] at calldata
  refine ⟨forwarded, callGas, safeTransfer_dynamicCallMemory M p amount toWord, d, step,
    calldata, ⟨1, _, stack, by decide⟩, output, width, ?_⟩
  rw [St.self stack rfl] at tail
  change SFunc.RunCutP P cert.prog sevm [] _ skimTransferReplyTree _ at tail
  obtain ⟨_, tail⟩ := skimTransferReply_inv project (by decide : 16 ∉ ([] : List Nat)) tail
  obtain ⟨_, outEq, accept⟩ := skimTransferDecode_inv project tail
  refine ⟨?_, outEq⟩
  have lenNat : d.returnData.length.toB256.toNat = d.returnData.length :=
    B256.toNat_toB256_of_lt width
  by_cases empty : d.returnData.length.toB256 = 0
  · left
    rw [empty] at lenNat
    exact List.eq_nil_of_length_eq_zero (by rw [← lenNat]; rfl)
  · right
    rw [ite_eq_right empty, ite_eq_right empty] at accept
    rw [show Bytes.toB256 (d.memory.read 64 32).1 = p + 164 from postMem.word,
      postMem.read_self (by omega)] at accept
    have copied : d.returnData.sliceD 0 d.returnData.length.toB256.toNat 0 = d.returnData := by
      rw [lenNat]
      exact Bytes.sliceD_zero_length rfl
    rw [copied] at accept
    have images := Blanc.Lift.bytesArrayMemory_image (bytes := d.returnData) postMem
      (by rw [nat164]; omega) (by rw [nat164]; omega) (by rw [nat164]; omega)
    change Bytes.toB256 ((Blanc.Lift.bytesArrayMemory d.memory (p + 164) d.returnData).read
        (p + 164).toNat 32).1 = 0 ∨
      (32 ≤ (Bytes.toB256 ((Blanc.Lift.bytesArrayMemory d.memory (p + 164) d.returnData).read
        (p + 164).toNat 32).1).toNat ∧
        Bytes.toB256 ((Blanc.Lift.bytesArrayMemory d.memory (p + 164) d.returnData).read
          (32 + (p + 164)).toNat 32).1 ≠ 0) at accept
    rw [show Bytes.toB256 ((Blanc.Lift.bytesArrayMemory d.memory (p + 164) d.returnData).read
        (p + 164).toNat 32).1 = d.returnData.length.toB256 from images.2.1, lenNat] at accept
    rcases accept with zero | ⟨enough, head⟩
    · exact (empty zero).elim
    · rw [show (32 : B256) + (p + 164) = (p + 164) + 32 from B256.add_comm,
        images.2.2 enough] at head
      exact ⟨enough, head⟩

end Blanc.Lift.UniswapV2Pair
