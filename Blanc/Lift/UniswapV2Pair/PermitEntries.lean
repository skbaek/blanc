import Blanc.Lift.UniswapV2Pair.PermitWalk
import Blanc.Lift.ByteWindowMemory
import Blanc.Lift.UniswapV2Pair.WriterEntries

/-! The permit recovery call, the signer guard, the approval core at the moved
free pointer, and the whole internal permit body. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The address word the guard reads: the copied reply prefix over the zeroed output word. -/
def permitRecoveredWord (out : Bytes) : B256 :=
  Bytes.toB256 (out.take 32 ++ List.replicate (32 - (out.take 32).length) 0)

def permitReplyMemory (D : Mem) (out : Bytes) : Mem :=
  (D.extends [(482, 128), (450, 32)]).write 450 (out.take 32)

theorem permitReplyMemory_ptr {D : Mem} (mem : PtrMem 482 640 D) (out : Bytes) :
    PtrMem 482 640 (permitReplyMemory D out) := by
  unfold permitReplyMemory
  have extendedEq : D.extends [(482, 128), (450, 32)] = D := by
    unfold Mem.extends
    rw [mem.size]
    change (⟨D.data, 640⟩ : Mem) = D
    rw [← mem.size]
  rw [extendedEq]
  apply mem.write_bytes_of_le 450 (out.take 32)
  · rw [List.length_take]
    have := Nat.min_le_left 32 out.length
    omega
  · exact Or.inr (by decide)

/-- Over the zeroed output word, the guard reads exactly the copied reply prefix. -/
theorem permitReplyMemory_word {C : Mem} {img : Bytes} (wf : Mem.Wf C) (reads : Mem.Reads C img)
    (mem : PtrMem 450 480 C) (digest : B256) (v : UInt8) (r s : B256) (out : Bytes) :
    Bytes.toB256 ((permitReplyMemory (permitRequestMemory C digest v r s) out).read 450 32).1 =
      permitRecoveredWord out := by
  have short : (out.take 32).length ≤ 32 := by
    rw [List.length_take]; exact Nat.min_le_left 32 out.length
  have rD := permitRequestMemory_reads wf reads digest v r s
  have wfD := (permitRequestMemory_ptr mem digest v r s).wf
  have rF := (rD.extends [(482, 128), (450, 32)]).write (wfD.extends _) 450 (out.take 32)
  unfold permitReplyMemory
  rw [rF.read, Bytes.sliceD_writeAt_short _ _ 450 short]
  unfold permitRequestImage
  rw [Bytes.sliceD_writeAt_before _ _ _ _ 578 (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ 546 (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ 514 (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ 482 (by omega),
    Bytes.sliceD_writeAt_word_after _ 64 _ _ _ (by omega),
    Bytes.sliceD_writeAt_inside _ _ 450 _ _ (by omega) (by rw [B256.length_toBytes]; omega),
    Nat.add_sub_cancel_left, B256.zero_toBytes_sliceD]
  rfl

def permitFinalMemory (F : Mem) (owner spender : Adr) (value : B256) : Mem :=
  (approveScratch F owner.toB256 spender.toB256).write (482 : B256).toNat value.toBytes

/-- After the successful reply: the actual signer guard, the approval core at
pointer 482, and the nine-word unwind back to the caller. -/
theorem permitSigner_inv {sevm : Sevm} {d : Devm} {R : List B256} {F : Mem} {G : Nat}
    {digest s r vw dl val ρ : B256} {owner spender : Adr} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 482 640 F)
    (run : SFunc.Run cert.prog sevm (St d (0 :: 610 :: 1 :: 0 :: digest :: s :: r :: vw :: dl ::
      val :: spender.toB256 :: owner.toB256 :: ρ :: R) F G) t_1cdc_c29 o) :
    (Bytes.toB256 (F.read 450 32).1).toAdr ≠ 0 ∧
      (Bytes.toB256 (F.read 450 32).1).toAdr = owner ∧ sevm.isStatic = false ∧
      ∃ G', o = .returned (St (approveCoreBase sevm d owner spender val) R
        (permitFinalMemory F owner spender val) G') := by
  have read0 : Bytes.toB256 (F.read 64 32).1 = 482 := mem.word
  have same0 : (F.read 64 32).2 = F := mem.read_self (by decide)
  have same1 : (F.read 450 32).2 = F := mem.read_self (by decide)
  have h := run.cut
  unfold t_1cdc_c29 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, read0, same0] at hd; subst d'
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 450) (by decide) (ri_add hd)
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  rw [show (450 : B256).toNat = 450 from rfl, same1] at hd; subst d'
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := (Bytes.toB256 (F.read 450 32).1).toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word _) (ri_and hd)
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branchTo (k := 15) (g := t_1d57_c15) (by decide) rfl h with
    ⟨zero, _, h⟩ | ⟨nonzero, _, h⟩
  · have recoveredNonzero : (Bytes.toB256 (F.read 450 32).1).toAdr ≠ 0 := by
      intro bad
      rw [bad] at zero
      exact (by decide : B256.eqCheck (0 : Adr).toB256 0 ≠ 0) zero
    unfold t_1d27_c29 at h
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d', hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_val (w := owner.toB256)
      (ff20_and_adr owner) (ri_and hd)
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d', hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_val (w := (Bytes.toB256 (F.read 450 32).1).toAdr.toB256)
      (ff20_and_word _) (ri_and hd)
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_eq hd
    unfold t_1d57_c15 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    rcases ric_branch h with ⟨_, _, bad⟩ | ⟨equal, _, h⟩
    · exact (bad.false_of_noOk (by decide)).elim
    have signer : (Bytes.toB256 (F.read 450 32).1).toAdr = owner := by
      by_contra different
      have flag : B256.eqCheck (Bytes.toB256 (F.read 450 32).1).toAdr.toB256 owner.toB256 = 0 := by
        simp only [B256.eqCheck, ite_eq_right_iff]
        intro same
        exact absurd (Adr.toB256_inj same) different
      exact equal flag
    unfold t_1dc2_c15 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, h⟩ := ric_call (g := t_259c_c64) (by rfl) h
    rcases h with ⟨D, hc, h⟩ | ⟨D, hc, _⟩
    · obtain ⟨nonstatic, _, eq⟩ := approve64_inv_at fork mem (by decide) hc
      cases eq
      unfold t_1dcd_c15 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨G', hg⟩ := ric_ret h
      exact ⟨recoveredNonzero, signer, nonstatic, G', Seg.done.inj hg⟩
    · obtain ⟨_, _, eq⟩ := approve64_inv_at fork mem (by decide) hc
      cases eq
  · unfold t_1d57_c15 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    rcases ric_branch h with ⟨_, _, bad⟩ | ⟨rejected, _, _⟩
    · exact (bad.false_of_noOk (by decide)).elim
    · exact (nonzero (eq_zero_of_iszero_ne_zero rejected)).elim

/-- The old nonce's digest, over the domain word read at slot 3. -/
def permitCallDigest (sevm : Sevm) (b : Devm) (owner spender : Adr) (value deadline : B256) :
    B256 :=
  permitDigestOf (b.getStorVal sevm.currentTarget 3)
    (permitInner owner spender value (permitNonceRead sevm b owner) deadline)

/-- Memory at the recovery call: scratch slot hash, struct, packed digest and request. -/
def permitCallMemory (sevm : Sevm) (b : Devm) (M : Mem) (owner spender : Adr)
    (value deadline : B256) (v : UInt8) (r s : B256) : Mem :=
  permitRequestMemory (permitDigestMemory (permitStructMemory (permitNonceMemory M owner) owner
    spender value (permitNonceRead sevm b owner) deadline) (b.getStorVal sevm.currentTarget 3)
    (permitInner owner spender value (permitNonceRead sevm b owner) deadline))
    (permitCallDigest sevm b owner spender value deadline) v r s

def permitCallStack (sevm : Sevm) (b : Devm) (owner spender : Adr) (value deadline : B256)
    (v : UInt8) (r s ρ : B256) (R : List B256) : List B256 :=
  610 :: 1 :: 0 :: permitCallDigest sevm b owner spender value deadline :: s :: r :: v.toB256 ::
    deadline :: value :: spender.toB256 :: owner.toB256 :: ρ :: R

theorem permitCallMemory_facts {sevm : Sevm} {b : Devm} {M : Mem} {img : Bytes}
    (mem : PtrMem 128 96 M) (reads : Mem.Reads M img) (owner spender : Adr)
    (value deadline : B256) (v : UInt8) (r s : B256) :
    PtrMem 482 640 (permitCallMemory sevm b M owner spender value deadline v r s) ∧
    ((permitCallMemory sevm b M owner spender value deadline v r s).read 482 128).1 =
      ExternalOperation.encode
        (.recover (permitCallDigest sevm b owner spender value deadline) v r s) ∧
    (∀ out, Bytes.toB256 ((permitReplyMemory
      (permitCallMemory sevm b M owner spender value deadline v r s) out).read 450 32).1 =
        permitRecoveredWord out) := by
  have mA := permitNonceMemory_ptr mem owner
  have wA := (mem.wf.write 0 owner.toB256.toBytes).write 32 (4 : B256).toBytes
  have rA := (reads.write mem.wf 0 owner.toB256.toBytes).write
    (mem.wf.write 0 owner.toB256.toBytes) 32 (4 : B256).toBytes
  have mB := permitStructMemory_ptr mA owner spender value (permitNonceRead sevm b owner) deadline
  have rB := permitStructMemory_reads wA rA owner spender value (permitNonceRead sevm b owner) deadline
  have mC := permitDigestMemory_ptr mB (b.getStorVal sevm.currentTarget 3)
    (permitInner owner spender value (permitNonceRead sevm b owner) deadline)
  have rC := permitDigestMemory_reads mB.wf rB (b.getStorVal sevm.currentTarget 3)
    (permitInner owner spender value (permitNonceRead sevm b owner) deadline)
  have rD := permitRequestMemory_reads mC.wf rC (permitCallDigest sevm b owner spender value deadline)
    v r s
  refine ⟨permitRequestMemory_ptr mC _ v r s, ?_, fun out =>
    permitReplyMemory_word mC.wf rC mC _ v r s out⟩
  unfold permitCallMemory
  rw [rD.read, permitRequestImage_window]

/-- Successful internal permit, over any instruction relation projecting to steps: deadline
and static guards, the actual recovery call (a `P` step of the same run) with its observed reply, the signer guard on the copied word, and the exact approval post. -/
theorem permitBody_invP {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {img : Bytes}
    {G : Nat} {s r deadline value ρ : B256} {v : UInt8} {owner spender : Adr} {o : Outcome}
    (project : ∀ {s : Sevm} {before : Devm} {n : Ninst} {after : Devm},
      P s before n after → Ninst.Run s before n after)
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M) (reads : Mem.Reads M img)
    (run : SFunc.RunP P cert.prog sevm (St b (s :: r :: v.toB256 :: deadline :: value ::
      spender.toB256 :: owner.toB256 :: ρ :: R) M G) t_1b0c_c29 o) :
    sevm.isStatic = false ∧ sevm.benvStat.time ≤ deadline ∧
      ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (G' : Nat),
        P sevm (St (permitNonceWorld sevm b owner)
          (gw :: 1 :: 482 :: 128 :: 450 :: 32 ::
            permitCallStack sevm b owner spender value deadline v r s ρ R)
          (permitCallMemory sevm b M owner spender value deadline v r s) callGas)
          (.exec .staticcall) d ∧
        StaticCallPost (permitNonceWorld sevm b owner) d
          (permitCallStack sevm b owner spender value deadline v r s ρ R)
          (permitCallMemory sevm b M owner spender value deadline v r s) 482 128 450 32 1 out ∧
        out.length < 2 ^ 256 ∧
        StaticAnswered sevm (permitNonceWorld sevm b owner) (1 : B256).toAdr
          (ExternalOperation.encode
            (.recover (permitCallDigest sevm b owner spender value deadline) v r s)) out ∧
        (permitRecoveredWord out).toAdr ≠ 0 ∧ (permitRecoveredWord out).toAdr = owner ∧
        o = .returned (St (approveCoreBase sevm d owner spender value) R
          (permitFinalMemory (permitReplyMemory
            (permitCallMemory sevm b M owner spender value deadline v r s) out)
            owner spender value) G') := by
  obtain ⟨memD, request, reply⟩ := permitCallMemory_facts (sevm := sevm) (b := b) mem reads
    owner spender value deadline v r s
  have mA := permitNonceMemory_ptr mem owner
  have wA := (mem.wf.write 0 owner.toB256.toBytes).write 32 (4 : B256).toBytes
  have rA := (reads.write mem.wf 0 owner.toB256.toBytes).write
    (mem.wf.write 0 owner.toB256.toBytes) 32 (4 : B256).toBytes
  have mB := permitStructMemory_ptr mA owner spender value (permitNonceRead sevm b owner) deadline
  have rB := permitStructMemory_reads wA rA owner spender value (permitNonceRead sevm b owner) deadline
  have mC := permitDigestMemory_ptr mB (b.getStorVal sevm.currentTarget 3)
    (permitInner owner spender value (permitNonceRead sevm b owner) deadline)
  have h := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_1b0c_c29 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_timestamp (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_lt (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rcases ric_branchP h with ⟨_, _, bad⟩ | ⟨timely, _, h⟩
  · exact (bad.false_of_noOk (by decide)).elim
  have timely : sevm.benvStat.time ≤ deadline := by
    have flag := eq_zero_of_iszero_ne_zero timely
    by_contra late
    have one : B256.ltCheck deadline sevm.benvStat.time = 1 := by
      simp only [B256.ltCheck, lt_of_not_ge late, ite_true]
    rw [one] at flag
    exact (by decide : (1 : B256) ≠ 0) flag
  unfold t_1b7b_c29 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, line, h⟩ := SFunc.RunCutP.split_nexts (fun step => project step) permitNonceLine h
  obtain ⟨nonstatic, _, state⟩ := permitNonceLine_inv fork mem line
  rw [state] at h
  obtain ⟨_, line, h⟩ := SFunc.RunCutP.split_nexts (fun step => project step) permitStructLine h
  obtain ⟨_, state⟩ := permitStructLine_inv mA rA line
  rw [state] at h
  obtain ⟨_, line, h⟩ := SFunc.RunCutP.split_nexts (fun step => project step) permitDigestLine h
  obtain ⟨_, state⟩ := permitDigestLine_inv mB rB line
  rw [state] at h
  obtain ⟨_, line, h⟩ := SFunc.RunCutP.split_nexts (fun step => project step) permitRequestLine h
  obtain ⟨_, state⟩ := permitRequestLine_inv mC line
  rw [state] at h
  obtain ⟨d', hd, h⟩ := ric_nextP h
  obtain ⟨gw, callGas, rfl⟩ := ri_gas (project hd)
  obtain ⟨d, hcall, h⟩ := ric_nextP h
  obtain ⟨flag, out, post, bound, answered⟩ := ri_staticcall_bounded fork (project hcall)
  rw [post.eq_St] at h
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rcases ric_branchP h with ⟨_, _, bad⟩ | ⟨accepted, _, h⟩
  · exact (bad.false_of_noOk (by decide)).elim
  have one : flag = 1 := by
    rcases post.flag with zero | one
    · rw [zero, show B256.eqCheck (B256.eqCheck (0 : B256) 0) 0 = 0 from by decide] at accepted
      exact (accepted rfl).elim
    · exact one
  subst flag
  rw [show B256.eqCheck (1 : B256) 0 = 0 from by decide] at h
  obtain ⟨recovered, signer, _, G', eq⟩ := permitSigner_inv fork
    (F := permitReplyMemory (permitCallMemory sevm b M owner spender value deadline v r s) out)
    (permitReplyMemory_ptr memD out) ((SFunc.runP_iff_runCutP_nil.mpr h).mono project)
  rw [reply out] at recovered signer
  refine ⟨nonstatic, timely, gw, callGas, d, out, G', hcall, post, bound, ?_, recovered, signer, eq⟩
  have answer := answered rfl
  change StaticAnswered sevm (permitNonceWorld sevm b owner) (1 : B256).toAdr
    ((permitCallMemory sevm b M owner spender value deadline v r s).read 482 128).1 out at answer
  rw [request] at answer
  exact answer

def permitOwner (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr
def permitSpender (sevm : Sevm) : Adr := (Sevm.dataWord sevm 36).toAdr
def permitValue (sevm : Sevm) : B256 := Sevm.dataWord sevm 68
def permitDeadline (sevm : Sevm) : B256 := Sevm.dataWord sevm 100
/-- The decoder masks the `uint8` word to its low byte; high bits are accepted. -/
def permitV (sevm : Sevm) : UInt8 := (Sevm.dataWord sevm 132).2.2.toUInt8
def permitR (sevm : Sevm) : B256 := Sevm.dataWord sevm 164
def permitS (sevm : Sevm) : B256 := Sevm.dataWord sevm 196

def permitPublicCallMemory (sevm : Sevm) (b : Devm) : Mem :=
  permitCallMemory sevm b getterInitMemory (permitOwner sevm) (permitSpender sevm)
    (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)

def permitPublicDigest (sevm : Sevm) (b : Devm) : B256 :=
  permitCallDigest sevm b (permitOwner sevm) (permitSpender sevm) (permitValue sevm)
    (permitDeadline sevm)

def permitPublicCallStack (sevm : Sevm) (b : Devm) (sel : B256) : List B256 :=
  permitCallStack sevm b (permitOwner sevm) (permitSpender sevm) (permitValue sevm)
    (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm) 0x0257 [sel]

/-- The halted permit frame: approval core over the call's world, STOP with no output bytes. -/
def permitPublicPost (sevm : Sevm) (b d : Devm) (out : Bytes) (sel : B256) (G : Nat) : Devm :=
  St (approveCoreBase sevm d (permitOwner sevm) (permitSpender sevm) (permitValue sevm)) [sel]
    (permitFinalMemory (permitReplyMemory (permitPublicCallMemory sevm b) out)
      (permitOwner sevm) (permitSpender sevm) (permitValue sevm)) G

/-- The permit raw-success facts at one call occurrence, shared by the entry and pc0 inverses. -/
def PermitRawCall (sevm : Sevm) (b : Devm) (sel : B256) (gw : B256) (callGas : Nat) (d : Devm)
    (out : Bytes) : Prop :=
  Ninst.Run sevm (St (permitNonceWorld sevm b (permitOwner sevm))
      (gw :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStack sevm b sel)
      (permitPublicCallMemory sevm b) callGas) (.exec .staticcall) d ∧
    StaticCallPost (permitNonceWorld sevm b (permitOwner sevm)) d
      (permitPublicCallStack sevm b sel) (permitPublicCallMemory sevm b) 482 128 450 32 1 out ∧
    out.length < 2 ^ 256 ∧
    StaticAnswered sevm (permitNonceWorld sevm b (permitOwner sevm)) (1 : B256).toAdr
      (ExternalOperation.encode
        (.recover (permitPublicDigest sevm b) (permitV sevm) (permitR sevm) (permitS sevm))) out ∧
    (permitRecoveredWord out).toAdr ≠ 0 ∧ (permitRecoveredWord out).toAdr = permitOwner sevm

/-- `PermitRawCall` with the recovery STATICCALL as a step of the instruction relation `P`. -/
def PermitRawCallP (P : Sevm → Devm → Ninst → Devm → Prop) (sevm : Sevm) (b : Devm) (sel : B256)
    (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) : Prop :=
  P sevm (St (permitNonceWorld sevm b (permitOwner sevm))
      (gw :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStack sevm b sel)
      (permitPublicCallMemory sevm b) callGas) (.exec .staticcall) d ∧
    StaticCallPost (permitNonceWorld sevm b (permitOwner sevm)) d
      (permitPublicCallStack sevm b sel) (permitPublicCallMemory sevm b) 482 128 450 32 1 out ∧
    out.length < 2 ^ 256 ∧
    StaticAnswered sevm (permitNonceWorld sevm b (permitOwner sevm)) (1 : B256).toAdr
      (ExternalOperation.encode
        (.recover (permitPublicDigest sevm b) (permitV sevm) (permitR sevm) (permitS sevm))) out ∧
    (permitRecoveredWord out).toAdr ≠ 0 ∧ (permitRecoveredWord out).toAdr = permitOwner sevm

theorem permitEntry_invP {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {b : Devm}
    {G : Nat} {sel : B256} {o : Outcome}
    (project : ∀ {s : Sevm} {before : Devm} {n : Ninst} {after : Devm},
      P s before n after → Ninst.Run s before n after)
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunP P cert.prog sevm (St b [sel] getterInitMemory G) t_05e2_c76 o) :
    (224 : B256) ≤ sevm.data.length.toB256 - 4 ∧ sevm.isStatic = false ∧
      sevm.benvStat.time ≤ permitDeadline sevm ∧
      ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (G' : Nat),
        PermitRawCallP P sevm b sel gw callGas d out ∧
        o = .halted (permitPublicPost sevm b d out sel G') := by
  have h := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_05e2_c76 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldatasize (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sub (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_lt (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rcases ric_branchP h with ⟨_, _, bad⟩ | ⟨long, _, h⟩
  · exact (bad.false_of_noOk (by decide)).elim
  have guard : (224 : B256) ≤ sevm.data.length.toB256 - 4 := by
    have flag := eq_zero_of_iszero_ne_zero long
    by_contra short
    have one : B256.ltCheck (sevm.data.length.toB256 - Bytes.toB256 [4]) (Bytes.toB256 [0xe0]) = 1 := by
      simp only [B256.ltCheck, show Bytes.toB256 [4] = (4 : B256) from rfl,
        show Bytes.toB256 [0xe0] = (224 : B256) from rfl, lt_of_not_ge short, ite_true]
    rw [one] at flag
    exact (by decide : (1 : B256) ≠ 0) flag
  unfold t_05f8_c76 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldataload (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_val (w := (permitOwner sevm).toB256) (ff20_and_word _) (ri_and (project hd))
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_val (w := 36) (by decide) (ri_add (project hd))
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldataload (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_val (w := (permitSpender sevm).toB256) (ff20_and_word _) (ri_and (project hd))
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_val (w := 68) (by decide) (ri_add (project hd))
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldataload (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_val (w := 100) (by decide) (ri_add (project hd))
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldataload (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_val (w := 132) (by decide) (ri_add (project hd))
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldataload (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_val (w := (permitV sevm).toB256) (B256.and_ff_eq_toUInt8 _) (ri_and (project hd))
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_val (w := 164) (by decide) (ri_add (project hd))
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldataload (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_val (w := 196) (by decide) (ri_add (project hd))
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldataload (project hd)
  obtain ⟨d', hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  cases h with
  | callHalt _ lookup pop hc =>
    rw [show cert.prog[29]? = some t_1b0c_c29 from rfl] at lookup
    cases lookup
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, eq⟩ := permitBody_invP project (R := [sel])
      fork getterInitMemory_ptr (Mem.reads_data getterInitMemory) ((St.of_pop1 pop).2 ▸ hc)
    cases eq
  | callRet _ lookup pop hc h =>
    rw [show cert.prog[29]? = some t_1b0c_c29 from rfl] at lookup
    cases lookup
    obtain ⟨nonstatic, timely, gw, callGas, d, out, G', call, post, bound, answered,
      recovered, signer, eq⟩ := permitBody_invP project (R := [sel]) fork getterInitMemory_ptr
        (Mem.reads_data getterInitMemory) ((St.of_pop1 pop).2 ▸ hc)
    cases eq
    unfold t_0257_c76 at h
    obtain ⟨residual, h⟩ := ric_destP h
    cases h with
    | last hr =>
      exact ⟨guard, nonstatic, timely, gw, callGas, d, out, residual,
        ⟨call, post, bound, answered, recovered, signer⟩,
        congrArg Outcome.halted (Except.ok.inj hr).symm⟩

theorem permit_selector_invP {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {o : Outcome}
    (project : ∀ {s : Sevm} {before : Devm} {n : Ninst} {after : Devm},
      P s before n after → Ninst.Run s before n after)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : SFunc.RunP P cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ G', SFunc.RunP P cert.prog sevm (St b [0xd505accf] M G') t_05e2_c76 o := by
  have h := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_calldataload (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd⟩ := ri_shr (project hd)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0xd505accf : B256) from selector] at hd
  subst d
  obtain ⟨_, h⟩ := ric_cmp_gtP (fun step => project step) h
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0xd505accf : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_002b_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_gtP (fun step => project step) h
  simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0xd505accf : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_0036_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_gtP (fun step => project step) h
  simp only [show B256.gtCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7]) (0xd505accf : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_0041_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eqP (fun step => project step) (g := t_05da_c75) (by intro bad; cases bad) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7]) (0xd505accf : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_004c_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eqP (fun step => project step) (g := t_05e2_c76) (by intro bad; cases bad) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0xd5, 0x05, 0xac, 0xcf]) (0xd505accf : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  exact ⟨_, SFunc.runP_iff_runCutP_nil.mpr h⟩

/-- The signer guard, the approval core at pointer 482 (no expansion) and the unwind cost
2142 gas besides the selected allowance store; the sentry is the store's incoming gas. -/
theorem permitSigner_exact {sevm : Sevm} {d : Devm} {R : List B256} {F : Mem} {G c : Nat}
    {digest s r vw dl val ρ : B256} {owner spender : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 482 640 F)
    (recovered : (Bytes.toB256 (F.read 450 32).1).toAdr ≠ 0)
    (signer : (Bytes.toB256 (F.read 450 32).1).toAdr = owner)
    (cost : c = sstoreCost sevm d (mapSlot spender.toB256 (mapSlot owner.toB256 2)) val)
    (sentry : gCallStipend < G + c + 1845) (nonstatic : sevm.isStatic = false)
    (room : R.length ≤ 1000) :
    SFunc.RunExact cert.prog sevm (St d (0 :: 610 :: 1 :: 0 :: digest :: s :: r :: vw :: dl ::
      val :: spender.toB256 :: owner.toB256 :: ρ :: R) F (G + c + 2142)) t_1cdc_c29
      (.returned (St (approveCoreBase sevm d owner spender val) R
        (permitFinalMemory F owner spender val) G)) := by
  have nonzero : B256.eqCheck (Bytes.toB256 (F.read 450 32).1).toAdr.toB256 0 = 0 := by
    simp only [B256.eqCheck, ite_eq_right_iff]
    intro zero
    have adrZero : (0 : Adr).toB256 = 0 := by decide
    exact absurd (Adr.toB256_inj (zero.trans adrZero.symm)) recovered
  have equal : B256.eqCheck (Bytes.toB256 (F.read 450 32).1).toAdr.toB256 owner.toB256 = 1 := by
    rw [signer]
    simp only [B256.eqCheck, ite_true]
  unfold t_1cdc_c29
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (i := 64) (v := 482) (c := 3) (by rw [St.extCost_eq mem.size]; decide)
    mem.word (mem.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 450) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (i := 450) (v := Bytes.toB256 (F.read 450 32).1) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) rfl (mem.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_and (v := (Bytes.toB256 (F.read 450 32).1).toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word _) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_iszero nonzero (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_push (w := 0x1d57) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_branchTo_zero ?_
  unfold t_1d27_c29
  refine rx_pop ?_
  refine rx_dup (n := 8) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_and (v := owner.toB256) (ff20_and_adr owner) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_and (v := (Bytes.toB256 (F.read 450 32).1).toAdr.toB256) (ff20_and_word _) (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_eq equal (by simp only [List.length_cons, List.length_set]; omega) ?_
  unfold t_1d57_c15
  refine rx_dest ?_
  refine rx_push (w := 0x1dc2) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_1dc2_c15
  refine rx_dest ?_
  refine rx_push (w := 0x1dcd) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 9) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 9) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_dup (n := 9) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  refine rx_push (w := 0x259c) rfl (by simp only [List.length_cons, List.length_set]; omega) ?_
  have gas : G + c + 2028 = ((G + 27) + 0 + c + 1993) + 8 := by omega
  rw [gas]
  refine rx_callRet (g := t_259c_c64) (by rfl)
    (approve64_exact_at fork mem (by decide) (by decide) cost (by omega) nonstatic
      (by simp only [List.length_cons, List.length_set]; omega)) ?_
  unfold t_1dcd_c15
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

/-- Forward internal permit from the supplied compiled recovery call at its derived
state: the call's returned gas, success stack and reply are premises about the callee,
never a successful endpoint of this frame. -/
theorem permitBody_exact {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem} {img : Bytes}
    {G callGas c1 c2 c3 c : Nat} {s r deadline value ρ : B256} {v : UInt8} {owner spender : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M) (reads : Mem.Reads M img)
    (room : R.length ≤ 990) (nonstatic : sevm.isStatic = false)
    (timely : sevm.benvStat.time ≤ deadline)
    (charge1 : c1 = sloadCost sevm b 3)
    (charge2 : c2 = sloadCost sevm (afterSload sevm b 3) (permitNonceSlot owner))
    (charge3 : c3 = sstoreCost sevm (afterSload sevm (afterSload sevm b 3) (permitNonceSlot owner))
      (permitNonceSlot owner) (permitNonceRead sevm b owner + 1))
    (sentry3 : gCallStipend < callGas + 641 + c3)
    (call : Ninst.RunCompiled sevm (St (permitNonceWorld sevm b owner)
      (callGas.toB256 :: 1 :: 482 :: 128 :: 450 :: 32 ::
        permitCallStack sevm b owner spender value deadline v r s ρ R)
      (permitCallMemory sevm b M owner spender value deadline v r s) callGas)
      (.exec .staticcall) d)
    (success : d.stack = 1 :: permitCallStack sevm b owner spender value deadline v r s ρ R)
    (returnedGas : d.gasLeft = G + c + 2142 + 22)
    (recovered : (permitRecoveredWord d.returnData).toAdr ≠ 0)
    (signer : (permitRecoveredWord d.returnData).toAdr = owner)
    (cost : c = sstoreCost sevm d (mapSlot spender.toB256 (mapSlot owner.toB256 2)) value)
    (sentry : gCallStipend < G + c + 1845) :
    SFunc.RunExact cert.prog sevm (St b (s :: r :: v.toB256 :: deadline :: value ::
      spender.toB256 :: owner.toB256 :: ρ :: R) M (callGas + c3 + c2 + c1 + 781)) t_1b0c_c29
      (.returned (St (approveCoreBase sevm d owner spender value) R
        (permitFinalMemory (permitReplyMemory
          (permitCallMemory sevm b M owner spender value deadline v r s) d.returnData)
          owner spender value) G)) := by
  obtain ⟨memD, _, reply⟩ := permitCallMemory_facts (sevm := sevm) (b := b) mem reads
    owner spender value deadline v r s
  have mA := permitNonceMemory_ptr mem owner
  have wA := (mem.wf.write 0 owner.toB256.toBytes).write 32 (4 : B256).toBytes
  have rA := (reads.write mem.wf 0 owner.toB256.toBytes).write
    (mem.wf.write 0 owner.toB256.toBytes) 32 (4 : B256).toBytes
  have mB := permitStructMemory_ptr mA owner spender value (permitNonceRead sevm b owner) deadline
  have rB := permitStructMemory_reads wA rA owner spender value (permitNonceRead sevm b owner) deadline
  have mC := permitDigestMemory_ptr mB (b.getStorVal sevm.currentTarget 3)
    (permitInner owner spender value (permitNonceRead sevm b owner) deadline)
  unfold t_1b0c_c29
  refine rx_dest ?_
  refine rx_timestamp (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le timely) (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x1b7b) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_1b7b_c29
  refine rx_dest ?_
  rw [show callGas + c3 + c2 + c1 + 755 = (callGas + 641) + c3 + c2 + c1 + 114 by omega]
  refine permitNonceLine_exact fork mem (by simp only [List.length_cons]; omega) nonstatic charge1 charge2 charge3 sentry3 ?_
  rw [show callGas + 641 = (callGas + 368) + 273 by omega]
  refine permitStructLine_exact mA rA (by simp only [List.length_cons]; omega) ?_
  rw [show callGas + 368 = (callGas + 176) + 192 by omega]
  refine permitDigestLine_exact mB rB (by simp only [List.length_cons]; omega) ?_
  rw [show callGas + 176 = (callGas + 2) + 174 by omega]
  refine permitRequestLine_exact mC (by simp only [List.length_cons]; omega) ?_
  refine rx_gas (by simp only [List.length_cons]; omega) ?_
  refine rx_staticcall fork call ?_
  intro flag out post _
  have one : flag = 1 := (List.cons.inj (post.stack.symm.trans success)).1
  subst flag
  rw [returnedGas, ← post.returnData]
  refine rx_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x1cdc) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branch_succ (by decide) ?_
  rw [post.returnData]
  exact permitSigner_exact
    (F := permitReplyMemory (permitCallMemory sevm b M owner spender value deadline v r s) out)
    fork (permitReplyMemory_ptr memD out)
    (by rw [reply out, ← post.returnData]; exact recovered)
    (by rw [reply out, ← post.returnData]; exact signer) cost sentry nonstatic (by omega)

/-- The per-call selected storage charges of the nonce prefix. -/
def permitNonceCharge (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm b 3 + sloadCost sevm (afterSload sevm b 3) (permitNonceSlot (permitOwner sevm))

def permitNonceStoreCharge (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCost sevm (afterSload sevm (afterSload sevm b 3) (permitNonceSlot (permitOwner sevm)))
    (permitNonceSlot (permitOwner sevm)) (permitNonceRead sevm b (permitOwner sevm) + 1)

def permitApproveCharge (sevm : Sevm) (d : Devm) : Nat :=
  sstoreCost sevm d (mapSlot (permitSpender sevm).toB256 (mapSlot (permitOwner sevm).toB256 2))
    (permitValue sevm)

/-- The public entry: wrapped length guard, seven-word decoder, internal call, STOP. -/
theorem permitEntry_exact {sevm : Sevm} {b d : Devm} {G callGas : Nat} {sel : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (guard : (224 : B256) ≤ sevm.data.length.toB256 - 4) (nonstatic : sevm.isStatic = false)
    (timely : sevm.benvStat.time ≤ permitDeadline sevm)
    (sentry3 : gCallStipend < callGas + 641 + permitNonceStoreCharge sevm b)
    (call : Ninst.RunCompiled sevm (St (permitNonceWorld sevm b (permitOwner sevm))
      (callGas.toB256 :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStack sevm b sel)
      (permitPublicCallMemory sevm b) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: permitPublicCallStack sevm b sel)
    (returnedGas : d.gasLeft = G + permitApproveCharge sevm d + 2165)
    (recovered : (permitRecoveredWord d.returnData).toAdr ≠ 0)
    (signer : (permitRecoveredWord d.returnData).toAdr = permitOwner sevm)
    (sentry : gCallStipend < G + permitApproveCharge sevm d + 1846) :
    SFunc.RunExact cert.prog sevm (St b [sel] getterInitMemory
      (callGas + permitNonceStoreCharge sevm b + permitNonceCharge sevm b + 952)) t_05e2_c76
      (.halted (permitPublicPost sevm b d d.returnData sel G)) := by
  unfold t_05e2_c76
  refine rx_dest ?_
  refine rx_push (w := 0x0257) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 4) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_sub' (v := sevm.data.length.toB256 - 4) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le guard) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 0x05f8) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_05f8_c76
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_and (v := (permitOwner sevm).toB256) (ff20_and_word _) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_add' (v := 36) (by decide) (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_and (v := (permitSpender sevm).toB256) (ff20_and_word _) (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_add' (v := 68) (by decide) (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_push (w := 96) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_add' (v := 100) (by decide) (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_push (w := 0xff) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 128) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_add' (v := 132) (by decide) (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_and (v := (permitV sevm).toB256) (B256.and_ff_eq_toUInt8 _) (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_push (w := 160) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_add' (v := 164) (by decide) (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_push (w := 192) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_add' (v := 196) (by decide) (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 0x1b0c) rfl (by simp only [List.length_set, List.length_cons, List.length_nil]; omega) ?_
  have gas : callGas + permitNonceStoreCharge sevm b + permitNonceCharge sevm b + 789 =
      (callGas + permitNonceStoreCharge sevm b +
        sloadCost sevm (afterSload sevm b 3) (permitNonceSlot (permitOwner sevm)) +
        sloadCost sevm b 3 + 781) + 8 := by
    unfold permitNonceCharge; omega
  rw [gas]
  refine rx_callRet (g := t_1b0c_c29) (by rfl)
    (permitBody_exact (G := G + 1) (c := permitApproveCharge sevm d) fork getterInitMemory_ptr (Mem.reads_data getterInitMemory)
      (by simp only [List.length_cons, List.length_nil]; omega) nonstatic timely rfl rfl rfl
      sentry3 call success (by rw [returnedGas]; omega) recovered signer rfl (by omega)) ?_
  unfold t_0257_c76
  exact rx_dest rx_stop

theorem permit_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (body : SFunc.RunExact cert.prog sevm (St b [0xd505accf] getterInitMemory G) t_05e2_c76 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 185)) t_0000_c0 o := by
  refine getterString_guards_exact (G := G + 122) value size ?_
  unfold t_001a_c0
  refine rx_push (w := 0) rfl (by decide) ?_
  refine rx_calldataload (by decide) ?_
  refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_shr (v := 0xd505accf) selector (by decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_002b_c0
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x97) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_0036_c0
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0xd21220a7) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x71) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_0041_c0
  refine cmp_miss (by decide) ?_
  unfold t_004c_c0
  exact cmp_hit (tgt := t_05e2_c76) rfl (by rfl) body

/-- Pc-zero liveness from the supplied compiled recovery call, with every selected storage
charge and both store sentries on their actual incoming gas. -/
theorem permit_pc0_exact {sevm : Sevm} {b d : Devm} {G callGas : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (value : sevm.value = 0)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (guard : (224 : B256) ≤ sevm.data.length.toB256 - 4) (nonstatic : sevm.isStatic = false)
    (timely : sevm.benvStat.time ≤ permitDeadline sevm)
    (sentry3 : gCallStipend < callGas + 641 + permitNonceStoreCharge sevm b)
    (call : Ninst.RunCompiled sevm (St (permitNonceWorld sevm b (permitOwner sevm))
      (callGas.toB256 :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStack sevm b 0xd505accf)
      (permitPublicCallMemory sevm b) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: permitPublicCallStack sevm b 0xd505accf)
    (returnedGas : d.gasLeft = G + permitApproveCharge sevm d + 2165)
    (recovered : (permitRecoveredWord d.returnData).toAdr ≠ 0)
    (signer : (permitRecoveredWord d.returnData).toAdr = permitOwner sevm)
    (sentry : gCallStipend < G + permitApproveCharge sevm d + 1846) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty
      (callGas + permitNonceStoreCharge sevm b + permitNonceCharge sevm b + 1137))
      (permitPublicPost sevm b d d.returnData 0xd505accf G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  rw [show callGas + permitNonceStoreCharge sevm b + permitNonceCharge sevm b + 1137 =
    (callGas + permitNonceStoreCharge sevm b + permitNonceCharge sevm b + 952) + 185 by omega]
  exact permit_dispatch_exact value size selector
    (permitEntry_exact fork guard nonstatic timely sentry3 call success returnedGas recovered
      signer sentry)

theorem permit_bytecode_live_raw {sevm : Sevm} {b d : Devm} {G callGas : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork) (value : sevm.value = 0)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (guard : (224 : B256) ≤ sevm.data.length.toB256 - 4) (nonstatic : sevm.isStatic = false)
    (timely : sevm.benvStat.time ≤ permitDeadline sevm)
    (sentry3 : gCallStipend < callGas + 641 + permitNonceStoreCharge sevm b)
    (call : Ninst.RunCompiled sevm (St (permitNonceWorld sevm b (permitOwner sevm))
      (callGas.toB256 :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStack sevm b 0xd505accf)
      (permitPublicCallMemory sevm b) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: permitPublicCallStack sevm b 0xd505accf)
    (returnedGas : d.gasLeft = G + permitApproveCharge sevm d + 2165)
    (recovered : (permitRecoveredWord d.returnData).toAdr ≠ 0)
    (signer : (permitRecoveredWord d.returnData).toAdr = permitOwner sevm)
    (sentry : gCallStipend < G + permitApproveCharge sevm d + 1846) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty
      (callGas + permitNonceStoreCharge sevm b + permitNonceCharge sevm b + 1137))
      (.ok (permitPublicPost sevm b d d.returnData 0xd505accf G))) :=
  lift_exact cert_check jumps_ok codeEq fork
    (permit_pc0_exact fork value size selector guard nonstatic timely sentry3 call success
      returnedGas recovered signer sentry)

end Blanc.Lift.UniswapV2Pair
