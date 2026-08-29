-- Gas-exact execution semantics for the hand-emitted WETH10 constructor.
--
-- This module isolates the constructor's memory model and exact compiled walk
-- from deployment settlement and accounting.  The constructor itself remains
-- defined and byte-certified in Weth10Deploy.

import Blanc.Weth10Deploy
import Blanc.Reverts
import Blanc.ForwardCall

namespace Blanc

open Jaune

namespace Weth10

/-! ## Gas-exact constructor execution -/

/-- Constructor memory immediately after copying the runtime template. -/
private def weth10InitCopyMemory (sevm : Sevm) : Mem :=
  Mem.empty.write 0
    (sevm.code.sliceD 177 6313 (Linst.toUInt8 .stop))

/-- Constructor memory after the three deployment-chain words are patched. -/
private def weth10InitChainMemory (sevm : Sevm) : Mem :=
  let M0 := weth10InitCopyMemory sevm
  let chain := sevm.benvStat.chainId.toB256
  let M1 := M0.write 372 chain.toBytes
  let M2 := M1.write 691 chain.toBytes
  M2.write 2875 chain.toBytes

/-- Constructor memory immediately after the five-word EIP-712 preimage has
been written, before it is hashed. -/
def weth10InitPreHashMemory (sevm : Sevm) : Mem :=
  let M3 := weth10InitChainMemory sevm
  let chain := sevm.benvStat.chainId.toB256
  let M4 := M3.write 6336 DOMAIN_TYPEHASH.toBytes
  let M5 := M4.write 6368 NAME_HASH.toBytes
  let M6 := M5.write 6400 VERSION_HASH.toBytes
  let M7 := M6.write 6432 chain.toBytes
  M7.write 6464 sevm.currentTarget.toB256.toBytes

/-- Reader-level byte image corresponding exactly to
`weth10InitPreHashMemory`. -/
def weth10InitPreHashImage (sevm : Sevm) : Bytes :=
  let I0 := Bytes.writeAt [] 0
    (sevm.code.sliceD 177 6313 (Linst.toUInt8 .stop))
  let chain := sevm.benvStat.chainId.toB256
  let I1 := Bytes.writeAt I0 372 chain.toBytes
  let I2 := Bytes.writeAt I1 691 chain.toBytes
  let I3 := Bytes.writeAt I2 2875 chain.toBytes
  let I4 := Bytes.writeAt I3 6336 DOMAIN_TYPEHASH.toBytes
  let I5 := Bytes.writeAt I4 6368 NAME_HASH.toBytes
  let I6 := Bytes.writeAt I5 6400 VERSION_HASH.toBytes
  let I7 := Bytes.writeAt I6 6432 chain.toBytes
  Bytes.writeAt I7 6464 sevm.currentTarget.toB256.toBytes

/-- Memory after the successful constructor has copied the template, patched
the three chain words, built and hashed the EIP-712 preimage, and patched the
two separator words. -/
def weth10InitMemory (sevm : Sevm) : Mem :=
  let M8 := weth10InitPreHashMemory sevm
  let hash := (M8.read 6336 160).1.keccak
  let M9 := M8.write 536 hash.toBytes
  M9.write 3039 hash.toBytes

/-- Every constructor `MSTORE` is reflected by the corresponding byte-image
write. -/
theorem weth10InitPreHashMemory_reads (sevm : Sevm) :
    Mem.Reads (weth10InitPreHashMemory sevm)
      (weth10InitPreHashImage sevm) := by
  let copied := sevm.code.sliceD 177 6313 (Linst.toUInt8 .stop)
  let chain := sevm.benvStat.chainId.toB256
  have wf0 := Mem.Wf.write Mem.wf_empty 0 copied
  have r0 := Mem.Reads.write Mem.wf_empty Mem.reads_empty 0 copied
  have wf1 := Mem.Wf.write wf0 372 chain.toBytes
  have r1 := Mem.Reads.write wf0 r0 372 chain.toBytes
  have wf2 := Mem.Wf.write wf1 691 chain.toBytes
  have r2 := Mem.Reads.write wf1 r1 691 chain.toBytes
  have wf3 := Mem.Wf.write wf2 2875 chain.toBytes
  have r3 := Mem.Reads.write wf2 r2 2875 chain.toBytes
  have wf4 := Mem.Wf.write wf3 6336 DOMAIN_TYPEHASH.toBytes
  have r4 := Mem.Reads.write wf3 r3 6336 DOMAIN_TYPEHASH.toBytes
  have wf5 := Mem.Wf.write wf4 6368 NAME_HASH.toBytes
  have r5 := Mem.Reads.write wf4 r4 6368 NAME_HASH.toBytes
  have wf6 := Mem.Wf.write wf5 6400 VERSION_HASH.toBytes
  have r6 := Mem.Reads.write wf5 r5 6400 VERSION_HASH.toBytes
  have wf7 := Mem.Wf.write wf6 6432 chain.toBytes
  have r7 := Mem.Reads.write wf6 r6 6432 chain.toBytes
  have r8 := Mem.Reads.write wf7 r7 6464 sevm.currentTarget.toB256.toBytes
  simpa [weth10InitPreHashMemory, weth10InitChainMemory,
    weth10InitCopyMemory, weth10InitPreHashImage, copied, chain]
    using r8

theorem weth10InitPreHashMemory_wf (sevm : Sevm) :
    Mem.Wf (weth10InitPreHashMemory sevm) := by
  unfold weth10InitPreHashMemory weth10InitChainMemory weth10InitCopyMemory
  apply Mem.Wf.write
  apply Mem.Wf.write
  apply Mem.Wf.write
  apply Mem.Wf.write
  apply Mem.Wf.write
  apply Mem.Wf.write
  apply Mem.Wf.write
  apply Mem.Wf.write
  apply Mem.Wf.write
  exact Mem.wf_empty

private lemma Bytes.length_writeAt_of_le
    {bs xs : Bytes} {n : Nat} (h : n + xs.length ≤ bs.length) :
    (Bytes.writeAt bs n xs).length = bs.length := by
  unfold Bytes.writeAt
  simp only [List.length_append, List.length_drop]
  rw [List.takeD_eq_take _ (by omega), List.length_take_of_le (by omega)]
  omega

private lemma Bytes.writeAt_append_payload
    {bs xs ys : Bytes} {n : Nat} (hbs : bs.length ≤ n) :
    Bytes.writeAt (Bytes.writeAt bs n xs) (n + xs.length) ys =
      Bytes.writeAt bs n (xs ++ ys) := by
  have hfirst :
      Bytes.writeAt bs n xs = List.takeD n bs 0 ++ xs := by
    unfold Bytes.writeAt
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
  rw [hfirst]
  rw [Bytes.writeAt_of_length_eq (by rw [List.length_append, List.takeD_length])]
  unfold Bytes.writeAt
  rw [List.drop_eq_nil_of_le (by omega)]
  simp [List.append_assoc]

private lemma Bytes.sliceD_five_b256_writes
    (bs : Bytes) (n : Nat) (hbs : bs.length ≤ n)
    (a b c d e : B256) :
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt
            (Bytes.writeAt bs n a.toBytes)
            (n + 32) b.toBytes)
          (n + 64) c.toBytes)
        (n + 96) d.toBytes)
      (n + 128) e.toBytes).sliceD n 160 0 =
      a.toBytes ++ b.toBytes ++ c.toBytes ++ d.toBytes ++ e.toBytes := by
  rw [show n + 32 = n + a.toBytes.length by rw [B256.length_toBytes],
    Bytes.writeAt_append_payload hbs]
  rw [show n + 64 = n + (a.toBytes ++ b.toBytes).length by
      simp only [List.length_append, B256.length_toBytes],
    Bytes.writeAt_append_payload hbs]
  rw [show n + 96 =
      n + (a.toBytes ++ b.toBytes ++ c.toBytes).length by
      simp only [List.length_append, B256.length_toBytes],
    Bytes.writeAt_append_payload hbs]
  rw [show n + 128 =
      n + (a.toBytes ++ b.toBytes ++ c.toBytes ++ d.toBytes).length by
      simp only [List.length_append, B256.length_toBytes],
    Bytes.writeAt_append_payload hbs]
  rw [show 160 =
      (a.toBytes ++ b.toBytes ++ c.toBytes ++ d.toBytes ++ e.toBytes).length by
      simp only [List.length_append, B256.length_toBytes],
    Bytes.sliceD_writeAt]

/-- The scratch window hashed by the constructor is exactly the five-word
EIP-712 deployment preimage. -/
theorem weth10InitPreHashMemory_read (sevm : Sevm) :
    ((weth10InitPreHashMemory sevm).read 6336 160).1 =
      DOMAIN_TYPEHASH.toBytes ++ NAME_HASH.toBytes ++ VERSION_HASH.toBytes ++
        sevm.benvStat.chainId.toB256.toBytes ++
        sevm.currentTarget.toB256.toBytes := by
  rw [Mem.Reads.read (weth10InitPreHashMemory_reads sevm) 6336 160]
  let copied := sevm.code.sliceD 177 6313 (Linst.toUInt8 .stop)
  let chain := sevm.benvStat.chainId.toB256
  let I0 := Bytes.writeAt [] 0 copied
  let I1 := Bytes.writeAt I0 372 chain.toBytes
  let I2 := Bytes.writeAt I1 691 chain.toBytes
  let I3 := Bytes.writeAt I2 2875 chain.toBytes
  have h0 : I0.length = 6313 := by
    simp [I0, copied, Bytes.writeAt, ByteArray.length_sliceD]
  have h1 : I1.length = 6313 := by
    rw [show I1 = Bytes.writeAt I0 372 chain.toBytes from rfl,
      Bytes.length_writeAt_of_le (by rw [h0, B256.length_toBytes]; omega), h0]
  have h2 : I2.length = 6313 := by
    rw [show I2 = Bytes.writeAt I1 691 chain.toBytes from rfl,
      Bytes.length_writeAt_of_le (by rw [h1, B256.length_toBytes]; omega), h1]
  have h3 : I3.length = 6313 := by
    rw [show I3 = Bytes.writeAt I2 2875 chain.toBytes from rfl,
      Bytes.length_writeAt_of_le (by rw [h2, B256.length_toBytes]; omega), h2]
  change
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt
            (Bytes.writeAt I3 6336 DOMAIN_TYPEHASH.toBytes)
            6368 NAME_HASH.toBytes)
          6400 VERSION_HASH.toBytes)
        6432 chain.toBytes)
      6464 sevm.currentTarget.toB256.toBytes).sliceD 6336 160 0 = _
  exact Bytes.sliceD_five_b256_writes I3 6336 (by omega)
    DOMAIN_TYPEHASH NAME_HASH VERSION_HASH chain sevm.currentTarget.toB256

/-- The constructor's `CODECOPY` window is exactly the appended zero-parameter
runtime template. -/
theorem weth10InitCode_slice_runtime {sevm : Sevm}
    (h_code : sevm.code.toList = weth10InitCode) :
    sevm.code.sliceD 177 6313 (Linst.toUInt8 .stop) =
      weth10RuntimeTemplate := by
  rw [ByteArray.sliceD_eq, h_code]
  unfold weth10InitCode
  rw [show 177 = weth10InitPrefix.length from weth10InitPrefix_length.symm]
  unfold List.sliceD
  rw [List.drop_left]
  rw [List.takeD_eq_take _ (by rw [weth10RuntimeTemplate_length])]
  simpa only [weth10RuntimeTemplate_length] using
    (List.take_length (l := weth10RuntimeTemplate))

/-- Reader-level image of the completed constructor memory. -/
theorem weth10InitMemory_reads (sevm : Sevm) :
    let separator := deploymentDomainSeparator
      sevm.benvStat.chainId.toB256 sevm.currentTarget
    Mem.Reads (weth10InitMemory sevm)
      (Bytes.writeAt
        (Bytes.writeAt (weth10InitPreHashImage sevm) 536 separator.toBytes)
        3039 separator.toBytes) := by
  let separator := deploymentDomainSeparator
    sevm.benvStat.chainId.toB256 sevm.currentTarget
  have hhash :
      ((weth10InitPreHashMemory sevm).read 6336 160).1.keccak = separator := by
    rw [weth10InitPreHashMemory_read]
    rfl
  have wf8 := weth10InitPreHashMemory_wf sevm
  have r8 := weth10InitPreHashMemory_reads sevm
  have wf9 := Mem.Wf.write wf8 536 separator.toBytes
  have r9 := Mem.Reads.write wf8 r8 536 separator.toBytes
  have r10 := Mem.Reads.write wf9 r9 3039 separator.toBytes
  simpa [weth10InitMemory, separator, hhash] using r10

private lemma Bytes.sliceD_writeAt_after
    (bs xs : Bytes) (start len n : Nat)
    (h : start + len ≤ n) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt]
  rw [if_neg]
  omega

private lemma Bytes.getD_sliceD_of_lt
    (bs : Bytes) (start len i : Nat) (hi : i < len) :
    (bs.sliceD start len 0).getD i 0 = bs.getD (start + i) 0 := by
  rw [List.sliceD_eq_map]
  simp [List.getD_eq_getElem?_getD, hi]

private lemma Bytes.sliceD_writeAt_congr
    {bs cs xs : Bytes} {len n : Nat}
    (h : bs.sliceD 0 len 0 = cs.sliceD 0 len 0) :
    (Bytes.writeAt bs n xs).sliceD 0 len 0 =
      (Bytes.writeAt cs n xs).sliceD 0 len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [Nat.zero_add]
  rw [Bytes.getD_writeAt, Bytes.getD_writeAt]
  split
  · rfl
  · have hg := congrArg (fun zs : Bytes => zs.getD i 0) h
    simpa only [Bytes.getD_sliceD_of_lt _ 0 len i hi', Nat.zero_add] using hg

/-- Scratch writes lie above the returned window, while the five in-window
stores are exactly `weth10PatchedRuntime`. -/
theorem weth10InitMemory_read_runtime {sevm : Sevm}
    (h_code : sevm.code.toList = weth10InitCode) :
    ((weth10InitMemory sevm).read 0 6313).1 =
      weth10PatchedRuntime sevm.benvStat.chainId.toB256
        (deploymentDomainSeparator
          sevm.benvStat.chainId.toB256 sevm.currentTarget) := by
  let chain := sevm.benvStat.chainId.toB256
  let separator := deploymentDomainSeparator chain sevm.currentTarget
  let I1 := Bytes.writeAt weth10RuntimeTemplate 372 chain.toBytes
  let I2 := Bytes.writeAt I1 691 chain.toBytes
  let I3 := Bytes.writeAt I2 2875 chain.toBytes
  let I4 := Bytes.writeAt I3 536 separator.toBytes
  let I5 := Bytes.writeAt I4 3039 separator.toBytes
  have h1 : I1.length = 6313 := by
    rw [show I1 = Bytes.writeAt weth10RuntimeTemplate 372 chain.toBytes from rfl,
      Bytes.length_writeAt_of_le (by
        rw [weth10RuntimeTemplate_length, B256.length_toBytes]; omega),
      weth10RuntimeTemplate_length]
  have h2 : I2.length = 6313 := by
    rw [show I2 = Bytes.writeAt I1 691 chain.toBytes from rfl,
      Bytes.length_writeAt_of_le (by rw [h1, B256.length_toBytes]; omega), h1]
  have h3 : I3.length = 6313 := by
    rw [show I3 = Bytes.writeAt I2 2875 chain.toBytes from rfl,
      Bytes.length_writeAt_of_le (by rw [h2, B256.length_toBytes]; omega), h2]
  have h4 : I4.length = 6313 := by
    rw [show I4 = Bytes.writeAt I3 536 separator.toBytes from rfl,
      Bytes.length_writeAt_of_le (by rw [h3, B256.length_toBytes]; omega), h3]
  have h5 : I5.length = 6313 := by
    rw [show I5 = Bytes.writeAt I4 3039 separator.toBytes from rfl,
      Bytes.length_writeAt_of_le (by rw [h4, B256.length_toBytes]; omega), h4]
  have hpre :
      (weth10InitPreHashImage sevm).sliceD 0 6313 0 = I3 := by
    unfold weth10InitPreHashImage
    rw [Bytes.sliceD_writeAt_after _ _ 0 6313 6464 (by omega),
      Bytes.sliceD_writeAt_after _ _ 0 6313 6432 (by omega),
      Bytes.sliceD_writeAt_after _ _ 0 6313 6400 (by omega),
      Bytes.sliceD_writeAt_after _ _ 0 6313 6368 (by omega),
      Bytes.sliceD_writeAt_after _ _ 0 6313 6336 (by omega)]
    rw [weth10InitCode_slice_runtime h_code]
    rw [show Bytes.writeAt [] 0 weth10RuntimeTemplate =
      weth10RuntimeTemplate from Bytes.writeAt_zero_of_le (by simp)]
    exact Bytes.sliceD_zero_length h3
  have hsep1 :
      (Bytes.writeAt (weth10InitPreHashImage sevm) 536 separator.toBytes).sliceD
          0 6313 0 = I4.sliceD 0 6313 0 := by
    have hpre' :
        (weth10InitPreHashImage sevm).sliceD 0 6313 0 =
          I3.sliceD 0 6313 0 :=
      hpre.trans (Bytes.sliceD_zero_length h3).symm
    exact Bytes.sliceD_writeAt_congr hpre'
  have hsep2 :
      (Bytes.writeAt
        (Bytes.writeAt (weth10InitPreHashImage sevm) 536 separator.toBytes)
        3039 separator.toBytes).sliceD 0 6313 0 =
          I5.sliceD 0 6313 0 := by
    exact Bytes.sliceD_writeAt_congr hsep1
  rw [Mem.Reads.read (weth10InitMemory_reads sevm) 0 6313]
  rw [hsep2, Bytes.sliceD_zero_length h5]
  rfl

private theorem memRead_fst_eq (d : Devm) (index size : Nat) :
    (d.memRead index size).1 = (d.memory.read index size).1 := rfl

private def weth10InitReturnPre
    (base : Devm) (M : Mem) (g : Nat) : Devm :=
  base.setMach
    ⟨[(0 : B256), (6313 : B256)], M, g - 1471⟩

private def weth10InitReturnRead
    (base : Devm) (M : Mem) (g : Nat) : Bytes × Devm :=
  let retPre := weth10InitReturnPre base M g
  (retPre.setMach ⟨[], retPre.memory, g - 1471⟩).memRead 0 6313

private theorem weth10InitReturnPre_stack
    (base : Devm) (M : Mem) (g : Nat) :
    (weth10InitReturnPre base M g).stack =
      [(0 : B256), (6313 : B256)] := rfl

private theorem weth10InitReturnPre_memory
    (base : Devm) (M : Mem) (g : Nat) :
    (weth10InitReturnPre base M g).memory = M := rfl

private theorem weth10InitReturnPre_gasLeft
    (base : Devm) (M : Mem) (g : Nat) :
    (weth10InitReturnPre base M g).gasLeft = g - 1471 := rfl

private theorem weth10InitReturnRead_eq
    (base : Devm) (M : Mem) (g : Nat) :
    ((weth10InitReturnPre base M g).setMach
      ⟨[], (weth10InitReturnPre base M g).memory,
        g - 1471⟩).memRead 0 6313 =
      weth10InitReturnRead base M g := rfl

private theorem weth10InitReturnRead_fst
    (base : Devm) (M : Mem) (g : Nat) :
    (weth10InitReturnRead base M g).1 = (M.read 0 6313).1 := rfl

private theorem weth10InitReturnRead_state
    (base : Devm) (M : Mem) (g : Nat) :
    (weth10InitReturnRead base M g).2.state = base.state := rfl

private theorem weth10InitReturnRead_logs
    (base : Devm) (M : Mem) (g : Nat) :
    (weth10InitReturnRead base M g).2.logs = base.logs := rfl

private theorem weth10InitReturnRead_error
    (base : Devm) (M : Mem) (g : Nat) :
    (weth10InitReturnRead base M g).2.error = base.error := rfl

private theorem weth10InitReturnRead_refundCounter
    (base : Devm) (M : Mem) (g : Nat) :
    (weth10InitReturnRead base M g).2.refundCounter = base.refundCounter := rfl

private theorem weth10InitReturnRead_accountsToDelete
    (base : Devm) (M : Mem) (g : Nat) :
    (weth10InitReturnRead base M g).2.accountsToDelete =
      base.accountsToDelete := rfl

private theorem weth10InitReturnRead_createdAccounts
    (base : Devm) (M : Mem) (g : Nat) :
    (weth10InitReturnRead base M g).2.createdAccounts =
      base.createdAccounts := rfl

/-- The exact successful constructor post-state before creation settlement
charges code-deposit gas. -/
def weth10InitPost (sevm : Sevm) (base : Devm) (g : Nat) : Devm :=
  let d := weth10InitReturnRead base (weth10InitMemory sevm) g
  d.2.withOutput d.1

private theorem weth10InitPost_eq
    (sevm : Sevm) (base : Devm) (g : Nat) :
    weth10InitPost sevm base g =
      (weth10InitReturnRead base (weth10InitMemory sevm) g).2.withOutput
        (weth10InitReturnRead base (weth10InitMemory sevm) g).1 := rfl

private theorem weth10InitCopyLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {g : Nat}
    {rest : Func} (h_gas : 1275 ≤ g)
    (h_rest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], weth10InitCopyMemory sevm, g - 1275⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, g⟩)
      (weth10InitCopyLine 6313 177 +++ rest) post := by
  unfold weth10InitCopyLine
  func_run (4) [1267]
  · exact Devm.extCost_add_of_size
      (a := gVerylow + gasCopy * ceilDiv 6313 32)
      rfl (by decide)
  · exact h_rest

private theorem weth10InitCopyMemory_size (sevm : Sevm) :
    (weth10InitCopyMemory sevm).size = 6336 := by
  unfold weth10InitCopyMemory
  generalize hb :
      sevm.code.sliceD 177 6313 (Linst.toUInt8 .stop) = bs
  have hlen : bs.length = 6313 := by
    rw [← hb]
    exact ByteArray.length_sliceD _ _ _ _
  rcases bs with _ | ⟨b, bs⟩
  · simp at hlen
  · rw [Mem.size_write_cons]
    simp only [List.length_cons] at hlen ⊢
    simp [Mem.empty, hlen, ceil32]

private theorem weth10InitChainLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {g : Nat}
    {rest : Func} (h_gas : 24 ≤ g)
    (h_rest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], weth10InitChainMemory sevm, g - 24⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], weth10InitCopyMemory sevm, g⟩)
      (weth10InitChainLine +++ rest) post := by
  have h372 :
      (Bytes.toB256 [(372 >>> 8).toUInt8, (372 : Nat).toUInt8]).toNat =
        372 := by
    decide +kernel
  have h691 :
      (Bytes.toB256 [(691 >>> 8).toUInt8, (691 : Nat).toUInt8]).toNat =
        691 := by
    decide +kernel
  have h2875 :
      (Bytes.toB256 [(2875 >>> 8).toUInt8, (2875 : Nat).toUInt8]).toNat =
        2875 := by
    decide +kernel
  unfold weth10InitChainLine deploymentChainIdWordOffsets
  func_run (9) [0, 0, 0]
  · exact Devm.extCost_zero_of_le
      (by rw [weth10InitCopyMemory_size])
      (by rw [weth10InitCopyMemory_size, h372]; decide)
  · exact Devm.extCost_zero_of_le
      (by rw [Mem.size_write_of_le
        (by rw [weth10InitCopyMemory_size, B256.length_toBytes]; decide),
        weth10InitCopyMemory_size])
      (by
        rw [Mem.size_write_of_le
          (by rw [weth10InitCopyMemory_size, B256.length_toBytes]; decide),
          weth10InitCopyMemory_size, h691]
        decide)
  · exact Devm.extCost_zero_of_le
      (by
        rw [Mem.size_write_of_le
          (by
            rw [Mem.size_write_of_le
              (by rw [weth10InitCopyMemory_size, B256.length_toBytes]; decide),
              weth10InitCopyMemory_size, B256.length_toBytes]
            decide),
          Mem.size_write_of_le
            (by rw [weth10InitCopyMemory_size, B256.length_toBytes]; decide),
          weth10InitCopyMemory_size])
      (by
        rw [Mem.size_write_of_le
          (by
            rw [Mem.size_write_of_le
              (by rw [weth10InitCopyMemory_size, B256.length_toBytes]; decide),
              weth10InitCopyMemory_size, B256.length_toBytes]
            decide),
          Mem.size_write_of_le
            (by rw [weth10InitCopyMemory_size, B256.length_toBytes]; decide),
          weth10InitCopyMemory_size, h2875]
        decide)
  · exact h_rest

private theorem weth10InitChainMemory_size (sevm : Sevm) :
    (weth10InitChainMemory sevm).size = 6336 := by
  unfold weth10InitChainMemory
  repeat' rw [Mem.size_write_of_le]
  · exact weth10InitCopyMemory_size sevm
  all_goals
    rw [weth10InitCopyMemory_size, B256.length_toBytes]
    decide

private def weth10InitPreHashTail1 : Line :=
  (weth10InitPreHashLine 6313).drop 3

private def weth10InitPreHashTail2 : Line :=
  (weth10InitPreHashLine 6313).drop 6

private def weth10InitPreHashTail3 : Line :=
  (weth10InitPreHashLine 6313).drop 9

private def weth10InitPreHashTail4 : Line :=
  (weth10InitPreHashLine 6313).drop 12

private def weth10InitPreHashTail5 : Line :=
  (weth10InitPreHashLine 6313).drop 15

private theorem weth10InitPreHashType_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {g : Nat}
    {M : Mem} {rest : Func} (h_gas : 13 ≤ g) (h_size : M.size = 6336)
    (h_rest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], M.write 6336 DOMAIN_TYPEHASH.toBytes, g - 13⟩)
      (weth10InitPreHashTail1 +++ rest) post) :
    Func.RunCompiled fs sevm (base.setMach ⟨[], M, g⟩)
      (weth10InitPreHashLine 6313 +++ rest) post := by
  unfold weth10InitPreHashLine
  func_run (3) [4]
  · exact Devm.extCost_of_size h_size (by decide)
  · exact h_rest

private theorem weth10InitPreHashName_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {g : Nat}
    {M : Mem} {rest : Func} (h_gas : 13 ≤ g) (h_size : M.size = 6368)
    (h_rest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M.write 6368 NAME_HASH.toBytes, g - 13⟩)
      (weth10InitPreHashTail2 +++ rest) post) :
    Func.RunCompiled fs sevm (base.setMach ⟨[], M, g⟩)
      (weth10InitPreHashTail1 +++ rest) post := by
  unfold weth10InitPreHashTail1 weth10InitPreHashLine
  func_run (3) [4]
  · exact Devm.extCost_of_size h_size (by decide)
  · exact h_rest

private theorem weth10InitPreHashVersion_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {g : Nat}
    {M : Mem} {rest : Func} (h_gas : 12 ≤ g) (h_size : M.size = 6400)
    (h_rest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M.write 6400 VERSION_HASH.toBytes, g - 12⟩)
      (weth10InitPreHashTail3 +++ rest) post) :
    Func.RunCompiled fs sevm (base.setMach ⟨[], M, g⟩)
      (weth10InitPreHashTail2 +++ rest) post := by
  unfold weth10InitPreHashTail2 weth10InitPreHashLine
  func_run (3) [3]
  · exact Devm.extCost_of_size h_size (by decide)
  · exact h_rest

private theorem weth10InitPreHashChain_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {g : Nat}
    {M : Mem} {rest : Func} (h_gas : 12 ≤ g) (h_size : M.size = 6432)
    (h_rest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], M.write 6432 sevm.benvStat.chainId.toB256.toBytes, g - 12⟩)
      (weth10InitPreHashTail4 +++ rest) post) :
    Func.RunCompiled fs sevm (base.setMach ⟨[], M, g⟩)
      (weth10InitPreHashTail3 +++ rest) post := by
  unfold weth10InitPreHashTail3 weth10InitPreHashLine
  func_run (3) [4]
  · exact Devm.extCost_of_size h_size (by decide)
  · exact h_rest

private theorem weth10InitPreHashAddress_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {g : Nat}
    {M : Mem} {rest : Func} (h_gas : 12 ≤ g) (h_size : M.size = 6464)
    (h_rest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], M.write 6464 sevm.currentTarget.toB256.toBytes, g - 12⟩)
      (weth10InitPreHashTail5 +++ rest) post) :
    Func.RunCompiled fs sevm (base.setMach ⟨[], M, g⟩)
      (weth10InitPreHashTail4 +++ rest) post := by
  unfold weth10InitPreHashTail4 weth10InitPreHashLine
  func_run (3) [4]
  · exact Devm.extCost_of_size h_size (by decide)
  · exact h_rest

private theorem initGas_preHash13 {g : Nat} (h : 62 ≤ g) :
    (g - 13) - 13 = g - 26 := by omega

private theorem initGas_preHash26 {g : Nat} (h : 62 ≤ g) :
    (g - 26) - 12 = g - 38 := by omega

private theorem initGas_preHash38 {g : Nat} (h : 62 ≤ g) :
    (g - 38) - 12 = g - 50 := by omega

private theorem initGas_preHash50 {g : Nat} (h : 62 ≤ g) :
    (g - 50) - 12 = g - 62 := by omega

private theorem weth10InitPreHashLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {g : Nat}
    {rest : Func} (h_gas : 62 ≤ g)
    (h_rest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], weth10InitPreHashMemory sevm, g - 62⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], weth10InitChainMemory sevm, g⟩)
      (weth10InitPreHashLine 6313 +++ rest) post := by
  let M3 := weth10InitChainMemory sevm
  let chain := sevm.benvStat.chainId.toB256
  let M4 := M3.write 6336 DOMAIN_TYPEHASH.toBytes
  let M5 := M4.write 6368 NAME_HASH.toBytes
  let M6 := M5.write 6400 VERSION_HASH.toBytes
  let M7 := M6.write 6432 chain.toBytes
  have hs3 : M3.size = 6336 := weth10InitChainMemory_size sevm
  have hs4 : M4.size = 6368 := by
    rw [Mem.size_write_word_at, hs3]
    decide
  have hs5 : M5.size = 6400 := by
    rw [Mem.size_write_word_at, hs4]
    decide
  have hs6 : M6.size = 6432 := by
    rw [Mem.size_write_word_at, hs5]
    decide
  have hs7 : M7.size = 6464 := by
    rw [Mem.size_write_word_at, hs6]
    decide
  apply weth10InitPreHashType_runCompiled (g := g) (h_size := hs3)
  · omega
  · apply weth10InitPreHashName_runCompiled
        (g := g - 13) (h_size := hs4)
    · omega
    · rw [initGas_preHash13 h_gas]
      apply weth10InitPreHashVersion_runCompiled
          (g := g - 26) (h_size := hs5)
      · omega
      · rw [initGas_preHash26 h_gas]
        apply weth10InitPreHashChain_runCompiled
            (g := g - 38) (h_size := hs6)
        · omega
        · rw [initGas_preHash38 h_gas]
          apply weth10InitPreHashAddress_runCompiled
              (g := g - 50) (h_size := hs7)
          · omega
          · simpa [weth10InitPreHashMemory, M3, M4, M5, M6, M7, chain,
              weth10InitPreHashTail5, weth10InitPreHashLine, prepend,
              initGas_preHash50 h_gas] using h_rest

private theorem weth10InitPreHashMemory_size (sevm : Sevm) :
    (weth10InitPreHashMemory sevm).size = 6496 := by
  let M3 := weth10InitChainMemory sevm
  let chain := sevm.benvStat.chainId.toB256
  let M4 := M3.write 6336 DOMAIN_TYPEHASH.toBytes
  let M5 := M4.write 6368 NAME_HASH.toBytes
  let M6 := M5.write 6400 VERSION_HASH.toBytes
  let M7 := M6.write 6432 chain.toBytes
  have hs3 : M3.size = 6336 := weth10InitChainMemory_size sevm
  have hs4 : M4.size = 6368 := by
    rw [show M4 = M3.write 6336 DOMAIN_TYPEHASH.toBytes from rfl,
      Mem.size_write_word_at, hs3]
    decide
  have hs5 : M5.size = 6400 := by
    rw [show M5 = M4.write 6368 NAME_HASH.toBytes from rfl,
      Mem.size_write_word_at, hs4]
    decide
  have hs6 : M6.size = 6432 := by
    rw [show M6 = M5.write 6400 VERSION_HASH.toBytes from rfl,
      Mem.size_write_word_at, hs5]
    decide
  have hs7 : M7.size = 6464 := by
    rw [show M7 = M6.write 6432 chain.toBytes from rfl,
      Mem.size_write_word_at, hs6]
    decide
  have hs8 : (M7.write 6464 sevm.currentTarget.toB256.toBytes).size =
      6496 := by
    rw [Mem.size_write_word_at, hs7]
    decide
  simpa [weth10InitPreHashMemory, M3, M4, M5, M6, M7, chain] using hs8

private theorem initPush2Value_160 :
    (Bytes.toB256 [(160 >>> 8).toUInt8, (160 : Nat).toUInt8]).toNat =
      160 := by
  decide +kernel

private theorem initPush2Value_6336 :
    (Bytes.toB256 [(6336 >>> 8).toUInt8, (6336 : Nat).toUInt8]).toNat =
      6336 := by
  decide +kernel

private theorem weth10InitHashLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {g : Nat}
    {M M' : Mem} {hash : B256} {rest : Func}
    (h_gas : 66 ≤ g)
    (h_align : M.size % 32 = 0)
    (h_cover : 6336 + 160 ≤ M.size)
    (h_hash : (M.read 6336 160).1.keccak = hash)
    (h_image : (M.read 6336 160).2 = M')
    (h_rest : Func.RunCompiled fs sevm
      (base.setMach ⟨[hash], M', g - 66⟩) rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, g⟩)
      (weth10InitHashLine 6313 +++ rest) post := by
  unfold weth10InitHashLine
  func_run (3) [60, hash]
  · rw [initPush2Value_160, initPush2Value_6336]
    rw [Devm.extCost_zero_of_le h_align h_cover]
    decide
  · rw [initPush2Value_160, initPush2Value_6336, h_image]
    exact h_rest

private def weth10InitSeparatorMemory (M : Mem) (separator : B256) : Mem :=
  (M.write 536 separator.toBytes).write 3039 separator.toBytes

private def weth10InitBeforeSeparator (base : Devm) (M : Mem)
    (separator : B256) (g : Nat) : Devm :=
  base.setMach ⟨[separator], M, g - 1446⟩

private def weth10InitAfterSeparator (base : Devm) (M : Mem)
    (separator : B256) (g : Nat) : Devm :=
  base.setMach
    ⟨[], weth10InitSeparatorMemory M separator, g - 1466⟩

private def weth10InitAfterReturnArgs (base : Devm) (M : Mem)
    (g : Nat) : Devm :=
  base.setMach ⟨[(0 : B256), (6313 : B256)], M, g - 1471⟩

private theorem weth10InitAfterReturnArgs_eq
    (base : Devm) (M : Mem) (g : Nat) :
    weth10InitAfterReturnArgs base M g =
      weth10InitReturnPre base M g := rfl

private theorem weth10InitSeparatorLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {M : Mem}
    {separator : B256} {g : Nat} {rest : Func}
    (h_size : M.size = 6496) (h_gas : 1471 ≤ g)
    (h_rest : Func.RunCompiled fs sevm
      (weth10InitAfterSeparator base M separator g) rest post) :
    Func.RunCompiled fs sevm
      (weth10InitBeforeSeparator base M separator g)
      (weth10InitSeparatorLine +++ rest) post := by
  have h536 :
      (Bytes.toB256 [(536 >>> 8).toUInt8, (536 : Nat).toUInt8]).toNat =
        536 := by
    decide +kernel
  have h3039 :
      (Bytes.toB256 [(3039 >>> 8).toUInt8, (3039 : Nat).toUInt8]).toNat =
        3039 := by
    decide +kernel
  have hM1 : (M.write 536 separator.toBytes).size = 6496 := by
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, h_size]
      omega)]
    exact h_size
  unfold weth10InitBeforeSeparator
  unfold weth10InitSeparatorLine cachedDomainSeparatorWordOffsets
  func_run (7) [0, 0]
  · exact Devm.extCost_zero_of_le
      (by rw [h_size])
      (by rw [h_size, h536]; decide)
  · exact Devm.extCost_zero_of_le
      (by rw [h536, hM1])
      (by rw [h536, h3039, hM1]; decide)
  · exact h_rest

private theorem weth10InitReturnLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {M : Mem}
    {g : Nat} {rest : Func} (h_gas : 1471 ≤ g)
    (h_rest : Func.RunCompiled fs sevm
      (weth10InitAfterReturnArgs base M g) rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, g - 1466⟩)
      (weth10InitReturnLine 6313 +++ rest) post := by
  unfold weth10InitReturnLine
  func_run (2)
  exact h_rest

private theorem weth10InitGuard_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {g : Nat}
    (h_value : sevm.value = 0) (h_gas : 1471 ≤ g)
    (h_rest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, g - 19⟩)
      (weth10InitSuccess 6313 177) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, g⟩) weth10InitFunc post := by
  unfold weth10InitFunc
  func_run (3) [1]
  · simp only [h_value]
    decide
  · exact h_rest

private theorem weth10InitMemory_size (sevm : Sevm) :
    (weth10InitMemory sevm).size = 6496 := by
  let M8 := weth10InitPreHashMemory sevm
  let hash := (M8.read 6336 160).1.keccak
  have hs8 : M8.size = 6496 := weth10InitPreHashMemory_size sevm
  have hs9 : (M8.write 536 hash.toBytes).size = 6496 := by
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, hs8]
      omega)]
    exact hs8
  unfold weth10InitMemory
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, hs9]
    omega)]
  exact hs9

private theorem weth10InitRet_runCompiled
    {fs : List Func} {sevm : Sevm} {retPre : Devm}
    {rd : Bytes × Devm} {G : Nat}
    (h_stack : retPre.stack = [(0 : B256), (6313 : B256)])
    (h_size : retPre.memory.size = 6496)
    (h_gas : retPre.gasLeft = G)
    (h_read :
      (retPre.setMach ⟨[], retPre.memory, G⟩).memRead 0 6313 = rd) :
    Func.RunCompiled fs sevm retPre Func.ret
      (rd.2.withOutput rd.1) := by
  have h_ext : retPre.extCost [⟨(0 : Nat), (6313 : Nat)⟩] = 0 := by
    apply Devm.extCost_zero_of_le
    · change retPre.memory.size % 32 = 0
      rw [h_size]
    · change 0 + 6313 ≤ retPre.memory.size
      rw [h_size]
      omega
  rcases rd with ⟨out, d'⟩
  apply Func.runCompiled_ret_of (devm := retPre) (G := G)
    (e := 0) (out := out) (d' := d')
  · exact h_stack
  · exact h_ext
  · simpa using h_gas
  · exact h_read

private theorem initGas_hash {g : Nat} (h : 1471 ≤ g) :
    (g - 1380) - 66 = g - 1446 := by
  omega

private theorem initGas_preHash {g : Nat} (h : 1471 ≤ g) :
    (g - 1318) - 62 = g - 1380 := by
  omega

private theorem initGas_chain {g : Nat} (h : 1471 ≤ g) :
    (g - 1294) - 24 = g - 1318 := by
  omega

private theorem initGas_copy {g : Nat} (h : 1471 ≤ g) :
    (g - 19) - 1275 = g - 1294 := by
  omega

private theorem weth10InitSuccess_runCompiled_zero
    {sevm : Sevm} {base : Devm} {g : Nat} (h_gas : 1471 ≤ g) :
    Func.RunCompiled [weth10InitFunc] sevm
      (base.setMach ⟨[], Mem.empty, g - 19⟩)
      (weth10InitSuccess 6313 177) (weth10InitPost sevm base g) := by
  let Mpre := weth10InitPreHashMemory sevm
  let hash := (Mpre.read 6336 160).1.keccak
  have hpre_size : Mpre.size = 6496 := weth10InitPreHashMemory_size sevm
  have hread_image : (Mpre.read 6336 160).2 = Mpre := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hpre_size]
    · rw [hpre_size]
  have hret :
      Func.RunCompiled [weth10InitFunc] sevm
        (weth10InitAfterReturnArgs base (weth10InitMemory sevm) g)
        Func.ret (weth10InitPost sevm base g) := by
    rw [weth10InitAfterReturnArgs_eq, weth10InitPost_eq]
    apply weth10InitRet_runCompiled
        (retPre := weth10InitReturnPre base (weth10InitMemory sevm) g)
        (rd := weth10InitReturnRead base (weth10InitMemory sevm) g)
        (G := g - 1471)
    · exact weth10InitReturnPre_stack base (weth10InitMemory sevm) g
    · rw [weth10InitReturnPre_memory]
      exact weth10InitMemory_size sevm
    · exact weth10InitReturnPre_gasLeft base (weth10InitMemory sevm) g
    · exact weth10InitReturnRead_eq base (weth10InitMemory sevm) g
  have hreturn :
      Func.RunCompiled [weth10InitFunc] sevm
        (base.setMach ⟨[], weth10InitMemory sevm, g - 1466⟩)
        (weth10InitReturnLine 6313 +++ Func.ret)
        (weth10InitPost sevm base g) :=
    weth10InitReturnLine_runCompiled h_gas hret
  have hafter :
      weth10InitAfterSeparator base Mpre hash g =
        base.setMach ⟨[], weth10InitMemory sevm, g - 1466⟩ := by
    rfl
  have hseparator :
      Func.RunCompiled [weth10InitFunc] sevm
        (weth10InitBeforeSeparator base Mpre hash g)
        (weth10InitSeparatorLine +++
          (weth10InitReturnLine 6313 +++ Func.ret))
        (weth10InitPost sevm base g) := by
    apply weth10InitSeparatorLine_runCompiled hpre_size h_gas
    rw [hafter]
    exact hreturn
  have hg_hash := initGas_hash h_gas
  have hhash :
      Func.RunCompiled [weth10InitFunc] sevm
        (base.setMach ⟨[], Mpre, g - 1380⟩)
        (weth10InitHashLine 6313 +++
          (weth10InitSeparatorLine +++
            (weth10InitReturnLine 6313 +++ Func.ret)))
        (weth10InitPost sevm base g) := by
    apply weth10InitHashLine_runCompiled
        (g := g - 1380) (M := Mpre) (M' := Mpre) (hash := hash)
    · omega
    · rw [hpre_size]
    · rw [hpre_size]
    · rfl
    · exact hread_image
    · simpa [weth10InitBeforeSeparator, hg_hash] using hseparator
  have hg_pre := initGas_preHash h_gas
  have hprehash :
      Func.RunCompiled [weth10InitFunc] sevm
        (base.setMach ⟨[], weth10InitChainMemory sevm, g - 1318⟩)
        (weth10InitPreHashLine 6313 +++
          (weth10InitHashLine 6313 +++
            (weth10InitSeparatorLine +++
              (weth10InitReturnLine 6313 +++ Func.ret))))
        (weth10InitPost sevm base g) := by
    apply weth10InitPreHashLine_runCompiled (g := g - 1318)
    · omega
    · simpa [Mpre, hg_pre] using hhash
  have hg_chain := initGas_chain h_gas
  have hchain :
      Func.RunCompiled [weth10InitFunc] sevm
        (base.setMach ⟨[], weth10InitCopyMemory sevm, g - 1294⟩)
        (weth10InitChainLine +++
          (weth10InitPreHashLine 6313 +++
            (weth10InitHashLine 6313 +++
              (weth10InitSeparatorLine +++
                (weth10InitReturnLine 6313 +++ Func.ret)))))
        (weth10InitPost sevm base g) := by
    apply weth10InitChainLine_runCompiled (g := g - 1294)
    · omega
    · simpa [hg_chain] using hprehash
  have hg_copy := initGas_copy h_gas
  have hcopy :
      Func.RunCompiled [weth10InitFunc] sevm
        (base.setMach ⟨[], Mem.empty, g - 19⟩)
        (weth10InitCopyLine 6313 177 +++
          (weth10InitChainLine +++
            (weth10InitPreHashLine 6313 +++
              (weth10InitHashLine 6313 +++
                (weth10InitSeparatorLine +++
                  (weth10InitReturnLine 6313 +++ Func.ret))))))
        (weth10InitPost sevm base g) := by
    apply weth10InitCopyLine_runCompiled (g := g - 19)
    · omega
    · simpa [hg_copy] using hchain
  exact hcopy

/-- On zero endowment, the constructor's successful branch has a complete
gas-exact Blanc walk.  The returned state is named explicitly so downstream
memory and creation-message lemmas can identify its output without replaying
the constructor phases. -/
theorem weth10InitFunc_runCompiled_zero
    {sevm : Sevm} {base : Devm} {g : Nat}
    (h_value : sevm.value = 0) (h_gas : 1471 ≤ g) :
    Func.RunCompiled [weth10InitFunc] sevm
      (base.setMach ⟨[], Mem.empty, g⟩) weth10InitFunc
      (weth10InitPost sevm base g) ∧
    (weth10InitPost sevm base g).gasLeft = g - 1471 := by
  constructor
  · exact weth10InitGuard_runCompiled h_value h_gas
      (weth10InitSuccess_runCompiled_zero h_gas)
  · rfl

/-- The successful constructor returns the exact runtime image produced by its
five fixed-width parameter patches. -/
theorem weth10InitPost_output {sevm : Sevm} {base : Devm} {g : Nat}
    (h_code : sevm.code.toList = weth10InitCode) :
    (weth10InitPost sevm base g).output =
      weth10PatchedRuntime sevm.benvStat.chainId.toB256
        (deploymentDomainSeparator
          sevm.benvStat.chainId.toB256 sevm.currentTarget) := by
  rw [weth10InitPost_eq, Devm.withOutput_output,
    weth10InitReturnRead_fst]
  exact weth10InitMemory_read_runtime h_code

/-- The returned bytes are the exact runtime family member determined by the
creation environment's chain id and target address. -/
theorem weth10InitPost_output_code {sevm : Sevm} {base : Devm} {g : Nat}
    (h_code : sevm.code.toList = weth10InitCode) :
    (weth10InitPost sevm base g).output =
      weth10Code
        (freshDeployParams sevm.benvStat.chainId.toB256 sevm.currentTarget) := by
  rw [weth10InitPost_output h_code, weth10PatchedRuntime_eq_code]
  rfl

/-- Constructor execution changes only machine memory/stack/gas and the return
buffer: it preserves the supplied world state, logs, and settled-error field. -/
theorem weth10InitPost_preserves_frame {sevm : Sevm} {base : Devm} {g : Nat} :
    (weth10InitPost sevm base g).state = base.state ∧
    (weth10InitPost sevm base g).logs = base.logs ∧
    (weth10InitPost sevm base g).error = base.error := by
  refine ⟨?_, ?_, ?_⟩
  · rw [weth10InitPost_eq, Devm.withOutput_state]
    exact weth10InitReturnRead_state base (weth10InitMemory sevm) g
  · rw [weth10InitPost_eq, Devm.withOutput_logs]
    exact weth10InitReturnRead_logs base (weth10InitMemory sevm) g
  · rw [weth10InitPost_eq, Devm.withOutput_error]
    exact weth10InitReturnRead_error base (weth10InitMemory sevm) g

/-- Constructor execution also preserves the transaction-settlement metadata
that a top-level creation bridge must expose explicitly. -/
theorem weth10InitPost_preserves_transaction_meta
    {sevm : Sevm} {base : Devm} {g : Nat} :
    (weth10InitPost sevm base g).refundCounter = base.refundCounter ∧
    (weth10InitPost sevm base g).accountsToDelete = base.accountsToDelete ∧
    (weth10InitPost sevm base g).createdAccounts = base.createdAccounts := by
  refine ⟨?_, ?_, ?_⟩
  · rw [weth10InitPost_eq, Devm.withOutput_refundCounter]
    exact weth10InitReturnRead_refundCounter base (weth10InitMemory sevm) g
  · rw [weth10InitPost_eq, Devm.withOutput_accountsToDelete]
    exact weth10InitReturnRead_accountsToDelete base (weth10InitMemory sevm) g
  · rw [weth10InitPost_eq, Devm.withOutput_createdAccounts]
    exact weth10InitReturnRead_createdAccounts base (weth10InitMemory sevm) g

/-- The actual hand-emitted initcode, including its inert runtime-data suffix,
executes the gas-exact successful constructor walk at pc zero. -/
theorem weth10Init_exec_zero
    {sevm : Sevm} {base : Devm} {g : Nat}
    (h_value : sevm.value = 0) (h_gas : 1471 ≤ g)
    (h_code : sevm.code.toList = weth10InitCode) :
    exec ⟨0, sevm, base.setMach ⟨[], Mem.empty, g⟩⟩ =
      .ok (weth10InitPost sevm base g) := by
  apply Func.exec_of_runCompiled_prefix
    (weth10InitFunc_runCompiled_zero h_value h_gas).1
    weth10InitFunc_noCalls weth10InitFunc_compile
  simpa [weth10InitCode] using h_code

/-- Exact pre-settlement state of the constructor's nonpayable rejection arm. -/
def weth10InitRejectPost (base : Devm) (g : Nat) : Devm :=
  (base.setMach ⟨[], Mem.empty, g - 22⟩).withOutput []

/-- A nonzero endowment takes the constructor's short arm and empty-reverts
after exactly 22 gas, before any runtime copy or persistent effect. -/
theorem weth10InitFunc_runCompiledTo_nonzero
    {sevm : Sevm} {base : Devm} {g : Nat}
    (h_value : sevm.value ≠ 0) (h_gas : 22 ≤ g) :
    Func.RunCompiledTo [weth10InitFunc] sevm
      (base.setMach ⟨[], Mem.empty, g⟩) weth10InitFunc
      (.error (.revert, weth10InitRejectPost base g)) := by
  unfold weth10InitFunc weth10InitRejectPost
  func_run (3) [0]
  · simp [B256.eqCheck, h_value]
  · exact Func.runCompiledTo_rev_func
      (devm := base.setMach ⟨[], Mem.empty, g - 18⟩) (G := g - 22)
      (by simp only [Devm.gasLeft_setMach, gBase]; omega)
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)

/-- The actual appended-data initcode empty-reverts on every nonzero
endowment; the runtime suffix is never entered. -/
theorem weth10Init_exec_nonzero
    {sevm : Sevm} {base : Devm} {g : Nat}
    (h_value : sevm.value ≠ 0) (h_gas : 22 ≤ g)
    (h_code : sevm.code.toList = weth10InitCode) :
    exec ⟨0, sevm, base.setMach ⟨[], Mem.empty, g⟩⟩ =
      .error (.revert, weth10InitRejectPost base g) := by
  apply Func.exec_of_runCompiledTo_prefix
    (weth10InitFunc_runCompiledTo_nonzero h_value h_gas)
    weth10InitFunc_noCalls weth10InitFunc_compile
  simpa [weth10InitCode] using h_code


end Weth10

end Blanc
