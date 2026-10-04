import Blanc.Lift.UniswapV2Pair.Creation.Facts
import Blanc.Lift.CreationOps
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.PackedSha

/-!
# The Uniswap V2 Pair constructor, walked

A gas-exact synthetic run (`SProg.RunExact`) of the lifted constructor of the Pair's creation
code (`Creation/Cert.lean`, solc 0.5.16; one straight-line entry).  The constructor

* sets the free pointer and stores `unlocked = 1` in slot 12;
* rejects a nonzero call value;
* copies the 82-byte EIP-712 domain type string from the end of the creation code and hashes it,
  lays out the ABI words `typeHash`, `keccak("Uniswap V2")`, `keccak("1")`, `3 + 2322 + 3 + 3 + 3 + 3 + sstoreCost sevm (w3 sevm b) 5 sevm.caller.toB256 + 3 + 3 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (w2 sevm b) 5 + 3 + 3 + 2 + sstoreCost sevm (w1 sevm b) 3 (domainSeparator sevm.benvStat.chainId.toB256 sevm.currentTarget) + 3 + 60 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 48 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 24 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 2 + 1 + 10 + 3 + 3 + 3 + 2 + sstoreCost sevm b 12 1 + 3 + 3 + 12 + 3 + 3ID` and
  `ADDRESS`, hashes those five words and stores the digest in slot 3 (`DOMAIN_SEPARATOR`);
* reads slot 5, clears its low 160 bits and ORs in `CALLER` (`factory = msg.sender`);
* copies the appended runtime (11,293 bytes at offset `0x105`) to memory and returns it.

The domain separator is a conclusion of the walk: the digest of the memory the walk itself built
(`domain_read`), with the chain id and the new address symbolic.  Gas is exact.
-/

namespace Blanc.Lift.UniswapV2Pair.Creation

open Jaune Blanc.Lift

/-- The lifted constructor program. -/
abbrev prog : List SFunc := Cert.prog cert

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome}

/-- `3 + 2322 + 3 + 3 + 3 + 3 + sstoreCost sevm (w3 sevm b) 5 sevm.caller.toB256 + 3 + 3 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (w2 sevm b) 5 + 3 + 3 + 2 + sstoreCost sevm (w1 sevm b) 3 (domainSeparator sevm.benvStat.chainId.toB256 sevm.currentTarget) + 3 + 60 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 48 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 24 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 2 + 1 + 10 + 3 + 3 + 3 + 2 + sstoreCost sevm b 12 1 + 3 + 3 + 12 + 3 + 3ID`. -/
private theorem rx_chainid (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (sevm.benvStat.chainId.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .chainid) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

/-- `ADDRESS`. -/
private theorem rx_address (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (sevm.currentTarget.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .address) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

end Steps

/-- The EIP-712 domain separator the constructor stores, over the chain-id word and the new
address: `keccak(typeHash ‖ keccak("Uniswap V2") ‖ keccak("1") ‖ chainId ‖ address)`. -/
def domainSeparator (chainWord : B256) (self : Adr) : B256 :=
  Bytes.keccak (typeHash.toBytes ++ nameHash.toBytes ++ versionHash.toBytes ++ chainWord.toBytes ++
    self.toB256.toBytes)

/-- The domain separator is the EIP-712 hash of the type string, the name, the version, the chain
id and the address, each hash computed from its literal bytes. -/
theorem domainSeparator_eip712 (chainWord : B256) (self : Adr) :
    domainSeparator chainWord self =
      Bytes.keccak ((Bytes.keccak typeString).toBytes ++ (Bytes.keccak nameBytes).toBytes ++
        (Bytes.keccak versionBytes).toBytes ++ chainWord.toBytes ++ self.toB256.toBytes) := by
  rw [typeHash_eq, nameHash_eq, versionHash_eq]
  rfl

/-- `"Uniswap V2"`, left-aligned. -/
def nameWord : B256 := 0x556e697377617020563200000000000000000000000000000000000000000000
/-- `"1"`, left-aligned. -/
def versionWord : B256 := 0x3100000000000000000000000000000000000000000000000000000000000000
/-- The low 160 bits. -/
def addressBits : B256 := 0xffffffffffffffffffffffffffffffffffffffff

/-! ## Memory of the walk -/

def m0 : Mem := Mem.empty
def m1 : Mem := m0.write 64 (0x80 : B256).toBytes
def m2 : Mem := m1.write 128 typeString
def m3 : Mem := m2.write 64 (0xc0 : B256).toBytes
def m4 : Mem := m3.write 128 (0xa : B256).toBytes
def m5 : Mem := m4.write 160 nameWord.toBytes
def m6 : Mem := m5.write 64 (0x100 : B256).toBytes
def m7 : Mem := m6.write 192 (0x1 : B256).toBytes
def m8 : Mem := m7.write 224 versionWord.toBytes
def m9 : Mem := m8.write 288 typeHash.toBytes
def m10 : Mem := m9.write 320 nameHash.toBytes
def m11 : Mem := m10.write 352 versionHash.toBytes
def m12 (c : B256) : Mem := m11.write 384 c.toBytes
def m13 (c a : B256) : Mem := (m12 c).write 416 a.toBytes
def m14 (c a : B256) : Mem := (m13 c a).write 256 (0xa0 : B256).toBytes
def m15 (c a : B256) : Mem := (m14 c a).write 64 (0x1c0 : B256).toBytes
def m16 (c a : B256) : Mem := (m15 c a).write 0 runtimeWindow

theorem runtimeWindow_length : runtimeWindow.length = 0x2c1d := ByteArray.length_sliceD _ _ _ _

theorem m0_size : m0.size = 0 := rfl
theorem m1_size : m1.size = 96 := by decide +kernel
theorem m2_size : m2.size = 224 := by decide +kernel
theorem m3_size : m3.size = 224 := by decide +kernel
theorem m4_size : m4.size = 224 := by decide +kernel
theorem m5_size : m5.size = 224 := by decide +kernel
theorem m6_size : m6.size = 224 := by decide +kernel
theorem m7_size : m7.size = 224 := by decide +kernel
theorem m8_size : m8.size = 256 := by decide +kernel
theorem m9_size : m9.size = 320 := by decide +kernel
theorem m10_size : m10.size = 352 := by decide +kernel
theorem m11_size : m11.size = 384 := by decide +kernel

theorem m12_size (c : B256) : (m12 c).size = 416 := by
  rw [m12, Mem.size_write_word_aligned (by rw [m11_size]) (by decide), m11_size]
  decide

theorem m13_size (c a : B256) : (m13 c a).size = 448 := by
  rw [m13, Mem.size_write_word_aligned (by rw [m12_size]) (by decide), m12_size]
  decide

theorem m14_size (c a : B256) : (m14 c a).size = 448 := by
  rw [m14, Mem.size_write_word_aligned (by rw [m13_size]) (by decide), m13_size]
  decide

theorem m15_size (c a : B256) : (m15 c a).size = 448 := by
  rw [m15, Mem.size_write_word_aligned (by rw [m14_size]) (by decide), m14_size]
  decide

theorem m16_size (c a : B256) : (m16 c a).size = 11296 := by
  rw [m16, Mem.size_write_of_size (m15_size c a) (by decide) runtimeWindow_length]
  decide

/-! ### Byte images of the symbolic memories -/

def img11 : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt []
    64 (0x80 : B256).toBytes) 128 typeString) 64 (0xc0 : B256).toBytes) 128 (0xa : B256).toBytes)
    160 nameWord.toBytes) 64 (0x100 : B256).toBytes) 192 (0x1 : B256).toBytes) 224
    versionWord.toBytes) 288 typeHash.toBytes) 320 nameHash.toBytes) 352 versionHash.toBytes

def img13 (c a : B256) : Bytes := Bytes.writeAt (Bytes.writeAt img11 384 c.toBytes) 416 a.toBytes
def img15 (c a : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (img13 c a) 256 (0xa0 : B256).toBytes) 64 (0x1c0 : B256).toBytes

theorem m11_reads : Mem.Wf m11 ∧ Mem.Reads m11 img11 := by
  have w0 : Mem.Wf m0 := Mem.wf_empty
  have r0 : Mem.Reads m0 [] := Mem.reads_empty
  refine ⟨?_, ?_⟩ <;>
  · have w1 := w0.write 64 (0x80 : B256).toBytes
    have r1 := r0.write w0 64 (0x80 : B256).toBytes
    have w2 := w1.write 128 typeString
    have r2 := r1.write w1 128 typeString
    have w3 := w2.write 64 (0xc0 : B256).toBytes
    have r3 := r2.write w2 64 (0xc0 : B256).toBytes
    have w4 := w3.write 128 (0xa : B256).toBytes
    have r4 := r3.write w3 128 (0xa : B256).toBytes
    have w5 := w4.write 160 nameWord.toBytes
    have r5 := r4.write w4 160 nameWord.toBytes
    have w6 := w5.write 64 (0x100 : B256).toBytes
    have r6 := r5.write w5 64 (0x100 : B256).toBytes
    have w7 := w6.write 192 (0x1 : B256).toBytes
    have r7 := r6.write w6 192 (0x1 : B256).toBytes
    have w8 := w7.write 224 versionWord.toBytes
    have r8 := r7.write w7 224 versionWord.toBytes
    have w9 := w8.write 288 typeHash.toBytes
    have r9 := r8.write w8 288 typeHash.toBytes
    have w10 := w9.write 320 nameHash.toBytes
    have r10 := r9.write w9 320 nameHash.toBytes
    first
    | exact w10.write 352 versionHash.toBytes
    | exact r10.write w10 352 versionHash.toBytes

theorem m15_reads (c a : B256) : Mem.Wf (m15 c a) ∧ Mem.Reads (m15 c a) (img15 c a) := by
  obtain ⟨w11, r11⟩ := m11_reads
  have w12 := w11.write 384 c.toBytes
  have r12 := r11.write w11 384 c.toBytes
  have w13 := w12.write 416 a.toBytes
  have r13 := r12.write w12 416 a.toBytes
  have w14 := w13.write 256 (0xa0 : B256).toBytes
  have r14 := r13.write w13 256 (0xa0 : B256).toBytes
  exact ⟨w14.write 64 (0x1c0 : B256).toBytes, r14.write w14 64 (0x1c0 : B256).toBytes⟩

theorem m13_reads (c a : B256) : Mem.Reads (m13 c a) (img13 c a) := by
  obtain ⟨w11, r11⟩ := m11_reads
  have w12 := w11.write 384 c.toBytes
  have r12 := r11.write w11 384 c.toBytes
  exact r12.write w12 416 a.toBytes

theorem img11_length : img11.length = 384 := by decide +kernel

/-- The free-pointer read after the chain id and address are laid out. -/
theorem mload_40_13 (c a : B256) :
    Bytes.toB256 ((m13 c a).read (0x40 : B256).toNat 32).1 = (0x100 : B256) := by
  rw [(m13_reads c a).read, img13,
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  decide +kernel

/-- The read of the ABI length word just stored at `0x100`. -/
theorem mload_100_15 (c a : B256) :
    Bytes.toB256 ((m15 c a).read (0x100 : B256).toNat 32).1 = (0xa0 : B256) := by
  rw [(m15_reads c a).2.read, img15,
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide)]
  have h := Bytes.sliceD_writeAt (img13 c a) (0xa0 : B256).toBytes 256
  rw [B256.length_toBytes] at h
  rw [show (0x100 : B256).toNat = 256 from rfl, h, B256.toB256_toBytes]

/-- **The domain memory.**  The five words the second `KECCAK256` hashes are the type hash, the
name and version hashes, the chain-id word and the address word the walk laid out. -/
theorem domain_read (c : B256) (self : Adr) :
    ((m15 c self.toB256).read (0x120 : B256).toNat (0xa0 : B256).toNat).1 =
      typeHash.toBytes ++ nameHash.toBytes ++ versionHash.toBytes ++ c.toBytes ++
        self.toB256.toBytes := by
  rw [(m15_reads c self.toB256).2.read, img15,
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    show (0x120 : B256).toNat = 288 from rfl, show (0xa0 : B256).toNat = 96 + 32 + 32 from rfl,
    List.sliceD_split, List.sliceD_split, img13,
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  have hc := Bytes.sliceD_writeAt img11 c.toBytes 384
  have ha := Bytes.sliceD_writeAt (Bytes.writeAt img11 384 c.toBytes) self.toB256.toBytes 416
  rw [B256.length_toBytes] at hc ha
  rw [show 288 + 96 = 384 from rfl, show 384 + 32 = 416 from rfl, ha,
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), hc]
  have hprefix : img11.sliceD 288 96 0 = typeHash.toBytes ++ nameHash.toBytes ++
      versionHash.toBytes := by decide +kernel
  rw [hprefix, List.append_assoc, List.append_assoc, List.append_assoc]

/-! ## The whole constructor -/

/-- The worlds of the walk: after `unlocked`, after the domain separator, after reading slot 5,
after the factory. -/
abbrev w1 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm b 12 1
abbrev w2 (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (w1 sevm b) 3 (domainSeparator sevm.benvStat.chainId.toB256 sevm.currentTarget)
abbrev w3 (sevm : Sevm) (b : Devm) : Devm := afterSload sevm (w2 sevm b) 5
abbrev w4 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (w3 sevm b) 5 sevm.caller.toB256

/-- The constructor's exact cost from the world `b`. -/
def ctorCost (sevm : Sevm) (b : Devm) : Nat :=
  3 + 2322 + 3 + 3 + 3 + 3 + sstoreCost sevm (w3 sevm b) 5 sevm.caller.toB256 + 3 + 3 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (w2 sevm b) 5 + 3 + 3 + 2 + sstoreCost sevm (w1 sevm b) 3 (domainSeparator sevm.benvStat.chainId.toB256 sevm.currentTarget) + 3 + 60 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 48 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 24 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 2 + 1 + 10 + 3 + 3 + 3 + 2 + sstoreCost sevm b 12 1 + 3 + 3 + 12 + 3 + 3

/-- The constructor's storage: `unlocked = 1`, the domain separator over the frame's chain id and
address, and the caller as factory. -/
def ctorStor (chainWord : B256) (self caller : Adr) (s : Stor) : Stor :=
  ((s.set 12 1).set 3 (domainSeparator chainWord self)).set 5 caller.toB256

/-- **The Pair constructor, gas-exact**: from a fresh account (empty storage, zero call value)
with an empty stack and memory and `G + ctorCost` gas, the lifted constructor halts with `G`
gas left, returning the runtime window, with the world's error unchanged and the constructor
storage written. -/
theorem ctor_run {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hcode : sevm.code = code) (hvalue : sevm.value = 0)
    {b : Devm} (hstor : ∀ x, (Devm.getStor b sevm.currentTarget).get x = 0) (G : Nat) :
    ∃ post, SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorCost sevm b)) post ∧
      post.output = runtimeWindow ∧ post.error = b.error ∧
      Devm.getStor post sevm.currentTarget =
        ctorStor sevm.benvStat.chainId.toB256 sevm.currentTarget sevm.caller
          (Devm.getStor b sevm.currentTarget) ∧
      post.gasLeft = G := by
  have hold5 : (w2 sevm b).getStorVal sevm.currentTarget 5 = 0 := by
    show (Devm.getStor (w2 sevm b) sevm.currentTarget).get 5 = 0
    rw [w2, w1, afterSstore_getStor_self, afterSstore_getStor_self, Stor.get_set_ite,
      ite_eq_right (by decide), Stor.get_set_ite, ite_eq_right (by decide)]
    exact hstor 5
  have hout : ((m16 sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256).read
      (0 : B256).toNat (0x2c1d : B256).toNat).1 = runtimeWindow := by
    obtain ⟨w15, r15⟩ := m15_reads sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256
    rw [m16, (r15.write w15 0 runtimeWindow).read]
    have h := Bytes.sliceD_writeAt
      (img15 sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256) runtimeWindow 0
    rw [runtimeWindow_length] at h
    exact h
  refine ⟨returnPost (St (w4 sevm b) [0, 0x2c1d]
      (m16 sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256) G) 0 0x2c1d [],
    ⟨t_0000_c0, rfl, ?_⟩, ?_⟩
  swap
  · obtain ⟨p1, p2, p3, p4⟩ := returnPost_facts (St (w4 sevm b) [0, 0x2c1d]
      (m16 sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256) G) 0 0x2c1d []
    refine ⟨?_, ?_, ?_, p4⟩
    · rw [p1, St.memory]
      exact hout
    · rw [p2, St_error]
      simp only [w4, w3, w2, w1, afterSstore_error, afterSload_error]
    · rw [p3, St_getStor]
      simp only [w4, w3, w2, w1, afterSstore_getStor_self, afterSload_getStor, ctorStor]
  rw [show G + ctorCost sevm b = G + 3 + 2322 + 3 + 3 + 3 + 3 + sstoreCost sevm (w3 sevm b) 5 sevm.caller.toB256 + 3 + 3 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (w2 sevm b) 5 + 3 + 3 + 2 + sstoreCost sevm (w1 sevm b) 3 (domainSeparator sevm.benvStat.chainId.toB256 sevm.currentTarget) + 3 + 60 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 48 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 24 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 2 + 1 + 10 + 3 + 3 + 3 + 2 + sstoreCost sevm b 12 1 + 3 + 3 + 12 + 3 + 3 by unfold ctorCost; omega]
  unfold t_0000_c0
  refine rx_push (w := (0x80 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 12) (M' := m1) ?_ rfl ?_
  · rw [St.extCost_eq (show Mem.empty.size = 0 from rfl)]; decide
  refine rx_push (w := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xc : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sstore hfork (by unfold gCallStipend; omega) hstatic ?_
  refine rx_callvalue (Nat.le_of_ble_eq_true rfl) ?_
  rw [hvalue]
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_iszero (v := 1) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x15 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0015_c0
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x80 : B256)) (charge_covered m1_size (by decide) (by decide)) (by decide +kernel) (read_covered m1_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_chainid (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x80 : B256), sevm.benvStat.chainId.toB256]) rfl ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x52 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x2d22 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_codecopy (c := 24) (M' := m2) ?_ ?_ ?_
  · rw [St.extCost_eq m1_size]; decide
  · rw [hcode]
    show m1.write 128 (code.sliceD 0x2d22 0x52 (Linst.toUInt8 .stop)) = _
    rw [typeWindow_eq]
    rfl
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x80 : B256)) (charge_covered m2_size (by decide) (by decide)) (by decide +kernel) (read_covered m2_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 1) (S' := [(0x80 : B256), (0x40 : B256), (0x80 : B256), (0x80 : B256), sevm.benvStat.chainId.toB256]) rfl ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x80 : B256), (0x80 : B256), (0x40 : B256), (0x80 : B256), (0x80 : B256), sevm.benvStat.chainId.toB256]) rfl ?_
  refine rx_sub' (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x52 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x52 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_keccak (c := 48) (v := typeHash) ?_ ?_ ?_ (Nat.le_of_ble_eq_true rfl) ?_
  · rw [St.extCost_eq m2_size]; decide
  · rw [← typeHash_eq]
    exact congrArg Bytes.keccak (by decide +kernel)
  · exact read_covered_len m2_size (by decide) (by decide)
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0xc0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := m3) ?_ rfl ?_
  · rw [St.extCost_eq m2_size]; decide
  refine rx_push (w := (0xa : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := m4) ?_ rfl ?_
  · rw [St.extCost_eq m3_size]; decide
  refine rx_push (w := (0x2ab734b9bbb0b8102b19 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xb1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_shl (v := nameWord) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 3) (S' := [(0x80 : B256), nameWord, typeHash, (0x40 : B256), (0x20 : B256), (0x80 : B256), sevm.benvStat.chainId.toB256]) rfl ?_
  refine rx_dup (n := 4) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0xa0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := m5) ?_ rfl ?_
  · rw [St.extCost_eq m4_size]; decide
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0xc0 : B256)) (charge_covered m5_size (by decide) (by decide)) (by decide +kernel) (read_covered m5_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x100 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := m6) ?_ rfl ?_
  · rw [St.extCost_eq m5_size]; decide
  refine rx_push (w := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := m7) ?_ rfl ?_
  · rw [St.extCost_eq m6_size]; decide
  refine rx_push (w := (0x31 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xf8 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_shl (v := versionWord) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0xc0 : B256), versionWord, typeHash, (0x40 : B256), (0x20 : B256), (0x80 : B256), sevm.benvStat.chainId.toB256]) rfl ?_
  refine rx_dup (n := 4) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0xe0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 6) (M' := m8) ?_ rfl ?_
  · rw [St.extCost_eq m7_size]; decide
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x100 : B256)) (charge_covered m8_size (by decide) (by decide)) (by decide +kernel) (read_covered m8_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 4) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x120 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 1) (S' := [typeHash, (0x100 : B256), (0x120 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), sevm.benvStat.chainId.toB256]) rfl ?_
  refine rx_swap (n := 0) (S' := [(0x100 : B256), typeHash, (0x120 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), sevm.benvStat.chainId.toB256]) rfl ?_
  refine rx_swap (n := 1) (S' := [(0x120 : B256), typeHash, (0x100 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), sevm.benvStat.chainId.toB256]) rfl ?_
  refine rx_mstore (c := 9) (M' := m9) ?_ rfl ?_
  · rw [St.extCost_eq m8_size]; decide
  refine rx_push (w := nameHash) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x140 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 6) (M' := m10) ?_ rfl ?_
  · rw [St.extCost_eq m9_size]; decide
  refine rx_push (w := versionHash) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x60 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x160 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 6) (M' := m11) ?_ rfl ?_
  · rw [St.extCost_eq m10_size]; decide
  refine rx_push (w := (0x80 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x180 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 4) (S' := [sevm.benvStat.chainId.toB256, (0x100 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), (0x180 : B256)]) rfl ?_
  refine rx_swap (n := 0) (S' := [(0x100 : B256), sevm.benvStat.chainId.toB256, (0x40 : B256), (0x20 : B256), (0x80 : B256), (0x180 : B256)]) rfl ?_
  refine rx_swap (n := 4) (S' := [(0x180 : B256), sevm.benvStat.chainId.toB256, (0x40 : B256), (0x20 : B256), (0x80 : B256), (0x100 : B256)]) rfl ?_
  refine rx_mstore (c := 6) (M' := (m12 sevm.benvStat.chainId.toB256)) ?_ rfl ?_
  · rw [St.extCost_eq m11_size]; decide
  refine rx_address (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xa0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 6) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x1a0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 1) (S' := [sevm.currentTarget.toB256, (0xa0 : B256), (0x1a0 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), (0x100 : B256)]) rfl ?_
  refine rx_swap (n := 0) (S' := [(0xa0 : B256), sevm.currentTarget.toB256, (0x1a0 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), (0x100 : B256)]) rfl ?_
  refine rx_swap (n := 1) (S' := [(0x1a0 : B256), sevm.currentTarget.toB256, (0xa0 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), (0x100 : B256)]) rfl ?_
  refine rx_mstore (c := 6) (M' := (m13 sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256)) ?_ rfl ?_
  · rw [St.extCost_eq (m12_size sevm.benvStat.chainId.toB256)]; decide
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x100 : B256)) (charge_covered (m13_size sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256) (by decide) (by decide)) (mload_40_13 sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256) (read_covered (m13_size sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256) (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 6) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sub' (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x100 : B256), (0x0 : B256), (0xa0 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), (0x100 : B256)]) rfl ?_
  refine rx_swap (n := 1) (S' := [(0xa0 : B256), (0x0 : B256), (0x100 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), (0x100 : B256)]) rfl ?_
  refine rx_add' (v := (0xa0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := (m14 sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256)) ?_ rfl ?_
  · rw [St.extCost_eq (m13_size sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256)]; decide
  refine rx_push (w := (0xc0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x100 : B256), (0xc0 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), (0x100 : B256)]) rfl ?_
  refine rx_swap (n := 4) (S' := [(0x100 : B256), (0xc0 : B256), (0x40 : B256), (0x20 : B256), (0x80 : B256), (0x100 : B256)]) rfl ?_
  refine rx_add' (v := (0x1c0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x40 : B256), (0x1c0 : B256), (0x20 : B256), (0x80 : B256), (0x100 : B256)]) rfl ?_
  refine rx_mstore (c := 3) (M' := (m15 sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256)) ?_ rfl ?_
  · rw [St.extCost_eq (m14_size sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256)]; decide
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0xa0 : B256)) (charge_covered (m15_size sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256) (by decide) (by decide)) (mload_100_15 sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256) (read_covered (m15_size sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256) (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 2) (S' := [(0x100 : B256), (0x20 : B256), (0x80 : B256), (0xa0 : B256)]) rfl ?_
  refine rx_add' (v := (0x120 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 1) (S' := [(0xa0 : B256), (0x80 : B256), (0x120 : B256)]) rfl ?_
  refine rx_swap (n := 0) (S' := [(0x80 : B256), (0xa0 : B256), (0x120 : B256)]) rfl ?_
  refine rx_swap (n := 1) (S' := [(0x120 : B256), (0xa0 : B256), (0x80 : B256)]) rfl ?_
  refine rx_keccak (c := 60) (v := (domainSeparator sevm.benvStat.chainId.toB256 sevm.currentTarget)) ?_ ?_ ?_ (Nat.le_of_ble_eq_true rfl) ?_
  · rw [St.extCost_eq (m15_size sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256)]; decide
  · exact congrArg Bytes.keccak (domain_read sevm.benvStat.chainId.toB256 sevm.currentTarget)
  · exact read_covered_len (m15_size sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256) (by decide) (by decide)
  refine rx_push (w := (0x3 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sstore hfork (by unfold gCallStipend; omega) hstatic ?_
  refine rx_pop ?_
  refine rx_push (w := (0x5 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sload_sel hfork (Nat.le_of_ble_eq_true rfl) ?_
  rw [hold5]
  refine rx_push (w := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xa0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_shl (v := (0x10000000000000000000000000000000000000000 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sub' (v := addressBits) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_not (v := (~~~ addressBits)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := 0) (b256_and_zero _) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_caller (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_or (v := sevm.caller.toB256) (b256_or_zero _) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x5 : B256), sevm.caller.toB256]) rfl ?_
  refine rx_sstore hfork (by unfold gCallStipend; omega) hstatic ?_
  refine rx_push (w := (0x2c1d : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x105 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_codecopy (c := 2322) (M' := (m16 sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256)) ?_ ?_ ?_
  · rw [St.extCost_eq (m15_size sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256)]; decide
  · rw [hcode]
    rfl
  refine rx_push (w := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  exact rx_return_any (S := []) rfl (by rw [St.extCost_eq (m16_size sevm.benvStat.chainId.toB256 sevm.currentTarget.toB256)]; decide)

end Blanc.Lift.UniswapV2Pair.Creation
