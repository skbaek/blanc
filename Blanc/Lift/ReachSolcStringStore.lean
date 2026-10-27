import Blanc.Lift.ReachSstoreLoops
import Blanc.Lift.SolcAbiStringStaging

/-!
# solc 0.6 `string storage = string calldata` on a prefix reach

The storage-string assignment helper solc 0.6 emits for a `string calldata` source, as a
shape over its jump tags and table indices (`StrTags`), so one proof serves every
compilation that contains it. The helper (entry stack `len :: p :: slot :: …`: the string
length, its calldata data pointer and the storage slot) stores the header at `slot`, then
either the short string at `slot` or the payload words at `keccak(slot) + j` (the copy loop
`ReachPayload.headJ` over `CALLDATALOAD`), and clears the old tail with the compact clearing
loop (`SolcStorageClear.head`).

`StrStoreCd.reach`: a reach into the helper from an empty continuation stack stops at an
`SSTORE` that writes `slot`, writes zero, or writes `keccak(slot) + j` for
`j < (len + 31) / 32`; the calldata bound `p + len + 32 ≤ 2 ^ 256` is the only premise.

Contract-neutral.
-/

namespace Blanc.Lift

open Jaune Blanc

theorem len2 (a b : UInt8) : [a, b].length ≤ 32 := Nat.le_add_left 2 30

/-- A two-byte `PUSH` of a jump tag. -/
def tagPush (t : UInt8 × UInt8) : Ninst := .push [t.1, t.2] (len2 _ _)

/-- The tags and table indices of one compilation of the helper. -/
structure StrTags : Type where
  long : UInt8 × UInt8
  exit : UInt8 × UInt8
  back : UInt8 × UInt8
  ret : UInt8 × UInt8
  clr : UInt8 × UInt8
  clrBack : UInt8 × UInt8
  kExit : Nat
  kLoop : Nat
  kClr : Nat
  kClrLoop : Nat

/-- solc's scratch hash of one word: `mstore(0, w); keccak256(0, 32)` reads `w` back. -/
theorem scratch_word (M : Mem) (w : B256) :
    ((M.write (Bytes.toB256 [0]).toNat w.toBytes).read (Bytes.toB256 [0]).toNat
      (Bytes.toB256 [32]).toNat).1 = w.toBytes :=
  Mem.read_write_zero M (ys := w.toBytes) (List.ne_nil_of_length_pos (by rw [B256.length_toBytes]; decide))

namespace StrStore

variable (τ : StrTags)

/-- The copy loop head of the helper (inline and at entry `kLoop`), reading with `rd`. -/
def loopHead (rd : Ninst) : SFunc :=
  ReachPayload.headJ rd [τ.back.1, τ.back.2] [τ.exit.1, τ.exit.2]
    (len2 _ _) (len2 _ _) τ.kLoop τ.kExit

/-- The clearing loop head (entry `kClrLoop`). -/
def clrHead : SFunc :=
  SolcStorageClear.head [τ.clrBack.1, τ.clrBack.2] [τ.ret.1, τ.ret.2] (len2 _ _) (len2 _ _)
    τ.kClrLoop

/-- The shared exit (entry `kExit`): drop, call the clearing loop, return. -/
def exitTree : SFunc :=
  .dest (.next (.reg .pop) (.next (tagPush τ.ret) (.next (.reg (.swap 2)) (.next (.reg (.swap 1))
    (.next (.reg .pop) (.next (tagPush τ.clr) (.callNext τ.kClr
      (.dest (.next (.reg .pop) (.next (.reg (.swap 0)) .ret))))))))))

/-- The short-string arm of a `string calldata` source. -/
def shortCd : SFunc :=
  .next (.reg (.dup 2)) (.next (.reg (.dup 0)) (.next (.reg .add) (.next (.push [0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00] (by decide))
    (.next (.reg (.dup 2)) (.next (.reg .calldataload) (.next (.reg .and) (.next (.reg .or)
    (.next (.reg (.dup 5)) (.next (.reg .sstore) (.next (tagPush τ.exit) (.jump τ.kExit)))))))))))

/-- The short-string arm of a `string memory` source. -/
def shortMem : SFunc :=
  .next (.reg (.dup 0)) (.next (.reg .mload) (.next (.push [0xff] (by decide)) (.next (.reg .not)
    (.next (.reg .and) (.next (.reg (.dup 3)) (.next (.reg (.dup 0)) (.next (.reg .add)
    (.next (.reg .or) (.next (.reg (.dup 5)) (.next (.reg .sstore) (.next (tagPush τ.exit)
    (.jump τ.kExit))))))))))))

/-- The long-string arm: header, empty test, then the copy loop. -/
def longArm (rd : Ninst) : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.reg (.dup 0)) (.next (.reg .add) (.next (.push [0x01]
    (by decide)) (.next (.reg .add) (.next (.reg (.dup 5)) (.next (.reg .sstore)
    (.next (.reg (.dup 2)) (.next (.reg .iszero) (.next (tagPush τ.exit)
    (.branchTo (.next (.reg (.swap 1)) (.next (.reg (.dup 2)) (.next (.reg .add) (loopHead τ rd))))
      τ.kExit)))))))))))

/-- The helper over its copy loop's read `rd` and its short arm `sa`. -/
def helper (rd : Ninst) (sa : SFunc) : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.reg (.dup 0)) (.next (.reg .sload) (.next (.push [0x01]
    (by decide)) (.next (.reg (.dup 1)) (.next (.push [0x01] (by decide)) (.next (.reg .and)
    (.next (.reg .iszero) (.next (.push [0x01, 0x00] (by decide)) (.next (.reg .mul)
    (.next (.reg .sub) (.next (.reg .and) (.next (.push [0x02] (by decide)) (.next (.reg (.swap 0))
    (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.push [0x00] (by decide))
    (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.push [0x00] (by decide))
    (.next (.reg .keccak256) (.next (.reg (.swap 0)) (.next (.push [0x1f] (by decide))
    (.next (.reg .add) (.next (.push [0x20] (by decide)) (.next (.reg (.swap 0)) (.next (.reg .div)
    (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.swap 2)) (.next (.reg (.dup 2))
    (.next (.push [0x1f] (by decide)) (.next (.reg .lt) (.next (tagPush τ.long)
    (.branch sa (longArm τ rd))))))))))))))))))))))))))))))))))))

/-- The table entries the helper reaches. -/
structure Entries (rd : Ninst) (fs : List SFunc) : Prop where
  exit : fs[τ.kExit]? = some (exitTree τ)
  loop : fs[τ.kLoop]? = some (loopHead τ rd)
  clr : fs[τ.kClr]? = some (.dest (clrHead τ))
  clrLoop : fs[τ.kClrLoop]? = some (clrHead τ)

/-- What a store of the helper writes: the slot, zero, or a payload word below `n`. -/
def StoreAt (slot : B256) (n : Nat) (T : Conf) : Prop :=
  ∃ key v S, T.d.stack = key :: v :: S ∧
    (key = slot ∨ v = 0 ∨ ∃ j : Nat, j < n ∧ key = slot.toBytes.keccak + j.toB256)

theorem StoreAt.mono {slot : B256} {n m : Nat} {T : Conf} (h : n ≤ m) (s : StoreAt slot n T) :
    StoreAt slot m T := by
  obtain ⟨key, v, S, hs, hk | hv | ⟨j, hj, hk⟩⟩ := s
  · exact ⟨key, v, S, hs, .inl hk⟩
  · exact ⟨key, v, S, hs, .inr (.inl hv)⟩
  · exact ⟨key, v, S, hs, .inr (.inr ⟨j, by omega, hk⟩)⟩

/-- The exact old-tail endpoint computed from the stored string header. -/
def oldEnd (slot old : B256) : B256 :=
  slot.toBytes.keccak + (Bytes.toB256 [31] +
    (Bytes.toB256 [1, 0] * ((Bytes.toB256 [1] &&& old) =? 0) -
      Bytes.toB256 [1] &&& old) / Bytes.toB256 [2]) / Bytes.toB256 [32]

/-- A clearing key lies after an actual copy-prefix endpoint and below an old
header's endpoint. No well-formedness assumption is made about that old header. -/
def ClearRange (slot : B256) (n : Nat) (key : B256) : Prop :=
  ∃ old i, i ≤ n ∧ (slot.toBytes.keccak + i.toB256).toNat ≤ key.toNat ∧
    key.toNat < (oldEnd slot old).toNat

/-- The helper's stores with the zero-clearing range retained. -/
def StoreRangeAt (slot : B256) (n : Nat) (T : Conf) : Prop :=
  ∃ key v S, T.d.stack = key :: v :: S ∧
    (key = slot ∨ (∃ j : Nat, j < n ∧ key = slot.toBytes.keccak + j.toB256) ∨
      v = 0 ∧ ClearRange slot n key)

theorem StoreRangeAt.mono {slot : B256} {n m : Nat} {T : Conf}
    (h : n ≤ m) (s : StoreRangeAt slot n T) : StoreRangeAt slot m T := by
  obtain ⟨key, v, S, stack, fixed | ⟨j, bound, payload⟩ | ⟨zero, old, i, bound, lo, hi⟩⟩ := s
  · exact ⟨key, v, S, stack, .inl fixed⟩
  · exact ⟨key, v, S, stack, .inr (.inl ⟨j, by omega, payload⟩)⟩
  · exact ⟨key, v, S, stack, .inr (.inr ⟨zero, old, i, by omega, lo, hi⟩)⟩

theorem StoreRangeAt.storeAt {slot : B256} {n : Nat} {T : Conf}
    (s : StoreRangeAt slot n T) : StoreAt slot n T := by
  obtain ⟨key, v, S, stack, fixed | payload | ⟨zero, -⟩⟩ := s
  · exact ⟨key, v, S, stack, .inl fixed⟩
  · exact ⟨key, v, S, stack, .inr (.inr payload)⟩
  · exact ⟨key, v, S, stack, .inr (.inl zero)⟩

/-- The copy loop's iteration count is at most the string's word count. -/
theorem count_le (p len : Nat) :
    SolcStoragePayload.count (p + len).toB256 p ≤ (len + 31) / 32 := by
  unfold SolcStoragePayload.count
  have h : ((p + len).toB256).toNat ≤ p + len := by
    rw [B256.toNat_toB256]
    exact Nat.mod_le _ _
  exact Nat.div_le_div_right (by omega)

variable {τ} {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {T : Conf}

/-- The shared exit retains the exact clearing start and end from its stack. -/
theorem exit_reach_range (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {rd : Ninst}
    (E : Entries τ rd fs)
    {K : List SFunc} {b : Devm} {x y z w s0 s1 : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach P fs sevm ⟨St b (x :: y :: z :: w :: s0 :: s1 :: S) M G, exitTree τ, K⟩ T)
    (hT : AtSstore T) :
    (∃ key rest, T.d.stack = key :: 0 :: rest ∧
      y.toNat ≤ key.toNat ∧ key.toNat < w.toNat) ∨ ∃ f K' b' G', K = f :: K' ∧
      Reach P fs sevm ⟨St b' (s0 :: S) M G', f, K'⟩ T := by
  unfold exitTree at run
  rsd
  iterate 6 rsx
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  rw [E.clr] at hg
  cases hg
  rsd
  rcases ReachClear.clear_reach_range erase E.clrLoop rfl run hT with h | ⟨f, K', b', G', hK, run⟩
  · exact .inl h
  cases hK
  rsd
  iterate 2 rsx
  exact .inr (rs_retM run hT)

theorem exit_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {rd : Ninst}
    (E : Entries τ rd fs)
    {K : List SFunc} {b : Devm} {x y z w s0 s1 : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach P fs sevm ⟨St b (x :: y :: z :: w :: s0 :: s1 :: S) M G, exitTree τ, K⟩ T)
    (hT : AtSstore T) :
    ReachClear.ZeroAt T ∨ ∃ f K' b' G', K = f :: K' ∧
      Reach P fs sevm ⟨St b' (s0 :: S) M G', f, K'⟩ T := by
  rcases exit_reach_range erase E run hT with
    ⟨key, rest, stack, -, -⟩ | returned
  · exact .inl ⟨key, rest, stack⟩
  · exact .inr returned

theorem toB256_add (a b : Nat) : a.toB256 + b.toB256 = (a + b).toB256 := by
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_toB256, B256.toNat_toB256, B256.toNat_toB256]
  exact (Nat.add_mod _ _ _).symm

/-- What a short arm owes: on the arm's entry stack, it stores at the slot (its fifth word) and
leaves for the shared exit with the same stack under kept memory. -/
def ShortOK (P : Sevm → Devm → Ninst → Devm → Prop) (fs : List SFunc) (sevm : Sevm)
    (τ : StrTags) (sa : SFunc) : Prop :=
  ∀ {K : List SFunc} {b : Devm} {x y z w s0 r : B256} {S : List B256} {M : Mem} {G : Nat}
    {T : Conf}, Reach P fs sevm ⟨St b (x :: y :: z :: w :: s0 :: r :: S) M G, sa, K⟩ T →
    AtSstore T → (∃ v S', T.d.stack = s0 :: v :: S') ∨
      ∃ b' M' G', SolcStorageReturn.Keeps M M' ∧
        Reach P fs sevm ⟨St b' (x :: y :: z :: w :: s0 :: r :: S) M' G', exitTree τ, K⟩ T

theorem shortCd_ok (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hexit : fs[τ.kExit]? = some (exitTree τ)) : ShortOK P fs sevm τ (shortCd τ) := by
  intro K b x y z w s0 r S M G T run hT
  unfold shortCd at run
  iterate 9 rsx
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact .inl ⟨_, _, rfl⟩
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  rsx
  obtain ⟨g, _, hg, run⟩ := rs_jump run hT
  rw [hexit] at hg
  cases hg
  exact .inr ⟨_, _, _, SolcStorageReturn.Keeps.refl _, run⟩

theorem shortMem_ok (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hexit : fs[τ.kExit]? = some (exitTree τ)) : ShortOK P fs sevm τ (shortMem τ) := by
  intro K b x y z w s0 r S M G T run hT
  unfold shortMem at run
  iterate 10 rsx
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact .inl ⟨_, _, rfl⟩
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  rsx
  obtain ⟨g, _, hg, run⟩ := rs_jump run hT
  rw [hexit] at hg
  cases hg
  exact .inr ⟨_, _, _, SolcStorageReturn.Keeps.read _ _ _, run⟩

/-- **The helper on a reach to an `SSTORE`.** Entered with `len :: p :: slot :: r :: S` (the
string length, its data pointer and the slot), the reach stops at a store of the slot, of
a payload word `keccak(slot) + j` below the copy count, or zero within `ClearRange`;
or the helper returns `slot :: S` into the pending continuation, with every byte of the entry
memory but the scratch word at `0` kept. `rdStep` and `win` are the copy loop's read laws. -/
theorem reach_range (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {rd : Ninst}
    (hrd : rd ≠ .reg .sstore)
    (rdStep : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d →
        ∃ v b' M' G', d = St b' (v :: S) M' G' ∧ SolcStorageReturn.Keeps M M')
    {sa : SFunc} (hsa : ShortOK P fs sevm τ sa) (E : Entries τ rd fs)
    {K : List SFunc} {b : Devm} {r : B256} {S : List B256} {M : Mem} {G : Nat} {len p : Nat}
    {slot : B256} (hp : p < 2 ^ 256)
    (win : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d → c.toNat < ((p + len).toB256).toNat →
        c.toNat + 32 < 2 ^ 256)
    (run : Reach P fs sevm ⟨St b (len.toB256 :: p.toB256 :: slot :: r :: S) M G,
      helper τ rd sa, K⟩ T)
    (hT : AtSstore T) :
    StoreRangeAt slot (SolcStoragePayload.count (p + len).toB256 p) T ∨ ∃ f K' b' M' G',
      K = f :: K' ∧ SolcStorageReturn.Keeps (M.write 0 slot.toBytes) M' ∧
      Reach P fs sevm ⟨St b' (slot :: S) M' G', f, K'⟩ T := by
  unfold helper at run
  rsd
  iterate 2 rsx
  rsld
  iterate 18 rsx
  rw [scratch_word M slot] at run
  have k0 : SolcStorageReturn.Keeps (M.write 0 slot.toBytes)
      ((M.write (Bytes.toB256 [0]).toNat slot.toBytes).read (Bytes.toB256 [0]).toNat
        (Bytes.toB256 [32]).toNat).2 := SolcStorageReturn.Keeps.read _ _ _
  generalize ((M.write (Bytes.toB256 [0]).toNat slot.toBytes).read (Bytes.toB256 [0]).toNat
    (Bytes.toB256 [32]).toNat).2 = M1 at run k0
  iterate 13 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · rcases hsa run hT with ⟨v, S', hk⟩ | ⟨b', M', G', hk, run⟩
    · exact .inl ⟨_, _, _, hk, .inl rfl⟩
    · rcases exit_reach_range erase E run hT with ⟨x, S', h, lower, upper⟩ | ⟨f, K', b'', G'', hK, run⟩
      · refine .inl ⟨_, _, _, h, .inr (.inr ⟨rfl, _, 0, Nat.zero_le _, ?_, upper⟩)⟩
        simpa only [show (0 : Nat).toB256 = 0 from rfl, B256.add_zero] using lower
      · exact .inr ⟨f, K', b'', _, G'', hK, k0.trans hk, run⟩
  · unfold longArm at run
    rsd
    iterate 6 rsx
    rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
    · exact .inl ⟨_, _, _, rfl, .inl rfl⟩
    obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
    subst e
    clear hstep
    iterate 3 rsx
    rcases rs_branchTo run hT with ⟨hz, _, run⟩ | ⟨_, g, _, hg, run⟩
    · iterate 3 rsx
      rw [toB256_add] at run
      rcases ReachPayload.payloadJ_reach_exact erase hrd rdStep win E.loop (i := 0)
          (fin := (p + len).toB256) (base0 := slot.toBytes.keccak) (p := p)
          (by
            refine ⟨Nat.zero_le _, by omega, ?_⟩
            rw [St.stack, Nat.mul_zero, Nat.add_zero, show ((0 : Nat).toB256) = 0 from rfl,
              B256.add_zero])
          run hT with ⟨j, v, S', hj, h⟩ | ⟨i, g, b', M', G', countEq, hg, hk, run⟩
      · exact .inl ⟨_, _, _, h, .inr (.inl ⟨j, hj, rfl⟩)⟩
      · rw [E.exit] at hg
        cases hg
        rcases exit_reach_range erase E run hT with ⟨x, S', h, lower, upper⟩ | ⟨f, K', b'', G'', hK, run⟩
        · exact .inl ⟨_, _, _, h, .inr (.inr ⟨rfl, _, i, countEq.le, lower, upper⟩)⟩
        · exact .inr ⟨f, K', b'', _, G'', hK, k0.trans hk, run⟩
    · rw [E.exit] at hg
      cases hg
      rcases exit_reach_range erase E run hT with ⟨x, S', h, lower, upper⟩ | ⟨f, K', b'', G'', hK, run⟩
      · refine .inl ⟨_, _, _, h, .inr (.inr ⟨rfl, _, 0, Nat.zero_le _, ?_, upper⟩)⟩
        simpa only [show (0 : Nat).toB256 = 0 from rfl, B256.add_zero] using lower
      · exact .inr ⟨f, K', b'', _, G'', hK, k0, run⟩

theorem reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {rd : Ninst}
    (hrd : rd ≠ .reg .sstore)
    (rdStep : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d →
        ∃ v b' M' G', d = St b' (v :: S) M' G' ∧ SolcStorageReturn.Keeps M M')
    {sa : SFunc} (hsa : ShortOK P fs sevm τ sa) (E : Entries τ rd fs)
    {K : List SFunc} {b : Devm} {r : B256} {S : List B256} {M : Mem} {G : Nat} {len p : Nat}
    {slot : B256} (hp : p < 2 ^ 256)
    (win : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {d : Devm} {c : B256},
      P sevm (St b (c :: S) M G) rd d → c.toNat < ((p + len).toB256).toNat →
        c.toNat + 32 < 2 ^ 256)
    (run : Reach P fs sevm ⟨St b (len.toB256 :: p.toB256 :: slot :: r :: S) M G,
      helper τ rd sa, K⟩ T)
    (hT : AtSstore T) :
    StoreAt slot (SolcStoragePayload.count (p + len).toB256 p) T ∨ ∃ f K' b' M' G',
      K = f :: K' ∧ SolcStorageReturn.Keeps (M.write 0 slot.toBytes) M' ∧
      Reach P fs sevm ⟨St b' (slot :: S) M' G', f, K'⟩ T := by
  rcases reach_range erase hrd rdStep hsa E hp win run hT with stored | returned
  · exact .inl stored.storeAt
  · exact .inr returned

end StrStore

namespace StrStoreCd

/-- The `string storage = string calldata` helper. -/
abbrev helper (τ : StrTags) : SFunc := StrStore.helper τ (.reg .calldataload) (StrStore.shortCd τ)

/-- Its table entries. -/
abbrev Entries (τ : StrTags) (fs : List SFunc) : Prop := StrStore.Entries τ (.reg .calldataload) fs

/-- What a store of the helper writes: the slot, zero, or a payload word. -/
def StoreAt (slot : B256) (len : Nat) (T : Conf) : Prop :=
  ∃ key v S, T.d.stack = key :: v :: S ∧
    (key = slot ∨ v = 0 ∨ ∃ j : Nat, j < (len + 31) / 32 ∧ key = slot.toBytes.keccak + j.toB256)

variable {τ : StrTags} {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {T : Conf}

theorem reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (E : Entries τ fs)
    {K : List SFunc} {b : Devm} {r : B256} {S : List B256} {M : Mem} {G : Nat} {len p : Nat}
    {slot : B256} (bound : p + len + 32 ≤ 2 ^ 256)
    (run : Reach P fs sevm ⟨St b (len.toB256 :: p.toB256 :: slot :: r :: S) M G, helper τ, K⟩ T)
    (hT : AtSstore T) :
    StoreAt slot len T ∨ ∃ f K' b' M' G', K = f :: K' ∧
      Reach P fs sevm ⟨St b' (slot :: S) M' G', f, K'⟩ T := by
  have hfin : ((p + len).toB256).toNat = p + len := B256.toNat_toB256_of_lt (by omega)
  rcases StrStore.reach erase (by intro h; cases h) (ReachPayload.cdload_rdStep erase)
      (StrStore.shortCd_ok erase E.exit) E (by omega)
      (ReachPayload.cdload_win (by omega)) run hT with
    s | ⟨f, K', b', M', G', hK, -, run⟩
  · obtain ⟨key, v, S', hs, h⟩ := s.mono (StrStore.count_le p len)
    exact .inl ⟨key, v, S', hs, h⟩
  · exact .inr ⟨f, K', b', M', G', hK, run⟩

end StrStoreCd

/-! ## A solc 0.6 dynamic-string allocation from calldata -/

/-- A write leaves every word of the old memory that lies outside its window. -/
theorem memWord_write_far {μ : Mem} {n o : Nat} {ys : Bytes} (hsz : o + 32 ≤ μ.size)
    (h : o + 32 ≤ n ∨ n + ys.length ≤ o) : memWord (μ.write n ys) o = memWord μ o := by
  apply memWord_congr
  intro j hj
  exact (Mem.write_agree μ n ys).2 _ (by omega) (by omega)

theorem size_write_ge (μ : Mem) (n : Nat) (ys : Bytes) : μ.size ≤ (μ.write n ys).size :=
  (Mem.write_agree μ n ys).1

/-- **One solc 0.6 string allocation.** The memory after the free-pointer read and update,
the length header, the payload copy and the zero word after the payload, as the code computes
it: the header reads back, the free pointer is the next allocation's, and every word between
`96` and the allocation that the old memory held is kept. -/
theorem alloc06_facts {M : Mem} {L : B256} {ys : Bytes} (hlen : ys.length = L.toNat)
    (hp : 96 ≤ (memWord M 64).toNat) (hb : (memWord M 64).toNat + L.toNat + 128 < 2 ^ 256) :
    let fp := (M.read (Bytes.toB256 [64]).toNat 32).1.toB256
    let sz := Bytes.toB256 [32] + (Bytes.toB256 [31] + L) / Bytes.toB256 [32] * Bytes.toB256 [32]
    let M' := ((((M.read (Bytes.toB256 [64]).toNat 32).2.write (Bytes.toB256 [64]).toNat
      (fp + sz).toBytes).write fp.toNat L.toBytes).write (Bytes.toB256 [32] + fp).toNat ys).write
      (Bytes.toB256 [32] + fp + L).toNat (Bytes.toB256 [0]).toBytes
    memWord M' fp.toNat = L ∧ memWord M' 64 = fp + sz ∧
      (fp + sz).toNat = fp.toNat + 32 + ((L.toNat + 31) / 32 * 32) ∧
      fp.toNat + 32 ≤ M'.size ∧ M.size ≤ M'.size ∧
      ∀ o, 96 ≤ o → o + 32 ≤ fp.toNat → o + 32 ≤ M.size → memWord M' o = memWord M o := by
  intro fp sz M'
  have h64 : (Bytes.toB256 [64]).toNat = 64 := by decide
  have hfp : fp = memWord M 64 := by
    show (M.read (Bytes.toB256 [64]).toNat 32).1.toB256 = Bytes.toB256 (M.read 64 32).1
    rw [h64]
  rw [← hfp] at hp hb
  have h32 : (Bytes.toB256 [32] + fp).toNat = fp.toNat + 32 := by
    rw [B256.toNat_add, show (Bytes.toB256 [32]).toNat = 32 by decide, Nat.lo_eq_of_lt (by omega)]
    omega
  have h32L : (Bytes.toB256 [32] + fp + L).toNat = fp.toNat + 32 + L.toNat := by
    rw [B256.toNat_add, h32, Nat.lo_eq_of_lt (by omega)]
  have hsz : sz.toNat = 32 + ((L.toNat + 31) / 32 * 32) := by
    have e31 : (Bytes.toB256 [31] + L).toNat = 31 + L.toNat := by
      rw [B256.toNat_add, show (Bytes.toB256 [31]).toNat = 31 by decide,
        Nat.lo_eq_of_lt (by omega)]
    have ediv : ((Bytes.toB256 [31] + L) / Bytes.toB256 [32]).toNat = (31 + L.toNat) / 32 := by
      rw [B256.toNat_div (by decide), e31, show (Bytes.toB256 [32]).toNat = 32 by decide]
    have emul : ((Bytes.toB256 [31] + L) / Bytes.toB256 [32] * Bytes.toB256 [32]).toNat =
        (31 + L.toNat) / 32 * 32 := by
      rw [B256.toNat_mul, ediv, show (Bytes.toB256 [32]).toNat = 32 by decide,
        Nat.lo_eq_of_lt (by have := Nat.div_mul_le_self (31 + L.toNat) 32; omega)]
    show (Bytes.toB256 [32] + (Bytes.toB256 [31] + L) / Bytes.toB256 [32] * Bytes.toB256 [32]).toNat
      = _
    rw [B256.toNat_add, emul, show (Bytes.toB256 [32]).toNat = 32 by decide,
      Nat.lo_eq_of_lt (by have := Nat.div_mul_le_self (31 + L.toNat) 32; omega)]
    rw [Nat.add_comm L.toNat 31]
  have hnext : (fp + sz).toNat = fp.toNat + 32 + ((L.toNat + 31) / 32 * 32) := by
    have hr : ((L.toNat + 31) / 32 * 32) ≤ L.toNat + 31 := by
      have := Nat.div_mul_le_self (L.toNat + 31) 32
      omega
    rw [B256.toNat_add, hsz, Nat.lo_eq_of_lt (by omega)]
    omega
  have e : M' = ((((M.read 64 32).2.write 64 (fp + sz).toBytes).write fp.toNat L.toBytes).write
      (fp.toNat + 32) ys).write (fp.toNat + 32 + L.toNat) (Bytes.toB256 [0]).toBytes := by
    show ((((M.read (Bytes.toB256 [64]).toNat 32).2.write (Bytes.toB256 [64]).toNat
      (fp + sz).toBytes).write fp.toNat L.toBytes).write (Bytes.toB256 [32] + fp).toNat ys).write
      (Bytes.toB256 [32] + fp + L).toNat (Bytes.toB256 [0]).toBytes = _
    rw [h64, h32, h32L]
  rw [e]
  have s0 : M.size ≤ (M.read 64 32).2.size := (SolcStorageReturn.Keeps.read M _ _).2
  have m0 : ∀ o, memWord (M.read 64 32).2 o = memWord M o := fun _ => rfl
  generalize (M.read 64 32).2 = A0 at s0 m0
  have hL32 : L.toBytes.length = 32 := B256.length_toBytes L
  have hz32 : (Bytes.toB256 [0]).toBytes.length = 32 := B256.length_toBytes _
  have hv32 : (fp + sz).toBytes.length = 32 := B256.length_toBytes _
  have a1 := Mem.memWord_write_word A0 64 (fp + sz)
  have a2 := Mem.memWord_write_word (A0.write 64 (fp + sz).toBytes) fp.toNat L
  have t1 := size_write_ge A0 64 (fp + sz).toBytes
  have t2 := size_write_ge (A0.write 64 (fp + sz).toBytes) fp.toNat L.toBytes
  have t3 := size_write_ge ((A0.write 64 (fp + sz).toBytes).write fp.toNat L.toBytes)
    (fp.toNat + 32) ys
  have t4 := size_write_ge (((A0.write 64 (fp + sz).toBytes).write fp.toNat L.toBytes).write
    (fp.toNat + 32) ys) (fp.toNat + 32 + L.toNat) (Bytes.toB256 [0]).toBytes
  refine ⟨?_, ?_, hnext, by omega, by omega, ?_⟩
  · rw [memWord_write_far (by omega) (by omega), memWord_write_far (by omega) (by omega)]
    exact a2.1
  · rw [memWord_write_far (by omega) (by omega), memWord_write_far (by omega) (by omega),
      memWord_write_far (by omega) (by omega)]
    exact a1.1
  · intro o ho96 ho hoM
    rw [memWord_write_far (by omega) (by omega), memWord_write_far (by omega) (by omega),
      memWord_write_far (by omega) (by omega), memWord_write_far (by omega) (by omega)]
    exact m0 o

/-- The allocation code of one string: size, free-pointer read and update, header, payload
copy from calldata, zero word, then the spare word popped. -/
def alloc06Frag (k : SFunc) : SFunc :=
  .next (.reg (.swap 1)) <| .next (.reg (.swap 0)) <| .next (.reg (.dup 0)) <|
  .next (.reg (.dup 0)) <| .next (.push [0x1f] (by decide)) <| .next (.reg .add) <|
  .next (.push [0x20] (by decide)) <| .next (.reg (.dup 0)) <| .next (.reg (.swap 1)) <|
  .next (.reg .div) <| .next (.reg .mul) <| .next (.push [0x20] (by decide)) <|
  .next (.reg .add) <| .next (.push [0x40] (by decide)) <| .next (.reg .mload) <|
  .next (.reg (.swap 0)) <| .next (.reg (.dup 1)) <| .next (.reg .add) <|
  .next (.push [0x40] (by decide)) <| .next (.reg .mstore) <| .next (.reg (.dup 0)) <|
  .next (.reg (.swap 3)) <| .next (.reg (.swap 2)) <| .next (.reg (.swap 1)) <|
  .next (.reg (.swap 0)) <| .next (.reg (.dup 1)) <| .next (.reg (.dup 1)) <|
  .next (.reg .mstore) <| .next (.push [0x20] (by decide)) <| .next (.reg .add) <|
  .next (.reg (.dup 3)) <| .next (.reg (.dup 3)) <| .next (.reg (.dup 0)) <|
  .next (.reg (.dup 2)) <| .next (.reg (.dup 4)) <| .next (.reg .calldatacopy) <|
  .next (.push [0x00] (by decide)) <| .next (.reg (.swap 2)) <| .next (.reg .add) <|
  .next (.reg (.swap 1)) <| .next (.reg (.swap 0)) <| .next (.reg (.swap 1)) <|
  .next (.reg .mstore) <| .next (.reg .pop) k

/-- What one allocation leaves: the header at the old free pointer `fp`, the next free pointer
at `64`, the allocation's room, and every older word between `96` and `fp` kept. -/
structure Alloc06 (M M' : Mem) (fp L : B256) : Prop where
  hdr : memWord M' fp.toNat = L
  next : (memWord M' 64).toNat = fp.toNat + 32 + (L.toNat + 31) / 32 * 32
  fit : fp.toNat + 32 ≤ M'.size
  grow : M.size ≤ M'.size
  keep : ∀ o, 96 ≤ o → o + 32 ≤ fp.toNat → o + 32 ≤ M.size → memWord M' o = memWord M o

section Alloc

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {T : Conf}

/-- **One allocation on a reach to an `SSTORE`.** -/
theorem alloc06Frag_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {k : SFunc} {K : List SFunc} {b : Devm} {a L src : B256} {R : List B256} {M : Mem}
    {G : Nat} (hp : 96 ≤ (memWord M 64).toNat)
    (hb : (memWord M 64).toNat + L.toNat + 128 < 2 ^ 256)
    (run : Reach P fs sevm ⟨St b (a :: L :: src :: R) M G, alloc06Frag k, K⟩ T)
    (hT : AtSstore T) :
    ∃ M' G', Alloc06 M M' (memWord M 64) L ∧
      Reach P fs sevm ⟨St b (L :: L :: src :: memWord M 64 :: a :: R) M' G', k, K⟩ T := by
  unfold alloc06Frag at run
  iterate 44 rsx
  have hlen : (sevm.data.sliceD src.toNat L.toNat 0).length = L.toNat := List.takeD_length _ _ _
  have h := alloc06_facts (M := M) hlen hp hb
  dsimp only at h
  obtain ⟨hdr, hnx, hnext, fit, grow, keep⟩ := h
  have hfp : (M.read (Bytes.toB256 [64]).toNat 32).1.toB256 = memWord M 64 := by
    show (M.read (Bytes.toB256 [64]).toNat 32).1.toB256 = Bytes.toB256 (M.read 64 32).1
    rw [show (Bytes.toB256 [64]).toNat = 64 by decide]
  revert grow hfp
  generalize (M.read (Bytes.toB256 [64]).toNat 32).1.toB256 = fp at run hdr hnx hnext fit keep ⊢
  intro grow hfp
  subst hfp
  refine ⟨_, _, ⟨hdr, ?_, fit, grow, keep⟩, run⟩
  rw [hnx]
  exact hnext

end Alloc

/-! ## The external wrapper of `f(string calldata)` -/

/-- The tags of one compilation of the wrapper and its body's table index. -/
structure CdWrapTags : Type where
  ret : UInt8 × UInt8
  a : UInt8 × UInt8
  b : UInt8 × UInt8
  c : UInt8 × UInt8
  d : UInt8 × UInt8
  body : UInt8 × UInt8
  kBody : Nat

namespace CdStrWrap

variable (ω : CdWrapTags)

/-- solc's `REVERT(0, 0)` arm. -/
def revert0 : SFunc := .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

/-- The wrapper's call into the body and its stopping continuation. -/
def callTail : SFunc :=
  .dest (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg (.swap 2)) (.next (.reg .pop)
    (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (tagPush ω.body)
      (.callNext ω.kBody (.dest (.last .stop))))))))))

/-- The length decode with its range and calldata guard. -/
def lenDecode : SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg .calldataload) (.next (.reg (.swap 0))
    (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1))
    (.next (.reg (.dup 4)) (.next (.push [0x01] (by decide)) (.next (.reg (.dup 3))
    (.next (.reg .mul) (.next (.reg (.dup 4)) (.next (.reg .add) (.next (.reg .gt)
    (.next (.push [0x01, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg (.dup 3))
    (.next (.reg .gt) (.next (.reg .or) (.next (.reg .iszero) (.next (tagPush ω.d)
    (.branch revert0 (callTail ω)))))))))))))))))))))

/-- The head guard of the length word. -/
def headGuard : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg (.dup 3))
    (.next (.push [0x20] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .add)
    (.next (.reg .gt) (.next (.reg .iszero) (.next (tagPush ω.c)
    (.branch revert0 (lenDecode ω)))))))))))

/-- The offset decode with its range guard. -/
def offDecode : SFunc :=
  .dest (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.swap 0))
    (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .add)
    (.next (.reg (.dup 1)) (.next (.reg .calldataload)
    (.next (.push [0x01, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg (.dup 1))
    (.next (.reg .gt) (.next (.reg .iszero) (.next (tagPush ω.b)
    (.branch revert0 (headGuard ω)))))))))))))))

/-- The wrapper. -/
def wrapper : SFunc :=
  .dest (.next (tagPush ω.ret) (.next (.push [0x04] (by decide)) (.next (.reg (.dup 0))
    (.next (.reg .calldatasize) (.next (.reg .sub) (.next (.push [0x20] (by decide))
    (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.reg .iszero) (.next (tagPush ω.a)
    (.branch revert0 (offDecode ω))))))))))))

/-- The decoded string's calldata offset word (after the selector). -/
def cdOff (sevm : Sevm) : Nat := (Sevm.dataWord sevm 4).toNat

/-- The decoded string's length word. -/
def cdLen (sevm : Sevm) : Nat := (Sevm.dataWord sevm (4 + Sevm.dataWord sevm 4)).toNat

theorem or_gt_zero {x y u v : B256} (h : (B256.gtCheck x y ||| B256.gtCheck u v) = 0) :
    B256.gtCheck x y = 0 := by
  unfold B256.gtCheck at h ⊢
  split_ifs at h ⊢
  all_goals first
    | rfl
    | exact ((by decide : ((1 : B256) ||| 1) ≠ 0) h).elim

variable {ω} {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {T : Conf}

/-- **Through the wrapper.** A reach of the wrapper to an `SSTORE` lies inside its body,
entered with the decoded length and data pointer over the return tag, both in range. -/
theorem reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {body : SFunc}
    (hk : fs[ω.kBody]? = some body) {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach P fs sevm ⟨St b S M G, wrapper ω, []⟩ T) (hT : AtSstore T) :
    ∃ b' M' G' T', Reach P fs sevm ⟨St b' ((cdLen sevm).toB256 :: (36 + cdOff sevm).toB256 ::
        Bytes.toB256 [ω.ret.1, ω.ret.2] :: S) M' G', body, []⟩ T' ∧ AtSstore T' ∧
      T = T'.below [.dest (.last .stop)] ∧ cdLen sevm ≤ 2 ^ 32 ∧ cdOff sevm ≤ 2 ^ 32 := by
  unfold wrapper at run
  rsd
  iterate 10 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  unfold offDecode at run
  rsd
  iterate 13 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  have offsetBound := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  unfold headGuard at run
  rsd
  iterate 9 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  unfold lenDecode at run
  rsd
  iterate 19 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  have lenBound := toNat_le_of_gtCheck_eq_zero (or_gt_zero (eq_zero_of_iszero_ne_zero hw))
  unfold callTail at run
  rsd
  iterate 7 rsx
  obtain ⟨_, T', inside, rfl⟩ := rs_callInto (E := []) rfl hk rfl (fun _ h => by cases h) run hT
  have four : Bytes.toB256 [4] = (4 : B256) := by decide
  have big : (Bytes.toB256 [1, 0, 0, 0, 0]).toNat = 2 ^ 32 := by decide
  rw [four] at offsetBound lenBound inside
  rw [big] at offsetBound lenBound
  have ptr : Bytes.toB256 [0x20] + (4 + Sevm.dataWord sevm 4) = (36 + cdOff sevm).toB256 := by
    unfold cdOff
    apply B256.toNat_inj
    rw [B256.toNat_add, B256.toNat_add, B256.toNat_toB256_of_lt (by omega),
      show (Bytes.toB256 [0x20]).toNat = 32 from rfl, show (4 : B256).toNat = 4 from rfl,
      Nat.lo_eq_of_lt (show 4 + (Sevm.dataWord sevm 4).toNat < 2 ^ 256 by omega),
      Nat.lo_eq_of_lt (show 32 + (4 + (Sevm.dataWord sevm 4).toNat) < 2 ^ 256 by omega)]
    omega
  rw [ptr, show Sevm.dataWord sevm (4 + Sevm.dataWord sevm 4) = (cdLen sevm).toB256 from
    (toB256_toNat _).symm] at inside
  exact ⟨_, _, _, T', inside, AtSstore.below.mp hT, rfl, lenBound, offsetBound⟩

end CdStrWrap

/-! ## solc's ABI string decoder fragments on a prefix reach -/

namespace ReachAbi

open SolcAbiStringStaging

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {b : Devm}
  {R : List B256} {M : Mem} {G : Nat} {k : SFunc} {K : List SFunc} {T : Conf}

private theorem lit20 : Bytes.toB256 [0x20] = (32 : B256) := by decide

/-- **The dynamic-string fragment on a reach to an `SSTORE`.** The reach passes the fragment
(it holds no `SSTORE`) into `k` with the allocation of `strFrag_lift` in memory, whose size
the potential after the payload copy bounds. -/
theorem strFrag_reach (eraseP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {h base E : B256}
    (run : Reach (FreePtr.PotStep P) fs sevm ⟨St b (h :: base :: E :: R) M G, strFrag k, K⟩ T)
    (hT : AtSstore T) :
    ∃ G' : Nat,
      (allocMem M (memWord M 64) (Sevm.dataWord sevm (base + Sevm.dataWord sevm h))
        (sevm.data.sliceD (32 + (base + Sevm.dataWord sevm h)).toNat
          (Sevm.dataWord sevm (base + Sevm.dataWord sevm h)).toNat 0)).size < 2 ^ 160 ∧
      Reach (FreePtr.PotStep P) fs sevm
        ⟨St b ((32 + (base + Sevm.dataWord sevm h)) :: memWord M 64 :: (32 + h) :: base ::
          E :: R)
          (allocMem M (memWord M 64) (Sevm.dataWord sevm (base + Sevm.dataWord sevm h))
            (sevm.data.sliceD (32 + (base + Sevm.dataWord sevm h)).toNat
              (Sevm.dataWord sevm (base + Sevm.dataWord sevm h)).toNat 0)) G', k, K⟩ T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep P s d n d' → Ninst.Run s d n d' :=
    fun h => eraseP h.1
  unfold strFrag at run
  iterate 47 rsx
  have hnext := rs_next run hT
  clear run
  obtain ⟨_, hstep, run⟩ := hnext
  obtain ⟨_, e⟩ := ri_stepR (erase hstep) rfl
  subst e
  have hpot := FreePtr.Pot.size_lt hstep.2.2
  clear hstep
  iterate 8 rsx
  rw [strFrag_mem] at run hpot
  rw [lit20] at run hpot
  exact ⟨_, hpot, run⟩

/-- The cursor rotation on a reach: the dropped source pointer is gone and the decoded value
`v` sits under the decoder triple. -/
theorem rotFrag_reach (eraseP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {x v h base E : B256}
    (run : Reach (FreePtr.PotStep P) fs sevm
      ⟨St b (x :: v :: h :: base :: E :: R) M G, rotFrag k, K⟩ T) (hT : AtSstore T) :
    ∃ G' : Nat, Reach (FreePtr.PotStep P) fs sevm ⟨St b (h :: base :: E :: v :: R) M G', k, K⟩ T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep P s d n d' → Ninst.Run s d n d' :=
    fun h => eraseP h.1
  unfold rotFrag at run
  iterate 6 rsx
  exact ⟨_, run⟩

/-- One masked static head decode on a reach: the masked word sits under the decoder triple
and the cursor advances by `32`. -/
theorem staticFrag_reach (eraseP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {xs : Bytes} {le : xs.length ≤ 32} {h base E : B256}
    (run : Reach (FreePtr.PotStep P) fs sevm
      ⟨St b (h :: base :: E :: R) M G, staticFrag xs le k, K⟩ T) (hT : AtSstore T) :
    ∃ G' : Nat, Reach (FreePtr.PotStep P) fs sevm
      ⟨St b ((32 + h) :: base :: E :: (xs.toB256 &&& Sevm.dataWord sevm h) :: R) M G', k, K⟩ T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep P s d n d' → Ninst.Run s d n d' :=
    fun h => eraseP h.1
  unfold staticFrag at run
  iterate 11 rsx
  rw [lit20] at run
  exact ⟨_, run⟩

end ReachAbi

end Blanc.Lift
