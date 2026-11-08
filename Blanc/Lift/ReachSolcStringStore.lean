import Blanc.Lift.ReachSstoreLoops
import Blanc.Lift.SolcAbiStringStaging
import Jaune.WordFacts

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
      rw [Nat.toB256_add_toB256] at run
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

/-- Retain the bounded old-tail interval for zero-clearing writes. -/
theorem reach_range (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (E : Entries τ fs)
    {K : List SFunc} {b : Devm} {r : B256} {S : List B256} {M : Mem} {G : Nat} {len p : Nat}
    {slot : B256} (bound : p + len + 32 ≤ 2 ^ 256)
    (run : Reach P fs sevm ⟨St b (len.toB256 :: p.toB256 :: slot :: r :: S) M G, helper τ, K⟩ T)
    (hT : AtSstore T) :
    StrStore.StoreRangeAt slot ((len + 31) / 32) T ∨ ∃ f K' b' M' G', K = f :: K' ∧
      Reach P fs sevm ⟨St b' (slot :: S) M' G', f, K'⟩ T := by
  have hfin : ((p + len).toB256).toNat = p + len := B256.toNat_toB256_of_lt (by omega)
  rcases StrStore.reach_range erase (by intro h; cases h) (ReachPayload.cdload_rdStep erase)
      (StrStore.shortCd_ok erase E.exit) E (by omega)
      (ReachPayload.cdload_win (by omega)) run hT with
    s | ⟨f, K', b', M', G', hK, -, run⟩
  · exact .inl (s.mono (StrStore.count_le p len))
  · exact .inr ⟨f, K', b', M', G', hK, run⟩

theorem reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (E : Entries τ fs)
    {K : List SFunc} {b : Devm} {r : B256} {S : List B256} {M : Mem} {G : Nat} {len p : Nat}
    {slot : B256} (bound : p + len + 32 ≤ 2 ^ 256)
    (run : Reach P fs sevm ⟨St b (len.toB256 :: p.toB256 :: slot :: r :: S) M G, helper τ, K⟩ T)
    (hT : AtSstore T) :
    StoreAt slot len T ∨ ∃ f K' b' M' G', K = f :: K' ∧
      Reach P fs sevm ⟨St b' (slot :: S) M' G', f, K'⟩ T := by
  rcases reach_range erase E bound run hT with h | h
  · exact .inl h.storeAt
  · exact .inr h

end StrStoreCd

/-! ## A solc 0.6 dynamic-string allocation from calldata -/

section Alloc

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {T : Conf}

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

variable {ω} {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {T : Conf}

end CdStrWrap

/-! ## solc's ABI string decoder fragments on a prefix reach -/

namespace ReachAbi

open SolcAbiStringStaging

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {b : Devm}
  {R : List B256} {M : Mem} {G : Nat} {k : SFunc} {K : List SFunc} {T : Conf}

end ReachAbi

end Blanc.Lift
