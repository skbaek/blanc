import Blanc.Lift.ReachSstoreLoops

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

namespace StrStoreCd

variable (τ : StrTags)

/-- The copy loop head of the helper (inline and at entry `kLoop`). -/
def loopHead : SFunc :=
  ReachPayload.headJ (.reg .calldataload) [τ.back.1, τ.back.2] [τ.exit.1, τ.exit.2]
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

/-- The short-string arm. -/
def shortArm : SFunc :=
  .next (.reg (.dup 2)) (.next (.reg (.dup 0)) (.next (.reg .add) (.next (.push [0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00] (by decide))
    (.next (.reg (.dup 2)) (.next (.reg .calldataload) (.next (.reg .and) (.next (.reg .or)
    (.next (.reg (.dup 5)) (.next (.reg .sstore) (.next (tagPush τ.exit) (.jump τ.kExit)))))))))))

/-- The long-string arm: header, empty test, then the copy loop. -/
def longArm : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.reg (.dup 0)) (.next (.reg .add) (.next (.push [0x01]
    (by decide)) (.next (.reg .add) (.next (.reg (.dup 5)) (.next (.reg .sstore)
    (.next (.reg (.dup 2)) (.next (.reg .iszero) (.next (tagPush τ.exit)
    (.branchTo (.next (.reg (.swap 1)) (.next (.reg (.dup 2)) (.next (.reg .add) (loopHead τ))))
      τ.kExit)))))))))))

/-- The helper. -/
def helper : SFunc :=
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
    (.branch (shortArm τ) (longArm τ))))))))))))))))))))))))))))))))))))

/-- The table entries the helper reaches. -/
structure Entries (fs : List SFunc) : Prop where
  exit : fs[τ.kExit]? = some (exitTree τ)
  loop : fs[τ.kLoop]? = some (loopHead τ)
  clr : fs[τ.kClr]? = some (.dest (clrHead τ))
  clrLoop : fs[τ.kClrLoop]? = some (clrHead τ)

/-- What a store of the helper writes: the slot, zero, or a payload word. -/
def StoreAt (slot : B256) (len : Nat) (T : Conf) : Prop :=
  ∃ key v S, T.d.stack = key :: v :: S ∧
    (key = slot ∨ v = 0 ∨ ∃ j : Nat, j < (len + 31) / 32 ∧ key = slot.toBytes.keccak + j.toB256)

variable {τ} {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {T : Conf}

theorem exit_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (E : Entries τ fs)
    {K : List SFunc} {b : Devm} {x y z w s0 s1 : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach P fs sevm ⟨St b (x :: y :: z :: w :: s0 :: s1 :: S) M G, exitTree τ, K⟩ T)
    (hT : AtSstore T) :
    ReachClear.ZeroAt T ∨ ∃ f K' b' M' G', K = f :: K' ∧
      Reach P fs sevm ⟨St b' (s0 :: S) M' G', f, K'⟩ T := by
  unfold exitTree at run
  rsd
  iterate 6 rsx
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  rw [E.clr] at hg
  cases hg
  rsd
  rcases ReachClear.clear_reach erase E.clrLoop rfl run hT with h | ⟨f, K', b', M', G', hK, run⟩
  · exact .inl h
  cases hK
  rsd
  iterate 2 rsx
  exact .inr (rs_ret run hT)

theorem reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (E : Entries τ fs)
    {K : List SFunc} {b : Devm} {r : B256} {S : List B256} {M : Mem} {G : Nat} {len p : Nat}
    {slot : B256} (bound : p + len + 32 ≤ 2 ^ 256)
    (run : Reach P fs sevm ⟨St b (len.toB256 :: p.toB256 :: slot :: r :: S) M G, helper τ, K⟩ T)
    (hT : AtSstore T) :
    StoreAt slot len T ∨ ∃ f K' b' M' G', K = f :: K' ∧
      Reach P fs sevm ⟨St b' (slot :: S) M' G', f, K'⟩ T := by
  unfold helper at run
  rsd
  iterate 2 rsx
  rsload
  iterate 18 rsx
  rw [scratch_word M slot] at run
  iterate 13 rsx
  rcases rs_branch run hT with ⟨hw, _, run⟩ | ⟨hw, _, run⟩
  · unfold shortArm at run
    iterate 9 rsx
    rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
    · exact .inl ⟨_, _, _, rfl, .inl rfl⟩
    obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
    subst e
    clear hstep
    rsx
    obtain ⟨g, _, hg, run⟩ := rs_jump run hT
    rw [E.exit] at hg
    cases hg
    rcases exit_reach erase E run hT with ⟨x, S', h⟩ | h
    · exact .inl ⟨_, _, _, h, .inr (.inl rfl)⟩
    · exact .inr h
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
      rw [toB256_add_toB256 (by omega)] at run
      have hfin : ((p + len).toB256).toNat = p + len := B256.toNat_toB256_of_lt (by omega)
      rcases ReachPayload.payloadJ_reach erase (by intro h; cases h)
          (ReachPayload.cdload_rdStep erase) (ReachPayload.cdload_win (by omega)) E.loop (i := 0) (fin := (p + len).toB256)
          (base0 := slot.toBytes.keccak) (p := p)
          (by
            refine ⟨Nat.zero_le _, by omega, ?_⟩
            rw [St.stack, Nat.mul_zero, Nat.add_zero, show ((0 : Nat).toB256) = 0 from rfl,
              B256.add_zero])
          run hT with ⟨j, v, S', hj, h⟩ | ⟨i, g, b', M', G', -, hg, run⟩
      · refine .inl ⟨_, _, _, h, .inr (.inr ⟨j, ?_, rfl⟩)⟩
        unfold SolcStoragePayload.count at hj
        omega
      · rw [E.exit] at hg
        cases hg
        rcases exit_reach erase E run hT with ⟨x, S', h⟩ | h
        · exact .inl ⟨_, _, _, h, .inr (.inl rfl)⟩
        · exact .inr h
    · rw [E.exit] at hg
      cases hg
      rcases exit_reach erase E run hT with ⟨x, S', h⟩ | h
      · exact .inl ⟨_, _, _, h, .inr (.inl rfl)⟩
      · exact .inr h

end StrStoreCd

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
    | exact ((by decide : ((1 : B256) ||| 0) ≠ 0) h).elim

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

end Blanc.Lift
