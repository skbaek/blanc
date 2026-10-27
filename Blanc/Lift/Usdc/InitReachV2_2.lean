import Blanc.Lift.Usdc.InitReach
import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.CursorKeccak
import Blanc.Lift.FrameSkip
import Blanc.Lift.ObservedReachSplit

/-!
# FiatTokenV2_2's `initializeV2` on a prefix reach

Shape equations (`rfl`) placing the FiatTokenV2_2 code's trees at the shared shapes of
`Blanc/Lift/Usdc/InitReach.lean` and `Blanc/Lift/ReachSolcStringStore.lean`, and the walk
from entry `0`: every `SSTORE` a FiatTokenV2_2 frame reaches under `initializeV2` writes a key of
`KeysInitV2` or zero, whatever the frame's outcome (`initV2_reach`).
-/

namespace Blanc.Lift.Usdc.InitReachV2_2

open Jaune Blanc Blanc.Lift

/-- The `string storage = string calldata` helper (entry `74`). -/
def τ : StrTags := ⟨(0x55, 0xaa), (0x55, 0x3b), (0x55, 0xbc), (0x55, 0x47), (0x55, 0xd7),
  (0x55, 0xd8), 14, 105, 82, 108⟩

theorem helper_eq : Impl.cert.prog[74]? = some (StrStoreCd.helper τ) := rfl

theorem entries : StrStoreCd.Entries τ Impl.cert.prog := ⟨rfl, rfl, rfl, rfl⟩

/-- The `initializeV2(string)` wrapper (entry `133`). -/
def ω : CdWrapTags := ⟨(0x04, 0x89), (0x0f, 0xd8), (0x0f, 0xf3), (0x10, 0x05), (0x10, 0x27),
  (0x37, 0x44), 25⟩

theorem wrap_eq : Impl.cert.prog[133]? = some (CdStrWrap.wrapper ω) := rfl

/-- The shared part of `initializeV2`'s body. -/
def ν : V2Tags := ⟨(0x37, 0x86), (0x55, 0x4b), (0x37, 0xfb), (0x4c, 0x29), 74, 75⟩

/-- The domain-separator helper holds no `SSTORE`. -/
theorem freeDom : SstoreFreeSet Impl.cert.prog [75, 77] = true := by decide

theorem body_eq : Impl.cert.prog[25]? = some (InitV2Check.body (0x37, 0x71) (0x37, 0x7a) 5
    (InitV2Tail.tree ν)) := rfl

theorem join_eq : Impl.cert.prog[5]? = some (InitV2Check.join (0x37, 0x7a) (InitV2Tail.tree ν)) := rfl

/-- The dispatcher's comparison tree. -/
def selTree : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide)) (.next (.reg .gt)
    (.next (.push [0x01, 0xd3] (by decide)) (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))

theorem root_eq : Impl.t_0000_c0 = dispatch06 (0x00, 0x10) (0x03, 0x6d) selTree := rfl

theorem route_initV2 : selTree.selWalk 0xd608ea64 =
    .inl (Bytes.toB256 [0xd6, 0x08, 0xea, 0x64], 133) := by
  decide +kernel

variable {observe : Conf → Conf → Prop}

variable {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}

/-- **FiatTokenV2_2 `initializeV2` on a prefix reach.** A reach of the FiatTokenV2_2 code from entry `0`, with
empty stack and the `initializeV2` selector, to an `SSTORE` stops at a write of `KeysInitV2`
or of zero. -/
theorem initV2_reach_range (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : initSelWord sevm = 0xd608ea64) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitRangeV2 sevm T := by
  rw [root_eq] at run
  obtain ⟨g, b, G', hg, run⟩ := dispatch06_reach erase sel route_initV2 run hT
  rw [wrap_eq] at hg
  cases hg
  obtain ⟨b', M'', G'', T', inside, hT', rfl, lenB, offB⟩ :=
    CdStrWrap.reach erase body_eq run hT
  have small : 36 + CdStrWrap.cdOff sevm + CdStrWrap.cdLen sevm + 32 ≤ 2 ^ 34 := by omega
  have bound : 36 + CdStrWrap.cdOff sevm + CdStrWrap.cdLen sevm + 32 ≤ 2 ^ 256 :=
    small.trans (Nat.pow_le_pow_right (by decide) (by decide))
  refine InitRangeV2.below.mpr (InitRangeV2Len.cap lenB
    (InitV2Check.reach erase join_eq ?_ inside hT'))
  intro d' M₁ G₁ tail
  exact InitV2Tail.reach_range erase entries helper_eq freeDom (by decide) rfl bound tail hT'

theorem initV2_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : initSelWord sevm = 0xd608ea64) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInitV2 sevm) T :=
  (initV2_reach_range erase sel run hT).to_initStore


/-! ## `initializeV2_2(address[], string)` -/

/-- solc's 20-byte address mask. -/
def addrMask : B256 := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- **`_blacklist(x)` (entry `86`) on a reach.** It writes only `balanceAndBlacklistStates[x]`
(slot `9` of the masked address), then returns over its argument and return tag. -/
theorem blacklist_source (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {K : List SFunc} {b : Devm} {x t : B256} {R : List B256} {M : Mem} {G : Nat}
    (run : ObservedReach P observe Impl.cert.prog sevm ⟨St b (x :: t :: R) M G, Impl.t_4224_c86, K⟩ T)
    (hT : AtSstore T) :
    ((∀ key v S, T.d.stack = key :: v :: S → key = mapSlot (x &&& addrMask) 9) ∧
      ObservedKeccak P observe sevm ((x &&& addrMask).toBytes ++ (9 : B256).toBytes)
        (fun _ => True)) ∨
      ∃ f K' b' M' G', K = f :: K' ∧ ObservedReach P observe Impl.cert.prog sevm ⟨St b' R M' G', f, K'⟩ T := by
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  cases hg
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨hw, _, run⟩ | ⟨-, _, run⟩
  · exact absurd hw (by decide)
  orsd
  iterate 13 orsx
  orsld
  iterate 2 orsx
  orsd
  iterate 13 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := (x &&& addrMask).toBytes ++ (9 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 3 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨_, hstep, _, run⟩
  · refine .inl ⟨?_, hash⟩
    intro key v S h
    simp only [St.stack, List.cons.injEq] at h
    rw [← h.1]
    rfl
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  orsx
  obtain ⟨f, K', b', G', hK, run⟩ := ObservedReach.rs_retM run hT
  cases hK
  orsd
  orsx
  obtain ⟨f, K', b', G', hK, run⟩ := ObservedReach.rs_retM run hT
  exact .inr ⟨f, K', b', _, G', hK, run⟩

theorem blacklist_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {K : List SFunc} {b : Devm} {x t : B256} {R : List B256} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b (x :: t :: R) M G, Impl.t_4224_c86, K⟩ T)
    (hT : AtSstore T) :
    (∀ key v S, T.d.stack = key :: v :: S → key = mapSlot (x &&& addrMask) 9) ∨
      ∃ f K' b' M' G', K = f :: K' ∧ Reach P Impl.cert.prog sevm ⟨St b' R M' G', f, K'⟩ T := by
  rcases blacklist_source erase (ObservedReach.of_reach run) hT with
    ⟨keys, _⟩ | ⟨f, K', b', M', G', same, rest⟩
  · exact .inl keys
  · exact .inr ⟨f, K', b', M', G', same, rest.forget⟩

theorem head_eq : Impl.t_255a_c55 = Impl.t_255a_c101 := rfl

/-- The account the loop reads at index `j` of the calldata array at `aP`, as the code masks
it. -/
def acctAt (sevm : Sevm) (aP : B256) (j : Nat) : B256 :=
  addrMask &&& Sevm.dataWord sevm (Bytes.toB256 [32] * j.toB256 + aP)

/-- The keys the blacklisting loop writes for the first `n` accounts: their
`_deprecatedBlacklisted` row (slot `3`) and their `balanceAndBlacklistStates` row (slot `9`). -/
def LoopKeys (sevm : Sevm) (aP : B256) (n : Nat) (key : B256) : Prop :=
  ∃ j < n, key = mapSlot (acctAt sevm aP j) 3 ∨ key = mapSlot (acctAt sevm aP j &&& addrMask) 9

theorem lt_of_ltCheck {x y : B256} (h : B256.ltCheck x y ≠ 0) : x.toNat < y.toNat := by
  unfold B256.ltCheck at h
  split at h
  · rename_i hl
    exact B256.lt_iff_toNat_lt_toNat.mp hl
  · exact (h rfl).elim

theorem pass22_source (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {i : Nat} {sL sP aL aP r : B256} {S : List B256} {M : Mem} {G : Nat}
    (hi : i ≤ aL.toNat)
    (run : ObservedReach P observe Impl.cert.prog sevm ⟨St b (i.toB256 :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_255a_c101, []⟩ T) (hT : AtSstore T) :
    (∀ key v S, T.d.stack = key :: v :: S → ∃ j < aL.toNat,
      (key = mapSlot (acctAt sevm aP j) 3 ∧
        ObservedKeccak P observe sevm ((acctAt sevm aP j).toBytes ++ (3 : B256).toBytes) (fun _ => True)) ∨
      (key = mapSlot (acctAt sevm aP j &&& addrMask) 9 ∧
        ObservedKeccak P observe sevm ((acctAt sevm aP j &&& addrMask).toBytes ++ (9 : B256).toBytes)
          (fun _ => True))) ∨
      (∃ b' M' G', i + 1 ≤ aL.toNat ∧ ObservedReach P observe Impl.cert.prog sevm
        ⟨St b' ((i + 1).toB256 :: sL :: sP :: aL :: aP :: r :: S) M' G', Impl.t_255a_c101, []⟩ T) ∨
      ∃ b' M' G', ObservedReach P observe Impl.cert.prog sevm
        ⟨St b' (i.toB256 :: sL :: sP :: aL :: aP :: r :: S) M' G', Impl.t_2698_c101, []⟩ T := by
  have hiN : (i.toB256).toNat = i := B256.toNat_toB256_of_lt (by have := B256.toNat_lt aL; omega)
  repeat first | orsd | orsx
  rcases ObservedReach.rs_branch run hT with ⟨hw, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact .inr (.inr ⟨_, _, _, run⟩)
  have hlt : i < aL.toNat := by
    have := lt_of_ltCheck (eqCheck_zero_eq_zero hw)
    rwa [hiN] at this
  repeat orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  repeat first | orsd | orsx | orsld
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  repeat first | orsd | orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  repeat first | orsd | orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  cases hg
  rcases blacklist_source erase run hT with ⟨h, hash⟩ | ⟨f, K', b', M', G', hK, run⟩
  · refine .inl fun key v S' hs => ⟨i, hlt, .inr ⟨h key v S' hs, hash⟩⟩
  cases hK
  repeat first | orsd | orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  orsd
  iterate 23 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := (acctAt sevm aP i).toBytes ++ (3 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [0] + Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  repeat first | orsx | orsld
  rcases ObservedReach.sstoreS run with rfl | ⟨_, hstep, _, run⟩
  · refine .inl ?_
    intro key v S' hs
    simp only [St.stack, List.cons.injEq] at hs
    rw [← hs.1]
    exact ⟨i, hlt, .inl ⟨rfl, hash⟩⟩
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_jump run hT
  cases hg
  rw [show Bytes.toB256 [1] + i.toB256 = (i + 1).toB256 by
    rw [B256.add_comm]
    exact toB256_add_toB256 (a := i) (b := 1) (by have := B256.toNat_lt aL; omega)] at run
  exact .inr (.inl ⟨_, _, _, hlt, run⟩)

theorem pass22_keys (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {i : Nat} {sL sP aL aP r : B256} {S : List B256} {M : Mem} {G : Nat}
    (hi : i ≤ aL.toNat)
    (run : Reach P Impl.cert.prog sevm ⟨St b (i.toB256 :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_255a_c101, []⟩ T) (hT : AtSstore T) :
    (∀ key v S, T.d.stack = key :: v :: S → LoopKeys sevm aP aL.toNat key) ∨
      (∃ b' M' G', i + 1 ≤ aL.toNat ∧ Reach P Impl.cert.prog sevm
        ⟨St b' ((i + 1).toB256 :: sL :: sP :: aL :: aP :: r :: S) M' G', Impl.t_255a_c101, []⟩ T) ∨
      ∃ b' M' G', Reach P Impl.cert.prog sevm
        ⟨St b' (i.toB256 :: sL :: sP :: aL :: aP :: r :: S) M' G', Impl.t_2698_c101, []⟩ T := by
  rcases pass22_source erase hi (ObservedReach.of_reach run) hT with
    keys | ⟨b', M', G', next, rest⟩ | ⟨b', M', G', rest⟩
  · refine .inl fun key v S hs => ?_
    obtain ⟨j, hj, h | h⟩ := keys key v S hs
    · exact ⟨j, hj, .inl h.1⟩
    · exact ⟨j, hj, .inr h.1⟩
  · exact .inr (.inl ⟨b', M', G', next, rest.forget⟩)
  · exact .inr (.inr ⟨b', M', G', rest.forget⟩)

theorem pass22 (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {i : Nat} {sL sP aL aP r : B256} {S : List B256} {M : Mem} {G : Nat}
    (hi : i ≤ aL.toNat)
    (run : Reach P Impl.cert.prog sevm ⟨St b (i.toB256 :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_255a_c101, []⟩ T) (hT : AtSstore T) :
    InitStore (LoopKeys sevm aP aL.toNat) T ∨
      (∃ b' M' G', i + 1 ≤ aL.toNat ∧ Reach P Impl.cert.prog sevm
        ⟨St b' ((i + 1).toB256 :: sL :: sP :: aL :: aP :: r :: S) M' G', Impl.t_255a_c101, []⟩ T) ∨
      ∃ b' M' G', Reach P Impl.cert.prog sevm
        ⟨St b' (i.toB256 :: sL :: sP :: aL :: aP :: r :: S) M' G', Impl.t_2698_c101, []⟩ T := by
  rcases pass22_keys erase hi run hT with keys | next
  · exact .inl fun key v S hs => .inl (keys key v S hs)
  · exact .inr next

/-- The keys the code after the loop writes: the contract's own `_deprecatedBlacklisted` and
`balanceAndBlacklistStates` rows and the version slot `18`. -/
def AfterKeys (sevm : Sevm) (key : B256) : Prop :=
  key = mapSlot (sevm.currentTarget.toB256 &&& addrMask) 9 ∨
    key = mapSlot sevm.currentTarget.toB256 3 ∨ key = 18

theorem after22_source (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {i sL sP aL aP r : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : ObservedReach P observe Impl.cert.prog sevm ⟨St b (i :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_2698_c101, []⟩ T) (hT : AtSstore T) : ∀ key v S, T.d.stack = key :: v :: S →
      (key = mapSlot (sevm.currentTarget.toB256 &&& addrMask) 9 ∧
        ObservedKeccak P observe sevm ((sevm.currentTarget.toB256 &&& addrMask).toBytes ++ (9 : B256).toBytes)
          (fun _ => True)) ∨
      (key = mapSlot sevm.currentTarget.toB256 3 ∧
        ObservedKeccak P observe sevm (sevm.currentTarget.toB256.toBytes ++ (3 : B256).toBytes)
          (fun _ => True)) ∨ key = 18 := by
  repeat first | orsd | orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  cases hg
  rcases blacklist_source erase run hT with ⟨h, hash⟩ | ⟨f, K', b', M', G', hK, run⟩
  · exact fun key v S' hs => .inl ⟨h key v S' hs, hash⟩
  cases hK
  orsd
  iterate 15 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := sevm.currentTarget.toB256.toBytes ++ (3 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  repeat first | orsx | orsld
  rcases ObservedReach.sstoreS run with rfl | ⟨_, hstep, _, run⟩
  · intro key v S' hs
    simp only [St.stack, List.cons.injEq] at hs
    rw [← hs.1]
    exact .inr (.inl ⟨rfl, hash⟩)
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat first | orsx | orsld
  rcases ObservedReach.sstoreS run with rfl | ⟨_, hstep, _, run⟩
  · intro key v S' hs
    simp only [St.stack, List.cons.injEq] at hs
    rw [← hs.1]
    exact .inr (.inr (by decide))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat orsx
  exact (Reach.not_ret_nilS run.forget hT).elim

theorem after22_keys (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {i sL sP aL aP r : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b (i :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_2698_c101, []⟩ T) (hT : AtSstore T) : ∀ key v S, T.d.stack = key :: v :: S → AfterKeys sevm key := by
  intro key v S hs
  rcases after22_source erase (ObservedReach.of_reach run) hT key v S hs with h | h | h
  · exact .inl h.1
  · exact .inr (.inl h.1)
  · exact .inr (.inr h)

theorem after22 (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {i sL sP aL aP r : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b (i :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_2698_c101, []⟩ T) (hT : AtSstore T) : InitStore (AfterKeys sevm) T := by
  intro key v S hs
  exact .inl (after22_keys erase run hT key v S hs)

theorem loop22_source (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sL sP aL aP r : B256} {S : List B256} {i : Nat} (hi : i ≤ aL.toNat) {b : Devm} {M : Mem}
    {G : Nat}
    (run : ObservedReach P observe Impl.cert.prog sevm ⟨St b (i.toB256 :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_255a_c101, []⟩ T) (hT : AtSstore T) :
    (∀ key v S, T.d.stack = key :: v :: S → ∃ j < aL.toNat,
      (key = mapSlot (acctAt sevm aP j) 3 ∧
        ObservedKeccak P observe sevm ((acctAt sevm aP j).toBytes ++ (3 : B256).toBytes) (fun _ => True)) ∨
      (key = mapSlot (acctAt sevm aP j &&& addrMask) 9 ∧
        ObservedKeccak P observe sevm ((acctAt sevm aP j &&& addrMask).toBytes ++ (9 : B256).toBytes)
          (fun _ => True))) ∨
      ∃ j b' M' G', ObservedReach P observe Impl.cert.prog sevm
        ⟨St b' (j :: sL :: sP :: aL :: aP :: r :: S) M' G', Impl.t_2698_c101, []⟩ T := by
  refine ObservedReach.loop_index (fun j d => j ≤ aL.toNat ∧ ∃ b M G,
      d = St b (j.toB256 :: sL :: sP :: aL :: aP :: r :: S) M G) aL.toNat (fun _ _ h => h.1) ?_
    i _ ⟨hi, b, M, G, rfl⟩ run
  intro j d ⟨hj, b, M, G, hd⟩ run
  subst hd
  rcases pass22_source erase hj run hT with h | ⟨b', M', G', hj', run⟩ | ⟨b', M', G', run⟩
  · exact .inl (.inl h)
  · exact .inr ⟨_, ⟨hj', b', M', G', rfl⟩, run⟩
  · exact .inl (.inr ⟨_, b', M', G', run⟩)

theorem loop22_keys (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sL sP aL aP r : B256} {S : List B256} {i : Nat} (hi : i ≤ aL.toNat) {b : Devm} {M : Mem}
    {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b (i.toB256 :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_255a_c101, []⟩ T) (hT : AtSstore T) :
    (∀ key v S, T.d.stack = key :: v :: S → LoopKeys sevm aP aL.toNat key) ∨
      ∃ j b' M' G', Reach P Impl.cert.prog sevm
        ⟨St b' (j :: sL :: sP :: aL :: aP :: r :: S) M' G', Impl.t_2698_c101, []⟩ T := by
  rcases loop22_source erase hi (ObservedReach.of_reach run) hT with keys | ⟨j, b', M', G', rest⟩
  · refine .inl fun key v S hs => ?_
    obtain ⟨j, hj, h | h⟩ := keys key v S hs
    · exact ⟨j, hj, .inl h.1⟩
    · exact ⟨j, hj, .inr h.1⟩
  · exact .inr ⟨j, b', M', G', rest.forget⟩

theorem loop22 (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sL sP aL aP r : B256} {S : List B256} {i : Nat} (hi : i ≤ aL.toNat) {b : Devm} {M : Mem}
    {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b (i.toB256 :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_255a_c101, []⟩ T) (hT : AtSstore T) :
    InitStore (LoopKeys sevm aP aL.toNat) T ∨
      ∃ j b' M' G', Reach P Impl.cert.prog sevm
        ⟨St b' (j :: sL :: sP :: aL :: aP :: r :: S) M' G', Impl.t_2698_c101, []⟩ T := by
  rcases loop22_keys erase hi run hT with keys | next
  · exact .inl fun key v S hs => .inl (keys key v S hs)
  · exact .inr next

/-- The keys `initializeV2_2` writes: the symbol (slot `5` and its payload words), the
blacklisting loop's rows, and the rows the code after the loop writes. -/
def BodyKeys (sevm : Sevm) (sLen : Nat) (aP : B256) (aLen : Nat) (key : B256) : Prop :=
  key = 5 ∨ (∃ j : Nat, j < (sLen + 31) / 32 ∧ key = (5 : B256).toBytes.keccak + j.toB256) ∨
    LoopKeys sevm aP aLen key ∨ AfterKeys sevm key

/-- Exact initialized keys or an actual zero-clearing interval of the old symbol. -/
def BodyRange22 (sevm : Sevm) (sLen : Nat) (aP : B256) (aLen : Nat) (T : Conf) : Prop :=
  ∀ key v S, T.d.stack = key :: v :: S →
    BodyKeys sevm sLen aP aLen key ∨
      v = 0 ∧ StrStore.ClearRange 5 ((sLen + 31) / 32) key

theorem BodyRange22.of_eq {sLen aLen : Nat} {aP key v : B256} {S : List B256}
    (h : T.d.stack = key :: v :: S)
    (hk : BodyKeys sevm sLen aP aLen key ∨
      v = 0 ∧ StrStore.ClearRange 5 ((sLen + 31) / 32) key) :
    BodyRange22 sevm sLen aP aLen T := by
  intro key' v' S' h'
  rw [h] at h'
  simp only [List.cons.injEq] at h'
  obtain ⟨rfl, rfl, -⟩ := h'
  exact hk

theorem BodyRange22.to_initStore {sLen aLen : Nat} {aP : B256}
    (h : BodyRange22 sevm sLen aP aLen T) : InitStore (BodyKeys sevm sLen aP aLen) T :=
  fun key v S hs => (h key v S hs).imp_right And.left

theorem BodyRange22.below {sLen aLen : Nat} {aP : B256} {L : List SFunc} :
    BodyRange22 sevm sLen aP aLen (T.below L) ↔ BodyRange22 sevm sLen aP aLen T := Iff.rfl

theorem body22_range (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sL sP : Nat} {aL aP r : B256} {S : List B256} {b : Devm} {M : Mem} {G : Nat}
    (bound : sP + sL + 32 ≤ 2 ^ 256)
    (run : Reach P Impl.cert.prog sevm ⟨St b (sL.toB256 :: sP.toB256 :: aL :: aP :: r :: S) M G,
      Impl.t_2538_c55, []⟩ T) (hT : AtSstore T) : BodyRange22 sevm sL aP aL.toNat T := by
  rsd
  rsx
  rsld
  iterate 5 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  repeat rsa
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  rw [helper_eq] at hg
  cases hg
  rcases StrStoreCd.reach_range erase entries bound run hT with
    ⟨key, v, S', h, hk | ⟨j, hj, hk⟩ | ⟨hv, hr⟩⟩ | ⟨f, K', b', M', G', hK, run⟩
  · exact BodyRange22.of_eq h (.inl (.inl (hk.trans (by decide))))
  · exact BodyRange22.of_eq h (.inl (.inr (.inl ⟨j, hj, by rw [hk]; rfl⟩)))
  · exact BodyRange22.of_eq h (.inr ⟨hv, hr⟩)
  cases hK
  rsd
  iterate 2 rsx
  rw [head_eq] at run
  rcases loop22_keys erase (i := 0) (Nat.zero_le _) run hT with h | ⟨j, b', M', G', run⟩
  · exact fun key v S hs => .inl (.inr (.inr (.inl (h key v S hs))))
  · exact fun key v S hs => .inl (.inr (.inr (.inr (after22_keys erase run hT key v S hs))))

theorem body22 (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sL sP : Nat} {aL aP r : B256} {S : List B256} {b : Devm} {M : Mem} {G : Nat}
    (bound : sP + sL + 32 ≤ 2 ^ 256)
    (run : Reach P Impl.cert.prog sevm ⟨St b (sL.toB256 :: sP.toB256 :: aL :: aP :: r :: S) M G,
      Impl.t_2538_c55, []⟩ T) (hT : AtSstore T) : InitStore (BodyKeys sevm sL aP aL.toNat) T :=
  (body22_range erase bound run hT).to_initStore


/-- A migration mapping write and the successful hash that computed its key. -/
def MigrationSource (P : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (key : B256) : Prop :=
  ∃ account : Adr,
    (key = mapSlot account.toB256 3 ∧
      ObservedKeccak P observe sevm (account.toB256.toBytes ++ (3 : B256).toBytes) (fun _ => True)) ∨
    (key = mapSlot account.toB256 9 ∧
      ObservedKeccak P observe sevm (account.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True))

theorem MigrationSource.below {key : B256} {L : List SFunc}
    (source : MigrationSource P
      (fun before after => observe (before.below L) (after.below L)) sevm key) :
    MigrationSource P observe sevm key := by
  obtain ⟨account, source | source⟩ := source
  · exact ⟨account, .inl ⟨source.1, source.2.below L⟩⟩
  · exact ⟨account, .inr ⟨source.1, source.2.below L⟩⟩

/-- String-store ranges, literal version18, or an actually observed migration mapping. -/
def BodySource22 (P : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (sLen : Nat) (T : Conf) : Prop :=
  StrStore.StoreRangeAt 5 ((sLen + 31) / 32) T ∨
    ∀ key value rest, T.d.stack = key :: value :: rest →
      key = 18 ∨ MigrationSource P observe sevm key

theorem BodySource22.below {sLen : Nat} {L : List SFunc}
    (source : BodySource22 P
      (fun before after => observe (before.below L) (after.below L)) sevm sLen T) :
    BodySource22 P observe sevm sLen (T.below L) := by
  rcases source with string | other
  · exact .inl string
  · refine .inr fun key value rest stack => ?_
    exact (other key value rest stack).imp_right MigrationSource.below

/-- Retain original mapping observations through the actual string helper's return.
The checked return arity suffices because the caller discards the helper result. -/
theorem body22_source (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sL sP : Nat} {aL aP r : B256} {S : List B256} {b : Devm} {M : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none) (bound : sP + sL + 32 ≤ 2 ^ 256)
    (run : ObservedReach P observe Impl.cert.prog sevm
      ⟨St b (sL.toB256 :: sP.toB256 :: aL :: aP :: r :: S) M G, Impl.t_2538_c55, []⟩ T)
    (hT : AtSstore T) : BodySource22 P observe sevm sL T := by
  orsd
  orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT
      (by decide) (fun _ h => by cases h)).elim
  repeat first | orsd | orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_554b_c74 = some g at hg
  cases hg
  rcases ObservedReach.split run (S := []) rfl with
    ⟨target, inside, same⟩ | ⟨returned, callee, _, later⟩
  · have atStore : AtSstore target := by rw [same] at hT; exact hT
    change ObservedReach _ _ _ _ ⟨_, StrStoreCd.helper τ, []⟩ target at inside
    rcases StrStoreCd.reach_range erase entries bound inside.forget atStore with
      stored | ⟨f, K', b', M', G', impossible, _⟩
    · rw [same]
      exact .inl stored
    · cases impossible
  obtain ⟨Y, stack, length⟩ := callee.entry_stack_below_noStateGas erase Impl.cert_check hsg
    (k := 74) (ρ := 0x2556) (X := [sL.toB256, sP.toB256, 5, 0x2556])
    (R := sL.toB256 :: sP.toB256 :: aL :: aP :: r :: S)
    (show Impl.cert.entries[74]? = some ⟨0x554b, [.unk, .unk, .unk, .ret], 1⟩ from rfl)
    (show Impl.cert.prog[74]? = some Impl.t_554b_c74 from rfl) rfl
    (by exact .cons trivial (.cons trivial (.cons trivial (.cons rfl .nil))))
  have singleton : ∃ result, Y = [result] := by
    cases Y with
    | nil => simp only [List.length_nil] at length; omega
    | cons result tail =>
      cases tail with
      | nil => exact ⟨result, rfl⟩
      | cons next rest => simp only [List.length_cons] at length; omega
  obtain ⟨result, rfl⟩ := singleton
  rw [St.self stack rfl] at later
  clear run
  have run := later
  orsd
  iterate 2 orsx
  rw [head_eq] at run
  rcases loop22_source erase (i := 0) (Nat.zero_le _) run hT with
    loop | ⟨j, b', M', G', run⟩
  · refine .inr fun key value rest stack => .inr ?_
    obtain ⟨j, _, at3 | at9⟩ := loop key value rest stack
    · have account : acctAt sevm aP j =
          (Sevm.dataWord sevm (Bytes.toB256 [32] * j.toB256 + aP)).toAdr.toB256 :=
        ff20_and_word _
      rw [account] at at3
      exact ⟨_, .inl at3⟩
    · have account : acctAt sevm aP j &&& addrMask = (acctAt sevm aP j).toAdr.toB256 := by
        rw [B256.and_comm]
        exact ff20_and_word _
      rw [account] at at9
      exact ⟨_, .inr at9⟩
  · refine .inr fun key value rest stack => ?_
    rcases after22_source erase run hT key value rest stack with at9 | at3 | version
    · have account : sevm.currentTarget.toB256 &&& addrMask = sevm.currentTarget.toB256 := by
        rw [B256.and_comm]
        exact ff20_and_adr _
      rw [account] at at9
      exact .inr ⟨_, .inr at9⟩
    · exact .inr ⟨_, .inl at3⟩
    · exact .inl version

/-- The decoded array's data pointer and length words. -/
def arrPtr (sevm : Sevm) : B256 :=
  Bytes.toB256 [32] + (Bytes.toB256 [4] + Sevm.dataWord sevm (Bytes.toB256 [4]))

def arrLen (sevm : Sevm) : B256 :=
  Sevm.dataWord sevm (Bytes.toB256 [4] + Sevm.dataWord sevm (Bytes.toB256 [4]))

/-- The decoded string's calldata offset word (second head) and length word. -/
def strOff (sevm : Sevm) : Nat := (Sevm.dataWord sevm 36).toNat

def strLen (sevm : Sevm) : Nat := (Sevm.dataWord sevm (4 + Sevm.dataWord sevm 36)).toNat

/-- The keys `initializeV2_2(accounts, symbol)` writes, with the frame's decoded symbol and
array lengths capped at the decoder's bound `2 ^ 32` (a longer one reverts before any store). -/
def KeysInitV2_2 (sevm : Sevm) : B256 → Prop :=
  BodyKeys sevm (min (strLen sevm) (2 ^ 32)) (arrPtr sevm) (min (arrLen sevm).toNat (2 ^ 32))

/-- Frame-local V2.2 initializer range, with both actual decoder caps. -/
def InitRange22 (sevm : Sevm) (T : Conf) : Prop :=
  BodyRange22 sevm (min (strLen sevm) (2 ^ 32)) (arrPtr sevm)
    (min (arrLen sevm).toNat (2 ^ 32)) T

theorem InitRange22.to_initStore (h : InitRange22 sevm T) :
    InitStore (KeysInitV2_2 sevm) T := BodyRange22.to_initStore h

theorem wrap22_body (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (run : ObservedReach P observe Impl.cert.prog sevm ⟨St b S M G, Impl.t_0851_c162, []⟩ T)
    (hT : AtSstore T) : ∃ G' T',
      ObservedReach P
        (fun before after => observe (before.below [Impl.t_0489_c162]) (after.below [Impl.t_0489_c162]))
        Impl.cert.prog sevm
        ⟨St b ((strLen sevm).toB256 :: (36 + strOff sevm).toB256 :: arrLen sevm :: arrPtr sevm ::
          0x0489 :: S) M G', Impl.t_2538_c55, []⟩ T' ∧
      T = T'.below [Impl.t_0489_c162] ∧ 36 + strOff sevm + strLen sevm + 32 ≤ 2 ^ 34 ∧
      min (strLen sevm) (2 ^ 32) = strLen sevm ∧
      min (arrLen sevm).toNat (2 ^ 32) = (arrLen sevm).toNat := by
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  orsd
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  have off1 := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  orsd
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  orsd
  iterate 19 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  have len1 := toNat_le_of_gtCheck_eq_zero (CdStrWrap.or_gt_zero (eq_zero_of_iszero_ne_zero hw))
  orsd
  iterate 16 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  have off2 := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  orsd
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  orsd
  iterate 19 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide) (fun _ h => by cases h)).elim
  have len2 := toNat_le_of_gtCheck_eq_zero (CdStrWrap.or_gt_zero (eq_zero_of_iszero_ne_zero hw))
  orsd
  iterate 7 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_2538_c55 = some g at hg
  cases hg
  rcases ObservedReach.split run (S := []) rfl with
    ⟨T', inside, same⟩ | ⟨returned, _, _, later⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl later.forget hT
      (by decide) (fun _ h => by cases h)).elim
  have e36 : Bytes.toB256 [4] + Bytes.toB256 [32] = (36 : B256) := by decide
  have four : Bytes.toB256 [4] = (4 : B256) := by decide
  have big : (Bytes.toB256 [1, 0, 0, 0, 0]).toNat = 2 ^ 32 := by decide
  rw [e36] at off2 len2 inside
  rw [big] at off2 len2 len1
  rw [show Bytes.toB256 [4] + Sevm.dataWord sevm 36 = 4 + Sevm.dataWord sevm 36 by rw [four]]
    at len2 inside
  have ptr : Bytes.toB256 [0x20] + (4 + Sevm.dataWord sevm 36) = (36 + strOff sevm).toB256 := by
    unfold strOff
    apply B256.toNat_inj
    rw [B256.toNat_add, B256.toNat_add, B256.toNat_toB256_of_lt (by omega),
      show (Bytes.toB256 [0x20]).toNat = 32 from rfl, show (4 : B256).toNat = 4 from rfl,
      Nat.lo_eq_of_lt (show 4 + (Sevm.dataWord sevm 36).toNat < 2 ^ 256 by omega),
      Nat.lo_eq_of_lt (show 32 + (4 + (Sevm.dataWord sevm 36).toNat) < 2 ^ 256 by omega)]
    omega
  rw [ptr, show Sevm.dataWord sevm (4 + Sevm.dataWord sevm 36) = (strLen sevm).toB256 from
    (toB256_toNat _).symm] at inside
  have small : 36 + strOff sevm + strLen sevm + 32 ≤ 2 ^ 34 := by unfold strOff strLen; omega
  have hs : min (strLen sevm) (2 ^ 32) = strLen sevm := Nat.min_eq_left (by unfold strLen; omega)
  have ha : min (arrLen sevm).toNat (2 ^ 32) = (arrLen sevm).toNat :=
    Nat.min_eq_left (by unfold arrLen; omega)
  exact ⟨_, T', inside, same, small, hs, ha⟩

theorem wrap22_reach_range (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b S M G, Impl.t_0851_c162, []⟩ T)
    (hT : AtSstore T) : InitRange22 sevm T := by
  obtain ⟨G', T', inside, rfl, small, hs, ha⟩ := wrap22_body erase (ObservedReach.of_reach run) hT
  unfold InitRange22
  rw [hs, ha]
  exact BodyRange22.below.mpr (body22_range erase
    (small.trans (Nat.pow_le_pow_right (by decide) (by decide))) inside.forget hT)

/-- The original ABI decoder carries the body's actual mapping hash occurrences. -/
theorem wrap22_source (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : ObservedReach P observe Impl.cert.prog sevm ⟨St b S M G, Impl.t_0851_c162, []⟩ T)
    (hT : AtSstore T) : BodySource22 P observe sevm (min (strLen sevm) (2 ^ 32)) T := by
  obtain ⟨G', T', inside, rfl, small, hs, _⟩ := wrap22_body erase run hT
  rw [hs]
  exact BodySource22.below (body22_source erase hsg
    (small.trans (Nat.pow_le_pow_right (by decide) (by decide))) inside hT)

theorem wrap22_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b S M G, Impl.t_0851_c162, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInitV2_2 sevm) T :=
  (wrap22_reach_range erase run hT).to_initStore

theorem route_initV2_2 : selTree.selWalk 0x430239b4 =
    .inl (Bytes.toB256 [0x43, 0x02, 0x39, 0xb4], 162) := by
  decide +kernel

/-- **V2_2 `initializeV2_2` on a prefix reach.** A reach of the V2_2 code from entry `0`, with
empty stack and the `initializeV2_2` selector, to an `SSTORE` stops at a write of
`KeysInitV2_2` or of zero. -/
theorem initV2_2_reach_range (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : initSelWord sevm = 0x430239b4) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitRange22 sevm T := by
  rw [root_eq] at run
  obtain ⟨g, b, G', hg, run⟩ := dispatch06_reach erase sel route_initV2_2 run hT
  rw [show Impl.cert.prog[162]? = some Impl.t_0851_c162 from rfl] at hg
  cases hg
  exact wrap22_reach_range erase run hT

/-- The actual selector0x430239b4 route retains every successful migration key hash. -/
theorem initV2_2_source (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : initSelWord sevm = 0x430239b4) {d : Devm} {M : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : ObservedReach P observe Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : BodySource22 P observe sevm (min (strLen sevm) (2 ^ 32)) T := by
  rw [root_eq] at run
  unfold dispatch06 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT
      (by decide) (fun _ h => by cases h)).elim
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT
      (by decide) (fun _ h => by cases h)).elim
  iterate 4 orsx
  change ObservedReach _ _ _ _ ⟨St _ (initSelWord sevm :: _) _ _, _, _⟩ _ at run
  rw [sel] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_initV2_2 run hT
  rw [show Impl.cert.prog[162]? = some Impl.t_0851_c162 from rfl] at hg
  cases hg
  exact wrap22_source erase hsg run hT

theorem initV2_2_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : initSelWord sevm = 0x430239b4) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInitV2_2 sevm) T :=
  (initV2_2_reach_range erase sel run hT).to_initStore

end Blanc.Lift.Usdc.InitReachV2_2
