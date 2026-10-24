import Blanc.Lift.Usdc.InitReach
import Blanc.Lift.Usdc.Impl.Cert

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

variable {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}

/-- **FiatTokenV2_2 `initializeV2` on a prefix reach.** A reach of the FiatTokenV2_2 code from entry `0`, with
empty stack and the `initializeV2` selector, to an `SSTORE` stops at a write of `KeysInitV2`
or of zero. -/
theorem initV2_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : selWord sevm = 0xd608ea64) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInitV2 sevm) T := by
  rw [root_eq] at run
  obtain ⟨g, b, G', hg, run⟩ := dispatch06_reach erase sel route_initV2 run hT
  rw [wrap_eq] at hg
  cases hg
  obtain ⟨b', M'', G'', T', inside, hT', rfl, lenB, offB⟩ :=
    CdStrWrap.reach erase body_eq run hT
  have small : 36 + CdStrWrap.cdOff sevm + CdStrWrap.cdLen sevm + 32 ≤ 2 ^ 34 := by omega
  have bound : 36 + CdStrWrap.cdOff sevm + CdStrWrap.cdLen sevm + 32 ≤ 2 ^ 256 :=
    small.trans (Nat.pow_le_pow_right (by decide) (by decide))
  refine InitStore.below.mpr (InitStore.mono (KeysV2Len.cap lenB)
    (InitV2Check.reach erase join_eq ?_ inside hT'))
  intro d' M₁ G₁ tail
  exact InitV2Tail.reach erase entries helper_eq freeDom (by decide) rfl bound tail hT'

/-! ## `initializeV2_2(address[], string)` -/

/-- solc's 20-byte address mask. -/
def addrMask : B256 := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- **`_blacklist(x)` (entry `86`) on a reach.** It writes only `balanceAndBlacklistStates[x]`
(slot `9` of the masked address), then returns over its argument and return tag. -/
theorem blacklist_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {K : List SFunc} {b : Devm} {x t : B256} {R : List B256} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b (x :: t :: R) M G, Impl.t_4224_c86, K⟩ T)
    (hT : AtSstore T) :
    (∀ key v S, T.d.stack = key :: v :: S → key = mapSlot (x &&& addrMask) 9) ∨
      ∃ f K' b' M' G', K = f :: K' ∧ Reach P Impl.cert.prog sevm ⟨St b' R M' G', f, K'⟩ T := by
  rsd
  iterate 4 rsx
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  cases hg
  rsd
  iterate 2 rsx
  rcases rs_branch run hT with ⟨hw, _, run⟩ | ⟨-, _, run⟩
  · exact absurd hw (by decide)
  rsd
  iterate 13 rsx
  rsld
  iterate 2 rsx
  rsd
  iterate 17 rsx
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · refine .inl fun key v S h => ?_
    simp only [St.stack, List.cons.injEq] at h
    rw [← h.1]
    exact mapSlot_scratch _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  rsx
  obtain ⟨f, K', b', M', G', hK, run⟩ := rs_ret run hT
  cases hK
  rsd
  rsx
  exact .inr (rs_ret run hT)

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
  have hiN : (i.toB256).toNat = i := B256.toNat_toB256_of_lt (by have := B256.toNat_lt aL; omega)
  repeat rsa
  rcases rs_branch run hT with ⟨hw, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact .inr (.inr ⟨_, _, _, run⟩)
  have hlt : i < aL.toNat := by
    have := lt_of_ltCheck (eqCheck_zero_eq_zero hw)
    rwa [hiN] at this
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  repeat rsa
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  cases hg
  rcases blacklist_reach erase run hT with h | ⟨f, K', b', M', G', hK, run⟩
  · refine .inl fun key v S' hs => .inl ⟨i, hlt, .inr (h key v S' hs)⟩
  cases hK
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · refine .inl (InitStore.of_top rfl ⟨i, hlt, .inl ?_⟩)
    exact mapSlot_scratch _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat rsa
  obtain ⟨g, _, hg, run⟩ := rs_jump run hT
  cases hg
  rw [show Bytes.toB256 [1] + i.toB256 = (i + 1).toB256 by
    rw [B256.add_comm]
    exact toB256_add_toB256 (a := i) (b := 1) (by have := B256.toNat_lt aL; omega)] at run
  exact .inr (.inl ⟨_, _, _, hlt, run⟩)

/-- The keys the code after the loop writes: the contract's own `_deprecatedBlacklisted` and
`balanceAndBlacklistStates` rows and the version slot `18`. -/
def AfterKeys (sevm : Sevm) (key : B256) : Prop :=
  key = mapSlot (sevm.currentTarget.toB256 &&& addrMask) 9 ∨
    key = mapSlot sevm.currentTarget.toB256 3 ∨ key = 18

theorem after22 (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {i sL sP aL aP r : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b (i :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_2698_c101, []⟩ T) (hT : AtSstore T) : InitStore (AfterKeys sevm) T := by
  repeat rsa
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  cases hg
  rcases blacklist_reach erase run hT with h | ⟨f, K', b', M', G', hK, run⟩
  · exact fun key v S' hs => .inl (.inl (h key v S' hs))
  cases hK
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact InitStore.of_top rfl
      (.inr (.inl (mapSlot_scratch _ _ _ (by decide) (by decide) (by decide) (by decide))))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact InitStore.of_top rfl (.inr (.inr (by decide)))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat rsa
  exact (Reach.not_ret_nilS run hT).elim

theorem loop22 (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sL sP aL aP r : B256} {S : List B256} {i : Nat} (hi : i ≤ aL.toNat) {b : Devm} {M : Mem}
    {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b (i.toB256 :: sL :: sP :: aL :: aP :: r :: S) M G,
      Impl.t_255a_c101, []⟩ T) (hT : AtSstore T) :
    InitStore (LoopKeys sevm aP aL.toNat) T ∨
      ∃ j b' M' G', Reach P Impl.cert.prog sevm
        ⟨St b' (j :: sL :: sP :: aL :: aP :: r :: S) M' G', Impl.t_2698_c101, []⟩ T := by
  refine reach_loop_index (fun j d => j ≤ aL.toNat ∧ ∃ b M G,
      d = St b (j.toB256 :: sL :: sP :: aL :: aP :: r :: S) M G) aL.toNat (fun _ _ h => h.1) ?_
    i _ ⟨hi, b, M, G, rfl⟩ run
  intro j d ⟨hj, b, M, G, hd⟩ run
  subst hd
  rcases pass22 erase hj run hT with h | ⟨b', M', G', hj', run⟩ | ⟨b', M', G', run⟩
  · exact .inl (.inl h)
  · exact .inr ⟨_, ⟨hj', b', M', G', rfl⟩, run⟩
  · exact .inl (.inr ⟨_, b', M', G', run⟩)

/-- The keys `initializeV2_2` writes: the symbol (slot `5` and its payload words), the
blacklisting loop's rows, and the rows the code after the loop writes. -/
def BodyKeys (sevm : Sevm) (sLen : Nat) (aP : B256) (aLen : Nat) (key : B256) : Prop :=
  key = 5 ∨ (∃ j : Nat, j < (sLen + 31) / 32 ∧ key = (5 : B256).toBytes.keccak + j.toB256) ∨
    LoopKeys sevm aP aLen key ∨ AfterKeys sevm key

theorem body22 (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sL sP : Nat} {aL aP r : B256} {S : List B256} {b : Devm} {M : Mem} {G : Nat}
    (bound : sP + sL + 32 ≤ 2 ^ 256)
    (run : Reach P Impl.cert.prog sevm ⟨St b (sL.toB256 :: sP.toB256 :: aL :: aP :: r :: S) M G,
      Impl.t_2538_c55, []⟩ T) (hT : AtSstore T) : InitStore (BodyKeys sevm sL aP aL.toNat) T := by
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
  rcases StrStoreCd.reach erase entries bound run hT with
    ⟨key, v, S', h, hk | hv | ⟨j, hj, hk⟩⟩ | ⟨f, K', b', M', G', hK, run⟩
  · exact InitStore.of_eq h (.inl (.inl (hk.trans (by decide))))
  · exact InitStore.of_eq h (.inr hv)
  · exact InitStore.of_eq h (.inl (.inr (.inl ⟨j, hj, by rw [hk]; rfl⟩)))
  cases hK
  rsd
  iterate 2 rsx
  rw [head_eq] at run
  rcases loop22 erase (i := 0) (Nat.zero_le _) run hT with h | ⟨j, b', M', G', run⟩
  · exact h.mono fun k hk => .inr (.inr (.inl hk))
  · exact (after22 erase run hT).mono fun k hk => .inr (.inr (.inr hk))

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

theorem wrap22_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St b S M G, Impl.t_0851_c162, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInitV2_2 sevm) T := by
  rsd
  iterate 10 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  rsd
  iterate 13 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  have off1 := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  rsd
  iterate 9 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  rsd
  iterate 19 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  have len1 := toNat_le_of_gtCheck_eq_zero (CdStrWrap.or_gt_zero (eq_zero_of_iszero_ne_zero hw))
  rsd
  iterate 16 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  have off2 := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  rsd
  iterate 9 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  rsd
  iterate 19 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  have len2 := toNat_le_of_gtCheck_eq_zero (CdStrWrap.or_gt_zero (eq_zero_of_iszero_ne_zero hw))
  rsd
  iterate 7 rsx
  obtain ⟨_, T', inside, rfl⟩ := rs_callInto (E := []) rfl
    (show Impl.cert.prog[55]? = some Impl.t_2538_c55 from rfl) rfl (fun _ h => by cases h) run hT
  have hT' : AtSstore T' := AtSstore.below.mp hT
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
  unfold KeysInitV2_2
  rw [hs, ha]
  exact InitStore.below.mpr (body22 erase
    (small.trans (Nat.pow_le_pow_right (by decide) (by decide))) inside hT')

theorem route_initV2_2 : selTree.selWalk 0x430239b4 =
    .inl (Bytes.toB256 [0x43, 0x02, 0x39, 0xb4], 162) := by
  decide +kernel

/-- **V2_2 `initializeV2_2` on a prefix reach.** A reach of the V2_2 code from entry `0`, with
empty stack and the `initializeV2_2` selector, to an `SSTORE` stops at a write of
`KeysInitV2_2` or of zero. -/
theorem initV2_2_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : selWord sevm = 0x430239b4) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInitV2_2 sevm) T := by
  rw [root_eq] at run
  obtain ⟨g, b, G', hg, run⟩ := dispatch06_reach erase sel route_initV2_2 run hT
  rw [show Impl.cert.prog[162]? = some Impl.t_0851_c162 from rfl] at hg
  cases hg
  exact wrap22_reach erase run hT

end Blanc.Lift.Usdc.InitReachV2_2
