import Blanc.Lift.ReachSolcStringStore

/-!
# USDC initializers on a prefix reach: shared shapes

What an initializer frame's `SSTORE` writes, read at a configuration a prefix reach of the
implementation code stops at (`InitStore`), and the part of FiatTokenV2's `initializeV2(string)`
that every V2 compilation shares after its version checks (`InitV2Tail.tree`, over the tags and
table indices `V2Tags` of one compilation): the name stored through the shared
`string storage = string calldata` helper (`StrStoreCd`), the domain separator computed by an
`SSTORE`-free helper and stored at slot `15`, and the version byte of slot `18`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- What an initializer `SSTORE` writes, read at the reach's target: a key of `Keys`, or zero. -/
def InitStore (Keys : B256 → Prop) (T : Conf) : Prop :=
  ∀ key v S, T.d.stack = key :: v :: S → Keys key ∨ v = 0

theorem InitStore.of_eq {Keys : B256 → Prop} {T : Conf} {key v : B256} {S : List B256}
    (h : T.d.stack = key :: v :: S) (hk : Keys key ∨ v = 0) : InitStore Keys T := by
  intro key' v' S' h'
  rw [h] at h'
  simp only [List.cons.injEq] at h'
  obtain ⟨rfl, rfl, -⟩ := h'
  exact hk

theorem InitStore.of_top {Keys : B256 → Prop} {T : Conf} {key : B256} {R : List B256}
    (h : T.d.stack = key :: R) (hk : Keys key) : InitStore Keys T := by
  intro key' v' S' h'
  rw [h] at h'
  simp only [List.cons.injEq] at h'
  exact .inl (h'.1 ▸ hk)

theorem InitStore.below {Keys : B256 → Prop} {T : Conf} {L : List SFunc} :
    InitStore Keys (T.below L) ↔ InitStore Keys T :=
  Iff.rfl

theorem InitStore.mono {Keys Keys' : B256 → Prop} {T : Conf} (h : ∀ k, Keys k → Keys' k)
    (s : InitStore Keys T) : InitStore Keys' T :=
  fun key v S hs => (s key v S hs).imp_left (h key)

/-- The selector word solc 0.6's dispatcher computes. -/
def initSelWord (sevm : Sevm) : B256 :=
  Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat

/-- solc 0.6's dispatcher prefix: free pointer, nonpayable check, short-calldata fallback (a
revert) and the selector word, before the comparison tree `sel`. -/
def dispatch06 (a b : UInt8 × UInt8) (sel : SFunc) : SFunc :=
  .next (.push [0x80] (by decide)) (.next (.push [0x40] (by decide)) (.next (.reg .mstore)
    (.next (.reg .callvalue) (.next (.reg (.dup 0)) (.next (.reg .iszero) (.next (tagPush a)
    (.branch CdStrWrap.revert0 (.dest (.next (.reg .pop) (.next (.push [0x04] (by decide))
    (.next (.reg .calldatasize) (.next (.reg .lt) (.next (tagPush b)
    (.branch (.next (.push [0x00] (by decide)) (.next (.reg .calldataload)
      (.next (.push [0xe0] (by decide)) (.next (.reg .shr) sel))))
      (.dest CdStrWrap.revert0)))))))))))))))

/-- **Through the dispatcher.** A reach of a solc 0.6 dispatcher to an `SSTORE`, for a
selector word whose walk ends at the goto `(c, j)`, continues from entry `j`. -/
theorem dispatch06_reach {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc}
    {sevm : Sevm} {T : Conf} (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {a b : UInt8 × UInt8} {sel : SFunc} {σ c : B256} {j : Nat} (hs : initSelWord sevm = σ)
    (hw : sel.selWalk σ = .inl (c, j)) {d : Devm} {G : Nat} {M : Mem}
    (run : Reach P fs sevm ⟨St d [] M G, dispatch06 a b sel, []⟩ T) (hT : AtSstore T) :
    ∃ g b' G', fs[j]? = some g ∧ Reach P fs sevm ⟨St b' [σ]
      (M.write (Bytes.toB256 [0x40]).toNat (Bytes.toB256 [0x80]).toBytes) G', g, []⟩ T := by
  unfold dispatch06 at run
  iterate 7 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  rsd
  iterate 5 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  iterate 4 rsx
  change Reach _ _ _ ⟨St _ (initSelWord sevm :: _) _ _, _, _⟩ _ at run
  rw [hs] at run
  obtain ⟨-, g, _, hg, run⟩ := Reach.selWalk_inlS erase hw run hT
  exact ⟨g, _, _, hg, run⟩

/-- The keys `initializeV2(name)` writes for a name of length `n`: slots `4`, `15`, `18` and
the name's payload words. -/
def KeysV2Len (n : Nat) (key : B256) : Prop :=
  key = 4 ∨ key = 15 ∨ key = 18 ∨
    ∃ j : Nat, j < (n + 31) / 32 ∧ key = (4 : B256).toBytes.keccak + j.toB256

/-- The keys `initializeV2(name)` writes, with the frame's decoded name length capped at the
decoder's bound `2 ^ 32` (a longer name reverts before any store). -/
def KeysInitV2 (sevm : Sevm) : B256 → Prop :=
  KeysV2Len (min (CdStrWrap.cdLen sevm) (2 ^ 32))

theorem KeysV2Len.cap {sevm : Sevm} (h : CdStrWrap.cdLen sevm ≤ 2 ^ 32) (key : B256)
    (k : KeysV2Len (CdStrWrap.cdLen sevm) key) : KeysInitV2 sevm key := by
  unfold KeysInitV2
  rw [Nat.min_eq_left h]
  exact k

/-- The tags and table indices of one compilation of `initializeV2`'s shared part. -/
structure V2Tags : Type where
  ret : UInt8 × UInt8
  helper : UInt8 × UInt8
  cont : UInt8 × UInt8
  dom : UInt8 × UInt8
  kHelper : Nat
  kDom : Nat

namespace InitV2Tail

variable (ν : V2Tags)

/-- `name = newName; DOMAIN_SEPARATOR = …; _initializedVersion = 1`. -/
def tree : SFunc :=
  (.dest (.next (tagPush ν.ret) (.next (.push [0x04] (by decide)) (.next (.reg (.dup 3))
    (.next (.reg (.dup 3)) (.next (tagPush ν.helper) (.callNext ν.kHelper (.dest
    (.next (.reg .pop) (.next (tagPush ν.cont) (.next (.reg (.dup 2)) (.next (.reg (.dup 2))
    (.next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x1f] (by decide))
    (.next (.reg .add) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 0))
    (.next (.reg (.swap 1)) (.next (.reg .div) (.next (.reg .mul)
    (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.push [0x40] (by decide))
    (.next (.reg .mload) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg .add)
    (.next (.push [0x40] (by decide)) (.next (.reg .mstore) (.next (.reg (.dup 0))
    (.next (.reg (.swap 3)) (.next (.reg (.swap 2)) (.next (.reg (.swap 1))
    (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg (.dup 1)) (.next (.reg .mstore)
    (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.dup 3))
    (.next (.reg (.dup 3)) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg (.dup 4))
    (.next (.reg .calldatacopy) (.next (.push [0x00] (by decide)) (.next (.reg (.swap 2))
    (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.swap 1))
    (.next (.reg .mstore) (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x40] (by decide))
    (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2))
    (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.reg (.swap 1)) (.next (.reg .mstore)
    (.next (.push [0x01] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .mstore)
    (.next (.push [0x32, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide))
    (.next (.push [0x20] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .add)
    (.next (.reg .mstore) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next (tagPush ν.dom)
    (.next (.reg (.swap 0)) (.next (.reg .pop) (.callNext ν.kDom (.dest
    (.next (.push [0x0f] (by decide)) (.next (.reg .sstore) (.next (.reg .pop) (.next (.reg .pop)
    (.next (.push [0x12] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .sload)
    (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00] (by decide))
    (.next (.reg .and) (.next (.push [0x01] (by decide)) (.next (.reg .or) (.next (.reg (.swap 0))
    (.next (.reg .sstore) .ret))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

variable {ν} {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {T : Conf}

theorem reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {τ : StrTags}
    (E : StrStoreCd.Entries τ fs) (hh : fs[ν.kHelper]? = some (StrStoreCd.helper τ))
    {F : List Nat} (hF : SstoreFreeSet fs F = true) (hdF : ν.kDom ∈ F) {g : SFunc}
    (hdom : fs[ν.kDom]? = some g)
    {b : Devm} {r : B256} {S : List B256} {M : Mem} {G : Nat}
    (bound : 36 + CdStrWrap.cdOff sevm + CdStrWrap.cdLen sevm + 32 ≤ 2 ^ 256)
    (run : Reach P fs sevm ⟨St b ((CdStrWrap.cdLen sevm).toB256 ::
      (36 + CdStrWrap.cdOff sevm).toB256 :: r :: S) M G, tree ν, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysV2Len (CdStrWrap.cdLen sevm)) T := by
  unfold tree at run
  rsd
  iterate 5 rsx
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  rw [hh] at hg
  cases hg
  rcases StrStoreCd.reach erase E (by omega) run hT with
    ⟨key, v, S', h, hk | hv | ⟨j, hj, hk⟩⟩ | ⟨f, K', b', M', G', hK, run⟩
  · exact InitStore.of_eq h (.inl (.inl (hk.trans (by decide))))
  · exact InitStore.of_eq h (.inr hv)
  · exact InitStore.of_eq h (.inl (.inr (.inr (.inr ⟨j, hj, by rw [hk]; rfl⟩))))
  cases hK
  rsd
  iterate 69 rsx
  obtain ⟨D, run⟩ := rs_callOverAny hF hdom hdF run hT
  rw [St.self' D] at run
  rsd
  rsx
  rcases Reach.sstoreS run with rfl | ⟨d', -, run⟩
  · exact InitStore.of_top rfl (.inr (.inl (by decide)))
  rw [St.self' d'] at run
  iterate 2 rsk
  iterate 2 rsx
  rsld
  iterate 5 rsx
  rcases Reach.sstoreS run with rfl | ⟨d', -, run⟩
  · exact InitStore.of_top rfl (.inr (.inr (.inl (by decide))))
  rw [St.self' d'] at run
  exact (Reach.not_ret_nilS run hT).elim

end InitV2Tail

/-! ## The V2_1/V2_2 version check before the shared part -/

namespace InitV2Check

/-- The join point: revert unless the check word is nonzero, then the shared part. -/
def join (b : UInt8 × UInt8) (tail : SFunc) : SFunc :=
  .dest (.next (tagPush b) (.branch CdStrWrap.revert0 tail))

/-- `require(initialized && _initializedVersion == 0)`: the second test only when the first
holds, both arriving at the join point (entry `k`). -/
def body (j b : UInt8 × UInt8) (k : Nat) (tail : SFunc) : SFunc :=
  .dest (.next (.push [0x08] (by decide)) (.next (.reg .sload) (.next (.push [0x01, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00] (by decide)) (.next (.reg (.swap 0)) (.next (.reg .div)
    (.next (.push [0xff] (by decide)) (.next (.reg .and) (.next (.reg (.dup 0))
    (.next (.reg .iszero) (.next (tagPush j)
    (.branchTo (.next (.reg .pop) (.next (.push [0x12] (by decide)) (.next (.reg .sload)
      (.next (.push [0xff] (by decide)) (.next (.reg .and) (.next (.reg .iszero)
      (join b tail))))))) k)))))))))))

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {T : Conf}

theorem join_reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {b : UInt8 × UInt8}
    {tail : SFunc} {Q : Prop} {d : Devm} {w : B256} {S : List B256} {M : Mem} {G : Nat}
    (cont : ∀ d' M' G', Reach P fs sevm ⟨St d' S M' G', tail, []⟩ T → Q)
    (run : Reach P fs sevm ⟨St d (w :: S) M G, join b tail, []⟩ T) (hT : AtSstore T) : Q := by
  unfold join at run
  rsd
  rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide) (fun _ h => by cases h)).elim
  exact cont _ _ _ run

/-- **Through the version check.** A reach of the checked body to an `SSTORE` lies in the
shared part, entered with the body's own stack. -/
theorem reach (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {j b : UInt8 × UInt8} {k : Nat} {tail : SFunc} (hk : fs[k]? = some (join b tail)) {Q : Prop}
    {d : Devm} {S : List B256} {M : Mem} {G : Nat}
    (cont : ∀ d' M' G', Reach P fs sevm ⟨St d' S M' G', tail, []⟩ T → Q)
    (run : Reach P fs sevm ⟨St d S M G, body j b k tail, []⟩ T) (hT : AtSstore T) : Q := by
  unfold body at run
  rsd
  rsx
  rsld
  iterate 8 rsx
  rcases rs_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
  · rsx
    rsx
    rsld
    iterate 3 rsx
    exact join_reach erase cont run hT
  · rw [hk] at hg
    cases hg
    exact join_reach erase cont run hT

end InitV2Check

end Blanc.Lift.Usdc
