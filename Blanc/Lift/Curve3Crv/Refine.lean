import Blanc.Lift.Curve3Crv.Dispatch
import Blanc.Lift.Curve3Crv.Slots

/-!
# The raw effects refine the model (pure)

For each function, under the storage abstraction `VyInv stor s K` and the frame-local premise
`Fresh` for the keys the call touches, the raw effect over storage (`Spec.lean`) and the model's
`step` succeed together, and when they do the new storage abstracts the model's new state
(for the live keys extended by the touched ones), the appended log entries are the model's
events, and the return data is the model's (`RawRefines`).  No bytecode appears here: these are
statements about `Stor.set`, `mapSlot`, and the model's functions.

Every lemma is a frozen segment; `refine_at` assembles them by the body index.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc.Curve3Crv (Call Ret)

/-- The raw effect of body `k`, with `ow` the owner answer (`set_name` only). -/
def rawOf (k : Nat) (sevm : Sevm) (ow : Option B256) (stor : Stor) : Option Raw :=
  match k with
  | 0 => rawSetMinter sevm stor
  | 1 => rawSetName sevm stor ow
  | 2 => rawTotalSupply sevm stor
  | 3 => rawAllowance sevm stor
  | 4 => rawTransfer sevm stor
  | 5 => rawTransferFrom sevm stor
  | 6 => rawApprove sevm stor
  | 7 => rawMint sevm stor
  | 8 => rawBurnFrom sevm stor
  | 9 => rawName sevm stor
  | 10 => rawSymbol sevm stor
  | 11 => rawDecimals sevm stor
  | 12 => rawBalanceOf sevm stor
  | _ => none

/-- The return kind and data of a raw effect and a model result agree.
Only `none` represents `STOP`; a `RETURN` cannot be matched to it. -/
def RetMatch : Option Bytes → Ret → Prop
  | none, r => r = .stop
  | some _, .stop => False
  | some out, r => RetOut out r

/-- A raw effect and a model result correspond: storage abstracts the new state over `K'`, the
log entries are the model's events, the return data the model's. -/
def Corr (sevm : Sevm) (K' : Key → Prop) (r : Raw) (o : Curve3Crv.Out) : Prop :=
  VyInv r.1 o.1 K' ∧ r.2.1 = o.2.1.map (eventLog sevm.currentTarget) ∧ RetMatch r.2.2 o.2.2

/-- The raw effect and the model's result succeed together and correspond. -/
def RawRefines (sevm : Sevm) (raw : Option Raw) (res : Curve3Crv.Result) (K' : Key → Prop) :
    Prop :=
  (∀ r, raw = some r → ∃ o, res = .ok o ∧ Corr sevm K' r o) ∧
    (∀ o, res = .ok o → ∃ r, raw = some r ∧ Corr sevm K' r o)

/-- Both sides succeed under one condition, with one result each. -/
theorem RawRefines.of_iff {sevm : Sevm} {raw : Option Raw} {res : Curve3Crv.Result}
    {K' : Key → Prop} (r0 : Raw) (o0 : Curve3Crv.Out) (P : Prop)
    (hraw : ∀ r, raw = some r ↔ P ∧ r = r0) (hres : ∀ o, res = .ok o ↔ P ∧ o = o0)
    (hc : P → Corr sevm K' r0 o0) : RawRefines sevm raw res K' := by
  refine ⟨fun r hr => ?_, fun o ho => ?_⟩
  · obtain ⟨hP, rfl⟩ := (hraw r).mp hr
    exact ⟨o0, (hres o0).mpr ⟨hP, rfl⟩, hc hP⟩
  · obtain ⟨hP, rfl⟩ := (hres o).mp ho
    exact ⟨r0, (hraw r0).mpr ⟨hP, rfl⟩, hc hP⟩

/-! ## Storage facts the refinement lemmas share -/

/-- A write off a string's slots keeps the string. -/
theorem VyStr.set_ne {stor : Stor} {base x v : B256} {n : Nat} {bs : Bytes}
    (h0 : base ≠ x) (hj : ∀ j < n, base + Nat.toB256 (j + 1) ≠ x) (h : VyStr stor base n bs) :
    VyStr (stor.set x v) base n bs := by
  have hw : vyStrWords (stor.set x v) base n = vyStrWords stor base n := by
    unfold vyStrWords
    simp only [List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro j hjm
    rw [Stor.get_set_ne _ (Ne.symm (hj j (List.mem_range.mp hjm)))]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, ?_⟩
  · rw [Stor.get_set_ne _ (Ne.symm h0)]; exact h1
  · rw [hw]; exact h3

/-- A write to one of the three word slots keeps both strings. -/
theorem VyInv.strs_set_word {stor : Stor} {s : Curve3Crv.State} {x v : B256}
    (hx : x ∈ vyWordSlots) (hn : VyStr stor vyNameBase 2 s.name)
    (hy : VyStr stor vySymbolBase 1 s.symbol) :
    VyStr (stor.set x v) vyNameBase 2 s.name ∧ VyStr (stor.set x v) vySymbolBase 1 s.symbol := by
  have h := vyStrSlots_apart.1
  refine ⟨hn.set_ne (h _ (by simp [vyNameSlots]) x hx) (fun j hj => h _ ?_ x hx),
    hy.set_ne (h _ (by simp [vySymbolSlots]) x hx) (fun j hj => h _ ?_ x hx)⟩
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp [vyNameSlots]
  · have : j = 0 := by omega
    subst this; simp [vySymbolSlots]

/-- A write to one of the three word slots, with the model changed only in those words. -/
theorem VyInv.of_set_word {stor : Stor} {s s' : Curve3Crv.State} {K : Key → Prop} {x v : B256}
    (h : VyInv stor s K) (hx : x ∈ vyWordSlots) (hbal : s'.balanceOf = s.balanceOf)
    (hall : s'.allowances = s.allowances) (hname : s'.name = s.name) (hsym : s'.symbol = s.symbol)
    (hdec : (stor.set x v).get vyDecimalsSlot = s'.decimals)
    (hsup : (stor.set x v).get vySupplySlot = s'.totalSupply)
    (hmin : (stor.set x v).get vyMinterSlot = s'.minter.toB256) (hcons : Curve3Crv.Conserved s') :
    VyInv (stor.set x v) s' K := by
  have hxf : x ∈ vyFixedSlots := by
    simp only [vyWordSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [vyFixedSlots]
  have hval : ∀ k : Key, k.val s' = k.val s := by
    intro k; cases k <;> simp [Key.val, hbal, hall]
  obtain ⟨hn, hy⟩ := VyInv.strs_set_word (v := v) hx h.name h.symbol
  refine ⟨hdec, hsup, hmin, hname ▸ hn, hsym ▸ hy, fun k hk => ?_, fun k hk => ?_, fun y hy' => ?_,
    h.inj, h.apart, hcons⟩
  · rw [Stor.get_set_ne _ (fun e : x = k.slot => h.apart k hk (e ▸ hxf)), hval]
    exact h.known k hk
  · rw [hval]; exact h.unknown k hk
  · by_cases hyx : x = y
    · exact .inl (hyx ▸ hxf)
    · rw [Stor.get_set_ne _ hyx] at hy'
      exact h.support y hy'

/-- Storage that agrees at a string's slots keeps the string. -/
theorem VyStr.congr {stor stor' : Stor} {base : B256} {n : Nat} {bs : Bytes}
    (h0 : stor'.get base = stor.get base)
    (hj : ∀ j < n, stor'.get (base + Nat.toB256 (j + 1)) = stor.get (base + Nat.toB256 (j + 1)))
    (h : VyStr stor base n bs) : VyStr stor' base n bs := by
  have hw : vyStrWords stor' base n = vyStrWords stor base n := by
    unfold vyStrWords
    simp only [List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro j hjm
    rw [hj j (List.mem_range.mp hjm)]
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [h0]; exact h1, h2, by rw [hw]; exact h3⟩

/-- A fresh or live key's slot is off the fixed slots. -/
theorem VyInv.slot_apart {stor : Stor} {s : Curve3Crv.State} {K : Key → Prop} {k : Key}
    (h : VyInv stor s K) (hk : Fresh K k) : k.slot ∉ vyFixedSlots := by
  rcases hk with hK | ⟨hfix, -⟩
  · exact h.apart k hK
  · exact hfix

/-- **The abstraction after a writer's update**: storage changed only at the touched keys' slots
and some word slots, the touched keys hold their new model values, every other key and both
strings are unchanged in the model, the three words read as the new model's, and the new model
is conserved. -/
theorem VyInv.update {stor stor' : Stor} {s s' : Curve3Crv.State} {K : Key → Prop}
    {ks : List Key} {ws : List B256}
    (h : VyInv stor s K) (hf : FreshKeys K ks) (hws : ∀ x ∈ ws, x ∈ vyWordSlots)
    (hoff : ∀ x, (∀ k ∈ ks, k.slot ≠ x) → x ∉ ws → stor'.get x = stor.get x)
    (hkeys : ∀ k ∈ ks, stor'.get k.slot = k.val s')
    (hval : ∀ k, k ∉ ks → k.val s' = k.val s)
    (hname : s'.name = s.name) (hsym : s'.symbol = s.symbol)
    (hdec : stor'.get vyDecimalsSlot = s'.decimals)
    (hsup : stor'.get vySupplySlot = s'.totalSupply)
    (hmin : stor'.get vyMinterSlot = s'.minter.toB256) (hcons : Curve3Crv.Conserved s') :
    VyInv stor' s' (Key.extend K ks) := by
  have hstr := vyStrSlots_apart.1
  -- a string slot is written by no key and no word store
  have hkeep : ∀ x, x ∈ vyNameSlots ++ vySymbolSlots → stor'.get x = stor.get x := by
    intro x hx
    apply hoff
    · intro k hk he
      apply h.slot_apart (hf.1 k hk)
      rw [he]
      simp only [List.mem_append, vyNameSlots, vySymbolSlots, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      simp only [vyFixedSlots, List.mem_cons, List.not_mem_nil, or_false]
      rcases hx with (rfl | rfl | rfl) | (rfl | rfl) <;> simp
    · intro hw
      exact hstr x hx x (hws x hw) rfl
  refine ⟨hdec, hsup, hmin, ?_, ?_, fun k hk => ?_, fun k hk => ?_, fun y hy => ?_, ?_, ?_,
    hcons⟩
  · rw [hname]
    refine h.name.congr (hkeep _ (by simp [vyNameSlots])) (fun j hj => hkeep _ ?_)
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp [vyNameSlots]
  · rw [hsym]
    refine h.symbol.congr (hkeep _ (by simp [vySymbolSlots])) (fun j hj => hkeep _ ?_)
    have : j = 0 := by omega
    subst this; simp [vySymbolSlots]
  · by_cases hks : k ∈ ks
    · exact hkeys k hks
    · have hK : K k := hk.resolve_right hks
      rw [hval k hks, hoff _ ?_ ?_]
      · exact h.known k hK
      · intro k' hk' he
        rcases hf.1 k' hk' with hK' | ⟨-, hoff'⟩
        · exact hks (h.inj k k' hK hK' he.symm ▸ hk')
        · exact hoff' k hK he.symm
      · intro hw
        exact h.apart k hK (by
          have := hws _ hw
          simp only [vyWordSlots, List.mem_cons, List.not_mem_nil, or_false] at this
          rcases this with h1 | h1 | h1 <;> rw [h1] <;> simp [vyFixedSlots])
  · have hks : k ∉ ks := fun h' => hk (.inr h')
    rw [hval k hks]
    exact h.unknown k (fun h' => hk (.inl h'))
  · by_cases hk : ∃ k ∈ ks, k.slot = y
    · obtain ⟨k, hk, he⟩ := hk
      exact .inr ⟨k, .inr hk, he⟩
    · push Not at hk
      by_cases hw : y ∈ ws
      · left
        have := hws _ hw
        simp only [vyWordSlots, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with h1 | h1 | h1 <;> rw [h1] <;> simp [vyFixedSlots]
      · rw [hoff y hk hw] at hy
        rcases h.support y hy with hx | ⟨k, hK, he⟩
        · exact .inl hx
        · exact .inr ⟨k, .inl hK, he⟩
  · intro k k' hk hk' he
    rcases hk with hk | hk <;> rcases hk' with hk' | hk'
    · exact h.inj k k' hk hk' he
    · rcases hf.1 k' hk' with hK' | ⟨-, hoff'⟩
      · exact h.inj k k' hk hK' he
      · exact absurd he (hoff' k hk)
    · rcases hf.1 k hk with hK | ⟨-, hoff'⟩
      · exact h.inj k k' hK hk' he
      · exact absurd he.symm (hoff' k' hk')
    · exact hf.2 k hk k' hk' he
  · intro k hk
    rcases hk with hk | hk
    · exact h.apart k hk
    · exact h.slot_apart (hf.1 k hk)

theorem toB256_inj_adr {a b : Adr} (h : a.toB256 = b.toB256) : a = b := by
  have := congrArg B256.toAdr h
  simpa only [toAdr_toB256] using this

/-! ## The string copy's storage -/

theorem sliceD_zero_take (bs : Bytes) {n : Nat} (h : n ≤ bs.length) :
    bs.sliceD 0 n 0 = bs.take n := by
  unfold List.sliceD
  rw [List.drop_zero, List.takeD_eq_take _ h]

theorem vyCopyStore_succ (stor : Stor) (base : B256) (src : Bytes) (n : Nat) :
    vyCopyStore stor base src (n + 1) = (vyCopyStore stor base src n).set (base + Nat.toB256 n)
      (Bytes.toB256 (src.sliceD (32 * n) 32 0)) := by
  unfold vyCopyStore
  rw [List.range_succ, List.foldl_append]
  rfl

theorem add_toB256_inj {base : B256} {i j : Nat} (hi : i < 2 ^ 256) (hj : j < 2 ^ 256)
    (h : base + Nat.toB256 i = base + Nat.toB256 j) : i = j := by
  have := congrArg B256.toNat h
  rw [B256.toNat_add, B256.toNat_add, B256.toNat_toB256_of_lt hi, B256.toNat_toB256_of_lt hj,
    Nat.lo, Nat.lo] at this
  have := B256.toNat_lt base
  omega

/-- The copy leaves every slot it does not write. -/
theorem vyCopyStore_get_off {stor : Stor} {base x : B256} {src : Bytes} {n : Nat}
    (h : ∀ i < n, base + Nat.toB256 i ≠ x) : (vyCopyStore stor base src n).get x = stor.get x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [vyCopyStore_succ, Stor.get_set_ne _ (h n (by omega)), ih (fun i hi => h i (by omega))]

/-- The copy's word `i`. -/
theorem vyCopyStore_get_at {stor : Stor} {base : B256} {src : Bytes} {n i : Nat} (hi : i < n)
    (hn : n ≤ 2 ^ 256) :
    (vyCopyStore stor base src n).get (base + Nat.toB256 i) =
      Bytes.toB256 (src.sliceD (32 * i) 32 0) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [vyCopyStore_succ]
    by_cases hin : i = n
    · subst hin; rw [Stor.get_set_self]
    · rw [Stor.get_set_ne _ (fun he => hin (add_toB256_inj (by omega) (by omega) he).symm),
        ih (by omega) (by omega)]

theorem add_toB256_zero (base : B256) : base + Nat.toB256 0 = base := by
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_toB256_of_lt (by decide), Nat.add_zero,
    Nat.lo_eq_of_lt (B256.toNat_lt _)]

/-- The copy's word `0`, at the base itself. -/
theorem vyCopyStore_get_zero {stor : Stor} {base : B256} {src : Bytes} {n : Nat} (hn : 0 < n)
    (hn' : n ≤ 2 ^ 256) :
    (vyCopyStore stor base src n).get base = Bytes.toB256 (src.sliceD 0 32 0) := by
  have h := vyCopyStore_get_at (stor := stor) (base := base) (src := src) hn hn'
  rwa [add_toB256_zero] at h

/-- A string word written by the copy, as bytes. -/
theorem vyCopyStore_bytes_at {stor : Stor} {base : B256} {src : Bytes} {n i : Nat} (hi : i < n)
    (hn : n ≤ 2 ^ 256) :
    ((vyCopyStore stor base src n).get (base + Nat.toB256 i)).toBytes = src.sliceD (32 * i) 32 0 := by
  rw [vyCopyStore_get_at hi hn]
  exact Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)

section Segments

variable {sevm : Sevm} {stor : Stor} {s : Curve3Crv.State} {K : Key → Prop} {ow : Option B256}

-- SEGMENT: refineSetMinter (pure, short)
/-- `set_minter`.  Proof sketch: unfold `rawSetMinter`, `step`, `setMinter`; the guards agree
(`VyInv.minter`: `stor.get 6 = s.minter.toB256`, and `Adr.toB256` is injective); the new storage
differs at slot 6 only, a fixed slot, so every `VyInv` field but `minter` transfers
(`Stor.get_set_ne` with `apart`, `support` gains nothing new); `minter`: `m.toAdr.toB256 = m`
for `m < 2^160`.  No keys. -/
theorem refine_setMinter (hinv : VyInv stor s K)
    (_hf : FreshKeys K (callKeys sevm.caller (callAt sevm 0))) :
    RawRefines sevm (rawOf 0 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 0) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 0))) := by
  have hcall : stor.get vyMinterSlot = sevm.caller.toB256 ↔ sevm.caller = s.minter := by
    rw [hinv.minter]
    exact ⟨fun e => (toB256_inj_adr e).symm, fun e => by rw [e]⟩
  refine RawRefines.of_iff (stor.set vyMinterSlot (Sevm.argWord sevm 0), [], none)
    ({s with minter := (Sevm.argWord sevm 0).toAdr}, [], .stop)
    (sevm.value = 0 ∧ (Sevm.argWord sevm 0).toNat < 2 ^ 160 ∧ sevm.caller = s.minter) ?_ ?_ ?_
  · intro r
    simp only [rawOf, rawSetMinter, hcall]
    split_ifs <;> simp_all [eq_comm]
  · intro o
    simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx]
    by_cases hv : sevm.value = 0
    · simp only [hv, ite_true, Curve3Crv.setMinter_eq_ok, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · simp [hv]
  · rintro ⟨-, hm, -⟩
    refine ⟨?_, rfl, rfl⟩
    have hext : Key.extend K (callKeys sevm.caller (callAt sevm 0)) = K := by
      funext k; simp [Key.extend, SlotFootprint.extendBy, callKeys, callAt]
    rw [hext]
    refine hinv.of_set_word (by simp [vyWordSlots]) rfl rfl rfl rfl ?_ ?_ ?_ hinv.conserved
    · rw [Stor.get_set_ne _ (by decide)]; exact hinv.decimals
    · rw [Stor.get_set_ne _ (by decide)]; exact hinv.supply
    · rw [Stor.get_set_self]; exact (B256.toAdr_toB256_of_lt hm).symm

-- SEGMENT: refineSetName (pure, medium: the string words)
/-- `set_name`.  Proof sketch: the guards agree (`strArg`'s length is the length word;
`c3ctx`'s `ownerOf` is `ow` at every address).  The new storage is `vyCopyStore` twice: the
name's `min 3 ((32 + L0)/32 + 1)` words at `vyNameBase + i`, the symbol's at `vySymbolBase + i`;
all eight string slots are in `vyFixedSlots`, pairwise distinct and distinct from 2, 5, 6
(`vyFixedSlots_nodup`, a kernel `decide` on two Keccak digests — put it in its own file, out of
the language server's way), so live keys and the three words are untouched.  `VyStr` for the new
name: the length word is `L0`; the first `L0` bytes of the two data words are the calldata's
content bytes (`vyStrWords` of the stored words is `(data.sliceD (s0+32) 64 0)` up to the words
the loop wrote, which cover `L0` bytes: `L0 ≤ 32 ((32 + L0)/32)`); likewise the symbol. -/
theorem refine_setName (hinv : VyInv stor s K)
    (hf : FreshKeys K (callKeys sevm.caller (callAt sevm 1))) :
    RawRefines sevm (rawOf 1 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 1) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 1))) := by
  clear hf
  set s0 := Sevm.argWord sevm 0 + 4
  set s1 := Sevm.argWord sevm 1 + 4
  set L0 := (Sevm.dataWord sevm s0).toNat with hL0def
  set L1 := (Sevm.dataWord sevm s1).toNat with hL1def
  set src0 := sevm.data.sliceD s0.toNat 96 0
  set src1 := sevm.data.sliceD s1.toNat 64 0
  set n0 := min 3 ((32 + L0) / 32 + 1)
  set n1 := min 2 ((32 + L1) / 32 + 1)
  set T := vyCopyStore (vyCopyStore stor vyNameBase src0 n0) vySymbolBase src1 n1
  have hkeys : callKeys sevm.caller (callAt sevm 1) = [] := rfl
  rw [hkeys]
  refine RawRefines.of_iff (T, [], none)
    ({ s with name := strArg sevm 0, symbol := strArg sevm 1 }, [], .stop)
    (sevm.value = 0 ∧ L0 ≤ 64 ∧ L1 ≤ 32 ∧ ow = some sevm.caller.toB256) ?_ ?_ ?_
  · intro r
    show rawSetName sevm stor ow = some r ↔ _
    unfold rawSetName
    dsimp only
    split_ifs with h
    · exact ⟨fun h' => ⟨h, (Option.some.inj h').symm⟩, fun ⟨_, h'⟩ => h' ▸ rfl⟩
    · exact ⟨fun h' => absurd h' (by simp), fun ⟨hP, _⟩ => absurd hP h⟩
  · intro o
    have hl0 : (strArg sevm 0).length = L0 := List.length_sliceD _ _ _ _
    have hl1 : (strArg sevm 1).length = L1 := List.length_sliceD _ _ _ _
    simp only [callAt, Curve3Crv.step, Curve3Crv.body, Curve3Crv.setName, c3ctx, hl0, hl1]
    clear hL0def hL1def
    rcases ow with _ | w <;> split_ifs <;> simp [*, eq_comm]
    by_cases hw : w = sevm.caller.toB256 <;> simp [hw, eq_comm]
  rintro ⟨-, hL0, hL1, -⟩
  refine ⟨?_, rfl, rfl⟩
  -- the written slots
  have hname : ∀ i < 3, vyNameBase + Nat.toB256 i ∈ vyNameSlots := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [add_toB256_zero]; simp [vyNameSlots]
    · simp [vyNameSlots]
    · simp [vyNameSlots]
  have hsym : ∀ i < 2, vySymbolBase + Nat.toB256 i ∈ vySymbolSlots := by
    intro i hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · rw [add_toB256_zero]; simp [vySymbolSlots]
    · simp [vySymbolSlots]
  have hn0 : n0 ≤ 3 := Nat.min_le_left _ _
  have hn0' : 2 ≤ n0 := by simp only [n0]; omega
  have hn1 : n1 = 2 := by simp only [n1]; omega
  have hfix : ∀ x, x ∈ vyNameSlots ++ vySymbolSlots → x ∈ vyFixedSlots := by
    intro x hx
    simp only [List.mem_append, vyNameSlots, vySymbolSlots, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with (rfl | rfl | rfl) | (rfl | rfl) <;> simp [vyFixedSlots]
  have hoff : ∀ x, x ∉ vyNameSlots ++ vySymbolSlots → T.get x = stor.get x := by
    intro x hx
    rw [vyCopyStore_get_off (fun i hi he =>
        hx (List.mem_append_right _ (by rw [← he]; exact hsym i (by omega)))),
      vyCopyStore_get_off (fun i hi he =>
        hx (List.mem_append_left _ (by rw [← he]; exact hname i (by omega))))]
  have hsymoff : ∀ i < 3, T.get (vyNameBase + Nat.toB256 i) =
      (vyCopyStore stor vyNameBase src0 n0).get (vyNameBase + Nat.toB256 i) := by
    intro i hi
    exact vyCopyStore_get_off (fun j hj he =>
      vyStrSlots_apart.2 _ (hname i hi) _ (hsym j (by omega)) he.symm)
  have hword : ∀ x ∈ vyWordSlots, T.get x = stor.get x := by
    intro x hx
    exact hoff x (fun hs => vyStrSlots_apart.1 x hs x hx rfl)
  have hw0 : ∀ (src : Bytes) (s' : B256), src = sevm.data.sliceD s'.toNat src.length 0 →
      32 ≤ src.length → Bytes.toB256 (src.sliceD 0 32 0) = Sevm.dataWord sevm s' := by
    intro src s' hsrc hlen
    rw [hsrc, Bytes.sliceD_sliceD_of_le _ _ _ _ _ hlen, Nat.add_zero]; rfl
  have hsl : ∀ (s' : B256) (w L : Nat), 32 + L ≤ w →
      (sevm.data.sliceD s'.toNat w 0).sliceD 32 L 0 = sevm.data.sliceD (s'.toNat + 32) L 0 :=
    fun s' w L h => Bytes.sliceD_sliceD_of_le _ _ _ _ _ h
  refine ⟨?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_, fun y hy => ?_, ?_, ?_,
    hinv.conserved⟩
  · rw [hword _ (by simp [vyWordSlots])]; exact hinv.decimals
  · rw [hword _ (by simp [vyWordSlots])]; exact hinv.supply
  · rw [hword _ (by simp [vyWordSlots])]; exact hinv.minter
  · -- the new name
    have hlen0 : (strArg sevm 0).length = L0 := List.length_sliceD _ _ _ _
    refine ⟨?_, by rw [hlen0]; omega, ?_⟩
    · have h0 := hsymoff 0 (by omega)
      rw [add_toB256_zero] at h0
      show _ = (strArg sevm 0).length
      rw [h0, vyCopyStore_get_zero (by omega) (by omega),
        hw0 src0 s0 (by rw [List.length_sliceD]) (by rw [List.length_sliceD]; omega), hlen0]
    · have hW : vyStrWords T vyNameBase 2 =
          (T.get (vyNameBase + Nat.toB256 1)).toBytes ++ (T.get (vyNameBase + Nat.toB256 2)).toBytes := by
        simp [vyStrWords, List.range_succ]
      rw [hW, hlen0, hsymoff 1 (by omega), vyCopyStore_bytes_at (by omega) (by omega)]
      by_cases h32 : L0 ≤ 32
      · rw [List.take_append_of_le_length (by rw [List.length_sliceD]; omega),
          ← sliceD_zero_take _ (by rw [List.length_sliceD]; omega),
          Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by omega), Nat.add_zero, hsl s0 96 L0 (by omega)]
        rfl
      · rw [hsymoff 2 (by omega), vyCopyStore_bytes_at (by simp only [n0]; omega) (by omega),
          show 32 * 1 = 32 from rfl, show 32 * 2 = 32 + 32 from rfl, ← List.sliceD_split,
          ← sliceD_zero_take _ (by rw [List.length_sliceD]; omega),
          Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by omega), Nat.add_zero, hsl s0 96 L0 (by omega)]
        rfl
  · -- the new symbol
    have hlen1 : (strArg sevm 1).length = L1 := List.length_sliceD _ _ _ _
    refine ⟨?_, by rw [hlen1]; omega, ?_⟩
    · show _ = (strArg sevm 1).length
      rw [vyCopyStore_get_zero (by omega) (by omega),
        hw0 src1 s1 (by rw [List.length_sliceD]) (by rw [List.length_sliceD]; omega), hlen1]
    · have hW : vyStrWords T vySymbolBase 1 = (T.get (vySymbolBase + Nat.toB256 1)).toBytes := by
        simp [vyStrWords]
      rw [hW, hlen1, vyCopyStore_bytes_at (by omega) (by omega),
        ← sliceD_zero_take _ (by rw [List.length_sliceD]; omega),
        Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by omega), Nat.add_zero, hsl s1 64 L1 (by omega)]
      rfl
  · have hK : K k := by simpa [Key.extend, SlotFootprint.extendBy] using hk
    rw [hoff _ (fun hs => hinv.apart k hK (hfix _ hs))]
    cases k <;> exact hinv.known _ hK
  · have hK : ¬ K k := fun h => hk (.inl h)
    cases k <;> exact hinv.unknown _ hK
  · by_cases hs : y ∈ vyNameSlots ++ vySymbolSlots
    · exact .inl (hfix y hs)
    · rw [hoff y hs] at hy
      rcases hinv.support y hy with hx | ⟨k, hK, he⟩
      · exact .inl hx
      · exact .inr ⟨k, .inl hK, he⟩
  · intro k k' hk hk' he
    simp only [Key.extend, SlotFootprint.extendBy, List.not_mem_nil, or_false] at hk hk'
    exact hinv.inj k k' hk hk' he
  · intro k hk
    simp only [Key.extend, SlotFootprint.extendBy, List.not_mem_nil, or_false] at hk
    exact hinv.apart k hk

-- SEGMENT: refineWordViews (pure, short; four views)
/-- `totalSupply`, `decimals`, `balanceOf`, `allowance`.  Proof sketch: storage unchanged, the
model state unchanged, no events; the return word is `VyInv.supply`/`decimals`, or
`VyInv.get_slot` for the fresh key (`mapSlot 3 h = (Key.bal h.toAdr).slot` since
`h.toAdr.toB256 = h` below `2^160`).  `VyInv` over `K` extended by a fresh key: its slot
reads `0 = val` (`get_slot`), injectivity and `apart` from `Fresh`. -/
theorem refine_wordView {k : Nat} (hk : k = 2 ∨ k = 3 ∨ k = 11 ∨ k = 12) (hinv : VyInv stor s K)
    (hf : FreshKeys K (callKeys sevm.caller (callAt sevm k))) :
    RawRefines sevm (rawOf k sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm k) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm k))) := by
  have hext := hinv.extend hf
  rcases hk with rfl | rfl | rfl | rfl
  · refine RawRefines.of_iff (stor, [], some (stor.get vySupplySlot).toBytes)
      (s, [], .word s.totalSupply) (sevm.value = 0) ?_ ?_ ?_
    · intro r; simp only [rawOf, rawTotalSupply]; split_ifs <;> simp_all [eq_comm]
    · intro o
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, Curve3Crv.totalSupplyView, c3ctx]
      split_ifs <;> simp_all [eq_comm]
    · intro _
      exact ⟨hext, rfl, by simp only [RetMatch, RetOut, hinv.supply]⟩
  · refine RawRefines.of_iff (stor, [], some (stor.get (mapSlot (mapSlot 4
      (Sevm.argWord sevm 0)) (Sevm.argWord sevm 1))).toBytes) (s, [], .word (s.allowances (Sevm.argWord sevm 0).toAdr
      (Sevm.argWord sevm 1).toAdr)) (sevm.value = 0 ∧ (Sevm.argWord sevm 0).toNat < 2 ^ 160 ∧
      (Sevm.argWord sevm 1).toNat < 2 ^ 160) ?_ ?_ ?_
    · intro r; simp only [rawOf, rawAllowance]; split_ifs <;> simp_all [eq_comm]
    · intro o
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, Curve3Crv.allowanceView, c3ctx]
      by_cases h1 : sevm.value = 0
      · simp only [h1, ite_true, true_and]
        split_ifs <;> simp_all [eq_comm]
      · simp [h1]
    · rintro ⟨-, h0, h1⟩
      refine ⟨hext, rfl, ?_⟩
      have hs := hinv.get_slot (hf.1 _ (List.mem_singleton_self _))
      simp only [Key.slot, Key.val, vyAllowSlot, B256.toAdr_toB256_of_lt h0,
        B256.toAdr_toB256_of_lt h1] at hs
      simp only [RetMatch, RetOut]
      rw [hs]
  · refine RawRefines.of_iff (stor, [], some (stor.get vyDecimalsSlot).toBytes)
      (s, [], .word s.decimals) (sevm.value = 0) ?_ ?_ ?_
    · intro r; simp only [rawOf, rawDecimals]; split_ifs <;> simp_all [eq_comm]
    · intro o
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, Curve3Crv.decimalsView, c3ctx]
      split_ifs <;> simp_all [eq_comm]
    · intro _
      exact ⟨hext, rfl, by simp only [RetMatch, RetOut, hinv.decimals]⟩
  · refine RawRefines.of_iff (stor, [], some (stor.get (mapSlot 3 (Sevm.argWord sevm 0))).toBytes)
      (s, [], .word (s.balanceOf (Sevm.argWord sevm 0).toAdr))
      (sevm.value = 0 ∧ (Sevm.argWord sevm 0).toNat < 2 ^ 160) ?_ ?_ ?_
    · intro r; simp only [rawOf, rawBalanceOf]; split_ifs <;> simp_all [eq_comm]
    · intro o
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, Curve3Crv.balanceOfView, c3ctx]
      by_cases h1 : sevm.value = 0
      · simp only [h1, ite_true, true_and]
        split_ifs <;> simp_all [eq_comm]
      · simp [h1]
    · rintro ⟨-, h0⟩
      refine ⟨hext, rfl, ?_⟩
      have hs := hinv.get_slot (hf.1 _ (List.mem_singleton_self _))
      simp only [Key.slot, Key.val, vyBalSlot, B256.toAdr_toB256_of_lt h0] at hs
      simp only [RetMatch, RetOut]
      rw [hs]

-- SEGMENT: refineStringViews (pure, short)
/-- `name`, `symbol`.  Proof sketch: `VyInv.name`/`symbol` give the length bound and
`vyStrOf stor base n = s.name` (`VyStr`'s third clause is exactly `vyStrOf`); the return data is
`abiString` of it on both sides. -/
theorem refine_stringView {k : Nat} (hk : k = 9 ∨ k = 10) (hinv : VyInv stor s K)
    (hf : FreshKeys K (callKeys sevm.caller (callAt sevm k))) :
    RawRefines sevm (rawOf k sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm k) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm k))) := by
  have hext := hinv.extend hf
  have hstr : ∀ {base n bs}, VyStr stor base n bs → vyStrOf stor base n = bs := by
    intro base n bs h
    rw [vyStrOf, h.1]
    exact h.2.2.symm
  rcases hk with rfl | rfl
  · obtain ⟨hl, hle, -⟩ := hinv.name
    refine RawRefines.of_iff (stor, [], some (abiString s.name)) (s, [], .string s.name)
      (sevm.value = 0) ?_ ?_ ?_
    · intro r
      simp only [rawOf, rawName, hl, hstr hinv.name]
      split_ifs <;> simp_all [eq_comm]
    · intro o
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, Curve3Crv.nameView, c3ctx]
      split_ifs <;> simp_all [eq_comm]
    · intro _
      exact ⟨hext, rfl, rfl⟩
  · obtain ⟨hl, hle, -⟩ := hinv.symbol
    refine RawRefines.of_iff (stor, [], some (abiString s.symbol)) (s, [], .string s.symbol)
      (sevm.value = 0) ?_ ?_ ?_
    · intro r
      simp only [rawOf, rawSymbol, hl, hstr hinv.symbol]
      split_ifs <;> simp_all [eq_comm]
    · intro o
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, Curve3Crv.symbolView, c3ctx]
      split_ifs <;> simp_all [eq_comm]
    · intro _
      exact ⟨hext, rfl, rfl⟩

-- SEGMENT: refineTransfer (pure, medium)
/-- `transfer`.  Proof sketch: `get_slot` for `bal caller` and `bal d` (both fresh) turns the raw
reads into the model's balances; with `a = caller`, `d' = d.toAdr`: if `d' = a` the second read
is of the first write (`Stor.get_set_self`), matching `ledgerDebit … d'` at `a`; otherwise the
slots differ (`inj` for live keys, `Fresh` otherwise) and `Stor.get_set_ne`.  The new storage
abstracts `ledgerCredit (ledgerDebit …)` on the two keys, everything else is unchanged;
`support` gains exactly the two slots, now live; `conserved` by the model's `step_conserved`.
The log entry is `eventLog` of `.transfer a d' v` (`d'.toB256 = d`). -/
theorem refine_transfer (hinv : VyInv stor s K)
    (hf : FreshKeys K (callKeys sevm.caller (callAt sevm 4))) :
    RawRefines sevm (rawOf 4 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 4) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 4))) := by
  set a := sevm.caller with ha_def
  set d := Sevm.argWord sevm 0 with hd_def
  set v := Sevm.argWord sevm 1 with hv_def
  set f := s.balanceOf with hf_def
  have hks : callKeys a (callAt sevm 4) = [.bal a, .bal d.toAdr] := rfl
  have hfa : stor.get (vyBalSlot a) = f a := hinv.get_slot (hf.1 (.bal a) (by simp [hks]))
  by_cases hd : d.toNat < 2 ^ 160
  swap
  · refine ⟨fun r hr => ?_, fun o ho => ?_⟩
    · simp only [rawOf, rawTransfer] at hr
      split_ifs at hr with hc
      exact absurd hc.2.1 hd
    · simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx] at ho
      by_cases hv : sevm.value = 0
      · simp only [hv, ite_true] at ho
        exact absurd (Curve3Crv.transfer_eq_ok.mp ho).1 hd
      · simp [hv] at ho
  set d' := d.toAdr
  have hs2 : mapSlot 3 d = vyBalSlot d' := by
    simp only [vyBalSlot, d', B256.toAdr_toB256_of_lt hd]
  have hfd : stor.get (vyBalSlot d') = f d' := hinv.get_slot (hf.1 (.bal d') (by simp [hks]))
  have hne : a ≠ d' → vyBalSlot a ≠ vyBalSlot d' := fun h e =>
    h (Key.bal.inj (hf.2 (.bal a) (by simp [hks]) (.bal d') (by simp [hks]) e))
  have hy : ((stor.set (vyBalSlot a) (f a - v)).get (vyBalSlot d')) = ledgerDebit f a v d' := by
    by_cases had : d' = a
    · rw [had, Stor.get_set_self, ledgerDebit_self]
    · rw [Stor.get_set_ne _ (hne (Ne.symm had)), ledgerDebit_ne _ had, hfd]
  set s' : Curve3Crv.State := { s with balanceOf := ledgerCredit (ledgerDebit f a v) d' v }
  refine RawRefines.of_iff ((stor.set (vyBalSlot a) (f a - v)).set (vyBalSlot d') (ledgerDebit f a v d' + v),
      [⟨sevm.currentTarget, [transferTopic, a.toB256, d], v.toBytes⟩], some (1 : B256).toBytes)
    (s', [.transfer a d' v], .bool true)
    (sevm.value = 0 ∧ v ≤ f a ∧ (ledgerDebit f a v d').toNat + v.toNat < 2 ^ 256) ?_ ?_ ?_
  · intro r
    simp only [rawOf, rawTransfer, ← ha_def, ← hd_def, ← hv_def]
    rw [hs2, hfa, hy]
    split_ifs with hc <;> simp_all [eq_comm]
  · intro o
    simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx]
    by_cases hv : sevm.value = 0
    · simp only [hv, ite_true, Curve3Crv.transfer_eq_ok, true_and, B256.Nof]
      constructor
      · rintro ⟨-, h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨hd, h1, h2, h3⟩
    · simp [hv]
  · rintro ⟨hv, hle, hnof⟩
    have hstep : Curve3Crv.step (c3ctx sevm ow) (callAt sevm 4) s =
        .ok (s', [.transfer a d' v], .bool true) := by
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx, hv, ite_true]
      exact Curve3Crv.transfer_eq_ok.mpr ⟨hd, hle, hnof, rfl⟩
    refine ⟨?_, ?_, rfl⟩
    · rw [hks]
      refine hinv.update (ws := []) (hf := hks ▸ hf) (by simp) ?_ ?_ ?_ rfl rfl ?_ ?_ ?_
        (Curve3Crv.step_conserved hinv.conserved hstep)
      · intro x hx _
        dsimp only
        have h1 := hx (.bal a) (by simp)
        have h2 := hx (.bal d') (by simp)
        rw [Stor.get_set_ne (k := vyBalSlot d') _ h2, Stor.get_set_ne (k := vyBalSlot a) _ h1]
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · show ((stor.set (vyBalSlot a) (f a - v)).set (vyBalSlot d') (ledgerDebit f a v d' + v)).get (vyBalSlot a) =
            ledgerCredit (ledgerDebit f a v) d' v a
          by_cases had : d' = a
          · rw [had, Stor.get_set_self, ledgerCredit_self]
          · rw [Stor.get_set_ne _ (hne (Ne.symm had)).symm, ledgerCredit_ne _ (Ne.symm had),
              ledgerDebit_self, Stor.get_set_self]
        · show ((stor.set (vyBalSlot a) (f a - v)).set (vyBalSlot d') (ledgerDebit f a v d' + v)).get (vyBalSlot d') =
            ledgerCredit (ledgerDebit f a v) d' v d'
          rw [Stor.get_set_self, ledgerCredit_self]
      · intro k hk
        cases k with
        | bal c =>
          simp only [List.mem_cons, Key.bal.injEq, List.not_mem_nil, or_false, not_or] at hk
          show ledgerCredit (ledgerDebit f a v) d' v c = f c
          rw [ledgerCredit_ne _ hk.2, ledgerDebit_ne _ hk.1]
        | allow o p => rfl
      · dsimp only
        rw [Stor.get_set_ne _ ?_, Stor.get_set_ne _ ?_]
        · exact hinv.decimals
        · exact fun e => hinv.slot_apart (hf.1 (.bal a) (by simp [hks])) (by
            rw [show (Key.bal a).slot = vyBalSlot a from rfl, e]; simp [vyFixedSlots])
        · exact fun e => hinv.slot_apart (hf.1 (.bal d') (by simp [hks])) (by
            rw [show (Key.bal d').slot = vyBalSlot d' from rfl, e]; simp [vyFixedSlots])
      · dsimp only
        rw [Stor.get_set_ne _ ?_, Stor.get_set_ne _ ?_]
        · exact hinv.supply
        · exact fun e => hinv.slot_apart (hf.1 (.bal a) (by simp [hks])) (by
            rw [show (Key.bal a).slot = vyBalSlot a from rfl, e]; simp [vyFixedSlots])
        · exact fun e => hinv.slot_apart (hf.1 (.bal d') (by simp [hks])) (by
            rw [show (Key.bal d').slot = vyBalSlot d' from rfl, e]; simp [vyFixedSlots])
      · dsimp only
        rw [Stor.get_set_ne _ ?_, Stor.get_set_ne _ ?_]
        · exact hinv.minter
        · exact fun e => hinv.slot_apart (hf.1 (.bal a) (by simp [hks])) (by
            rw [show (Key.bal a).slot = vyBalSlot a from rfl, e]; simp [vyFixedSlots])
        · exact fun e => hinv.slot_apart (hf.1 (.bal d') (by simp [hks])) (by
            rw [show (Key.bal d').slot = vyBalSlot d' from rfl, e]; simp [vyFixedSlots])
    · simp only [List.map, eventLog, List.cons.injEq, and_true]
      rw [B256.toAdr_toB256_of_lt hd]

-- SEGMENT: refineTransferFrom (pure, medium-long)
/-- The non-minter (allowance-spending) case of `refine_transferFrom`, split into its own
declaration so its proof gets a fresh heartbeat budget: the shared preamble plus this branch
alone already approaches the elaborator's default limit inside one declaration. -/
private theorem refine_transferFrom_spend (hinv : VyInv stor s K)
    (hf : FreshKeys K (callKeys sevm.caller (callAt sevm 5))) (hmint : sevm.caller ≠ s.minter) :
    RawRefines sevm (rawOf 5 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 5) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 5))) := by
  set a := sevm.caller with ha_def
  set f := Sevm.argWord sevm 0 with hf_def
  set d := Sevm.argWord sevm 1 with hd_def
  set v := Sevm.argWord sevm 2 with hv_def
  set bf := s.balanceOf with hbf_def
  have hks : callKeys a (callAt sevm 5) = [.bal f.toAdr, .bal d.toAdr, .allow f.toAdr a] := rfl
  by_cases hfr : f.toNat < 2 ^ 160
  swap
  · refine ⟨fun r hr => ?_, fun o ho => ?_⟩
    · simp only [rawOf, rawTransferFrom] at hr
      split_ifs at hr with hc <;> exact absurd hc.2.1 hfr
    · simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx] at ho
      by_cases hv0 : sevm.value = 0
      · simp only [hv0, ite_true] at ho
        exact absurd (Curve3Crv.transferFrom_eq_ok.mp ho).1 hfr
      · simp [hv0] at ho
  by_cases hdr : d.toNat < 2 ^ 160
  swap
  · refine ⟨fun r hr => ?_, fun o ho => ?_⟩
    · simp only [rawOf, rawTransferFrom] at hr
      split_ifs at hr with hc <;> exact absurd hc.2.2.1 hdr
    · simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx] at ho
      by_cases hv0 : sevm.value = 0
      · simp only [hv0, ite_true] at ho
        exact absurd (Curve3Crv.transferFrom_eq_ok.mp ho).2.1 hdr
      · simp [hv0] at ho
  set f' := f.toAdr with hf'_def
  set d' := d.toAdr with hd'_def
  have hs1 : mapSlot 3 f = vyBalSlot f' := by
    simp only [vyBalSlot, hf'_def, B256.toAdr_toB256_of_lt hfr]
  have hs2 : mapSlot 3 d = vyBalSlot d' := by
    simp only [vyBalSlot, hd'_def, B256.toAdr_toB256_of_lt hdr]
  have hff : stor.get (vyBalSlot f') = bf f' := hinv.get_slot (hf.1 (.bal f') (by simp [hks]))
  have hfd : stor.get (vyBalSlot d') = bf d' := hinv.get_slot (hf.1 (.bal d') (by simp [hks]))
  have hnebd : f' ≠ d' → vyBalSlot f' ≠ vyBalSlot d' := fun h e =>
    h (Key.bal.inj (hf.2 (.bal f') (by simp [hks]) (.bal d') (by simp [hks]) e))
  have hy : (stor.set (vyBalSlot f') (bf f' - v)).get (vyBalSlot d') = ledgerDebit bf f' v d' := by
    by_cases had : d' = f'
    · rw [had, Stor.get_set_self, ledgerDebit_self]
    · rw [Stor.get_set_ne _ (hnebd (Ne.symm had)), ledgerDebit_ne _ had, hfd]
  have hbf_apart : vyBalSlot f' ≠ vyMinterSlot := fun e =>
    hinv.slot_apart (hf.1 (.bal f') (by simp [hks])) (by
      rw [show (Key.bal f').slot = vyBalSlot f' from rfl, e]; simp [vyFixedSlots])
  have hbd_apart : vyBalSlot d' ≠ vyMinterSlot := fun e =>
    hinv.slot_apart (hf.1 (.bal d') (by simp [hks])) (by
      rw [show (Key.bal d').slot = vyBalSlot d' from rfl, e]; simp [vyFixedSlots])
  set st1 := stor.set (vyBalSlot f') (bf f' - v) with hst1_def
  set st2 := st1.set (vyBalSlot d') (ledgerDebit bf f' v d' + v) with hst2_def
  have hminter2 : st2.get vyMinterSlot = stor.get vyMinterSlot := by
    rw [hst2_def, Stor.get_set_ne _ hbd_apart, hst1_def, Stor.get_set_ne _ hbf_apart]
  set s3 := mapSlot (mapSlot 4 f) a.toB256 with hs3_def
  have hs3eq : s3 = vyAllowSlot f' a := by
    simp only [hs3_def, vyAllowSlot, hf'_def, B256.toAdr_toB256_of_lt hfr]
  have hne_f3 : vyBalSlot f' ≠ s3 := by
    rw [hs3eq]
    intro e
    have heq := hf.2 (.bal f') (by simp [hks]) (.allow f' a) (by simp [hks]) e
    injection heq
  have hne_d3 : vyBalSlot d' ≠ s3 := by
    rw [hs3eq]
    intro e
    have heq := hf.2 (.bal d') (by simp [hks]) (.allow f' a) (by simp [hks]) e
    injection heq
  have hst2s3 : st2.get s3 = stor.get s3 := by
    rw [hst2_def, Stor.get_set_ne _ hne_d3, hst1_def, Stor.get_set_ne _ hne_f3]
  have hz : st2.get s3 = s.allowances f' a := by
    rw [hst2s3, hs3eq]
    exact hinv.get_slot (hf.1 (.allow f' a) (by simp [hks]))
  have hbf_fixed : vyBalSlot f' ∉ vyFixedSlots := hinv.slot_apart (hf.1 (.bal f') (by simp [hks]))
  have hbd_fixed : vyBalSlot d' ∉ vyFixedSlots := hinv.slot_apart (hf.1 (.bal d') (by simp [hks]))
  have hbf_word : ∀ x ∈ vyWordSlots, vyBalSlot f' ≠ x := fun x hx e => hbf_fixed (by
    rw [e]; simp only [vyWordSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [vyFixedSlots])
  have hbd_word : ∀ x ∈ vyWordSlots, vyBalSlot d' ≠ x := fun x hx e => hbd_fixed (by
    rw [e]; simp only [vyWordSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [vyFixedSlots])
  have hs3_fixed : s3 ∉ vyFixedSlots := by
    rw [hs3eq]; exact hinv.slot_apart (hf.1 (.allow f' a) (by simp [hks]))
  have hs3_word : ∀ x ∈ vyWordSlots, s3 ≠ x := fun x hx e => hs3_fixed (by
    rw [e]; simp only [vyWordSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [vyFixedSlots])
  have hfks : FreshKeys K [Key.bal f', Key.bal d', Key.allow f' a] := hks ▸ hf
  have hmint : ¬ a = s.minter := hmint
  -- the caller is not the minter: the allowance is spent
  have hspend : st2.get vyMinterSlot ≠ a.toB256 := by
    rw [hminter2, hinv.minter]
    exact fun he => hmint (toB256_inj_adr he).symm
  set z := st2.get s3 with hz_def
  set s' : Curve3Crv.State := { s with
      balanceOf := ledgerCredit (ledgerDebit bf f' v) d' v,
      allowances := Function.update s.allowances f' (ledgerDebit (s.allowances f') a v) }
    with hs'_def
  set st3 := st2.set s3 (z - v) with hst3_def
  refine RawRefines.of_iff
    (st3, [⟨sevm.currentTarget, [transferTopic, f, d], v.toBytes⟩], some (1 : B256).toBytes)
    (s', [.transfer f' d' v], .bool true)
    (sevm.value = 0 ∧ v ≤ bf f' ∧ (ledgerDebit bf f' v d').toNat + v.toNat < 2 ^ 256 ∧
      v ≤ s.allowances f' a) ?_ ?_ ?_
  · intro r
    simp only [rawOf, rawTransferFrom, ← ha_def, ← hf_def, ← hd_def, ← hv_def]
    rw [hs1, hs2, hff, hy, ← hst1_def, ← hst2_def, if_pos hspend, ← hz_def, ← hst3_def]
    split_ifs with hc <;> simp_all [eq_comm]
  · intro o
    simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx, ← ha_def, ← hf_def, ← hd_def,
      ← hv_def, ← hf'_def, ← hd'_def]
    by_cases hv : sevm.value = 0
    · simp only [hv, ite_true, Curve3Crv.transferFrom_eq_ok, true_and, B256.Nof]
      constructor
      · rintro ⟨-, -, h1, h2, hal, rfl⟩
        refine ⟨⟨h1, h2, hal hmint⟩, ?_⟩
        simp [hs'_def, hmint, hbf_def, hf'_def, hd'_def]
      · rintro ⟨⟨h1, h2, hal⟩, rfl⟩
        exact ⟨hfr, hdr, h1, h2, fun _ => hal,
          by simp [hs'_def, hmint, hbf_def, hf'_def, hd'_def]⟩
    · simp [hv]
  · rintro ⟨hv, hle, hnof, hal⟩
    have hstep : Curve3Crv.step (c3ctx sevm ow) (callAt sevm 5) s =
        .ok (s', [.transfer f' d' v], .bool true) := by
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx, ← ha_def, ← hf_def, ← hd_def,
        ← hv_def, ← hf'_def, ← hd'_def, hv, ite_true]
      exact Curve3Crv.transferFrom_eq_ok.mpr
        ⟨hfr, hdr, hle, hnof, fun _ => hal, by simp [hs'_def, hmint, hbf_def, hf'_def, hd'_def]⟩
    refine And.intro ?_ (And.intro ?_ rfl)
    · have hcons := Curve3Crv.step_conserved hinv.conserved hstep
      rw [hks]
      refine hinv.update (ws := []) (hf := hfks) (by simp) ?_ ?_ ?_ rfl rfl ?_ ?_ ?_ hcons
      · intro x hx _
        have h1 : vyBalSlot f' ≠ x := hx (.bal f') (by simp [hks])
        have h2 : vyBalSlot d' ≠ x := hx (.bal d') (by simp [hks])
        have h3 : s3 ≠ x := by rw [hs3eq]; exact hx (.allow f' a) (by simp [hks])
        rw [hst3_def, Stor.get_set_ne _ h3, hst2_def, Stor.get_set_ne _ h2, hst1_def,
          Stor.get_set_ne _ h1]
      · intro k hk
        simp only [hks, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · dsimp only [Key.slot, Key.val]
          rw [hs'_def]
          dsimp only
          rw [hst3_def, Stor.get_set_ne _ (Ne.symm hne_f3), hst2_def, hst1_def]
          by_cases had : d' = f'
          · rw [had, Stor.get_set_self, ledgerCredit_self]
          · rw [Stor.get_set_ne _ (hnebd (Ne.symm had)).symm, ledgerCredit_ne _ (Ne.symm had),
              ledgerDebit_self, Stor.get_set_self]
        · dsimp only [Key.slot, Key.val]
          rw [hs'_def]
          dsimp only
          rw [hst3_def, Stor.get_set_ne _ (Ne.symm hne_d3), hst2_def, Stor.get_set_self,
            ledgerCredit_self]
        · dsimp only [Key.slot, Key.val]
          rw [hst3_def, ← hs3eq, Stor.get_set_self, hz, hs'_def]
          show s.allowances f' a - v =
            Function.update s.allowances f' (ledgerDebit (s.allowances f') a v) f' a
          rw [Function.update_self, ledgerDebit_self]
      · intro k hk
        cases k with
        | bal c =>
          simp only [hks, List.mem_cons, Key.bal.injEq, List.not_mem_nil, or_false, not_or]
            at hk
          show ledgerCredit (ledgerDebit bf f' v) d' v c = bf c
          rw [ledgerCredit_ne _ hk.2.1, ledgerDebit_ne _ hk.1]
        | allow o p =>
          simp only [hks, List.mem_cons, Key.allow.injEq, List.not_mem_nil, or_false, not_or]
            at hk
          show Function.update s.allowances f' (ledgerDebit (s.allowances f') a v) o p =
            s.allowances o p
          by_cases ho : o = f'
          · subst ho
            rw [Function.update_self]
            exact ledgerDebit_ne v (fun he => hk.2.2 ⟨rfl, he⟩)
          · rw [Function.update_of_ne ho]
      · rw [hst3_def, Stor.get_set_ne _ (hs3_word _ (by simp [vyWordSlots])), hst2_def,
          Stor.get_set_ne _ (hbd_word _ (by simp [vyWordSlots])), hst1_def,
          Stor.get_set_ne _ (hbf_word _ (by simp [vyWordSlots]))]
        exact hinv.decimals
      · rw [hst3_def, Stor.get_set_ne _ (hs3_word _ (by simp [vyWordSlots])), hst2_def,
          Stor.get_set_ne _ (hbd_word _ (by simp [vyWordSlots])), hst1_def,
          Stor.get_set_ne _ (hbf_word _ (by simp [vyWordSlots]))]
        exact hinv.supply
      · rw [hst3_def, Stor.get_set_ne _ (hs3_word _ (by simp [vyWordSlots]))]
        exact hminter2.trans hinv.minter
    · simp only [List.map, eventLog, List.cons.injEq, and_true]
      rw [hf'_def, hd'_def, B256.toAdr_toB256_of_lt hfr, B256.toAdr_toB256_of_lt hdr]

/-- `transferFrom`.  Proof sketch: as `refineTransfer` for the two balance writes, then the
minter test reads slot 6 of the twice-written storage, which is `stor.get 6` (balance slots are
off `vyFixedSlots`); the allowance key `allow f caller` is fresh, so its slot is distinct from
both balance slots, and its read is the model's `s.allowances f caller`; the write matches
`Function.update … (ledgerDebit …)`. -/
theorem refine_transferFrom (hinv : VyInv stor s K)
    (hf : FreshKeys K (callKeys sevm.caller (callAt sevm 5))) :
    RawRefines sevm (rawOf 5 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 5) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 5))) := by
  set a := sevm.caller with ha_def
  set f := Sevm.argWord sevm 0 with hf_def
  set d := Sevm.argWord sevm 1 with hd_def
  set v := Sevm.argWord sevm 2 with hv_def
  set bf := s.balanceOf with hbf_def
  have hks : callKeys a (callAt sevm 5) = [.bal f.toAdr, .bal d.toAdr, .allow f.toAdr a] := rfl
  by_cases hfr : f.toNat < 2 ^ 160
  swap
  · refine ⟨fun r hr => ?_, fun o ho => ?_⟩
    · simp only [rawOf, rawTransferFrom] at hr
      split_ifs at hr with hc <;> exact absurd hc.2.1 hfr
    · simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx] at ho
      by_cases hv0 : sevm.value = 0
      · simp only [hv0, ite_true] at ho
        exact absurd (Curve3Crv.transferFrom_eq_ok.mp ho).1 hfr
      · simp [hv0] at ho
  by_cases hdr : d.toNat < 2 ^ 160
  swap
  · refine ⟨fun r hr => ?_, fun o ho => ?_⟩
    · simp only [rawOf, rawTransferFrom] at hr
      split_ifs at hr with hc <;> exact absurd hc.2.2.1 hdr
    · simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx] at ho
      by_cases hv0 : sevm.value = 0
      · simp only [hv0, ite_true] at ho
        exact absurd (Curve3Crv.transferFrom_eq_ok.mp ho).2.1 hdr
      · simp [hv0] at ho
  set f' := f.toAdr with hf'_def
  set d' := d.toAdr with hd'_def
  have hs1 : mapSlot 3 f = vyBalSlot f' := by
    simp only [vyBalSlot, hf'_def, B256.toAdr_toB256_of_lt hfr]
  have hs2 : mapSlot 3 d = vyBalSlot d' := by
    simp only [vyBalSlot, hd'_def, B256.toAdr_toB256_of_lt hdr]
  have hff : stor.get (vyBalSlot f') = bf f' := hinv.get_slot (hf.1 (.bal f') (by simp [hks]))
  have hfd : stor.get (vyBalSlot d') = bf d' := hinv.get_slot (hf.1 (.bal d') (by simp [hks]))
  have hnebd : f' ≠ d' → vyBalSlot f' ≠ vyBalSlot d' := fun h e =>
    h (Key.bal.inj (hf.2 (.bal f') (by simp [hks]) (.bal d') (by simp [hks]) e))
  have hy : (stor.set (vyBalSlot f') (bf f' - v)).get (vyBalSlot d') = ledgerDebit bf f' v d' := by
    by_cases had : d' = f'
    · rw [had, Stor.get_set_self, ledgerDebit_self]
    · rw [Stor.get_set_ne _ (hnebd (Ne.symm had)), ledgerDebit_ne _ had, hfd]
  have hbf_apart : vyBalSlot f' ≠ vyMinterSlot := fun e =>
    hinv.slot_apart (hf.1 (.bal f') (by simp [hks])) (by
      rw [show (Key.bal f').slot = vyBalSlot f' from rfl, e]; simp [vyFixedSlots])
  have hbd_apart : vyBalSlot d' ≠ vyMinterSlot := fun e =>
    hinv.slot_apart (hf.1 (.bal d') (by simp [hks])) (by
      rw [show (Key.bal d').slot = vyBalSlot d' from rfl, e]; simp [vyFixedSlots])
  set st1 := stor.set (vyBalSlot f') (bf f' - v) with hst1_def
  set st2 := st1.set (vyBalSlot d') (ledgerDebit bf f' v d' + v) with hst2_def
  have hminter2 : st2.get vyMinterSlot = stor.get vyMinterSlot := by
    rw [hst2_def, Stor.get_set_ne _ hbd_apart, hst1_def, Stor.get_set_ne _ hbf_apart]
  set s3 := mapSlot (mapSlot 4 f) a.toB256 with hs3_def
  have hs3eq : s3 = vyAllowSlot f' a := by
    simp only [hs3_def, vyAllowSlot, hf'_def, B256.toAdr_toB256_of_lt hfr]
  have hne_f3 : vyBalSlot f' ≠ s3 := by
    rw [hs3eq]
    intro e
    have heq := hf.2 (.bal f') (by simp [hks]) (.allow f' a) (by simp [hks]) e
    injection heq
  have hne_d3 : vyBalSlot d' ≠ s3 := by
    rw [hs3eq]
    intro e
    have heq := hf.2 (.bal d') (by simp [hks]) (.allow f' a) (by simp [hks]) e
    injection heq
  have hst2s3 : st2.get s3 = stor.get s3 := by
    rw [hst2_def, Stor.get_set_ne _ hne_d3, hst1_def, Stor.get_set_ne _ hne_f3]
  have hz : st2.get s3 = s.allowances f' a := by
    rw [hst2s3, hs3eq]
    exact hinv.get_slot (hf.1 (.allow f' a) (by simp [hks]))
  have hbf_fixed : vyBalSlot f' ∉ vyFixedSlots := hinv.slot_apart (hf.1 (.bal f') (by simp [hks]))
  have hbd_fixed : vyBalSlot d' ∉ vyFixedSlots := hinv.slot_apart (hf.1 (.bal d') (by simp [hks]))
  have hbf_word : ∀ x ∈ vyWordSlots, vyBalSlot f' ≠ x := fun x hx e => hbf_fixed (by
    rw [e]; simp only [vyWordSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [vyFixedSlots])
  have hbd_word : ∀ x ∈ vyWordSlots, vyBalSlot d' ≠ x := fun x hx e => hbd_fixed (by
    rw [e]; simp only [vyWordSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [vyFixedSlots])
  have hs3_fixed : s3 ∉ vyFixedSlots := by
    rw [hs3eq]; exact hinv.slot_apart (hf.1 (.allow f' a) (by simp [hks]))
  have hs3_word : ∀ x ∈ vyWordSlots, s3 ≠ x := fun x hx e => hs3_fixed (by
    rw [e]; simp only [vyWordSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [vyFixedSlots])
  have hfks : FreshKeys K [Key.bal f', Key.bal d', Key.allow f' a] := hks ▸ hf
  by_cases hmint : a = s.minter
  · -- the caller is the minter: no allowance is spent
    have hspend : ¬ (st2.get vyMinterSlot ≠ a.toB256) := by
      rw [hminter2, hinv.minter, hmint]; exact fun h => h rfl
    set s' : Curve3Crv.State := { s with balanceOf := ledgerCredit (ledgerDebit bf f' v) d' v }
      with hs'_def
    refine RawRefines.of_iff
      (st2, [⟨sevm.currentTarget, [transferTopic, f, d], v.toBytes⟩], some (1 : B256).toBytes)
      (s', [.transfer f' d' v], .bool true)
      (sevm.value = 0 ∧ v ≤ bf f' ∧ (ledgerDebit bf f' v d').toNat + v.toNat < 2 ^ 256) ?_ ?_ ?_
    · intro r
      simp only [rawOf, rawTransferFrom, ← ha_def, ← hf_def, ← hd_def, ← hv_def, ← hbf_def]
      rw [hs1, hs2, hff, hy, ← hst1_def, ← hst2_def, if_neg hspend]
      split_ifs with hc <;> simp_all [eq_comm]
    · intro o
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx, ← ha_def, ← hf_def, ← hd_def,
        ← hv_def, ← hf'_def, ← hd'_def]
      by_cases hv : sevm.value = 0
      · simp only [hv, ite_true, Curve3Crv.transferFrom_eq_ok, true_and, B256.Nof]
        constructor
        · rintro ⟨-, -, h1, h2, -, rfl⟩
          refine ⟨⟨h1, h2⟩, ?_⟩
          simp [hs'_def, hmint, hbf_def, hf'_def, hd'_def]
        · rintro ⟨⟨h1, h2⟩, rfl⟩
          exact ⟨hfr, hdr, h1, h2, fun hc => absurd hmint hc,
            by simp [hs'_def, hmint, hbf_def, hf'_def, hd'_def]⟩
      · simp [hv]
    · rintro ⟨hv, hle, hnof⟩
      have hstep : Curve3Crv.step (c3ctx sevm ow) (callAt sevm 5) s =
          .ok (s', [.transfer f' d' v], .bool true) := by
        simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx, ← ha_def, ← hf_def, ← hd_def,
          ← hv_def, ← hf'_def, ← hd'_def, hv, ite_true]
        exact Curve3Crv.transferFrom_eq_ok.mpr
          ⟨hfr, hdr, hle, hnof, fun hc => absurd hmint hc,
            by simp [hs'_def, hmint, hbf_def, hf'_def, hd'_def]⟩
      refine ⟨?_, ?_, rfl⟩
      · rw [hks]
        refine hinv.update (ws := []) (hf := hfks) (by simp) ?_ ?_ ?_ rfl rfl ?_ ?_ ?_
          (Curve3Crv.step_conserved hinv.conserved hstep)
        · intro x hx _
          have h1 : vyBalSlot f' ≠ x := hx (.bal f') (by simp [hks])
          have h2 : vyBalSlot d' ≠ x := hx (.bal d') (by simp [hks])
          rw [hst2_def, Stor.get_set_ne _ h2, hst1_def, Stor.get_set_ne _ h1]
        · intro k hk
          simp only [hks, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl
          · show st2.get (vyBalSlot f') = ledgerCredit (ledgerDebit bf f' v) d' v f'
            rw [hst2_def, hst1_def]
            by_cases had : d' = f'
            · rw [had, Stor.get_set_self, ledgerCredit_self]
            · rw [Stor.get_set_ne _ (hnebd (Ne.symm had)).symm, ledgerCredit_ne _ (Ne.symm had),
                ledgerDebit_self, Stor.get_set_self]
          · show st2.get (vyBalSlot d') = ledgerCredit (ledgerDebit bf f' v) d' v d'
            rw [hst2_def, Stor.get_set_self, ledgerCredit_self]
          · show st2.get (vyAllowSlot f' a) = s'.allowances f' a
            rw [← hs3eq, hz, hs'_def]
        · intro k hk
          cases k with
          | bal c =>
            simp only [hks, List.mem_cons, Key.bal.injEq, List.not_mem_nil, or_false, not_or] at hk
            show ledgerCredit (ledgerDebit bf f' v) d' v c = bf c
            rw [ledgerCredit_ne _ hk.2.1, ledgerDebit_ne _ hk.1]
          | allow o p => rfl
        · show st2.get vyDecimalsSlot = s'.decimals
          rw [hst2_def, Stor.get_set_ne _ (hbd_word _ (by simp [vyWordSlots])),
            hst1_def, Stor.get_set_ne _ (hbf_word _ (by simp [vyWordSlots]))]
          exact hinv.decimals
        · show st2.get vySupplySlot = s'.totalSupply
          rw [hst2_def, Stor.get_set_ne _ (hbd_word _ (by simp [vyWordSlots])),
            hst1_def, Stor.get_set_ne _ (hbf_word _ (by simp [vyWordSlots]))]
          exact hinv.supply
        · exact hminter2.trans hinv.minter
      · simp only [List.map, eventLog, List.cons.injEq, and_true]
        rw [hf'_def, hd'_def, B256.toAdr_toB256_of_lt hfr, B256.toAdr_toB256_of_lt hdr]
  · -- the caller is not the minter: the allowance is spent (its own declaration, see above)
    exact refine_transferFrom_spend hinv hf hmint

-- SEGMENT: refineApprove (pure, short)
/-- `approve`.  Proof sketch: one fresh key `allow caller p`; the guard `v = 0 ∨ current = 0`
reads the model's allowance (`get_slot`); one write. -/
theorem refine_approve (hinv : VyInv stor s K)
    (hf : FreshKeys K (callKeys sevm.caller (callAt sevm 6))) :
    RawRefines sevm (rawOf 6 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 6) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 6))) := by
  set a := sevm.caller with ha_def
  set p := Sevm.argWord sevm 0 with hp_def
  set v := Sevm.argWord sevm 1 with hv_def
  by_cases hp : p.toNat < 2 ^ 160
  swap
  · refine ⟨fun r hr => ?_, fun o ho => ?_⟩
    · simp only [rawOf, rawApprove] at hr
      split_ifs at hr with hc
      exact absurd hc.2.1 hp
    · simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx] at ho
      by_cases hv : sevm.value = 0
      · simp only [hv, ite_true] at ho
        exact absurd (Curve3Crv.approve_eq_ok.mp ho).1 hp
      · simp [hv] at ho
  set p' := p.toAdr
  have hks : callKeys a (callAt sevm 6) = [.allow a p'] := rfl
  have hslot : mapSlot (mapSlot 4 a.toB256) p = vyAllowSlot a p' := by
    simp only [vyAllowSlot, p', B256.toAdr_toB256_of_lt hp]
  have hcur : stor.get (vyAllowSlot a p') = s.allowances a p' :=
    hinv.get_slot (hf.1 (.allow a p') (by simp [hks]))
  have hap : vyAllowSlot a p' ∉ vyFixedSlots := hinv.slot_apart (hf.1 (.allow a p') (by simp [hks]))
  set s' : Curve3Crv.State :=
    { s with allowances := (Function.update s.allowances a (Function.update (s.allowances a) p' v)) }
  refine RawRefines.of_iff (stor.set (vyAllowSlot a p') v,
      [⟨sevm.currentTarget, [approvalTopic, a.toB256, p], v.toBytes⟩], some (1 : B256).toBytes)
    (s', [.approval a p' v], .bool true)
    (sevm.value = 0 ∧ (v = 0 ∨ s.allowances a p' = 0)) ?_ ?_ ?_
  · intro r
    simp only [rawOf, rawApprove, ← ha_def, ← hp_def, ← hv_def]
    rw [hslot, hcur]
    split_ifs with hc <;> simp_all [eq_comm]
  · intro o
    simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx]
    by_cases hv : sevm.value = 0
    · simp only [hv, ite_true, Curve3Crv.approve_eq_ok, true_and]
      constructor
      · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨hp, h1, h2⟩
    · simp [hv]
  · rintro ⟨hv, hz⟩
    have hstep : Curve3Crv.step (c3ctx sevm ow) (callAt sevm 6) s =
        .ok (s', [.approval a p' v], .bool true) := by
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx, hv, ite_true]
      exact Curve3Crv.approve_eq_ok.mpr ⟨hp, hz, rfl⟩
    refine ⟨?_, ?_, rfl⟩
    · rw [hks]
      have hne : ∀ x ∈ vyWordSlots, vyAllowSlot a p' ≠ x := fun x hx e => hap (by
        rw [e]; simp only [vyWordSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp [vyFixedSlots])
      refine hinv.update (ws := []) (hf := hks ▸ hf) (by simp) ?_ ?_ ?_ rfl rfl ?_ ?_ ?_
        (Curve3Crv.step_conserved hinv.conserved hstep)
      · intro x hx _
        dsimp only
        rw [Stor.get_set_ne (k := vyAllowSlot a p') _ (hx (.allow a p') (by simp))]
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        subst hk
        show (stor.set (vyAllowSlot a p') v).get (vyAllowSlot a p') =
          Function.update s.allowances a (Function.update (s.allowances a) p' v) a p'
        simp [Stor.get_set_self]
      · intro k hk
        cases k with
        | bal c => rfl
        | allow o q =>
          simp only [List.mem_cons, Key.allow.injEq, List.not_mem_nil, or_false, not_and] at hk
          show Function.update s.allowances a (Function.update (s.allowances a) p' v) o q =
            s.allowances o q
          by_cases ho : o = a
          · subst ho
            simp [Function.update_of_ne (hk rfl)]
          · simp [Function.update_of_ne ho]
      · dsimp only
        rw [Stor.get_set_ne _ (hne _ (by simp [vyWordSlots]))]
        exact hinv.decimals
      · dsimp only
        rw [Stor.get_set_ne _ (hne _ (by simp [vyWordSlots]))]
        exact hinv.supply
      · dsimp only
        rw [Stor.get_set_ne _ (hne _ (by simp [vyWordSlots]))]
        exact hinv.minter
    · simp only [List.map, eventLog, List.cons.injEq, and_true]
      rw [B256.toAdr_toB256_of_lt hp]

-- SEGMENT: refineMintBurn (pure, medium; `mint` and `burnFrom`)
/-- `mint`.  Proof: slot 5 then one fresh balance key; the balance read after
the supply write is of the unchanged balance slot (off `vyFixedSlots`); guards and effects are
the model's clause by clause; `conserved` by `step_conserved`. -/
theorem refine_mint (hinv : VyInv stor s K)
    (hf : FreshKeys K (callKeys sevm.caller (callAt sevm 7))) :
    RawRefines sevm (rawOf 7 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 7) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 7))) := by
  set d := Sevm.argWord sevm 0 with hd_def
  set v := Sevm.argWord sevm 1 with hv_def
  set f := s.balanceOf with hf_def
  have hmin : stor.get vyMinterSlot = sevm.caller.toB256 ↔ sevm.caller = s.minter := by
    rw [hinv.minter]
    exact ⟨fun e => (toB256_inj_adr e).symm, fun e => by rw [e]⟩
  by_cases hd : d.toNat < 2 ^ 160
  swap
  · refine ⟨fun r hr => ?_, fun o ho => ?_⟩
    · simp only [rawOf, rawMint] at hr
      split_ifs at hr with hc
      exact absurd hc.2.1 hd
    · simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx] at ho
      by_cases hv : sevm.value = 0
      · simp only [hv, ite_true] at ho
        exact absurd (Curve3Crv.mint_eq_ok.mp ho).1 hd
      · simp [hv] at ho
  set d' := d.toAdr
  have hks : callKeys sevm.caller (callAt sevm 7) = [.bal d'] := rfl
  have hs2 : mapSlot 3 d = vyBalSlot d' := by
    simp only [vyBalSlot, d', B256.toAdr_toB256_of_lt hd]
  have hfd : stor.get (vyBalSlot d') = f d' := hinv.get_slot (hf.1 (.bal d') (by simp [hks]))
  have hap : vyBalSlot d' ∉ vyFixedSlots := hinv.slot_apart (hf.1 (.bal d') (by simp [hks]))
  have h5 : vyBalSlot d' ≠ vySupplySlot := fun e => hap (by rw [e]; simp [vyFixedSlots])
  have h2 : vyBalSlot d' ≠ vyDecimalsSlot := fun e => hap (by rw [e]; simp [vyFixedSlots])
  have h6 : vyBalSlot d' ≠ vyMinterSlot := fun e => hap (by rw [e]; simp [vyFixedSlots])
  have hyE : (stor.set vySupplySlot (s.totalSupply + v)).get (vyBalSlot d') = f d' := by
    rw [Stor.get_set_ne _ (Ne.symm h5), hfd]
  set s' : Curve3Crv.State := { s with totalSupply := s.totalSupply + v, balanceOf := ledgerCredit f d' v }
  refine RawRefines.of_iff ((stor.set vySupplySlot (s.totalSupply + v)).set (vyBalSlot d')
      (f d' + v), [⟨sevm.currentTarget, [transferTopic, 0, d], v.toBytes⟩], some (1 : B256).toBytes)
    (s', [.transfer 0 d' v], .bool true) (sevm.value = 0 ∧ sevm.caller = s.minter ∧ d ≠ 0 ∧ s.totalSupply.toNat + v.toNat < 2 ^ 256 ∧ (f d').toNat + v.toNat < 2 ^ 256) ?_ ?_ ?_
  · intro r
    simp only [rawOf, rawMint, ← hd_def, ← hv_def]
    rw [hs2, hinv.supply, hyE]
    split_ifs with hc <;> simp_all [eq_comm]
  · intro o
    simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx]
    by_cases hv : sevm.value = 0
    · simp only [hv, ite_true, Curve3Crv.mint_eq_ok, true_and, B256.Nof]
      constructor
      · rintro ⟨-, h1, h2, h3, h4, h5⟩; exact ⟨⟨h1, h2, h3, h4⟩, h5⟩
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨hd, h1, h2, h3, h4, h5⟩
    · simp [hv]
  · rintro ⟨hv, hmn, hnz, hs1, hs2'⟩
    have hstep : Curve3Crv.step (c3ctx sevm ow) (callAt sevm 7) s = .ok (s', [.transfer 0 d' v], .bool true) := by
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx, hv, ite_true]
      exact Curve3Crv.mint_eq_ok.mpr ⟨hd, hmn, hnz, hs1, hs2', rfl⟩
    refine ⟨?_, ?_, rfl⟩
    · rw [hks]
      refine hinv.update (ws := [vySupplySlot]) (hf := hks ▸ hf) (by simp [vyWordSlots]) ?_ ?_ ?_
        rfl rfl ?_ ?_ ?_ (Curve3Crv.step_conserved hinv.conserved hstep)
      · intro x hx hw
        dsimp only
        have h1 := hx (.bal d') (by simp)
        have h3 : vySupplySlot ≠ x := fun e => hw (by simp [e])
        rw [Stor.get_set_ne (k := vyBalSlot d') _ h1, Stor.get_set_ne _ h3]
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        subst hk
        show ((stor.set vySupplySlot _).set (vyBalSlot d') (f d' + v)).get (vyBalSlot d') =
          ledgerCredit f d' v d'
        rw [Stor.get_set_self, ledgerCredit_self]
      · intro k hk
        cases k with
        | bal c =>
          simp only [List.mem_cons, Key.bal.injEq, List.not_mem_nil, or_false] at hk
          show ledgerCredit f d' v c = f c
          rw [ledgerCredit_ne _ hk]
        | allow o p => rfl
      · dsimp only
        rw [Stor.get_set_ne _ h2, Stor.get_set_ne _ (by decide)]
        exact hinv.decimals
      · dsimp only
        rw [Stor.get_set_ne _ h5, Stor.get_set_self]
      · dsimp only
        rw [Stor.get_set_ne _ h6, Stor.get_set_ne _ (by decide)]
        exact hinv.minter
    · simp only [List.map, eventLog, List.cons.injEq, and_true]
      rw [B256.toAdr_toB256_of_lt hd]
      rfl

-- SEGMENT: refineMintBurn (pure, medium; `mint` and `burnFrom`)
/-- `burnFrom`.  Proof: slot 5 then one fresh balance key; the balance read after
the supply write is of the unchanged balance slot (off `vyFixedSlots`); guards and effects are
the model's clause by clause; `conserved` by `step_conserved`. -/
theorem refine_burnFrom (hinv : VyInv stor s K)
    (hf : FreshKeys K (callKeys sevm.caller (callAt sevm 8))) :
    RawRefines sevm (rawOf 8 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 8) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 8))) := by
  set d := Sevm.argWord sevm 0 with hd_def
  set v := Sevm.argWord sevm 1 with hv_def
  set f := s.balanceOf with hf_def
  have hmin : stor.get vyMinterSlot = sevm.caller.toB256 ↔ sevm.caller = s.minter := by
    rw [hinv.minter]
    exact ⟨fun e => (toB256_inj_adr e).symm, fun e => by rw [e]⟩
  by_cases hd : d.toNat < 2 ^ 160
  swap
  · refine ⟨fun r hr => ?_, fun o ho => ?_⟩
    · simp only [rawOf, rawBurnFrom] at hr
      split_ifs at hr with hc
      exact absurd hc.2.1 hd
    · simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx] at ho
      by_cases hv : sevm.value = 0
      · simp only [hv, ite_true] at ho
        exact absurd (Curve3Crv.burnFrom_eq_ok.mp ho).1 hd
      · simp [hv] at ho
  set d' := d.toAdr
  have hks : callKeys sevm.caller (callAt sevm 8) = [.bal d'] := rfl
  have hs2 : mapSlot 3 d = vyBalSlot d' := by
    simp only [vyBalSlot, d', B256.toAdr_toB256_of_lt hd]
  have hfd : stor.get (vyBalSlot d') = f d' := hinv.get_slot (hf.1 (.bal d') (by simp [hks]))
  have hap : vyBalSlot d' ∉ vyFixedSlots := hinv.slot_apart (hf.1 (.bal d') (by simp [hks]))
  have h5 : vyBalSlot d' ≠ vySupplySlot := fun e => hap (by rw [e]; simp [vyFixedSlots])
  have h2 : vyBalSlot d' ≠ vyDecimalsSlot := fun e => hap (by rw [e]; simp [vyFixedSlots])
  have h6 : vyBalSlot d' ≠ vyMinterSlot := fun e => hap (by rw [e]; simp [vyFixedSlots])
  have hyE : (stor.set vySupplySlot (s.totalSupply - v)).get (vyBalSlot d') = f d' := by
    rw [Stor.get_set_ne _ (Ne.symm h5), hfd]
  set s' : Curve3Crv.State := { s with totalSupply := s.totalSupply - v, balanceOf := ledgerDebit f d' v }
  refine RawRefines.of_iff ((stor.set vySupplySlot (s.totalSupply - v)).set (vyBalSlot d')
      (f d' - v), [⟨sevm.currentTarget, [transferTopic, d, 0], v.toBytes⟩], some (1 : B256).toBytes)
    (s', [.transfer d' 0 v], .bool true) (sevm.value = 0 ∧ sevm.caller = s.minter ∧ d ≠ 0 ∧ v ≤ s.totalSupply ∧ v ≤ f d') ?_ ?_ ?_
  · intro r
    simp only [rawOf, rawBurnFrom, ← hd_def, ← hv_def]
    rw [hs2, hinv.supply, hyE]
    split_ifs with hc <;> simp_all [eq_comm]
  · intro o
    simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx]
    by_cases hv : sevm.value = 0
    · simp only [hv, ite_true, Curve3Crv.burnFrom_eq_ok, true_and]
      constructor
      · rintro ⟨-, h1, h2, h3, h4, h5⟩; exact ⟨⟨h1, h2, h3, h4⟩, h5⟩
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨hd, h1, h2, h3, h4, h5⟩
    · simp [hv]
  · rintro ⟨hv, hmn, hnz, hs1, hs2'⟩
    have hstep : Curve3Crv.step (c3ctx sevm ow) (callAt sevm 8) s = .ok (s', [.transfer d' 0 v], .bool true) := by
      simp only [callAt, Curve3Crv.step, Curve3Crv.body, c3ctx, hv, ite_true]
      exact Curve3Crv.burnFrom_eq_ok.mpr ⟨hd, hmn, hnz, hs1, hs2', rfl⟩
    refine ⟨?_, ?_, rfl⟩
    · rw [hks]
      refine hinv.update (ws := [vySupplySlot]) (hf := hks ▸ hf) (by simp [vyWordSlots]) ?_ ?_ ?_
        rfl rfl ?_ ?_ ?_ (Curve3Crv.step_conserved hinv.conserved hstep)
      · intro x hx hw
        dsimp only
        have h1 := hx (.bal d') (by simp)
        have h3 : vySupplySlot ≠ x := fun e => hw (by simp [e])
        rw [Stor.get_set_ne (k := vyBalSlot d') _ h1, Stor.get_set_ne _ h3]
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        subst hk
        show ((stor.set vySupplySlot _).set (vyBalSlot d') (f d' - v)).get (vyBalSlot d') =
          ledgerDebit f d' v d'
        rw [Stor.get_set_self, ledgerDebit_self]
      · intro k hk
        cases k with
        | bal c =>
          simp only [List.mem_cons, Key.bal.injEq, List.not_mem_nil, or_false] at hk
          show ledgerDebit f d' v c = f c
          rw [ledgerDebit_ne _ hk]
        | allow o p => rfl
      · dsimp only
        rw [Stor.get_set_ne _ h2, Stor.get_set_ne _ (by decide)]
        exact hinv.decimals
      · dsimp only
        rw [Stor.get_set_ne _ h5, Stor.get_set_self]
      · dsimp only
        rw [Stor.get_set_ne _ h6, Stor.get_set_ne _ (by decide)]
        exact hinv.minter
    · simp only [List.map, eventLog, List.cons.injEq, and_true]
      rw [B256.toAdr_toB256_of_lt hd]
      rfl

end Segments

/-- **The refinement of every body's raw effect**, assembled. -/
theorem refine_at {sevm : Sevm} {stor : Stor} {s : Curve3Crv.State} {K : Key → Prop}
    {ow : Option B256} {k : Nat} (hk : k < 13) (hinv : VyInv stor s K)
    (hf : FreshKeys K (callKeys sevm.caller (callAt sevm k))) :
    RawRefines sevm (rawOf k sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm k) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm k))) := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · exact refine_setMinter hinv hf
  · exact refine_setName hinv hf
  · exact refine_wordView (by simp) hinv hf
  · exact refine_wordView (by simp) hinv hf
  · exact refine_transfer hinv hf
  · exact refine_transferFrom hinv hf
  · exact refine_approve hinv hf
  · exact refine_mint hinv hf
  · exact refine_burnFrom hinv hf
  · exact refine_stringView (by simp) hinv hf
  · exact refine_stringView (by simp) hinv hf
  · exact refine_wordView (by simp) hinv hf
  · exact refine_wordView (by simp) hinv hf
  · omega

end Blanc.Lift.Curve3Crv
