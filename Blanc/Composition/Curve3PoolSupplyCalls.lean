import Blanc.Composition.Curve3CrvTokenCore
import Blanc.Lift.Curve3Pool.Observe

/-!
# The pool's token calls as 3Crv reads them (U8c support)

The pool frame's state-changing calls are the model's `ExtCall`s, encoded by `encodeCall`
(`Lift/Curve3Pool/Observe.lean`).  3Crv's dispatcher reads only the calldata (`decodeCall_congr`), so
each encoded call decodes to a fixed 3Crv call:

* `.mint dst amt` — `mint(dst, amt)` at the word values, so 3Crv's facet counts the amount
  `wordAmt amt` (`encode_minted`);
* `.burn src amt` — `burnFrom(src, amt)`, burning `wordAmt amt` (`encode_burned`);
* `.pull`/`.push` — `transferFrom`/`transfer`, neither a mint nor a burn;
* none of them is `setMinter` (`encode_not_setMinter`).

`callsMinted`/`callsBurned` sum the amounts over a model call list.
-/

namespace Blanc.Composition.Curve3PoolSupply

open Jaune Blanc Blanc.Lift Blanc.Lift.Token Blanc.Lift.Curve3Crv Blanc.Composition.Curve3CrvToken
open Blanc.Curve3Crv (Call)

/-! ## Calldata only -/

/-- A message carrying only calldata. -/
def dataSevm (d : Bytes) : Sevm := { (default : Sevm) with data := d }

/-- 3Crv's dispatcher reads only the calldata. -/
theorem decodeCall_congr {e e' : Sevm} (h : e.data = e'.data) : decodeCall e = decodeCall e' := by
  unfold decodeCall strArg Sevm.selector Sevm.argWord Sevm.dataWord
  rw [h]

/-- The amount a calldata mints, as 3Crv's facet counts it. -/
def msgMinted (d : Bytes) : Nat := ((c3crvMintOf (dataSevm d)).map Prod.snd).getD 0

/-- The amount a calldata burns, as 3Crv's facet counts it. -/
def msgBurned (d : Bytes) : Nat := ((c3crvBurnOf (dataSevm d)).map Prod.snd).getD 0

theorem c3crvMintOf_data (e : Sevm) : c3crvMintOf e = c3crvMintOf (dataSevm e.data) := by
  unfold c3crvMintOf
  rw [decodeCall_congr (e := e) (e' := dataSevm e.data) rfl]

theorem c3crvBurnOf_data (e : Sevm) : c3crvBurnOf e = c3crvBurnOf (dataSevm e.data) := by
  unfold c3crvBurnOf
  rw [decodeCall_congr (e := e) (e' := dataSevm e.data) rfl]

/-- The facet's minted total over messages, read off their calldata. -/
theorem minted_eq_sum (msgs : List Sevm) :
    c3crvSupply.minted msgs = (msgs.map fun e => msgMinted e.data).sum := by
  induction msgs with
  | nil => rfl
  | cons a as ih =>
    rw [SupplyFacet.minted_cons, ih, List.map_cons, List.sum_cons]
    change ((c3crvMintOf a).map Prod.snd).getD 0 + _ = _
    rw [c3crvMintOf_data]
    rfl

theorem burned_eq_sum (msgs : List Sevm) :
    c3crvSupply.burned msgs = (msgs.map fun e => msgBurned e.data).sum := by
  induction msgs with
  | nil => rfl
  | cons a as ih =>
    rw [SupplyFacet.burned_cons, ih, List.map_cons, List.sum_cons]
    change ((c3crvBurnOf a).map Prod.snd).getD 0 + _ = _
    rw [c3crvBurnOf_data]
    rfl

/-! ## Calldata words -/

/-- A word placed after a prefix is the calldata word at the prefix's length. -/
theorem dataWord_eq_of_append {e : Sevm} {pre rest : Bytes} {w i : B256}
    (h : e.data = pre ++ (w.toBytes ++ rest)) (hi : i.toNat = pre.length) :
    Sevm.dataWord e i = w := by
  unfold Sevm.dataWord
  rw [h, hi, List.sliceD, List.drop_left,
    List.takeD_eq_take 0 (by simp only [List.length_append, B256.length_toBytes]; omega),
    List.take_left' (B256.length_toBytes w), B256.toB256_toBytes]

theorem abiSelectorBytes_length' (sel : B256) : (abiSelectorBytes sel).length = 4 := by
  simp only [abiSelectorBytes, List.length_drop, B256.length_toBytes]

/-- The pool's selector byte strings are the ABI selector bytes of 3Crv's selectors. -/
theorem mintSel_eq : Curve3Pool.mintSel = abiSelectorBytes selMint := by decide
theorem burnFromSel_eq : Curve3Pool.burnFromSel = abiSelectorBytes selBurnFrom := by decide
theorem transferSel_eq : Curve3Pool.transferSel = abiSelectorBytes selTransfer := by decide
theorem transferFromSel_eq :
    Curve3Pool.transferFromSel = abiSelectorBytes selTransferFrom := by decide

theorem word_length (n : Nat) : (Curve3Pool.word n).length = 32 := B256.length_toBytes _

/-- A calldata starting with a selector's bytes has that selector. -/
theorem selector_of_prefix {d tail : Bytes} {sel : B256}
    (canonical : Bytes.toB256 (abiSelectorBytes sel) = sel) (h : d = abiSelectorBytes sel ++ tail) :
    Sevm.selector (dataSevm d) = sel :=
  selector_eq_of_data_eq_abiSelectorBytes_append canonical h

/-! ## Each encoded call decoded -/

theorem decode_mint (dst amt : Nat) (tail : Bytes)
    (h : tail = Curve3Pool.word dst ++ Curve3Pool.word amt) :
    decodeCall (dataSevm (Curve3Pool.mintSel ++ tail)) =
      .mint (Nat.toB256 dst) (Nat.toB256 amt) := by
  subst h
  have hsel : Sevm.selector (dataSevm (Curve3Pool.mintSel ++
      (Curve3Pool.word dst ++ Curve3Pool.word amt))) = selMint :=
    selector_of_prefix (by decide) (by rw [mintSel_eq])
  have ha0 : Sevm.argWord (dataSevm (Curve3Pool.mintSel ++
      (Curve3Pool.word dst ++ Curve3Pool.word amt))) 0 = Nat.toB256 dst :=
    dataWord_eq_of_append (pre := Curve3Pool.mintSel) (rest := Curve3Pool.word amt) rfl (by decide)
  have ha1 : Sevm.argWord (dataSevm (Curve3Pool.mintSel ++
      (Curve3Pool.word dst ++ Curve3Pool.word amt))) 1 = Nat.toB256 amt :=
    dataWord_eq_of_append (pre := Curve3Pool.mintSel ++ Curve3Pool.word dst) (rest := [])
      (by simp only [dataSevm, List.append_nil, List.append_assoc]; rfl)
      (by rw [List.length_append, word_length]; decide)
  have hlen : ¬ (dataSevm (Curve3Pool.mintSel ++
      (Curve3Pool.word dst ++ Curve3Pool.word amt))).data.length < 4 := by
    simp only [dataSevm, List.length_append, word_length, Curve3Pool.mintSel, List.length_cons,
      List.length_nil]
    omega
  unfold decodeCall
  rw [if_neg hlen]
  simp only [hsel, ha0, ha1]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos trivial]

theorem decode_burn (src amt : Nat) (tail : Bytes)
    (h : tail = Curve3Pool.word src ++ Curve3Pool.word amt) :
    decodeCall (dataSevm (Curve3Pool.burnFromSel ++ tail)) =
      .burnFrom (Nat.toB256 src) (Nat.toB256 amt) := by
  subst h
  have hsel : Sevm.selector (dataSevm (Curve3Pool.burnFromSel ++
      (Curve3Pool.word src ++ Curve3Pool.word amt))) = selBurnFrom :=
    selector_of_prefix (by decide) (by rw [burnFromSel_eq])
  have ha0 : Sevm.argWord (dataSevm (Curve3Pool.burnFromSel ++
      (Curve3Pool.word src ++ Curve3Pool.word amt))) 0 = Nat.toB256 src :=
    dataWord_eq_of_append (pre := Curve3Pool.burnFromSel) (rest := Curve3Pool.word amt) rfl
      (by decide)
  have ha1 : Sevm.argWord (dataSevm (Curve3Pool.burnFromSel ++
      (Curve3Pool.word src ++ Curve3Pool.word amt))) 1 = Nat.toB256 amt :=
    dataWord_eq_of_append (pre := Curve3Pool.burnFromSel ++ Curve3Pool.word src) (rest := [])
      (by simp only [dataSevm, List.append_nil, List.append_assoc]; rfl)
      (by rw [List.length_append, word_length]; decide)
  have hlen : ¬ (dataSevm (Curve3Pool.burnFromSel ++
      (Curve3Pool.word src ++ Curve3Pool.word amt))).data.length < 4 := by
    simp only [dataSevm, List.length_append, word_length, Curve3Pool.burnFromSel,
      List.length_cons, List.length_nil]
    omega
  unfold decodeCall
  rw [if_neg hlen]
  simp only [hsel, ha0, ha1]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos trivial]

theorem decode_transfer (tail : Bytes) (hlen : 4 ≤ (Curve3Pool.transferSel ++ tail).length) :
    ∃ a b, decodeCall (dataSevm (Curve3Pool.transferSel ++ tail)) = .transfer a b := by
  have hsel : Sevm.selector (dataSevm (Curve3Pool.transferSel ++ tail)) = selTransfer :=
    selector_of_prefix (by decide) (by rw [transferSel_eq])
  unfold decodeCall
  rw [if_neg (by simp only [dataSevm]; omega)]
  simp only [hsel]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos trivial]
  exact ⟨_, _, rfl⟩

theorem decode_transferFrom (tail : Bytes)
    (hlen : 4 ≤ (Curve3Pool.transferFromSel ++ tail).length) :
    ∃ a b c, decodeCall (dataSevm (Curve3Pool.transferFromSel ++ tail)) = .transferFrom a b c := by
  have hsel : Sevm.selector (dataSevm (Curve3Pool.transferFromSel ++ tail)) = selTransferFrom :=
    selector_of_prefix (by decide) (by rw [transferFromSel_eq])
  unfold decodeCall
  rw [if_neg (by simp only [dataSevm]; omega)]
  simp only [hsel]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos trivial]
  exact ⟨_, _, _, rfl⟩

/-! ## Amounts of a model call -/

/-- A model amount as the word the pool sends. -/
def wordAmt (v : Nat) : Nat := (Nat.toB256 v).toNat

/-- The amount a model call mints, as 3Crv counts it. -/
def callMinted : Curve3Pool.ExtCall → Nat
  | .mint _ v => wordAmt v
  | _ => 0

/-- The amount a model call burns, as 3Crv counts it. -/
def callBurned : Curve3Pool.ExtCall → Nat
  | .burn _ v => wordAmt v
  | _ => 0

/-- The amounts a model call list mints. -/
def callsMinted (calls : List Curve3Pool.ExtCall) : Nat := (calls.map callMinted).sum

/-- The amounts a model call list burns. -/
def callsBurned (calls : List Curve3Pool.ExtCall) : Nat := (calls.map callBurned).sum

/-- **The decoded call of an encoded model call**: mint and burn at their word values, the coin
transfers as transfers; never `setMinter`. -/
theorem encode_decoded (pool : Adr) (coin : Fin 3 → Adr) (token : Adr)
    (c : Curve3Pool.ExtCall) :
    msgMinted (Curve3Pool.encodeCall pool coin token c).input = callMinted c ∧
      msgBurned (Curve3Pool.encodeCall pool coin token c).input = callBurned c ∧
      ∀ m, decodeCall (dataSevm (Curve3Pool.encodeCall pool coin token c).input) ≠ .setMinter m := by
  cases c with
  | pull i src amt =>
    obtain ⟨a, b, d, h⟩ := decode_transferFrom
      (Curve3Pool.word src ++ pool.toB256.toBytes ++ Curve3Pool.word amt)
      (by simp only [List.length_append, Curve3Pool.transferFromSel, List.length_cons,
        List.length_nil]; omega)
    simp only [Curve3Pool.encodeCall, msgMinted, msgBurned, c3crvMintOf, c3crvBurnOf,
      List.append_assoc] at h ⊢
    rw [h]
    exact ⟨rfl, rfl, fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩
  | push i dst amt =>
    obtain ⟨a, b, h⟩ := decode_transfer (Curve3Pool.word dst ++ Curve3Pool.word amt)
      (by simp only [List.length_append, Curve3Pool.transferSel, List.length_cons,
        List.length_nil]; omega)
    simp only [Curve3Pool.encodeCall, msgMinted, msgBurned, c3crvMintOf, c3crvBurnOf,
      List.append_assoc] at h ⊢
    rw [h]
    exact ⟨rfl, rfl, fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩
  | mint dst amt =>
    have h := decode_mint dst amt _ rfl
    simp only [Curve3Pool.encodeCall, msgMinted, msgBurned, c3crvMintOf, c3crvBurnOf,
      List.append_assoc]
    rw [h]
    exact ⟨rfl, rfl, fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩
  | burn src amt =>
    have h := decode_burn src amt _ rfl
    simp only [Curve3Pool.encodeCall, msgMinted, msgBurned, c3crvMintOf, c3crvBurnOf,
      List.append_assoc]
    rw [h]
    exact ⟨rfl, rfl, fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩

end Blanc.Composition.Curve3PoolSupply
