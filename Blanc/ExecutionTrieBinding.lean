import Blanc.ExecutionIndexedReceipts
import Blanc.ExecutionBlockCommitments
import Blanc.ExecutionBodyTransactionCut
import Blanc.RlpRoundTrip

/-!
Trie-map binding for configured blocks: the nibble-keyed maps Jaune's
transaction and receipt roots hash, their lookups, the block output's
transaction map as the decoded body, and the encoding injectivity that turns a
recorded map entry into an exact body slot or receipt. Equality of a trace's map
with a recorded one stays the caller's obligation; no trie injectivity is proved.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The comparator of Jaune's nibble-keyed trie maps (`NTB`). -/
abbrev ntbCmp : Bytes → Bytes → Ordering := @Jaune.List.compare UInt8 ⟨UInt8.compareLows⟩

private theorem uint8_nibbles :
    ∀ x : UInt8, x.highs.lows = x.highs ∧ x.lows.lows = x.lows ∧
      (x.highs <<< 4 ||| x.lows) = x := by
  intro x
  have key : ∀ n : Fin 256,
      (UInt8.ofNat n.val).highs.lows = (UInt8.ofNat n.val).highs ∧
        (UInt8.ofNat n.val).lows.lows = (UInt8.ofNat n.val).lows ∧
        ((UInt8.ofNat n.val).highs <<< 4 ||| (UInt8.ofNat n.val).lows) =
          UInt8.ofNat n.val := by
    decide +kernel
  simpa only [UInt8.ofNat_toNat] using key ⟨x.toNat, x.toNat_lt⟩

theorem toNibbles_injective {as bs : Bytes} (h : as.toNibbles = bs.toNibbles) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons b bs => simp only [Bytes.toNibbles, UInt8.toNibbles, List.cons_append, List.nil_append,
      reduceCtorEq] at h
  | cons a as ih => cases bs with
    | nil => simp only [Bytes.toNibbles, UInt8.toNibbles, List.cons_append, List.nil_append,
      reduceCtorEq] at h
    | cons b bs =>
      simp only [Bytes.toNibbles, UInt8.toNibbles, List.cons_append, List.nil_append,
        List.cons.injEq] at h
      obtain ⟨hh, hl, rest⟩ := h
      rw [← (uint8_nibbles a).2.2, ← (uint8_nibbles b).2.2, hh, hl, ih rest]

/-! ## The trie maps Jaune's roots hash -/

/-- The value Jaune's transaction root stores for one transaction: its
envelope type byte (none for legacy) followed by its RLP encoding. -/
def txTrieValue (tx : Tx) : Bytes :=
  (match tx.type with
    | .zero _ _ => []
    | .one _ _ _ _ => [0x01]
    | .two _ _ _ _ _ => [0x02]
    | .three _ _ _ _ _ _ _ => [0x03]
    | .four _ _ _ _ _ _ => [0x04]) ++ tx.toBLT.toBytes

/-- The value Jaune's receipt root stores for one typed receipt. -/
def receiptTrieValue (receipt : Fin 5 × Receipt) : Bytes :=
  receipt.1.val.toBytes ++ receipt.2.toBLT.toBytes

/-- The entry list Jaune's transaction root builds its trie map from. -/
def transactionsEntries (bout : BlockOutput) : List (Bytes × Bytes) :=
  bout.transactionsTrie.toList.map fun p => (p.1.toNibbles, txTrieValue p.2)

/-- The entry list Jaune's receipt root builds its trie map from. -/
def receiptsEntries (bout : BlockOutput) : List (Bytes × Bytes) :=
  bout.receiptsTrie.toList.map fun p => (p.1.toNibbles, receiptTrieValue p.2)

/-- The nibble-keyed map whose `trie` is the transaction root of `bout`. -/
def transactionsNTB (bout : BlockOutput) : NTB :=
  Std.TreeMap.ofList (transactionsEntries bout) ntbCmp

/-- The nibble-keyed map whose `trie` is the receipt root of `bout`. -/
def receiptsNTB (bout : BlockOutput) : NTB :=
  Std.TreeMap.ofList (receiptsEntries bout) ntbCmp

theorem getTransactionsRoot_eq_trie (bout : BlockOutput) :
    getTransactionsRoot bout = trie (transactionsNTB bout) := rfl

theorem getReceiptRoot_eq_trie (bout : BlockOutput) :
    getReceiptRoot bout = trie (receiptsNTB bout) := rfl

/-- The configured block's header transaction root is the trie of its actual
transaction map. -/
theorem ConfiguredBlockTraceIn.txsRoot_eq_trie
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) :
    block.block.header.txsRoot = trie (transactionsNTB block.blockOutput) :=
  block.txsRoot

/-- The configured block's header receipt root is the trie of its actual
receipt map. -/
theorem ConfiguredBlockTraceIn.receiptRoot_eq_trie
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) :
    block.block.header.receiptRoot = trie (receiptsNTB block.blockOutput) :=
  block.receiptRoot

/-! ## The block output's transaction map is the decoded body -/

/-- A successful transaction inserts exactly itself at its own encoded index. -/
theorem processTransaction_transactionsTrie {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {index : Nat} {p : State × BlockOutput} (hp : processTransaction benv bout tx index = .ok p) :
    p.2.transactionsTrie =
      bout.transactionsTrie.insert (BLT.toBytes (.bytes index.toBytes)) tx := by
  unfold processTransaction at hp
  obtain ⟨b1, hb1, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b2, hb2, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b3, hb3, hp⟩ := Except.bind_eq_ok hp
  simp only [Except.ok.injEq] at hb1 hb2 hb3
  cases hp
  subst hb1 hb2 hb3
  rfl

/-- Replaying indexed transactions inserts each at its encoded index, in order. -/
theorem ApplyTransactionsTrace.transactionsTrie_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    finalBout.transactionsTrie = txs.foldl
      (fun m item => m.insert (BLT.toBytes (.bytes item.1.toBytes)) item.2)
      bout.transactionsTrie := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
    rw [ih, processTransaction_transactionsTrie head.result]
    rfl

private theorem foldl_insert_putIndex_aux (xs : List Tx) (offset : Nat)
    (m : Std.TreeMap Bytes Tx compare) (i : Nat) :
    (List.foldl (fun m item => m.insert (BLT.toBytes (.bytes item.1.toBytes)) item.2) m
        (List.putIndex.aux offset xs))[BLT.toBytes (.bytes i.toBytes)]? =
      if offset ≤ i ∧ i < offset + xs.length then xs[i - offset]?
      else m[BLT.toBytes (.bytes i.toBytes)]? := by
  induction xs generalizing offset m with
  | nil =>
    simp only [List.putIndex.aux, List.foldl_nil, List.length_nil, Nat.add_zero]
    rw [ite_eq_right (by omega)]
  | cons x xs ih =>
    simp only [List.putIndex.aux, List.foldl_cons, List.length_cons]
    rw [ih, Std.TreeMap.getElem?_insert]
    by_cases same : offset = i
    · subst same
      have hcmp : compare (BLT.toBytes (.bytes offset.toBytes))
          (BLT.toBytes (.bytes offset.toBytes)) = .eq := Std.ReflCmp.compare_self
      rw [ite_eq_right (by omega), ite_eq_left hcmp, ite_eq_left (by omega), Nat.sub_self]
      rfl
    · have hcmp : ¬ compare (BLT.toBytes (.bytes offset.toBytes))
          (BLT.toBytes (.bytes i.toBytes)) = .eq := fun h =>
        RlpConcrete.receipt_key_ne same (Std.LawfulEqCmp.eq_of_compare h)
      rw [ite_eq_right hcmp]
      by_cases inside : offset + 1 ≤ i ∧ i < offset + 1 + xs.length
      · rw [ite_eq_left inside, ite_eq_left (by omega)]
        obtain ⟨k, hk⟩ : ∃ k, i - offset = k + 1 := ⟨i - offset - 1, by omega⟩
        rw [hk, List.getElem?_cons_succ]
        congr 1
        omega
      · rw [ite_eq_right inside, ite_eq_right (by omega)]

/-- Indexed insertion from an empty map recovers the list by position. -/
theorem foldl_insert_putIndex_getElem? (xs : List Tx) (i : Nat) :
    (List.foldl (fun m item => m.insert (BLT.toBytes (.bytes item.1.toBytes)) item.2)
        (∅ : Std.TreeMap Bytes Tx compare) xs.putIndex)[BLT.toBytes (.bytes i.toBytes)]? =
      xs[i]? := by
  rw [List.putIndex, foldl_insert_putIndex_aux]
  split
  · rename_i h
    rw [Nat.sub_zero]
  · rename_i h
    rw [Std.TreeMap.getElem?_emptyc, List.getElem?_eq_none (by omega)]

/-- Request processing leaves the transaction map unchanged. -/
theorem RequestsTrace.transactionsTrie_eq
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    bout'.transactionsTrie = bout.transactionsTrie := by
  have run := trace.run
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at run
  obtain ⟨_, _, run⟩ := Except.bind_eq_ok run
  dsimp only at run
  obtain ⟨_, _, run⟩ := Except.bind_eq_ok run
  cases run
  rfl

/-- Both the enabled and disabled request stages preserve the transaction map. -/
theorem RequestStageTrace.transactionsTrie_eq
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    bout'.transactionsTrie = bout.transactionsTrie := by
  cases trace with
  | skipped => rfl
  | called _ requests _ => exact requests.transactionsTrie_eq

/-- The body's final transaction map is the one after the transaction pass. -/
theorem StagedBodyTrace.transactionsTrie_eq_transactionBout
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    bout.transactionsTrie = trace.transactionBout.transactionsTrie := by
  have withdrawal : trace.withdrawalBout.transactionsTrie =
      trace.transactionBout.transactionsTrie := by
    have run := congrArg (fun p : State × BlockOutput => p.2.transactionsTrie)
      trace.withdrawalsRun
    unfold withdrawalsPass at run
    split at run <;> exact run.symm
  have requests := trace.requests.transactionsTrie_eq
  have final := congrArg BlockOutput.transactionsTrie trace.finalBout_eq
  exact final.symm.trans (requests.trans withdrawal)

/-- The body's transaction map at encoded index `i` is the `i`-th decoded transaction. -/
theorem StagedBodyTrace.transactionsTrie_getElem?
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (i : Nat) :
    bout.transactionsTrie[BLT.toBytes (.bytes i.toBytes)]? = trace.decodedTxs[i]? := by
  rw [trace.transactionsTrie_eq_transactionBout, trace.transactions.transactionsTrie_eq]
  exact foldl_insert_putIndex_getElem? trace.decodedTxs i

/-- A successful monadic list decode has a source entry, at the same position,
for every result entry. -/
theorem exists_getElem_of_mapM_eq_ok {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (run : xs.mapM f = .ok ys)
    {i : Nat} {y : β} (atOutput : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ f x = .ok y := by
  induction xs generalizing ys i with
  | nil =>
    cases Except.ok.inj run
    simp only [List.reverse_nil, List.getElem?_nil, reduceCtorEq] at atOutput
  | cons a xs ih =>
    simp only [List.mapM_cons] at run
    obtain ⟨b, head, run⟩ := Except.bind_eq_ok run
    obtain ⟨bs, tail, run⟩ := Except.bind_eq_ok run
    cases Except.ok.inj run
    cases i with
    | zero =>
      cases Option.some.inj atOutput
      exact ⟨a, rfl, head⟩
    | succ i => exact ih tail atOutput

/-- `transactionsTrie_index`: the configured block's transaction map at encoded
index `i` is the `i`-th decoded transaction of the actual body. -/
theorem ConfiguredBlockTraceIn.transactionsTrie_getElem?
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (i : Nat) :
    block.blockOutput.transactionsTrie[BLT.toBytes (.bytes i.toBytes)]? =
      block.bodyTrace.decodedTxs[i]? :=
  block.bodyTrace.transactionsTrie_getElem? i

/-- An entry of the configured block's transaction map at encoded index `i` is
the decoding of body slot `i`. -/
theorem ConfiguredBlockTraceIn.exists_slot_of_transactionsTrie
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat} {tx : Tx}
    (lookup : block.blockOutput.transactionsTrie[BLT.toBytes (.bytes i.toBytes)]? = some tx) :
    ∃ slot, block.block.txs[i]? = some slot ∧
      decodeTx (initBenv block.fork pre block.block.header).stat.rules slot = .ok tx := by
  rw [block.transactionsTrie_getElem?] at lookup
  exact exists_getElem_of_mapM_eq_ok block.bodyTrace.decodeRun lookup

/-! ## Encoding injectivity used by the trie entries -/

theorem nat_toBytes_injective {m n : Nat} (h : m.toBytes = n.toBytes) : m = n := by
  simpa only [RlpConcrete.nat_bytes_roundtrip] using congrArg Bytes.toNat h

theorem nat_toBytesPack_injective {m n : Nat} (h : m.toBytesPack = n.toBytesPack) : m = n := by
  have roundtrip : ∀ k : Nat, k.toBytesPack.toNat = k := by
    intro k
    cases k with
    | zero => rfl
    | succ k => exact RlpConcrete.nat_bytes_roundtrip (k + 1)
  simpa only [roundtrip] using congrArg Bytes.toNat h

theorem uint32_toBytes_injective {x y : UInt32} (h : x.toBytes = y.toBytes) : x = y := by
  simpa only [toUInt32_toBytes] using congrArg Bytes.toUInt32 h

theorem uint64_toBytes_injective {x y : UInt64} (h : x.toBytes = y.toBytes) : x = y := by
  simpa only [UInt64.toUInt64_toBytes] using congrArg Bytes.toUInt64 h

theorem b256_toBytes_injective {x y : B256} (h : x.toBytes = y.toBytes) : x = y := by
  simpa only [B256.toB256_toBytes] using congrArg Bytes.toB256 h

theorem adr_toBytes_injective {a b : Adr} (h : a.toBytes = b.toBytes) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only [Adr.toBytes, B128.toBytes] at h
  obtain ⟨h1, h23⟩ := List.append_inj h rfl
  obtain ⟨h2, h3⟩ := List.append_inj h23 rfl
  rw [uint32_toBytes_injective h1, uint64_toBytes_injective h2, uint64_toBytes_injective h3]

/-- Jaune's RLP encoder is injective on items encoded in fewer than `2 ^ 64` bytes. -/
theorem blt_toBytes_injective {a b : BLT} (small : a.toBytes.length < 2 ^ 64)
    (h : a.toBytes = b.toBytes) : a = b := by
  have ha := RlpConcrete.toBLT?_toBytes a small
  have hb := RlpConcrete.toBLT?_toBytes b (h ▸ small)
  rw [h] at ha
  exact Option.some.inj (ha.symm.trans hb)

/-- A list item's encoding starts with a list prefix byte (at least `0xC0`),
so it never begins with a typed-envelope byte. -/
theorem list_toBytes_head (rs : List BLT) (small : (BLT.list rs).toBytes.length < 2 ^ 64) :
    ∃ c rest, (BLT.list rs).toBytes = c :: rest ∧ 192 ≤ c.toNat := by
  rw [BLT.toBytes, BLTs.toBytes] at small ⊢
  dsimp only at small ⊢
  split
  · rename_i short
    refine ⟨_, _, rfl, ?_⟩
    simp only [UInt8.toNat_add, Nat.toUInt8_eq, UInt8.toNat_ofNat', UInt8.reduceToNat]
    omega
  · rename_i long
    rw [ite_eq_right long] at small
    refine ⟨_, _, rfl, ?_⟩
    simp only [List.length_cons, List.length_append] at small
    have width : (BLTs.toBytesJoin rs).length.toBytesPack.length ≤ 8 := by
      rw [RlpConcrete.toBytesPack_of_pos _ (by omega)]
      have mono := RlpConcrete.nat_bytes_length_mono
        (show (BLTs.toBytesJoin rs).length ≤ 2 ^ 64 - 1 by omega)
      have top : (2 ^ 64 - 1 : Nat).toBytes.length = 8 := by decide +kernel
      omega
    simp only [UInt8.toNat_add, Nat.toUInt8_eq, UInt8.toNat_ofNat', UInt8.reduceToNat]
    omega

/-- Leading zero bytes do not change a big-endian word: `Tx.toBLT`'s trimming
of signature scalars preserves the value `recoverSender` reads. -/
theorem toB256_trimZero (xs : Bytes) : Bytes.toB256 (trimZero xs) = xs.toB256 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x = 0
    · subst hx
      rw [Bytes.toB256_zero_cons, ← ih]; rfl
    · simp only [trimZero, List.dropWhile_cons, hx, decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem receiver_bytes_injective {a b : Option Adr}
    (h : @Option.rec Adr (fun _ => Bytes) [] Adr.toBytes a =
      @Option.rec Adr (fun _ => Bytes) [] Adr.toBytes b) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some b =>
      have := congrArg List.length h
      simp only [Adr.toBytes, B128.toBytes, List.length_append, List.length_nil] at this
      cases this
  | some a => cases b with
    | none =>
      have := congrArg List.length h
      simp only [Adr.toBytes, B128.toBytes, List.length_append, List.length_nil] at this
      cases this
    | some b => exact congrArg some (adr_toBytes_injective h)

/-- Two legacy transactions with the same RLP item agree on every field it
encodes; the signature scalars agree up to leading zero bytes (`Tx.toBLT`
trims them), hence as words (`toB256_trimZero`). -/
theorem legacy_fields_of_toBLT_eq {tx tx' : Tx} {gasPrice gasPrice' : Nat}
    {receiver receiver' : Option Adr}
    (type : tx.type = .zero gasPrice receiver) (type' : tx'.type = .zero gasPrice' receiver')
    (same : tx.toBLT = tx'.toBLT) :
    tx.nonce = tx'.nonce ∧ gasPrice = gasPrice' ∧ tx.gas = tx'.gas ∧ receiver = receiver' ∧
      tx.value = tx'.value ∧ tx.data = tx'.data ∧ tx.v = tx'.v ∧
      tx.r.toB256 = tx'.r.toB256 ∧ tx.s.toB256 = tx'.s.toB256 := by
  obtain ⟨nonce, gas, value, data, v, r, s, ty⟩ := tx
  obtain ⟨nonce', gas', value', data', v', r', s', ty'⟩ := tx'
  dsimp only at type type' ⊢
  subst type type'
  simp only [Tx.toBLT, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, and_true] at same
  obtain ⟨hnonce, hprice, hgas, hreceiver, hvalue, hdata, hv, hr, hs⟩ := same
  refine ⟨UInt64.toNat_inj.mp (nat_toBytes_injective hnonce), nat_toBytes_injective hprice,
    nat_toBytes_injective hgas, receiver_bytes_injective hreceiver, nat_toBytes_injective hvalue,
    hdata, nat_toBytes_injective hv, ?_, ?_⟩
  · rw [← toB256_trimZero r, hr, toB256_trimZero]
  · rw [← toB256_trimZero s, hs, toB256_trimZero]

/-- A legacy transaction's trie value is its bare RLP encoding. -/
theorem txTrieValue_of_legacy {tx : Tx} {gasPrice : Nat} {receiver : Option Adr}
    (type : tx.type = .zero gasPrice receiver) : txTrieValue tx = tx.toBLT.toBytes := by
  simp only [txTrieValue, type, List.nil_append]

/-- A transaction whose trie value is a legacy transaction's is itself legacy,
with the same RLP item. -/
theorem txTrieValue_eq_legacy {tx tx₀ : Tx} {gasPrice₀ : Nat} {receiver₀ : Option Adr}
    (type₀ : tx₀.type = .zero gasPrice₀ receiver₀)
    (small : (txTrieValue tx₀).length < 2 ^ 64) (same : txTrieValue tx = txTrieValue tx₀) :
    ∃ gasPrice receiver, tx.type = .zero gasPrice receiver ∧ tx.toBLT = tx₀.toBLT := by
  have value₀ := txTrieValue_of_legacy type₀
  obtain ⟨fields₀, list₀⟩ : ∃ fields, tx₀.toBLT = .list fields := by
    rw [Tx.toBLT, type₀]
    exact ⟨_, rfl⟩
  rw [value₀] at small same
  obtain ⟨c, rest, encoded, high⟩ := list_toBytes_head fields₀ (list₀ ▸ small)
  rw [← list₀] at encoded
  cases htype : tx.type with
  | zero gasPrice receiver =>
    simp only [txTrieValue, htype, List.nil_append] at same
    exact ⟨gasPrice, receiver, rfl, (blt_toBytes_injective (same ▸ small) same)⟩
  | one | two | three | four =>
    simp only [txTrieValue, htype, List.cons_append, List.nil_append, encoded,
      List.cons.injEq] at same
    have := congrArg UInt8.toNat same.1
    simp only [UInt8.reduceToNat] at this
    omega

/-- Jaune's typed-envelope decoder never yields a legacy transaction. -/
theorem Bytes.toExTx_not_legacy {bs : Bytes} {tx : Tx} (h : bs.toExTx = .ok tx) :
    tx.type.isLegacy = false := by
  unfold Bytes.toExTx at h
  split at h
  · cases h
  · split at h
    all_goals try cases h
    all_goals (repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h)
    all_goals try split at h
    all_goals (repeat obtain ⟨_, hstep, h⟩ := Except.bind_eq_ok h)
    all_goals (cases h; rfl)

theorem log_toBLT_injective : Function.Injective Log.toBLT := by
  intro a b h
  obtain ⟨aAdr, aTopics, aData⟩ := a
  obtain ⟨bAdr, bTopics, bData⟩ := b
  simp only [Log.toBLT, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, and_true] at h
  obtain ⟨hadr, htopics, hdata⟩ := h
  have topicInj : Function.Injective B256.toBLT := fun x y hxy =>
    b256_toBytes_injective (by simpa only [B256.toBLT, BLT.bytes.injEq] using hxy)
  rw [adr_toBytes_injective hadr, List.map_injective_iff.mpr topicInj htopics, hdata]

theorem receipt_toBLT_injective : Function.Injective Receipt.toBLT := by
  intro a b h
  obtain ⟨aOk, aGas, aBloom, aLogs⟩ := a
  obtain ⟨bOk, bGas, bBloom, bLogs⟩ := b
  simp only [Receipt.toBLT, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, and_true] at h
  obtain ⟨hok, hgas, hbloom, hlogs⟩ := h
  have hok : aOk = bOk := by
    cases aOk <;> cases bOk <;> first | rfl | (simp only [Bool.false_eq_true, ↓reduceIte,
      List.nil_eq, List.cons_ne_nil] at hok)
  rw [hok, nat_toBytesPack_injective hgas, hbloom,
    List.map_injective_iff.mpr log_toBLT_injective hlogs]

private theorem fin5_toBytes :
    ∀ f : Fin 5, f.val.toBytes.length ≤ 1 ∧ ∀ b ∈ f.val.toBytes, b.toNat ≤ 4 := by
  decide +kernel

/-- Typed receipt trie values determine the typed receipt. -/
theorem receiptTrieValue_injective {r r₀ : Fin 5 × Receipt}
    (small : (receiptTrieValue r₀).length < 2 ^ 64)
    (same : receiptTrieValue r = receiptTrieValue r₀) : r = r₀ := by
  have smallFor : ∀ q : Fin 5 × Receipt, (receiptTrieValue q).length < 2 ^ 64 →
      ∃ c rest, q.2.toBLT.toBytes = c :: rest ∧ 192 ≤ c.toNat ∧
        q.2.toBLT.toBytes.length < 2 ^ 64 := by
    intro q hq
    have hlen : q.2.toBLT.toBytes.length < 2 ^ 64 := by
      simp only [receiptTrieValue, List.length_append] at hq
      omega
    obtain ⟨c, rest, enc, high⟩ := list_toBytes_head _ hlen
    exact ⟨c, rest, enc, high, hlen⟩
  obtain ⟨c₀, rest₀, enc₀, high₀, len₀⟩ := smallFor r₀ small
  obtain ⟨c, rest, enc, high, _⟩ := smallFor r (same ▸ small)
  obtain ⟨p1, p2⟩ := fin5_toBytes r.1
  obtain ⟨q1, q2⟩ := fin5_toBytes r₀.1
  have value := same
  simp only [receiptTrieValue] at value
  have headTag : ∀ (P : Bytes) (c : UInt8) (rest : Bytes), P.length ≤ 1 →
      (∀ b ∈ P, b.toNat ≤ 4) → 192 ≤ c.toNat →
      (P = [] ↔ 192 ≤ ((P ++ c :: rest).head?.getD 0).toNat) := by
    intro P c rest short tags highc
    cases P with
    | nil => simpa only [List.nil_append, List.head?_cons, Option.getD_some, true_iff] using highc
    | cons x xs =>
      have hx := tags x List.mem_cons_self
      simp only [List.cons_append, List.head?_cons, Option.getD_some, reduceCtorEq, false_iff,
        Nat.not_le]
      omega
  have lengths : r.1.val.toBytes.length = r₀.1.val.toBytes.length := by
    have hr := headTag _ c rest p1 p2 high
    have hr₀ := headTag _ c₀ rest₀ q1 q2 high₀
    rw [← enc, value, enc₀] at hr
    have empties : r.1.val.toBytes = [] ↔ r₀.1.val.toBytes = [] := by
      rw [hr, hr₀]
    rcases hp : r.1.val.toBytes with _ | ⟨x, xs⟩ <;>
      rcases hq : r₀.1.val.toBytes with _ | ⟨y, ys⟩ <;>
      simp only [hp, hq, List.length_nil, List.length_cons, iff_false,
        false_iff, not_true_eq_false, List.cons_ne_nil] at empties p1 q1 ⊢
    omega
  obtain ⟨prefixEq, encEq⟩ := List.append_inj value lengths
  have tag : r.1 = r₀.1 := Fin.ext (nat_toBytes_injective prefixEq)
  have body : r.2 = r₀.2 :=
    receipt_toBLT_injective (blt_toBytes_injective (encEq ▸ len₀) encEq)
  exact Prod.ext tag body

/-! ## From a recorded entry to the body observation -/

/-- An entry of a nibble-keyed entry list built from a byte-keyed map is the
re-encoded map entry at the same byte key. -/
theorem exists_getElem?_of_mem_toNibbles_map {β : Type} {m : Std.TreeMap Bytes β compare}
    {f : β → Bytes} {k e : Bytes}
    (entry : (k.toNibbles, e) ∈ m.toList.map fun p => (p.1.toNibbles, f p.2)) :
    ∃ v, m[k]? = some v ∧ f v = e := by
  obtain ⟨⟨k', v⟩, mem, same⟩ := List.mem_map.mp entry
  simp only [Prod.mk.injEq] at same
  have key := toNibbles_injective same.1
  subst key
  exact ⟨v, Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp mem, same.2⟩

/-- An entry `(nibbles k, e)` of the block's transaction entry list is the trie
value of the block output's transaction at `k`. -/
theorem exists_transaction_of_mem_transactionsEntries {bout : BlockOutput} {k e : Bytes}
    (entry : (k.toNibbles, e) ∈ transactionsEntries bout) :
    ∃ tx, bout.transactionsTrie[k]? = some tx ∧ txTrieValue tx = e :=
  exists_getElem?_of_mem_toNibbles_map entry

/-- An entry `(nibbles k, e)` of the block's receipt entry list is the trie
value of the block output's receipt at `k`. -/
theorem exists_receipt_of_mem_receiptsEntries {bout : BlockOutput} {k e : Bytes}
    (entry : (k.toNibbles, e) ∈ receiptsEntries bout) :
    ∃ r, bout.receiptsTrie[k]? = some r ∧ receiptTrieValue r = e :=
  exists_getElem?_of_mem_toNibbles_map entry

/-- If the block's transaction entry list holds, at index `i`'s nibble key, a
legacy transaction's trie value, body slot `i` is an already-decoded legacy
transaction with that transaction's RLP item. Signature-scalar bytes are fixed
only up to leading zeros, which the fields `recoverSender` and intrinsic gas
read do not see (`legacy_fields_of_toBLT_eq`). -/
theorem ConfiguredBlockTraceIn.legacy_slot_of_transactionsEntries
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat} {tx₀ : Tx}
    {gasPrice₀ : Nat} {receiver₀ : Option Adr} (type₀ : tx₀.type = .zero gasPrice₀ receiver₀)
    (small : (txTrieValue tx₀).length < 2 ^ 64)
    (entry : ((BLT.toBytes (.bytes i.toBytes)).toNibbles, txTrieValue tx₀) ∈
      transactionsEntries block.blockOutput) :
    ∃ tx gasPrice receiver, block.block.txs[i]? = some (.inr tx) ∧
      tx.type = .zero gasPrice receiver ∧ tx.toBLT = tx₀.toBLT := by
  obtain ⟨tx, lookup, value⟩ := exists_transaction_of_mem_transactionsEntries entry
  obtain ⟨slot, atSlot, decoded⟩ := block.exists_slot_of_transactionsTrie lookup
  obtain ⟨gasPrice, receiver, type, blt⟩ := txTrieValue_eq_legacy type₀ small value
  refine ⟨tx, gasPrice, receiver, ?_, type, blt⟩
  cases slot with
  | inl bs =>
    unfold decodeTx at decoded
    obtain ⟨tx', parsed, decoded⟩ := Except.bind_eq_ok decoded
    obtain ⟨_, _, decoded⟩ := Except.bind_eq_ok decoded
    cases decoded
    have typed := Bytes.toExTx_not_legacy parsed
    rw [type] at typed
    cases typed
  | inr tx' =>
    cases decoded
    exact atSlot

/-- If the block's receipt entry list holds, at key `k`'s nibbles, the trie
value of `r`, the block output's receipt at `k` is exactly `r`. -/
theorem ConfiguredBlockTraceIn.receipt_of_receiptsEntries
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {k : Bytes} {r : Fin 5 × Receipt}
    (small : (receiptTrieValue r).length < 2 ^ 64)
    (entry : (k.toNibbles, receiptTrieValue r) ∈ receiptsEntries block.blockOutput) :
    block.blockOutput.receiptsTrie[k]? = some r := by
  obtain ⟨r', lookup, value⟩ := exists_receipt_of_mem_receiptsEntries entry
  rw [lookup, receiptTrieValue_injective small value]

end Blanc.ExecutionTrace
