-- Fixed DRIP receipt annotation protocol; all encoding, bloom and trie work
-- uses the pinned Jaune implementation. Native replay remains a separate gate.
import Jaune.Transaction

namespace Blanc.Drip.ReceiptEvaluation

open Jaune

private abbrev J := _root_.Lean.Json

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def keys (value : J) (expected : List String) : Except String Unit := do
  let fields ← value.getObj?
  require ((fields.toList.map Prod.fst).mergeSort (· ≤ ·) == expected.mergeSort (· ≤ ·))
    "DRIP protocol object keys differ"

private def field (value : J) (name : String) : Except String J :=
  value.getObjVal? name

private def decimal (value : J) : Except String Nat := do
  let text ← value.getStr?
  let number ← text.toNat?.toExcept "DRIP protocol decimal required"
  require (text == toString number) "DRIP protocol decimal is not canonical"
  return number

private def bytes (value : J) : Except String Bytes := do
  let text ← value.getStr?
  require (text.startsWith "0x") "DRIP protocol hex prefix required"
  let raw ← Hex.toBytes (text.drop 2 |>.toString) |>.toExcept "DRIP protocol hex required"
  return raw

private def logValue (value : J) : Except String Log := do
  keys value ["address", "topics", "data"]
  let address ← (← bytes (← field value "address")).toAdr?.toExcept "DRIP log address width"
  let rawTopics ← (← field value "topics").getArr?
  require (rawTopics.size ≤ 4) "DRIP log topic count"
  let topics ← rawTopics.toList.mapM fun topic => do
    let raw ← bytes topic
    require (raw.length == 32) "DRIP log topic width"
    return raw.toB256
  return { address, topics, data := ← bytes (← field value "data") }

private def receiptValue (value : J) : Except String (Receipt × Nat) := do
  keys value ["status", "cumulativeGasUsed", "gasUsed", "logs"]
  let status ← decimal (← field value "status")
  let cumulative ← decimal (← field value "cumulativeGasUsed")
  let used ← decimal (← field value "gasUsed")
  let logs ← (← (← field value "logs").getArr?).toList.mapM logValue
  require (status ≤ 1 && cumulative > 0 && used > 0) "DRIP receipt status/gas"
  require (status == 1 || logs.isEmpty) "DRIP failed receipt has logs"
  -- Jaune's Receipt.gasUsed is the RLP cumulative field, as in makeReceipt.
  return ({ succeeded := status == 1, gasUsed := cumulative,
            bloom := logsBloom logs, logs }, used)

private def hex (raw : Bytes) : J := .str ("0x" ++ raw.toHex)
private def nat (value : Nat) : J := .str (toString value)

private def blockValue (value : J) : Except String (J × Nat) := do
  keys value ["fixture", "case", "blockIndex", "blockNumber", "rlp", "receipts"]
  let fixture ← (← field value "fixture").getStr?
  let caseName ← (← field value "case").getStr?
  let index ← decimal (← field value "blockIndex")
  let number ← decimal (← field value "blockNumber")
  let (block, headerHash) ← rlpToBlock (← bytes (← field value "rlp"))
  require (block.header.number == number && block.ommers.isEmpty && block.wds.isEmpty)
    "DRIP block envelope differs"
  let receipts ← (← (← field value "receipts").getArr?).toList.mapM receiptValue
  require (receipts.length == block.txs.length) "DRIP receipt count differs"
  let mut previous := 0
  let mut encoded : List (Bytes × Bytes) := []
  let mut allLogs : List Log := []
  let mut rows : Array J := #[]
  for ((receipt, used), txEntry) in receipts.zip block.txs do
    let tx ← match txEntry with
      | .inl _ => .error "DRIP typed transaction unsupported"
      | .inr tx => .ok tx
    match tx.type with
    | .zero .. => pure ()
    | _ => throw "DRIP nonlegacy transaction unsupported"
    require (receipt.gasUsed == previous + used && used < tx.gas)
      "DRIP cumulative gas delta or transaction bound differs"
    previous := receipt.gasUsed
    let key := (BLT.bytes rows.size.toBytes).toBytes
    let raw := receipt.toBLT.toBytes
    encoded := encoded ++ [(key, raw)]
    allLogs := allLogs ++ receipt.logs
    rows := rows.push (.mkObj [("index", nat rows.size), ("key", hex key),
      ("encoded", hex raw), ("bloom", hex receipt.bloom), ("gasUsed", nat used)])
  let root := receiptRoot encoded
  let bloom := logsBloom allLogs
  require (root == block.header.receiptRoot) "DRIP receipt root differs"
  require (bloom == block.header.bloom) "DRIP block bloom differs"
  require (previous == block.header.gasUsed) "DRIP block gas differs"
  return (.mkObj [("fixture", .str fixture), ("case", .str caseName),
    ("blockIndex", nat index), ("blockNumber", nat number),
    ("headerHash", hex headerHash.toBytes), ("receiptRoot", hex root.toBytes),
    ("bloom", hex bloom), ("gasUsed", nat previous), ("receipts", .arr rows)], rows.size)

def response (request : J) : Except String J := do
  keys request ["schema", "fixtures", "receipts", "blocks"]
  require ((← (← field request "schema").getNat?) == 1) "DRIP protocol version"
  require ((← decimal (← field request "fixtures")) == 91 &&
    (← decimal (← field request "receipts")) == 137) "DRIP frozen population differs"
  let blocks ← (← (← field request "blocks").getArr?).toList.mapM blockValue
  require ((blocks.map Prod.snd).sum == 137) "DRIP total receipt count differs"
  return .mkObj [("schema", .num 1), ("request", request),
    ("blocks", .arr (blocks.map Prod.fst).toArray),
    ("done", .str "drip-receipts-v1-complete")]

end Blanc.Drip.ReceiptEvaluation

def main : IO UInt32 := do
  let input ← (← IO.getStdin).getLine
  match _root_.Lean.Json.parse input >>= Blanc.Drip.ReceiptEvaluation.response with
  | .error message =>
    (← IO.getStderr).putStrLn message
    return 1
  | .ok output =>
    (← IO.getStdout).putStrLn output.compress
    return 0
