import «Blanc».Execution



----------------- TESTING DEFS ------------------

def Lean.Json.toIoList : Lean.Json → IO (List Json)
  | .arr a => return a.toList
  | _ => IO.throw "not an array"

def Lean.Json.toIoRBNode :
  Lean.Json →
    -- IO (RBNode String (λ _ => Json))
    IO (Std.TreeMap.Raw String Json compare)
  | .obj r => return r
  | _ => IO.throw "not an object"

def Lean.Json.toString? : Lean.Json → Option String
  | .str s => some s
  | _ => none

def Lean.Json.toIoString : Lean.Json → IO String
  | .str s => return s
  | _ => IO.throw "not a string"

def Lean.Json.toIoB8L (j : Json) : IO B8L := do
  let x ← toIoString j >>= .remove0x
  (Hex.toB8L x).toIO ""

def Lean.Json.toIoAdr (j : Json) : IO Adr := do
  let x ← toIoString j >>= .remove0x
  (Hex.toAdr? x).toIO ""

def Lean.Json.toIoB64 (j : Json) : IO B64 := do
  let x ← toIoString j >>= .remove0x
  (Hex.toB64? x).toIO

def Lean.Json.toB256? (j : Json) : Option B256 := do
  let x ← toString? j >>= .remove0x
  Hex.toB256? x

def Lean.Json.toIoB256 (j : Json) : IO B256 := do
  let x ← toIoString j >>= .remove0x
  (Hex.toB256? x).toIO ""

def Lean.Json.toIoB64P (j : Json) : IO B64 := do
  let x ← toIoString j >>= .remove0x
  let xs ← (Hex.toB8L x).toIO ""
  return (B8L.toB64P xs)

def Lean.Json.toIoB256P (j : Json) : IO B256 := do
  let x ← toIoString j >>= .remove0x
  let xs ← (Hex.toB8L x).toIO ""
  return (B8L.toB256P xs)

def Lean.Json.toAcct : Lean.Json → IO Acct
  | .obj r => do
    let aux (xy : String × Lean.Json) : IO (B256 × B256) := do
      let x ← .remove0x xy.fst
      let bs ← (Hex.toB8L x).toIO ""
      let bs' ← xy.snd.toIoB8L
      return ⟨bs.toB256P, bs'.toB256P⟩
    let bal_json ← (r.get? "balance").toIO ""
    let nonce_json ← (r.get? "nonce").toIO ""
    let code_json ← (r.get? "code").toIO ""
    let stor_json ← (r.get? "storage").toIO "" >>= Lean.Json.toIoRBNode
    let bal ← Lean.Json.toIoB256P bal_json
    let nonce ← Lean.Json.toIoB64P nonce_json
    let code ← Lean.Json.toIoB8L code_json
    let stor ← List.mapM aux stor_json.toArray.toList
    return ⟨nonce, bal, Lean.RBMap.fromList stor _, code.toByteArray⟩
  | _ => .throw "cannot parse account (not .obj)"

def Lean.Json.toWorld (j : Lean.Json) : IO State := do
  let aux : State → (String × Lean.Json) → IO State :=
    fun | w, ⟨s, j⟩ => do
      let adr ← (Hex.toAdr? <| remove0x s).toIO ""
      let acct ← j.toAcct
      pure <| w.set adr acct
  let ob ← j.toIoRBNode
  List.foldlM aux .empty ob.toArray.toList

def Lean.Json.find? : String → Lean.Json → Option Lean.Json
  | k, .obj r => r.get? k
  | _, _ => .none

def Lean.Json.find : String → Lean.Json → IO Lean.Json
  | k, .obj r => (r.get? k).toIO s!"ERROR : FAILED JSON RETRIEVAL WITH KEY : {k}"
  | k, _ => .throw s!"ERROR : INPUT JSON IS NOT OBJECT, FAILED RETRIEVAL WITH KEY : {k}"

def getTxExMap (j : Lean.Json) : IO (Option String × B8L) := do
  let rlp ← j.find "rlp" >>= Lean.Json.toIoB8L
  match j.find? "expectException" with
  | .none => pure ⟨.none, rlp⟩
  | .some exj => do
    let exs ← exj.toIoString
    pure ⟨.some exs, rlp⟩

def Lean.Json.toHeader (json : Lean.Json) : IO Header := do
  let parentHash ← json.find "parentHash" >>= Lean.Json.toIoB256
  let ommersHash ← json.find "uncleHash" >>= Lean.Json.toIoB256
  let coinbase ← json.find "coinbase" >>= Lean.Json.toIoAdr
  let stateRoot ← json.find "stateRoot" >>= Lean.Json.toIoB256
  let txsRoot ← json.find "transactionsTrie" >>= Lean.Json.toIoB256
  let receiptRoot ← json.find "receiptTrie" >>= Lean.Json.toIoB256
  let bloom ← json.find "bloom" >>= Lean.Json.toIoB8L
  let difficulty ← (json.find "difficulty" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let number ← (json.find "number" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let gasLimit ← (json.find "gasLimit" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let gasUsed ← (json.find "gasUsed" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let timestamp ← (json.find "timestamp" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let extraData ← json.find "extraData" >>= Lean.Json.toIoB8L
  let prevRandao ← json.find "mixHash" >>= Lean.Json.toIoB256
  let nonce ← json.find "nonce" >>= Lean.Json.toIoB64
  let baseFeePerGas ← (json.find "baseFeePerGas" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let withdrawalsRoot ← json.find "withdrawalsRoot" >>= Lean.Json.toIoB256
  let blobGasUsed ← (json.find "blobGasUsed" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let excessBlobGas ← (json.find "excessBlobGas" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let parentBeaconBlockRoot ← json.find "parentBeaconBlockRoot" >>= Lean.Json.toIoB256
  let requestsHash := (json.find? "requestsHash" >>= Lean.Json.toB256?)
  .ok {
    parentHash := parentHash
    ommersHash := ommersHash
    coinbase := coinbase
    stateRoot := stateRoot
    txsRoot := txsRoot
    receiptRoot := receiptRoot
    bloom := bloom
    difficulty := difficulty
    number := number
    gasLimit := gasLimit
    gasUsed := gasUsed
    timestamp := timestamp
    extraData := extraData
    prevRandao := prevRandao
    nonce := nonce
    baseFeePerGas := baseFeePerGas
    withdrawalsRoot := withdrawalsRoot
    blobGasUsed := blobGasUsed
    excessBlobGas := excessBlobGas
    parentBeaconBlockRoot := parentBeaconBlockRoot
    requestsHash := requestsHash
  }

def getPostStateRoot (json : Lean.Json) : IO B256 :=
  ( do let stateJson ← json.find "postState"
       let state ← stateJson.toWorld
       .ok state.root ) <|>
  (json.find "postStateHash" >>= Lean.Json.toIoB256)

def Except.toIO {ξ : Type} : Except String ξ → IO ξ
  | .ok x => .ok x
  | .error err => .throw err

def processBlockJsons (vb : Bool) (chain : BlockChain) :
  List Lean.Json → IO (Option BlockChain)
  | j :: js => do
    let ⟨ex, j⟩ ← getTxExMap j
    match ex with
    | .none =>
      match (← (addBlockToChain vb chain j).toIO) with
      | .inr ex => .throw s!"unexpected TX exception : {ex}"
      | .inl chain => processBlockJsons vb chain js
    | .some _ =>
      match (← (addBlockToChain vb chain j).toIO) with
      | .inr ex' =>
        .guard
          (isEthereumException ex' || isRlpException ex')
          s!"ERROR : {ex'} is not an ethereum exception or an RLP exception"
        .ok none
      | .inl _ =>
        .throw "ERROR : expected exception not raised"
  | [] => .ok <| some chain

def runBlockchainStTest (vb : Bool) (idx? : Option Nat)
  (incls excls : List String) : (Nat × String × Lean.Json) → IO Unit
  | ⟨idx, name, json⟩ => do
    match idx? with
    | none => .ok ()
    | some specIdx =>
      if specIdx ≠ idx then
        return ()
    if ¬ (incls.isEmpty ∨ name ∈ incls) then
      return ()
    if name ∈ excls then
      return ()
    let nw ← json.find "network" >>= Lean.Json.toIoString
    if "Prague" ≠ nw then
      return ()

    .println s!"TEST NAME : {name}"

    let gbh_json ← json.find "genesisBlockHeader"
    let gbh ← gbh_json.toHeader
    let gb : Block := {header := gbh, txs := [], ommers := [], wds := []}
    let gbh_hash ← gbh_json.find "hash" >>= Lean.Json.toIoB256
    let gbh_hash' := (BLT.toB8L (Header.toBLT gbh)).keccak

    .guard
      (gbh_hash = gbh_hash')
      s!"error : genesis block header hash, expected = {gbh_hash}, computed = {gbh_hash'}"

    let genesisRLP ← json.find "genesisRLP" >>= Lean.Json.toIoB8L
    let genesisRLP' := gb.toBLT.toB8L
    .guard (genesisRLP = genesisRLP') "error : unexpected genesis block RLP."
    let (chainId : Nat) ←
      match gbh_json.find? "chainId" with
      | .none => .ok 1
      | .some chainIdJson => chainIdJson.toIoB64 <&> UInt64.toNat

    let preState ← json.find "pre" >>= Lean.Json.toWorld

    let chain : BlockChain :=
    {
      blocks := [gb]
      state := preState
      chainId := chainId.toUInt64
    }

    let blockJsons ← json.find "blocks" >>= Lean.Json.toIoList
    let (some chain) ← processBlockJsons vb chain blockJsons | .ok ()
    let lastBlockHash ← json.find "lastblockhash" >>= Lean.Json.toIoB256
    let lastBlock ← chain.blocks.getLast?.toIO "error : no last block "
    let lastBlockHash' := (Header.toBLT lastBlock.header).toB8L.keccak
    .guard
      (lastBlockHash = lastBlockHash')
      s!"error : last block hash does not match\n  expected : {lastBlockHash}\n  computed : {lastBlockHash'}"

    let postStateRoot ← getPostStateRoot json
    .guard
      (postStateRoot = chain.state.root)
      s!"error : end state root does not match\n  expected : {postStateRoot}\n  computed : {chain.state.root}"

def runTestFile (vb : Bool) (testIdx : Option Nat)
  (incls excls : List String) (idxPath : Nat × String) : IO Unit := do
  let fileIdx := idxPath.fst
  let path := idxPath.snd
  .println "\n================================================================\n"
  .println s!"TEST FILE #{fileIdx} : {path}\n"
  let rb ← readJsonFile path >>= Lean.Json.toIoRBNode
  let js := rb.toArray.toList.putIndex
  let _ ← js.mapM <| runBlockchainStTest vb testIdx incls excls
  .ok ()

def getTestNames (incls excls : List String) :
  List String → (List String × List String)
  | option :: arg :: strs =>
    if option = "--name"
    then getTestNames (arg :: incls) excls strs
    else
      if option = "--notName"
      then getTestNames incls (arg :: excls) strs
      else getTestNames incls excls (arg :: strs)
  | [_] => ⟨incls, excls⟩
  | [] => ⟨incls, excls⟩

def getSkip : List String → Option Nat
  | s0 :: s1 :: ss =>
    if s0 = "--skip"
    then String.toNat? s1
    else getSkip <| s1 :: ss
  | _ => none

def getTestIndex : List String → Option Nat
  | s0 :: s1 :: ss =>
    if s0 = "--index"
    then String.toNat? s1
    else getTestIndex <| s1 :: ss
  | _ => none

def getFiles (path : System.FilePath) : IO (List System.FilePath) := do
  if (← System.FilePath.isDir path) then
    let paths ← System.FilePath.walkDir path
    List.filterM (fun path => path.isDir <&> .not) paths.toList
  else
    return [path]

def main : List String → IO Unit
  | path :: opts => do
    let vb : Bool := List.contains opts "--verbose"
    let testIdx : Option Nat := getTestIndex opts
    let skip : Option Nat := getSkip opts
    let ⟨incls, excls⟩ := getTestNames [] [] opts
    let files ← getFiles path
    let files :=
      match skip with
      | none => files
      | some n => files.drop n
    let _ ←
      List.mapM
        (runTestFile vb testIdx incls excls)
        (files.map System.FilePath.toString).putIndex
    pure ()
  | _ => IO.throw "error : invalid arguments"
