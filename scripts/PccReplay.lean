import Blanc.Composition.BuilderRequestApplicabilityInput
import Jaune.T8n
import JauneConsensus.Harness.ConfigOverride
import JauneConsensus.Harness.RecordedPairsGloas

/-! Exact-input runtime entry for the local real-BLS PCC applicability scenario.
All decoded bytes must be listed in the supplied SHA256SUMS. Inspect mode only
reports decoded inputs; run mode calls the full original applicability checker.
It never treats an empty run as nontrivial evidence. -/
namespace PccReplay

open Lean Jaune JauneConsensus
open Blanc.Composition.BuilderRequestApplicabilityInput

abbrev P := Preset.mainnet

private def ioExcept {α : Type} (result : Except String α) : IO α :=
  IO.ofExcept (result.mapError IO.userError)

private def bytesAt (files : List (String × ByteArray)) (path : String) : IO ByteArray :=
  match files.lookup path with
  | some bytes => pure bytes
  | none => throw (IO.userError s!"input is absent from SHA256SUMS: {path}")

private def jsonAt (files : List (String × ByteArray)) (path : String) : IO Json := do
  let bytes ← bytesAt files path
  let text ← match String.fromUTF8? bytes with
    | some text => pure text
    | none => throw (IO.userError s!"input is not UTF-8: {path}")
  ioExcept (Json.parse text)

private def sszAt (α : Type) [Ssz α] (files : List (String × ByteArray)) (path : String) : IO α := do
  match (deserialize (← bytesAt files path).toList : M α) with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"SSZ decode {path}: {repr error}")

/-- The frozen allocation spells Ethereum hex quantities, including odd digit
counts. Preserve their numeric values by adding only a leading zero nibble
before passing them to the original byte-oriented account decoder. -/
private def alignAllocQuantities (alloc : Json) : IO Json := do
  let accounts ← alloc.toIoRBNode
  let mapped ← accounts.toArray.toList.mapM fun (address, account) => do
    let fields ← account.toIoRBNode
    let aligned ← fields.toArray.toList.mapM fun (name, value) => do
      if name = "balance" ∨ name = "nonce" then
        let _ ← value.toIoHexNat
        let text ← value.toIoString
        let digits := (text.drop 2).toString
        let value := if digits.length % 2 = 1 then Json.str ("0x0" ++ digits) else value
        pure (name, value)
      else pure (name, value)
    pure (address, Json.mkObj aligned)
  pure (Json.mkObj mapped)

private def load (dir : System.FilePath) : IO
    (List (String × ByteArray) × ChainConfig × Config × JointState P) := do
  let sums ← ioExcept (Harness.RecordedGloas.parseSums (← IO.FS.readFile (dir / "SHA256SUMS")))
  let files ← Harness.RecordedGloas.readVerified dir sums
  let configDoc ← match Harness.Yaml.parse (← bytesAt files "model-config.yaml") with
    | .ok doc => pure doc
    | .error error => throw (IO.userError s!"configuration YAML: {repr error}")
  let ccfg ← match Config.mainnet.applyOverrides configDoc with
    | .ok config => pure config
    | .error error => throw (IO.userError s!"configuration: {error}")
  if ccfg.SLOT_DURATION_MS = 0 ∨ ccfg.SLOT_DURATION_MS % 1000 ≠ 0 then
    throw (IO.userError "this local scenario requires positive whole-second slots")
  if 2 ^ 64 ≤ ccfg.DEPOSIT_CHAIN_ID then
    throw (IO.userError "execution chain ID is outside UInt64")
  let world ← (← alignAllocQuantities (← jsonAt files "alloc.json")).toWorld
  let rawHeader ← bytesAt files "genesis-header.rlp"
  let blt ← match Bytes.toBLT? rawHeader.toList with
    | some value => pure value
    | none => throw (IO.userError "genesis header is not one complete RLP value")
  let header ← match BLT.toExHeader blt with
    | .ok header => pure header
    | .error error => throw (IO.userError s!"genesis header: {repr error}")
  if header.toBLT.toBytes ≠ rawHeader.toList then
    throw (IO.userError "genesis header is not the original canonical RLP encoding")
  let beacon ← sszAt (BeaconState P .fulu) files "anchor-fulu.ssz"
  let chain : BlockChain := ⟨[⟨header, [], [], []⟩], world, UInt64.ofNat ccfg.DEPOSIT_CHAIN_ID⟩
  let forkTime := beacon.genesis_time.toNat + ccfg.GLOAS_FORK_EPOCH * P.SLOTS_PER_EPOCH *
    (ccfg.SLOT_DURATION_MS / 1000)
  let cfg : ChainConfig := ⟨chain.chainId, [.atTime .bpo2 0, .atTime .amsterdam forkTime]⟩
  pure (files, cfg, ccfg, ⟨.fulu, beacon, chain⟩)

private def inputsAt (files : List (String × ByteArray)) : IO (List (Blanc.JointGloasReplayStep.Input P)) := do
  let entries ← ioExcept ((← jsonAt files "inputs.json").getArr?)
  let mut inputs := #[]
  for entry in entries do
    let blockPath ← ioExcept ((← ioExcept (entry.getObjVal? "block")).getStr?)
    let block ← sszAt (Gloas.SignedBeaconBlock P) files blockPath
    let env? ← match ← ioExcept (entry.getObjVal? "envelope") with
      | .null => pure none
      | .str path => some <$> sszAt (Gloas.SignedExecutionPayloadEnvelope P) files path
      | _ => throw (IO.userError "envelope must name an exact SSZ input or be null")
    inputs := inputs.push (.gloas block, env?)
  pure inputs.toList

private def output (fields : List (String × Json)) : IO Unit :=
  IO.println (Json.compress (Json.mkObj fields))

def inspect (dir : System.FilePath) : IO UInt32 := do
  let (_, cfg, ccfg, state) ← load dir
  let manifestHash := (Bytes.sha256 (← IO.FS.readBinFile (dir / "SHA256SUMS")).toList).toHex
  let anchorOk := decide (PreAnchor cfg state)
  let finiteOk := decide
    (Blanc.Composition.BuilderRequestApplicability.Checks.FiniteApplicability ccfg state.exec [.pre state])
  output [("mode", toJson "inspect-inputs-only"), ("bls", toJson true),
    ("preset", toJson "mainnet"), ("input_manifest_sha256", toJson manifestHash), ("anchor_slot", toJson state.beacon.slot.toNat),
    ("validator_count", toJson state.beacon.validators.toArray.size),
    ("execution_head", toJson (state.exec.blocks.getLast?.map (fun b => b.header.hash.toHex))),
    ("pre_anchor_checked", toJson anchorOk), ("finite_checked", toJson finiteOk),
    ("p5_complete", toJson false)]
  pure (if anchorOk && finiteOk then 0 else 1)

def run (dir : System.FilePath) (depth : Nat) : IO UInt32 := do
  let (files, cfg, ccfg, state) ← load dir
  let manifestHash := (Bytes.sha256 (← IO.FS.readBinFile (dir / "SHA256SUMS")).toList).toHex
  let inputs ← inputsAt files
  if inputs.isEmpty then throw (IO.userError "nontrivial replay refuses an empty input sequence")
  let positiveBids := inputs.countP (fun input => match input.1 with
    | .pre _ => false
    | .gloas block => 0 < block.message.body.signed_execution_payload_bid.message.value.toNat)
  if positiveBids = 0 then throw (IO.userError "nontrivial replay requires a positive external builder bid")
  match replayApplicable depth cfg ccfg state inputs with
  | none =>
      output [("mode", toJson "full-applicability"), ("input_manifest_sha256", toJson manifestHash), ("accepted", toJson false),
        ("input_steps", toJson inputs.length), ("bls", toJson true)]
      pure 1
  | some cert =>
      output [("mode", toJson "full-applicability"), ("input_manifest_sha256", toJson manifestHash), ("accepted", toJson true),
        ("input_steps", toJson inputs.length), ("states", toJson cert.val.2.1.length),
        ("kept_blocks", toJson cert.val.2.2.length), ("positive_bids", toJson positiveBids),
        ("bls", toJson true), ("full_valid_joint_g", toJson true),
        ("independent_client_agreement_checked", toJson false)]
      pure 0

end PccReplay

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--inspect", directory] => PccReplay.inspect directory
  | ["--run", directory, limit] =>
      match limit.toNat? with
      | some depth => PccReplay.run directory depth
      | none => throw (IO.userError "depth must be a natural number")
  | _ => throw (IO.userError "usage: pccReplay --inspect DIR | --run DIR DEPTH")
