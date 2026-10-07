import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.World

/-!
# V+ setup message 3: the kernel run of `initialize` through the clone

The frames of the call, as configurations of the node-exposing walks of
`Blanc/Lift/NodeWalk.lean`, over the creations' settled world `world2` (a closed term; the
walks read the world through the shadows `acs0`/`stor0`, and the kernel evaluates it only for
the `SSTORE` original values), at Prague (kernel decisions: do not open this file in the
language server).  The step counts were printed by the Lean interpreter (`#eval` over the
walks, in a scratch file) and agree with an EELS trace of the same message (the V2 report).

* `top`, the forwarder at the clone: 11 steps to its `DELEGATECALL` (pc 31), then 10 steps and
  `RETURN` after its child;
* `B`, the implementation's runtime in the clone's storage: 393 steps to the `STATICCALL` of the
  identity precompile `0x04` (pc 3515, the `concat` copy of the 23-byte name), which answers at
  once; then 154 steps and `STOP` (pc 3866).  Every walk holds the hash policy `.avoid 0`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach

/-- The kernel's top-level frame over the input world `W` (Prague). -/
def fI (W : State) : Frame := Frame.ofCall (callMsg .prague W initCall 1000000)

/-! ### The forwarder frame up to its `DELEGATECALL` -/

def eI (W : State) : Evm := runOr (frameEnterS (fI W) acs0)
def cI (W : State) : PCfg := childCfg (eI W) (fI W) [] [] stor0 acs0
def cI1 (W : State) : PCfg := cfgOr (cI W) (pwalkH .refuse fwdTries (eI W).sta okAny 11 (cI W))
def cpI (W : State) : CallPrep :=
  prepOr (dcallPrep (eI W).sta (cI1 W).devm (cI1 W).adrs (cI1 W).acs)

/-! ### The implementation frame up to the identity `STATICCALL` -/

def eIB (W : State) : Evm := runOr (frameEnterS (cpI W).f (cI1 W).acs)
def cIB0 (W : State) : PCfg :=
  childCfg (eIB W) (cpI W).f (cI1 W).keys (cpI W).adrs (cI1 W).stor (cI1 W).acs
def cIB1 (W : State) : PCfg :=
  cfgOr (cIB0 W) (pwalkH (.avoid 0) codeTries (eIB W).sta okAny 393 (cIB0 W))
def cpId (W : State) : CallPrep :=
  prepOr (scallPrep (eIB W).sta (cIB1 W).devm (cIB1 W).adrs (cIB1 W).acs)

/-- The identity precompile's answer. -/
def chId (W : State) : Devm :=
  match frameEnterS (cpId W).f (cIB1 W).acs with
  | .done (.ok d) => d
  | _ => default

/-! ### The implementation frame after the precompile, and `STOP` -/

def dIB2 (W : State) : Devm := resumeOr (cpId W) (chId W)
def cIB2 (W : State) : PCfg :=
  ⟨(cIB1 W).pc + 1, dIB2 W, (cIB1 W).keys, (cpId W).adrs, (cIB1 W).stor,
    acsTransfer (cpId W).f.inner (cIB1 W).acs⟩
def cIB3 (W : State) : PCfg :=
  cfgOr (cIB0 W) (pwalkH (.avoid 0) codeTries (eIB W).sta okAny 154 (cIB2 W))
def dIB (W : State) : Devm := haltOf (pwalkH (.avoid 0) codeTries (eIB W).sta okAny 1 (cIB3 W))

/-! ### The forwarder after the implementation frame, and `RETURN` -/

def dI2 (W : State) : Devm := resumeOr (cpI W) (dIB W)
def cI2 (W : State) : PCfg :=
  ⟨(cI1 W).pc + 1, dI2 W, (cI1 W).keys ++ (cIB3 W).keys, (cpI W).adrs ++ (cIB3 W).adrs,
    (cIB3 W).stor, (cIB3 W).acs⟩
def cI3 (W : State) : PCfg :=
  cfgOr (cI2 W) (pwalkH .refuse fwdTries (eI W).sta okAny 10 (cI2 W))
def dI (W : State) : Devm := haltOf (pwalkH .refuse fwdTries (eI W).sta okAny 1 (cI3 W))

/-! ## The pool storage the run leaves -/

/-- `"Curve.fi Factory Pool: "` (the name prefix; the name argument is empty). -/
def nameBytes : Bytes :=
  [0x43, 0x75, 0x72, 0x76, 0x65, 0x2e, 0x66, 0x69, 0x20, 0x46, 0x61, 0x63, 0x74, 0x6f, 0x72, 0x79, 0x20, 0x50, 0x6f, 0x6f, 0x6c, 0x3a, 0x20]

/-- `"-f"` (the symbol suffix; the symbol argument is empty). -/
def symbolBytes : Bytes := [0x2d, 0x66]

/-- A short string's data word: its bytes left-aligned in 32 bytes. -/
def leftWord (s : Bytes) : B256 := Bytes.toB256 (s ++ List.replicate (32 - s.length) 0)

/-- `"v6.0.1"`, the source's `version` constant. -/
def versionBytes : Bytes := [0x76, 0x36, 0x2e, 0x30, 0x2e, 0x31]

/-- `"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"`. -/
def eip712TypeBytes : Bytes :=
  [0x45, 0x49, 0x50, 0x37, 0x31, 0x32, 0x44, 0x6f, 0x6d, 0x61, 0x69, 0x6e, 0x28, 0x73, 0x74, 0x72, 0x69, 0x6e, 0x67, 0x20, 0x6e, 0x61, 0x6d, 0x65, 0x2c, 0x73, 0x74, 0x72, 0x69, 0x6e, 0x67, 0x20, 0x76, 0x65, 0x72, 0x73, 0x69, 0x6f, 0x6e, 0x2c, 0x75, 0x69, 0x6e, 0x74, 0x32, 0x35, 0x36, 0x20, 0x63, 0x68, 0x61, 0x69, 0x6e, 0x49, 0x64, 0x2c, 0x61, 0x64, 0x64, 0x72, 0x65, 0x73, 0x73, 0x20, 0x76, 0x65, 0x72, 0x69, 0x66, 0x79, 0x69, 0x6e, 0x67, 0x43, 0x6f, 0x6e, 0x74, 0x72, 0x61, 0x63, 0x74, 0x29]

/-- `keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")`. -/
def eip712Typehash : B256 := Bytes.keccak eip712TypeBytes

/-- **The clone's EIP-712 domain separator**, by its definition:
`keccak256(abi.encode(TYPEHASH, keccak256(name), keccak256("v6.0.1"), chain id, clone))`. -/
def domainSeparator : B256 :=
  Bytes.keccak (Witness.word eip712Typehash.toNat ++ Witness.word (Bytes.keccak nameBytes).toNat ++
    Witness.word (Bytes.keccak versionBytes).toNat ++ Witness.word chainIdV2.toNat ++
    Witness.word proxyAddr.toNat)

/-- The packed `(last_price, ma_price) = (10^18, 10^18)`. -/
def packedPrices : B256 := (1000000000000000000 + 1000000000000000000 * 2 ^ 128 : Nat).toB256

/-- **The world's storage after `initialize`**, newest write first (slots of the clone, then
the implementation's `factory`).  Slot names from the source's field order, each located at its
writing `SSTORE` in the V2 report: `0x17 DOMAIN_SEPARATOR`, `0x13`/`0x12` symbol data/length,
`0x10`/`0x0f` name data/length, `0x1b ma_last_time`, `0x19 last_prices_packed`,
`0x1a ma_exp_time`, `0x01 factory`, `0x0a future_A`, `0x09 initial_A`, `0x03`/`0x02 coins`,
`0x0e originator`.  `fee` (`0x06`) is written 0 and holds nothing. -/
def storInit : StorShadow :=
  [((proxyAddr, 0x17), domainSeparator),
   ((proxyAddr, 0x13), leftWord symbolBytes),
   ((proxyAddr, 0x12), (2 : Nat).toB256),
   ((proxyAddr, 0x10), leftWord nameBytes),
   ((proxyAddr, 0x0f), (23 : Nat).toB256),
   ((proxyAddr, 0x1b), timeV2),
   ((proxyAddr, 0x19), packedPrices),
   ((proxyAddr, 0x1a), (866 : Nat).toB256),
   ((proxyAddr, 0x01), creator.toNat.toB256),
   ((proxyAddr, 0x0a), (100 : Nat).toB256),
   ((proxyAddr, 0x09), (100 : Nat).toB256),
   ((proxyAddr, 0x03), tokenAddr.toNat.toB256),
   ((proxyAddr, 0x02), ethSentinel.toB256),
   ((proxyAddr, 0x0e), creator.toNat.toB256),
   ((implAddr, 1), 1)]

/-! ## The kernel decisions -/

/-- The forwarder to its `DELEGATECALL`, and the implementation frame to the identity call. -/
theorem initFactsA :
    frameEnterS (fI world2) acs0 = .run (eI world2) ∧
    ((eI world2).pc, (eI world2).sta.currentTarget, (eI world2).sta.code, (eI world2).sta.benvStat.fork,
      (eI world2).sta.benvStat.excessBlobGas) =
      (0, proxyAddr, Blanc.forwarderCode Blanc.curvePlainImpl847e, .prague, 0) ∧
    pwalkH .refuse fwdTries (eI world2).sta okAny 11 (cI world2) = .cont (cI1 world2) ∧
    (cI1 world2).pc = 31 ∧
    decodeT 6 fwdTries.bytes 31 = some (.next (.exec .delegatecall)) ∧
    dcallPrep (eI world2).sta (cI1 world2).devm (cI1 world2).adrs (cI1 world2).acs = some (cpI world2) ∧
    frameEnterS (cpI world2).f (cI1 world2).acs = .run (eIB world2) ∧
    ((eIB world2).pc, (eIB world2).sta.currentTarget, (eIB world2).sta.code) = (0, proxyAddr, code) ∧
    (cpI world2).f.inner.codeAddress = some implAddr ∧
    pwalkH (.avoid 0) codeTries (eIB world2).sta okAny 393 (cIB0 world2) = .cont (cIB1 world2) ∧
    (cIB1 world2).pc = 3515 ∧
    decodeT 15 codeTries.bytes 3515 = some (.next (.exec .staticcall)) ∧
    scallPrep (eIB world2).sta (cIB1 world2).devm (cIB1 world2).adrs (cIB1 world2).acs = some (cpId world2) ∧
    (cpId world2).f.inner.codeAddress = some 4 ∧
    frameEnterS (cpId world2).f (cIB1 world2).acs = .done (.ok (chId world2)) ∧
    (chId world2).error = none ∧
    resumeCallB (cpId world2).p (cpId world2).oi (cpId world2).os (.ok (chId world2)) = some (dIB2 world2) := by
  kernel_rfl_and

/-- The implementation frame after the identity call, `STOP`, and the forwarder's tail. -/
theorem initFactsB :
    pwalkH (.avoid 0) codeTries (eIB world2).sta okAny 154 (cIB2 world2) = .cont (cIB3 world2) ∧
    pwalkH (.avoid 0) codeTries (eIB world2).sta okAny 1 (cIB3 world2) = .halt (.ok (dIB world2)) ∧
    (dIB world2).error = none ∧
    resumeCallB (cpI world2).p (cpI world2).oi (cpI world2).os (.ok (dIB world2)) = some (dI2 world2) ∧
    pwalkH .refuse fwdTries (eI world2).sta okAny 10 (cI2 world2) = .cont (cI3 world2) ∧
    pwalkH .refuse fwdTries (eI world2).sta okAny 1 (cI3 world2) = .halt (.ok (dI world2)) ∧
    (dI world2).error = none ∧ (dI world2).gasLeft = 679367 ∧ (dI world2).refundCounter = 0 := by
  kernel_rfl_and

/-- The shadows the run leaves: its canonical storage log is `storInit`; its account log
names the identity precompile, the clone, the creator and the implementation, each read as at
the start. -/
theorem initFactsC :
    canonS (cI3 world2).stor = storInit ∧
    (cI3 world2).acs.map Prod.fst = [4, proxyAddr, proxyAddr, creator, creator, proxyAddr, implAddr] ∧
    lookupA (cI3 world2).acs 4 = lookupA acs0 4 ∧
    lookupA (cI3 world2).acs proxyAddr = lookupA acs0 proxyAddr ∧
    lookupA (cI3 world2).acs creator = lookupA acs0 creator ∧
    lookupA (cI3 world2).acs implAddr = lookupA acs0 implAddr := by
  kernel_rfl_and

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
