import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Violation
import Blanc.Lift.OrigKeys
import Blanc.Lift.WitnessSpawn
import Blanc.Lift.KernelBatchForall

/-!
# V− V4 freeze: the violating message's frame boundaries and its frozen statements

The V− violation is one root message: the code-free `creator` calls the reachable attacker
`AttackerR` at `attackerAddr` with the selector `0x12345678` (`violMsg`, value 0, 1,000,000
gas) over a world `W` with `Checkpoint W`.  Its frames, outermost first, with the step counts
the Lean interpreter takes over the reached checkpoint (scratch probe, not committed; the same
chain the V4 report measured):

* **F0** `AttackerR` (static machine `sR`, certificate `fsA`): 33 steps to its `CALL` of the
  clone `proxyAddr` (`remove_liquidity(200, [0, 0], attackerAddr)`, value 0, all gas); after
  its child, one step to `STOP` (gas left `gasV`);
* **F1** the clone's forwarder `fwdCode`: 11 steps to its `DELEGATECALL`; after it, 10 steps
  and `RETURN` (`gasFwd`);
* **F2** the implementation's `remove_liquidity` (`sRm`, certificate `fsI`): 339 steps to its
  ETH `CALL` of the attacker (value 100), holding lock slot 2, with the supply 2000 cached; the
  callback child; 234 steps to the token's `transfer(attackerAddr, 100)` (`childRun` by the
  token's certificate); 187 steps and `RETURN` (`gasRm`, `outRm`), the burn computed from the
  stale cached supply;
* **F3** the callback `AttackerR` (`sCb`, a code child of F2's `CALL`, value 100): 32 steps to
  its `CALL` of the clone (`add_liquidity([100, 0], 0, attackerAddr)`, value 100); after it,
  one step to `STOP` (`gasCb`);
* **F4** the clone's forwarder again: 11 steps to its `DELEGATECALL`; after it, 10 steps and
  `RETURN`;
* **F5** the re-entrant `add_liquidity` (`sRe`): 4,504 steps and `RETURN` (`gasRe`, `outRe`),
  taking lock slot 0 while slot 2 is held (step 2625, node `t_0370_c63`, the body past its
  guard) and minting 106 LP: `totalSupply = balanceOf[attackerAddr] = 2106`.

Settled: `totalSupply = 1800 < 1906 = balanceOf[attackerAddr]` (`storV`).

**Boundaries.** Every frame entry, a few interior chunk points of the long frames (each at a
named certificate node with no pending return), and every frame exit is a closed literal
(`Boundary.Bnd1` for configurations; gas, return data, accessed keys and addresses, and storage
and account prefixes for halts), printed by the Lean interpreter.  Each shadow is a literal
**prefix followed by the free tail** of `W` (`readStor ++ storTailOf W`, `readAcct ++
acctTailOf W`, `Checkpoint`'s `checkpoint_worldShadow`): the boundary kit with a tail
(`Boundary.cfgOfT`/`obsDT`, `Blanc/Lift/ShadowTail.lean`) decides the prefixes and leaves the
tails as terms, so a kernel decision against these boundaries holds for **every** `W` with
`Checkpoint W`.  The kernel's original state is the closed `O0 = origOf readStor`; a run is
transported to the actual original state `W` by `wrun_withOrig_keys`
(`Blanc/Lift/OrigKeys.lean`), which needs agreement only on the keys the run records
(`origAgreeOn_O0`: every frame's keys are `Checkpoint`'s read keys, `keys_sub_readKeys`).

**Statements.** The final part freezes, as propositions, the interface between the two proof
packages and the final theorems: `ReAddFrame` (package P1: the re-entrant frame F5),
`ViolationAt`/`ViolationStmt` (the universal violation), `CapstoneStmt` and `InstanceStmt`
(package P2).  This module proves none of them; it proves only cheap sanity facts about the
literals (`root_entry`, `shadows_extend_checkpoint`, `keys_sub_readKeys`, `boundary_values`,
`checkpoint_worldR`).  The frozen statement document (Plans evidence
`vyper-minus-reachable-reentrancy-v1/v4/frozen-statements.md`) gives each frame's statement.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-! ## The violating message -/

/-- The root call's calldata: `AttackerR`'s start selector. -/
def violCall : Bytes := [0x12, 0x34, 0x56, 0x78]

/-- The root call's gas. -/
def violGas : Nat := 1000000

/-- **The violating message**: the code-free `creator` calls `AttackerR` at `attackerAddr`
(value 0) over world `W`, at transaction depth 1024, with `W` its original state. -/
def violMsg (fork : Fork) (W : State) : Msg :=
  callMsg fork W attackerAddr AttackerR.code violCall violGas

/-- `remove_liquidity(200, [0, 0], attackerAddr)`, the calldata `AttackerR` sends the clone. -/
def removeCallR : Bytes :=
  [0x3e, 0xb1, 0x71, 0x9f] ++ abiWord 200 ++ abiWord 0 ++ abiWord 0 ++ abiWord attackerAddr.toNat

/-- `add_liquidity([100, 0], 0, attackerAddr)`, the calldata of the re-entry. -/
def reAddCall : Bytes :=
  [0x0c, 0x3e, 0x4b, 0x54] ++ abiWord 100 ++ abiWord 0 ++ abiWord 0 ++ abiWord attackerAddr.toNat

/-- `AttackerR`'s program (its lifted certificate). -/
abbrev fsA : List SFunc := Cert.prog AttackerR.cert

/-! ## The kernel's original state and the static machines of the certificate frames -/

/-- The kernel's closed original state: exactly `Checkpoint`'s storage read set. -/
def O0 : State := origOf readStor

/-- The block environment's static part every frame of the message carries (kernel form). -/
def violStat : BenvStat := { (default : BenvStat) with fork := .prague, origState := O0 }

/-- A frame's static machine in the message (kernel form): a call frame of `code` at `cur`. -/
def frameSevm (caller cur codeAdr : Adr) (gas : Nat) (value : B256) (data : Bytes)
    (code : ByteArray) (depth : Nat) (stv : Bool) : Sevm where
  caller := caller
  target := some cur
  currentTarget := cur
  gas := gas
  value := value
  data := data
  codeAddress := some codeAdr
  code := code
  depth := depth
  shouldTransferValue := stv
  isStatic := false
  disablePrecompiles := false
  benvStat := violStat
  tenvStat := rootTenv.stat

/-- F0: `AttackerR` as the root frame. -/
def sR : Sevm := frameSevm creator attackerAddr attackerAddr 1000000 0 violCall AttackerR.code 1024 true

/-- F2: the implementation's `remove_liquidity` (storage owner the clone). -/
def sRm : Sevm :=
  frameSevm attackerAddr proxyAddr implAddr 963749 0 removeCallR Vulnerable.code 1022 false

/-- F3: `AttackerR` called back by the pool with 100 wei. -/
def sCb : Sevm := frameSevm proxyAddr attackerAddr attackerAddr 907011 100 [] AttackerR.code 1021 true

/-- F5: the implementation's re-entrant `add_liquidity` (storage owner the clone, value 100). -/
def sRe : Sevm :=
  frameSevm attackerAddr proxyAddr implAddr 872071 100 reAddCall Vulnerable.code 1019 false

/-! ## The root frame's entry over a free world -/

/-- The account shadow of a world with `Checkpoint W`: the read prefix, then `W`'s own tail. -/
def acsW (W : State) : AcctShadow := readAcct ++ acctTailOf W

/-- The storage shadow of a world with `Checkpoint W`. -/
def storW (W : State) : StorShadow := readStor ++ storTailOf W

/-- The kernel's message: Prague, original state `O0`. -/
def rootMsgK (W : State) : Msg := (violMsg .prague W).withOrig O0

/-- The root frame's entry machine (kernel form). -/
def rootEvm (W : State) : Evm :=
  match frameEnterS (Frame.ofCall (rootMsgK W)) (acsW W) with
  | .run e => e
  | .done _ => default

/-- The root frame's start configuration (kernel form). -/
def rootCfg (W : State) : Cfg :=
  ⟨(rootEvm W).dyna, AttackerR.t_0000_c0, [], [], [], storW W, acsTransfer (rootMsgK W) (acsW W)⟩

/-! ## The boundaries (printed by the Lean interpreter over the reached checkpoint) -/

/-- Root frame entry: `AttackerR` at `attackerAddr`, called by `creator` (step 0). -/
def bR0 : Boundary.Bnd1 :=
  (⟨[], ⟨#[], 0⟩, 1000000, .zero⟩, AttackerR.t_0000_c0, [], [], [], [((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- `remove_liquidity` frame entry (step 0 of the implementation frame the outer forwarder's `DELEGATECALL` spawns). -/
def bRm0 : Boundary.Bnd1 :=
  (⟨[], ⟨#[], 0⟩, 963749, .zero⟩, Vulnerable.t_0000_c0, [], [], [implAddr, proxyAddr], [((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- `remove_liquidity` at step 161 (node `t_1af3_c23`): an optional chunk boundary before the ETH `CALL` (step 339). -/
def bRm161 : Boundary.Bnd1 :=
  (⟨[(1051816351 : Nat).toB256], ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 177, 113, 159, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68], 352⟩, 963111, .zero⟩, Vulnerable.t_1af3_c23, [], [], [implAddr, proxyAddr], [((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- Callback frame entry: `AttackerR` at `attackerAddr`, called by the pool with 100 wei (step 0). -/
def bCb0 : Boundary.Bnd1 :=
  (⟨[], ⟨#[], 0⟩, 907011, .zero⟩, AttackerR.t_0000_c0, [], [(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)], [attackerAddr, (4 : Adr), implAddr, proxyAddr], [((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- **Re-entrant `add_liquidity` frame entry** (P1's entry; step 0). -/
def bRe0 : Boundary.Bnd1 :=
  (⟨[], ⟨#[], 0⟩, 872071, .zero⟩, Vulnerable.t_0000_c0, [], [(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)], [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr], [((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- Re-entrant frame at step 1112 (node `t_0185_c2`). -/
def bRe1112 : Boundary.Bnd1 :=
  (⟨[(2 : Nat).toB256, (640 : Nat).toB256, (205409108 : Nat).toB256], ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232], 832⟩, 835580, .zero⟩, Vulnerable.t_0185_c2, [], [(proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)], [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr], [((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- Re-entrant frame at step 1159 (node `t_0158_c45`). -/
def bRe1159 : Boundary.Bnd1 :=
  (⟨[(2 : Nat).toB256, (640 : Nat).toB256, (205409108 : Nat).toB256], ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232], 832⟩, 835423, .zero⟩, Vulnerable.t_0158_c45, [], [(proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)], [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr], [((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- Re-entrant frame at step 2527 (node `t_02c4_c46`). -/
def bRe2527 : Boundary.Bnd1 :=
  (⟨[(2 : Nat).toB256, (800 : Nat).toB256, (205409108 : Nat).toB256], ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 179, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232], 928⟩, 828699, .zero⟩, Vulnerable.t_02c4_c46, [], [(proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)], [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr], [((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- Re-entrant frame at step 2625: `add_liquidity`'s body (node `t_0370_c63`, pc 0x370, past its guard), slot 0 taken while slot 2 is held. -/
def bReBody : Boundary.Bnd1 :=
  (⟨[(2 : Nat).toB256, (800 : Nat).toB256, (205409108 : Nat).toB256], ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232], 928⟩, 828357, .zero⟩, Vulnerable.t_0370_c63, [], [(proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)], [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr], [((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- Re-entrant frame at step 3088 (node `t_046d_c152`). -/
def bRe3088 : Boundary.Bnd1 :=
  (⟨[(0 : Nat).toB256, (0 : Nat).toB256, (0 : Nat).toB256, (0 : Nat).toB256, (2000 : Nat).toB256, (1000 : Nat).toB256, (1000 : Nat).toB256, (2000 : Nat).toB256, (1899 : Nat).toB256, (1000000000000000000 : Nat).toB256, (1000000000000000000 : Nat).toB256, (1000 : Nat).toB256, (900 : Nat).toB256, (10000 : Nat).toB256, (389733769954907444854315955391008805241582011460 : Nat).toB256, (205409108 : Nat).toB256], ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232], 928⟩, 826652, .zero⟩, Vulnerable.t_046d_c152, [], [(proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)], [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr], [((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- Re-entrant frame at step 4048 (node `t_04e0_c155`). -/
def bRe4048 : Boundary.Bnd1 :=
  (⟨[(0 : Nat).toB256, (0 : Nat).toB256, (0 : Nat).toB256, (0 : Nat).toB256, (2000 : Nat).toB256, (1000 : Nat).toB256, (1000 : Nat).toB256, (2000 : Nat).toB256, (1899 : Nat).toB256, (1000000000000000000 : Nat).toB256, (1000000000000000000 : Nat).toB256, (1000 : Nat).toB256, (900 : Nat).toB256, (10000 : Nat).toB256, (389733769954907444854315955391008805241582011460 : Nat).toB256, (205409108 : Nat).toB256], ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208], 1120⟩, 823493, .zero⟩, Vulnerable.t_04e0_c155, [], [(proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)], [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr], [((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- Re-entrant frame at step 4377 (node `t_056f_c4`); 127 steps before its `RETURN`. -/
def bRe4377 : Boundary.Bnd1 :=
  (⟨[(205409108 : Nat).toB256], ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208], 1120⟩, 822338, .zero⟩, Vulnerable.t_056f_c4, [], [(proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)], [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr], [((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)
/-- The re-entrant frame's return data (the minted amount). -/
def outRe : Bytes :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106]
/-- The re-entrant frame's accessed storage keys at its halt. -/
def keysRe : List (Adr × B256) :=
  [(proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)]
/-- The re-entrant frame's accessed addresses at its halt. -/
def adrsRe : List Adr :=
  [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr]
/-- The re-entrant frame's storage-shadow prefix at its halt (the free tail follows). -/
def storRe : StorShadow :=
  [((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2106 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2106 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)]
/-- The re-entrant frame's account-shadow prefix at its halt (the free tail follows). -/
def acsRe : AcctShadow :=
  [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)]
/-- The callback frame's accessed storage keys at its halt. -/
def keysCb : List (Adr × B256) :=
  [(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)]
/-- The callback frame's accessed addresses at its halt. -/
def adrsCb : List Adr :=
  [proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr]
/-- The callback frame's storage-shadow prefix at its halt. -/
def storCb : StorShadow :=
  [((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2106 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2106 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)]
/-- The callback frame's account-shadow prefix at its halt. -/
def acsCb : AcctShadow :=
  [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)]
/-- The `remove_liquidity` frame's return data. -/
def outRm : Bytes :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100]
/-- The `remove_liquidity` frame's accessed storage keys at its halt. -/
def keysRm : List (Adr × B256) :=
  [(proxyAddr, (7 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (proxyAddr, (7 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)]
/-- The `remove_liquidity` frame's accessed addresses at its halt. -/
def adrsRm : List Adr :=
  [(4 : Adr), tokenAddr, (4 : Adr), (4 : Adr), attackerAddr, (4 : Adr), implAddr, proxyAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, tokenAddr, (4 : Adr), (4 : Adr), attackerAddr, (4 : Adr), implAddr, proxyAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr]
/-- The `remove_liquidity` frame's storage-shadow prefix at its halt. -/
def storRm : StorShadow :=
  [((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (1800 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (1906 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (100 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2106 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2106 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)]
/-- The `remove_liquidity` frame's account-shadow prefix at its halt. -/
def acsRm : AcctShadow :=
  [((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)]
/-- The root frame's accessed storage keys at its halt. -/
def keysV : List (Adr × B256) :=
  [(proxyAddr, (7 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (proxyAddr, (7 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256), (proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (proxyAddr, (10 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)]
/-- The root frame's accessed addresses at its halt. -/
def adrsV : List Adr :=
  [proxyAddr, implAddr, proxyAddr, (4 : Adr), tokenAddr, (4 : Adr), (4 : Adr), attackerAddr, (4 : Adr), implAddr, proxyAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, tokenAddr, (4 : Adr), (4 : Adr), attackerAddr, (4 : Adr), implAddr, proxyAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr, implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr]
/-- The root frame's storage-shadow prefix at its halt: the settled world's storage before the free tail. -/
def storV : StorShadow :=
  [((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (1800 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (1906 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (100 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2106 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2106 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (900 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (1 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (2 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (14 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (26 : Nat).toB256), (2000 : Nat).toB256), ((proxyAddr, (84660355655810519959918999825310140898287098658970868295960858922642126597640 : Nat).toB256), (2000 : Nat).toB256), ((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256), (0 : Nat).toB256), ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256), (1000 : Nat).toB256)]
/-- The root frame's account-shadow prefix at its halt. -/
def acsV : AcctShadow :=
  [((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (100 : Nat).toB256, .empty, AttackerR.code⟩), (proxyAddr, ⟨1, (900 : Nat).toB256, .empty, fwdCode⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩)]

/-! ## Frame exits: gas left -/

/-- F5's gas left at its `RETURN`. -/
def gasRe : Nat := 809492
/-- F4's (the callback forwarder's) gas left at its `RETURN`. -/
def gasCbFwd : Nat := 823298
/-- F3's gas left at its `STOP`. -/
def gasCb : Nat := 837324
/-- The token child's gas left at its `RETURN` (`transfer(attackerAddr, 100)`, word 1). -/
def gasTok : Nat := 802488
/-- F2's gas left at its `RETURN`. -/
def gasRm : Nat := 810345
/-- F1's (the outer forwarder's) gas left at its `RETURN`. -/
def gasFwd : Nat := 825603
/-- F0's gas left at its `STOP`: the message's settled gas. -/
def gasV : Nat := 841183

/-! ## Sanity facts about the literals -/

/-- `Checkpoint`'s storage read keys. -/
def readKeys : List (Adr × B256) := readStor.map Prod.fst

/-- **The root entry over a free world**: for every `W`, the kernel's root frame enters with
the static machine `sR` at pc 0, and its start configuration is the boundary `bR0` with the
tails `storTailOf W`/`acctTailOf W` (the root value transfer's reads of `creator` and
`attackerAddr` stay in the prefix). -/
theorem root_entry : ∀ W : State,
    frameEnterS (Frame.ofCall (rootMsgK W)) (acsW W) = .run (rootEvm W) ∧
    (rootEvm W).pc = 0 ∧ (rootEvm W).sta = sR ∧
    Boundary.obsDT bR0 (.cont (rootCfg W)) =
      Boundary.obsDOkT bR0 (storTailOf W) (acctTailOf W) := by
  kernel_forall_rfl_and

/-- Every boundary's shadows are fresh entries followed by `Checkpoint`'s read prefixes. -/
theorem shadows_extend_checkpoint :
    (∀ b ∈ [bR0, bRm0, bRm161, bCb0, bRe0, bRe1112, bRe1159, bRe2527, bReBody, bRe3088, bRe4048,
        bRe4377],
      (Boundary.storOf1 b).drop ((Boundary.storOf1 b).length - readStor.length) = readStor ∧
      ((Boundary.acsOf1 b).drop ((Boundary.acsOf1 b).length - readAcct.length)).map
        Boundary.acctKey = readAcct.map Boundary.acctKey) ∧
    (∀ s ∈ [storRe, storCb, storRm, storV], s.drop (s.length - readStor.length) = readStor) ∧
    (∀ a ∈ [acsRe, acsCb, acsRm, acsV],
      (a.drop (a.length - readAcct.length)).map Boundary.acctKey = readAcct.map Boundary.acctKey) := by
  decide +kernel

/-- Every frame's accessed storage keys are `Checkpoint`'s read keys (what
`origAgreeOn_O0` needs to transport a run to the actual original state). -/
theorem keys_sub_readKeys :
    (∀ x ∈ keysRe, x ∈ readKeys) ∧ (∀ x ∈ keysCb, x ∈ readKeys) ∧
    (∀ x ∈ keysRm, x ∈ readKeys) ∧ (∀ x ∈ keysV, x ∈ readKeys) := by
  decide +kernel

/-- The values the frozen statements cite, read off the literals: the locks at F2's and F5's
entries and at F5's body, F5's mint, and the stale-supply burn at F2's and F0's halts. -/
theorem boundary_values :
    lookupS (Boundary.storOf1 bRm0) proxyAddr 2 = 0 ∧
    lookupS (Boundary.storOf1 bRe0) proxyAddr 2 = 1 ∧ lookupS (Boundary.storOf1 bRe0) proxyAddr 0 = 0 ∧
    lookupS (Boundary.storOf1 bRe0) proxyAddr 26 = 2000 ∧
    lookupS (Boundary.storOf1 bReBody) proxyAddr 0 = 1 ∧
    lookupS (Boundary.storOf1 bReBody) proxyAddr 2 = 1 ∧
    lookupS storRe proxyAddr 26 = 2106 ∧ lookupS storRe proxyAddr lpSlotA = 2106 ∧
    lookupS storRe proxyAddr 0 = 0 ∧ lookupS storRe proxyAddr 2 = 1 ∧
    lookupS storRm proxyAddr 26 = 1800 ∧ lookupS storRm proxyAddr lpSlotA = 1906 ∧
    lookupS storRm proxyAddr 2 = 0 ∧
    lookupS storV proxyAddr 26 = 1800 ∧ lookupS storV proxyAddr lpSlotA = 1906 ∧
    lookupS storV proxyAddr 2 = 0 := by
  decide +kernel

theorem readStor_lookup : ∀ e ∈ readStor, lookupS readStor e.1.1 e.1.2 = e.2 := by
  decide +kernel

/-- **The kernel's original state agrees with any `Checkpoint` world on `Checkpoint`'s read
keys**: the premise of `wrun_withOrig_keys`/`childRun_withOrig_keys` for every frame of the
message (with `keys_sub_readKeys`). -/
theorem origAgreeOn_O0 {O : State} (h : ∀ e ∈ readStor, storOf O e.1.1 e.1.2 = e.2)
    {D : List (Adr × B256)} (hD : ∀ x ∈ D, x ∈ readKeys) : OrigAgreeOn O0 O D := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hD x hx)
  show storOf O0 e.1.1 e.1.2 = storOf O e.1.1 e.1.2
  rw [O0, storOf_origOf, readStor_lookup e he, h e he]

/-! ## A closed world with `Checkpoint`: the standalone instance's pre-state -/

/-- The reached checkpoint's accounts, storage dropped. -/
def acctsR : List (Adr × Acct) :=
  [(creator, ⟨0, creatorFunds - 1000, .empty, .empty⟩),
   (implAddr, ⟨1, 0, .empty, Vulnerable.code⟩),
   (proxyAddr, ⟨1, 1000, .empty, fwdCode⟩),
   (tokenAddr, ⟨1, 0, .empty, Token20.code⟩),
   (attackerAddr, ⟨1, 0, .empty, AttackerR.code⟩)]

/-- A closed world with exactly the reached checkpoint's accounts and storage (`storAdd`). -/
def worldR : State := stateFoldStor (stateFoldAcct default acctsR) storAdd.reverse

/-- The closed world satisfies `Checkpoint`. -/
theorem checkpoint_worldR : Checkpoint worldR := by
  have hs : ∀ a k, storOf worldR a k = lookupS storAdd a k := fun a k => by
    rw [worldR, storOf_stateFoldStor _ (storOf_stateFoldAcct acctsR), storShadowOf_reverse]
  have ha : AcctAgree worldR (acctShadowOf acctsR) :=
    acctAgree_stateFoldStor _ (acctAgree_stateFoldAcct acctsR)
  refine ⟨fun e he => (hs e.1.1 e.1.2).trans (readStor_storAdd e he), fun e he => ?_, ?_⟩
  · refine (ha e.1).trans ?_
    simp only [readAcct, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> kernel_rfl
  · have h := congrArg Acct.code (ha creator)
    exact h.trans (by kernel_rfl)

/-! ## The frozen statements

Package **P1** proves `ReAddFrame`; package **P2** proves everything else (frames F0–F4, the
composition, the fork transport, `ViolationStmt`, `CapstoneStmt`, `InstanceStmt`), consuming
`ReAddFrame` by name.  Neither package edits this module. -/

/-- **P1: the re-entrant `add_liquidity` frame (F5), the package interface.**  For every
covered fork, every original state that agrees with `Checkpoint`'s read set, every pair of
shadow tails and every machine whose configuration is the boundary `bRe0` with those tails:
the frame is an `Exec` of the implementation's bytes from that machine (static machine `sRe`
with the original state and the fork changed) halting without error with `gasRe` gas left and
return data `outRe`; its settled machine is described by the halt's literal prefixes followed
by the same tails (`ChildAgree`); at step 2625 it is at `add_liquidity`'s body with lock slot 0
taken while lock slot 2 is held; and a non-create frame without state gas (the forwarder's
`DELEGATECALL` frame) settles to that machine. -/
def ReAddFrame : Prop :=
  ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    CoveredFork g → (∀ e ∈ readStor, storOf O e.1.1 e.1.2 = e.2) →
    Agree (Boundary.cfgOfT bRe0 tS tA m w) →
    ∃ post : Devm,
      Nonempty (Exec 0 ((sRe.withOrig O).withFork g) (Boundary.cfgOfT bRe0 tS tA m w).devm
        (.ok post)) ∧
      post.gasLeft = gasRe ∧ post.output = outRe ∧ post.error = none ∧
      ChildAgree post keysRe adrsRe (storRe ++ tS) (acsRe ++ tA) ∧
      (∃ cB : Cfg,
        wrun fsI ((sRe.withOrig O).withFork g) 2625 (Boundary.cfgOfT bRe0 tS tA m w) = .cont cB ∧
        Agree cB ∧ cB.f = Vulnerable.t_0370_c63 ∧
        storOf cB.devm.state proxyAddr 0 = 1 ∧ storOf cB.devm.state proxyAddr 2 = 1) ∧
      ∀ f : Frame, f.isCreate = false → f.inner.benv.stat.rules.stateGas = none →
        f.settle (.ok post) = .ok post

/-- **The violation, observed on one settled execution** of `violMsg g W`: the message
succeeds with `gasV` gas left and breaks the LP ledger (`totalSupply = 1800 < 1906 =
balanceOf[attackerAddr]`, non-wrapping, lock slot 2 released), and the same execution's frames
show the mechanism (the clauses of `vminus_witness`):
* the root frame is `AttackerR`, called by `creator`; at its `CALL` (step 33) it spawns the
  clone's forwarder, whose `DELEGATECALL` spawns the implementation running `remove_liquidity`
  for the clone's storage (F2);
* (a) F2 is entered with lock slot 2 free, and at its `CALL` (step 339) holds slot 2 with the
  supply 2000 cached, sending the attacker 100 wei; the attacker's callback (F3) `CALL`s the
  clone (step 32), whose forwarder's `DELEGATECALL` spawns the implementation again (F5) with
  `add_liquidity([100, 0], 0, attackerAddr)`, entered while slot 2 is held and slot 0 free; F5
  is an `Exec` of the real bytes, reaches `add_liquidity`'s body (step 2625, node
  `t_0370_c63`) with slot 0 taken while slot 2 is held, and mints: `totalSupply =
  balanceOf[attackerAddr] = 2106`, slot 0 released, slot 2 still held;
* (b) the two guards are on different slots in the deployed bytes (slot 2 at pcs 6900-6911,
  slot 0 at pcs 88-99);
* (c) F2 settles with `totalSupply = 1800` (the cached 2000 minus the 200 burned: the stale
  supply), `balanceOf[attackerAddr] = 1906`, slot 2 released. -/
def ViolationAt (g : Fork) (W : State) (post : Devm) : Prop :=
  processMessage (violMsg g W) = .ok post ∧ post.error = none ∧ post.gasLeft = gasV ∧
  storOf post.state proxyAddr 26 = 1800 ∧ storOf post.state proxyAddr lpSlotA = 1906 ∧
  (storOf post.state proxyAddr 26).toNat < (storOf post.state proxyAddr lpSlotA).toNat ∧
  storOf post.state proxyAddr 2 = 0 ∧
  ∃ (e0 e1 e1' e2 e3 e4 e4' e5 : Evm) (c0 cR c2 c339 c3 cA c5 cB : Cfg) (post2 post5 : Devm),
    -- the root frame: `AttackerR`, called by the code-free creator
    (Frame.ofCall (violMsg g W)).enter = .run e0 ∧ Nonempty (Exec e0.pc e0.sta e0.dyna (.ok post)) ∧
    e0.sta.caller = creator ∧ e0.sta.currentTarget = attackerAddr ∧ e0.sta.code = AttackerR.code ∧
    c0.devm = e0.dyna ∧ c0.f = AttackerR.t_0000_c0 ∧ c0.K = [] ∧ Agree c0 ∧
    wrun fsA e0.sta 33 c0 = .cont cR ∧ Agree cR ∧ SpawnedBy e0.sta cR.devm .call e1 ∧
    e1.sta.currentTarget = proxyAddr ∧ e1.sta.code = fwdCode ∧
    stepN 11 e1 = some e1' ∧ SpawnedBy e1'.sta e1'.dyna .delegatecall e2 ∧
    -- (a) F2: `remove_liquidity` takes slot 2 and, holding it, sends the attacker 100 wei
    e2.sta.currentTarget = proxyAddr ∧ e2.sta.code = Vulnerable.code ∧ e2.sta.data = removeCallR ∧
    Nonempty (Exec e2.pc e2.sta e2.dyna (.ok post2)) ∧ post2.error = none ∧
    storOf e2.dyna.state proxyAddr 2 = 0 ∧
    c2.devm = e2.dyna ∧ c2.f = Vulnerable.t_0000_c0 ∧ c2.K = [] ∧ Agree c2 ∧
    wrun fsI e2.sta 339 c2 = .cont c339 ∧ Agree c339 ∧
    storOf c339.devm.state proxyAddr 2 = 1 ∧ storOf c339.devm.state proxyAddr 26 = 2000 ∧
    SpawnedBy e2.sta c339.devm .call e3 ∧
    e3.sta.currentTarget = attackerAddr ∧ e3.sta.code = AttackerR.code ∧ e3.sta.value = 100 ∧
    -- the callback re-enters the clone: F5 runs `add_liquidity` while slot 2 is held
    c3.devm = e3.dyna ∧ c3.f = AttackerR.t_0000_c0 ∧ c3.K = [] ∧ Agree c3 ∧
    wrun fsA e3.sta 32 c3 = .cont cA ∧ Agree cA ∧ SpawnedBy e3.sta cA.devm .call e4 ∧
    e4.sta.currentTarget = proxyAddr ∧ e4.sta.code = fwdCode ∧ e4.sta.value = 100 ∧
    stepN 11 e4 = some e4' ∧ SpawnedBy e4'.sta e4'.dyna .delegatecall e5 ∧
    e5.sta.currentTarget = proxyAddr ∧ e5.sta.code = Vulnerable.code ∧ e5.sta.data = reAddCall ∧
    storOf e5.dyna.state proxyAddr 2 = 1 ∧ storOf e5.dyna.state proxyAddr 0 = 0 ∧
    Nonempty (Exec e5.pc e5.sta e5.dyna (.ok post5)) ∧ post5.error = none ∧
    c5.devm = e5.dyna ∧ c5.f = Vulnerable.t_0000_c0 ∧ c5.K = [] ∧ Agree c5 ∧
    wrun fsI e5.sta 2625 c5 = .cont cB ∧ Agree cB ∧ cB.f = Vulnerable.t_0370_c63 ∧
    storOf cB.devm.state proxyAddr 0 = 1 ∧ storOf cB.devm.state proxyAddr 2 = 1 ∧
    storOf post5.state proxyAddr 26 = 2106 ∧ storOf post5.state proxyAddr lpSlotA = 2106 ∧
    storOf post5.state proxyAddr 0 = 0 ∧ storOf post5.state proxyAddr 2 = 1 ∧
    -- (b) the two guards: slot 2 (`remove_liquidity`) and slot 0 (`add_liquidity`)
    (Vulnerable.code.getInst 6900 = some (.next (.push [0x02] (by decide))) ∧
      Vulnerable.code.getInst 6902 = some (.next (.reg .sload)) ∧
      Vulnerable.code.getInst 6911 = some (.next (.reg .sstore))) ∧
    (Vulnerable.code.getInst 88 = some (.next (.push [0x00] (by decide))) ∧
      Vulnerable.code.getInst 90 = some (.next (.reg .sload)) ∧
      Vulnerable.code.getInst 99 = some (.next (.reg .sstore))) ∧
    -- (c) F2 burns with the stale cached supply and releases slot 2
    storOf post2.state proxyAddr 26 = 1800 ∧ storOf post2.state proxyAddr lpSlotA = 1906 ∧
    storOf post2.state proxyAddr 2 = 0

/-- **The universal V− violation (P2).**  For every covered fork and every world `W` with
`Checkpoint W`, the violating message settles to a machine on which `ViolationAt` holds. -/
def ViolationStmt : Prop :=
  ∀ g : Fork, CoveredFork g → ∀ W : State, Checkpoint W → ∃ post : Devm, ViolationAt g W post

/-- **The reachable V− capstone (P2).**  For every covered fork, eight root messages compose from
the disclosed initial world, each from the previous settled world: the seven setup messages
(`setup_reaches_checkpoint`), reaching a world with the sound LP ledger (`SoundCheckpoint`)
and `Checkpoint`, then the violating message, on whose settled machine `ViolationAt` holds. -/
def CapstoneStmt : Prop :=
  ∀ fork : Fork, CoveredFork fork →
    ∃ postI postP postC tokenPost attackerPost approvePost addPost post : Devm,
      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧
      processMessage (initMsg fork postP.state) = .ok postC ∧
      processCreateMessage (tokenCreateMsg fork postC.state) = .ok tokenPost ∧
      processCreateMessage (attackerCreateMsg fork tokenPost.state) = .ok attackerPost ∧
      processMessage (approveMsg fork attackerPost.state) = .ok approvePost ∧
      processMessage (addMsg fork approvePost.state) = .ok addPost ∧
      SoundCheckpoint addPost.state ∧ Checkpoint addPost.state ∧
      ViolationAt fork addPost.state post

/-- **The standalone instance (P2)**: the violation at the closed checkpoint world `worldR`
(`checkpoint_worldR`), under every covered fork. -/
def InstanceStmt : Prop :=
  ∀ g : Fork, CoveredFork g → ∃ post : Devm, ViolationAt g worldR post

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
