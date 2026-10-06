import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.AddSetup
import Blanc.Lift.KernelBatchForall
import Blanc.Lift.ShadowCanon

/-!
# V− setup, message 7: the kernel run of the first `add_liquidity`

Prague kernel decisions over an **arbitrary** input world `W` (a free variable: the walk reads
the world only through the shadows `acs6`/`stor6`), with the transaction-original state
replaced by the closed `world6` (the only place the run reads it is the `SSTORE` charge; see
`AddSetup.lean`).  Do not open this file in the language server.  The frames of the message,
outermost first, with step counts printed by the Lean interpreter over the same configurations:

* the forwarder `fwdCode` at `proxyAddr` (1000 wei transferred in at entry): 11 steps to its
  `DELEGATECALL` (pc 31); after its child, 10 steps and `RETURN` (pc 44);
* the implementation frame (storage owner `proxyAddr`, code `Vulnerable.code`, calldata
  `addCall`, call value 1000): 2023 steps of the registered 0x6326 certificate (`wrun`) to its
  `CALL` of the token's `transferFrom(creator, proxyAddr, 1000)`; the token child, run by the
  token's own certificate (`childRun`); the resume; 186 steps to its `RETURN` of the minted
  amount 2000.

The final storage shadow, canonicalized (`canonS`: shadowed and zero writes dropped), is
`storAdd`: the pool's `totalSupply` (slot 26) and `balanceOf[attacker]` (`lpSlotA`) 2000,
`balances` (slots 8, 9) 1000 each, the token's `balanceOf[proxy] = 1000`,
`balanceOf[creator] = 999000` (the allowance spent to zero), and the untouched configuration.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable (cert t_0000_c0 t_0185_c2 t_056f_c4)

/-- The pool's `balanceOf[attackerAddr]` slot, `keccak256(pad32(24) ‖ pad32(attackerAddr))`, as a
literal (`lpSlotA_eq` evaluates the hash once). -/
def lpSlotA : B256 :=
  84660355655810519959918999825310140898287098658970868295960858922642126597640

theorem lpSlotA_eq :
    lpSlotA = Bytes.keccak (abiWord 24 ++ abiWord attackerAddr.toNat) := by
  kernel_rfl

/-- The forwarder at its `DELEGATECALL` (pc 31). -/
def eA31 (W : State) : Evm := (stepN 11 (eA W)).getD default

/-- The forwarder's `DELEGATECALL` up to its spawn. -/
def cpA (W : State) : CallPrep := (dcallPrep (eA31 W).sta (eA31 W).dyna [] acsA).getD noPrepI

/-- The implementation frame's entry machine. -/
def eB (W : State) : Evm :=
  match frameEnterS (cpA W).f acsA with | .run e => e | .done _ => default

/-- The implementation frame's static machine with the original state `world6`: the machine
the kernel runs (`wrun_withOrig` transports its runs to `(eB W).sta`). -/
def sB (W : State) : Sevm := (eB W).sta.withOrig world6

/-- The implementation frame's start configuration. -/
def cB0 (W : State) : Cfg :=
  ⟨(eB W).dyna, t_0000_c0, [], [], (cpA W).adrs, stor6, acsTransfer (cpA W).f.inner acsA⟩

/-- The kernel's implementation-frame machine, closed (`sB_eq`: it is `sB W` for every `W`). -/
def sBc : Sevm := sB world6

/-! ### The boundaries (printed by the Lean interpreter over the same configurations) -/

/-- The implementation frame's entry. -/
def bAdd0 : Boundary.Bnd1 :=
  (⟨[], ⟨#[], 0⟩, 981763, .zero⟩, t_0000_c0, [], [], [implAddr], [((tokenAddr, (14759267106877659846041667251020382311670702899506369221369802620944854706670 : Nat).toB256), (1000 : Nat).toB256), ((tokenAddr, (97433442488726861213578988847752201310395502865 : Nat).toB256), (1000000 : Nat).toB256), ((proxyAddr, (22 : Nat).toB256), (20534296586854382678417119990996247571837989427425521718122903977259886968832 : Nat).toB256), ((proxyAddr, (21 : Nat).toB256), (2 : Nat).toB256), ((proxyAddr, (18 : Nat).toB256), (30512471952670789164122273054066300063710012785238889216544515826871133274112 : Nat).toB256), ((proxyAddr, (17 : Nat).toB256), (23 : Nat).toB256), ((proxyAddr, (5 : Nat).toB256), (97433442488726861213578988847752201310395502865 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (11 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (6 : Nat).toB256), (1364068194842176056990105843868530818345537040110 : Nat).toB256), ((implAddr, (10 : Nat).toB256), (31337 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (proxyAddr, ⟨1, (0 : Nat).toB256, .empty, fwdCode⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (creator, ⟨0, (1000000000000000000 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)

/-- Step 769 (node `t_0185_c2`). -/
def bAdd769 : Boundary.Bnd1 :=
  (⟨[(2 : Nat).toB256, (640 : Nat).toB256, (205409108 : Nat).toB256], ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 832⟩, 942405, .zero⟩, t_0185_c2, [], [(proxyAddr, (26 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256)], [implAddr], [((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((tokenAddr, (14759267106877659846041667251020382311670702899506369221369802620944854706670 : Nat).toB256), (1000 : Nat).toB256), ((tokenAddr, (97433442488726861213578988847752201310395502865 : Nat).toB256), (1000000 : Nat).toB256), ((proxyAddr, (22 : Nat).toB256), (20534296586854382678417119990996247571837989427425521718122903977259886968832 : Nat).toB256), ((proxyAddr, (21 : Nat).toB256), (2 : Nat).toB256), ((proxyAddr, (18 : Nat).toB256), (30512471952670789164122273054066300063710012785238889216544515826871133274112 : Nat).toB256), ((proxyAddr, (17 : Nat).toB256), (23 : Nat).toB256), ((proxyAddr, (5 : Nat).toB256), (97433442488726861213578988847752201310395502865 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (11 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (6 : Nat).toB256), (1364068194842176056990105843868530818345537040110 : Nat).toB256), ((implAddr, (10 : Nat).toB256), (31337 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (proxyAddr, ⟨1, (0 : Nat).toB256, .empty, fwdCode⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (creator, ⟨0, (1000000000000000000 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)

/-- Step 1898 (node `t_056f_c4`). -/
def bAdd1898 : Boundary.Bnd1 :=
  (⟨[(205409108 : Nat).toB256], ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 208], 928⟩, 898700, .zero⟩, t_056f_c4, [], [(proxyAddr, (26 : Nat).toB256), (proxyAddr, (16 : Nat).toB256), (proxyAddr, (15 : Nat).toB256), (proxyAddr, (9 : Nat).toB256), (proxyAddr, (8 : Nat).toB256), (proxyAddr, (12 : Nat).toB256), (proxyAddr, (14 : Nat).toB256), (proxyAddr, (0 : Nat).toB256)], [implAddr], [((proxyAddr, (9 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (8 : Nat).toB256), (1000 : Nat).toB256), ((proxyAddr, (0 : Nat).toB256), (1 : Nat).toB256), ((tokenAddr, (14759267106877659846041667251020382311670702899506369221369802620944854706670 : Nat).toB256), (1000 : Nat).toB256), ((tokenAddr, (97433442488726861213578988847752201310395502865 : Nat).toB256), (1000000 : Nat).toB256), ((proxyAddr, (22 : Nat).toB256), (20534296586854382678417119990996247571837989427425521718122903977259886968832 : Nat).toB256), ((proxyAddr, (21 : Nat).toB256), (2 : Nat).toB256), ((proxyAddr, (18 : Nat).toB256), (30512471952670789164122273054066300063710012785238889216544515826871133274112 : Nat).toB256), ((proxyAddr, (17 : Nat).toB256), (23 : Nat).toB256), ((proxyAddr, (5 : Nat).toB256), (97433442488726861213578988847752201310395502865 : Nat).toB256), ((proxyAddr, (10 : Nat).toB256), (0 : Nat).toB256), ((proxyAddr, (12 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (11 : Nat).toB256), (10000 : Nat).toB256), ((proxyAddr, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (7 : Nat).toB256), (292300327466180583640736966543256603931186508595 : Nat).toB256), ((proxyAddr, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256), ((proxyAddr, (6 : Nat).toB256), (1364068194842176056990105843868530818345537040110 : Nat).toB256), ((implAddr, (10 : Nat).toB256), (31337 : Nat).toB256)], [(proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩), (creator, ⟨0, (999999999999999000 : Nat).toB256, .empty, .empty⟩), (attackerAddr, ⟨1, (0 : Nat).toB256, .empty, AttackerR.code⟩), (tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩), (proxyAddr, ⟨1, (0 : Nat).toB256, .empty, fwdCode⟩), (implAddr, ⟨1, (0 : Nat).toB256, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩), (creator, ⟨0, (1000000000000000000 : Nat).toB256, .empty, .empty⟩)], [], [], none, false)

/-- The implementation frame from step 1898: 125 steps to the token `CALL`, the token child run
by its own certificate, the resume, 186 steps to `RETURN`. -/
def callEnd (sta : Sevm) (c : Cfg) : Res :=
  match wrun fsI sta 125 c with
  | .cont c3 =>
    match childRun Token20.prog Token20.code sta 200 c3 with
    | .done (.halted d2) cl =>
      if d2.error.isNone then
        match callResume sta c3 d2 cl.keys cl.adrs cl.stor cl.acs with
        | some c4 => wrun fsI sta 186 c4
        | none => .stuck
      else .stuck
    | _ => .stuck
  | _ => .stuck

/-- The implementation frame's settled machine as its parent sees it. -/
abbrev obsChildB (d : Devm) : Devm := childObs 811048 (abiWord 2000) d

/-- The forwarder resumed from its settled child. -/
def dA2 (W : State) (d : Devm) : Devm :=
  (resumeCallB (cpA W).p (cpA W).oi (cpA W).os (.ok d)).getD default

/-- The forwarder at its `RETURN` (pc 44). -/
def eA44 (W : State) (d : Devm) : Evm := (stepN 10 ⟨32, (eA W).sta, dA2 W d⟩).getD default

/-- The forwarder's halted machine: message 7's result. -/
def postA (W : State) (d : Devm) : Devm :=
  match Evm.step (eA44 W d) with
  | .halt (.ok d') => d'
  | _ => default

/-- The pool's and the token's storage after message 7, canonical (newest first). -/
def storAdd : StorShadow :=
  [((proxyAddr, 26), 2000), ((proxyAddr, lpSlotA), 2000),
   ((tokenAddr, Token20.balSlot proxyAddr), 1000), ((tokenAddr, creator.toB256), 999000),
   ((proxyAddr, 9), 1000), ((proxyAddr, 8), 1000)] ++
  initWrites.filter (fun e => decide (e.2 ≠ 0)) ++ stor2

/-- The account shadow the implementation frame halts with (its entries' views, newest first:
the identity precompile and the clone restated by the calls, the token child's, the value
moved at the message's entry). -/
def acsB : AcctShadow :=
  [((4 : Adr), ⟨0, 0, .empty, .empty⟩), (proxyAddr, ⟨1, 1000, .empty, fwdCode⟩),
   (tokenAddr, ⟨1, 0, .empty, Token20.code⟩), (proxyAddr, ⟨1, 1000, .empty, fwdCode⟩),
   ((4 : Adr), ⟨0, 0, .empty, .empty⟩), (proxyAddr, ⟨1, 1000, .empty, fwdCode⟩),
   ((4 : Adr), ⟨0, 0, .empty, .empty⟩), (proxyAddr, ⟨1, 1000, .empty, fwdCode⟩),
   (proxyAddr, ⟨1, 1000, .empty, fwdCode⟩),
   (creator, ⟨0, creatorFunds - 1000, .empty, .empty⟩)] ++ acs6

/-- What the implementation frame's halt shows, decided value by value. -/
def obsB (r : Res) : Bool :=
  match r with
  | .done (.halted d) cl =>
    decide (d.gasLeft = 811048) && decide (d.output = abiWord 2000) && d.error.isNone &&
      decide (canonS cl.stor = storAdd) &&
      decide (cl.acs.map Boundary.acctKey = acsB.map Boundary.acctKey)
  | _ => false

/-- The account entries' storage and code at the halt (compared as terms). -/
def restB (r : Res) : List (Stor × ByteArray) :=
  match r with
  | .done (.halted _) cl => cl.acs.map Boundary.acctRest
  | _ => []

/-! ### The kernel decisions -/

/-- **The forwarder to its `DELEGATECALL` and the implementation frame's entry**, over any
`W`: the entry decided against the boundary `bAdd0`, and the closed kernel machine. -/
theorem addFacts0 : ∀ W : State,
    frameEnterS (frameA W) acs6 = .run (eA W) ∧
    stepN 11 (eA W) = some (eA31 W) ∧
    dcallPrep (eA31 W).sta (eA31 W).dyna [] acsA = some (cpA W) ∧
    frameEnterS (cpA W).f acsA = .run (eB W) ∧
    Boundary.obsD1 bAdd0 (.cont (cB0 W)) = Boundary.obsDOk1 bAdd0 ∧
    sB W = sBc := by
  kernel_forall_rfl_and

/-- Steps 0 to 769, over any world and bookkeeping. -/
theorem addChunk1 : ∀ m w, Boundary.obsD1 bAdd769 (wrun fsI sBc 769 (Boundary.cfgOf1 bAdd0 m w)) =
    Boundary.obsDOk1 bAdd769 := by
  kernel_forall_rfl

/-- Steps 769 to 1898, over any world and bookkeeping. -/
theorem addChunk2 : ∀ m w,
    Boundary.obsD1 bAdd1898 (wrun fsI sBc 1129 (Boundary.cfgOf1 bAdd769 m w)) =
      Boundary.obsDOk1 bAdd1898 := by
  kernel_forall_rfl

/-- From step 1898: the token `CALL`, its child, the resume and the `RETURN`, decided. -/
theorem addChunk3 : ∀ m w, obsB (callEnd sBc (Boundary.cfgOf1 bAdd1898 m w)) = true ∧
    restB (callEnd sBc (Boundary.cfgOf1 bAdd1898 m w)) = Boundary.restsOf acsB := by
  kernel_forall_rfl_and

/-- **The forwarder's tail**, from any settled implementation frame with the observed gas and
output: the resume, 10 steps and `RETURN`. -/
theorem addFactsC : ∀ (W : State) (d : Devm),
    resumeCallB (cpA W).p (cpA W).oi (cpA W).os (.ok (obsChildB d)) = some (dA2 W (obsChildB d)) ∧
    stepN 10 ⟨32, (eA W).sta, dA2 W (obsChildB d)⟩ = some (eA44 W (obsChildB d)) ∧
    Evm.step (eA44 W (obsChildB d)) = .halt (.ok (postA W (obsChildB d))) := by
  kernel_forall_rfl_and

theorem addFactsD : ∀ (W : State) (d : Devm),
    (decide ((postA W (obsChildB d)).gasLeft = 826595) &&
      decide ((postA W (obsChildB d)).output = abiWord 2000) &&
      (postA W (obsChildB d)).error.isNone) = true := by
  kernel_forall_rfl_and

theorem addFactsE : ∀ (W : State) (d : Devm),
    (postA W (obsChildB d)).state = (dA2 W (obsChildB d)).state := by
  kernel_forall_rfl_and

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
