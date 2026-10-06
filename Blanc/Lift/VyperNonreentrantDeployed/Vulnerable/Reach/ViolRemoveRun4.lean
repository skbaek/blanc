import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun3

/-!
# V− P2, F2 token stages: the token `transfer` child and the third boundary

F2 runs 11 steps from `bRmX2` to its token `transfer` `CALL` (`cTokRm`, as
data like `cRm339`); the token child runs 200 steps by its own certificate
(`childRun Token20.prog Token20.code`, gas `gasTok` left, word-1 output); the
token resume plus 3 steps reaches the third boundary `bRmX3` (node
`t_1d27_c53`); 188 steps reach the halt with the frozen exits. Each kernel
fact evaluates at most a few hundred steps. Every literal below is
scratch-printed (shadows composed from the frozen prefixes, kernel-checked).
Do not open this file in the language server.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-! ## Token shadows (the token child's halt prefixes) -/

/-- The token child's accessed storage keys at its halt: its two balance
slots, then F2's frame reads. -/
def keysTok : List (Adr × B256) :=
  [(tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256),
    (tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256),
    (proxyAddr, (7 : Nat).toB256), (proxyAddr, (8 : Nat).toB256),
    (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)] ++ keysCb

/-- The token child's accessed addresses at its halt: itself, the precompiles
it touches and F2's frame addresses. -/
def adrsTok : List Adr :=
  [tokenAddr, (4 : Adr), (4 : Adr), attackerAddr, (4 : Adr), implAddr,
    proxyAddr] ++ adrsCb

/-- The token child's storage-shadow prefix at its halt: the `transfer`
settlement, then the callback's halt shadow. -/
def storTok : StorShadow :=
  [((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256),
    (100 : Nat).toB256),
   ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256),
    (900 : Nat).toB256),
   ((proxyAddr, (9 : Nat).toB256), (900 : Nat).toB256)] ++ storCb

/-- The token child's account-shadow prefix at its halt: the touched accounts,
then the callback's halt shadow. -/
def acsTok : AcctShadow :=
  [(tokenAddr, ⟨1, (0 : Nat).toB256, .empty, Token20.code⟩),
    (proxyAddr, ⟨1, (0 : Nat).toB256, .empty, fwdCode⟩),
    ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩),
    (proxyAddr, ⟨1, (0 : Nat).toB256, .empty, fwdCode⟩),
    ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩),
    (proxyAddr, ⟨1, (0 : Nat).toB256, .empty, fwdCode⟩)] ++ acsCb

/-- The token child's return data: word 1. -/
def outTok : Bytes := List.replicate 31 0 ++ [0x01]

/-! ## Token `CALL` staging (11 steps after `bRmX2`), as data -/

/-- F2 at its token `transfer` `CALL`: the configuration 11 steps after `bRmX2`. -/
def cTokRm (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  match wrun fsI sRm 11 (Boundary.cfgOfT bRmX2 tS tA m w) with
  | .cont c => c
  | _ => Boundary.cfgOfT bRm0 tS tA m w

theorem cTokRm_eq : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    wrun fsI sRm 11 (Boundary.cfgOfT bRmX2 tS tA m w) =
      .cont (cTokRm tS tA m w) := by
  kernel_forall_rfl

/- F2's token `CALL` shape is used only through `cTokRm` (the 11-step
configuration) and the token child's run: `childOk_of_childRun` discharges
the entered machine from the run and the certificate, so no
`callPrep`/`frameEnterS` projection fact is stated here. -/

/-! ## Token child run (200 steps by its own certificate) -/

/-- The token child's settled machine: the halted machine of its 200-step run. -/
def dTokRm (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Devm :=
  match childRun Token20.prog Token20.code sRm 200 (cTokRm tS tA m w) with
  | .done (.halted d) _ => d
  | _ => default

/-- The token child's halting configuration. -/
def clTokRm (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  match childRun Token20.prog Token20.code sRm 200 (cTokRm tS tA m w) with
  | .done (.halted _) cl => cl
  | _ => Boundary.cfgOfT bRm0 tS tA m w

theorem tokChild_eq : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    childRun Token20.prog Token20.code sRm 200 (cTokRm tS tA m w) =
      .done (.halted (dTokRm tS tA m w)) (clTokRm tS tA m w) := by
  kernel_forall_rfl

/-- The token child's gas, output and error observations. -/
theorem tokChild_gas : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (dTokRm tS tA m w).gasLeft = gasTok := by
  kernel_forall_rfl

theorem tokChild_out : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (dTokRm tS tA m w).output = outTok := by
  kernel_forall_rfl

theorem tokChild_err : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (dTokRm tS tA m w).error = none := by
  kernel_forall_rfl

/-- The token child's halt shadows are the token prefixes over any tails. -/
theorem tokChild_keys : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (clTokRm tS tA m w).keys = keysTok := by
  kernel_forall_rfl

theorem tokChild_adrs : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (clTokRm tS tA m w).adrs = adrsTok := by
  kernel_forall_rfl

theorem tokChild_stor : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (clTokRm tS tA m w).stor = storTok ++ tS := by
  kernel_forall_rfl

theorem tokChild_acs : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (clTokRm tS tA m w).acs = acsTok ++ tA := by
  kernel_forall_rfl

/-- The token child's recorded keys (for the origin-state transport). -/
theorem tokRun_keys : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    resKeys (childRun Token20.prog Token20.code sRm 200 (cTokRm tS tA m w)) =
      keysTok := by
  kernel_forall_rfl

/-! ## Third chunk boundary and its run -/

/-- F2's memory at the third boundary: 1120 bytes of data in a 1120-byte
window (scratch-printed run-length encoded). -/
def memRmX3 : List UInt8 :=
  List.replicate 28 0 ++ List.replicate 1 0x3e ++ List.replicate 1 0xb1 ++
    List.replicate 1 0x71 ++ List.replicate 1 0x9f ++ List.replicate 300 0 ++
    List.replicate 20 0x44 ++ List.replicate 30 0 ++ List.replicate 1 0x07 ++
    List.replicate 1 0xd0 ++ List.replicate 31 0 ++ List.replicate 1 0x64 ++
    List.replicate 31 0 ++ List.replicate 1 0x64 ++ List.replicate 31 0 ++
    List.replicate 1 0x01 ++ List.replicate 30 0 ++ List.replicate 1 0x03 ++
    List.replicate 1 0xe8 ++ List.replicate 31 0 ++ List.replicate 1 0x64 ++
    List.replicate 127 0 ++ List.replicate 1 0x04 ++ List.replicate 1 0xa9 ++
    List.replicate 1 0x05 ++ List.replicate 1 0x9c ++ List.replicate 1 0xbb ++
    List.replicate 91 0 ++ List.replicate 1 0x44 ++ List.replicate 1 0xa9 ++
    List.replicate 1 0x05 ++ List.replicate 1 0x9c ++ List.replicate 1 0xbb ++
    List.replicate 12 0 ++ List.replicate 20 0x44 ++ List.replicate 31 0 ++
    List.replicate 1 0x64 ++ List.replicate 91 0 ++ List.replicate 1 0x44 ++
    List.replicate 1 0xa9 ++ List.replicate 1 0x05 ++ List.replicate 1 0x9c ++
    List.replicate 1 0xbb ++ List.replicate 12 0 ++ List.replicate 20 0x44 ++
    List.replicate 31 0 ++ List.replicate 1 0x64 ++ List.replicate 123 0 ++
    List.replicate 1 0x01

/-- F2's return data at the third boundary: 31 zeros and word 1 (the token's
output, kept). -/
def rdRmX3 : Bytes := List.replicate 31 0 ++ [0x01]

/-- F2's machine at the third boundary: stack, 1120-byte memory, gas 815642. -/
def machRmX3 : Mach :=
  ⟨[(2 : Nat).toB256, (448 : Nat).toB256, (1051816351 : Nat).toB256],
    ⟨memRmX3.toArray, 1120⟩, 815642, .zero⟩

/-- F2 at 3 steps after the token resume (node `t_1d27_c53`): the third own
chunk boundary. Storage and accounts are the token child's halt shadows; keys
re-read the frame prefix, addresses double the token child's. -/
def bRmX3 : Boundary.Bnd1 :=
  (machRmX3, Vulnerable.t_1d27_c53, [],
    (keysTok.drop 2) ++ keysTok, adrsTok ++ adrsTok,
    storTok, acsTok, [], rdRmX3, none, false)

/-- F2 from its 11-step token-`CALL` result (with result `r`), resumed with the
token child `d` and run 3 more steps. -/
def runRmB (tS : StorShadow) (tA : AcctShadow) (r : Res) (d : Devm) : Res :=
  Boundary.callPairA fsI sRm keysTok adrsTok (storTok ++ tS) (acsTok ++ tA) 3 r d

/-- 11 steps, the token resume and 3 steps reach `bRmX3`, over any tails,
world and bookkeeping, for any token child at the observed gas and output. -/
theorem rmChunkX3 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    Boundary.obsDT bRmX3 (runRmB tS tA
      (wrun fsI sRm 11 (Boundary.cfgOfT bRmX2 tS tA m w)) (childObs gasTok outTok d)) =
      Boundary.obsDOkT bRmX3 tS tA := by
  kernel_forall_rfl

/-! ## The run to the halt -/

/-- F2's settled machine: the halted machine 188 steps after `bRmX3`. -/
def postRm (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Devm :=
  match wrun fsI sRm 188 (Boundary.cfgOfT bRmX3 tS tA m w) with
  | .done (.halted d) _ => d
  | _ => default

/-- F2's halting configuration. -/
def clRm (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  match wrun fsI sRm 188 (Boundary.cfgOfT bRmX3 tS tA m w) with
  | .done (.halted _) cl => cl
  | _ => Boundary.cfgOfT bRm0 tS tA m w

theorem rmEnd_eq : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    wrun fsI sRm 188 (Boundary.cfgOfT bRmX3 tS tA m w) =
      .done (.halted (postRm tS tA m w)) (clRm tS tA m w) := by
  kernel_forall_rfl

/-- F2's halt gas, output and error. -/
theorem rmEnd_gas : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (postRm tS tA m w).gasLeft = gasRm := by
  kernel_forall_rfl

theorem rmEnd_out : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (postRm tS tA m w).output = outRm := by
  kernel_forall_rfl

theorem rmEnd_err : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (postRm tS tA m w).error = none := by
  kernel_forall_rfl

/-- F2's halt shadows are the frozen prefixes over any tails. -/
theorem rmEnd_keys : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (clRm tS tA m w).keys = keysRm := by
  kernel_forall_rfl

theorem rmEnd_adrs : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (clRm tS tA m w).adrs = adrsRm := by
  kernel_forall_rfl

theorem rmEnd_stor : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (clRm tS tA m w).stor = storRm ++ tS := by
  kernel_forall_rfl

theorem rmEnd_acs : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (clRm tS tA m w).acs = acsRm ++ tA := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
