-- Semantics.lean : Blanc's compiled-program semantics over Jaune's execution layer

import Blanc.Basic
import Jaune.Hash
import Jaune.Sufficiency
import Jaune.Exec

namespace Blanc

open Jaune

-------------------------------------------------------------------------------
-- THE SEAM.  The EVM-generic execution layer (the fieldwise `Devm` relations,
-- the `*.At` decode predicates, the frame/step relational layer, the canonical
-- `Exec` relation, its inversions, `Fueled` residue, depth side conditions and
-- the adequacy pair `exec_iff_exec_eq`) is owned by Jaune: `Jaune.ExecFrame`
-- and `Jaune.Exec`, imported above.  This module keeps only the Blanc layer:
-- the compiled-program language and the relations built on it, plus the two
-- statements that straddle the seam (`Devm.PopBurn`, phrased with Blanc's
-- `Stack.Pop`, and the unused-by-Jaune `Except.Split`) and Blanc's fork
-- coverage.
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- BLANC.  The compiled-program instruction encoding and the program syntax.
-- `Stack.Push`/`Stack.Pop` are phrased with Blanc's own `Split` (`Basic.lean`),
-- so they are Blanc's however Jaune-shaped `Stack = List B256` looks.
-------------------------------------------------------------------------------

def Rinst.toUInt8 : Rinst → UInt8
  | .add          => 0x01
  | .mul          => 0x02
  | .sub          => 0x03
  | .div          => 0x04
  | .sdiv         => 0x05
  | .mod          => 0x06
  | .smod         => 0x07
  | .addmod       => 0x08
  | .mulmod       => 0x09
  | .exp          => 0x0A
  | .signextend   => 0x0B
  | .lt           => 0x10
  | .gt           => 0x11
  | .slt          => 0x12
  | .sgt          => 0x13
  | .eq           => 0x14
  | .iszero       => 0x15
  | .and          => 0x16
  | .or           => 0x17
  | .xor          => 0x18
  | .not          => 0x19
  | .byte         => 0x1A
  | .shl          => 0x1B
  | .shr          => 0x1C
  | .sar          => 0x1D
  | .clz          => 0x1E
  | .keccak256          => 0x20
  | .address      => 0x30
  | .balance      => 0x31
  | .origin       => 0x32
  | .caller       => 0x33
  | .callvalue    => 0x34
  | .calldataload => 0x35
  | .calldatasize => 0x36
  | .calldatacopy => 0x37
  | .codesize     => 0x38
  | .codecopy     => 0x39
  | .gasprice     => 0x3A
  | .extcodesize  => 0x3B
  | .extcodecopy  => 0x3C
  | .returndatasize  => 0x3D
  | .returndatacopy  => 0x3E
  | .extcodehash  => 0x3F
  | .blockhash    => 0x40
  | .coinbase     => 0x41
  | .timestamp    => 0x42
  | .number       => 0x43
  | .prevrandao   => 0x44
  | .gaslimit     => 0x45
  | .chainid      => 0x46
  | .selfbalance  => 0x47
  | .basefee      => 0x48
  | .blobhash     => 0x49
  | .blobbasefee  => 0x4A
  | .slotnum      => 0x4B
  | .pop          => 0x50
  | .mload        => 0x51
  | .mstore       => 0x52
  | .mstore8      => 0x53
  | .sload        => 0x54
  | .sstore       => 0x55
  | .pc           => 0x58
  | .msize        => 0x59
  | .gas          => 0x5A
  | .tload        => 0x5C
  | .tstore       => 0x5D
  | .mcopy        => 0x5E
  | .dup n        => 0x80 + n.val.toUInt8
  | .swap n       => 0x90 + n.val.toUInt8
  | .log n        => 0xA0 + n.val.toUInt8

abbrev Stack : Type := List B256

def Stack.Push (x y xy : Stack) : Prop := x <++ xy ++> y
def Stack.Pop (x xy y : Stack) : Prop := x <++ xy ++> y

inductive Func : Type
  | branch : Func → Func → Func
  | last : Linst → Func
  | next : Ninst → Func → Func
  | call : Nat → Func

structure Prog : Type where
  (main : Func)
  (aux : List Func)

-- `Devm.PopBurn` straddles the seam: a `Jaune.Devm.Rel` whose stack component
-- is Blanc's `Stack.Pop`, so it stays in Blanc.
def Devm.PopBurn (xs : List B256) : Devm → Devm → Prop :=
  Devm.Rel {
    Devm.Rels.eq with
    stack := Stack.Pop xs
    gasLeft := (· ≥ ·)
  }

def Except.Split {ξ υ ζ : Type}
    (e : Except ξ υ) (e' : Except ξ ζ) (q : υ → Prop) : Prop :=
  (∃ x, e = .error x ∧ e' = .error x) ∨ (∃ y : υ, e = .ok y ∧ q y)

inductive Func.Run : List Func → Sevm → Devm → Func → Devm → Prop
  | zero :
    ∀ {fs sevm devm devm' f g devm''},
      Devm.PopBurn [0] devm devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (branch f g) devm''
  | succ :
    ∀ {fs sevm devm w devm' f g devm_jd devm''},
      w ≠ 0 →
      Devm.PopBurn [w] devm devm' →
      Devm.Burn devm' devm_jd →
      Func.Run fs sevm devm_jd g devm'' →
      Func.Run fs sevm devm (branch f g) devm''
  | last :
    ∀ {fs sevm devm i devm' },
      Linst.Run sevm devm i (.ok devm') →
      Func.Run fs sevm devm (last i) devm'
  | next :
    ∀ {fs sevm devm i devm' f devm''},
      Ninst.Run sevm devm i devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (next i f) devm''
  | call :
    ∀ {fs sevm devm devm' k f devm''},
      fs[k]? = some f →
      Devm.Burn devm devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (call k) devm''

def Prog.Run (sevm : Sevm) (devm : Devm) (p : Prog) (devm' : Devm) : Prop :=
  Func.Run (p.main :: p.aux) sevm devm (.call 0) devm'

/-- The covered forks, in activation order. -/
def coveredForks : List Fork := [.prague, .osaka, .bpo1, .bpo2]

/-- The user-approved fork coverage: Prague, Osaka, BPO1, and BPO2
(programme §B).  Amsterdam is not covered. -/
def CoveredFork (f : Fork) : Prop := f ∈ coveredForks

instance : DecidablePred CoveredFork :=
  fun f => inferInstanceAs (Decidable (f ∈ coveredForks))

/-- Eliminate a coverage proof into one case per covered fork.  The only place
outside this block that should depend on which forks are covered. -/
theorem CoveredFork.cases {motive : Fork → Prop} {f : Fork}
    (h : CoveredFork f)
    (prague : motive .prague) (osaka : motive .osaka)
    (bpo1 : motive .bpo1) (bpo2 : motive .bpo2) : motive f := by
  unfold CoveredFork coveredForks at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact prague
  · exact osaka
  · exact bpo1
  · exact bpo2

theorem CoveredFork.stateGas_none {f : Fork} (h : CoveredFork f) :
    (Fork.ruleSet f).stateGas = none :=
  h.cases (motive := fun f => (Fork.ruleSet f).stateGas = none)
    rfl rfl rfl rfl

theorem CoveredFork.bal_none {f : Fork} (h : CoveredFork f) :
    (Fork.ruleSet f).bal = none :=
  h.cases (motive := fun f => (Fork.ruleSet f).bal = none)
    rfl rfl rfl rfl

theorem CoveredFork.rules_stateGas_none {s : BenvStat}
    (h : CoveredFork s.fork) : s.rules.stateGas = none :=
  h.stateGas_none

theorem CoveredFork.rules_bal_none {s : BenvStat} (h : CoveredFork s.fork) :
    s.rules.bal = none :=
  h.bal_none

/-- Every covered fork runs the Prague general-purpose request contracts. -/
theorem CoveredFork.requests_eq {f : Fork} (h : CoveredFork f) :
    (Fork.ruleSet f).requests = pragueRequests :=
  h.cases (motive := fun f => (Fork.ruleSet f).requests = pragueRequests)
    rfl rfl rfl rfl

/-- The beacon-roots system address is not a precompile on any covered fork. -/
theorem CoveredFork.beaconRoots_not_precompile {fork : Fork}
    (hfork : CoveredFork fork) :
    ¬ (Fork.ruleSet fork).isPrecomp beaconRootsAddress :=
  hfork.cases
    (motive := fun f => ¬ (Fork.ruleSet f).isPrecomp beaconRootsAddress)
    (by decide) (by decide) (by decide) (by decide)

/-- The history-storage system address is not a precompile on any covered
fork. -/
theorem CoveredFork.historyStorage_not_precompile {fork : Fork}
    (hfork : CoveredFork fork) :
    ¬ (Fork.ruleSet fork).isPrecomp historyStorageAddress :=
  hfork.cases
    (motive := fun f => ¬ (Fork.ruleSet f).isPrecomp historyStorageAddress)
    (by decide) (by decide) (by decide) (by decide)

/-- Transport a coverage proof along a fork equation. -/
theorem CoveredFork.of_eq {f1 f2 : Fork} (h : f1 = f2) (hf : CoveredFork f1) :
    CoveredFork f2 := by
  cases h; exact hf

/-- Prague is covered. -/
theorem CoveredFork.prague : CoveredFork .prague := by decide

/-- Osaka is covered. -/
theorem CoveredFork.osaka : CoveredFork .osaka := by decide

/-- BPO1 is covered. -/
theorem CoveredFork.bpo1 : CoveredFork .bpo1 := by decide

/-- BPO2 is covered. -/
theorem CoveredFork.bpo2 : CoveredFork .bpo2 := by decide

/-- Amsterdam is not covered (the negative control on the covered set). -/
theorem CoveredFork.not_amsterdam : ¬ CoveredFork .amsterdam := by decide

end Blanc
