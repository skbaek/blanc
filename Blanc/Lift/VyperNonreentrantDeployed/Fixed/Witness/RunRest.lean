import Blanc.Lift.KernelBatch
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.RunF

/-!
# V+ witness, the reader frame, the reentrant frame and the tails

Kernel decisions (do not open this file in the language server):

* the reader frame `R` walks 9 steps to its `STATICCALL` of the pool (pc 38), which spawns
  the reentrant pool frame `G` with calldata `get_virtual_price()`;
* `G` walks 141 steps, never at a guarded body start, and halts by `REVERT` (the lock
  check at `0x1649`-`0x1652` reads the held lock 2 and jumps to `0x477e`);
* `R` resumes from the failed child, pops the status word and `STOP`s;
* `F` resumes from `R` and, finding fewer than 32 bytes of return data, reverts after 12
  more steps.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun

/-! ### The reader frame up to its `STATICCALL` -/

def cT0 : PCfg := childCfg eT cpH.f cH.keys cpH.adrs cH.stor cH.acs

def cTs : PCfg := getC c0 (pwalk readerTries eT.sta okAll 9 cT0)

def cpT : CallPrep :=
  (scallPrep eT.sta cTs.devm cTs.adrs cTs.acs).getD ⟨f0, default, 0, 0, []⟩

/-- The reentrant pool frame's entry machine. -/
def eG : Evm := match frameEnterS cpT.f cTs.acs with | .run e => e | .done _ => default

/-! ### The reentrant frame -/

def cG0 : PCfg := childCfg eG cpT.f cTs.keys cpT.adrs cTs.stor cTs.acs

/-- The reentrant frame's halted machine. -/
def dG : Devm :=
  match pwalk codeTries eG.sta okBody 141 cG0 with
  | .halt (.error (_, d)) => d
  | _ => default

/-! ### The reader frame after its failed child -/

def childG : Devm := match cpT.f.settle (.error (.revert, dG)) with | .ok d => d | _ => default

def dT1 : Devm := (resumeCallB cpT.p cpT.oi cpT.os (.ok childG)).getD default

def cT1 : PCfg := ⟨cTs.pc + 1, dT1, cTs.keys, cpT.adrs, cTs.stor, cTs.acs⟩

def cT2 : PCfg := getC c0 (pwalk readerTries eT.sta okAll 1 cT1)

/-! ### The pool frame after the reader -/

def dF1 : Devm := (resumeCallB cpH.p cpH.oi cpH.os (.ok cT2.devm)).getD default

def cF1 : PCfg := ⟨cH.pc + 1, dF1, cH.keys ++ cT2.keys, cpH.adrs ++ cT2.adrs, cT2.stor, cT2.acs⟩

/-- The pool frame's halted machine. -/
def dF : Devm :=
  match pwalk codeTries e0.sta okAll 12 cF1 with
  | .halt (.error (_, d)) => d
  | _ => default

-- Share the concrete frame history across these related kernel equations.
private theorem frameChainFacts :
    (pwalk readerTries eT.sta okAll 9 cT0 = .cont cTs) ∧
    (cTs.pc = 38) ∧
    (decodeT 6 readerTries.bytes 38 = some (.next (.exec .staticcall))) ∧
    (scallPrep eT.sta cTs.devm cTs.adrs cTs.acs = some cpT) ∧
    (frameEnterS cpT.f cTs.acs = .run eG) ∧
    (pwalk codeTries eG.sta okBody 141 cG0 = .halt (.error (.revert, dG))) ∧
    ((eG.pc, eG.sta.currentTarget, eG.sta.code, eG.sta.data) =
    (0, poolAddress, code, [0xbb, 0x7b, 0x8b, 0x80])) ∧
    (cpT.f.settle (.error (.revert, dG)) = .ok childG) ∧
    (resumeCallB cpT.p cpT.oi cpT.os (.ok childG) = some dT1) ∧
    (pwalk readerTries eT.sta okAll 1 cT1 = .cont cT2) ∧
    (pwalk readerTries eT.sta okAll 1 cT2 = .halt (.ok cT2.devm)) ∧
    (cT2.devm.error = none) ∧
    ((cpT.f.isCreate, cpT.f.inner.benv.stat.rules.stateGas) = (false, none)) ∧
    ((cpH.f.isCreate, cpH.f.inner.benv.stat.rules.stateGas) = (false, none)) ∧
    (resumeCallB cpH.p cpH.oi cpH.os (.ok cT2.devm) = some dF1) ∧
    (pwalk codeTries e0.sta okAll 12 cF1 = .halt (.error (.revert, dF))) ∧
    ((eT.pc, eT.sta.currentTarget, eT.sta.code) = (0, readerAddress, Reader.code)) := by
  kernel_rfl_and

theorem walkTs : pwalk readerTries eT.sta okAll 9 cT0 = .cont cTs := by
  exact frameChainFacts.1

theorem cTs_pc : cTs.pc = 38 := by
  exact frameChainFacts.2.1

theorem decodeTs : decodeT 6 readerTries.bytes 38 = some (.next (.exec .staticcall)) := by
  exact frameChainFacts.2.2.1

theorem scallT : scallPrep eT.sta cTs.devm cTs.adrs cTs.acs = some cpT := by
  exact frameChainFacts.2.2.2.1

theorem enterG : frameEnterS cpT.f cTs.acs = .run eG := by
  exact frameChainFacts.2.2.2.2.1

theorem walkG : pwalk codeTries eG.sta okBody 141 cG0 = .halt (.error (.revert, dG)) := by
  exact frameChainFacts.2.2.2.2.2.1

/-- Static facts of the reentrant frame: it enters at pc 0 as the pool's own storage owner
running the comparator, with the `get_virtual_price()` calldata. -/
theorem eG_facts : (eG.pc, eG.sta.currentTarget, eG.sta.code, eG.sta.data) =
    (0, poolAddress, code, [0xbb, 0x7b, 0x8b, 0x80]) := by
  exact frameChainFacts.2.2.2.2.2.2.1

theorem settleG : cpT.f.settle (.error (.revert, dG)) = .ok childG := by
  exact frameChainFacts.2.2.2.2.2.2.2.1

theorem resumeT : resumeCallB cpT.p cpT.oi cpT.os (.ok childG) = some dT1 := by
  exact frameChainFacts.2.2.2.2.2.2.2.2.1

theorem walkT2 : pwalk readerTries eT.sta okAll 1 cT1 = .cont cT2 := by
  exact frameChainFacts.2.2.2.2.2.2.2.2.2.1

theorem walkT3 : pwalk readerTries eT.sta okAll 1 cT2 = .halt (.ok cT2.devm) := by
  exact frameChainFacts.2.2.2.2.2.2.2.2.2.2.1

theorem cT2_err : cT2.devm.error = none := by
  exact frameChainFacts.2.2.2.2.2.2.2.2.2.2.2.1

theorem cpT_facts : (cpT.f.isCreate, cpT.f.inner.benv.stat.rules.stateGas) = (false, none) := by
  exact frameChainFacts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cpH_facts : (cpH.f.isCreate, cpH.f.inner.benv.stat.rules.stateGas) = (false, none) := by
  exact frameChainFacts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem resumeF : resumeCallB cpH.p cpH.oi cpH.os (.ok cT2.devm) = some dF1 := by
  exact frameChainFacts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem walkF : pwalk codeTries e0.sta okAll 12 cF1 = .halt (.error (.revert, dF)) := by
  exact frameChainFacts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem eT_facts : (eT.pc, eT.sta.currentTarget, eT.sta.code) = (0, readerAddress, Reader.code) := by
  exact frameChainFacts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness
