import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5Chunks
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4ChunkA
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5ChunkA

/-! V- as an admitted transaction, frame 5's first chunk (2,625 steps from the real spawn to the
boundary), in three kernel decisions of about 875 steps each, all over a free world and free
bookkeeping: from the spawn (`c5C_eq`) to a boundary at `t_35a9_c84` (step 880), from there to one
at `t_3467_c84` (step 1753) and from there to `cfgB5C`'s.  Each decision is its own declaration, so
the kernel's caches do not outlive it.  The boundary literals were printed by an untrusted
scratch evaluation; the decisions check them.  Kernel only; do not open this file in the
language server. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

/-- Frame 5's machine at step 880. -/
def machC880 : Mach := { machT880 with gasLeft := 14683699 }

/-- Frame 5's machine at step 1753. -/
def machC1753 : Mach := { machT1753 with gasLeft := 14680751 }

def bndC880 : Bnd :=
  (machC880, t_35a9_c84, [t_37a9_c44, t_010d_c1], keysA1, adrs5C, storT880, acsAT, 0, [], [], none)

def bndC1753 : Bnd :=
  (machC1753, t_3467_c84, [t_37a9_c44, t_0236_c45], keysA1, adrs5C, storT880, acsAT, 0, [], [],
    none)

/-- `obsB5EELSC`'s boundary. -/
def bndC2625 : Bnd :=
  (machC2625, t_0370_c63, [], keys2625, adrs5C, storT2625, acsAT, 2800, [], [], none)

/-- Frame 5's entry as a boundary: an empty machine with the spawn's gas at the certificate's
entry 0, the shadows of frame 3's `CALL` with the implementation added. -/
def bndC0 : Bnd :=
  (⟨[], Mem.empty, 14719332, .zero⟩, t_0000_c0, [],
    [(proxyAddress, (8 : Nat).toB256), (proxyAddress, (26 : Nat).toB256),
     (proxyAddress, (2 : Nat).toB256)],
    adrs5C, storT0, acsAT, 0, [], [], none)

/-- `c5C` is its boundary at its own world and bookkeeping (the one evaluation of the spawn
chain in this file). -/
theorem c5C_eq : c5C = cfgOf bndC0 c5C.devm.meta c5C.devm.world := by kernel_rfl

theorem chunkC1 : ∀ (m : Meta) (w : World),
    obsD bndC880 (wrun fs1 sta5C 880 (cfgOf bndC0 m w)) = obsDOk bndC880 := by
  kernel_forall_rfl

theorem chunkC2 : ∀ (m : Meta) (w : World),
    obsD bndC1753 (wrun fs1 sta5C 873 (cfgOf bndC880 m w)) = obsDOk bndC1753 := by
  kernel_forall_rfl

theorem chunkC3 : ∀ (m : Meta) (w : World),
    obsD bndC2625 (wrun fs1 sta5C 872 (cfgOf bndC1753 m w)) = obsDOk bndC2625 := by
  kernel_forall_rfl

theorem chunk5AC : obsB (wrun fs1 e5C.sta 2625 c5C) = obsB5EELSC ∧ AtdClean (wrun fs1 e5C.sta 2625 c5C) := by
  rw [e5C_sta_eq]
  exact obsB_of_obsD (obsD_chain3 (n1 := 880) (n2 := 873) (n3 := 872) c5C_eq chunkC1 chunkC2 chunkC3)
    rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
