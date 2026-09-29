import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5Chunks
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5ChunkB

/-! V- as an admitted transaction, frame 5's second chunk (from the boundary, over a free world
and free bookkeeping, to the `RETURN`), in two kernel decisions: 938 steps to a boundary at
`t_3467_c62` (step 3563 of the frame), then 942 steps to the `RETURN`.  Each decision is its own
declaration, so the kernel's caches do not outlive it.  The boundary literal was printed by an
untrusted scratch evaluation; the decisions check it.  Kernel only; do not open this file in the
language server. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

/-- Frame 5's machine at step 3563. -/
def machC3563 : Mach := { machT3563 with gasLeft := 14672359 }

def bndC3563 : Bnd :=
  (machC3563, t_3467_c62, [t_37a9_c44, t_04d4_c152], keys2625, adrs5C, storT3563, acsAT, 2800, [],
    [], none)

theorem chunkCB1 : ∀ (m : Meta) (w : World),
    obsD bndC3563 (wrun fs1 sta5C 938 (cfgB5C m w)) = obsDOk bndC3563 := by
  kernel_forall_rfl

theorem chunkCB2 : ∀ (m : Meta) (w : World),
    obs5C (wrun fs1 sta5C 942 (cfgOf bndC3563 m w)) = obs5EELSC := by
  kernel_forall_rfl

theorem chunk5BC : ∀ (m : Meta) (w : World), obs5C (wrun fs1 e5C.sta 1880 (cfgB5C m w)) = obs5EELSC := by
  intro m w
  rw [e5C_sta_eq, show (1880 : Nat) = 938 + 942 from rfl]
  exact obsD_chain (P := fun r => obs5C r = obs5EELSC) (chunkCB1 m w) chunkCB2

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
