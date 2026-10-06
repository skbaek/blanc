import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun2

/-!
# V− P2, F2 second chunk: the 220-step run to `bRmX2`

F2 runs 220 steps from the first own chunk boundary `bRmX1` to the second,
`bRmX2` (node `t_1d0d_c53`, 11 steps before the token's `transfer` `CALL`, the
same code point as Frame 1's step 563). The token child, the third boundary
`bRmX3` and the run to the halt live in later `ViolRemoveRun*` modules. The
memory literal is scratch-printed run-length encoded; the kernel checks every
byte. Do not open this file in the language server.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-! ## Second chunk boundary and its run -/

/-- F2's memory 220 steps after `bRmX1`: 996 bytes of data in a 1024-byte
window (scratch-printed run-length encoded). -/
def memRmX2 : List UInt8 :=
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
    List.replicate 31 0 ++ List.replicate 1 0x64

/-- F2's machine 220 steps after `bRmX1`: stack, memory, gas 847667. -/
def machRmX2 : Mach :=
  (⟨[(100 : Nat).toB256, (736 : Nat).toB256, (2 : Nat).toB256,
      (448 : Nat).toB256, (1051816351 : Nat).toB256],
    ⟨memRmX2.toArray, 1024⟩, 847667, .zero⟩)

/-- F2 at 220 steps after `bRmX1` (11 steps before the token's `transfer`
`CALL`; node `t_1d0d_c53`): the second own chunk boundary. Storage is the
resume's plus the `(proxy, 9) := 900` write; keys the resume's; addresses and
accounts carry two identity-precompile touches each. -/
def bRmX2 : Boundary.Bnd1 :=
  (machRmX2, Vulnerable.t_1d0d_c53, [],
    [(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
      (proxyAddr, (2 : Nat).toB256)] ++ keysCb,
    [(4 : Adr), (4 : Adr), attackerAddr, (4 : Adr), implAddr, proxyAddr] ++ adrsCb,
    [((proxyAddr, (9 : Nat).toB256), (900 : Nat).toB256)] ++ storCb,
    [((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩),
      (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩),
      ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩),
      (proxyAddr, ⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩)] ++ acsCb,
    [], List.replicate 31 0 ++ [0x44, 0xa9, 0x05, 0x9c, 0xbb] ++
      List.replicate 12 0 ++ List.replicate 20 0x44 ++ List.replicate 12 0 ++
      List.replicate 19 0 ++ [0x64], none, false)

/-- 220 steps from `bRmX1` reach `bRmX2`, over any tails, world and bookkeeping. -/
theorem rmChunkX2 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bRmX2 (wrun fsI sRm 220 (Boundary.cfgOfT bRmX1 tS tA m w)) =
      Boundary.obsDOkT bRmX2 tS tA := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
