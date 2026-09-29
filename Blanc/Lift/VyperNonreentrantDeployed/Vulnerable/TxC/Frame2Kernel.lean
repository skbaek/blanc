import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame2Run
import Blanc.Lift.WitnessBoundary
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame2Kernel

/-!
V- as an admitted transaction, frame 2 whole, the kernel decisions: for every settled callback
child (`A'`) with the EELS gas and output (all its other parts free), frame 2 (the
implementation's `remove_liquidity`), with its token child run, halts by `RETURN` with the EELS
observation.  The callback child's world is never inspected: the interpreter reads storage and
accounts from the shadows.

The run is checked as four kernel decisions between three literal boundaries (`Bnd1`, `obsD1`):
step 343 (`t_1c73_c23`, three steps after the callback child's resume), step 563 (`t_1d0d_c53`,
eleven steps before the token's `CALL`) and step 578 (`t_1d27_c53`, three steps after the token
child's resume).  Each decision is its own declaration, so the kernel's caches do not outlive it.
The boundary literals were printed by an untrusted scratch evaluation (the message-level
witness's boundaries with the attacker address `A'` and the transaction's gas); the decisions
check them.  The composition (`run2FromC_stages`) is over variables only, so the kernel evaluates
nothing outside the four decisions.  Kernel only (`kernel_forall_rfl`); do not open this file in
the language server.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-! ### The boundaries -/

/-- Frame 2's machine at step 343. -/
def machC343 : Mach := { machT343 with gasLeft := 15368844 }

/-- Step 343's addresses: frame 2's own (`A'`, the identity precompile, the implementation,
then the proxy frame's, the transaction's pre-warmed set) before the callback's `CALL`, then the
callback child's. -/
def adrsC343 : List Adr :=
  [a2Address, (4 : Adr), implementationAddress, proxyAddress] ++ warmC ++ adrsAC

def bndC343 : Bnd1 := (machC343, t_1c73_c23, [], keysT343, adrsC343, storAT, acsAT, [], [], some refund3, true)

/-- Frame 2's machine at step 563. -/
def machC563 : Mach := { machT563 with gasLeft := 15364843 }

def adrsC563 : List Adr := [(4 : Adr), (4 : Adr)] ++ adrsC343

def bndC563 : Bnd1 := (machC563, t_1d0d_c53, [], keysT343, adrsC563, storT563, acsT563, [], rdT563, some refund3, true)

/-- Frame 2's machine at step 578. -/
def machC578 : Mach := { machT578 with gasLeft := 15332936 }

def adrsC578 : List Adr := tokenAddress :: adrsC563 ++ tokenAddress :: adrsC563

/-- Step 578, whose return data is the token's `true`. -/
def bndC578 : Bnd1 := (machC578, t_1d27_c53, [], keysT578, adrsC578, storT578, acsT578, [], word 1, some refund3, true)

/-! ### The stages -/

/-- Frame 2 from the result `r` of its first 339 steps to step 343: the callback child's
resume, three steps. -/
def run2Ca (r : Res) (d1 : Devm) : Res := callPairA fs1 sta2C keysAT adrsAC storAT acsAT 3 r d1

/-- Frame 2 from step 563 to step 578: to the token's `CALL`, the token child, its resume,
three steps. -/
def run2Cb (c : Cfg) : Res := callPairB fs1 sta2C fsT Token.code 11 23 3 c

theorem frame2C_k1 : ∀ d1 : Devm,
    obsD1 bndC343 (run2Ca (wrun fs1 sta2C 339 c2C) (childObsX gasAC [] refund3 d1)) = obsDOk1 bndC343 := by
  kernel_forall_rfl

theorem frame2C_k2 : ∀ (m : Meta) (w : World),
    obsD1 bndC563 (wrun fs1 sta2C 220 (cfgOf1 bndC343 m w)) = obsDOk1 bndC563 := by
  kernel_forall_rfl

theorem frame2C_k3 : ∀ (m : Meta) (w : World),
    obsD1 bndC578 (run2Cb (cfgOf1 bndC563 m w)) = obsDOk1 bndC578 := by
  kernel_forall_rfl

theorem frame2C_k4 : ∀ (m : Meta) (w : World),
    obs2T (wrun fs1 sta2C 185 (cfgOf1 bndC578 m w)) = obs2CEELS := by
  kernel_forall_rfl

/-! ### The whole of frame 1 -/

/-- The four stages compose (`Boundary.callPairFrom_stages`), over any boundaries and any
prefix result: every configuration the proof cases on is a variable, so the kernel evaluates
nothing here. -/
theorem run2FromC_stages {r0 : Res} {d : Devm} {x1 x2 x3 : Bnd1}
    (h1 : obsD1 x1 (run2Ca r0 d) = obsDOk1 x1)
    (h2 : ∀ m w, obsD1 x2 (wrun fs1 sta2C 220 (cfgOf1 x1 m w)) = obsDOk1 x2)
    (h3 : ∀ m w, obsD1 x3 (run2Cb (cfgOf1 x2 m w)) = obsDOk1 x3)
    (h4 : ∀ m w, obs2T (wrun fs1 sta2C 185 (cfgOf1 x3 m w)) = obs2CEELS) :
    obs2T (run2FromC r0 d) = obs2CEELS :=
  callPairFrom_stages (P := fun r => obs2T r = obs2CEELS) (n1 := 3) (n2 := 220) (n3 := 11)
    (n4 := 3) (n5 := 185) rfl rfl h1 h2 h3 h4

theorem frame2C_kernel : ∀ d1 : Devm, obs2T (run2C (childObsX gasAC [] refund3 d1)) = obs2CEELS := fun d1 =>
  run2FromC_stages (frame2C_k1 d1) frame2C_k2 frame2C_k3 frame2C_k4

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
