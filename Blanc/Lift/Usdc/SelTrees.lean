import Blanc.Lift.Usdc.ImplV1.Cert
import Blanc.Lift.Usdc.ImplV2.Cert
import Blanc.Lift.Usdc.ImplV2_1.Cert
import Blanc.Lift.Usdc.Impl.Cert

/-!
# The USDC implementations' selector comparison trees

Each implementation's solc dispatcher, after the selector shift, is one comparison tree; a
route fact `X.selTree.selWalk σ = .inl (σ, k)` (`decide +kernel`) names the wrapper entry `k`
without restating the tree (`Blanc/Lift/SelectorRoute.lean`).
-/

namespace Blanc.Lift.Usdc

/-- `Impl`'s dispatcher comparison tree. -/
def Impl.selTree : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide)) (.next (.reg .gt)
    (.next (.push [0x01, 0xd3] (by decide)) (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))

/-- `ImplV1`'s dispatcher comparison tree. -/
def ImplV1.selTree : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [0x06, 0xfd, 0xde, 0x03] (by decide)) (.next (.reg .eq)
    (.next (.push [0x01, 0x90] (by decide)) (.branchTo ImplV1.t_0041_c0 53))))

/-- `ImplV2`'s dispatcher comparison tree. -/
def ImplV2.selTree : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide)) (.next (.reg .gt)
    (.next (.push [0x01, 0xbd] (by decide)) (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))

/-- `ImplV2_1`'s dispatcher comparison tree. -/
def ImplV2_1.selTree : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [0x7f, 0x2e, 0xec, 0xc3] (by decide)) (.next (.reg .gt)
    (.next (.push [0x01, 0xb2] (by decide)) (.branch ImplV2_1.t_002b_c0 ImplV2_1.t_01b2_c0))))

end Blanc.Lift.Usdc
