import Blanc.Lift.Usdc.Model

/-!
# The call families of USDC's implementation

A partition of `Call` into the families whose refinement laws the USDC refinement units prove
(`Blanc/Lift/Usdc/RefineShape.lean`): `famTransfer` (U6d), `famSigned` (U6e), `famAdmin` (U6f),
`famDispatch` (U6g: the views and the two initializers modelled exactly), and the remaining
`rescueERC20` (U6f, `RescueLaw`) and the two argument-free initializers `initialize` and
`initializeV2_2` (U6g, which the model makes revert; their law is conditional on a good ledger).
`call_family_cases` says every call is in exactly one of these classes, which the family ladder's
instance consumes.
-/

namespace Blanc.Lift.Usdc

/-- The transfer and allowance family (U6d). -/
def famTransfer : Call → Prop
  | .transfer .. | .transferFrom .. | .approve .. | .increaseAllowance .. | .decreaseAllowance .. => True
  | _ => False

/-- The signed family, verified through the library (U6e). -/
def famSigned : Call → Prop
  | .permit .. | .transferWithAuthorization .. | .receiveWithAuthorization ..
  | .cancelAuthorization .. => True
  | _ => False

/-- Roles, minting, burning, pausing and blacklisting (U6f). -/
def famAdmin : Call → Prop
  | .mint .. | .burn .. | .configureMinter .. | .removeMinter .. | .updateMasterMinter ..
  | .pause | .unpause | .updatePauser .. | .updateBlacklister .. | .updateRescuer ..
  | .transferOwnership .. | .blacklist .. | .unBlacklist .. => True
  | _ => False

/-- The views and the two initializers the model states exactly (U6g). -/
def famDispatch : Call → Prop
  | .view | .initializeV2 | .initializeV2_1 .. => True
  | _ => False

/-- The two argument-free initializers, modelled as reverting (decision usdc-u5a-initialize-revert). -/
def famInitRevert : Call → Prop
  | .initialize | .initializeV2_2 => True
  | _ => False

/-- Every call is in one of the families, or is `rescueERC20`. -/
theorem call_family_cases (c : Call) :
    famTransfer c ∨ famSigned c ∨ famAdmin c ∨ famDispatch c ∨ famInitRevert c ∨
      ∃ token dst v, c = .rescueERC20 token dst v := by
  cases c <;> first
    | exact Or.inl trivial
    | exact Or.inr (Or.inl trivial)
    | exact Or.inr (Or.inr (Or.inl trivial))
    | exact Or.inr (Or.inr (Or.inr (Or.inl trivial)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩))))

end Blanc.Lift.Usdc
