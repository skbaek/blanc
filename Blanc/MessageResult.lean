import Blanc.Semantics

/-!
# Contract-neutral settled message observations

This module names only result-level facts.  It does not identify a contract,
an implementation address, or a particular forwarding program.

`ChildToWrapperSettledAt` is intentionally more exact than a symmetric result
equivalence.  A clean delegated child is returned cleanly, while any settled
child error is converted into the wrapper's ordinary `REVERT`.  The wrapper
copies the complete child output.  Child logs commit only on the clean arm;
the failed-child arm retains no child logs.
-/

namespace Blanc

open Jaune

/-- The result returned by Jaune's raw message wrapper. -/
abbrev MessageResult : Type :=
  Except (EvmError × State × AdrSet × Tra) Devm

/-- Persistent storage agrees at one account for every EVM word key. -/
def MessageStorageEqualAt
    (owner : Adr) (left right : State) : Prop :=
  ∀ key, (left.get owner).stor.get key = (right.get owner).stor.get key

/-- Transient storage agrees at one account for every EVM word key. -/
def MessageTransientEqualAt
    (owner : Adr) (left right : Tra) : Prop :=
  ∀ key,
    (left.getD owner Stor.empty).get key =
      (right.getD owner Stor.empty).get key

/-- Exact status conversion performed by a forwarding `DELEGATECALL` wrapper.
A clean child remains clean.  Any settled child failure, whether `REVERT` or an
exceptional halt, makes the wrapper execute its ordinary revert arm. -/
def DelegatecallStatusRelated
    (child wrapper : Option SettledHalt) : Prop :=
  (child = none ∧ wrapper = none) ∨
    (child.isSome = true ∧ wrapper = some .revert)

theorem DelegatecallStatusRelated.clean :
    DelegatecallStatusRelated none none :=
  Or.inl ⟨rfl, rfl⟩

theorem DelegatecallStatusRelated.failed
    {child : Option SettledHalt} (failed : child.isSome = true) :
    DelegatecallStatusRelated child (some .revert) :=
  Or.inr ⟨failed, rfl⟩

/-- Exact successful-channel relation between the settled delegated child and
the settled forwarding wrapper.  Gas and warm-access sets are deliberately not
fields.  The relation does pin status conversion, complete output, committed
logs, and the persistent/transient storage projections at the storage owner. -/
structure ChildToWrapperOkAt
    (owner : Adr) (child wrapper : Devm) : Prop where
  status : DelegatecallStatusRelated child.error wrapper.error
  output : wrapper.output = child.output
  logs : wrapper.logs =
    (if child.error.isNone then child.logs else [])
  storage : MessageStorageEqualAt owner child.state wrapper.state
  transientStorage : MessageTransientEqualAt owner
    child.transientStorage wrapper.transientStorage

/-- Exact child-to-wrapper envelope at `processMessage` altitude.

The fatal error channel has no returndata or logs.  It retains the exact error
and the same storage projections while deliberately omitting created-account
and warm-access bookkeeping from the observation. -/
def ChildToWrapperSettledAt (owner : Adr) :
    MessageResult → MessageResult → Prop
  | .ok child, .ok wrapper => ChildToWrapperOkAt owner child wrapper
  | .error ⟨childError, childState, _, childTransient⟩,
      .error ⟨wrapperError, wrapperState, _, wrapperTransient⟩ =>
      childError = wrapperError ∧
        MessageStorageEqualAt owner childState wrapperState ∧
        MessageTransientEqualAt owner childTransient wrapperTransient
  | _, _ => False

@[simp] theorem ChildToWrapperSettledAt.ok_iff
    (owner : Adr) (child wrapper : Devm) :
    ChildToWrapperSettledAt owner (.ok child) (.ok wrapper) ↔
      ChildToWrapperOkAt owner child wrapper :=
  Iff.rfl

@[simp] theorem ChildToWrapperSettledAt.error_iff
    (owner : Adr)
    (childError wrapperError : EvmError)
    (childState wrapperState : State)
    (childCreated wrapperCreated : AdrSet)
    (childTransient wrapperTransient : Tra) :
    ChildToWrapperSettledAt owner
        (.error ⟨childError, childState, childCreated, childTransient⟩)
        (.error ⟨wrapperError, wrapperState, wrapperCreated,
          wrapperTransient⟩) ↔
      childError = wrapperError ∧
        MessageStorageEqualAt owner childState wrapperState ∧
        MessageTransientEqualAt owner childTransient wrapperTransient :=
  Iff.rfl

end Blanc
