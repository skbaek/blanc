import Blanc.Lift.Usdc.Hist
import Blanc.Lift.Usdc.Book

/-!
# The per-entry refinement shapes of USDC's implementation and library frames

The shapes the USDC refinement units deliver and the family ladder consumes
(`Blanc/ExecutionOwnerFamily.lean`):

* `ImplStepLaw fam` — a successful non-static implementation frame at the proxy's storage whose message
  decodes to a call of the family `fam` commits the book's step on its message, keeps the proxy's
  implementation and admin slots, and spawns only `DELEGATECALL`s (library frames), at whose nodes the
  ledger is still good: the whole-frame shape;
* `RescueLaw` — `rescueERC20` keeps the proxy's storage up to and after its single `CALL` and the book's
  step on its message is the identity: the model shape with one own step;
* `LibQuiet` — a successful library frame keeps its storage owner's storage along its own chain and
  spawns only static frames.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift.Token

/-- `rescueERC20(address,address,uint256)`. -/
def rescueSelector : B256 := 0xb2118a8d

/-- **The whole-frame step law of a call family** (the shape U6d (transfer/approve), U6e (signed),
U6f (roles/mint/burn/pause/blacklist), U6g (dispatch, views, `initialize*`) each deliver for their
calls).  A successful non-static implementation frame at the proxy's storage, entered by a caller
other than the admin word, with the library installed and its keys tracked in an injective universe
apart from the fixed slots, whose message decodes to a call of the family, commits the book's step on
its message, keeps the proxy's two slots, and spawns only library frames. -/
def ImplStepLaw (fam : Call → Prop) : Prop :=
  ∀ {P : Adr} {U : Key → Prop} {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post)),
    sevm.code = Impl.code → sevm.currentTarget = P → sevm.codeAddress = some usdcImpl →
    CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
    SlotFootprint.Inj Key.slot U → SlotFootprint.Apart Key.slot fixedSlots U →
    (∀ k ∈ frameKeys sevm, U k) → some (pre.state.getCode usdcLib).toList = libSem.image →
    sevm.caller ≠ adminOf pre.state P →
    ∀ c, decodeCall sevm = some c → fam c →
      (usdcBookS P).step (ledger U (pre.state.getStor P)) sevm =
          some (ledger U (post.state.getStor P)) ∧
        (post.state.getStor P).get implSlot = (pre.state.getStor P).get implSlot ∧
        (post.state.getStor P).get adminSlot = (pre.state.getStor P).get adminSlot ∧
        ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
          ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
            x = .delegatecall ∧ ((ledger U (pre.state.getStor P)).Good →
              (ledger U (N.devm.state.getStor P)).Good)

/-- **The model law of `rescueERC20`** (U6f): the frame's storage at the proxy is unchanged up to and
after its single `CALL`, and the book's step on its message is the identity. -/
def RescueLaw : Prop :=
  ∀ {P : Adr} {U : Key → Prop} {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post)),
    sevm.code = Impl.code → sevm.currentTarget = P → sevm.codeAddress = some usdcImpl →
    CoveredFork sevm.benvStat.fork → sevm.isStatic = false → (∀ k ∈ frameKeys sevm, U k) →
    sevm.caller ≠ adminOf pre.state P → Blanc.Sevm.selector sevm = rescueSelector →
      (usdcBookS P).step (ledger U (pre.state.getStor P)) sevm =
          some (ledger U (pre.state.getStor P)) ∧
        ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
          ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
            x = .call ∧ N.devm.state.getStor P = pre.state.getStor P ∧
            ∀ N', Exec.Deriv.ParentStep N' N →
              post.state.getStor P = N'.devm.state.getStor P ∧
              ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y)

/-- **The library is quiet** (U6e, from the library's certificate walk): a successful library frame
keeps its storage owner's storage at every node of its own chain and spawns only static frames. -/
def LibQuiet : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post)),
    sevm.code = Lib.code → CoveredFork sevm.benvStat.fork →
    (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      N.devm.state.getStor sevm.currentTarget = pre.state.getStor sevm.currentTarget) ∧
    ∀ f ∈ Exec.descendantFrames run, f.sevm.isStatic = true

end Blanc.Lift.Usdc
