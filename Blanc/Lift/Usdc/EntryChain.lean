import Blanc.Lift.ViewChain
import Blanc.Lift.BalanceLocality
import Blanc.Lift.CurveCoins.Keep
import Blanc.Lift.Usdc.RefineShape

/-!
# USDC's entry frames: the statement of balance-entry locality

The contract of U3c, compiled ahead of its proof, so that its consumers and the initializer unit can
build on the names:

* `ledgerView`: the words apart from the proxy's two slots. An upgrade writes the implementation slot
  between two token frames, so USDC's frames chain on this view;
* `EntryObs`: the chain's frames, the non-admin proxy frames. The admin word's frames write only
  the proxy's slots, so they are unobserved, and the frame an `upgradeToAndCall` calls below itself
  observes itself;
* `V22At`, `heldAt`: a frame reads the holder's entry by the code its implementation word finds at its
  own entry, not through the view: the whole word under V2 and V2_1, the low 255 bits under V2_2;
* `UsdcCertified`: the proxy admin's power, restrained at one state;
* `InitializerKeeps`: the named power still open as a field.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The words apart from the proxy's implementation and admin slots. -/
def ledgerView (w : StorWords) : StorWords := fun k =>
  if k = implSlot ∨ k = adminSlot then 0 else w k

/-- **The chain's frames**: frames of the proxy's runtime whose caller is not the admin word at their
entry. -/
def EntryObs (T : Adr) (F : Exec.Frame) : Prop :=
  F.sevm.code = Proxy.code ∧ F.sevm.caller ≠ adminOf F.pre.state T

/-- The implementation word at the frame's entry finds FiatTokenV2_2's code: the reading follows the
code the frame runs, not the address that holds it. -/
def V22At (T : Adr) (F : Exec.Frame) : Prop :=
  F.pre.getCode ((F.pre.state.getStor T).get implSlot).toAdr = Impl.code

open Classical in
/-- **How a frame reads `h`'s entry in a view**, by the code its implementation word finds at its own
entry: the low 255 bits under V2_2, the whole word before it. -/
noncomputable def heldAt (T h : Adr) (F : Exec.Frame) (w : StorWords) : Nat :=
  if V22At T F then balanceBits (w (balSlot h)) else (w (balSlot h)).toNat

/-- **The implementation word names one of the three versions, V2_2 finds its library, and the word names no
precompile on any fork** (the proxy admin's power, at one state). The library is deployed after the pool's cut, so
this is not a fact of the start state. A delegate to a precompile runs it and not the code at the address, so
`UsdcImplAt` alone does not say what the frame runs. -/
def UsdcCertified (d : Devm) (T : Adr) : Prop :=
  CurveCoins.UsdcImplAt d T ∧
    (d.getCode (d.getStorVal T implSlot).toAdr = Impl.code → d.getCode usdcLib = Lib.code) ∧
    ∀ f : Fork, ¬ (Fork.ruleSet f).isPrecomp (d.getStorVal T implSlot).toAdr

/-- The four initializers. -/
def usdcInitializers : List B256 := [0x3357162b, 0xd608ea64, 0x2fc81e09, 0x430239b4]

/-- **What the initializer unit discharges**: an initializer that commits does not lower the holder's
entry, as the frame reads it. The admin's power, by way of the upgrade that runs it. -/
def InitializerKeeps (T h : Adr) (settled : List Exec.Frame) : Prop :=
  ∀ F ∈ settled, F.sevm.currentTarget = T → F.sevm.isStatic = false → EntryObs T F →
    Blanc.Sevm.selector F.sevm ∈ usdcInitializers →
    heldAt T h F (ledgerView (wordsAt T F.pre.state)) ≤ heldAt T h F (ledgerView (wordsAt T F.post.state))

variable {T h : Adr}

/-- Bits never exceed the word. -/
theorem bits_le_word (w : B256) : balanceBits w ≤ w.toNat :=
  Nat.mod_le _ _

/-- A word below the flag is its bits. -/
theorem bits_eq_of_lt {w : B256} (hw : w.toNat < 2 ^ 255) : balanceBits w = w.toNat :=
  Nat.mod_eq_of_lt hw

/-- The view does not hide a balance entry apart from the proxy's slots. -/
theorem ledgerView_bal {w : StorWords} {a : Adr} (hi : balSlot a ≠ implSlot) (ha : balSlot a ≠ adminSlot) :
    ledgerView w (balSlot a) = w (balSlot a) := by
  unfold ledgerView
  refine ite_eq_right ?_
  rintro (e | e)
  · exact (hi e).elim
  · exact (ha e).elim

end Blanc.Lift.Usdc
