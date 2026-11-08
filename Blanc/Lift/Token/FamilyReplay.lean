import Blanc.ExecutionOwnerFamily
import Blanc.Lift.Token.Core

/-!
# The guarded book carrier and the observer bridge (contract-neutral)

A code family's ladder (`Blanc/ExecutionOwnerFamily.lean`) replays over a carrier whose boundary may
depend on storage the family's frames can rewrite (a proxy's implementation slot).  The **guarded
book carrier** reads a book ledger off the owner's storage together with a guard's verdict; a replay
claims, from a guarded boundary and over allowed messages only, that the book runs the steps and the
guard still holds, so the carrier says nothing at an unguarded boundary
(`guardedBookCarrier_unguarded`).

Its observer view sees the message of every non-static observer frame at the owner.  A token core
speaks of entry frames (`entryAsks`).  `ObserverChain` pairs each non-static entry with its observer
(itself, or the adjacent observer with a related message), and `ObserverChain.run_eq` turns the book
run over observer asks into the run over entry asks.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- **Entries and observers paired along a frame list.**  Each non-static entry at `T` is its own
observer, or is immediately followed by its (non-entry) observer carrying a related message; every
other frame is neither. -/
inductive ObserverChain (T : Adr) (Obs : Exec.Frame → Prop) (R : Sevm → Sevm → Prop) :
    List Exec.Frame → Prop
  | nil : ObserverChain T Obs R []
  | skip {f : Exec.Frame} {fs : List Exec.Frame} :
      ¬ (IsEntry T f ∧ f.sevm.isStatic = false) →
      ¬ (f.sevm.currentTarget = T ∧ f.sevm.isStatic = false ∧ Obs f) →
      ObserverChain T Obs R fs → ObserverChain T Obs R (f :: fs)
  | self {f : Exec.Frame} {fs : List Exec.Frame} :
      IsEntry T f → f.sevm.isStatic = false → Obs f →
      ObserverChain T Obs R fs → ObserverChain T Obs R (f :: fs)
  | pair {e o : Exec.Frame} {fs : List Exec.Frame} :
      IsEntry T e → e.sevm.isStatic = false → ¬ Obs e →
      o.sevm.currentTarget = T → o.sevm.isStatic = false → Obs o → ¬ IsEntry T o →
      R e.sevm o.sevm → ObserverChain T Obs R fs → ObserverChain T Obs R (e :: o :: fs)

end Blanc.Lift.Token
