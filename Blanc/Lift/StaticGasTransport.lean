import Blanc.Lift.ExactCallProfile

/-!
# Transport across the static initial-gas coordinate

Changing `Sevm.gas` retains each instruction's complete dynamic input and output.
In spawning steps the child message and execution slot stay the same. Dynamic
`Devm.gasLeft`, including the value observed by GAS, is not changed here.
-/

namespace Blanc.Lift

open Jaune

/-- Update static initial gas, retaining the single child slot and complete post. -/
theorem ninstRunCompiled_withStaticGas
    {s : Sevm} {a post : Devm} {n : Ninst}
    (h : Ninst.RunCompiled s a n post) (F : Nat) :
    Ninst.RunCompiled {s with gas := F} a n post := by
  exact h

/-- Terminal instruction transport retains both success and error outcomes. -/
theorem linstRun_withStaticGas
    {s : Sevm} {a : Devm} {l : Linst} {ex : Execution}
    (h : Linst.Run s a l ex) (F : Nat) :
    Linst.Run {s with gas := F} a l ex := by
  exact h

/-- Transport a complete exact tree without changing dynamic gas or its outcome. -/
theorem SFunc.RunExact.withStaticGas
    {fs : List SFunc} {s : Sevm} {a : Devm} {f : SFunc} {o : Outcome}
    (h : SFunc.RunExact fs s a f o) (F : Nat) :
    SFunc.RunExact fs {s with gas := F} a f o := by
  refine SFunc.RunExact.rec
    (motive := fun devm f o _ => SFunc.RunExact fs {s with gas := F} devm f o)
    (fun d hpop _ ih => .zero d hpop ih)
    (fun d w hne hpop _ ih => .succ d w hne hpop ih)
    (fun d hpop _ ih => .toZero d hpop ih)
    (fun d w hne hget hpop _ ih => .toSucc d w hne hget hpop ih)
    (fun hrun => .last (linstRun_withStaticGas hrun F))
    (fun hrun _ ih => .next (ninstRunCompiled_withStaticGas hrun F) ih)
    (fun hburn _ ih => .dest hburn ih)
    (fun d hget hpop _ ih => .jump d hget hpop ih)
    (fun d hpop => .ret d hpop)
    (fun d hget hpop _ ih => .callHalt d hget hpop ih)
    (fun d hget hpop _ _ ihrun ihcont => .callRet d hget hpop ihrun ihcont)
    (fun {_ _ p _ _} hstep _ ih => .pcAt hstep ih)
    h

/-- Identity readiness depends on the environment's rules, not its initial gas. -/
theorem IdReady.withStaticGas {s : Sevm} {b : Devm}
    (h : IdReady s b) (F : Nat) : IdReady {s with gas := F} b := by
  exact ⟨h.nodeleg, h.warm, h.pre, h.fork⟩

/-- Transport a profile with the identical debit, successor and fixed predicates. -/
theorem ExactCallProfile.withStaticGas
    {s : Sevm} {op : Ninst}
    {entry : Devm → List B256 → Mem → Nat → Devm}
    {Ready : Devm → List B256 → Mem → Nat → Prop}
    {After : Devm → List B256 → Mem → Devm → Prop} {U : Nat}
    {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (h : ExactCallProfile s op entry Ready After U debit next) (F : Nat) :
    ExactCallProfile {s with gas := F} op entry Ready After U debit next := by
  exact ⟨h.entry_gas, h.congr, h.sound⟩

/-- Retain a static-word profile's functions and indexed identity postcondition. -/
theorem StaticWordCallProfile.withStaticGas
    {s : Sevm} {W W' : Devm → Prop} {t A : B256} {data : Bytes}
    {U : Nat} {ii is oi : B256}
    {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (h : StaticWordCallProfile s W W' t data A U ii is oi debit next) (F : Nat) :
    StaticWordCallProfile {s with gas := F} W W' t data A U ii is oi debit next := by
  refine ⟨h.entry_gas, h.congr, ?_⟩
  intro b S M G hready
  obtain ⟨hc, d, hrun, hgas, hnext, out, hpost, hlen, hlt, hA, hW', hid⟩ :=
    h.sound b S M G hready
  refine ⟨hc, d, ninstRunCompiled_withStaticGas hrun F, hgas, hnext,
    out, hpost, hlen, hlt, hA, hW', ?_⟩
  intro hb
  exact (hid (hb.withStaticGas s.gas)).withStaticGas F

/-- Retain a mutable profile's functions, owner storage and identity postcondition. -/
theorem MutableCallProfile.withStaticGas
    {s : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes} {ok : Bytes → Prop}
    {U : Nat} {ii is oi : B256}
    {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (h : MutableCallProfile s W W' t data ok U ii is oi debit next) (F : Nat) :
    MutableCallProfile {s with gas := F} W W' t data ok U ii is oi debit next := by
  refine ⟨h.entry_gas, h.congr, ?_⟩
  intro b S M G hready
  obtain ⟨hc, d, hrun, hgas, hnext, hpost, hok, hlt, hstor, hW', hid⟩ :=
    h.sound b S M G hready
  refine ⟨hc, d, ninstRunCompiled_withStaticGas hrun F, hgas, hnext,
    hpost, hok, hlt, hstor, hW', ?_⟩
  intro hb
  exact (hid (hb.withStaticGas s.gas)).withStaticGas F

end Blanc.Lift
