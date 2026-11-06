import Blanc.Lift.CurveCoins.ApprovalLog

/-!
# The logs a reader of `noSignature` filters on

`AuthLogged`: `AuthorizationUsed` with the authorizer. `ApprovalLogged`: `Approval` with the owner. Each says a state holds
the log at the frame's own coin. `ret_logged`, `ric_stop_logs` carry them to a walk's end.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- A state holding the `AuthorizationUsed` log of the frame's own coin, with its authorizer. -/
def AuthLogged (sevm : Sevm) (d : Devm) (a : Adr) : Prop :=
  ∃ l ∈ d.logs, l.address = sevm.currentTarget ∧
    l.topics.take 2 = [0x98de503528ee59b575ef0c0a2576a82497bfc029a5685b209e9ec333479b10a5, a.toB256]

theorem AuthLogged.mono {sevm : Sevm} {d d' : Devm} {a : Adr} (h : AuthLogged sevm d a)
    (keep : ∀ l ∈ d.logs, l ∈ d'.logs) : AuthLogged sevm d' a := by
  obtain ⟨l, m, r⟩ := h
  exact ⟨l, keep l m, r⟩

theorem AuthLogged.of_eq {sevm : Sevm} {d d' : Devm} {a : Adr} (h : AuthLogged sevm d a) (e : d'.logs = d.logs) :
    AuthLogged sevm d' a :=
  h.mono fun l m => by rw [e]; exact m

/-- A state holding the `Approval` log of the frame's own coin, with its owner. -/
def ApprovalLogged (sevm : Sevm) (d : Devm) (a : Adr) : Prop :=
  ∃ l ∈ d.logs, l.address = sevm.currentTarget ∧ l.topics.take 2 = [CurveCoins.approvalTopic, a.toB256]

theorem ApprovalLogged.mono {sevm : Sevm} {d d' : Devm} {a : Adr} (h : ApprovalLogged sevm d a)
    (keep : ∀ l ∈ d.logs, l ∈ d'.logs) : ApprovalLogged sevm d' a := by
  obtain ⟨l, m, r⟩ := h
  exact ⟨l, keep l m, r⟩

theorem ApprovalLogged.of_eq {sevm : Sevm} {d d' : Devm} {a : Adr} (h : ApprovalLogged sevm d a)
    (e : d'.logs = d.logs) : ApprovalLogged sevm d' a :=
  h.mono fun l m => by rw [e]; exact m

/-- `ret_named`, keeping the logs. -/
theorem ret_logged {o : Outcome} {B : Devm} {S : List B256} {M : Mem} {G : Nat}
    (e : Seg.done o = Seg.done (.returned (St B S M G))) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧ Devm.getStor b' = Devm.getStor B ∧ b'.logs = B.logs :=
  ⟨B, M, G, Seg.done.inj e, rfl, rfl⟩

/-- A `STOP` halt keeps the base's logs. -/
theorem ric_stop_logs {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b post : Devm} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunCut fs sevm C (St b S M G) (.last .stop) (.done (.halted post))) : post.logs = b.logs := by
  cases run with
  | last hl =>
    simp only [Linst.Run, Linst.run, Except.ok.injEq] at hl
    subst hl
    rfl

end Blanc.Lift.Usdc
