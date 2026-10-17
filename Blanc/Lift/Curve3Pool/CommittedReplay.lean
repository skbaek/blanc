import Blanc.Lift.Curve3Pool.Refine
import Blanc.ExecutionFrames

/-!
# Curve 3pool: committed invocations and their model replay

A history step of the pool is one committed, non-static pc-`0` pool frame together with the
environment `e` it observed (`PoolInvocation`).  The environment is recorded data, not a function of
the frame: `EnvOf` constrains only the answers the frame actually received, so each invocation
carries the `Env` its frame theorem produced, with `EnvOf` evidence (`PoolInvocation.Authentic`).

* `PoolRun s invs s'` — the invocations replay through `Model.step` from `s` to `s'`, each with the
  frame's exact raw effect (`RawEffect`);
* `runPool` — the deterministic fold over the recorded environments; `PoolRun.runPool_eq` shows a
  replay is that fold, so the end state is unique (`PoolRun.unique`);
* `PoolRun.append`, `PoolRun.coins_token` — replays compose, and keep the coins and the token.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc

/-- One committed pool frame with the environment it observed. -/
structure PoolInvocation where
  frame : Exec.Frame
  env : Env

/-- **An authentic invocation**: a committed, non-static pc-`0` frame at the pool, and its recorded
environment is what that frame observed. -/
def PoolInvocation.Authentic (pool : Adr) (i : PoolInvocation) : Prop :=
  i.frame.pc = 0 ∧ Execution.commits i.frame.out = true ∧ i.frame.sevm.currentTarget = pool ∧
    i.frame.sevm.isStatic = false ∧ EnvOf (Exec.Frame.rootDeriv i.frame) i.env

/-- **The model replay of a list of invocations**: each is accepted by `step` on its decoded call
and its recorded environment, with the frame's exact raw effect, from the state the previous one
reached. -/
def PoolRun : State → List PoolInvocation → State → Prop
  | s, [], s' => s' = s
  | s, i :: rest, s' => ∃ o, step s i.env (decodeCall i.frame.sevm) = some o ∧
      RawEffect (Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧ PoolRun o.state rest s'

/-- The deterministic fold of `step` over the recorded environments. -/
def runPool : State → List PoolInvocation → Option State
  | s, [] => some s
  | s, i :: rest => (step s i.env (decodeCall i.frame.sevm)).bind fun o => runPool o.state rest

namespace PoolRun

theorem nil (s : State) : PoolRun s [] s := rfl

/-- A replay is the deterministic fold. -/
theorem runPool_eq : ∀ {s s' : State} {invs : List PoolInvocation},
    PoolRun s invs s' → runPool s invs = some s'
  | _, _, [], h => by
    simp only [PoolRun] at h
    rw [h]
    rfl
  | _, _, _ :: _, h => by
    obtain ⟨o, hstep, -, rest⟩ := h
    simp only [runPool, hstep, Option.bind_some]
    exact runPool_eq rest

/-- The end state of a replay is unique. -/
theorem unique {s t t' : State} {invs : List PoolInvocation} (h : PoolRun s invs t)
    (h' : PoolRun s invs t') : t = t' :=
  Option.some.inj ((runPool_eq h).symm.trans (runPool_eq h'))

/-- Replays compose. -/
theorem append : ∀ {s m t : State} {left right : List PoolInvocation},
    PoolRun s left m → PoolRun m right t → PoolRun s (left ++ right) t
  | _, _, _, [], _, h₁, h₂ => by
    simp only [PoolRun] at h₁
    subst h₁
    exact h₂
  | _, _, _, _ :: _, _, h₁, h₂ => by
    obtain ⟨o, hstep, hraw, rest⟩ := h₁
    exact ⟨o, hstep, hraw, append rest h₂⟩

/-- A replay keeps the coins and the token. -/
theorem coins_token : ∀ {s t : State} {invs : List PoolInvocation},
    PoolRun s invs t → t.coins = s.coins ∧ t.token = s.token
  | _, _, [], h => by
    simp only [PoolRun] at h
    subst h
    exact ⟨rfl, rfl⟩
  | _, _, _ :: _, h => by
    obtain ⟨o, hstep, -, rest⟩ := h
    obtain ⟨hc, ht⟩ := (step_keeps hstep).coins_token
    obtain ⟨hc', ht'⟩ := coins_token rest
    exact ⟨hc'.trans hc, ht'.trans ht⟩

end PoolRun

end Blanc.Lift.Curve3Pool
