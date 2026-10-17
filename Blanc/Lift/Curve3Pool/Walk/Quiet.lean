import Blanc.Lift.Curve3Pool.Refine
import Blanc.Lift.Curve3Pool.Cert
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.WalkSteps
import Blanc.Lift.Vyper
import Blanc.Lift.MemGlue

/-!
# The walk contract of a body that makes no external call

The admin functions without a coin call (`commit_new_fee` … `unkill_me`) and the public getters
make no `CALL`/`STATICCALL`: their frames observe only the block timestamp, `msg.sender` and
`msg.value`. Their safety walks deliver a `QuietLands`, stated over the body's entry base `b`
(the dispatcher hands the body `quietSt sevm b G`: the frame's entry state with empty stack and
the prologue's memory image), and `rawEffect_of_quietLands` turns it into Spec's `RawEffect` for
a frame `D` with no child frames.

* `quietEnv sevm`: the environment such a frame observes (no coin or token answer);
* `envOf_quiet`: every frame observes it (`EnvOf`'s answer clauses constrain positive answers
  only);
* `QuietLands sevm b post o`: the post state's pool storage is the model's footprint effect, other
  accounts' storage is unchanged, the model's events are appended, the output is the model's
  return word (or, for `STOP`, the entry output), and the model makes no call;
* `QuietSafe sevm b s f`: every successful halt of body `f` from its entry lands as the model's
  step on the decoded call says.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-- The body's entry state: the base, empty stack, the Vyper prologue's memory image. -/
def quietSt (sevm : Sevm) (b : Devm) (G : Nat) : Devm :=
  St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G

/-- The environment of a frame that makes no external call. -/
def quietEnv (sevm : Sevm) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun _ => ⟨none, none, false, false⟩, none, false, false⟩

/-- Every frame observes `quietEnv`: it carries no positive coin or token answer. -/
theorem envOf_quiet (D : Exec.Deriv) : EnvOf D (quietEnv D.sevm) where
  time := rfl
  caller := rfl
  value := rfl
  coin _ :=
    ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun h => (by cases h),
      fun h => (by cases h)⟩
  supply _ h := by cases h
  mintOk h := by cases h
  burnOk h := by cases h

/-- **A quiet body's landing** for the model result `o`. -/
structure QuietLands (sevm : Sevm) (b post : Devm) (o : Out) : Prop where
  stor : StorEffect (decodeCall sevm) (b.getStor sevm.currentTarget)
    (post.getStor sevm.currentTarget) o.state
  other : ∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a
  logs : post.logs = b.logs ++ o.events.map (eventLog sevm.currentTarget)
  output : post.output = retOut b.output o.ret
  calls : o.calls = []

/-- **The safety form of a quiet body**: every successful halt of `f` from the body's entry is
the model's step on the decoded call, observing `quietEnv`. -/
def QuietSafe (sevm : Sevm) (b : Devm) (s : State) (f : SFunc) : Prop :=
  ∀ G post, SFunc.Run cert.prog sevm (quietSt sevm b G) f (.halted post) →
    ∃ o, step s (quietEnv sevm) (decodeCall sevm) = some o ∧ QuietLands sevm b post o

/-- **A quiet landing of a childless frame is its raw effect.** -/
theorem rawEffect_of_quietLands {D : Exec.Deriv} {post : Devm} {o : Out}
    (hch : children D = []) (h : QuietLands D.sevm D.devm post o) :
    RawEffect D post (quietEnv D.sevm) o where
  env := envOf_quiet D
  stor := h.stor
  logs := by rw [h.logs, hch, List.flatMap_nil, List.append_nil]
  output := h.output
  calls _ := by
    simp only [CallsOf, modelCalls, hch, h.calls, List.filterMap_nil, List.map_nil,
      List.filter_nil]

/-! ## Helpers for the walks -/

/-- A footprint storage effect from the three facts a walk produces. -/
theorem StorEffect.of {c : Call} {pre post : Stor} {s' : State}
    (kept : ∀ x, (∀ f ∈ footprint c, f.slot ≠ x) → post.get x = pre.get x)
    (written : ∀ f ∈ footprint c, f.Reads post s') : StorEffect c pre post s' :=
  ⟨kept, written⟩

/-! ## Inversion helpers -/

section Guards

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg} {fail ok : SFunc}

theorem eq_of_eqCheck_ne_zero' {a c : B256} (h : B256.eqCheck a c ≠ 0) : a = c := by
  unfold B256.eqCheck at h; split at h
  · assumption
  · exact absurd rfl h

/-- `PUSH2 ok JUMPI` over a reverting fall-through, inverted: the tested word is nonzero. -/
theorem ric_assertJump {h l : UInt8} {w : B256} {le : [h, l].length ≤ 32}
    (hf : fail.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b (w :: S) M G)
      (.next (.push [h, l] le) (.branch fail (.dest ok))) r) :
    w ≠ 0 ∧ ∃ G', SFunc.RunCut fs sevm C (St b S M G') ok r := by
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G2, run⟩ | ⟨hw, G2, run⟩
  · exact (run.false_of_noOk hf).elim
  obtain ⟨G3, run⟩ := ric_dest run
  exact ⟨hw, G3, run⟩

/-- The owner guard `PUSH1 4 SLOAD CALLER EQ PUSH2 ok JUMPI`, inverted. -/
theorem ric_ownerGuard (hfork : CoveredFork sevm.benvStat.fork) {h l : UInt8}
    {le4 : [(0x04 : UInt8)].length ≤ 32} {le : [h, l].length ≤ 32} (hf : fail.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b S M G)
      (.next (.push [0x04] le4) (.next (.reg .sload) (.next (.reg .caller) (.next (.reg .eq)
        (.next (.push [h, l] le) (.branch fail (.dest ok))))))) r) :
    sevm.caller.toB256 = b.getStorVal sevm.currentTarget ownerSlot ∧
      ∃ G', SFunc.RunCut fs sevm C (St (afterSload sevm b ownerSlot) S M G') ok r := by
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_caller s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_eq s1
  obtain ⟨hw, G5, run⟩ := ric_assertJump hf run
  exact ⟨eq_of_eqCheck_ne_zero' hw, G5, run⟩

/-- The world part of a quiet body's straight-line run: the base `B` reached from the entry
base `b` by selected loads and stores keeps every other account, the logs and the output, and
holds `st` at the pool. -/
structure QStep (sevm : Sevm) (b B : Devm) (st : Stor) : Prop where
  self : B.getStor sevm.currentTarget = st
  other : ∀ a, a ≠ sevm.currentTarget → B.getStor a = b.getStor a
  logs : B.logs = b.logs
  output : B.output = b.output

theorem QStep.refl (sevm : Sevm) (b : Devm) : QStep sevm b b (b.getStor sevm.currentTarget) :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl⟩

theorem QStep.sload {B : Devm} {st : Stor} (h : QStep sevm b B st) (k : B256) :
    QStep sevm b (afterSload sevm B k) st :=
  ⟨by rw [afterSload_getStor, h.self], fun a ha => by rw [afterSload_getStor, h.other a ha],
    by rw [afterSload_logs, h.logs], by rw [afterSload_output, h.output]⟩

theorem QStep.sstore {B : Devm} {st : Stor} (h : QStep sevm b B st) (k v : B256) :
    QStep sevm b (afterSstore sevm B k v) (st.set k v) :=
  ⟨by rw [afterSstore_getStor_self, h.self],
    fun a ha => by rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), h.other a ha],
    by rw [afterSstore_logs, h.logs], by rw [afterSstore_output, h.output]⟩

theorem QStep.getStorVal {B : Devm} {st : Stor} (h : QStep sevm b B st) (k : B256) :
    B.getStorVal sevm.currentTarget k = st.get k := by
  show (Devm.getStor B sevm.currentTarget).get k = _
  rw [h.self]

theorem getStorVal_afterSstore_self' {B : Devm} {k v x : B256} :
    (afterSstore sevm B k v).getStorVal sevm.currentTarget x =
      ((B.getStor sevm.currentTarget).set k v).get x := by
  show (Devm.getStor _ _).get _ = _
  rw [afterSstore_getStor_self]

theorem quietEnv_value (hv : sevm.value = 0) : (quietEnv sevm).value = 0 := by
  show sevm.value.toNat = 0
  rw [hv]; rfl

theorem quietEnv_owner {s : State} (hc : Checkpoint (b.getStor sevm.currentTarget) s)
    (hown : sevm.caller.toB256 = b.getStorVal sevm.currentTarget ownerSlot) :
    (quietEnv sevm).caller = s.owner := by
  show sevm.caller.toB256.toNat = s.owner
  rw [hown]; exact hc.abs.owner

/-- A quiet `STOP` with no log. -/
theorem quietLands_stop {B : Devm} {st : Stor} {o : Out}
    (h : QStep sevm b B st)
    (hst : StorEffect (decodeCall sevm) (b.getStor sevm.currentTarget) st o.state)
    (hev : o.events = []) (hret : o.ret = none) (hc : o.calls = []) :
    QuietLands sevm b (St B S M G) o where
  stor := by rw [show (St B S M G).getStor sevm.currentTarget = B.getStor sevm.currentTarget
    from rfl, h.self]; exact hst
  other a ha := h.other a ha
  logs := by rw [hev, List.map_nil, List.append_nil]; exact h.logs
  output := by rw [hret]; exact h.output
  calls := hc

/-- A quiet `STOP` after one log. -/
theorem quietLands_stopLog {B : Devm} {st : Stor} {o : Out} {L : Log}
    (h : QStep sevm b B st)
    (hst : StorEffect (decodeCall sevm) (b.getStor sevm.currentTarget) st o.state)
    (hev : o.events.map (eventLog sevm.currentTarget) = [L]) (hret : o.ret = none)
    (hc : o.calls = []) :
    QuietLands sevm b (St (B.addLog L) S M G) o where
  stor := by rw [show (St (B.addLog L) S M G).getStor sevm.currentTarget =
    B.getStor sevm.currentTarget from rfl, h.self]; exact hst
  other a ha := h.other a ha
  logs := by
    rw [hev]
    show B.logs ++ [L] = _
    rw [h.logs]
  output := by rw [hret]; exact h.output
  calls := hc

/-- A quiet view's `RETURN` of one word that it read. -/
theorem quietLands_ret {B post : Devm} {o : Out} {r : Nat}
    (h : QStep sevm b B (b.getStor sevm.currentTarget))
    (hkept : footprint (decodeCall sevm) = [])
    (hev : o.events = []) (hret : o.ret = some r) (hc : o.calls = [])
    (hout : post.output = word r) (hs : ∀ a, post.getStor a = B.getStor a)
    (hl : post.logs = B.logs) :
    QuietLands sevm b post o where
  stor := ⟨fun x _ => by rw [hs, h.self], fun f hf => by rw [hkept] at hf; cases hf⟩
  other a ha := by rw [hs, h.other a ha]
  logs := by rw [hev, List.map_nil, List.append_nil, hl, h.logs]
  output := by rw [hret, hout]; rfl
  calls := hc

theorem QStep.trans {sevm : Sevm} {b B B' : Devm} {st st' : Stor} (h : QStep sevm b B st)
    (h' : QStep sevm B B' st') : QStep sevm b B' st' :=
  ⟨h'.self, fun a ha => by rw [h'.other a ha, h.other a ha], by rw [h'.logs, h.logs],
    by rw [h'.output, h.output]⟩

/-- `QStep` composition through an intermediate base. -/
theorem QStep.chain {b B B' : Devm} {st : Stor} (h : QStep sevm b B st)
    (h' : QStep sevm B B' (B.getStor sevm.currentTarget)) : QStep sevm b B' st := by
  rw [h.self] at h'; exact h.trans h'

end Guards

/-- Resolve memory reads over a chain of word stores from a well-formed base. -/
macro "mem_wf" : tactic => `(tactic| (repeat' (first
  | with_reducible assumption
  | with_reducible apply Mem.Wf.write
  | with_reducible apply Mem.Wf.extend
  | with_reducible apply Mem.Wf.extends)) <;> done)

/-- Resolve memory reads over a chain of word stores from a well-formed base. -/
macro "mem_reads" : tactic => `(tactic| simp (disch := first | mem_wf | omega | rfl) only
  [Mem.read_snd_eq, Mem.extend_read_fst, Mem.read_write_word_of_wf, Mem.read_split64,
  Mem.read_write_word_disjoint, B256.toB256_toBytes])


end Blanc.Lift.Curve3Pool
