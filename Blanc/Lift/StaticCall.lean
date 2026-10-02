import Blanc.Lift.Quiet
import Blanc.Lift.ReturnDataBound
import Blanc.Lift.ExactWalk
import Blanc.Lift.Transfer
import Blanc.LadderBase

/-!
# `STATICCALL` to an arbitrary callee, one step at a time

The walk steps for `SHA-256` (`staticcall_sha_step`, `ri_staticcall_sha`) know their callee.
These know nothing about it: the callee's code is arbitrary, so a step is described by its
abstract outcome, as the port's inversion `of_run_staticcall_val_with_depth_cause` permits —
a flag word (`0` failed, `1` succeeded), the returned bytes `out` (written to the output window
and kept as the return data), and, for a success, the static child message that answered
(`StaticAnswered`).  Every storage map and the log list are unchanged either way (a static frame
cannot write them; `Ninst.world_of_quiet`).

* `ri_staticcall`: a successful step from `St b (g :: t :: ii :: is :: oi :: os :: S) M G`,
  inverted;
* `rx_staticcall`: the forward form over a caller-supplied `Ninst.RunCompiled` of the step (the
  callee's behaviour is a premise of any liveness statement that crosses the call), with the
  continuation receiving the same abstract outcome.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-- A successful static child message from the frame `sevm`, over the world of `b`, to `t` with
calldata `input`, returned `out`: the message the port's inversion exhibits (delegation
resolved against `b`'s code), processed without error. -/
def StaticAnswered (sevm : Sevm) (b : Devm) (t : Adr) (input out : Bytes) : Prop :=
  ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (na : Adr) (code : ByteArray) (gas : Nat),
    parent.state = b.state ∧
    ((getDelegatedCodeAddress (b.getCode t) = none ∧ na = t ∧ code = b.getCode t ∧
        dp = false) ∨
      (∃ d, getDelegatedCodeAddress (b.getCode t) = some d ∧ na = d ∧ code = b.getCode d ∧
        dp = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage (callMsg sevm parent gas 0 sevm.currentTarget t na true true input code dp)
      xl (.ok child) ∧
    child.error.isSome = false ∧ child.output = out

/-- What a successful `STATICCALL` step from `St b (… :: S) M G` leaves, whatever the callee: the
flag on top of `S`, the output window written with (a prefix of) `out`, `out` as the return data,
and every storage map and the log list of `b`. -/
structure StaticCallPost (b d : Devm) (S : List B256) (M : Mem) (ii is oi os flag : B256)
    (out : Bytes) : Prop where
  stack : d.stack = flag :: S
  memory : d.memory =
    (M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat (out.take os.toNat)
  returnData : d.returnData = out
  stor : ∀ a, Devm.getStor d a = Devm.getStor b a
  logs : d.logs = b.logs
  output : flag = 1 → d.output = b.output
  flag : flag = 0 ∨ flag = 1

theorem StaticCallPost.eq_St {b d : Devm} {S : List B256} {M : Mem} {ii is oi os flag : B256}
    {out : Bytes} (h : StaticCallPost b d S M ii is oi os flag out) :
    d = St d (flag :: S)
      ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat
        (out.take os.toNat)) d.gasLeft :=
  St.self h.stack h.memory

private theorem matches_map_some (S : List B256) : Matches (S.map some) S := by
  induction S with
  | nil => trivial
  | cons x S ih => exact ⟨Or.inr rfl, ih⟩

private theorem eq_of_matches_map_some {S rest : List B256} (h : Matches (S.map some) rest) :
    rest = S := by
  induction S generalizing rest with
  | nil => cases rest with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons y S ih =>
    cases rest with
    | nil => exact h.elim
    | cons z rest =>
      obtain ⟨hz, hr⟩ := h
      rcases hz with hz | hz
      · cases hz
      · cases hz; rw [ih hr]

/-- The successor's stack is exactly the flag over the rest (the transfer checker's
full-stack match). -/
private theorem staticcall_stack {sevm : Sevm} {pre d : Devm} {g t ii is oi os : B256}
    {S : List B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hs : pre.stack = g :: t :: ii :: is :: oi :: os :: S)
    (run : Ninst.Run sevm pre (.exec .staticcall) d) :
    ∃ flag, d.stack = flag :: S := by
  have hm : Matches ((none :: none :: none :: none :: none :: none :: S.map some) : Pattern)
      pre.stack := by
    rw [hs]
    exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
      matches_map_some S⟩
  have h := ninstTransfer_run hfork hm rfl run
  obtain ⟨x, rest, hd⟩ : ∃ x rest, d.stack = x :: rest := by
    cases e : d.stack with
    | nil => rw [e] at h; exact h.elim
    | cons x rest => exact ⟨x, rest, rfl⟩
  rw [hd] at h
  refine ⟨x, ?_⟩
  rw [hd]
  congr 1
  exact eq_of_matches_map_some h.2

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- **`STATICCALL` to an arbitrary callee, inverted.**  A successful step leaves a flag and a
returned byte string `out` (`StaticCallPost`); a set flag comes from a successful static child
message to `t` with the input window as calldata. -/
theorem ri_staticcall {g t ii is oi os : B256} {d : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall) d) :
    ∃ flag out, StaticCallPost b d S M ii is oi os flag out ∧
      (flag = 1 → StaticAnswered sevm b t.toAdr (M.read ii.toNat is.toNat).1 out) := by
  obtain ⟨flag, hstack⟩ := staticcall_stack hfork rfl h
  have hw := Ninst.world_of_quiet hfork rfl h
  have hp : (g :: t :: ii :: is :: oi :: os :: S) <<+
      (St b (g :: t :: ii :: is :: oi :: os :: S) M G).stack := by
    simpa only [List.append_nil, St.stack] using
      (pref_append (g :: t :: ii :: is :: oi :: os :: S) [])
  rcases of_run_staticcall_val_with_depth_cause hp h hfork with hfail | hsucc
  · obtain ⟨hpf, -, out, hret, hmem, -⟩ := hfail
    rw [hstack] at hpf
    have h0 : flag = 0 := (pref_head_unique hpf (pref_append [flag] S)).symm
    refine ⟨flag, out, ⟨hstack, hmem, hret, fun a => congrFun hw.1 a, hw.2,
      fun h1 => False.elim (by rw [h0] at h1; exact (by decide : (0 : B256) ≠ 1) h1), .inl h0⟩, ?_⟩
    intro h1
    rw [h0] at h1
    exact absurd h1 (by decide)
  · obtain ⟨parent, child, xl, dp, na, code, avail, -, hs, hstate, hpm, -, houtput, hdel, hfill, hproc,
      hclean, hresume, -, hret, hmem, hpst⟩ := hsucc
    have hS : parent.stack = S := by
      have := hs
      simp only [St.stack, List.cons.injEq] at this
      exact this.2.2.2.2.2.2.symm
    rw [hpst, hS] at hstack
    have h1 : flag = 1 := (List.cons.inj hstack).1.symm
    refine ⟨flag, child.output, ⟨by rw [← h1] at hstack; rw [hpst, hS, h1],
      by rw [hmem, hpm]; rfl,
      hret, fun a => congrFun hw.1 a, hw.2,
      fun _ => (Resume.call_output hresume).trans houtput, .inr h1⟩, fun _ => ?_⟩
    exact ⟨parent, child, xl, dp, na, code, _, hstate, hdel, hfill, hproc, hclean, rfl⟩

/-- The actual static-call producer bounds the full return data in the same outcome. -/
theorem ri_staticcall_bounded {g t ii is oi os : B256} {d : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall) d) :
    ∃ flag out, StaticCallPost b d S M ii is oi os flag out ∧
      out.length < 2^256 ∧
      (flag = 1 → StaticAnswered sevm b t.toAdr (M.read ii.toNat is.toNat).1 out) := by
  obtain ⟨flag, out, hpost, hans⟩ := ri_staticcall hfork h
  have bound := ReturnDataBound.staticcall_returnData_length_lt h hfork
  rw [hpost.returnData] at bound
  exact ⟨flag, out, hpost, bound, hans⟩

/-- **`STATICCALL` to an arbitrary callee, forward.**  Given the step itself (a premise about the
callee), the run continues from its outcome as `ri_staticcall` describes it. -/
theorem rx_staticcall {fs : List SFunc} {f : SFunc} {o : Outcome} {g t ii is oi os : B256}
    {d : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hcall : Ninst.RunCompiled sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G)
      (.exec .staticcall) d)
    (k : ∀ flag out, StaticCallPost b d S M ii is oi os flag out →
      (flag = 1 → StaticAnswered sevm b t.toAdr (M.read ii.toNat is.toNat).1 out) →
      SFunc.RunExact fs sevm (St d (flag :: S)
        ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat
          (out.take os.toNat)) d.gasLeft) f o) :
    SFunc.RunExact fs sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G)
      (.next (.exec .staticcall) f) o := by
  obtain ⟨xl, hf, hr⟩ := hcall
  obtain ⟨flag, out, hpost, hans⟩ := ri_staticcall hfork ⟨xl, hf, 0, hr 0⟩
  refine .next ⟨xl, hf, hr⟩ ?_
  rw [hpost.eq_St]
  exact k flag out hpost hans

end Blanc.Lift
