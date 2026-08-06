-- ForwardCall.lean : crossing a `CALL`, forward.
--
-- `Blanc/Forward.lean` builds `Ninst.RunCompiled` derivations for every
-- instruction whose step is childless.  A `CALL` is not one of those: its step
-- outcome is a `.spawn`, its premise is genuinely existential in the child slot
-- (`Ninst.RunCompiled`'s `∃ xl, xl.Filled`), and the successor state is what
-- `Resume.run` makes of whatever the child settled at.  That is the one thing
-- the forward layer could not do, and this module is it.
--
-- Three things carry the weight, and each is small on its own.
--
-- * **The child comes from totality, never from a premise.**  Jaune's `exec` is
--   total and fuel-free (`Jaune/Sufficiency.lean`), `Blanc/Semantics.lean`'s
--   `exec_iff_exec_eq` is bidirectional for a general `Execution`, and
--   `Xlot.filled_exec` fills the slot for *any* machine.  So the slot obligation
--   an external call carries -- the one a proof about arbitrary callee bytecode
--   would normally have to assume away -- is discharged here by a theorem, at
--   `exec cevm`, with no premise about the callee at all.  Nothing below says
--   the child succeeds, terminates quickly, or behaves; it says only that its
--   derivation exists, which is what the caller then case-splits on.
-- * **The resume is characterised, not unfolded at the call site.**
--   `Resume.run (.call parent oi os)` has exactly three outcomes, and each is
--   one lemma: the settle propagated an error, the child settled with an error
--   set, the child settled clean.  The middle one is where the parent *keeps its
--   own warm sets* -- `incorporateChildOnError` copies state, transient storage,
--   created accounts, return data and gas and nothing else -- which is what
--   makes a post-`CALL` worst case deterministic rather than callee-controlled.
-- * **`value = 0` collapses the `.call` arm.**  Blanc's callbacks forward no
--   value, and at `value = 0` the new-account charge, the transfer charge and
--   the stipend are all zero, the static-context assertion passes on its right
--   disjunct, and the balance short-circuit `senderBal < 0` is unreachable.
--   What is left is one `min` and one `except64th`, which is the whole EIP-150
--   content at this altitude.  The nonzero-value case is not stated: no Blanc
--   contract needs it, and an unused generalisation of a lemma this shape is a
--   maintenance surface, not a capability.
--
-- Nothing here is contract-specific and nothing here mentions a `Func`: this is
-- the `Ninst`/`Xinst` altitude, and the walk that consumes it lives in a
-- contract-owned module.
--
-- The import is `Blanc/Reverts.lean` rather than `Blanc/Forward.lean` so that a
-- caller building a `Func.RunCompiledTo` walk has both layers from one import;
-- `Reverts.lean` imports `Forward.lean`, so nothing is duplicated.

import Blanc.Reverts

namespace Blanc

open Jaune

/-! ## The spawn premise, discharged by totality

`Ninst.RunCompiled sevm devm (.exec x) devm'` unfolds to
`∃ xl, xl.Filled ∧ ∀ pc, Ninst.StepRun pc sevm devm (.exec x) xl (.ok devm')`.
For a childless instruction the slot is `.none` and `Filled` is `True`; for a
spawning one it is a real obligation, and these three lemmas are the three ways
to meet it. -/

/-- A spawning instruction whose frame **enters**: the slot is filled at
`exec cevm` by `Xlot.filled_exec`, and the successor is whatever `Resume.run`
makes of the settle.

This is the arc's crossing lemma.  Read the premises: `h_step` is about the
parent's own state, `h_enter` is about the message the parent built, and
`h_res` is about the resume.  **There is no premise about the child.**  Its
derivation is `exec cevm`, an opaque term the caller case-splits on. -/
lemma Ninst.runCompiled_exec_run {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} {cevm : Evm} {devm' : Devm}
    (h_step : Xinst.step sevm devm x = .spawn f rsm)
    (h_enter : f.enter = .run cevm)
    (h_res : rsm.run (f.settle (exec cevm)) = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec x) devm' := by
  refine ⟨.some ⟨cevm, exec cevm⟩, Xlot.filled_exec cevm, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨_, RunFrame.of_run h_enter, h_res.symm⟩

/-- A spawning instruction whose frame **does not enter** — the value transfer
failed, or the callee is a precompile.  No child machine exists, the slot is
`.none`, and `Filled` is `True`. -/
lemma Ninst.runCompiled_exec_doneFrame {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} {devm' : Devm}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h_step : Xinst.step sevm devm x = .spawn f rsm)
    (h_enter : f.enter = .done r) (h_res : rsm.run r = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec x) devm' := by
  refine ⟨.none, trivial, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨r, RunFrame.of_done h_enter, h_res.symm⟩

/-- A call-type instruction that never spawns at all: `Xinst.step` itself
returned `.done`.  The depth-1024 arm below is the case this exists for. -/
lemma Ninst.runCompiled_exec_done {sevm : Sevm} {devm : Devm} {x : Xinst}
    {devm' : Devm} (h_step : Xinst.step sevm devm x = .done (.ok devm')) :
    Ninst.RunCompiled sevm devm (.exec x) devm' := by
  refine ⟨.none, trivial, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨rfl, rfl⟩

/-- `Devm.popToAdr`, evaluated forward — the mirror of `Blanc/Forward.lean`'s
`Devm.popToNat_eq_ok`, needed because a `CALL`'s second operand is an address.
It lives here rather than there for **A4**'s reason: `Blanc/Forward.lean`'s
elaboration row is the one this arc may not raise. -/
lemma Devm.popToAdr_eq_ok {x : B256} {s : List B256} {devm : Devm}
    (h : devm.stack = x :: s) :
    devm.popToAdr =
      .ok ⟨x.toAdr, devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
  rw [Devm.popToAdr_def, Devm.pop_eq_ok h]
  rfl

/-! ## Reading storage without deciding warmth

`Blanc/Forward.lean` splits `SLOAD` into a cold rule and a warm rule, because
the cold one moves the base state (the key joins the accessed set) and the warm
one does not.  A walk that has to be *correct whichever way the frame came in*
therefore forks, and a trunk with two such reads forks four ways.

The rule below is the fork, taken once and packaged.  Its successor's base is a
**variable** pinned by an `if`, so one derivation covers both cases and the
consumer reads what it needs off `h_base` — which for a continuation is only
ever membership, `getStorVal`, and the machine fields the `setMach` names.
`h_cost` is the same `if`, so the charge is symbolic and the caller bounds it.

Contract-agnostic, and here rather than in `Blanc/Forward.lean` for **A4**'s
reason: that module's elaboration row is the one this arc may not raise. -/

/-- `SLOAD`, warmth left open.  The successor's base is whichever of the two
states the frame's own accessed set selects, and the charge is the matching
schedule constant; both are handed to the caller as equations.

Neither `if` is decided here, so nothing about the frame's accessed set is
assumed — which is what lets a single walk serve a statement with no warmth
premise. -/
lemma Ninst.runCompiled_sload_of {sevm : Sevm} {devm base : Devm} {k v : B256}
    {s : List B256} {c G : Nat} (h_stk : devm.stack = k :: s)
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base)
    (h_cost : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then gasWarmAccess else gasColdSload) = c)
    (h_val : devm.getStorVal sevm.currentTarget k = v)
    (h_gas : devm.gasLeft = G + c) (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg .sload)
      (base.setMach ⟨v :: s, devm.memory, G⟩) := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base h_cost
    subst h_base; subst h_cost
    exact Ninst.runCompiled_sload_warm h_stk h h_val h_gas h_room
  · rw [if_neg h] at h_base h_cost
    subst h_base; subst h_cost
    exact Ninst.runCompiled_sload_cold h_stk h h_val h_gas h_room

/-- The key an `SLOAD` read is warm afterwards, whichever arm was taken. -/
lemma mem_accessedStorageKeys_sload_of {sevm : Sevm} {devm base : Devm}
    {k : B256}
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base) :
    (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ base.accessedStorageKeys := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base; subst h_base; exact h
  · rw [if_neg h] at h_base; subst h_base
    exact Std.HashSet.mem_insert_self

/-- A key already warm stays warm across an unrelated `SLOAD`. -/
lemma mem_accessedStorageKeys_sload_of_mem {sevm : Sevm} {devm base : Devm}
    {k k' : B256} {a : Adr}
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base)
    (h_mem : (⟨a, k'⟩ : Adr × B256) ∈ devm.accessedStorageKeys) :
    (⟨a, k'⟩ : Adr × B256) ∈ base.accessedStorageKeys := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base; subst h_base; exact h_mem
  · rw [if_neg h] at h_base; subst h_base
    exact Std.HashSet.mem_insert.mpr (Or.inr h_mem)

/-- The storage a `SLOAD` reads is the storage it leaves: the accessed set is
`meta`, the values are `world`. -/
lemma getStorVal_sload_of {sevm : Sevm} {devm base : Devm} {k : B256}
    {a : Adr} {k' : B256}
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base) :
    base.getStorVal a k' = devm.getStorVal a k' := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base; subst h_base; rfl
  · rw [if_neg h] at h_base; subst h_base; rfl

/-- …and so is the original storage the `SSTORE` pricing compares against. -/
lemma refundCounter_sload_of {sevm : Sevm} {devm base : Devm} {k : B256}
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base) :
    base.refundCounter = devm.refundCounter := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base; subst h_base; rfl
  · rw [if_neg h] at h_base; subst h_base; rfl

/-- A read emits no log. -/
lemma logs_sload_of {sevm : Sevm} {devm base : Devm} {k : B256}
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base) :
    base.logs = devm.logs := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base; subst h_base; rfl
  · rw [if_neg h] at h_base; subst h_base; rfl

/-- The charge is between the two schedule constants, whichever arm fires. -/
lemma le_sload_cost_of {sevm : Sevm} {devm : Devm} {k : B256} {c : Nat}
    (h_cost : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then gasWarmAccess else gasColdSload) = c) :
    gasWarmAccess ≤ c ∧ c ≤ gasColdSload := by
  subst h_cost; split <;> exact ⟨by decide, by decide⟩

/-! ### The two storage steps, in continuation-passing form

`Ninst.runCompiled_sload_of` above and `Blanc/Forward.lean`'s
`Ninst.runCompiled_sstore_warm` both hand the caller a successor whose base and
whose charge are *terms*, and a walk that meets several of them accumulates
those terms into a state nobody can write down.  The two rules below are the
same steps stated so that the successor's base, its charge and its gas account
arrive in the continuation as **variables with equations** — everything a later
instruction needs to know about them, and nothing else.

That is what makes a trunk with two warmth-unknown reads and two stores a
*single* walk instead of a four-way fork over unwritable states, and it is why
a caller never has to name a `Devm` that a rule produced.

Neither is exhaustive about the charge: both bound it by the schedule's worst
case, which is **A3**'s decision — a premise buying exactness would be a premise
about the frame's history, and the statements this serves have none. -/

/-- `SLOAD` as a walk step, with warmth, charge and successor handed to the
continuation.  `h_gas` is the worst case, so no warmth premise is needed to know
the frame can pay. -/
lemma Func.runCompiledTo_sload_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k v : B256} {s : List B256} {M : Mem} {rest : Func} {ex : Execution}
    (h_stk : devm.stack = k :: s) (h_room : s.length < 1024)
    (h_val : devm.getStorVal sevm.currentTarget k = v)
    (h_mem : devm.memory = M)
    (h_gas : gasColdSload ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (c G : Nat),
      (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ base.accessedStorageKeys →
      (∀ p : Adr × B256, p ∈ devm.accessedStorageKeys →
        p ∈ base.accessedStorageKeys) →
      (∀ (a : Adr) (k' : B256), base.getStorVal a k' = devm.getStorVal a k') →
      base.refundCounter = devm.refundCounter →
      base.logs = devm.logs →
      gasWarmAccess ≤ c → c ≤ gasColdSload →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (base.setMach ⟨v :: s, M, G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next Ninst.sload rest) ex := by
  subst h_val; subst h_mem
  set base : Devm :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
    then devm else addAccessedStorageKey devm sevm.currentTarget k with h_base
  set c : Nat :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
    then gasWarmAccess else gasColdSload with h_c
  have h_lo : gasWarmAccess ≤ c := (le_sload_cost_of h_c.symm).1
  have h_hi : c ≤ gasColdSload := (le_sload_cost_of h_c.symm).2
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_sload_of (base := base) (c := c) (G := devm.gasLeft - c)
      h_stk h_base.symm h_c.symm rfl (by omega) h_room) ?_
  exact h_next base c (devm.gasLeft - c)
    (mem_accessedStorageKeys_sload_of h_base.symm)
    (fun _ hp => mem_accessedStorageKeys_sload_of_mem h_base.symm hp)
    (fun _ _ => getStorVal_sload_of h_base.symm)
    (refundCounter_sload_of h_base.symm) (logs_sload_of h_base.symm)
    h_lo h_hi (by omega)

/-- `SSTORE` on a **warm** key as a walk step.  The written value, the untouched
keys, the unmoved accessed set, the charge's bound and the gas account arrive in
the continuation; the base state itself never has to be named.

Warm only, deliberately: every store this serves is preceded by a read of the
same key in the same frame, so the cold arm is unreachable rather than
unhandled. -/
lemma Func.runCompiledTo_sstore_warm_step {fs : List Func} {sevm : Sevm}
    {devm : Devm} {k v : B256} {s : List B256} {M : Mem} {rest : Func}
    {ex : Execution}
    (h_stk : devm.stack = k :: v :: s)
    (h_warm : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys)
    (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_gas : gasStorageSet ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (c G : Nat),
      base.getStorVal sevm.currentTarget k = v →
      (∀ (a : Adr) (k' : B256), (a, k') ≠ (sevm.currentTarget, k) →
        base.getStorVal a k' = devm.getStorVal a k') →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.logs = devm.logs →
      c ≤ gasStorageSet →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (base.setMach ⟨s, M, G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next Ninst.sstore rest) ex := by
  subst h_mem
  have h_bound : sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v ≤ gasStorageSet := by
    rw [sstoreValueCost]; split_ifs <;> decide
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_sstore_warm (c := sstoreValueCost
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v)
      (G := devm.gasLeft - sstoreValueCost
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v)
      h_stk h_warm (by simp only [gCallStipend, gasStorageSet] at *; omega)
      h_static rfl rfl (by omega)) ?_
  refine h_next _ _ _ ?_ (fun a k' h_ne => ?_) rfl rfl h_bound (by omega)
  · show (Devm.getStor _ sevm.currentTarget).get k = v
    rw [setStorVal_getStor_self, Stor.get_set_self]
  · by_cases h_adr : sevm.currentTarget = a
    · subst h_adr
      have h_key : k ≠ k' := fun h => h_ne (by rw [h])
      show (Devm.getStor _ sevm.currentTarget).get k' = _
      rw [setStorVal_getStor_self, Stor.get_set_ne _ h_key]
      rfl
    · show (Devm.getStor _ a).get k' = _
      have h_off : Devm.getStor
          ((devm.withRefundCounter (sstoreNewRefundCounter v
            (getOrigStorVal sevm sevm.currentTarget k)
            (devm.getStorVal sevm.currentTarget k)
            devm.refundCounter)).setStorVal sevm.currentTarget k v) a
            = Devm.getStor devm a := by
        simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, Devm.withState,
          Devm.setWorld, State.setStorVal]
        simp only [Devm.state, State.get_set_ne _ h_adr]
        rfl
      rw [h_off]
      rfl

/-! ## The memory window, in the shapes a walk's obligations arrive in

`func_run` hands every memory-expansion charge straight back — the image is a
chain of writes the tactic has no arithmetic for.  The three lemmas below are
what a caller closes those obligations with: the size of an image after one
word-write, the extension charge as a function of that size, and the fact that
*reading* a window the image already covers leaves the image alone.

The last is what keeps a `LOG` from doubling the state: `Mem.read` returns
`⟨μ.data, memExtSize …⟩`, which is `μ` again exactly when the window fits, and
structure eta makes that an equation the walk can rewrite with rather than a new
image every reader has to carry. -/

/-- The size of an image after writing one word: unchanged when the window
already fits, and rounded up to the word above otherwise.

`Mem.write` matches on the payload being non-empty, and `B256.toBytes` is not a
literal, so this needs the same `rcases` that `Mem.size_write_word` does. -/
lemma Mem.size_write_word_at {N : Mem} {i : Nat} {w : B256} :
    (N.write i w.toBytes).size = if i + 32 ≤ N.size then N.size else ceil32 (i + 32) := by
  rcases hb : w.toBytes with _ | ⟨b, bs⟩
  · exact absurd (hb ▸ B256.length_toBytes w) (by simp)
  · have hlen : (b :: bs).length = 32 := hb ▸ B256.length_toBytes w
    simp only [Mem.write, hlen]
    split_ifs <;> rfl

/-- `Mem.size_write_word_at` for an arbitrary non-empty payload: the size after
a write is unchanged when the window already fits and rounds up otherwise. -/
lemma Mem.size_write_cons {N : Mem} {n : Nat} {x : UInt8} {xs : Bytes} :
    (N.write n (x :: xs)).size =
      if n + (x :: xs).length ≤ N.size then N.size
      else ceil32 (n + (x :: xs).length) := by
  simp only [Mem.write]
  split_ifs <;> rfl

/-- The extension charge for a window, as a function of the image's size alone.
Stated with the charge as a parameter, and applied with `exact` rather than
`rw`: a walk's window index arrives as `(k * 32 : B256).toNat` rather than a
literal, which unifies but does not *match*. -/
lemma Devm.extCost_of_size {devm : Devm} {S : List B256} {N : Mem} {G : Nat}
    {i sz n e : Nat} (h : N.size = n)
    (he : calculateMemoryGasCost (memExtSize n i sz)
      - calculateMemoryGasCost n = e) :
    (devm.setMach ⟨S, N, G⟩).extCost [⟨i, sz⟩] = e := by
  simp only [Devm.extCost, Devm.memory_setMach, memExtsSize, h, he]

/-- The same, summed with the instruction's fixed part — the shape every charge
premise outside `MSTORE` arrives in. -/
lemma Devm.extCost_add_of_size {devm : Devm} {S : List B256} {N : Mem} {G : Nat}
    {i sz n a e : Nat} (h : N.size = n)
    (he : a + (calculateMemoryGasCost (memExtSize n i sz)
      - calculateMemoryGasCost n) = e) :
    a + (devm.setMach ⟨S, N, G⟩).extCost [⟨i, sz⟩] = e := by
  simp only [Devm.extCost, Devm.memory_setMach, memExtsSize, h, he]

/-- Reading a window the image already covers returns the image unchanged. -/
lemma Mem.read_snd_eq_self {N : Mem} {i sz : Nat}
    (h : memExtSize N.size i sz = N.size) : (N.read i sz).2 = N := by
  show N.extend i sz = N
  simp only [Mem.extend, h]

/-- A window inside a word-aligned image extends nothing.  The alignment
premise is real: an access to an unaligned image is rounded up whether or not
the window is covered. -/
lemma memExtSize_of_le {n i sz : Nat} (h32 : n % 32 = 0) (hw : i + sz ≤ n) :
    memExtSize n i sz = n := by
  unfold memExtSize
  split_ifs with h
  · rfl
  · have h1 : ceilDiv (i + sz) 32 ≤ ceilDiv n 32 := by
      simp only [ceilDiv]
      rw [if_pos h32]
      split_ifs with h2 <;> omega
    rw [Nat.max_eq_left h1]
    simp only [ceilDiv]
    rw [if_pos h32]
    omega

/-- The window charge vanishes for a window a word-aligned image covers — the
symbolic-image sibling of `Devm.extCost_of_size`, for walks over a memory
*variable* whose size is only bounded, never computed. -/
lemma Devm.extCost_zero_of_le {devm : Devm} {S : List B256} {N : Mem} {G : Nat}
    {i sz : Nat} (h32 : N.size % 32 = 0) (hw : i + sz ≤ N.size) :
    (devm.setMach ⟨S, N, G⟩).extCost [⟨i, sz⟩] = 0 := by
  simp only [Devm.extCost, Devm.memory_setMach, memExtsSize,
    memExtSize_of_le h32 hw, Nat.sub_self]

/-- A write inside the image leaves the size alone. -/
lemma Mem.size_write_of_le {N : Mem} {n : Nat} {bs : Bytes}
    (h : n + bs.length ≤ N.size) : (N.write n bs).size = N.size := by
  rcases bs with _ | ⟨x, xs⟩
  · rfl
  · rw [Mem.size_write_cons,
      if_pos (by simp only [List.length_cons] at h ⊢; omega)]

/-- Reading a covered window of a word-aligned image leaves the size alone. -/
lemma Mem.size_read_snd_of_le {N : Mem} {i sz : Nat} (h32 : N.size % 32 = 0)
    (hw : i + sz ≤ N.size) : ((N.read i sz).2).size = N.size := by
  rw [Mem.read_snd_eq_self (memExtSize_of_le h32 hw)]

/-- `setMach` moves no return data. -/
lemma Devm.returnData_setMach {devm : Devm} {m : Mach} :
    (devm.setMach m).returnData = devm.returnData := rfl

/-- `RETURN`, at the outcome relation's altitude — the `.ok` sibling of
`Func.runCompiledTo_rev_of`, with the read-back reduced to its *first*
component exactly as `Func.runCompiled_ret_word` does and for the same
reason. -/
lemma Func.runCompiledTo_ret_word {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i sz : B256} {s : List B256} {out : Bytes} {G e : Nat}
    (h_stk : devm.stack = i :: sz :: s)
    (h_ext : devm.extCost [⟨i.toNat, sz.toNat⟩] = e)
    (h_gas : devm.gasLeft = G + e)
    (h_out : ((devm.setMach ⟨s, devm.memory, G⟩).memRead i.toNat sz.toNat).1
      = out) :
    Func.RunCompiledTo fs sevm devm (.last .ret)
      (.ok ((((devm.setMach ⟨s, devm.memory, G⟩).memRead i.toNat
        sz.toNat).2).withOutput out)) := by
  subst h_ext
  have h_eq : devm.gasLeft - devm.extCost [⟨i.toNat, sz.toNat⟩] = G := by omega
  refine Func.RunCompiledTo.last ?_
  show Linst.run sevm devm .ret = _
  exact Linst.run_ret_eq_ok h_stk (by omega) (by rw [h_eq]; exact Prod.ext h_out rfl)

/-! ## The two remaining walk steps: `LOG` and `CALLDATACOPY`

Both are in the continuation-passing form the storage steps established, and
each is here for its own reason.

`LOG` moves the *base* — `Devm.addLog` — and its successor's memory image is a
projection out of the state it reads.  Handed to the walk as a term, both would
be carried inside every later state (**F8** of `~/plans/reports/
adversarial-progress-step2.md`); handed to a continuation, the base is a
variable and the image is whatever the caller names.

`CALLDATACOPY`'s charge is affine in the copied length, and `func_run` requires
every charge hint to be a **numeral** (**F10**).  A trunk that forwards a
caller-supplied `bytes` payload therefore cannot walk its copy with the tactic
at all; it applies this between two `func_run` segments, with the charge a
variable and one equation. -/

/-- `MSTORE` as a walk step, with the written image handed to the continuation
as a **variable**.

`func_run` has an `MSTORE` arm and it is the right one for a view: two or three
stores over `Mem.empty` and the image stays small.  It is the wrong one for a
frame that lays out a call's arguments.  There the image is a chain of eight
writes whose payloads are *concrete* — a selector that is a `keccak`, an
address, a length word — so every `whnf` the walk performs on a later state runs
that chain, and the cost per instruction grows with the number of stores before
it (measured: ≈ 0.1 s per node before the layout, ≈ 1.5 s after it).

Naming each image instead keeps every state one write deep, and the caller ends
up with the chain as a list of equations, which is also the shape a memory-image
characterisation wants. -/
lemma Func.runCompiledTo_mstore_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i v : B256} {s : List B256} {c : Nat} {M : Mem} {rest : Func}
    {ex : Execution}
    (h_stk : devm.stack = i :: v :: s)
    (h_mem : devm.memory = M)
    (h_cost : gVerylow + devm.extCost [⟨i.toNat, 32⟩] = c)
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (M' : Mem) (G : Nat), M.write i.toNat v.toBytes = M' →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (devm.setMach ⟨s, M', G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next Ninst.mstore rest) ex := by
  subst h_mem
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of (G := devm.gasLeft - c) (e := devm.extCost
      [⟨i.toNat, 32⟩]) h_stk rfl (by omega) rfl) ?_
  exact h_next _ _ rfl (by omega)

/-- `LOG n` as a walk step.  The emitted entry, the untouched storage and
accessed set, and the gas account arrive in the continuation. -/
lemma Func.runCompiledTo_log_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {n : Fin 5} {i sz : B256} {topics s : List B256} {c : Nat} {M M' : Mem}
    {payload : Bytes} {rest : Func} {ex : Execution}
    (h_stk : devm.stack = i :: sz :: (topics ++ s))
    (h_len : topics.length = n.val) (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_cost : gLog + gLogdata * sz.toNat + gLogtopic * n.val
      + devm.extCost [⟨i.toNat, sz.toNat⟩] = c)
    (h_data : (M.read i.toNat sz.toNat).1 = payload)
    (h_img : (M.read i.toNat sz.toNat).2 = M')
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (G : Nat),
      base.logs = devm.logs ++ [⟨sevm.currentTarget, topics, payload⟩] →
      (∀ (a : Adr) (k : B256), base.getStorVal a k = devm.getStorVal a k) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (base.setMach ⟨s, M', G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next (.reg (.log n)) rest) ex := by
  subst h_mem
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_log_of (G := devm.gasLeft - c) h_stk h_len h_static
      h_cost h_data h_img (by omega)) ?_
  exact h_next _ _ rfl (fun _ _ => rfl) rfl (by omega)

/-- `CALLDATACOPY` as a walk step, with the charge a variable.  The copied bytes
are `Sevm.data`'s slice — zero-filled past the end of calldata, which is why no
premise bounds the requested window. -/
lemma Func.runCompiledTo_calldatacopy_step {fs : List Func} {sevm : Sevm}
    {devm : Devm} {di si sz : B256} {s : List B256} {c : Nat} {M : Mem}
    {rest : Func} {ex : Execution}
    (h_stk : devm.stack = di :: si :: sz :: s)
    (h_mem : devm.memory = M)
    (h_cost : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩] = c)
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (M' : Mem) (G : Nat),
      M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0) = M' →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (devm.setMach ⟨s, M', G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next (.reg .calldatacopy) rest) ex := by
  subst h_mem
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_calldatacopy_of (G := devm.gasLeft - c) h_stk h_cost
      rfl (by omega)) ?_
  exact h_next _ _ rfl (by omega)

/-! ## EIP-150, at `value = 0`

`calculateMsgCallGas` is where the 63/64 rule lives, and P4 of
`~/plans/adversarial-progress.md` settles that it is *frame-local*: the cap is
computed inside `Xinst.step`, and no transaction layer is touched.  At
`value = 0` the stipend vanishes and the pair collapses to one `min`. -/

/-- `calculateMsgCallGas` at `value = 0`, in the branch where the frame can
afford its own overhead.  The forwarded amount is `min` of what the operand
asked for and the 63/64 cap; the stipend is zero. -/
lemma calculateMsgCallGas_zero {gas gl ext acc : Nat} (h : acc + ext ≤ gl) :
    calculateMsgCallGas 0 gas gl ext acc =
      ⟨min gas (except64th (gl - ext - acc)) + acc,
        min gas (except64th (gl - ext - acc))⟩ := by
  rw [calculateMsgCallGas, if_pos (rfl : (0 : Nat) = 0), if_neg (by omega)]
  show (min gas (except64th (gl - ext - acc)) + acc,
    min gas (except64th (gl - ext - acc)) + 0) = _
  rw [Nat.add_zero]

/-- **The retained gas, bounded below.**  Whatever the operand asked for, the
frame keeps at least a sixty-fourth of what it had after its own overhead:
`except64th n = n - n / 64` leaves `n / 64` behind, and `min` can only leave
more.

This is what makes a post-`CALL` continuation provable against a *closed* bound
without any premise about the callee — the callee cannot take the last
sixty-fourth however it behaves. -/
lemma le_retained_of_calculateMsgCallGas_zero {gas gl ext acc mcc mcs : Nat}
    (h : acc + ext ≤ gl)
    (h_split : calculateMsgCallGas 0 gas gl ext acc = ⟨mcc, mcs⟩) :
    (gl - ext - acc) / 64 ≤ gl - (mcc + ext) := by
  rw [calculateMsgCallGas_zero h] at h_split
  injection h_split with h_cost _
  subst h_cost
  rw [show except64th (gl - ext - acc)
    = (gl - ext - acc) - (gl - ext - acc) / 64 from rfl]
  have h_div : (gl - ext - acc) / 64 ≤ gl - ext - acc := Nat.div_le_self _ _
  omega

/-- The `min` collapses when the operand asked for at least the cap — which is
what a frame that pushed its own `GAS` and forwarded it does, since the cap is
strictly below the account the push read. -/
lemma calculateMsgCallGas_zero_of_cap_le {gas gl ext acc : Nat}
    (h : acc + ext ≤ gl) (h_cap : except64th (gl - ext - acc) ≤ gas) :
    calculateMsgCallGas 0 gas gl ext acc =
      ⟨except64th (gl - ext - acc) + acc, except64th (gl - ext - acc)⟩ := by
  rw [calculateMsgCallGas_zero h, Nat.min_eq_right h_cap]

/-! ## `genericCall.step`

Two arms, and the depth test is the whole difference.  At `sevm.depth = 0` no
child is spawned at all: the frame pushes `0`, gets the forwarded gas back and
carries on — a *revert-path* case for a contract that checks the return value,
never a premise. -/

/-- The spawning arm: at nonzero depth, the message is built and the frame
suspends.  Nothing is evaluated here that the caller cannot read off the
conclusion. -/
lemma genericCall.step_spawn {sevm : Sevm} {devm : Devm} {gas : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_depth : sevm.depth ≠ 0) :
    genericCall.step sevm devm gas value caller target codeAddress stv isStatic
        ii is oi os code dp =
      .spawn
        (Frame.ofCall
          (callMsg sevm (devm.withReturnData []) gas value caller target
            codeAddress stv isStatic
            ((devm.withReturnData []).memory.data.sliceD ii is 0) code dp))
        (.call (devm.withReturnData []) oi os) := by
  rw [genericCall.step, if_neg h_depth]

/-- The depth-limit arm: `sevm.depth = 0` is Jaune's encoding of "no room for a
child", and the instruction answers `0` on the stack with the requested gas
handed straight back.

A contract that branches on the returned flag reverts here, which is why P2's
trichotomy needs this arm and not a premise excluding it. -/
lemma genericCall.step_zero_depth {sevm : Sevm} {devm : Devm} {gas : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_depth : sevm.depth = 0)
    (h_room : devm.stack.length < 1024) :
    genericCall.step sevm devm gas value caller target codeAddress stv isStatic
        ii is oi os code dp =
      .done (.ok ((devm.withReturnData []).setMach
        ⟨0 :: devm.stack, devm.memory, devm.gasLeft + gas⟩)) := by
  rw [genericCall.step, if_pos h_depth]
  show XStep.ofExcept
    (Devm.push 0
      (((devm.withReturnData []).withGasLeft
        ((devm.withReturnData []).gasLeft + gas))) >>= fun d =>
          Except.ok (XStep.done (.ok d))) = _
  rw [Devm.push_eq_ok
    (devm := (devm.withReturnData []).withGasLeft
      ((devm.withReturnData []).gasLeft + gas))
    (by show devm.stack.length < 1024; exact h_room)]
  rfl

/-! ## `Xinst.step`'s `.call` arm, at `value = 0`

Seven pops, one memory-expansion charge, one delegation resolution, the EIP-150
split, and then `genericCall.step`.  Every step of that is either arithmetic the
caller supplies as an equation or a projection of the popped state.

The two branches a nonzero value would open are *closed* here rather than
assumed away: the static-context assertion succeeds on `value = 0`, and the
balance short-circuit tests `senderBal < 0`, which no `B256` satisfies. -/

/-- The `.call` arm reduced to a `genericCall.step`, at `value = 0`.

The premises name what the arm computes and this layer does not: the
memory-expansion charge (`h_ext`), the delegation resolution (`h_del` — EIP-7702
can add a second cold-account charge, and `dgc` is it), the collected access
cost (`h_acc`), and the EIP-150 split (`h_split`).  `h_afford` is the branch
condition of `calculateMsgCallGas`, and `h_gas` is the frame's own ability to
pay. -/
lemma Xinst.step_call_zero_value {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) :
    Xinst.step sevm devm .call =
      genericCall.step sevm
        ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
          [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
        mcs 0 sevm.currentTarget cw.toAdr cw.toAdr true false
        iiw.toNat isw.toNat oiw.toNat osw.toNat code dp := by
  subst h_ext; subst h_acc
  show XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨callee, d⟩ ← d.popToAdr
    let ⟨value, d⟩ ← d.pop
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost callee d.accessedAddresses
    let d := addAccessedAddress d callee
    let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d callee
    let accessCost := preAccessCost + delegatedAccessGasCost
    let createCost :=
      if (¬ (d.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount
    let transferCost := if value = 0 then 0 else gasCallValue
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas value.toNat gas.toNat d.gasLeft extendCost
        (accessCost + createCost + transferCost)
    let d ← chargeGas (msgCallCost + extendCost) d
    Except.assert (!sevm.isStatic ∨ value = 0)
      ⟨.halt (.writeInStaticContext .none), d⟩
    let d := d.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let senderBal := (d.getAcct sevm.currentTarget).bal
    if senderBal < value then
      let d ← d.push 0
      return .done
        (.ok ((d.withReturnData []).withGasLeft (d.gasLeft + msgCallStipend)))
    else
      return genericCall.step
        sevm d msgCallStipend value sevm.currentTarget callee callee
        true false inputIndex inputSize outputIndex outputSize
        code disablePrecompiles) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach ⟨cw :: 0 :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach ⟨0 :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  -- `value = 0` closes the new-account and transfer charges, and the
  -- static-context assertion, on their right disjuncts.  `simp only` rather
  -- than `rw` for `h_del`: the new-account `if` carries a `Decidable` instance
  -- that depends on the term being rewritten.
  simp only [if_pos (Or.inr trivial), if_pos trivial, Nat.add_zero,
    show ((0 : B256).toNat) = 0 from rfl]
  simp only [h_del, h_split]
  rw [chargeGas_eq_ok (devm := d1) h_gas]
  simp only [Except.assert, if_pos (Or.inr trivial)]
  -- The balance short-circuit tests `senderBal < 0`, which no `B256` satisfies:
  -- at `value = 0` the branch is unreachable rather than excluded by a premise.
  rw [if_neg (by
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _))]
  rfl

/-! ### The spawned frame, named

Step 2 of the arc has to state what the child starts from, and Step 4's success
form has to *quantify over it by name* rather than existentially (**A5**: an
∃-form boundary premise cannot compose forward, which the `fmint-restoration`
R4 finding established).  These two definitions are where that name comes from:
they are the spawn's two components, written as functions of the parent's own
state, so a statement about the callee is a statement about a term the caller
can build. -/

/-- The parent state a `value = 0` `CALL` suspends on: charged, window-extended
and with its return data cleared. -/
def callSpawnParent (d1 : Devm) (charge ii is oi os : Nat) : Devm :=
  ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - charge⟩).memExtends
    [⟨ii, is⟩, ⟨oi, os⟩]).withReturnData []

/-- The message a `value = 0` `CALL` builds: the callee is both target and
code address, the value is zero, and the calldata is the input window read out
of the parent's own memory. -/
def callSpawnMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (callee : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) : Msg :=
  callMsg sevm p mcs 0 sevm.currentTarget callee callee true false
    (p.memory.data.sliceD ii is 0) code dp

/-- The `.call` arm all the way to its `.spawn`, at `value = 0` and nonzero
depth. -/
lemma Xinst.step_call_zero_value_spawn {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0) :
    Xinst.step sevm devm .call =
      .spawn
        (Frame.ofCall (callSpawnMsg sevm
          (callSpawnParent d1 (mcc + ext)
            iiw.toNat isw.toNat oiw.toNat osw.toNat)
          mcs cw.toAdr iiw.toNat isw.toNat code dp))
        (.call (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat) := by
  rw [Xinst.step_call_zero_value h_stk h_ext h_del h_acc h_split h_gas,
    genericCall.step_spawn h_depth]
  rfl

/-- **The crossing, assembled.**

A `value = 0` `CALL` whose frame enters, as one `Ninst.RunCompiled` premise: the
parent's arithmetic on the left, `Resume.run` on the right, and in between the
child's derivation supplied by `Xlot.filled_exec` at `exec cevm`.

Count the premises about the callee: there are none.  `h_enter` is about the
message the *parent* built and `h_res` is about the resume — and the term
`exec cevm` that stands where a behavioural assumption would go is exactly what
a caller case-splits on to get a trichotomy rather than a hypothesis. -/
lemma Ninst.runCompiled_call_zero_value {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {cevm : Evm} {devm' : Devm}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0)
    (h_enter : (Frame.ofCall (callSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs cw.toAdr iiw.toNat isw.toNat code dp)).enter = .run cevm)
    (h_res : Resume.run
      (.call (callSpawnParent d1 (mcc + ext)
        iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat)
      ((Frame.ofCall (callSpawnMsg sevm
        (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat)
        mcs cw.toAdr iiw.toNat isw.toNat code dp)).settle (exec cevm))
        = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec .call) devm' :=
  Ninst.runCompiled_exec_run
    (Xinst.step_call_zero_value_spawn h_stk h_ext h_del h_acc h_split h_gas
      h_depth) h_enter h_res

/-! ## The resume, characterised

`Resume.run (.call parent oi os) r` is where the parent comes back.  Three
lemmas, one per outcome, and between them they are the whole post-`CALL` state.

What each says about the parent is the part worth reading twice.

* On a **fatal settle** (`.crypto`/`.internal`, the channel
  `executeCode.handleError` propagates rather than settles) the resume does not
  run at all: the error travels straight out, carrying the child's state.
* On a **settled child with an error** the parent keeps its **own** accessed
  addresses and storage keys, its own logs, its own refund counter and its own
  accounts-to-delete.  `incorporateChildOnError` copies gas, created accounts,
  return data, state and transient storage — and nothing else.  So a post-`CALL`
  worst case is fixed by the frame's own trunk, not by the callee.
* On a **clean child** the sets union, so warm stays warm.

None of the three is conditional on the callee doing anything. -/

/-- The fatal arm: the settle propagated a non-consensus error, so
`liftToExecution` re-raises it against the parent's world. -/
lemma Resume.run_call_fatal {parent : Devm} {oi os : Nat}
    {e : EvmError} {st : State} {ca : AdrSet} {tra : Tra} :
    Resume.run (.call parent oi os) (.error ⟨e, st, ca, tra⟩) =
      .error ⟨e, (parent.withCreatedAccounts ca).setWorld
        {parent.world with state := st, transientStorage := tra}⟩ := rfl

/-- The settled-with-error arm.  `h_err` is read off the child; `h_room` is the
parent's own headroom, which its trunk established. -/
lemma Resume.run_call_err {parent child : Devm} {oi os : Nat}
    (h_err : child.error.isSome = true)
    (h_room : parent.stack.length < 1024) :
    Resume.run (.call parent oi os) (.ok child) =
      .ok (((incorporateChildOnError parent child child.output).setMach
        ⟨0 :: parent.stack, parent.memory,
          parent.gasLeft + child.gasLeft⟩).memWrite oi
            (child.output.take os)) := by
  show (do
    let c ← liftToExecution parent (.ok child)
    let actualOutput := c.output.take os
    if c.error.isSome then
      let evm2 ← (incorporateChildOnError parent c c.output).push 0
      Except.ok (evm2.memWrite oi actualOutput)
    else
      let evm2 ← (incorporateChildOnSuccess parent c c.output).push 1
      Except.ok (evm2.memWrite oi actualOutput)) = _
  show (if child.error.isSome then
      (incorporateChildOnError parent child child.output).push 0 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))
    else
      (incorporateChildOnSuccess parent child child.output).push 1 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))) = _
  rw [if_pos h_err, Devm.push_eq_ok
    (devm := incorporateChildOnError parent child child.output)
    (by show parent.stack.length < 1024; exact h_room)]
  rfl

/-- The clean arm.  The pushed flag is `1`, and
`incorporateChildOnSuccess` unions the warm sets, the logs, the refund counter
and the accounts to delete. -/
lemma Resume.run_call_ok {parent child : Devm} {oi os : Nat}
    (h_ok : child.error.isSome = false)
    (h_room : parent.stack.length < 1024) :
    Resume.run (.call parent oi os) (.ok child) =
      .ok (((incorporateChildOnSuccess parent child child.output).setMach
        ⟨1 :: parent.stack, parent.memory,
          parent.gasLeft + child.gasLeft⟩).memWrite oi
            (child.output.take os)) := by
  show (do
    let c ← liftToExecution parent (.ok child)
    let actualOutput := c.output.take os
    if c.error.isSome then
      let evm2 ← (incorporateChildOnError parent c c.output).push 0
      Except.ok (evm2.memWrite oi actualOutput)
    else
      let evm2 ← (incorporateChildOnSuccess parent c c.output).push 1
      Except.ok (evm2.memWrite oi actualOutput)) = _
  show (if child.error.isSome then
      (incorporateChildOnError parent child child.output).push 0 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))
    else
      (incorporateChildOnSuccess parent child child.output).push 1 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))) = _
  rw [if_neg (by rw [h_ok]; exact Bool.false_ne_true), Devm.push_eq_ok
    (devm := incorporateChildOnSuccess parent child child.output)
    (by show parent.stack.length < 1024; exact h_room)]
  rfl

/-! ### Reading the resume state

The projections a continuation walk needs, so that it never has to unfold
`incorporateChild*` again. -/

/-- An empty return window writes nothing: `Mem.write` at an empty payload is
the identity, which is why fmint's `(0,0)` window costs the resume nothing. -/
lemma Devm.memWrite_nil {devm : Devm} {i : Nat} : devm.memWrite i [] = devm := rfl

/-- On the error path the parent's accessed storage keys are its own. -/
lemma incorporateChildOnError_accessedStorageKeys {parent child : Devm}
    {rd : Bytes} :
    (incorporateChildOnError parent child rd).accessedStorageKeys
      = parent.accessedStorageKeys := rfl

/-- And its accessed addresses. -/
lemma incorporateChildOnError_accessedAddresses {parent child : Devm}
    {rd : Bytes} :
    (incorporateChildOnError parent child rd).accessedAddresses
      = parent.accessedAddresses := rfl

/-- And its logs: a reverted child emits none the parent keeps. -/
lemma incorporateChildOnError_logs {parent child : Devm} {rd : Bytes} :
    (incorporateChildOnError parent child rd).logs = parent.logs := rfl

/-- The return data is the child's output on either path, which is what
`RETURNDATASIZE` then reads. -/
lemma incorporateChildOnError_returnData {parent child : Devm} {rd : Bytes} :
    (incorporateChildOnError parent child rd).returnData = rd := rfl

lemma incorporateChildOnSuccess_returnData {parent child : Devm} {rd : Bytes} :
    (incorporateChildOnSuccess parent child rd).returnData = rd := rfl

/-- On the success path the accessed sets union, so a key the parent warmed
stays warm across the call. -/
lemma incorporateChildOnSuccess_accessedStorageKeys {parent child : Devm}
    {rd : Bytes} :
    (incorporateChildOnSuccess parent child rd).accessedStorageKeys
      = parent.accessedStorageKeys.union child.accessedStorageKeys := rfl

/-! ## The non-consensus channel

`SettledHalt` is the storable half of `EvmError`: a frame settlement records an
exceptional halt or a revert, and a cryptographic or internal failure is
deliberately unrepresentable there, so it can only propagate on the error
channel.  `NonConsensus` names exactly that unrepresentability, which is what a
settlement trichotomy quarantines its third disjunct with. -/

/-- An error no settlement can store: it is outside `SettledHalt.toEvmError`'s
image, so it travels the error channel and never reads as a settled halt. -/
def NonConsensus (e : EvmError) : Prop := ∀ sh : SettledHalt, sh.toEvmError ≠ e

/-- A cryptographic failure is non-consensus. -/
lemma nonConsensus_crypto {r : CryptoError} : NonConsensus (.crypto r) := by
  intro sh; cases sh <;> simp [SettledHalt.toEvmError]

/-- An internal fault is non-consensus. -/
lemma nonConsensus_internal {r : InternalError} : NonConsensus (.internal r) := by
  intro sh; cases sh <;> simp [SettledHalt.toEvmError]

/-- The only errors `executeCode.handleError` re-raises are the two
non-consensus channels: a halt or a revert is *stored* and comes back `.ok`. -/
lemma handleError_error_inv {raw : Execution}
    {p : EvmError × State × AdrSet × Tra}
    (h : executeCode.handleError raw = .error p) : NonConsensus p.1 := by
  rcases raw with ⟨e, d⟩ | d
  · rcases e with r | _ | r | r <;>
      simp only [executeCode.handleError] at h
    · cases h
    · cases h
    · cases h; exact nonConsensus_crypto
    · cases h; exact nonConsensus_internal
  · cases h

/-- A call frame's settlement passes an error through untouched: the settle
step only inspects `.ok` results. -/
lemma Frame.settle_error_inv {f : Frame} {raw : Execution}
    {p : EvmError × State × AdrSet × Tra}
    (h_call : f.isCreate = false) (h : f.settle raw = .error p) :
    executeCode.handleError raw = .error p := by
  unfold Frame.settle Frame.settleMsg at h
  rw [h_call] at h
  simp only [Bool.false_eq_true, if_false] at h
  rcases hh : executeCode.handleError raw with q | evm <;> rw [hh] at h
  · simpa [processMessage.settle] using h
  · unfold processMessage.settle at h
    simp only [bind, Except.bind] at h
    split at h <;> cases h

/-- A value transfer can only fail on the non-consensus channel: the one error
`Msg.benvAfterTransfer` raises is an internal assertion. -/
lemma Msg.benvAfterTransfer_error_inv {msg : Msg}
    {p : EvmError × State × AdrSet × Tra}
    (h : msg.benvAfterTransfer = .error p) : NonConsensus p.1 := by
  unfold Msg.benvAfterTransfer at h
  split at h
  · rcases hs : (msg.benv.subBal msg.caller msg.value) with _ | benv <;>
      simp only [hs, Option.toExcept, bind, Except.bind] at h
    · cases h; exact nonConsensus_internal
    · cases h
  · cases h

/-- A call frame that resolves without entering — a precompile, or a failed
transfer — can only carry a non-consensus error in its `.done`. -/
lemma Frame.enter_done_error_inv {f : Frame}
    {p : EvmError × State × AdrSet × Tra}
    (h_call : f.isCreate = false) (h : f.enter = .done (.error p)) :
    NonConsensus p.1 := by
  unfold Frame.enter at h
  rcases hb : f.inner.benvAfterTransfer with e | benv <;> simp only [hb] at h
  · injection h with h_eq
    have h_pass : f.settleMsg (.error e) = .error e := by
      unfold Frame.settleMsg
      rw [h_call]
      simp [processMessage.settle]
    rw [h_pass] at h_eq
    cases h_eq
    exact Msg.benvAfterTransfer_error_inv hb
  · rcases he : executeCode.enter (f.inner.withBenv benv) with evm | raw <;>
      simp only [he] at h
    · cases h
    · injection h with h_eq
      exact handleError_error_inv (Frame.settle_error_inv h_call h_eq)

/-! ## `Func.ExecTo` — a walk, transported to derivation evidence

`Func.RunCompiledTo` cannot say "the frame dies *at* this instruction": its
`.next` rule requires the instruction to succeed, and only a `.last` carries an
arbitrary outcome.  A `CALL` whose child settles on the non-consensus channel
is exactly that — a `.next` node whose step outcome is an error — so the
composition of a trichotomy has to happen one level down, at the `Exec`
derivation the bridge produces.

`Func.ExecTo` is that level, packaged so the walk machinery still applies: it
is the *statement* of `Func.exec_of_runCompiledTo_core` abstracted over the
walk — at every pc where this `Func`'s code sits, the execution from this state
settles at `ex`.  It is a `Prop`-valued definition, not a new inductive: no new
relation is built, and a complete `Func.RunCompiledTo` derivation embeds by one
application of the landed core.

The four structural rules below are positional mirrors of
`Func.RunCompiledTo`'s wrappers, which is what lets `func_run` build this
too (`Forward.execSpec`).  On top of them sit the two things only this level
can say: a `.next` node whose instruction *fails* (`Func.execTo_next_error`),
and the top-level bridge to the total `exec` (`Prog.exec_of_execTo`). -/

/-- At every pc where `p`'s compiled code sits, execution from `devm` settles
at `ex`.  The quantified `f₀ :: fs'` split and the compile equation are the
core bridge's own premises, threaded so the internal `.call` rule can resolve
table entries. -/
def Func.ExecTo (fs : List Func) (sevm : Sevm) (devm : Devm) (p : Func)
    (ex : Execution) : Prop :=
  ∀ (f₀ : Func) (fs' : List Func), fs = f₀ :: fs' →
    some sevm.code.toList = Prog.compile ⟨f₀, fs'⟩ →
    ∀ pc,
      subcode sevm.code.toList pc (Func.compile (table 0 (f₀ :: fs')) pc p) →
      noPushBefore sevm.code pc 32 = true →
      Nonempty (Exec pc sevm devm ex)

/-- A complete walk is `ExecTo` evidence: one application of the landed core. -/
lemma Func.ExecTo.of_runCompiledTo {fs : List Func} {sevm : Sevm} {devm : Devm}
    {p : Func} {ex : Execution} (h : Func.RunCompiledTo fs sevm devm p ex) :
    Func.ExecTo fs sevm devm p ex :=
  fun _ _ hFS h_eq pc sub hb => Func.exec_of_runCompiledTo_core h h_eq hFS pc sub hb

/-- The `.next` rule: one successful instruction, then the tail's evidence.
Positional mirror of `Func.RunCompiledTo.next`. -/
lemma Func.execTo_next {fs : List Func} {sevm : Sevm} {devm : Devm} {i : Ninst}
    {devm' : Devm} {f : Func} {ex : Execution}
    (h_n : Ninst.RunCompiled sevm devm i devm')
    (h_f : Func.ExecTo fs sevm devm' f ex) :
    Func.ExecTo fs sevm devm (.next i f) ex := by
  intro f₀ fs' hFS h_eq pc sub hb
  rcases Func.noPushBefore_next sub hb with ⟨hb', sub'⟩
  rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
  rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩
  simp [pure] at h_rw
  rw [← h_rw] at h_slice
  rcases h_n with ⟨xl, h_filled, h_step⟩
  exact Ninst.exec_of_stepRun (Ninst.at_of_slice (List.slice_prefix h_slice))
    h_filled (h_step pc) (h_f f₀ fs' hFS h_eq _ sub' hb')

/-- The fall-through arm of a `branch`.  Positional mirror of
`Func.runCompiledTo_branch_zero`. -/
lemma Func.execTo_branch_zero {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {ex : Execution} {s : List B256} {G : Nat}
    (h_stk : devm.stack = 0 :: s) (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh))
    (h_arm : Func.ExecTo fs sevm (devm.setMach ⟨s, devm.memory, G⟩) f ex) :
    Func.ExecTo fs sevm devm (.branch f g) ex := by
  intro f₀ fs' hFS h_eq pc sub hb
  rcases subcode_compile_branch_jumpable sub hb with
    ⟨loc, h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp, h_jd, h_jp, h_subq, h_bq⟩
  rcases Evm.branch_zero_steps h_push h_jumpi h_loc h_room
    (Devm.popBurnBy_setMach h_stk h_gas) with ⟨h1, h2⟩
  obtain ⟨excf⟩ := h_arm f₀ fs' hFS h_eq (pc + 4) h_subp h_bp
  exact ⟨Exec.cont h1 (Exec.cont h2 excf)⟩

/-- The jumped arm of a `branch`.  Positional mirror of
`Func.runCompiledTo_branch_succ`. -/
lemma Func.execTo_branch_succ {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {ex : Execution} {w : B256} {s : List B256} {G : Nat}
    (h_ne : w ≠ 0) (h_stk : devm.stack = w :: s)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh + gJumpdest))
    (h_arm : Func.ExecTo fs sevm (devm.setMach ⟨s, devm.memory, G⟩) g ex) :
    Func.ExecTo fs sevm devm (.branch f g) ex := by
  intro f₀ fs' hFS h_eq pc sub hb
  rcases subcode_compile_branch_jumpable sub hb with
    ⟨loc, h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp, h_jd, h_jp, h_subq, h_bq⟩
  rcases Evm.branch_succ_steps h_push h_jumpi h_jd h_jp h_loc h_ne h_room
    (Devm.popBurnBy_setMach h_stk h_gas) with ⟨h1, h2, h3⟩
  obtain ⟨excg⟩ := h_arm f₀ fs' hFS h_eq (loc + 1) h_subq h_bq
  exact ⟨Exec.cont h1 (Exec.cont h2 (Exec.cont h3 excg))⟩

/-- An internal `.call` into the flat table.  Positional mirror of
`Func.runCompiledTo_call'`. -/
lemma Func.execTo_call' {fs : List Func} {sevm : Sevm} {devm : Devm} {k : Nat}
    {f : Func} {ex : Execution} {G : Nat} (h_get : fs[k]? = some f)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gMid + gJumpdest))
    (h_body : Func.ExecTo fs sevm
      (devm.setMach ⟨devm.stack, devm.memory, G⟩) f ex) :
    Func.ExecTo fs sevm devm (.call k) ex := by
  intro f₀ fs' hFS h_eq pc sub hb
  subst hFS
  rcases subcode_compile_call sub with ⟨loc, p₁, h_get_tab, h_loc, h_pushAt, h_jump⟩
  have h_pf := (Prog.get?_table (m := 0)).symm.trans
    (congrArg (Prod.snd <$> ·) h_get_tab)
  rw [h_get] at h_pf
  simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at h_pf
  subst h_pf
  rcases subcode_of_get?_eq_some h_eq h_get_tab with ⟨h_jd, h_subf⟩
  have h_jpb := Prog.jumpable_of_get?_table h_eq h_get_tab
  rcases h_pushAt with ⟨le, h_push⟩
  rcases Evm.call_steps (le := le) h_push h_jump h_jd h_jpb.1 h_loc h_room
    (Devm.burnBy_setMach_gas h_gas) with ⟨h1, h2, h3⟩
  obtain ⟨excf⟩ := h_body f₀ fs' rfl h_eq (loc + 1) h_subf h_jpb.2
  exact ⟨Exec.cont h1 (Exec.cont h2 (Exec.cont h3 excf))⟩

/-- The error sibling of `Ninst.exec_of_stepRun`: an instruction whose step
outcome is an error ends the derivation right there, whichever of the three
step shapes produced it. -/
lemma Ninst.exec_of_stepRun_error {pc : Nat} {sevm : Sevm} {devm : Devm}
    {n : Ninst} {xl : Xlot} {e : EvmError × Devm}
    (h_at : Ninst.At sevm.code pc n)
    (h_filled : xl.Filled)
    (h_step : Ninst.StepRun pc sevm devm n xl (.error e)) :
    Nonempty (Exec pc sevm devm (.error e)) := by
  have hstep : Evm.step ⟨pc, sevm, devm⟩ = Ninst.step ⟨pc, sevm, devm⟩ n :=
    Evm.step_next h_at
  cases n with
  | reg r =>
    rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_step
    refine ⟨Exec.halt ?_⟩
    rw [hstep, Ninst.step_reg, ← h_step.2]
    rfl
  | push xs le =>
    rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_step
    refine ⟨Exec.halt ?_⟩
    rw [hstep, Ninst.step_push, ← h_step.2]
    rfl
  | exec x =>
    rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at h_step
    cases hx : Xinst.step sevm devm x with
    | done ex' =>
      rw [hx] at h_step
      simp only [XStep.Run] at h_step
      refine ⟨Exec.halt ?_⟩
      rw [hstep, Ninst.step_exec, hx, ← h_step.2]
      rfl
    | spawn fr rsm =>
      rw [hx] at h_step
      rcases h_step with ⟨r, hframe, hex⟩
      have hstep' : Evm.step ⟨pc, sevm, devm⟩ = .spawn fr rsm (pc + 1) := by
        rw [hstep, Ninst.step_exec, hx]
        rfl
      unfold RunFrame at hframe
      rcases henter : fr.enter with r' | cevm <;> simp only [henter] at hframe
      · exact ⟨Exec.doneErr hstep' henter (hframe.2 ▸ hex.symm)⟩
      · rcases hframe with ⟨raw, hxl, hr⟩
        subst hxl
        obtain ⟨excChild⟩ : Nonempty (Exec cevm.pc cevm.sta cevm.dyna raw) :=
          h_filled
        refine ⟨Exec.runErr hstep' henter excChild ?_⟩
        rw [← hr]
        exact hex.symm

/-- The terminal only this level has: a `.next` node whose instruction fails.
The whole frame settles at that error, whatever the rest of the `Func` was. -/
lemma Func.execTo_next_error {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i : Ninst} {rest : Func} {e : EvmError × Devm}
    (h : ∃ xl : Xlot, xl.Filled ∧
      ∀ pc, Ninst.StepRun pc sevm devm i xl (.error e)) :
    Func.ExecTo fs sevm devm (.next i rest) (.error e) := by
  intro f₀ fs' hFS h_eq pc sub hb
  rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
  rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩
  simp [pure] at h_rw
  rw [← h_rw] at h_slice
  rcases h with ⟨xl, h_filled, h_step⟩
  exact Ninst.exec_of_stepRun_error
    (Ninst.at_of_slice (List.slice_prefix h_slice)) h_filled (h_step pc)

/-- A spawning instruction whose entered child's settle propagates a fatal
error, as the step evidence `Func.execTo_next_error` consumes.  The mirror of
`Ninst.runCompiled_exec_run`, one constructor over: same premises, error side.
**There is still no premise about the child** — its derivation is
`exec cevm`. -/
lemma Ninst.stepRun_exec_run_error {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} {cevm : Evm} {e : EvmError × Devm}
    (h_step : Xinst.step sevm devm x = .spawn f rsm)
    (h_enter : f.enter = .run cevm)
    (h_res : rsm.run (f.settle (exec cevm)) = .error e) :
    ∃ xl : Xlot, xl.Filled ∧
      ∀ pc, Ninst.StepRun pc sevm devm (.exec x) xl (.error e) := by
  refine ⟨.some ⟨cevm, exec cevm⟩, Xlot.filled_exec cevm, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨_, RunFrame.of_run h_enter, h_res.symm⟩

/-- The same for a frame that resolves without entering: no child exists, and
the resume of its `.done` result propagates the error. -/
lemma Ninst.stepRun_exec_doneFrame_error {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} {e : EvmError × Devm}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h_step : Xinst.step sevm devm x = .spawn f rsm)
    (h_enter : f.enter = .done r) (h_res : rsm.run r = .error e) :
    ∃ xl : Xlot, xl.Filled ∧
      ∀ pc, Ninst.StepRun pc sevm devm (.exec x) xl (.error e) := by
  refine ⟨.none, trivial, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨r, RunFrame.of_done h_enter, h_res.symm⟩

/-- The program altitude: entry `JUMPDEST`, then the main `Func`'s evidence. -/
def Prog.ExecTo (sevm : Sevm) (devm : Devm) (p : Prog) (ex : Execution) : Prop :=
  ∃ mid, Devm.BurnBy gJumpdest devm mid ∧
    Func.ExecTo (p.main :: p.aux) sevm mid p.main ex

/-- **The bridge.**  `ExecTo` evidence at a compiled program *is* the total
`exec`'s value at pc 0 — the mirror of `Prog.exec_of_runCompiledTo`, consumed
by statements whose outcome cannot stay inside `Func.RunCompiledTo` because a
spawning instruction may fail. -/
theorem Prog.exec_of_execTo {sevm : Sevm} {pre : Devm} {p : Prog}
    {ex : Execution}
    (h : Prog.ExecTo sevm pre p ex)
    (h_eq : some sevm.code.toList = p.compile) :
    exec ⟨0, sevm, pre⟩ = ex := by
  rcases h with ⟨mid, h_burn, h_run⟩
  have h_eq' : some sevm.code.toList = Prog.compile ⟨p.main, p.aux⟩ := h_eq
  have h_get : (table 0 (p.main :: p.aux))[0]? = some (0, p.main) := rfl
  rcases subcode_of_get?_eq_some h_eq' h_get with ⟨h_jd, h_sub⟩
  have h_npb : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table h_eq' h_get).2
  have h1 : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont h_jd h_burn
  obtain ⟨exc⟩ := h_run p.main p.aux rfl h_eq' 1 h_sub h_npb
  rw [← exec_iff_exec_eq]
  exact ⟨Exec.cont h1 exc⟩

/-! ## `ExecSat` — the same evidence, existential in the outcome

A statement like a settlement trichotomy does not know its outcome up front:
which disjunct holds is decided by a case analysis *inside* the walk, on facts
about states the walk itself introduces.  A relation whose outcome is a fixed
parameter cannot carry that — the continuation-passing steps universally
quantify their successor states, so no single outcome term can be named before
the case split.  `ExecSat` is the fix: the outcome is existential, constrained
only by a predicate, and every walk step threads the pair through. -/

/-- Some outcome satisfying `P` is reachable: the existential the case tree
under a `CALL` needs. -/
def Func.ExecSat (fs : List Func) (sevm : Sevm) (devm : Devm) (f : Func)
    (P : Execution → Prop) : Prop :=
  ∃ ex, Func.ExecTo fs sevm devm f ex ∧ P ex

/-- The program altitude of `Func.ExecSat`. -/
def Prog.ExecSat (sevm : Sevm) (devm : Devm) (p : Prog)
    (P : Execution → Prop) : Prop :=
  ∃ ex, Prog.ExecTo sevm devm p ex ∧ P ex

/-- What `ExecSat` is for: the predicate holds of the total `exec`'s value. -/
theorem Prog.execSat_out {sevm : Sevm} {pre : Devm} {p : Prog}
    {P : Execution → Prop}
    (h : Prog.ExecSat sevm pre p P)
    (h_eq : some sevm.code.toList = p.compile) :
    P (exec ⟨0, sevm, pre⟩) := by
  rcases h with ⟨ex, hto, hp⟩
  rw [Prog.exec_of_execTo hto h_eq]
  exact hp

/-- The program entry, mirroring `Prog.runCompiledTo_intro`. -/
lemma Prog.execSat_intro {sevm : Sevm} {devm mid : Devm} {p : Prog}
    {P : Execution → Prop} {G : Nat}
    (h_gas : devm.gasLeft = G + gJumpdest)
    (h_mid : mid = devm.setMach ⟨devm.stack, devm.memory, G⟩)
    (h_main : Func.ExecSat (p.main :: p.aux) sevm mid p.main P) :
    Prog.ExecSat sevm devm p P := by
  rcases h_main with ⟨ex, hto, hp⟩
  subst h_mid
  exact ⟨ex, ⟨_, Devm.burnBy_setMach_gas h_gas, hto⟩, hp⟩

/-- A segment of ordinary instructions, threaded through the existential: the
transformer premise is a fixed-outcome `ExecTo` implication, which is exactly
the shape `func_run` proves — walk the goal, close the residue with the
hypothesis. -/
lemma Func.execSat_segment {fs : List Func} {sevm : Sevm} {devm devm' : Devm}
    {f f' : Func} {P : Execution → Prop}
    (h_seg : ∀ ex, Func.ExecTo fs sevm devm' f' ex →
      Func.ExecTo fs sevm devm f ex)
    (h : Func.ExecSat fs sevm devm' f' P) : Func.ExecSat fs sevm devm f P := by
  rcases h with ⟨ex, hto, hp⟩
  exact ⟨ex, h_seg ex hto, hp⟩

/-- One successful instruction, threaded through the existential. -/
lemma Func.execSat_next {fs : List Func} {sevm : Sevm} {devm devm' : Devm}
    {i : Ninst} {f : Func} {P : Execution → Prop}
    (h_n : Ninst.RunCompiled sevm devm i devm')
    (h_f : Func.ExecSat fs sevm devm' f P) :
    Func.ExecSat fs sevm devm (.next i f) P := by
  rcases h_f with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.execTo_next h_n hto, hp⟩

/-- A complete residual walk closes an `ExecSat` goal: the leaf terminal. -/
lemma Func.execSat_of_runCompiledTo {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f : Func} {ex : Execution} {P : Execution → Prop}
    (h : Func.RunCompiledTo fs sevm devm f ex) (hp : P ex) :
    Func.ExecSat fs sevm devm f P :=
  ⟨ex, Func.ExecTo.of_runCompiledTo h, hp⟩

/-- The fatal terminal: a spawning instruction fails, the frame settles at the
error right there, and the predicate is met on the error side. -/
lemma Func.execSat_next_error {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i : Ninst} {rest : Func} {e : EvmError × Devm} {P : Execution → Prop}
    (h : ∃ xl : Xlot, xl.Filled ∧
      ∀ pc, Ninst.StepRun pc sevm devm i xl (.error e))
    (hp : P (.error e)) :
    Func.ExecSat fs sevm devm (.next i rest) P :=
  ⟨.error e, Func.execTo_next_error h, hp⟩

/-! ### The continuation-passing steps, threaded through the existential

Positional siblings of the five `Func.runCompiledTo_*_step` lemmas above, for
walks whose outcome is decided by a case analysis further down.  Same premises,
same handed-back facts; only the relation differs, so each proof is its
sibling's with the pair threaded. -/

/-- `SLOAD` as an `ExecSat` walk step.  Sibling of
`Func.runCompiledTo_sload_step`. -/
lemma Func.execSat_sload_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k v : B256} {s : List B256} {M : Mem} {rest : Func} {P : Execution → Prop}
    (h_stk : devm.stack = k :: s) (h_room : s.length < 1024)
    (h_val : devm.getStorVal sevm.currentTarget k = v)
    (h_mem : devm.memory = M)
    (h_gas : gasColdSload ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (c G : Nat),
      (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ base.accessedStorageKeys →
      (∀ p : Adr × B256, p ∈ devm.accessedStorageKeys →
        p ∈ base.accessedStorageKeys) →
      (∀ (a : Adr) (k' : B256), base.getStorVal a k' = devm.getStorVal a k') →
      base.refundCounter = devm.refundCounter →
      base.logs = devm.logs →
      base.error = devm.error →
      gasWarmAccess ≤ c → c ≤ gasColdSload →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (base.setMach ⟨v :: s, M, G⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next Ninst.sload rest) P := by
  subst h_val; subst h_mem
  set base : Devm :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
    then devm else addAccessedStorageKey devm sevm.currentTarget k with h_base
  set c : Nat :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
    then gasWarmAccess else gasColdSload with h_c
  have h_lo : gasWarmAccess ≤ c := (le_sload_cost_of h_c.symm).1
  have h_hi : c ≤ gasColdSload := (le_sload_cost_of h_c.symm).2
  rcases h_next base c (devm.gasLeft - c)
      (mem_accessedStorageKeys_sload_of h_base.symm)
      (fun _ hp => mem_accessedStorageKeys_sload_of_mem h_base.symm hp)
      (fun _ _ => getStorVal_sload_of h_base.symm)
      (refundCounter_sload_of h_base.symm) (logs_sload_of h_base.symm)
      (by rw [h_base]; split <;> rfl)
      h_lo h_hi (by omega) with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.execTo_next
    (Ninst.runCompiled_sload_of (base := base) (c := c) (G := devm.gasLeft - c)
      h_stk h_base.symm h_c.symm rfl (by omega) h_room) hto, hp⟩

/-- `SSTORE` on a warm key as an `ExecSat` walk step.  Sibling of
`Func.runCompiledTo_sstore_warm_step`. -/
lemma Func.execSat_sstore_warm_step {fs : List Func} {sevm : Sevm}
    {devm : Devm} {k v : B256} {s : List B256} {M : Mem} {rest : Func}
    {P : Execution → Prop}
    (h_stk : devm.stack = k :: v :: s)
    (h_warm : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys)
    (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_gas : gasStorageSet ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (c G : Nat),
      base.getStorVal sevm.currentTarget k = v →
      (∀ (a : Adr) (k' : B256), (a, k') ≠ (sevm.currentTarget, k) →
        base.getStorVal a k' = devm.getStorVal a k') →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.logs = devm.logs →
      base.error = devm.error →
      c ≤ gasStorageSet →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (base.setMach ⟨s, M, G⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next Ninst.sstore rest) P := by
  subst h_mem
  have h_bound : sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v ≤ gasStorageSet := by
    rw [sstoreValueCost]; split_ifs <;> decide
  have h_key : ((devm.withRefundCounter (sstoreNewRefundCounter v
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k)
      devm.refundCounter)).setStorVal sevm.currentTarget k v).getStorVal
        sevm.currentTarget k = v := by
    show (Devm.getStor _ sevm.currentTarget).get k = v
    rw [setStorVal_getStor_self, Stor.get_set_self]
  have h_oth : ∀ (a : Adr) (k' : B256), (a, k') ≠ (sevm.currentTarget, k) →
      ((devm.withRefundCounter (sstoreNewRefundCounter v
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k)
        devm.refundCounter)).setStorVal sevm.currentTarget k v).getStorVal a k'
          = devm.getStorVal a k' := by
    intro a k' h_ne
    by_cases h_adr : sevm.currentTarget = a
    · subst h_adr
      have h_key' : k ≠ k' := fun h => h_ne (by rw [h])
      show (Devm.getStor _ sevm.currentTarget).get k' = _
      rw [setStorVal_getStor_self, Stor.get_set_ne _ h_key']
      rfl
    · show (Devm.getStor _ a).get k' = _
      have h_off : Devm.getStor
          ((devm.withRefundCounter (sstoreNewRefundCounter v
            (getOrigStorVal sevm sevm.currentTarget k)
            (devm.getStorVal sevm.currentTarget k)
            devm.refundCounter)).setStorVal sevm.currentTarget k v) a
            = Devm.getStor devm a := by
        simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, Devm.withState,
          Devm.setWorld, State.setStorVal]
        simp only [Devm.state, State.get_set_ne _ h_adr]
        rfl
      rw [h_off]
      rfl
  rcases h_next _ _ (devm.gasLeft - sstoreValueCost
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v)
      h_key h_oth rfl rfl rfl h_bound (by omega) with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.execTo_next
    (Ninst.runCompiled_sstore_warm (c := sstoreValueCost
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v)
      (G := devm.gasLeft - sstoreValueCost
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v)
      h_stk h_warm (by simp only [gCallStipend, gasStorageSet] at *; omega)
      h_static rfl rfl (by omega)) hto, hp⟩

/-- `MSTORE` as an `ExecSat` walk step.  Sibling of
`Func.runCompiledTo_mstore_step`. -/
lemma Func.execSat_mstore_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i v : B256} {s : List B256} {c : Nat} {M : Mem} {rest : Func}
    {P : Execution → Prop}
    (h_stk : devm.stack = i :: v :: s)
    (h_mem : devm.memory = M)
    (h_cost : gVerylow + devm.extCost [⟨i.toNat, 32⟩] = c)
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (M' : Mem) (G : Nat), M.write i.toNat v.toBytes = M' →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (devm.setMach ⟨s, M', G⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next Ninst.mstore rest) P := by
  subst h_mem
  rcases h_next _ (devm.gasLeft - c) rfl (by omega) with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.execTo_next
    (Ninst.runCompiled_mstore_of (G := devm.gasLeft - c) (e := devm.extCost
      [⟨i.toNat, 32⟩]) h_stk rfl (by omega) rfl) hto, hp⟩

/-- `LOG n` as an `ExecSat` walk step.  Sibling of
`Func.runCompiledTo_log_step`. -/
lemma Func.execSat_log_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {n : Fin 5} {i sz : B256} {topics s : List B256} {c : Nat} {M M' : Mem}
    {payload : Bytes} {rest : Func} {P : Execution → Prop}
    (h_stk : devm.stack = i :: sz :: (topics ++ s))
    (h_len : topics.length = n.val) (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_cost : gLog + gLogdata * sz.toNat + gLogtopic * n.val
      + devm.extCost [⟨i.toNat, sz.toNat⟩] = c)
    (h_data : (M.read i.toNat sz.toNat).1 = payload)
    (h_img : (M.read i.toNat sz.toNat).2 = M')
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (G : Nat),
      base.logs = devm.logs ++ [⟨sevm.currentTarget, topics, payload⟩] →
      (∀ (a : Adr) (k : B256), base.getStorVal a k = devm.getStorVal a k) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.error = devm.error →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (base.setMach ⟨s, M', G⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next (.reg (.log n)) rest) P := by
  subst h_mem
  rcases h_next (devm.addLog ⟨sevm.currentTarget, topics, payload⟩)
      (devm.gasLeft - c) rfl (fun _ _ => rfl) rfl rfl (by omega)
    with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.execTo_next
    (Ninst.runCompiled_log_of (G := devm.gasLeft - c) h_stk h_len h_static
      h_cost h_data h_img (by omega)) hto, hp⟩

/-- `CALLDATACOPY` as an `ExecSat` walk step.  Sibling of
`Func.runCompiledTo_calldatacopy_step`. -/
lemma Func.execSat_calldatacopy_step {fs : List Func} {sevm : Sevm}
    {devm : Devm} {di si sz : B256} {s : List B256} {c : Nat} {M : Mem}
    {rest : Func} {P : Execution → Prop}
    (h_stk : devm.stack = di :: si :: sz :: s)
    (h_mem : devm.memory = M)
    (h_cost : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩] = c)
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (M' : Mem) (G : Nat),
      M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0) = M' →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (devm.setMach ⟨s, M', G⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next (.reg .calldatacopy) rest) P := by
  subst h_mem
  rcases h_next _ (devm.gasLeft - c) rfl (by omega) with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.execTo_next
    (Ninst.runCompiled_calldatacopy_of (G := devm.gasLeft - c) h_stk h_cost
      rfl (by omega)) hto, hp⟩

/-! ## The `.call` arm's remaining shapes, and its world-dependent inputs

The crossing lemma family above (`Xinst.step_call_zero_value*`) covers the
spawn; a settlement statement also meets the **depth-limit arm** — at
`sevm.depth = 0` no child is spawned and the instruction answers `0` — and has
to price the world-dependent inputs it cannot compute: the delegation
resolution and the access cost.  Neither is knowable from the frame, so both
are *bounded*, which is all a closed gas bound needs. -/

/-- The delegation resolution moves only the accessed-address set: the machine
fields a continuation walks with are untouched, and the extra charge is at most
one cold account access. -/
lemma accessDelegation_inv {devm d1 : Devm} {a dadr : Adr} {dp : Bool}
    {code : ByteArray} {dgc : Nat}
    (h : accessDelegation devm a = ⟨dp, dadr, code, dgc, d1⟩) :
    d1.stack = devm.stack ∧ d1.memory = devm.memory ∧
      d1.gasLeft = devm.gasLeft ∧ dgc ≤ gasColdAccountAccess := by
  unfold accessDelegation at h
  rcases hd : getDelegatedCodeAddress (devm.state.getCode a) with _ | adr <;>
    simp only [hd] at h
  · cases h
    exact ⟨rfl, rfl, rfl, by decide⟩
  · cases h
    refine ⟨rfl, rfl, rfl, ?_⟩
    unfold accessCost
    split <;> decide

/-- And it leaves the settled-error field alone, which is how a frame-level
statement carries "this frame never stored a halt" across the `CALL`. -/
lemma accessDelegation_error {devm d1 : Devm} {a dadr : Adr} {dp : Bool}
    {code : ByteArray} {dgc : Nat}
    (h : accessDelegation devm a = ⟨dp, dadr, code, dgc, d1⟩) :
    d1.error = devm.error := by
  unfold accessDelegation at h
  rcases hd : getDelegatedCodeAddress (devm.state.getCode a) with _ | adr <;>
    simp only [hd] at h
  · cases h; rfl
  · cases h; rfl

/-- The account-access charge is at most the cold price. -/
lemma accessCost_le {x : Adr} {a : AdrSet} : accessCost x a ≤ gasColdAccountAccess := by
  unfold accessCost
  split <;> decide

/-- The depth-limit arm, packaged as the step interface: at `sevm.depth = 0`
the `CALL` charges, extends, pushes `0`, and hands the forwarded gas straight
back.  This is a *revert-path* case for a contract that branches on the flag,
never a premise. -/
lemma Ninst.runCompiled_call_zero_value_zero_depth {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth = 0)
    (h_room : d1.stack.length < 1024) :
    Ninst.RunCompiled sevm devm (.exec .call)
      ((((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
          [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).withReturnData
            []).setMach
        ⟨0 :: d1.stack,
          (d1.memory.extends [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]),
          d1.gasLeft - (mcc + ext) + mcs⟩) := by
  refine Ninst.runCompiled_exec_done ?_
  rw [Xinst.step_call_zero_value h_stk h_ext h_del h_acc h_split h_gas,
    genericCall.step_zero_depth h_depth (by
      show ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).stack.length < 1024
      exact h_room)]
  rfl

/-- Extending to already-covered windows leaves the image alone: the
`memExtends` a `CALL` performs after its charge is the identity whenever the
frame wrote its argument window first. -/
lemma Mem.extends_covered {N : Mem} {ps : List (Nat × Nat)}
    (h : memExtsSize N.size ps = N.size) : N.extends ps = N := by
  show (⟨N.data, memExtsSize N.size ps⟩ : Mem) = N
  rw [h]

/-- An access window the image already covers costs nothing. -/
lemma Devm.extCost_covered {devm : Devm} {S : List B256} {N : Mem} {G : Nat}
    {ws : List (Nat × Nat)} (h : memExtsSize N.size ws = N.size) :
    (devm.setMach ⟨S, N, G⟩).extCost ws = 0 := by
  simp only [Devm.extCost, Devm.memory_setMach, h]
  omega

/-! ### Reading the suspended parent

The three machine fields of `callSpawnParent`, as the continuation reads them.
All three are projections through `memExtends` and `withReturnData`, which
touch `mach.memory` and `meta` respectively. -/

lemma callSpawnParent_stack {d1 : Devm} {c ii is oi os : Nat} :
    (callSpawnParent d1 c ii is oi os).stack = d1.stack := rfl

lemma callSpawnParent_memory {d1 : Devm} {c ii is oi os : Nat} :
    (callSpawnParent d1 c ii is oi os).memory
      = d1.memory.extends [⟨ii, is⟩, ⟨oi, os⟩] := rfl

lemma callSpawnParent_gasLeft {d1 : Devm} {c ii is oi os : Nat} :
    (callSpawnParent d1 c ii is oi os).gasLeft = d1.gasLeft - c := rfl

/-- And the settled-error field, which the suspension does not touch either:
`withReturnData` writes `meta.returnData`, not `meta.error`. -/
lemma callSpawnParent_error {d1 : Devm} {c ii is oi os : Nat} :
    (callSpawnParent d1 c ii is oi os).error = d1.error := rfl

end Blanc
