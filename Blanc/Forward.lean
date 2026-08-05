-- Forward.lean : constructing `Func.RunCompiled` derivations, rather than
-- taking them apart.
--
-- `Blanc/Compiled.lean` relates the gas-exact relation to Jaune's `exec` in
-- both directions, and `Blanc/Tactics.lean` is entirely inversion: every one of
-- its tactics matches a run in *antecedent* position.  Nothing anywhere
-- **produces** a `Func.RunCompiled` derivation, so nothing in the repository
-- has ever said that a call succeeds.
--
-- This module is the missing dual.  Everything here is goal-directed: given a
-- state and the instruction that runs on it, produce the relation's premise
-- with the successor state written out.  Composed through
-- `Prog.exec_of_runCompiled`, a chain of these becomes a successful `Exec`.
--
-- Two conventions make the chaining work and are worth stating once.
--
-- * **Every successor state is `devm.setMach ⟨stack, memory, gasLeft⟩`.**  The
--   three machine fields are the only ones any instruction on a call-free path
--   moves, and `Devm.setMach_setMach` collapses a chain of them, so the state
--   after `n` steps is again one `setMach` over the *original* `devm`.  This is
--   what keeps the terms from nesting.
-- * **Every side condition is on the rule's pre-state.**  `Devm.push` guards
--   `stack.length < 1024` on the stack it pushes onto, so a lemma that pops
--   before it pushes asks for headroom on the *popped* stack.  The banner in
--   `Blanc/Compiled.lean` says the same thing about the relation's own rules.
--
-- Nothing here is contract-specific: a demonstration belongs in a
-- contract-owned module, since a shared module importing a contract is the
-- inverted import `scripts/check-layering.sh` rejects.
--
-- The import of `Blanc/CommonProofs.lean` -- which pulls `Blanc/Tactics.lean`
-- in behind it -- is for the `Devm`/`Bytes` algebra the inversion layer
-- already owns, `Bytes.toB256_sig` in particular.  Reproving those here would
-- be duplication across two modules of the same shared layer.

import Blanc.Compiled
import Blanc.CommonProofs

namespace Blanc

open Jaune

/-- The third machine projection through `setMach`.  `Blanc/Compiled.lean` has
the other two; this one is only needed by the forward direction, where states
are *written* as `setMach` terms rather than destructured. -/
lemma Devm.stack_setMach {devm : Devm} {m : Mach} :
    (devm.setMach m).stack = m.stack := rfl

/-- Storage is a world field, so a machine write cannot move it. -/
lemma Devm.getStorVal_setMach {devm : Devm} {m : Mach} {a : Adr} {k : B256} :
    (devm.setMach m).getStorVal a k = devm.getStorVal a k := rfl

/-- `Devm.popToNat`, evaluated forward: `Devm.pop` with the popped word read
as a `Nat`. -/
lemma Devm.popToNat_eq_ok {x : B256} {s : List B256} {devm : Devm}
    (h : devm.stack = x :: s) :
    devm.popToNat =
      .ok ⟨x.toNat, devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
  rw [Devm.popToNat_def, Devm.pop_eq_ok h]
  rfl

/-! ## The instruction premise, constructed

`Ninst.RunCompiled` is `∃ xl, xl.Filled ∧ ∀ pc, Ninst.StepRun pc … xl (.ok …)`.
For a `.reg` or a `.push` the slot is `.none`, whose `Filled` is `True`, so the
existential is discharged by `trivial` and only the step equation is left.  It
is genuinely existential only for a spawning instruction, which is exactly why
a call-free target keeps this layer unconditional. -/

/-- A register instruction other than `PC`, from one evaluation of
`Rinst.runCore`.  The `∀ pc` is free: `Rinst.runCore_pc_irrel` says `PC` is the
only opcode that can tell one program counter from another. -/
lemma Ninst.runCompiled_reg {sevm : Sevm} {devm devm' : Devm} {r : Rinst}
    (h_ne : r ≠ .pc) (h : Rinst.runCore 0 devm sevm r = .ok devm') :
    Ninst.RunCompiled sevm devm (.reg r) devm' := by
  refine ⟨.none, trivial, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution]
  refine ⟨rfl, ?_⟩
  show Except.ok devm' = Rinst.runCore pc devm sevm r
  rw [← Rinst.runCore_pc_irrel h_ne 0 pc, h]

/-- The gas a `PUSH` costs: `PUSH0` takes no immediate and is a `gBase`
instruction, everything else is `gVerylow`.  `Ninst.step_push` branches on
exactly this, and getting it wrong is the easiest way to build a derivation
that no execution realizes. -/
def pushCost (xs : Bytes) : Nat := if xs = [] then gBase else gVerylow

/-- A `PUSH`, from gas and headroom.  Covers `PUSH0` and `PUSH1 … PUSH32`
alike; `Blanc/Compiled.lean`'s `Evm.push_cont` is the same step at the `Exec`
altitude and is restricted to the non-empty case. -/
lemma Ninst.runCompiled_push {sevm : Sevm} {devm : Devm} {xs : Bytes}
    {le : xs.length ≤ 32} (h_gas : pushCost xs ≤ devm.gasLeft)
    (h_room : devm.stack.length < 1024) :
    Ninst.RunCompiled sevm devm (.push xs le)
      (devm.setMach ⟨xs.toB256 :: devm.stack, devm.memory,
        devm.gasLeft - pushCost xs⟩) := by
  refine ⟨.none, trivial, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution]
  refine ⟨rfl, ?_⟩
  show _ = (chargeGas (pushCost xs) devm >>= fun d => Devm.push xs.toB256 d)
  rw [chargeGas_eq_ok h_gas]
  simp only [bind, Except.bind]
  rw [Devm.push_eq_ok
    (devm := devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - pushCost xs⟩)
    h_room]
  rfl

/-- `PUSH0` is the only zero-valued push `Ninst.pushB256` emits: `Bytes.sig`
drops every leading zero byte, so `(0 : B256)` leaves nothing at all. -/
lemma pushCost_zero : pushCost ((0 : B256).toBytes.sig) = gBase := rfl

/-- Every other `Ninst.pushB256` carries an immediate and costs `gVerylow`.
Proved from `Bytes.toB256_sig`, so it needs no computation on `w` — an
`Ninst.pushB256` of a keccak-derived selector discharges it from `w ≠ 0`
alone. -/
lemma pushCost_of_ne_zero {w : B256} (h : w ≠ 0) :
    pushCost (w.toBytes.sig) = gVerylow := by
  rw [pushCost, if_neg]
  intro h_nil
  exact h (by rw [← B256.toB256_toBytes w, ← Bytes.toB256_sig, h_nil]; rfl)

/-! ## The register instructions, evaluated forward

`Rinst.runCore` routes most of the arithmetic and comparison opcodes through
`applyUnary` / `applyBinary`, so two lemmas cover a large part of the
instruction set at once.  The rest are one lemma per opcode and are added here
as targets need them. -/

/-- `applyUnary`, evaluated forward. -/
lemma applyUnary_eq_ok {f : B256 → B256} {cost : Nat} {devm : Devm}
    {x : B256} {s : List B256} (h_stk : devm.stack = x :: s)
    (h_gas : cost ≤ devm.gasLeft) (h_room : s.length < 1024) :
    applyUnary f cost devm =
      .ok (devm.setMach ⟨f x :: s, devm.memory, devm.gasLeft - cost⟩) := by
  rw [applyUnary_def, Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind, pushItem_def]
  rw [chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stack_setMach]
  rw [Devm.push_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft - cost⟩) h_room]
  rfl

/-- `applyBinary`, evaluated forward.  The operand order is the machine's: the
top of the stack is `f`'s first argument. -/
lemma applyBinary_eq_ok {f : B256 → B256 → B256} {cost : Nat} {devm : Devm}
    {x y : B256} {s : List B256} (h_stk : devm.stack = x :: y :: s)
    (h_gas : cost ≤ devm.gasLeft) (h_room : s.length < 1024) :
    applyBinary f cost devm =
      .ok (devm.setMach ⟨f x y :: s, devm.memory, devm.gasLeft - cost⟩) := by
  rw [applyBinary_def, Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach ⟨y :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [bind, Except.bind, pushItem_def, Devm.setMach_setMach,
    Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stack_setMach]
  rw [Devm.push_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft - cost⟩) h_room]
  rfl

/-- `DUP n`, evaluated forward.  The duplicated word is read off the *charged*
stack, which `chargeGas` leaves alone, so the index is into the pre-state. -/
lemma Rinst.runCore_dup_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {n : Fin 16} {w : B256} (h_get : devm.stack[n.val]? = some w)
    (h_gas : gVerylow ≤ devm.gasLeft) (h_room : devm.stack.length < 1024) :
    Rinst.runCore pc devm sevm (.dup n) =
      .ok (devm.setMach
        ⟨w :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩) := by
  show (chargeGas gVerylow devm >>= fun d =>
    match d.stack[n.val]? with
    | none => .error ⟨.halt (.stackUnderflow .none), d⟩
    | some word => Devm.push word d) = _
  rw [chargeGas_eq_ok h_gas]
  simp only [bind, Except.bind]
  show (match (devm.setMach
      ⟨devm.stack, devm.memory, devm.gasLeft - gVerylow⟩).stack[n.val]? with
    | none => _
    | some word => Devm.push word _) = _
  show (match devm.stack[n.val]? with
    | none => _
    | some word => Devm.push word _) = _
  rw [h_get]
  show Devm.push w
    (devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - gVerylow⟩) = _
  rw [Devm.push_eq_ok
    (devm := devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - gVerylow⟩)
    h_room]
  rfl

/-- `CALLDATALOAD`, evaluated forward.  The value is `Sevm.dataWord`, which is
defined to be exactly this expression, so nothing here models calldata a second
time. -/
lemma Rinst.runCore_calldataload_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {x : B256} {s : List B256} (h_stk : devm.stack = x :: s)
    (h_gas : gVerylow ≤ devm.gasLeft) (h_room : s.length < 1024) :
    Rinst.runCore pc devm sevm .calldataload =
      .ok (devm.setMach ⟨Sevm.dataWord sevm x :: s, devm.memory,
        devm.gasLeft - gVerylow⟩) := by
  show (devm.pop >>= fun p => chargeGas gVerylow p.2 >>= fun d =>
    d.push (Bytes.toB256 <| sevm.data.sliceD p.1.toNat 32 0)) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stack_setMach]
  rw [Devm.push_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft - gVerylow⟩) h_room]
  rfl

/-- `SLOAD` on a cold key, evaluated forward: the key joins the accessed set
and the read costs `gasColdSload`.

The warm case is a different lemma, not a parameter of this one: the two
charge different constants *and* end in different accessed-key sets, and a
statement covering both would have to carry the `if` into every downstream
gas equation. -/
lemma Rinst.runCore_sload_cold_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {k : B256} {s : List B256} (h_stk : devm.stack = k :: s)
    (h_cold : ⟨sevm.currentTarget, k⟩ ∉ devm.accessedStorageKeys)
    (h_gas : gasColdSload ≤ devm.gasLeft) (h_room : s.length < 1024) :
    Rinst.runCore pc devm sevm .sload =
      .ok ((addAccessedStorageKey
              (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
              sevm.currentTarget k).setMach
        ⟨devm.getStorVal sevm.currentTarget k :: s, devm.memory,
          devm.gasLeft - gasColdSload⟩) := by
  rw [show Rinst.runCore pc devm sevm .sload = (do
      let ⟨key, d⟩ ← devm.pop
      let d ←
        if ⟨sevm.currentTarget, key⟩ ∈ d.accessedStorageKeys then
          chargeGas gasWarmAccess d
        else
          chargeGas gasColdSload
            (addAccessedStorageKey d sevm.currentTarget key)
      d.push (d.getStorVal sevm.currentTarget key)) from rfl]
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  have h_keys : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedStorageKeys
      = devm.accessedStorageKeys := rfl
  rw [if_neg (by rw [h_keys]; exact h_cold)]
  set d0 : Devm := addAccessedStorageKey
    (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) sevm.currentTarget k with hd0
  have h_d0_gas : d0.gasLeft = devm.gasLeft := rfl
  have h_d0_stack : d0.stack = s := rfl
  have h_d0_mem : d0.memory = devm.memory := rfl
  have h_d0_stor : d0.getStorVal sevm.currentTarget k
      = devm.getStorVal sevm.currentTarget k := rfl
  rw [chargeGas_eq_ok (devm := d0) (by rw [h_d0_gas]; exact h_gas)]
  dsimp only
  rw [Devm.push_eq_ok
    (devm := d0.setMach ⟨d0.stack, d0.memory, d0.gasLeft - gasColdSload⟩)
    (by rw [Devm.stack_setMach, h_d0_stack]; exact h_room)]
  rw [h_d0_gas, h_d0_stack, h_d0_mem, Devm.getStorVal_setMach, h_d0_stor]
  simp only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]

/-- `MSTORE`, evaluated forward.  The memory-expansion charge is
`Devm.extCost`, left as it stands: it is a function of the pre-state's memory
and a target that fixes that memory turns it into a numeral. -/
lemma Rinst.runCore_mstore_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {i v : B256} {s : List B256} (h_stk : devm.stack = i :: v :: s)
    (h_gas : gVerylow + devm.extCost [⟨i.toNat, 32⟩] ≤ devm.gasLeft) :
    Rinst.runCore pc devm sevm .mstore =
      .ok ((devm.setMach ⟨s, devm.memory,
              devm.gasLeft - (gVerylow + devm.extCost [⟨i.toNat, 32⟩])⟩).memWrite
        i.toNat v.toBytes) := by
  show (devm.popToNat >>= fun p => p.2.pop >>= fun q =>
    chargeGas (gVerylow + q.2.extCost [⟨p.1, 32⟩]) q.2 >>= fun d =>
      Except.ok (d.memWrite p.1 q.1.toBytes)) = _
  rw [Devm.popToNat_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach ⟨v :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨i.toNat, 32⟩] = devm.extCost [⟨i.toNat, 32⟩] := rfl
  rw [h_ext, chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stack_setMach]

/-! ## The step interface: exact gas in, named successor out

Everything above evaluates a Jaune function and lands on
`devm.gasLeft - cost`.  The wrappers below take the gas premise in the
relation's own `a = b + cost` shape instead and hand the successor's gas
account back as a **name**.

That is not cosmetic.  Chaining `n` steps in the subtractive form gives a
successor whose gas is `pre.gasLeft - c₁ - … - cₙ`, and every state written
in a proof carries the whole prefix; in the additive form each state names
its own `G`, the caller picks `pre.gasLeft - N` for a single numeral `N`, and
every side condition is one `omega`.  `Nat` subtraction makes these two forms
propositionally but not definitionally equal, so the choice has to be made in
the signature.

Each wrapper also takes the computed word as a parameter with an equation, so
the successor carries the value the caller names rather than an unevaluated
application: on a dispatch walk that is the difference between a stack of
closed selector words and a stack of frozen `B256` redexes. -/

/-- `Ninst.pushB256`, the idiom Blanc's `Line`s are written in. -/
lemma Ninst.runCompiled_pushB256 {sevm : Sevm} {devm : Devm} {w : B256}
    {c G : Nat} (h_cost : pushCost (w.toBytes.sig) = c)
    (h_gas : devm.gasLeft = G + c) (h_room : devm.stack.length < 1024) :
    Ninst.RunCompiled sevm devm (Ninst.pushB256 w)
      (devm.setMach ⟨w :: devm.stack, devm.memory, G⟩) := by
  subst h_cost
  have h_eq : devm.gasLeft - pushCost (w.toBytes.sig) = G := by omega
  rw [← h_eq]
  have h := Ninst.runCompiled_push (sevm := sevm) (devm := devm)
    (xs := w.toBytes.sig)
    (le := le_of_le_of_eq (List.length_dropWhile_le _ _) (B256.length_toBytes _))
    (by omega) h_room
  rw [Bytes.toB256_sig, B256.toB256_toBytes] at h
  exact h

/-- A binary register opcode: `EQ`, `GT`, `SHR`, `ADD`, … -/
lemma Ninst.runCompiled_binary {sevm : Sevm} {devm : Devm} {r : Rinst}
    {f : B256 → B256 → B256} {cost G : Nat} {x y v : B256} {s : List B256}
    (h_ne : r ≠ .pc)
    (h_def : Rinst.runCore 0 devm sevm r = applyBinary f cost devm)
    (h_stk : devm.stack = x :: y :: s) (h_val : f x y = v)
    (h_gas : devm.gasLeft = G + cost) (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg r)
      (devm.setMach ⟨v :: s, devm.memory, G⟩) := by
  subst h_val
  have h_eq : devm.gasLeft - cost = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg h_ne
    (h_def.trans (applyBinary_eq_ok h_stk (by omega) h_room))

/-- A unary register opcode: `NOT`, `ISZERO`, … -/
lemma Ninst.runCompiled_unary {sevm : Sevm} {devm : Devm} {r : Rinst}
    {f : B256 → B256} {cost G : Nat} {x v : B256} {s : List B256}
    (h_ne : r ≠ .pc)
    (h_def : Rinst.runCore 0 devm sevm r = applyUnary f cost devm)
    (h_stk : devm.stack = x :: s) (h_val : f x = v)
    (h_gas : devm.gasLeft = G + cost) (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg r)
      (devm.setMach ⟨v :: s, devm.memory, G⟩) := by
  subst h_val
  have h_eq : devm.gasLeft - cost = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg h_ne
    (h_def.trans (applyUnary_eq_ok h_stk (by omega) h_room))

/-- `DUP n`. -/
lemma Ninst.runCompiled_dup {sevm : Sevm} {devm : Devm} {n : Fin 16} {w : B256}
    {G : Nat} (h_get : devm.stack[n.val]? = some w)
    (h_gas : devm.gasLeft = G + gVerylow)
    (h_room : devm.stack.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg (.dup n))
      (devm.setMach ⟨w :: devm.stack, devm.memory, G⟩) := by
  have h_eq : devm.gasLeft - gVerylow = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_dup_eq_ok h_get (by omega) h_room)

/-- `CALLDATALOAD`. -/
lemma Ninst.runCompiled_calldataload {sevm : Sevm} {devm : Devm} {x v : B256}
    {s : List B256} {G : Nat} (h_stk : devm.stack = x :: s)
    (h_val : Sevm.dataWord sevm x = v) (h_gas : devm.gasLeft = G + gVerylow)
    (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg .calldataload)
      (devm.setMach ⟨v :: s, devm.memory, G⟩) := by
  subst h_val
  have h_eq : devm.gasLeft - gVerylow = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_calldataload_eq_ok h_stk (by omega) h_room)

/-- `SLOAD` on a cold key.  The successor is not a `setMach` over `devm`: the
key joins the accessed set, which is a `meta` field, so the base state moves
once here and stays moved for the rest of the chain. -/
lemma Ninst.runCompiled_sload_cold {sevm : Sevm} {devm : Devm} {k v : B256}
    {s : List B256} {G : Nat} (h_stk : devm.stack = k :: s)
    (h_cold : ⟨sevm.currentTarget, k⟩ ∉ devm.accessedStorageKeys)
    (h_val : devm.getStorVal sevm.currentTarget k = v)
    (h_gas : devm.gasLeft = G + gasColdSload) (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg .sload)
      ((addAccessedStorageKey devm sevm.currentTarget k).setMach
        ⟨v :: s, devm.memory, G⟩) := by
  subst h_val
  have h_eq : devm.gasLeft - gasColdSload = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_sload_cold_eq_ok h_stk h_cold (by omega) h_room)

/-- `MSTORE`.  The expansion charge is `Devm.extCost`, which a target that
fixes the pre-state's memory turns into a numeral. -/
lemma Ninst.runCompiled_mstore {sevm : Sevm} {devm : Devm} {i v : B256}
    {s : List B256} {G : Nat} {M : Mem} (h_stk : devm.stack = i :: v :: s)
    (h_gas : devm.gasLeft = G + (gVerylow + devm.extCost [⟨i.toNat, 32⟩]))
    (h_write : devm.memory.write i.toNat v.toBytes = M) :
    Ninst.RunCompiled sevm devm (.reg .mstore)
      (devm.setMach ⟨s, M, G⟩) := by
  subst h_write
  have h_eq :
      devm.gasLeft - (gVerylow + devm.extCost [⟨i.toNat, 32⟩]) = G := by omega
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  rw [Rinst.runCore_mstore_eq_ok h_stk (by omega), h_eq]
  rfl

/-! ## The terminal instruction

`Func.RunCompiled`'s `.last` rule takes a `Linst.Run` unchanged — a `Linst`
ends the frame, so there is no successor state to pin.  Only `.ret` is
evaluated forward here; `.stop` needs nothing, and `.rev` and `.dest` do not
end in `.ok`. -/

/-- `Linst.run` on a `RETURN`, evaluated forward. -/
lemma Linst.run_ret_eq_ok {sevm : Sevm} {devm : Devm} {i sz : B256}
    {s : List B256} {out : Bytes} {d' : Devm}
    (h_stk : devm.stack = i :: sz :: s)
    (h_gas : devm.extCost [⟨i.toNat, sz.toNat⟩] ≤ devm.gasLeft)
    (h_read : (devm.setMach ⟨s, devm.memory,
        devm.gasLeft - devm.extCost [⟨i.toNat, sz.toNat⟩]⟩).memRead
          i.toNat sz.toNat = ⟨out, d'⟩) :
    Linst.run sevm devm .ret = .ok (d'.withOutput out) := by
  show (do
    let ⟨index, d⟩ ← devm.popToNat
    let ⟨size, d⟩ ← d.popToNat
    let cost := d.extCost [⟨index, size⟩]
    let d ← chargeGas cost d
    let ⟨output, d⟩ := d.memRead index size
    Except.ok (d.withOutput output)) = _
  rw [Devm.popToNat_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨sz :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨i.toNat, sz.toNat⟩] = devm.extCost [⟨i.toNat, sz.toNat⟩] := rfl
  rw [h_ext, chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stack_setMach]
  rw [h_read]

/-- `RETURN`.  The memory read is handed in rather than written out: it is a
function of the post-charge state, and a target that fixes that state turns
`h_read` into `rfl`. -/
lemma Func.runCompiled_ret {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i sz : B256} {s : List B256} {out : Bytes} {d' : Devm} {G : Nat}
    (h_stk : devm.stack = i :: sz :: s)
    (h_gas : devm.gasLeft = G + devm.extCost [⟨i.toNat, sz.toNat⟩])
    (h_read : (devm.setMach ⟨s, devm.memory, G⟩).memRead i.toNat sz.toNat
      = ⟨out, d'⟩) :
    Func.RunCompiled fs sevm devm (.last .ret) (d'.withOutput out) := by
  have h_eq : devm.gasLeft - devm.extCost [⟨i.toNat, sz.toNat⟩] = G := by omega
  refine Func.RunCompiled.last ?_
  show Linst.run sevm devm .ret = _
  exact Linst.run_ret_eq_ok (out := out) (d' := d') h_stk (by omega)
    (by rw [h_eq]; exact h_read)

/-! ## The exact-gas frames, constructed

`Func.RunCompiled`'s `.zero`, `.succ` and `.call` rules each ask for a frame
between the pre-state and the state their arm starts in.  On a chain of
`setMach` states both frames are the same shape, so these two lemmas replace
what would otherwise be a fourteen-field record literal at every jump. -/

/-- The exact burn between a state and the same state with `cost` off the gas
account. -/
lemma Devm.burnBy_setMach_gas {devm : Devm} {cost G : Nat}
    (h : devm.gasLeft = G + cost) :
    Devm.BurnBy cost devm (devm.setMach ⟨devm.stack, devm.memory, G⟩) :=
  { stack := rfl, memory := rfl, gasLeft := h,
    logs := rfl, refundCounter := rfl, output := rfl, accountsToDelete := rfl,
    returnData := rfl, error := rfl, accessedAddresses := rfl,
    accessedStorageKeys := rfl, state := rfl, createdAccounts := rfl,
    transientStorage := rfl }

/-- The exact pop-and-burn between a state whose stack is `x :: s` and the
same state cut down to `s` with `cost` off the gas account. -/
lemma Devm.popBurnBy_setMach {devm : Devm} {x : B256} {s : List B256}
    {cost G : Nat} (h_stk : devm.stack = x :: s)
    (h : devm.gasLeft = G + cost) :
    Devm.PopBurnBy [x] cost devm (devm.setMach ⟨s, devm.memory, G⟩) :=
  { stack := h_stk, memory := rfl, gasLeft := h,
    logs := rfl, refundCounter := rfl, output := rfl, accountsToDelete := rfl,
    returnData := rfl, error := rfl, accessedAddresses := rfl,
    accessedStorageKeys := rfl, state := rfl, createdAccounts := rfl,
    transientStorage := rfl }

/-! ## The two jump-emitting rules and the program entry

Wrappers that put the frame together with the side condition, so a
construction applies one lemma per node instead of one lemma plus a record.

The stack-headroom condition is on the **pre**-state in all three, including
`.call`, whose `PUSH2` needs the room whether or not the `JUMP` pops the value
straight back off. -/

/-- The `.zero` arm of a `branch`: the `JUMPI` condition is `0` and the arm
falls through, paying `PUSH2` and `JUMPI` only. -/
lemma Func.runCompiled_branch_zero {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {devm' : Devm} {s : List B256} {G : Nat}
    (h_stk : devm.stack = 0 :: s) (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh))
    (h_arm : Func.RunCompiled fs sevm (devm.setMach ⟨s, devm.memory, G⟩)
      f devm') :
    Func.RunCompiled fs sevm devm (.branch f g) devm' :=
  .zero h_room (Devm.popBurnBy_setMach h_stk h_gas) h_arm

/-- The `.succ` arm of a `branch`: the `JUMPI` condition is nonzero, so the
arm is reached by a jump and pays the target's `JUMPDEST` on top. -/
lemma Func.runCompiled_branch_succ {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {devm' : Devm} {w : B256} {s : List B256} {G : Nat}
    (h_ne : w ≠ 0) (h_stk : devm.stack = w :: s)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh + gJumpdest))
    (h_arm : Func.RunCompiled fs sevm (devm.setMach ⟨s, devm.memory, G⟩)
      g devm') :
    Func.RunCompiled fs sevm devm (.branch f g) devm' :=
  .succ h_ne h_room (Devm.popBurnBy_setMach h_stk h_gas) h_arm

/-- An internal `.call`: a tail jump into the flat table.  It is **not** an
external call — it carries no `Xlot` obligation at all, only the table lookup,
the headroom and `PUSH2; JUMP; JUMPDEST`'s gas. -/
lemma Func.runCompiled_call' {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k : Nat} {f : Func} {devm' : Devm} {G : Nat} (h_get : fs[k]? = some f)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gMid + gJumpdest))
    (h_body : Func.RunCompiled fs sevm
      (devm.setMach ⟨devm.stack, devm.memory, G⟩) f devm') :
    Func.RunCompiled fs sevm devm (.call k) devm' :=
  .call h_get h_room (Devm.burnBy_setMach_gas h_gas) h_body

/-- The program entry: `Table.compile`'s leading `JUMPDEST` and nothing else.
`Prog.RunCompiled` deliberately does not reuse the `.call` rule here — that
would charge `gVerylow + gMid` for a `PUSH2; JUMP` the entry never emits.

`h_mid` lets the caller name the state the main body starts in, which is what
makes a construction's first premise its own rather than a projection chain
over `devm`. -/
lemma Prog.runCompiled_intro {sevm : Sevm} {devm mid : Devm} {p : Prog}
    {devm' : Devm} {G : Nat} (h_gas : devm.gasLeft = G + gJumpdest)
    (h_mid : mid = devm.setMach ⟨devm.stack, devm.memory, G⟩)
    (h_main : Func.RunCompiled (p.main :: p.aux) sevm mid p.main devm') :
    Prog.RunCompiled sevm devm p devm' := by
  subst h_mid
  exact ⟨_, Devm.burnBy_setMach_gas h_gas, h_main⟩

end Blanc
