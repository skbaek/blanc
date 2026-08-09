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

/-- Account code is a world field, so a machine write cannot move it. -/
lemma Devm.getCode_setMach {devm : Devm} {m : Mach} {a : Adr} :
    (devm.setMach m).getCode a = devm.getCode a := rfl

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

/-- `pushItem`, evaluated forward.  `Jaune/Machine.lean`'s `pushItem_def` gives
`pushItem x c devm = chargeGas c devm >>= Devm.push x`, which is the same two
steps `Ninst.runCompiled_push` takes for a `PUSH`; the word is just supplied by
the frame instead of by an immediate.

Stated for the class rather than for one opcode.  `Rinst.runCore` routes
`ADDRESS`, `CALLER`, `CALLVALUE`, `ORIGIN`, `CALLDATASIZE`, `CODESIZE`,
`BASEFEE`, `GASPRICE` and `RETURNDATASIZE` through `pushItem` with `gBase` and a
word read off `sevm` or `devm`, so one lemma covers all of them and the caller
supplies only which word.  None of them reads the stack below the push, so
unlike `applyUnary`/`applyBinary` there is no stack-shape premise at all. -/
lemma pushItem_eq_ok {x : B256} {cost : Nat} {devm : Devm}
    (h_gas : cost ≤ devm.gasLeft) (h_room : devm.stack.length < 1024) :
    pushItem x cost devm =
      .ok (devm.setMach ⟨x :: devm.stack, devm.memory,
        devm.gasLeft - cost⟩) := by
  rw [pushItem_def, chargeGas_eq_ok h_gas]
  simp only [bind, Except.bind]
  rw [Devm.push_eq_ok
    (devm := devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - cost⟩) h_room]
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

/-- `EXTCODESIZE` on a cold account.  The queried address joins the frame's
access list, the instruction costs `gasColdAccountAccess`, and the pushed word
is the exact size of the account code in the pre-state. -/
lemma Rinst.runCore_extcodesize_cold_eq_ok {pc : Nat} {devm : Devm}
    {sevm : Sevm} {x : B256} {s : List B256}
    (h_stk : devm.stack = x :: s)
    (h_cold : x.toAdr ∉ devm.accessedAddresses)
    (h_gas : gasColdAccountAccess ≤ devm.gasLeft)
    (h_room : s.length < 1024) :
    Rinst.runCore pc devm sevm .extcodesize =
      .ok ((addAccessedAddress
              (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) x.toAdr).setMach
        ⟨(devm.getCode x.toAdr).size.toB256 :: s, devm.memory,
          devm.gasLeft - gasColdAccountAccess⟩) := by
  rw [show Rinst.runCore pc devm sevm .extcodesize = (do
      let ⟨adr, d⟩ ← devm.popToAdr
      let d ←
        if adr ∈ d.accessedAddresses then
          chargeGas gasWarmAccess d
        else
          chargeGas gasColdAccountAccess (addAccessedAddress d adr)
      d.push (d.getCode adr).size.toB256) from rfl]
  rw [Devm.popToAdr_def, Devm.pop_eq_ok h_stk]
  simp only [Functor.mapRev, Functor.map, Except.map, Prod.mapFst, Prod.map,
    id, bind, Except.bind]
  have h_addresses :
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses =
        devm.accessedAddresses := rfl
  rw [if_neg (by rw [h_addresses]; exact h_cold)]
  set d0 : Devm := addAccessedAddress
    (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) x.toAdr with hd0
  have h_d0_gas : d0.gasLeft = devm.gasLeft := rfl
  have h_d0_stack : d0.stack = s := rfl
  have h_d0_mem : d0.memory = devm.memory := rfl
  have h_d0_code : d0.getCode x.toAdr = devm.getCode x.toAdr := by
    rw [hd0, addAccessedAddress_getCode]
    rfl
  rw [chargeGas_eq_ok (devm := d0) (by rw [h_d0_gas]; exact h_gas)]
  dsimp only
  rw [Devm.push_eq_ok
    (devm := d0.setMach
      ⟨d0.stack, d0.memory, d0.gasLeft - gasColdAccountAccess⟩)
    (by rw [Devm.stack_setMach, h_d0_stack]; exact h_room)]
  rw [Devm.getCode_setMach, h_d0_gas, h_d0_stack, h_d0_mem, h_d0_code]
  simp only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]

/-- `EXTCODESIZE` on a warm account.  The address is already in the access
list, so the base state does not move and the instruction costs
`gasWarmAccess`. -/
lemma Rinst.runCore_extcodesize_warm_eq_ok {pc : Nat} {devm : Devm}
    {sevm : Sevm} {x : B256} {s : List B256}
    (h_stk : devm.stack = x :: s)
    (h_warm : x.toAdr ∈ devm.accessedAddresses)
    (h_gas : gasWarmAccess ≤ devm.gasLeft)
    (h_room : s.length < 1024) :
    Rinst.runCore pc devm sevm .extcodesize =
      .ok (devm.setMach
        ⟨(devm.getCode x.toAdr).size.toB256 :: s, devm.memory,
          devm.gasLeft - gasWarmAccess⟩) := by
  rw [show Rinst.runCore pc devm sevm .extcodesize = (do
      let ⟨adr, d⟩ ← devm.popToAdr
      let d ←
        if adr ∈ d.accessedAddresses then
          chargeGas gasWarmAccess d
        else
          chargeGas gasColdAccountAccess (addAccessedAddress d adr)
      d.push (d.getCode adr).size.toB256) from rfl]
  rw [Devm.popToAdr_def, Devm.pop_eq_ok h_stk]
  simp only [Functor.mapRev, Functor.map, Except.map, Prod.mapFst, Prod.map,
    id, bind, Except.bind]
  have h_addresses :
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses =
        devm.accessedAddresses := rfl
  rw [if_pos (by rw [h_addresses]; exact h_warm)]
  rw [chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stack_setMach]
  rw [Devm.push_eq_ok
    (devm := devm.setMach
      ⟨s, devm.memory, devm.gasLeft - gasWarmAccess⟩) h_room]
  rw [Devm.getCode_setMach]
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

/-- `SLOAD` on a warm key, evaluated forward: the key is already in the
accessed set, so nothing joins it and the read costs `gasWarmAccess`.

**Deliberately a separate lemma from `Rinst.runCore_sload_cold_eq_ok`, not a
parameter of it** — read that lemma's docstring for the reason, which this
pair does not relitigate: the two charge different constants *and* end in
different accessed-key sets, so a single statement covering both would have to
carry an `if` into every downstream gas equation. The `if` belongs one level
up, in the *cost function* (`Blanc/WethGas.lean`'s `wethGas`), where it is
stated once and eliminated by `by_cases` exactly once.

The warm successor is structurally *simpler* than the cold one: no
`addAccessedStorageKey`, so the base state does not move and the result is a
plain `setMach` over `devm`. -/
lemma Rinst.runCore_sload_warm_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {k : B256} {s : List B256} (h_stk : devm.stack = k :: s)
    (h_warm : ⟨sevm.currentTarget, k⟩ ∈ devm.accessedStorageKeys)
    (h_gas : gasWarmAccess ≤ devm.gasLeft) (h_room : s.length < 1024) :
    Rinst.runCore pc devm sevm .sload =
      .ok (devm.setMach
        ⟨devm.getStorVal sevm.currentTarget k :: s, devm.memory,
          devm.gasLeft - gasWarmAccess⟩) := by
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
  rw [if_pos (by rw [h_keys]; exact h_warm)]
  rw [chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stack_setMach]
  rw [Devm.push_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft - gasWarmAccess⟩) h_room]
  rw [Devm.getStorVal_setMach]
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

/-! ### The state-changing and call-adjacent opcodes

Everything above this point is a read: a value comes off `sevm`, off the stack
or out of storage, and only the machine moves.  The rules below are the ones a
mutator needs — the copies, the hash, the log, the store — plus the two stack
shufflers and `GAS`, which a `CALL` site needs in order to say what it
forwarded.

Three shapes recur and are worth naming once.

* **A copy writes memory.**  `CALLDATACOPY` and `RETURNDATACOPY` end in
  `Devm.memWrite`, which is `Ninst.runCompiled_mstore`'s successor shape with a
  wider payload, so their rules carry the written image the same way.
* **A read extends memory.**  `MLOAD`, `KECCAK256` and `LOG` end in
  `Devm.memRead`, whose second component is the *extended* memory: the window
  the charge paid for is in the image afterwards even when nothing was written.
  Their successors therefore name `(devm.memory.read i sz).2`, not
  `devm.memory`.
* **A value the tactic must not compute.**  `KECCAK256`'s hash is handed back
  as a value obligation exactly as `applyBinary`'s is; nothing here evaluates
  `Bytes.keccak`. -/

/-- `POP`, evaluated forward.  The charge comes *after* the pop, so the gas
premise is on the pre-state and the successor is the popped stack. -/
lemma Rinst.runCore_pop_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {x : B256} {s : List B256} (h_stk : devm.stack = x :: s)
    (h_gas : gBase ≤ devm.gasLeft) :
    Rinst.runCore pc devm sevm .pop =
      .ok (devm.setMach ⟨s, devm.memory, devm.gasLeft - gBase⟩) := by
  show ((devm.pop <&> Prod.snd) >>= chargeGas gBase) = _
  rw [Devm.pop_eq_ok h_stk]
  show chargeGas gBase (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) = _
  rw [chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  rfl

/-- `SWAP n`, evaluated forward.  The charge comes *first*, and `List.swap` is
then applied to the charged stack, which is the pre-state's; the permuted stack
is handed in rather than computed, because `List.swap` on a literal stack is a
`rfl` at the call site and an unfolded `Option` bind here. -/
lemma Rinst.runCore_swap_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {n : Fin 16} {S : List B256} (h_swap : List.swap devm.stack n.val = some S)
    (h_gas : gVerylow ≤ devm.gasLeft) :
    Rinst.runCore pc devm sevm (.swap n) =
      .ok (devm.setMach ⟨S, devm.memory, devm.gasLeft - gVerylow⟩) := by
  show (chargeGas gVerylow devm >>= fun d =>
    match List.swap d.stack n.val with
    | none => .error ⟨.halt (.stackUnderflow .none), d⟩
    | some stack => .ok (d.withStack stack)) = _
  rw [chargeGas_eq_ok h_gas]
  simp only [bind, Except.bind, Devm.stack_setMach, h_swap]
  rfl

/-- `GAS`, evaluated forward.  The word pushed is the account *after* the
`gBase` charge, which is why a frame that wants to say what it forwarded has to
know its own gas exactly at this instruction. -/
lemma Rinst.runCore_gas_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    (h_gas : gBase ≤ devm.gasLeft) (h_room : devm.stack.length < 1024) :
    Rinst.runCore pc devm sevm .gas =
      .ok (devm.setMach ⟨(devm.gasLeft - gBase).toB256 :: devm.stack,
        devm.memory, devm.gasLeft - gBase⟩) := by
  show (chargeGas gBase devm >>= fun d => d.push d.gasLeft.toB256) = _
  rw [chargeGas_eq_ok h_gas]
  show Devm.push
    (devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - gBase⟩).gasLeft.toB256
    (devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - gBase⟩) = _
  rw [Devm.push_eq_ok
    (devm := devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - gBase⟩)
    (by rw [Devm.stack_setMach]; exact h_room)]
  rfl

/-- `MLOAD`, evaluated forward.  The successor's memory is the read's, not the
pre-state's: `Mem.read` returns the window-extended image, and a target that
already covers the window gets its own memory back. -/
lemma Rinst.runCore_mload_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {i : B256} {s : List B256} (h_stk : devm.stack = i :: s)
    (h_gas : gVerylow + devm.extCost [⟨i.toNat, 32⟩] ≤ devm.gasLeft)
    (h_room : s.length < 1024) :
    Rinst.runCore pc devm sevm .mload =
      .ok (devm.setMach
        ⟨Bytes.toB256 (devm.memory.read i.toNat 32).1 :: s,
          (devm.memory.read i.toNat 32).2,
          devm.gasLeft - (gVerylow + devm.extCost [⟨i.toNat, 32⟩])⟩) := by
  show (devm.popToNat >>= fun p =>
    chargeGas (gVerylow + p.2.extCost [⟨p.1, 32⟩]) p.2 >>= fun d =>
      (d.memRead p.1 32).2.push (Bytes.toB256 (d.memRead p.1 32).1)) = _
  rw [Devm.popToNat_eq_ok h_stk]
  simp only [bind, Except.bind]
  have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨i.toNat, 32⟩] = devm.extCost [⟨i.toNat, 32⟩] := rfl
  rw [h_ext, chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stack_setMach]
  rw [Devm.push_eq_ok
    (devm := (devm.setMach ⟨s, devm.memory,
      devm.gasLeft - (gVerylow + devm.extCost [⟨i.toNat, 32⟩])⟩).memRead
        i.toNat 32 |>.2) h_room]
  rfl

/-- `KECCAK256`, evaluated forward.  The hash is *not* computed here: it stays
`Bytes.keccak` applied to the read window, which the caller either names with a
value obligation or carries symbolically. -/
lemma Rinst.runCore_kec_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {i sz : B256} {s : List B256} (h_stk : devm.stack = i :: sz :: s)
    (h_gas : gKeccak256 + gasKeccak256Word * ceilDiv sz.toNat 32
      + devm.extCost [⟨i.toNat, sz.toNat⟩] ≤ devm.gasLeft)
    (h_room : s.length < 1024) :
    Rinst.runCore pc devm sevm .kec =
      .ok (devm.setMach
        ⟨Bytes.keccak (devm.memory.read i.toNat sz.toNat).1 :: s,
          (devm.memory.read i.toNat sz.toNat).2,
          devm.gasLeft - (gKeccak256 + gasKeccak256Word * ceilDiv sz.toNat 32
            + devm.extCost [⟨i.toNat, sz.toNat⟩])⟩) := by
  show (devm.popToNat >>= fun p => p.2.popToNat >>= fun q =>
    chargeGas (gKeccak256 + gasKeccak256Word * ceilDiv q.1 32
      + q.2.extCost [⟨p.1, q.1⟩]) q.2 >>= fun d =>
        (d.memRead p.1 q.1).2.push (Bytes.keccak (d.memRead p.1 q.1).1)) = _
  rw [Devm.popToNat_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨sz :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨i.toNat, sz.toNat⟩] = devm.extCost [⟨i.toNat, sz.toNat⟩] := rfl
  rw [h_ext, chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stack_setMach]
  rw [Devm.push_eq_ok
    (devm := (devm.setMach ⟨s, devm.memory,
      devm.gasLeft - (gKeccak256 + gasKeccak256Word * ceilDiv sz.toNat 32
        + devm.extCost [⟨i.toNat, sz.toNat⟩])⟩).memRead
          i.toNat sz.toNat |>.2) h_room]
  rfl

/-- `CALLDATACOPY`, evaluated forward.  The copied bytes are
`sevm.data.sliceD`, the same expression `Sevm.dataWord` reads a single word
with, so nothing here models calldata a second time. -/
lemma Rinst.runCore_calldatacopy_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {di si sz : B256} {s : List B256}
    (h_stk : devm.stack = di :: si :: sz :: s)
    (h_gas : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩] ≤ devm.gasLeft) :
    Rinst.runCore pc devm sevm .calldatacopy =
      .ok (devm.setMach
        ⟨s, devm.memory.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0),
          devm.gasLeft - (gVerylow + gasCopy * ceilDiv sz.toNat 32
            + devm.extCost [⟨di.toNat, sz.toNat⟩])⟩) := by
  show (devm.popToNat >>= fun p => p.2.popToNat >>= fun q => q.2.popToNat >>=
    fun r => chargeGas (gVerylow + gasCopy * ceilDiv r.1 32
      + r.2.extCost [⟨p.1, r.1⟩]) r.2 >>= fun d =>
        Except.ok (d.memWrite p.1 (sevm.data.sliceD q.1 r.1 0))) = _
  rw [Devm.popToNat_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨si :: sz :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨sz :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨di.toNat, sz.toNat⟩] = devm.extCost [⟨di.toNat, sz.toNat⟩] := rfl
  rw [h_ext, chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stack_setMach]
  rfl

/-- `CODECOPY`, evaluated forward against the exact current code image. -/
lemma Rinst.runCore_codecopy_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {di si sz : B256} {s : List B256}
    (h_stk : devm.stack = di :: si :: sz :: s)
    (h_gas : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩] ≤ devm.gasLeft) :
    Rinst.runCore pc devm sevm .codecopy =
      .ok (devm.setMach
        ⟨s, devm.memory.write di.toNat
            (sevm.code.sliceD si.toNat sz.toNat (Linst.toUInt8 .stop)),
          devm.gasLeft - (gVerylow + gasCopy * ceilDiv sz.toNat 32
            + devm.extCost [⟨di.toNat, sz.toNat⟩])⟩) := by
  show (devm.popToNat >>= fun p => p.2.popToNat >>= fun q => q.2.popToNat >>=
    fun r => chargeGas (gVerylow + gasCopy * ceilDiv r.1 32
      + r.2.extCost [⟨p.1, r.1⟩]) r.2 >>= fun d =>
        Except.ok (d.memWrite p.1
          (sevm.code.sliceD q.1 r.1 (Linst.toUInt8 .stop)))) = _
  rw [Devm.popToNat_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨si :: sz :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨sz :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨di.toNat, sz.toNat⟩] = devm.extCost [⟨di.toNat, sz.toNat⟩] := rfl
  rw [h_ext, chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stack_setMach]
  rfl

/-- `RETURNDATACOPY`, evaluated forward.  The out-of-bounds guard is a premise,
not a case split: a frame that copies a fixed window out of a child's return
data has already established the length it needs. -/
lemma Rinst.runCore_retdatacopy_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {di ri sz : B256} {s : List B256}
    (h_stk : devm.stack = di :: ri :: sz :: s)
    (h_gas : gVerylow + gReturnDataCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩] ≤ devm.gasLeft)
    (h_bound : ri.toNat + sz.toNat ≤ devm.returnData.length) :
    Rinst.runCore pc devm sevm .retdatacopy =
      .ok (devm.setMach
        ⟨s, devm.memory.write di.toNat
              (devm.returnData.sliceD ri.toNat sz.toNat 0),
          devm.gasLeft - (gVerylow + gReturnDataCopy * ceilDiv sz.toNat 32
            + devm.extCost [⟨di.toNat, sz.toNat⟩])⟩) := by
  show (devm.popToNat >>= fun p => p.2.popToNat >>= fun q => q.2.popToNat >>=
    fun r => chargeGas (gVerylow + gReturnDataCopy * ceilDiv r.1 32
      + r.2.extCost [⟨p.1, r.1⟩]) r.2 >>= fun d =>
        if d.returnData.length < q.1 + r.1 then
          .error ⟨.halt (.outOfBoundsRead .none), d⟩
        else Except.ok (d.memWrite p.1 (d.returnData.sliceD q.1 r.1 0))) = _
  rw [Devm.popToNat_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨ri :: sz :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨sz :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨di.toNat, sz.toNat⟩] = devm.extCost [⟨di.toNat, sz.toNat⟩] := rfl
  rw [h_ext, chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stack_setMach]
  rw [if_neg (by
    show ¬ (Devm.returnData _ ).length < ri.toNat + sz.toNat
    show ¬ devm.returnData.length < ri.toNat + sz.toNat
    omega)]
  rfl

/-- `Devm.popN`, evaluated forward: a stack that starts with `xs` hands them
back in stack order, with the rest below.  `LOG n` is the only instruction that
uses it, and it uses it for the topics. -/
lemma Devm.popN_eq_ok {xs : List B256} : ∀ {s : List B256} {devm : Devm},
    devm.stack = xs ++ s →
    devm.popN xs.length =
      .ok ⟨xs, devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
  induction xs with
  | nil =>
    intro s devm h
    show Devm.popN devm 0 = _
    rw [Devm.popN_def]
    simp only [List.nil_append] at h
    rw [← h]
    rfl
  | cons x xs ih =>
    intro s devm h
    show Devm.popN devm (xs.length + 1) = _
    rw [Devm.popN_def]
    simp only []
    rw [Devm.pop_eq_ok (x := x) (s := xs ++ s) h]
    simp only [bind, Except.bind]
    rw [ih (s := s)
      (devm := devm.setMach ⟨xs ++ s, devm.memory, devm.gasLeft⟩) rfl]
    simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]

/-- `LOG n`, evaluated forward.  The topics come off the stack below the window
operands, the data is the read window, and the entry is appended to
`devm.logs` — so unlike every rule above it, the successor is not a `setMach`
over `devm` but a `setMach` under an `addLog`.

`h_static` is what a `LOG` needs and a read does not: a static frame cannot
emit one at all. -/
lemma Rinst.runCore_log_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {n : Fin 5} {i sz : B256} {topics s : List B256}
    (h_stk : devm.stack = i :: sz :: (topics ++ s))
    (h_len : topics.length = n.val) (h_static : sevm.isStatic = false)
    (h_gas : gLog + gLogdata * sz.toNat + gLogtopic * n.val
      + devm.extCost [⟨i.toNat, sz.toNat⟩] ≤ devm.gasLeft) :
    Rinst.runCore pc devm sevm (.log n) =
      .ok ((devm.setMach ⟨s, (devm.memory.read i.toNat sz.toNat).2,
          devm.gasLeft - (gLog + gLogdata * sz.toNat + gLogtopic * n.val
            + devm.extCost [⟨i.toNat, sz.toNat⟩])⟩).addLog
        ⟨sevm.currentTarget, topics,
          (devm.memory.read i.toNat sz.toNat).1⟩) := by
  show (devm.popToNat >>= fun p => p.2.popToNat >>= fun q =>
    q.2.popN n.val >>= fun t =>
      chargeGas (gLog + gLogdata * q.1 + gLogtopic * n.val
        + t.2.extCost [⟨p.1, q.1⟩]) t.2 >>= fun d =>
          assertDynamic sevm d >>= fun _ =>
            Except.ok ((d.memRead p.1 q.1).2.addLog
              ⟨sevm.currentTarget, t.1, (d.memRead p.1 q.1).1⟩)) = _
  rw [Devm.popToNat_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨sz :: (topics ++ s), devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [← h_len, Devm.popN_eq_ok (xs := topics) (s := s)
    (devm := devm.setMach ⟨topics ++ s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨i.toNat, sz.toNat⟩] = devm.extCost [⟨i.toNat, sz.toNat⟩] := rfl
  rw [h_ext, h_len, chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stack_setMach, assertDynamic, Except.assert, h_static]
  rfl

/-! ### `SSTORE`

The one instruction whose charge is not a function of the opcode: EIP-2200
prices a store by the *original*, *current* and *new* values together, and by
whether the key is already warm.  **A6** of `~/plans/adversarial-progress.md`
fixes how that enters a forward rule: the warmth splits the rule, exactly as it
splits `SLOAD`'s and for the same reason — the cold arm moves the base state and
the warm arm does not — and the value-case arithmetic is a caller-supplied
equation on `sstoreValueCost`, so the trunk (which charges exactly) and a
continuation (which bounds) apply the same rule.

`Rinst.runCore`'s `.sstore` arm also carries two guards no read has: the
EIP-2200 sentry `gCallStipend < gasLeft`, checked *before* any charge, and the
static-context check.  Both are premises. -/

/-- The value-case charge of an `SSTORE`, above whatever the key's warmth adds.
Jaune computes it inline, distributed over the branches; naming it is what makes
the charge a caller-supplied equation rather than a case split inside the
tactic. -/
def sstoreValueCost (orig cur new : B256) : Nat :=
  if orig = cur ∧ cur ≠ new then
    if orig = 0 then gasStorageSet else gasStorageUpdate - gasColdSload
  else gasWarmAccess

/-- Jaune's distributed form, collected: whatever the key's warmth contributes,
the value cases add `sstoreValueCost` on top of it. -/
lemma sstoreValueCost_add {a : Nat} {orig cur new : B256} :
    (if orig = cur ∧ cur ≠ new then
      (if orig = 0 then a + gasStorageSet
        else a + (gasStorageUpdate - gasColdSload))
      else a + gasWarmAccess) = a + sstoreValueCost orig cur new := by
  rw [sstoreValueCost]; split_ifs <;> rfl

/-- `SSTORE` on a cold key, evaluated forward.  The key joins the accessed set —
so, as with `SLOAD`, the base state moves once here — and the charge is
`gasColdSload` plus the value case. -/
lemma Rinst.runCore_sstore_cold_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {k v : B256} {s : List B256} {c : Nat} {rc : Int}
    (h_stk : devm.stack = k :: v :: s)
    (h_cold : ⟨sevm.currentTarget, k⟩ ∉ devm.accessedStorageKeys)
    (h_sentry : gCallStipend < devm.gasLeft) (h_static : sevm.isStatic = false)
    (h_cost : sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v = c)
    (h_refund : sstoreNewRefundCounter v
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) devm.refundCounter = rc)
    (h_gas : gasColdSload + c ≤ devm.gasLeft) :
    Rinst.runCore pc devm sevm .sstore =
      .ok ((((addAccessedStorageKey devm sevm.currentTarget k).withRefundCounter
        rc).setMach
          ⟨s, devm.memory, devm.gasLeft - (gasColdSload + c)⟩).setStorVal
            sevm.currentTarget k v) := by
  subst h_cost; subst h_refund
  rw [show Rinst.runCore pc devm sevm .sstore = (do
      let ⟨key, d⟩ ← devm.pop
      let ⟨new_value, d⟩ ← d.pop
      .assert (gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
      let ct := sevm.currentTarget
      let original_value := getOrigStorVal sevm ct key
      let current_value := d.getStorVal ct key
      let ⟨d, gasCost2⟩ ← Except.ok <|
        if ⟨ct, key⟩ ∉ d.accessedStorageKeys then
          ( ⟨addAccessedStorageKey d ct key, gasColdSload⟩ : Devm × Nat )
        else ⟨d, 0⟩
      let gasCost3 ← Except.ok <|
        if original_value = current_value ∧ current_value ≠ new_value then
          if original_value = 0 then gasCost2 + gasStorageSet
          else gasCost2 + (gasStorageUpdate - gasColdSload)
        else gasCost2 + gasWarmAccess
      let d ← Except.ok <| d.withRefundCounter
        (sstoreNewRefundCounter new_value original_value current_value
          d.refundCounter)
      let d ← chargeGas gasCost3 d
      assertDynamic sevm d
      .ok (d.setStorVal sevm.currentTarget key new_value)) from rfl]
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach ⟨v :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Except.assert, if_pos (show gCallStipend < devm.gasLeft from h_sentry)]
  simp only []
  rw [if_pos (show ⟨sevm.currentTarget, k⟩ ∉
    (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedStorageKeys
    from h_cold)]
  simp only [sstoreValueCost_add]
  -- The popped state's world projections are the pre-state's; naming them so
  -- lets `chargeGas_eq_ok` match syntactically rather than only up to `rfl`.
  rw [show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).getStorVal
        sevm.currentTarget k = devm.getStorVal sevm.currentTarget k from rfl,
    show (addAccessedStorageKey (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        sevm.currentTarget k).refundCounter = devm.refundCounter from rfl]
  rw [chargeGas_eq_ok
    (devm := ((addAccessedStorageKey
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) sevm.currentTarget
        k).withRefundCounter
      (sstoreNewRefundCounter v (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) devm.refundCounter)))
    (by
      show gasColdSload + sstoreValueCost _ _ _ ≤ devm.gasLeft
      exact h_gas)]
  simp only [assertDynamic, Except.assert, h_static]
  rfl

/-- `SSTORE` on a warm key.  Nothing joins the accessed set, so the base state
does not move and the charge is the value case alone. -/
lemma Rinst.runCore_sstore_warm_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {k v : B256} {s : List B256} {c : Nat} {rc : Int}
    (h_stk : devm.stack = k :: v :: s)
    (h_warm : ⟨sevm.currentTarget, k⟩ ∈ devm.accessedStorageKeys)
    (h_sentry : gCallStipend < devm.gasLeft) (h_static : sevm.isStatic = false)
    (h_cost : sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v = c)
    (h_refund : sstoreNewRefundCounter v
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) devm.refundCounter = rc)
    (h_gas : c ≤ devm.gasLeft) :
    Rinst.runCore pc devm sevm .sstore =
      .ok (((devm.withRefundCounter rc).setMach
        ⟨s, devm.memory, devm.gasLeft - c⟩).setStorVal
          sevm.currentTarget k v) := by
  subst h_cost; subst h_refund
  rw [show Rinst.runCore pc devm sevm .sstore = (do
      let ⟨key, d⟩ ← devm.pop
      let ⟨new_value, d⟩ ← d.pop
      .assert (gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
      let ct := sevm.currentTarget
      let original_value := getOrigStorVal sevm ct key
      let current_value := d.getStorVal ct key
      let ⟨d, gasCost2⟩ ← Except.ok <|
        if ⟨ct, key⟩ ∉ d.accessedStorageKeys then
          ( ⟨addAccessedStorageKey d ct key, gasColdSload⟩ : Devm × Nat )
        else ⟨d, 0⟩
      let gasCost3 ← Except.ok <|
        if original_value = current_value ∧ current_value ≠ new_value then
          if original_value = 0 then gasCost2 + gasStorageSet
          else gasCost2 + (gasStorageUpdate - gasColdSload)
        else gasCost2 + gasWarmAccess
      let d ← Except.ok <| d.withRefundCounter
        (sstoreNewRefundCounter new_value original_value current_value
          d.refundCounter)
      let d ← chargeGas gasCost3 d
      assertDynamic sevm d
      .ok (d.setStorVal sevm.currentTarget key new_value)) from rfl]
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach ⟨v :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Except.assert, if_pos (show gCallStipend < devm.gasLeft from h_sentry)]
  simp only []
  rw [if_neg (show ¬ (⟨sevm.currentTarget, k⟩ ∉
    (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedStorageKeys)
    from fun h => h h_warm)]
  simp only [Nat.zero_add]
  rw [show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).getStorVal
        sevm.currentTarget k = devm.getStorVal sevm.currentTarget k from rfl,
    show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).refundCounter
        = devm.refundCounter from rfl]
  rw [chargeGas_eq_ok
    (devm := (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).withRefundCounter
      (sstoreNewRefundCounter v (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) devm.refundCounter))
    (by
      show sstoreValueCost _ _ _ ≤ devm.gasLeft
      exact h_gas)]
  simp only [assertDynamic, Except.assert, h_static]
  rfl

/-! ## The one-word memory window

`MSTORE` a word at offset 0 and `RETURN` it is how every Blanc view answers, and
the two gas charges and the read-back are the same three facts every time.  They
are stated here rather than in a contract module because nothing in them names a
contract: the word is arbitrary and the offset is the ABI's. -/

/-- Writing one word into empty memory leaves exactly one word. -/
lemma Mem.size_write_word {w : B256} :
    (Mem.empty.write 0 w.toBytes).size = 32 := by
  rcases hb : w.toBytes with _ | ⟨b, bs⟩
  · exact absurd (hb ▸ B256.length_toBytes w) (by simp)
  · have hlen : (b :: bs).length = 32 := hb ▸ B256.length_toBytes w
    simp only [Mem.write, Mem.empty, hlen, if_neg (by simp : ¬ (0 + 32 ≤ 0))]
    rfl

/-- And reading that word back gives it unchanged: `Mem.Reads` carries the image
across the write, and a `B256` is exactly the window's width. -/
lemma Mem.read_write_word {w : B256} :
    ((Mem.empty.write 0 w.toBytes).read 0 32).1 = w.toBytes := by
  have h_reads : Mem.Reads (Mem.empty.write 0 w.toBytes) w.toBytes := by
    have h := Mem.Reads.write Mem.wf_empty Mem.reads_empty 0 w.toBytes
    rw [show Bytes.writeAt [] 0 w.toBytes = w.toBytes by simp [Bytes.writeAt]] at h
    exact h
  rw [Mem.Reads.read h_reads 0 32]
  show List.takeD 32 (List.drop 0 w.toBytes) 0 = w.toBytes
  rw [List.drop_zero, List.takeD_eq_self 0 (B256.length_toBytes w).symm]

/-- Expanding empty memory to one word costs `gMemory`: the quadratic term is
`1 / 512`. -/
lemma Devm.extCost_empty_word {devm : Devm} {S : List B256} {G : Nat} :
    (devm.setMach ⟨S, Mem.empty, G⟩).extCost [⟨0, 32⟩] = gMemory := by
  simp [Devm.extCost, Devm.memory_setMach, memExtsSize, memExtSize,
    calculateMemoryGasCost, ceilDiv, Mem.empty, gMemory]

/-- Reading a window memory already covers is free. -/
lemma Devm.extCost_word_word {devm : Devm} {S : List B256} {N : Mem} {G : Nat}
    (h : N.size = 32) :
    (devm.setMach ⟨S, N, G⟩).extCost [⟨0, 32⟩] = 0 := by
  simp [Devm.extCost, Devm.memory_setMach, memExtsSize, memExtSize,
    calculateMemoryGasCost, ceilDiv, h, gMemory]

/-- `Mem.read_write_word` at the `Devm` altitude, in the exact shape
`Func.RunCompiled`'s `.last .ret` premise wants.

Both the altitude and the `devm.memory` premise are load-bearing, and each cost
a measured half-minute of elaboration to find.  `Devm.memRead` returns a
`Bytes × Devm` where `Mem.read` returns a `Bytes × Mem`, so handing the unifier
the `Mem`-level fact sends it looking for a way to identify the two types.  And
writing the memory image *into* the conclusion rather than as `devm.memory`
makes the unifier reduce `Devm.memory devm` to weak head normal form, which
runs the whole 32-byte `Mem.write` symbolically. -/
lemma Devm.memRead_word_fst {devm : Devm} {S : List B256} {G : Nat} {w : B256}
    (hm : devm.memory = Mem.empty.write 0 w.toBytes) :
    ((devm.setMach ⟨S, devm.memory, G⟩).memRead 0 32).1 = w.toBytes := by
  show ((devm.setMach ⟨S, devm.memory, G⟩).memory.read 0 32).1 = w.toBytes
  rw [Devm.memory_setMach]
  show ((devm.memory).read 0 32).1 = w.toBytes
  rw [hm]
  exact Mem.read_write_word

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

/-- A fixed-width raw `PUSH`, retaining the exact immediate bytes. -/
lemma Ninst.runCompiled_pushBytes {sevm : Sevm} {devm : Devm}
    {xs : Bytes} {le : xs.length ≤ 32} {c G : Nat}
    (h_cost : pushCost xs = c)
    (h_gas : devm.gasLeft = G + c)
    (h_room : devm.stack.length < 1024) :
    Ninst.RunCompiled sevm devm (.push xs le)
      (devm.setMach ⟨xs.toB256 :: devm.stack, devm.memory, G⟩) := by
  subst c
  have h_eq : devm.gasLeft - pushCost xs = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_push (by omega) h_room

/-- A full-width word immediate is nonempty, costs `gVerylow`, and pushes the
word itself without normalizing its 32-byte image. -/
lemma pushCost_toBytes (w : B256) : pushCost w.toBytes = gVerylow := by
  rw [pushCost, if_neg]
  intro h
  have hlen := B256.length_toBytes w
  rw [h] at hlen
  simp at hlen

/-- The fixed-width 32-byte form of a word push.  This is distinct from
`Ninst.pushB256`: it retains leading zero bytes in the compiled immediate. -/
lemma Ninst.runCompiled_pushB256Full {sevm : Sevm} {devm : Devm} {w : B256}
    {le : w.toBytes.length ≤ 32} {G : Nat}
    (h_gas : devm.gasLeft = G + gVerylow)
    (h_room : devm.stack.length < 1024) :
    Ninst.RunCompiled sevm devm (.push w.toBytes le)
      (devm.setMach ⟨w :: devm.stack, devm.memory, G⟩) := by
  have h := Ninst.runCompiled_pushBytes
    (sevm := sevm) (devm := devm) (xs := w.toBytes) (le := le)
    (c := gVerylow) (G := G) (pushCost_toBytes w) h_gas h_room
  simpa only [B256.toB256_toBytes] using h

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

/-- A register opcode that pushes a word the frame already determines:
`ADDRESS`, `CALLER`, `CALLVALUE`, `ORIGIN`, `CALLDATASIZE`, `CODESIZE`,
`BASEFEE`, and every other arm `Rinst.runCore` sends through `pushItem`.

`h_def` is what selects the opcode, exactly as it does for
`Ninst.runCompiled_unary` and `_binary`, and it is `rfl` at every one of them.

**No `h_val` and no hint**, for `Ninst.runCompiled_calldataload`'s reason: `x`
is not a computation the walk has to be told the answer to, it is a projection
of `sevm` or `devm` that `h_def` already names.  A wrapper that consumed a hint
here would silently eat the hint the *next* value-producing opcode was given. -/
lemma Ninst.runCompiled_pushItem {sevm : Sevm} {devm : Devm} {r : Rinst}
    {x : B256} {cost G : Nat} (h_ne : r ≠ .pc)
    (h_def : Rinst.runCore 0 devm sevm r = pushItem x cost devm)
    (h_gas : devm.gasLeft = G + cost) (h_room : devm.stack.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg r)
      (devm.setMach ⟨x :: devm.stack, devm.memory, G⟩) := by
  have h_eq : devm.gasLeft - cost = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg h_ne
    (h_def.trans (pushItem_eq_ok (by omega) h_room))

/-- `EXTCODESIZE` on a cold account.  Besides the exact gas charge, the
successor records that the queried address has become warm. -/
lemma Ninst.runCompiled_extcodesize_cold {sevm : Sevm} {devm : Devm}
    {x v : B256} {s : List B256} {G : Nat}
    (h_stk : devm.stack = x :: s)
    (h_cold : x.toAdr ∉ devm.accessedAddresses)
    (h_val : (devm.getCode x.toAdr).size.toB256 = v)
    (h_gas : devm.gasLeft = G + gasColdAccountAccess)
    (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg .extcodesize)
      ((addAccessedAddress devm x.toAdr).setMach
        ⟨v :: s, devm.memory, G⟩) := by
  subst h_val
  have h_eq : devm.gasLeft - gasColdAccountAccess = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_extcodesize_cold_eq_ok h_stk h_cold (by omega) h_room)

/-- `EXTCODESIZE` on a warm account.  No access-list field moves. -/
lemma Ninst.runCompiled_extcodesize_warm {sevm : Sevm} {devm : Devm}
    {x v : B256} {s : List B256} {G : Nat}
    (h_stk : devm.stack = x :: s)
    (h_warm : x.toAdr ∈ devm.accessedAddresses)
    (h_val : (devm.getCode x.toAdr).size.toB256 = v)
    (h_gas : devm.gasLeft = G + gasWarmAccess)
    (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg .extcodesize)
      (devm.setMach ⟨v :: s, devm.memory, G⟩) := by
  subst h_val
  have h_eq : devm.gasLeft - gasWarmAccess = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_extcodesize_warm_eq_ok h_stk h_warm (by omega) h_room)

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

/-- `SLOAD` on a warm key.  Unlike the cold case the base state does *not*
move: nothing is added to the accessed set, so the successor is an ordinary
`setMach` over `devm` and the rest of the chain continues over the same base.

Separate from `Ninst.runCompiled_sload_cold` for the reason
`Rinst.runCore_sload_cold_eq_ok`'s docstring gives and
`Rinst.runCore_sload_warm_eq_ok`'s repeats.  The argument order mirrors the
cold lemma's exactly, so `func_run`'s two arms differ only in which lemma they
name, which charge they subtract, and whether the base moves. -/
lemma Ninst.runCompiled_sload_warm {sevm : Sevm} {devm : Devm} {k v : B256}
    {s : List B256} {G : Nat} (h_stk : devm.stack = k :: s)
    (h_warm : ⟨sevm.currentTarget, k⟩ ∈ devm.accessedStorageKeys)
    (h_val : devm.getStorVal sevm.currentTarget k = v)
    (h_gas : devm.gasLeft = G + gasWarmAccess) (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg .sload)
      (devm.setMach ⟨v :: s, devm.memory, G⟩) := by
  subst h_val
  have h_eq : devm.gasLeft - gasWarmAccess = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_sload_warm_eq_ok h_stk h_warm (by omega) h_room)

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

/-- `MSTORE` with the expansion charge named.  `Ninst.runCompiled_mstore` leaves
`Devm.extCost` inside the gas premise, which a caller can discharge but a
*generator* cannot: to name the successor's gas account it has to know the
charge as a number first.  This form splits the two, so the arithmetic premise
is mechanical and only `h_ext` carries the memory reasoning. -/
lemma Ninst.runCompiled_mstore_of {sevm : Sevm} {devm : Devm} {i v : B256}
    {s : List B256} {G e : Nat} {M : Mem} (h_stk : devm.stack = i :: v :: s)
    (h_ext : devm.extCost [⟨i.toNat, 32⟩] = e)
    (h_gas : devm.gasLeft = G + (gVerylow + e))
    (h_write : devm.memory.write i.toNat v.toBytes = M) :
    Ninst.RunCompiled sevm devm (.reg .mstore) (devm.setMach ⟨s, M, G⟩) := by
  subst h_ext
  exact Ninst.runCompiled_mstore h_stk h_gas h_write

/-! ### The mutators and the stack shufflers, in the step interface

Four of the rules below charge for a memory window, and every one of them takes
its **whole** charge as a single named `Nat` — `h_cost` — rather than naming the
expansion term the way `Ninst.runCompiled_mstore_of` does.  `MSTORE`'s charge is
`gVerylow` plus one expansion; a copy's or a hash's is a fee-schedule constant
plus a per-word term plus an expansion, and splitting a three-term sum across
three premises would give the walk three obligations where the caller has one
number.  One hint per instruction, one obligation per instruction.

Each successor is written with the `setMach` **outermost**, including the two
whose base moves (`LOG`'s `addLog`, `SSTORE`'s accessed-set, refund-counter and
storage writes).  That is not cosmetic either: the walk reads the state it is
standing on with `parseState`, which recognises `base.setMach ⟨_, _, _⟩` and
nothing else, so a successor written the other way round would break the chain
at the next instruction.  The two orders are definitionally equal — `setMach`
touches `mach`, the others touch `meta` or `world`. -/

/-- `POP`. -/
lemma Ninst.runCompiled_pop {sevm : Sevm} {devm : Devm} {x : B256}
    {s : List B256} {G : Nat} (h_stk : devm.stack = x :: s)
    (h_gas : devm.gasLeft = G + gBase) :
    Ninst.RunCompiled sevm devm (.reg .pop)
      (devm.setMach ⟨s, devm.memory, G⟩) := by
  have h_eq : devm.gasLeft - gBase = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_pop_eq_ok h_stk (by omega))

/-- `SWAP n`.  The permuted stack is named by the caller; on a literal stack
`h_swap` is a `rfl`. -/
lemma Ninst.runCompiled_swap {sevm : Sevm} {devm : Devm} {n : Fin 16}
    {S : List B256} {G : Nat} (h_swap : List.swap devm.stack n.val = some S)
    (h_gas : devm.gasLeft = G + gVerylow) :
    Ninst.RunCompiled sevm devm (.reg (.swap n))
      (devm.setMach ⟨S, devm.memory, G⟩) := by
  have h_eq : devm.gasLeft - gVerylow = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_swap_eq_ok h_swap (by omega))

/-- `GAS`.  **No value parameter**: the word pushed is the successor's own gas
account, so in the additive form it is literally `G`.  That is what makes this
instruction the one a `CALL` site can reason about — the frame learns its own
remaining gas as a name it already has. -/
lemma Ninst.runCompiled_gas {sevm : Sevm} {devm : Devm} {G : Nat}
    (h_gas : devm.gasLeft = G + gBase) (h_room : devm.stack.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg .gas)
      (devm.setMach ⟨G.toB256 :: devm.stack, devm.memory, G⟩) := by
  have h_eq : devm.gasLeft - gBase = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_gas_eq_ok (by omega) h_room)

/-- `MLOAD`.  The read's own two components are named: `v` is the word and `M`
the window-extended image. -/
lemma Ninst.runCompiled_mload_of {sevm : Sevm} {devm : Devm} {i v : B256}
    {s : List B256} {c G : Nat} {M : Mem} (h_stk : devm.stack = i :: s)
    (h_cost : gVerylow + devm.extCost [⟨i.toNat, 32⟩] = c)
    (h_val : Bytes.toB256 (devm.memory.read i.toNat 32).1 = v)
    (h_mem : (devm.memory.read i.toNat 32).2 = M)
    (h_gas : devm.gasLeft = G + c) (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg .mload)
      (devm.setMach ⟨v :: s, M, G⟩) := by
  subst h_cost; subst h_val; subst h_mem
  have h_eq :
      devm.gasLeft - (gVerylow + devm.extCost [⟨i.toNat, 32⟩]) = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_mload_eq_ok h_stk (by omega) h_room)

/-- `KECCAK256`.  `h_val` is the hash: it is the caller's to justify, and
nothing in this layer evaluates `Bytes.keccak`. -/
lemma Ninst.runCompiled_kec_of {sevm : Sevm} {devm : Devm} {i sz v : B256}
    {s : List B256} {c G : Nat} {M : Mem} (h_stk : devm.stack = i :: sz :: s)
    (h_cost : gKeccak256 + gasKeccak256Word * ceilDiv sz.toNat 32
      + devm.extCost [⟨i.toNat, sz.toNat⟩] = c)
    (h_val : Bytes.keccak (devm.memory.read i.toNat sz.toNat).1 = v)
    (h_mem : (devm.memory.read i.toNat sz.toNat).2 = M)
    (h_gas : devm.gasLeft = G + c) (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg .kec)
      (devm.setMach ⟨v :: s, M, G⟩) := by
  subst h_cost; subst h_val; subst h_mem
  have h_eq : devm.gasLeft - (gKeccak256 + gasKeccak256Word * ceilDiv sz.toNat 32
      + devm.extCost [⟨i.toNat, sz.toNat⟩]) = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_kec_eq_ok h_stk (by omega) h_room)

/-- `CALLDATACOPY`. -/
lemma Ninst.runCompiled_calldatacopy_of {sevm : Sevm} {devm : Devm}
    {di si sz : B256} {s : List B256} {c G : Nat} {M : Mem}
    (h_stk : devm.stack = di :: si :: sz :: s)
    (h_cost : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩] = c)
    (h_write : devm.memory.write di.toNat
      (sevm.data.sliceD si.toNat sz.toNat 0) = M)
    (h_gas : devm.gasLeft = G + c) :
    Ninst.RunCompiled sevm devm (.reg .calldatacopy)
      (devm.setMach ⟨s, M, G⟩) := by
  subst h_cost; subst h_write
  have h_eq : devm.gasLeft - (gVerylow + gasCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩]) = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_calldatacopy_eq_ok h_stk (by omega))

/-- `CODECOPY`. -/
lemma Ninst.runCompiled_codecopy_of {sevm : Sevm} {devm : Devm}
    {di si sz : B256} {s : List B256} {c G : Nat} {M : Mem}
    (h_stk : devm.stack = di :: si :: sz :: s)
    (h_cost : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩] = c)
    (h_write : devm.memory.write di.toNat
      (sevm.code.sliceD si.toNat sz.toNat (Linst.toUInt8 .stop)) = M)
    (h_gas : devm.gasLeft = G + c) :
    Ninst.RunCompiled sevm devm (.reg .codecopy)
      (devm.setMach ⟨s, M, G⟩) := by
  subst h_cost; subst h_write
  have h_eq : devm.gasLeft - (gVerylow + gasCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩]) = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_codecopy_eq_ok h_stk (by omega))

/-- `RETURNDATACOPY`.  `h_bound` is the out-of-bounds guard, as a premise. -/
lemma Ninst.runCompiled_retdatacopy_of {sevm : Sevm} {devm : Devm}
    {di ri sz : B256} {s : List B256} {c G : Nat} {M : Mem}
    (h_stk : devm.stack = di :: ri :: sz :: s)
    (h_cost : gVerylow + gReturnDataCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩] = c)
    (h_bound : ri.toNat + sz.toNat ≤ devm.returnData.length)
    (h_write : devm.memory.write di.toNat
      (devm.returnData.sliceD ri.toNat sz.toNat 0) = M)
    (h_gas : devm.gasLeft = G + c) :
    Ninst.RunCompiled sevm devm (.reg .retdatacopy)
      (devm.setMach ⟨s, M, G⟩) := by
  subst h_cost; subst h_write
  have h_eq : devm.gasLeft - (gVerylow + gReturnDataCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩]) = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_retdatacopy_eq_ok h_stk (by omega) h_bound)

/-- `LOG n`.  The successor's base carries the appended entry; the `setMach`
stays outermost so the walk can go on standing on it. -/
lemma Ninst.runCompiled_log_of {sevm : Sevm} {devm : Devm} {n : Fin 5}
    {i sz : B256} {topics s : List B256} {c G : Nat} {M : Mem} {data : Bytes}
    (h_stk : devm.stack = i :: sz :: (topics ++ s))
    (h_len : topics.length = n.val) (h_static : sevm.isStatic = false)
    (h_cost : gLog + gLogdata * sz.toNat + gLogtopic * n.val
      + devm.extCost [⟨i.toNat, sz.toNat⟩] = c)
    (h_data : (devm.memory.read i.toNat sz.toNat).1 = data)
    (h_mem : (devm.memory.read i.toNat sz.toNat).2 = M)
    (h_gas : devm.gasLeft = G + c) :
    Ninst.RunCompiled sevm devm (.reg (.log n))
      ((devm.addLog ⟨sevm.currentTarget, topics, data⟩).setMach
        ⟨s, M, G⟩) := by
  subst h_cost; subst h_data; subst h_mem
  have h_eq : devm.gasLeft - (gLog + gLogdata * sz.toNat + gLogtopic * n.val
      + devm.extCost [⟨i.toNat, sz.toNat⟩]) = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_log_eq_ok h_stk h_len h_static (by omega))

/-- `SSTORE` on a cold key.  Three premises no read has — the EIP-2200 sentry,
the static-context check and the value-case charge — and a base state that moves
three times.  `h_cost` is the whole charge, `gasColdSload` included. -/
lemma Ninst.runCompiled_sstore_cold {sevm : Sevm} {devm : Devm} {k v : B256}
    {s : List B256} {c G : Nat} {rc : Int} (h_stk : devm.stack = k :: v :: s)
    (h_cold : ⟨sevm.currentTarget, k⟩ ∉ devm.accessedStorageKeys)
    (h_sentry : gCallStipend < devm.gasLeft) (h_static : sevm.isStatic = false)
    (h_cost : gasColdSload
      + sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
          (devm.getStorVal sevm.currentTarget k) v = c)
    (h_refund : sstoreNewRefundCounter v
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) devm.refundCounter = rc)
    (h_gas : devm.gasLeft = G + c) :
    Ninst.RunCompiled sevm devm (.reg .sstore)
      ((((addAccessedStorageKey devm sevm.currentTarget k).withRefundCounter
        rc).setStorVal sevm.currentTarget k v).setMach
          ⟨s, devm.memory, G⟩) := by
  subst h_cost
  have h_eq : devm.gasLeft - (gasColdSload
      + sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v) = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_sstore_cold_eq_ok h_stk h_cold h_sentry h_static rfl h_refund
      (by omega))

/-- `SSTORE` on a warm key.  The accessed set does not move, so `h_cost` is the
value case alone. -/
lemma Ninst.runCompiled_sstore_warm {sevm : Sevm} {devm : Devm} {k v : B256}
    {s : List B256} {c G : Nat} {rc : Int} (h_stk : devm.stack = k :: v :: s)
    (h_warm : ⟨sevm.currentTarget, k⟩ ∈ devm.accessedStorageKeys)
    (h_sentry : gCallStipend < devm.gasLeft) (h_static : sevm.isStatic = false)
    (h_cost : sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v = c)
    (h_refund : sstoreNewRefundCounter v
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) devm.refundCounter = rc)
    (h_gas : devm.gasLeft = G + c) :
    Ninst.RunCompiled sevm devm (.reg .sstore)
      (((devm.withRefundCounter rc).setStorVal sevm.currentTarget k v).setMach
        ⟨s, devm.memory, G⟩) := by
  subst h_cost
  have h_eq : devm.gasLeft
      - sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v = G := by omega
  rw [← h_eq]
  exact Ninst.runCompiled_reg (by rintro ⟨⟩)
    (Rinst.runCore_sstore_warm_eq_ok h_stk h_warm h_sentry h_static rfl h_refund
      (by omega))

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

/-- `RETURN` with the read window's charge named, for the same reason
`Ninst.runCompiled_mstore_of` exists: the successor's gas account cannot be
written until the charge is a number. -/
lemma Func.runCompiled_ret_of {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i sz : B256} {s : List B256} {out : Bytes} {d' : Devm} {G e : Nat}
    (h_stk : devm.stack = i :: sz :: s)
    (h_ext : devm.extCost [⟨i.toNat, sz.toNat⟩] = e)
    (h_gas : devm.gasLeft = G + e)
    (h_read : (devm.setMach ⟨s, devm.memory, G⟩).memRead i.toNat sz.toNat
      = ⟨out, d'⟩) :
    Func.RunCompiled fs sevm devm (.last .ret) (d'.withOutput out) := by
  subst h_ext
  exact Func.runCompiled_ret h_stk h_gas h_read

/-- `RETURN` again, with the read-back reduced to its *first* component.  The
pairing happens inside the lemma, where both sides are variables; done at the
call site instead, `Prod.ext`'s second `rfl` forces the unifier through
`Devm.memRead` on a concrete memory image. -/
lemma Func.runCompiled_ret_word {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i sz : B256} {s : List B256} {out : Bytes} {G e : Nat}
    (h_stk : devm.stack = i :: sz :: s)
    (h_ext : devm.extCost [⟨i.toNat, sz.toNat⟩] = e)
    (h_gas : devm.gasLeft = G + e)
    (h_out : ((devm.setMach ⟨s, devm.memory, G⟩).memRead i.toNat sz.toNat).1
      = out) :
    Func.RunCompiled fs sevm devm (.last .ret)
      (((devm.setMach ⟨s, devm.memory, G⟩).memRead i.toNat sz.toNat).2.withOutput
        out) :=
  Func.runCompiled_ret_of h_stk h_ext h_gas (Prod.ext h_out rfl)

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

/-! ## Inspecting a successful compiler result

The compiler's `Option` binds and branch guards are useful at generation time,
but force an eager walk over a complete program when a downstream proof only
needs a finite byte slice.  The emitter below removes only those already-
discharged checks.  Its equivalence theorem requires the ordinary compiler's
successful result, so it is an inspection view of `compile`, not a second
compiler or an additional source of bytecode truth. -/

/-- Emit a function after table locations and compiler success are known.
Branch destinations use the source function's exact byte size; compiler
success proves this is the recursively emitted left arm's length. -/
def Func.emitUnchecked (locations : List Nat) (n : Nat) : Func → Bytes
  | .last o => [o.toUInt8]
  | .next i p =>
      Ninst.toBytes i ++ Func.emitUnchecked locations (n + i.size) p
  | .branch p q =>
      let pbs := Func.emitUnchecked locations (n + 4) p
      let loc := n + compsize p + 4
      ([0x61] : Bytes) ++ [(loc >>> 8).toUInt8, loc.toUInt8] ++
        [Jinst.toUInt8 .jumpi] ++ pbs ++
        [Jinst.toUInt8 .jumpdest] ++ Func.emitUnchecked locations (loc + 1) q
  | .call k =>
      let loc := locations.getD k 0
      ([0x61] : Bytes) ++ [(loc >>> 8).toUInt8, loc.toUInt8] ++
        [Jinst.toUInt8 .jump]

/-- Emit a table after its compiler checks have succeeded. -/
def Table.emitUnchecked (locations : List Nat) :
    List (Nat × Func) → Bytes
  | [] => []
  | (n, p) :: rest =>
      Jinst.toUInt8 .jumpdest ::
        Func.emitUnchecked locations (n + 1) p ++
          Table.emitUnchecked locations rest

/-- The unchecked inspection view of a complete program's emitted bytes. -/
def Prog.emitUnchecked (p : Prog) : Bytes :=
  let t := table 0 (p.main :: p.aux)
  Table.emitUnchecked (t.map Prod.fst) t

/-! ### Shape-indexed inspection

`emitUnchecked` is already equivalent to the compiler under a success witness.
For interval proofs it is useful to expose the compiler shape as a separate
argument: two programs with the same shape then share branch offsets and table
locations syntactically, while their instruction bytes remain visible. -/

/-- Exact byte size carried by a compiler shape. -/
def Func.CompileShape.byteSize : Func.CompileShape → Nat
  | .last => 1
  | .next size rest => rest.byteSize + size
  | .branch left right => left.byteSize + right.byteSize + 5
  | .call _ => 4

theorem Func.CompileShape.byteSize_compileShape (p : Func) :
    p.compileShape.byteSize = compsize p := by
  induction p with
  | last => rfl
  | next i p ih =>
      simp [Func.compileShape, Func.CompileShape.byteSize, compsize, ih,
        Ninst.size_eq_length_toBytes]
  | branch p q ihp ihq =>
      simp [Func.compileShape, Func.CompileShape.byteSize, compsize, ihp, ihq]
  | call => rfl

/-- Emit opcode contents while taking all layout decisions from an explicit
compiler shape.  Mismatched arguments are outside the proved use case and are
padded with zero bytes to the exact width carried by the shape. -/
def Func.emitByShape (locations : List Nat) (n : Nat)
    (shape : Func.CompileShape) : Func → Bytes
  | .last o =>
      match shape with
      | .last => [o.toUInt8]
      | _ => List.replicate shape.byteSize 0
  | .next i rest =>
      match shape with
      | .next size restShape =>
          List.takeD size (Ninst.toBytes i) 0 ++
            emitByShape locations (n + size) restShape rest
      | _ => List.replicate shape.byteSize 0
  | .branch left right =>
      match shape with
      | .branch leftShape rightShape =>
          let loc := n + leftShape.byteSize + 4
          let header : Bytes :=
            [0x61, (loc >>> 8).toUInt8, loc.toUInt8,
              Jinst.toUInt8 .jumpi]
          header ++
            emitByShape locations (n + 4) leftShape left ++
            [Jinst.toUInt8 .jumpdest] ++
            emitByShape locations (loc + 1) rightShape right
      | _ => List.replicate shape.byteSize 0
  | .call _ =>
      match shape with
      | .call k =>
          let loc := locations.getD k 0
          ([0x61] : Bytes) ++ [(loc >>> 8).toUInt8, loc.toUInt8] ++
            [Jinst.toUInt8 .jump]
      | _ => List.replicate shape.byteSize 0

private lemma List.length_takeD_exact {α} (n : Nat) (xs : List α) (d : α) :
    (List.takeD n xs d).length = n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      simp only [List.takeD_succ, List.length_cons]
      rw [ih]

/-- Shape-indexed emission always has the byte width carried by the shape.
This is the lazy boundary interval proofs use to skip an off-slice subtree. -/
theorem Func.length_emitByShape (locations : List Nat) (n : Nat)
    (shape : Func.CompileShape) (p : Func) :
    (Func.emitByShape locations n shape p).length = shape.byteSize := by
  induction p generalizing n shape with
  | last o =>
      cases shape <;>
        simp [Func.emitByShape, Func.CompileShape.byteSize]
  | next i p ih =>
      cases shape <;>
        simp [Func.emitByShape, Func.CompileShape.byteSize, ih, Nat.add_comm]
  | branch p q ihp ihq =>
      cases shape <;>
        simp [Func.emitByShape, Func.CompileShape.byteSize, ihp, ihq,
          Nat.add_assoc]
  | call k =>
      cases shape <;>
        simp [Func.emitByShape, Func.CompileShape.byteSize]

private lemma List.getD_append_inspect {α} (xs ys : List α)
    (i : Nat) (d : α) :
    (xs ++ ys).getD i d =
      if i < xs.length then xs.getD i d
      else ys.getD (i - xs.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

/-- Read one emitted byte without constructing any off-index subtree.  The
shape supplies exact segment widths, so evaluation follows only the branch
containing `i`. -/
def Func.byteAtByShape (locations : List Nat) (n : Nat)
    (shape : Func.CompileShape) : Func → Nat → UInt8 → UInt8
  | .last o, i, d =>
      match shape with
      | .last => [o.toUInt8].getD i d
      | _ => (List.replicate shape.byteSize 0).getD i d
  | .next inst rest, i, d =>
      match shape with
      | .next size restShape =>
          if i < size then
            (List.takeD size (Ninst.toBytes inst) 0).getD i d
          else
            byteAtByShape locations (n + size) restShape rest (i - size) d
      | _ => (List.replicate shape.byteSize 0).getD i d
  | .branch left right, i, d =>
      match shape with
      | .branch leftShape rightShape =>
          let loc := n + leftShape.byteSize + 4
          let header : Bytes :=
            [0x61, (loc >>> 8).toUInt8, loc.toUInt8,
              Jinst.toUInt8 .jumpi]
          if i < header.length then header.getD i d
          else
            let i := i - header.length
            if i < leftShape.byteSize then
              byteAtByShape locations (n + 4) leftShape left i d
            else
              let i := i - leftShape.byteSize
              if i < 1 then [Jinst.toUInt8 .jumpdest].getD i d
              else
                byteAtByShape locations (loc + 1) rightShape right (i - 1) d
      | _ => (List.replicate shape.byteSize 0).getD i d
  | .call _, i, d =>
      match shape with
      | .call k =>
          let loc := locations.getD k 0
          ([0x61, (loc >>> 8).toUInt8, loc.toUInt8,
            Jinst.toUInt8 .jump] : Bytes).getD i d
      | _ => (List.replicate shape.byteSize 0).getD i d

/-- The lazy byte reader is extensionally the corresponding byte of the
shape-indexed emitter. -/
theorem Func.getD_emitByShape (locations : List Nat) (n : Nat)
    (shape : Func.CompileShape) (p : Func) (i : Nat) (d : UInt8) :
    (Func.emitByShape locations n shape p).getD i d =
      Func.byteAtByShape locations n shape p i d := by
  induction p generalizing n shape i with
  | last o =>
      cases shape <;> simp [Func.emitByShape, Func.byteAtByShape]
  | next inst p ih =>
      cases shape <;>
        simp only [Func.emitByShape, Func.byteAtByShape,
          List.getD_append_inspect, List.length_takeD_exact, ih]
  | branch p q ihp ihq =>
      cases shape <;>
        simp only [Func.emitByShape, Func.byteAtByShape, List.append_assoc,
          List.getD_append_inspect, Func.length_emitByShape,
          List.length_singleton, ihp, ihq]
  | call k =>
      cases shape <;> simp [Func.emitByShape, Func.byteAtByShape]

/-- A function indexed by its own compiler shape is the ordinary unchecked
inspection view. -/
theorem Func.emitByShape_compileShape
    (locations : List Nat) (n : Nat) (p : Func) :
    Func.emitByShape locations n p.compileShape p =
      Func.emitUnchecked locations n p := by
  induction p generalizing n with
  | last o => rfl
  | next i p ih =>
      rw [Func.compileShape, Func.emitByShape, Func.emitUnchecked,
        List.takeD_eq_self 0 (Ninst.size_eq_length_toBytes i)]
      simp [ih]
  | branch p q ihp ihq =>
      simp [Func.compileShape, Func.emitByShape, Func.emitUnchecked,
        ihp, ihq, Func.CompileShape.byteSize_compileShape]
  | call k => simp [Func.compileShape, Func.emitByShape, Func.emitUnchecked]

/-- Table entry locations computed solely from compiler shapes. -/
def Func.CompileShape.locations : Nat → List Func.CompileShape → List Nat
  | _, [] => []
  | n, shape :: rest =>
      n :: locations (n + shape.byteSize + 1) rest

theorem Func.CompileShape.locations_compileShapes
    (n : Nat) (fs : List Func) :
    Func.CompileShape.locations n (fs.map Func.compileShape) =
      (table n fs).map Prod.fst := by
  induction fs generalizing n with
  | nil => rfl
  | cons f fs ih =>
      simp [Func.CompileShape.locations, table,
        Func.CompileShape.byteSize_compileShape, ih]

/-- Shape-indexed emission of a flat table. -/
def Table.emitByShape (locations : List Nat) :
    List Nat → List Func.CompileShape → List Func → Bytes
  | n :: ns, shape :: shapes, p :: ps =>
      Jinst.toUInt8 .jumpdest ::
        Func.emitByShape locations (n + 1) shape p ++
          Table.emitByShape locations ns shapes ps
  | _, _, _ => []

theorem Table.emitByShape_compileShapes
    (locations : List Nat) (n : Nat) (fs : List Func) :
    Table.emitByShape locations
        (Func.CompileShape.locations n (fs.map Func.compileShape))
        (fs.map Func.compileShape) fs =
      Table.emitUnchecked locations (table n fs) := by
  induction fs generalizing n with
  | nil => rfl
  | cons f fs ih =>
      simp [Func.CompileShape.locations, table, Table.emitByShape,
        Table.emitUnchecked, Func.emitByShape_compileShape,
        Func.CompileShape.byteSize_compileShape, ih]

/-- Inspect a program's opcode contents under an explicit compiler shape. -/
def Prog.emitByShape (shape : Prog.CompileShape) (p : Prog) : Bytes :=
  let shapes := shape.main :: shape.aux
  let locations := Func.CompileShape.locations 0 shapes
  Table.emitByShape locations locations shapes (p.main :: p.aux)

/-- Supplying a program's own compiler shape recovers `emitUnchecked`. -/
theorem Prog.emitByShape_compileShape (p : Prog) :
    Prog.emitByShape p.compileShape p = p.emitUnchecked := by
  unfold Prog.emitByShape Prog.compileShape Prog.emitUnchecked
  change Table.emitByShape
      (Func.CompileShape.locations 0
        ((p.main :: p.aux).map Func.compileShape))
      (Func.CompileShape.locations 0
        ((p.main :: p.aux).map Func.compileShape))
      ((p.main :: p.aux).map Func.compileShape) (p.main :: p.aux) =
    Table.emitUnchecked ((table 0 (p.main :: p.aux)).map Prod.fst)
      (table 0 (p.main :: p.aux))
  rw [Table.emitByShape_compileShapes,
    Func.CompileShape.locations_compileShapes]

/-- A successful function compilation is exactly its unchecked inspection
view.  The success witness discharges every table lookup and branch bound. -/
theorem Func.compile_eq_emitUnchecked
    {l : List (Nat × Func)} {n : Nat} {p : Func} {bs : Bytes}
    (h : Func.compile l n p = some bs) :
    bs = Func.emitUnchecked (l.map Prod.fst) n p := by
  induction p generalizing n bs with
  | last o =>
      simp [Func.compile] at h
      exact h.symm
  | next i p ih =>
      rcases of_bind_eq_some h with ⟨pbs, hp, hbs⟩
      simp at hbs
      subst bs
      simp [Func.emitUnchecked, ih hp]
  | branch p q ihp ihq =>
      rcases of_bind_eq_some h with ⟨pbs, hp, h⟩
      rcases of_guard_eq_some h with ⟨_, h⟩
      rcases of_bind_eq_some h with ⟨qbs, hq, hbs⟩
      simp at hbs
      subst bs
      have hp' := ihp hp
      have hq' := ihq hq
      have hlenp := Func.length_compile hp
      simp [Func.emitUnchecked, ← hp', hlenp, hq']
  | call k =>
      unfold Func.compile at h
      generalize hk : l[k]? = entry at h
      cases entry with
      | none => simp at h
      | some entry =>
          rcases entry with ⟨loc, f⟩
          rcases of_guard_eq_some h with ⟨_, h⟩
          simp at h
          subst bs
          simp [Func.emitUnchecked, List.getElem?_map, hk]

/-- A successful table compilation is exactly its unchecked inspection view. -/
theorem Table.compile_eq_emitUnchecked
    {l t : List (Nat × Func)} {bs : Bytes}
    (h : Table.compile l t = some bs) :
    bs = Table.emitUnchecked (l.map Prod.fst) t := by
  induction t generalizing bs with
  | nil =>
      simp [Table.compile] at h
      subst bs
      rfl
  | cons entry rest ih =>
      rcases entry with ⟨n, p⟩
      rcases of_bind_eq_some h with ⟨pbs, hp, h⟩
      rcases of_bind_eq_some h with ⟨rbs, hr, hbs⟩
      simp at hbs
      subst bs
      simp [Table.emitUnchecked, Func.compile_eq_emitUnchecked hp, ih hr]

/-- A successful complete-program compilation is exactly its unchecked
inspection view. -/
theorem Prog.compile_eq_emitUnchecked {p : Prog} {bs : Bytes}
    (h : Prog.compile p = some bs) : bs = p.emitUnchecked := by
  unfold Prog.compile at h
  unfold Prog.emitUnchecked
  exact Table.compile_eq_emitUnchecked h

/-! ## Executing a call-free compiled prefix

`Prog.exec_of_runCompiled` connects a whole compiled program to `exec`.  A
constructor is a different but equally standard byte layout: executable code
comes first and the runtime it will copy follows as inert data.  The two facts
below expose the corresponding boundary without pretending that the data tail
is another Blanc function.

The syntactic no-call premise is load-bearing.  A `Func.call` jumps through a
compiled table, so validating one requires the complete program layout.  A
call-free prefix needs only its own `subcode` witness and can therefore be
followed by arbitrary bytes. -/

/-- A `Func` containing no internal table jump.  External EVM instructions
such as `CALL` remain ordinary `Ninst`s and are not excluded by this syntax
predicate. -/
def Func.NoCalls : Func → Prop
  | .branch f g => f.NoCalls ∧ g.NoCalls
  | .last _ => True
  | .next _ f => f.NoCalls
  | .call _ => False

/-- Prepending a straight-line instruction sequence cannot introduce a Blanc
table call. -/
theorem Func.NoCalls.prepend (xs : Line) {f : Func} (hf : f.NoCalls) :
    (xs +++ f).NoCalls := by
  induction xs with
  | nil => simpa [Blanc.prepend] using hf
  | cons _ xs ih => simpa [Blanc.prepend, Func.NoCalls] using ih

/-- A gas-exact call-free walk executes from any bytecode window containing
the corresponding compiled function.  Unlike the whole-program bridge, this
theorem needs no equality for bytes outside that window. -/
theorem Func.exec_of_runCompiled_subcode
    {l : List (Nat × Func)} {FS : List Func} {sevm : Sevm}
    {devm : Devm} {p : Func} {devm' : Devm}
    (h_run : Func.RunCompiled FS sevm devm p devm')
    (h_noCalls : p.NoCalls) :
    ∀ pc,
      subcode sevm.code.toList pc (Func.compile l pc p) →
      noPushBefore sevm.code pc 32 = true →
      Nonempty (Exec pc sevm devm (.ok devm')) := by
  induction h_run with
  | zero h_room h_pop h_f ih =>
    intro pc sub hb
    rcases h_noCalls with ⟨hnf, _⟩
    rcases subcode_compile_branch_jumpable sub hb with
      ⟨loc, _h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp,
        _h_jd, _h_jp, _h_subq, _h_bq⟩
    rcases Evm.branch_zero_steps h_push h_jumpi h_loc h_room h_pop with
      ⟨h1, h2⟩
    obtain ⟨excf⟩ := ih hnf (pc + 4) h_subp h_bp
    exact ⟨Exec.cont h1 (Exec.cont h2 excf)⟩
  | succ h_ne h_room h_pop h_g ih =>
    intro pc sub hb
    rcases h_noCalls with ⟨_, hng⟩
    rcases subcode_compile_branch_jumpable sub hb with
      ⟨loc, _h_loc_eq, h_loc, h_push, h_jumpi, _h_subp, _h_bp,
        h_jd, h_jp, h_subq, h_bq⟩
    rcases Evm.branch_succ_steps h_push h_jumpi h_jd h_jp h_loc h_ne
      h_room h_pop with ⟨h1, h2, h3⟩
    obtain ⟨excg⟩ := ih hng (loc + 1) h_subq h_bq
    exact ⟨Exec.cont h1 (Exec.cont h2 (Exec.cont h3 excg))⟩
  | last h_lin =>
    intro pc sub _hb
    refine ⟨Exec.halt ?_⟩
    rw [Evm.step_last (Linst.at_of_slice sub)]
    exact congrArg Step.halt h_lin
  | next h_n h_f ih =>
    intro pc sub hb
    rcases Func.noPushBefore_next sub hb with ⟨hb', sub'⟩
    rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
    rcases of_bind_eq_some h_eq' with ⟨cd', _h_eq'', h_rw⟩
    simp [pure] at h_rw
    rw [← h_rw] at h_slice
    rcases h_n with ⟨xl, h_filled, h_step⟩
    exact Ninst.exec_of_stepRun
      (Ninst.at_of_slice (List.slice_prefix h_slice))
      h_filled (h_step pc) (ih h_noCalls _ sub' hb')
  | call _h_get _h_room _h_burn _h_f _ih =>
    exact False.elim h_noCalls

/-- The common constructor layout: `pfx` is executable and `sfx` is arbitrary
trailing data.  A `RunCompiled` witness for the call-free function fixes the
successful total `exec` result at pc zero. -/
theorem Func.exec_of_runCompiled_prefix
    {l : List (Nat × Func)} {FS : List Func} {sevm : Sevm}
    {devm : Devm} {p : Func} {devm' : Devm} {pfx sfx : Bytes}
    (h_run : Func.RunCompiled FS sevm devm p devm')
    (h_noCalls : p.NoCalls)
    (h_compile : Func.compile l 0 p = some pfx)
    (h_code : sevm.code.toList = pfx ++ sfx) :
    exec ⟨0, sevm, devm⟩ = .ok devm' := by
  have h_sub : subcode sevm.code.toList 0 (Func.compile l 0 p) := by
    rw [h_compile]
    show List.Slice sevm.code.toList 0 pfx
    rw [h_code]
    exact List.slice_prefix (List.slice_refl (pfx ++ sfx))
  have h_bound : noPushBefore sevm.code 0 32 = true := by
    simp [noPushBefore]
  obtain ⟨h_exec⟩ :=
    Func.exec_of_runCompiled_subcode h_run h_noCalls 0 h_sub h_bound
  rw [← exec_iff_exec_eq]
  exact ⟨h_exec⟩

/-! ## `func_run` — the constructor-side walk

`Blanc/Tactics.lean`'s `funcInv` walks a `Func` and applies `next_inv`,
`branch_inv`, `prepend_inv` to *destructure* a run sitting in antecedent
position.  This is its dual: the same walk over the same `Func` structure,
applying `Func.RunCompiled`'s constructors to a goal.

The walk carries the machine state forward itself rather than reading it back
out of each lemma's conclusion.  Every state it writes is
`base.setMach ⟨stack, memory, gasBase - n⟩` for a single numeral `n`, so gas
premises come out in `Devm.BurnBy`'s own additive shape and each one is a single
`omega`.  Threading the subtractive shape instead would make the `n`-th state
carry `pre.gasLeft - c₁ - … - cₙ`.

Two things a construction cannot compute, and how the tactic gets them:

* **Values.** What `SHR` produced, what `GT` decided.  These come from the
  bracketed hint list, elaborated in the goal's context and consumed left to
  right; where no hint is left the walk keeps the unevaluated application, which
  is always correct but leaves a later `branch` undecidable.
* **Memory expansion.** `MSTORE`'s `Devm.extCost` is a function of the whole
  memory image; it takes a `Nat` hint, and the proof obligation that the hint is
  right is handed back as a subgoal.

Obligations the walk cannot discharge mechanically are returned as goals in the
order they were met, and `Func.last` always is one: a terminal instruction ends
the frame, and evaluating it is the caller's.

**The walk is parameterised by the relation it builds** — `RelSpec` below, a
head constant plus four rule names.  `Func.RunCompiled` and
`Blanc/Reverts.lean`'s outcome-generalised `Func.RunCompiledTo` differ in
nothing the walk does, only in what its rules are called, so there is one walk
and a two-row table rather than two walks that would drift apart.  The relation
is read off the goal once, in `funcRunMain`, and every recursive call builds
that one.  Which relation a caller gets is therefore decided by how the caller
stated its goal, and mixing the two inside one walk is an error rather than a
silent switch. -/

section ForwardTactic

-- `Blanc.Lean` exists (`Blanc/Tactics.lean` adds to it), so an unqualified
-- `open Lean` inside this namespace would open that instead of the real one.
open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic

namespace Forward

/-- The relation a walk builds: the head constant its goals are stated with, and
the four structural rules it applies **by name**.

`Blanc/Reverts.lean`'s `Func.RunCompiledTo` is `Func.RunCompiled` with the
terminal outcome generalised from `.ok devm'` to an arbitrary `Execution`, and
its four structural rules are *positional* mirrors of the four below — same
binder order, same premises, same costs.  That is what makes one walk serve both
relations: everything `funcWalk` does other than naming a rule is identical, so
the difference between the two is exactly this table and nothing else.

**One walk, parameterised — never a second copy of it.**  Two `funcWalk`s would
drift apart within a single arc, and the `.ok` one is what the repository's
existing liveness witnesses are built from.

The `To` row's names are raw `Name` literals rather than `` ``Name `` because
`Blanc/Reverts.lean` imports *this* module: the constants do not exist yet at
this point in the tree.  They are resolved by `applyLemma`'s `getConstInfo` the
first time a walk actually reaches them, so a stale name fails loudly at the
first `func_run` over that relation — which is a compile error in
`Blanc/FmintReverts.lean`, not a silent fallback. -/
structure RelSpec where
  /-- The relation's head constant.  Its goals are `head fs sevm devm f out`. -/
  head : Name
  /-- The `.next` rule: one `Ninst.RunCompiled` and the rest of the `Func`. -/
  next : Name
  /-- The fall-through arm of a `branch`, condition `0`. -/
  branchZero : Name
  /-- The jumped arm of a `branch`, condition nonzero. -/
  branchSucc : Name
  /-- An internal tail call into the flat table. -/
  call : Name
  deriving Inhabited

/-- `Blanc/Compiled.lean`'s `Func.RunCompiled`, with this module's wrappers. -/
def okSpec : RelSpec where
  head := ``Blanc.Func.RunCompiled
  next := ``Blanc.Func.RunCompiled.next
  branchZero := ``Func.runCompiled_branch_zero
  branchSucc := ``Func.runCompiled_branch_succ
  call := ``Func.runCompiled_call'

/-- `Blanc/Reverts.lean`'s `Func.RunCompiledTo`, with that module's wrappers. -/
def toSpec : RelSpec where
  head := `Blanc.Func.RunCompiledTo
  next := `Blanc.Func.RunCompiledTo.next
  branchZero := `Blanc.Func.runCompiledTo_branch_zero
  branchSucc := `Blanc.Func.runCompiledTo_branch_succ
  call := `Blanc.Func.runCompiledTo_call'

/-- `Blanc/ForwardCall.lean`'s `Func.ExecTo`, the pc-quantified transport of a
walk into `Exec`-derivation evidence.  Same four structural rules, positional
mirrors of `toSpec`'s, and raw `Name` literals for the same reason as there:
the constants live downstream of this module. -/
def execSpec : RelSpec where
  head := `Blanc.Func.ExecTo
  next := `Blanc.Func.execTo_next
  branchZero := `Blanc.Func.execTo_branch_zero
  branchSucc := `Blanc.Func.execTo_branch_succ
  call := `Blanc.Func.execTo_call'

/-- `Blanc/ForwardCall.lean`'s outcome-aware witness relation.  Its structural
rules dispatch to `RunCompiled` on success and `ExecTo` on fatal error while
letting the shared walk elaborate the instruction prefix only once. -/
def witnessSpec : RelSpec where
  head := `Blanc.Func.ExecWitness
  next := `Blanc.Func.ExecWitness.next
  branchZero := `Blanc.Func.execWitness_branch_zero
  branchSucc := `Blanc.Func.execWitness_branch_succ
  call := `Blanc.Func.execWitness_call'

/-- Every relation `func_run` knows how to build, matched on the goal's head. -/
def relSpecs : List RelSpec := [okSpec, toSpec, execSpec, witnessSpec]

/-- The spec for a goal head, or nothing. -/
def specOf? (head : Name) : Option RelSpec := relSpecs.find? (·.head == head)

/-- The walk's mutable state: the relation it is building, the hints it has not
spent, the obligations it could not close, how many `Ninst` steps it has taken
(for messages), and how many it is still allowed to take.

`budget` is what makes a **prefix** walk possible.  A `Func` is concrete all the
way down, so a caller cannot abstract its tail and stop the walk that way; the
budget is the only place a walk can be told to stop somewhere other than a
terminal.  `none` is the original behaviour and every existing caller has it. -/
structure Ctx where
  rel : RelSpec
  hints : List Term
  side : Array MVarId
  step : Nat
  budget : Option Nat

abbrev ForwardM := StateRefT Ctx TacticM

/-- A `Nat` an expression is *equal to by evaluation*, or nothing.  Used only on
fee-schedule constants and hint terms, never to decide a semantic question. -/
def natOf? (e : Expr) : MetaM (Option Nat) := do
  if let some n := e.nat? then return some n
  if let some n := e.rawNatLit? then return some n
  let e' ← whnf e
  if let some n := e'.nat? then return some n
  return e'.rawNatLit?

/-- Apply `name` to `g`, fixing the arguments in `given` and returning the
argument positions in `holes` as goals. -/
def applyLemma (g : MVarId) (name : Name) (given : List (Nat × Expr))
    (holes : List Nat) : MetaM (List MVarId) := do
  let info ← getConstInfo name
  let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst name lvls
  let (mvars, _, concl) ← forallMetaTelescope (← inferType f)
  for i in holes do
    if i ≥ mvars.size then throwError "func_run: bad hole {i} for {name}"
    (mvars[i]!).mvarId!.setKind .syntheticOpaque
  for (i, e) in given do
    if i ≥ mvars.size then throwError "func_run: bad argument {i} for {name}"
    unless ← isDefEq mvars[i]! e do
      throwError "func_run: cannot fix argument {i} of {name} to{indentExpr e}"
  unless ← isDefEq concl (← g.getType) do
    throwError "func_run: {name} does not fit the goal{indentExpr (← g.getType)}"
  g.assign (mkAppN f mvars)
  let mut out := []
  for i in holes.reverse do
    let m := mvars[i]!
    unless ← m.mvarId!.isAssigned do out := m.mvarId! :: out
  return out

/-- Run one tactic on one goal, all or nothing. -/
def tryTacOn (g : MVarId) (stx : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  let prev ← getGoals
  try
    setGoals [g]
    evalTactic stx
    if (← getGoals).isEmpty then
      setGoals prev
      return true
    else
      saved.restore
      return false
  catch _ =>
    saved.restore
    return false

/-- Close `g` with the first tactic that works, or hand it back as a subgoal. -/
def discharge (g : MVarId) (stxs : List (TSyntax `tactic)) : ForwardM Unit := do
  if ← g.isAssigned then return
  for stx in stxs do
    if ← tryTacOn g stx then return
  modify fun c => { c with side := c.side.push g }

/-- Value obligations often exactly repeat a caller hypothesis.  Check for that
syntactically before invoking tactics, without paying to instantiate and scan
the whole local context for every gas, room, and stack obligation in a walk. -/
def dischargeValue (g : MVarId) (stxs : List (TSyntax `tactic)) : ForwardM Unit := do
  if ← g.isAssigned then return
  let exactLocal? ← g.withContext do
    let target ← instantiateMVars (← g.getType)
    (← getLCtx).findDeclM? fun decl => do
      if decl.isImplementationDetail then return none
      if (← instantiateMVars decl.type) == target then return some decl.toExpr
      return none
  if let some fvar := exactLocal? then
    g.assign fvar
    return
  discharge g stxs

/-- The gas obligation: always `base - n = (base - m) + c` over numerals. -/
def gasTacs : ForwardM (List (TSyntax `tactic)) := do
  let t ← `(tactic|
    (simp only [Devm.gasLeft_setMach, gVerylow, gBase, gHigh, gMid, gJumpdest,
      gasColdSload, gasColdAccountAccess, gasWarmAccess, gMemory]; omega))
  return [t]

/-- The stack-headroom obligation, on a literal stack. -/
def roomTacs : ForwardM (List (TSyntax `tactic)) := do
  let a ← `(tactic| (simp only [Devm.stack_setMach]; simp))
  let b ← `(tactic| simp)
  let c ← `(tactic| decide)
  return [a, b, c]

/-- The stack-shape obligation, true by construction. -/
def rflTacs : ForwardM (List (TSyntax `tactic)) := do
  let a ← `(tactic| rfl)
  let b ← `(tactic| simp)
  return [a, b]

/-- A value obligation `f x … = v`: `rfl` when the walk kept the application,
otherwise the hint has to be justified. -/
def valTacs : ForwardM (List (TSyntax `tactic)) := do
  let a ← `(tactic| rfl)
  let b ← `(tactic| assumption)
  let c ← `(tactic| decide)
  let d ← `(tactic| decide +kernel)
  let e ← `(tactic| simp)
  return [a, b, c, d, e]

/-- Elaborate the next hint at the expected type, or nothing if none is left. -/
def nextHint (g : MVarId) (expected : Expr) : ForwardM (Option Expr) := do
  let c ← get
  match c.hints with
  | [] => return none
  | h :: rest =>
    set { c with hints := rest }
    g.withContext do
      let e ← Term.elabTerm h (some expected)
      Term.synthesizeSyntheticMVarsNoPostponing
      return some (← instantiateMVars e)

/-- Split a state into its base and the three machine fields.  Every state the
walk writes is in this shape; the entry state is whatever the caller named. -/
def parseState (d : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let d' ← whnfR d
  match d'.getAppFnArgs with
  | (``Jaune.Devm.setMach, #[b, m]) =>
    let m' ← whnfR m
    match m'.getAppFnArgs with
    | (``Jaune.Mach.mk, #[s, mem, gas]) => return (b, s, mem, gas)
    | _ => return (b, ← mkAppM ``Jaune.Mach.stack #[m],
        ← mkAppM ``Jaune.Mach.memory #[m], ← mkAppM ``Jaune.Mach.gasLeft #[m])
  | _ => return (d', ← mkAppM ``Jaune.Devm.stack #[d'],
      ← mkAppM ``Jaune.Devm.memory #[d'], ← mkAppM ``Jaune.Devm.gasLeft #[d'])

/-- Read a gas account as `base - n`.  A state whose gas is not of that shape
starts a fresh offset, which is still correct — it only makes the numerals in
later premises relative to it. -/
def parseGas (gas : Expr) : MetaM (Expr × Nat) := do
  match gas.getAppFnArgs with
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    match b.nat? with
    | some n => return (a, n)
    | none => return (gas, 0)
  | _ => return (gas, 0)

/-- Peel `n` words off a stack expression. -/
def popStack : Nat → Expr → MetaM (List Expr × Expr)
  | 0, s => return ([], s)
  | n + 1, s => do
    let s' ← whnf s
    match s'.getAppFnArgs with
    | (``List.cons, #[_, x, t]) => do
      let (xs, t') ← popStack n t
      return (x :: xs, t')
    | _ => throwError "func_run: the stack is too short here:{indentExpr s}"

/-- Unfold until the head is one of `heads`, or until nothing unfolds.  Plain
`whnf` is wrong here: it would run straight past `applyBinary` into the machine
monad, and the head symbol *is* the classification the walk needs. -/
partial def whnfUntilHead (heads : List Name) : Nat → Expr → MetaM Expr
  | 0, e => return e
  | fuel + 1, e => do
    let e' ← whnfCore e
    match e'.getAppFn.constName? with
    | some n => if heads.contains n then return e' else
      match ← unfoldDefinition? e' with
      | some e'' => whnfUntilHead heads fuel e''
      | none => return e'
    | none =>
      match ← unfoldDefinition? e' with
      | some e'' => whnfUntilHead heads fuel e''
      | none => return e'

/-- Build `base.setMach ⟨stack, memory, gas⟩`. -/
def mkState (base stack memory gas : Expr) : MetaM Expr := do
  mkAppM ``Jaune.Devm.setMach #[base, ← mkAppM ``Jaune.Mach.mk #[stack, memory, gas]]

/-- `gasBase - (n + cost)`. -/
def mkGas (gasBase : Expr) (n cost : Nat) : MetaM Expr :=
  mkAppM ``HSub.hSub #[gasBase, mkNatLit (n + cost)]

/-- Restate a walk goal with the state the walk wrote, instead of the projection
chain the applied lemma's conclusion produced.  `head` is the relation's, so
this serves `Func.RunCompiled` and `Func.RunCompiledTo` alike. -/
def retarget (head : Name) (g : MVarId) (state : Expr) : MetaM MVarId := do
  let t ← instantiateMVars (← g.getType)
  match t.getAppFnArgs with
  | (h, #[fs, sevm, _, f, post]) =>
    if h == head then
      g.change (mkAppN (mkConst head) #[fs, sevm, state, f, post])
    else return g
  | _ => return g

/-- Discharge the successor-state equation of the applied rule against the state
the walk wrote. -/
def fixPost (post state : Expr) : MetaM Unit := do
  unless ← isDefEq post state do
    throwError "func_run: cannot name the successor state{indentExpr state}"

/-- One `Ninst` node: pick the wrapper the opcode calls for, name the successor,
and hand back what the wrapper leaves. -/
def ninstStep (g : MVarId) : ForwardM Unit := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let (sevm, d, i, post) ← match t.getAppFnArgs with
    | (``Blanc.Ninst.RunCompiled, #[a, b, c, e]) => pure (a, b, c, e)
    | _ => throwError "func_run: not an instruction goal{indentExpr t}"
  let (base, stk, mem, gas) ← parseState d
  let (gb, goff) ← parseGas gas
  let n := (← get).step
  modify fun c => { c with step := c.step + 1 }
  let i' ← whnfR i
  match i'.getAppFnArgs with
  | (``Blanc.Ninst.pushB256, #[w]) => do
    -- Evaluate `pushCost` rather than testing `w` for zero.  `Bytes.sig` drops
    -- leading zero bytes, so "is this a `PUSH0`?" is a question about the whole
    -- word, and a `pushB256` whose immediate is written `0 * 32` is one.
    let costE ← mkAppM ``pushCost
      #[← mkAppM ``Jaune.Bytes.sig #[← mkAppM ``Jaune.B256.toBytes #[w]]]
    let some cost ← natOf? costE
      | throwError "func_run: cannot tell what this PUSH costs:{indentExpr costE}"
    let gas' ← mkGas gb goff cost
    let succ ← mkState base (← mkAppM ``List.cons #[w, stk]) mem gas'
    fixPost post succ
    let gs ← applyLemma g ``Ninst.runCompiled_pushB256
      [(0, sevm), (1, d), (2, w), (3, mkNatLit cost), (4, gas')] [5, 6, 7]
    -- No nested `by`: a term-level tactic block is postponed past this walk's
    -- own `try`, so its failure would escape instead of falling through.
    let zero ← `(tactic| rfl)
    let ne ← `(tactic| (refine pushCost_of_ne_zero ?_; decide))
    let nek ← `(tactic| (refine pushCost_of_ne_zero ?_; decide +kernel))
    match gs with
    | [hc, hg, hr] =>
      discharge hc [zero, ne, nek]
      discharge hg (← gasTacs)
      discharge hr (← roomTacs)
    | _ => throwError "func_run: PUSH left {gs.length} obligations"
  | (``Jaune.Ninst.push, #[xs, le]) => do
    match xs.consumeMData.getAppFnArgs with
    | (``Jaune.B256.toBytes, #[w]) => do
      let gas' ← mkGas gb goff 3
      let succ ← mkState base (← mkAppM ``List.cons #[w, stk]) mem gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_pushB256Full
        [(0, sevm), (1, d), (2, w), (3, le), (4, gas')] [5, 6]
      match gs with
      | [hg, hr] =>
        discharge hg (← gasTacs)
        discharge hr (← roomTacs)
      | _ =>
        throwError "func_run: full-width raw PUSH left {gs.length} obligations"
    | _ => do
      let costE ← mkAppM ``pushCost #[xs]
      let some cost ← natOf? costE
        | throwError "func_run: cannot tell what this raw PUSH costs:{indentExpr costE}"
      let gas' ← mkGas gb goff cost
      let w ← mkAppM ``Jaune.Bytes.toB256 #[xs]
      let succ ← mkState base (← mkAppM ``List.cons #[w, stk]) mem gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_pushBytes
        [(0, sevm), (1, d), (2, xs), (3, le), (4, mkNatLit cost), (5, gas')]
        [6, 7, 8]
      let rfl' ← `(tactic| rfl)
      let dec ← `(tactic| decide)
      let deck ← `(tactic| decide +kernel)
      match gs with
      | [hc, hg, hr] =>
        discharge hc [rfl', dec, deck]
        discharge hg (← gasTacs)
        discharge hr (← roomTacs)
      | _ => throwError "func_run: raw PUSH left {gs.length} obligations"
  | (``Jaune.Ninst.reg, #[r]) => do
    let r' ← whnfR r
    match r'.getAppFnArgs with
    | (``Jaune.Rinst.dup, #[k]) => do
      let some kv ← natOf? (← mkAppM ``Fin.val #[k])
        | throwError "func_run: DUP index is not a literal{indentExpr k}"
      let (ws, _) ← popStack (kv + 1) stk
      let w := ws.getLast!
      let gas' ← mkGas gb goff 3
      let succ ← mkState base (← mkAppM ``List.cons #[w, stk]) mem gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_dup
        [(0, sevm), (1, d), (2, k), (3, w), (4, gas')] [5, 6, 7]
      match gs with
      | [hget, hg, hr] =>
        discharge hget (← rflTacs)
        discharge hg (← gasTacs)
        discharge hr (← roomTacs)
      | _ => throwError "func_run: DUP left {gs.length} obligations"
    | (``Jaune.Rinst.calldataload, #[]) => do
      let ([x], s) ← popStack 1 stk | throwError "func_run: CALLDATALOAD"
      -- No hint: the value is `Sevm.dataWord` of a word already on the stack,
      -- which is a definition applied to known arguments, not a computation.
      let v ← mkAppM ``Blanc.Sevm.dataWord #[sevm, x]
      let gas' ← mkGas gb goff 3
      let succ ← mkState base (← mkAppM ``List.cons #[v, s]) mem gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_calldataload
        [(0, sevm), (1, d), (2, x), (3, v), (4, s), (5, gas')] [6, 7, 8, 9]
      match gs with
      | [hstk, hval, hg, hr] =>
        discharge hstk (← rflTacs)
        dischargeValue hval (← valTacs)
        discharge hg (← gasTacs)
        discharge hr (← roomTacs)
      | _ => throwError "func_run: CALLDATALOAD left {gs.length} obligations"
    | (``Jaune.Rinst.extcodesize, #[]) => do
      let ([x], s) ← popStack 1 stk | throwError "func_run: EXTCODESIZE"
      let adr ← mkAppM ``Jaune.B256.toAdr #[x]
      let code ← mkAppM ``Jaune.Devm.getCode #[d, adr]
      let size ← mkAppM ``ByteArray.size #[code]
      let v ← mkAppM ``Jaune.Nat.toB256 #[size]
      -- As for SLOAD, warmth is a fact about the current frame and therefore
      -- comes from its hypotheses rather than from an unchecked walk hint.
      let warmProp ← mkAppM ``Membership.mem
        #[← mkAppM ``Jaune.Devm.accessedAddresses #[d], adr]
      let isWarm ← g.withContext do
        (← getLCtx).findDeclM? fun decl => do
          if decl.isImplementationDetail then return none
          if ← withNewMCtxDepth (isDefEq decl.type warmProp) then
            return some decl.type
          else return none
      let assum ← `(tactic| assumption)
      if isWarm.isSome then
        let gas' ← mkGas gb goff 100
        let succ ← mkState base (← mkAppM ``List.cons #[v, s]) mem gas'
        fixPost post succ
        let gs ← applyLemma g ``Ninst.runCompiled_extcodesize_warm
          [(0, sevm), (1, d), (2, x), (3, v), (4, s), (5, gas')]
          [6, 7, 8, 9, 10]
        match gs with
        | [hstk, hwarm, hval, hg, hr] =>
          discharge hstk (← rflTacs)
          discharge hwarm [assum]
          discharge hval (← rflTacs)
          discharge hg (← gasTacs)
          discharge hr (← roomTacs)
        | _ =>
          throwError "func_run: warm EXTCODESIZE left {gs.length} obligations"
      else
        let base' ← mkAppM ``Jaune.addAccessedAddress #[d, adr]
        let gas' ← mkGas gb goff 2600
        let succ ← mkState base' (← mkAppM ``List.cons #[v, s]) mem gas'
        fixPost post succ
        let gs ← applyLemma g ``Ninst.runCompiled_extcodesize_cold
          [(0, sevm), (1, d), (2, x), (3, v), (4, s), (5, gas')]
          [6, 7, 8, 9, 10]
        match gs with
        | [hstk, hcold, hval, hg, hr] =>
          discharge hstk (← rflTacs)
          discharge hcold [assum]
          discharge hval (← rflTacs)
          discharge hg (← gasTacs)
          discharge hr (← roomTacs)
        | _ => throwError "func_run: EXTCODESIZE left {gs.length} obligations"
    | (``Jaune.Rinst.sload, #[]) => do
      let ([k], s) ← popStack 1 stk | throwError "func_run: SLOAD"
      let tgt ← mkAppM ``Jaune.Sevm.currentTarget #[sevm]
      -- No hint either: the value read is `Devm.getStorVal` at the key that is
      -- already on the stack.
      let v ← mkAppM ``Jaune.Devm.getStorVal #[d, tgt, k]
      -- Warm or cold is a question about the *frame*, not about the
      -- instruction, so the arm is chosen by reading the caller's own
      -- hypotheses rather than by consuming a hint.  A hint would have to be
      -- supplied at every `SLOAD` of every existing walk, and it would let a
      -- caller assert warmth the frame does not carry; the local context
      -- cannot.  A frame carrying `⟨target, k⟩ ∈ accessedStorageKeys` takes the
      -- warm arm.  Everything else takes the cold arm, whose coldness
      -- obligation is discharged by `assumption` exactly as before -- so a
      -- frame carrying neither hypothesis still fails where it always did, and
      -- no existing walk changes.
      let warmProp ← mkAppM ``Membership.mem
        #[← mkAppM ``Jaune.Devm.accessedStorageKeys #[d],
          ← mkAppM ``Prod.mk #[tgt, k]]
      -- `withNewMCtxDepth` makes the probe read-only: every metavariable the
      -- walk has built so far is rigid inside it, so a hypothesis can be
      -- *recognised* but nothing can be *assigned* by recognising it.
      let isWarm ← g.withContext do
        (← getLCtx).findDeclM? fun decl => do
          if decl.isImplementationDetail then return none
          if ← withNewMCtxDepth (isDefEq decl.type warmProp) then
            return some decl.type
          else return none
      let assum ← `(tactic| assumption)
      if isWarm.isSome then
        -- `gasWarmAccess`.  The successor's base is `base`, unmoved: a warm
        -- read adds nothing to the accessed set.
        let gas' ← mkGas gb goff 100
        let succ ← mkState base (← mkAppM ``List.cons #[v, s]) mem gas'
        fixPost post succ
        let gs ← applyLemma g ``Ninst.runCompiled_sload_warm
          [(0, sevm), (1, d), (2, k), (3, v), (4, s), (5, gas')] [6, 7, 8, 9, 10]
        match gs with
        | [hstk, hwarm, hval, hg, hr] =>
          discharge hstk (← rflTacs)
          discharge hwarm [assum]
          dischargeValue hval (← valTacs)
          discharge hg (← gasTacs)
          discharge hr (← roomTacs)
        | _ => throwError "func_run: warm SLOAD left {gs.length} obligations"
      else
        let base' ← mkAppM ``Jaune.addAccessedStorageKey #[d, tgt, k]
        let gas' ← mkGas gb goff 2100
        let succ ← mkState base' (← mkAppM ``List.cons #[v, s]) mem gas'
        fixPost post succ
        let gs ← applyLemma g ``Ninst.runCompiled_sload_cold
          [(0, sevm), (1, d), (2, k), (3, v), (4, s), (5, gas')] [6, 7, 8, 9, 10]
        match gs with
        | [hstk, hcold, hval, hg, hr] =>
          discharge hstk (← rflTacs)
          discharge hcold [assum]
          dischargeValue hval (← valTacs)
          discharge hg (← gasTacs)
          discharge hr (← roomTacs)
        | _ => throwError "func_run: SLOAD left {gs.length} obligations"
    | (``Jaune.Rinst.mstore, #[]) => do
      let ([idx, val], s) ← popStack 2 stk | throwError "func_run: MSTORE"
      let some ext ← nextHint g (mkConst ``Nat)
        | throwError m!"func_run: step {n + 1} is an MSTORE. Its memory-expansion charge is not computable from the instruction alone; supply it as the next hint."
      let some extN ← natOf? ext
        | throwError "func_run: the MSTORE hint{indentExpr ext}is not a numeral"
      let gas' ← mkGas gb goff (3 + extN)
      let img ← mkAppM ``Jaune.Mem.write
        #[mem, ← mkAppM ``Jaune.B256.toNat #[idx], ← mkAppM ``Jaune.B256.toBytes #[val]]
      let succ ← mkState base s img gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_mstore_of
        [(0, sevm), (1, d), (2, idx), (3, val), (4, s), (5, gas'), (6, ext), (7, img)]
        [8, 9, 10, 11]
      match gs with
      | [hstk, hext, hg, hw] =>
        discharge hstk (← rflTacs)
        discharge hext []
        discharge hg (← gasTacs)
        discharge hw (← rflTacs)
      | _ => throwError "func_run: MSTORE left {gs.length} obligations"
    | (``Jaune.Rinst.pop, #[]) => do
      let ([_x], s) ← popStack 1 stk | throwError "func_run: POP"
      let gas' ← mkGas gb goff 2
      let succ ← mkState base s mem gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_pop
        [(0, sevm), (1, d), (2, _x), (3, s), (4, gas')] [5, 6]
      match gs with
      | [hstk, hg] =>
        discharge hstk (← rflTacs)
        discharge hg (← gasTacs)
      | _ => throwError "func_run: POP left {gs.length} obligations"
    | (``Jaune.Rinst.swap, #[k]) => do
      -- `List.swap (w₀ :: rest) k` exchanges `w₀` with `rest[k]`, which is the
      -- `(k+2)`-th word of the stack.  The walk permutes the words itself
      -- rather than leaving `List.swap` unevaluated: a frozen `List.swap`
      -- redex would stop the next `popStack` dead.
      let some kv ← natOf? (← mkAppM ``Fin.val #[k])
        | throwError "func_run: SWAP index is not a literal{indentExpr k}"
      let (ws, t) ← popStack (kv + 2) stk
      let top := ws[0]!
      let deep := ws[kv + 1]!
      let mid := (ws.drop 1).take kv
      let S ← (deep :: (mid ++ [top])).foldrM
        (fun x acc => mkAppM ``List.cons #[x, acc]) t
      let gas' ← mkGas gb goff 3
      let succ ← mkState base S mem gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_swap
        [(0, sevm), (1, d), (2, k), (3, S), (4, gas')] [5, 6]
      match gs with
      | [hswap, hg] =>
        discharge hswap (← rflTacs)
        discharge hg (← gasTacs)
      | _ => throwError "func_run: SWAP left {gs.length} obligations"
    | (``Jaune.Rinst.gas, #[]) => do
      -- No hint and no value obligation: what `GAS` pushes is the successor's
      -- own account, which in the additive convention is the name the walk has
      -- just written.
      let gas' ← mkGas gb goff 2
      let w ← mkAppM ``Jaune.Nat.toB256 #[gas']
      let succ ← mkState base (← mkAppM ``List.cons #[w, stk]) mem gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_gas
        [(0, sevm), (1, d), (2, gas')] [3, 4]
      match gs with
      | [hg, hr] =>
        discharge hg (← gasTacs)
        discharge hr (← roomTacs)
      | _ => throwError "func_run: GAS left {gs.length} obligations"
    | (``Jaune.Rinst.mload, #[]) => do
      let ([i], s) ← popStack 1 stk | throwError "func_run: MLOAD"
      let some cost ← nextHint g (mkConst ``Nat)
        | throwError m!"func_run: step {n + 1} is an MLOAD. Its charge includes a memory expansion, which is not computable from the instruction alone; supply the whole charge as the next hint."
      let some costN ← natOf? cost
        | throwError "func_run: the MLOAD hint{indentExpr cost}is not a numeral"
      let rd ← mkAppM ``Jaune.Mem.read
        #[mem, ← mkAppM ``Jaune.B256.toNat #[i], mkNatLit 32]
      let v ← mkAppM ``Jaune.Bytes.toB256 #[← mkAppM ``Prod.fst #[rd]]
      let m' ← mkAppM ``Prod.snd #[rd]
      let gas' ← mkGas gb goff costN
      let succ ← mkState base (← mkAppM ``List.cons #[v, s]) m' gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_mload_of
        [(0, sevm), (1, d), (2, i), (3, v), (4, s), (5, cost), (6, gas'),
          (7, m')] [8, 9, 10, 11, 12, 13]
      match gs with
      | [hstk, hcost, hval, hmem, hg, hr] =>
        discharge hstk (← rflTacs)
        discharge hcost []
        discharge hval (← rflTacs)
        discharge hmem (← rflTacs)
        discharge hg (← gasTacs)
        discharge hr (← roomTacs)
      | _ => throwError "func_run: MLOAD left {gs.length} obligations"
    | (``Jaune.Rinst.kec, #[]) => do
      let ([i, sz], s) ← popStack 2 stk | throwError "func_run: KECCAK256"
      let some cost ← nextHint g (mkConst ``Nat)
        | throwError m!"func_run: step {n + 1} is a KECCAK256. Supply its whole charge as the next hint."
      let some costN ← natOf? cost
        | throwError "func_run: the KECCAK256 hint{indentExpr cost}is not a numeral"
      let rd ← mkAppM ``Jaune.Mem.read
        #[mem, ← mkAppM ``Jaune.B256.toNat #[i],
          ← mkAppM ``Jaune.B256.toNat #[sz]]
      let m' ← mkAppM ``Prod.snd #[rd]
      -- The hash itself is a *value*, on the same footing as what `SHR`
      -- produced: a second hint names it and turns `h_val` into the caller's
      -- obligation, and with none left the walk keeps `Bytes.keccak` applied to
      -- the window it read.  Nothing here evaluates it.
      let v ← (do
        match ← nextHint g (mkConst ``Jaune.B256) with
        | some v => pure v
        | none => mkAppM ``Bytes.keccak #[← mkAppM ``Prod.fst #[rd]])
      let gas' ← mkGas gb goff costN
      let succ ← mkState base (← mkAppM ``List.cons #[v, s]) m' gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_kec_of
        [(0, sevm), (1, d), (2, i), (3, sz), (4, v), (5, s), (6, cost),
          (7, gas'), (8, m')] [9, 10, 11, 12, 13, 14]
      match gs with
      | [hstk, hcost, hval, hmem, hg, hr] =>
        discharge hstk (← rflTacs)
        discharge hcost []
        dischargeValue hval (← valTacs)
        discharge hmem (← rflTacs)
        discharge hg (← gasTacs)
        discharge hr (← roomTacs)
      | _ => throwError "func_run: KECCAK256 left {gs.length} obligations"
    | (``Jaune.Rinst.codecopy, #[]) => do
      let ([di, si, sz], s) ← popStack 3 stk
        | throwError "func_run: CODECOPY"
      let some cost ← nextHint g (mkConst ``Nat)
        | throwError m!"func_run: step {n + 1} is a CODECOPY. Supply its whole charge as the next hint."
      let some costN ← natOf? cost
        | throwError "func_run: the CODECOPY hint{indentExpr cost}is not a numeral"
      let u8zero ← mkAppOptM ``OfNat.ofNat
        #[mkConst ``UInt8, mkNatLit 0, none]
      let val ← mkAppM ``Jaune.ByteArray.sliceD
        #[← mkAppM ``Jaune.Sevm.code #[sevm],
          ← mkAppM ``Jaune.B256.toNat #[si],
          ← mkAppM ``Jaune.B256.toNat #[sz], u8zero]
      let img ← mkAppM ``Jaune.Mem.write
        #[mem, ← mkAppM ``Jaune.B256.toNat #[di], val]
      let gas' ← mkGas gb goff costN
      let succ ← mkState base s img gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_codecopy_of
        [(0, sevm), (1, d), (2, di), (3, si), (4, sz), (5, s), (6, cost),
          (7, gas'), (8, img)] [9, 10, 11, 12]
      match gs with
      | [hstk, hcost, hw, hg] =>
        discharge hstk (← rflTacs)
        discharge hcost []
        discharge hw (← rflTacs)
        discharge hg (← gasTacs)
      | _ => throwError "func_run: CODECOPY left {gs.length} obligations"
    | (``Jaune.Rinst.calldatacopy, #[]) => do
      let ([di, si, sz], s) ← popStack 3 stk
        | throwError "func_run: CALLDATACOPY"
      let some cost ← nextHint g (mkConst ``Nat)
        | throwError m!"func_run: step {n + 1} is a CALLDATACOPY. Supply its whole charge as the next hint."
      let some costN ← natOf? cost
        | throwError "func_run: the CALLDATACOPY hint{indentExpr cost}is not a numeral"
      -- `List.sliceD`'s default is a `UInt8`, not a `Nat`: a `Nat` literal
      -- here elaborates but does not typecheck at the call site.
      let u8zero ← mkAppOptM ``OfNat.ofNat
        #[mkConst ``UInt8, mkNatLit 0, none]
      let val ← mkAppM ``Jaune.List.sliceD
        #[← mkAppM ``Jaune.Sevm.data #[sevm],
          ← mkAppM ``Jaune.B256.toNat #[si],
          ← mkAppM ``Jaune.B256.toNat #[sz], u8zero]
      let img ← mkAppM ``Jaune.Mem.write
        #[mem, ← mkAppM ``Jaune.B256.toNat #[di], val]
      let gas' ← mkGas gb goff costN
      let succ ← mkState base s img gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_calldatacopy_of
        [(0, sevm), (1, d), (2, di), (3, si), (4, sz), (5, s), (6, cost),
          (7, gas'), (8, img)] [9, 10, 11, 12]
      match gs with
      | [hstk, hcost, hw, hg] =>
        discharge hstk (← rflTacs)
        discharge hcost []
        discharge hw (← rflTacs)
        discharge hg (← gasTacs)
      | _ => throwError "func_run: CALLDATACOPY left {gs.length} obligations"
    | (``Jaune.Rinst.retdatacopy, #[]) => do
      let ([di, ri, sz], s) ← popStack 3 stk
        | throwError "func_run: RETURNDATACOPY"
      let some cost ← nextHint g (mkConst ``Nat)
        | throwError m!"func_run: step {n + 1} is a RETURNDATACOPY. Supply its whole charge as the next hint."
      let some costN ← natOf? cost
        | throwError "func_run: the RETURNDATACOPY hint{indentExpr cost}is not a numeral"
      let rdE ← mkAppM ``Jaune.Devm.returnData #[d]
      let u8zero ← mkAppOptM ``OfNat.ofNat
        #[mkConst ``UInt8, mkNatLit 0, none]
      let val ← mkAppM ``Jaune.List.sliceD
        #[rdE, ← mkAppM ``Jaune.B256.toNat #[ri],
          ← mkAppM ``Jaune.B256.toNat #[sz], u8zero]
      let img ← mkAppM ``Jaune.Mem.write
        #[mem, ← mkAppM ``Jaune.B256.toNat #[di], val]
      let gas' ← mkGas gb goff costN
      let succ ← mkState base s img gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_retdatacopy_of
        [(0, sevm), (1, d), (2, di), (3, ri), (4, sz), (5, s), (6, cost),
          (7, gas'), (8, img)] [9, 10, 11, 12, 13]
      let assum ← `(tactic| assumption)
      match gs with
      | [hstk, hcost, hbound, hw, hg] =>
        discharge hstk (← rflTacs)
        discharge hcost []
        -- The out-of-bounds guard is about the *child's* return data, which no
        -- rule here knows anything about; it goes back to the caller unless a
        -- hypothesis already says it.
        discharge hbound [assum]
        discharge hw (← rflTacs)
        discharge hg (← gasTacs)
      | _ => throwError "func_run: RETURNDATACOPY left {gs.length} obligations"
    | (``Jaune.Rinst.log, #[k]) => do
      let some kv ← natOf? (← mkAppM ``Fin.val #[k])
        | throwError "func_run: LOG index is not a literal{indentExpr k}"
      let (ws, s) ← popStack (2 + kv) stk
      let i := ws[0]!
      let sz := ws[1]!
      let topics ← mkListLit (mkConst ``Jaune.B256) (ws.drop 2)
      let some cost ← nextHint g (mkConst ``Nat)
        | throwError m!"func_run: step {n + 1} is a LOG. Supply its whole charge as the next hint."
      let some costN ← natOf? cost
        | throwError "func_run: the LOG hint{indentExpr cost}is not a numeral"
      let rd ← mkAppM ``Jaune.Mem.read
        #[mem, ← mkAppM ``Jaune.B256.toNat #[i],
          ← mkAppM ``Jaune.B256.toNat #[sz]]
      let dat ← mkAppM ``Prod.fst #[rd]
      let m' ← mkAppM ``Prod.snd #[rd]
      let entry ← mkAppM ``Jaune.Log.mk
        #[← mkAppM ``Jaune.Sevm.currentTarget #[sevm], topics, dat]
      let base' ← mkAppM ``Jaune.Devm.addLog #[d, entry]
      let gas' ← mkGas gb goff costN
      let succ ← mkState base' s m' gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_log_of
        [(0, sevm), (1, d), (2, k), (3, i), (4, sz), (5, topics), (6, s),
          (7, cost), (8, gas'), (9, m'), (10, dat)]
        [11, 12, 13, 14, 15, 16, 17]
      let assum ← `(tactic| assumption)
      match gs with
      | [hstk, hlen, hstatic, hcost, hdata, hmem, hg] =>
        discharge hstk (← rflTacs)
        discharge hlen (← rflTacs)
        discharge hstatic [assum]
        discharge hcost []
        discharge hdata (← rflTacs)
        discharge hmem (← rflTacs)
        discharge hg (← gasTacs)
      | _ => throwError "func_run: LOG left {gs.length} obligations"
    | (``Jaune.Rinst.sstore, #[]) => do
      let ([k, v], s) ← popStack 2 stk | throwError "func_run: SSTORE"
      let tgt ← mkAppM ``Jaune.Sevm.currentTarget #[sevm]
      let some cost ← nextHint g (mkConst ``Nat)
        | throwError m!"func_run: step {n + 1} is an SSTORE. Its charge depends on the original, current and new values and on the key's warmth; supply the whole charge as the next hint."
      let some costN ← natOf? cost
        | throwError "func_run: the SSTORE hint{indentExpr cost}is not a numeral"
      let rc ← mkAppM ``Jaune.sstoreNewRefundCounter
        #[v, ← mkAppM ``Jaune.getOrigStorVal #[sevm, tgt, k],
          ← mkAppM ``Jaune.Devm.getStorVal #[d, tgt, k],
          ← mkAppM ``Jaune.Devm.refundCounter #[d]]
      -- Warmth is read off the local context, exactly as at `SLOAD`, and for
      -- the same reason: it is a fact about the frame, and a hint here would
      -- let a caller assert warmth the frame does not carry.
      let warmProp ← mkAppM ``Membership.mem
        #[← mkAppM ``Jaune.Devm.accessedStorageKeys #[d],
          ← mkAppM ``Prod.mk #[tgt, k]]
      let isWarm ← g.withContext do
        (← getLCtx).findDeclM? fun decl => do
          if decl.isImplementationDetail then return none
          if ← withNewMCtxDepth (isDefEq decl.type warmProp) then
            return some decl.type
          else return none
      let assum ← `(tactic| assumption)
      let sentry ← `(tactic|
        (simp only [Devm.gasLeft_setMach, gCallStipend]; omega))
      let gas' ← mkGas gb goff costN
      let base' ←
        if isWarm.isSome then pure d
        else mkAppM ``Jaune.addAccessedStorageKey #[d, tgt, k]
      let stored ← mkAppM ``Jaune.Devm.setStorVal
        #[← mkAppM ``Jaune.Devm.withRefundCounter #[base', rc], tgt, k, v]
      let succ ← mkState stored s mem gas'
      fixPost post succ
      let name := if isWarm.isSome then ``Ninst.runCompiled_sstore_warm
        else ``Ninst.runCompiled_sstore_cold
      let gs ← applyLemma g name
        [(0, sevm), (1, d), (2, k), (3, v), (4, s), (5, cost), (6, gas'),
          (7, rc)] [8, 9, 10, 11, 12, 13, 14]
      match gs with
      | [hstk, hwarmth, hsentry, hstatic, hcost, hrefund, hg] =>
        discharge hstk (← rflTacs)
        discharge hwarmth [assum]
        discharge hsentry [assum, sentry]
        discharge hstatic [assum]
        discharge hcost []
        discharge hrefund (← rflTacs)
        discharge hg (← gasTacs)
      | _ => throwError "func_run: SSTORE left {gs.length} obligations"
    | _ => do
      let core ← whnfUntilHead
        [``Jaune.applyBinary, ``Jaune.applyUnary, ``Jaune.pushItem] 16
        (← mkAppM ``Jaune.Rinst.runCore #[mkNatLit 0, d, sevm, r'])
      let ne ← `(tactic| rintro ⟨⟩)
      let ne' ← `(tactic| exact nofun)
      let rfl' ← `(tactic| rfl)
      match core.getAppFnArgs with
      | (``Jaune.applyBinary, #[f, costE, _]) => do
        let some cost ← natOf? costE
          | throwError "func_run: the cost{indentExpr costE}is not a numeral"
        let ([x, y], s) ← popStack 2 stk | throwError "func_run: binary opcode"
        let v ← (do
          match ← nextHint g (mkConst ``Jaune.B256) with
          | some v => pure v
          | none => mkAppM' f #[x, y])
        let gas' ← mkGas gb goff cost
        let succ ← mkState base (← mkAppM ``List.cons #[v, s]) mem gas'
        fixPost post succ
        let gs ← applyLemma g ``Ninst.runCompiled_binary
          [(0, sevm), (1, d), (2, r'), (3, f), (4, costE), (5, gas'), (6, x),
            (7, y), (8, v), (9, s)] [10, 11, 12, 13, 14, 15]
        match gs with
        | [hne, hdef, hstk, hval, hg, hr] =>
          discharge hne [ne, ne']
          discharge hdef [rfl']
          discharge hstk (← rflTacs)
          dischargeValue hval (← valTacs)
          discharge hg (← gasTacs)
          discharge hr (← roomTacs)
        | _ => throwError "func_run: binary opcode left {gs.length} obligations"
      | (``Jaune.applyUnary, #[f, costE, _]) => do
        let some cost ← natOf? costE
          | throwError "func_run: the cost{indentExpr costE}is not a numeral"
        let ([x], s) ← popStack 1 stk | throwError "func_run: unary opcode"
        let v ← (do
          match ← nextHint g (mkConst ``Jaune.B256) with
          | some v => pure v
          | none => mkAppM' f #[x])
        let gas' ← mkGas gb goff cost
        let succ ← mkState base (← mkAppM ``List.cons #[v, s]) mem gas'
        fixPost post succ
        let gs ← applyLemma g ``Ninst.runCompiled_unary
          [(0, sevm), (1, d), (2, r'), (3, f), (4, costE), (5, gas'), (6, x),
            (7, v), (8, s)] [9, 10, 11, 12, 13, 14]
        match gs with
        | [hne, hdef, hstk, hval, hg, hr] =>
          discharge hne [ne, ne']
          discharge hdef [rfl']
          discharge hstk (← rflTacs)
          dischargeValue hval (← valTacs)
          discharge hg (← gasTacs)
          discharge hr (← roomTacs)
        | _ => throwError "func_run: unary opcode left {gs.length} obligations"
      | (``Jaune.pushItem, #[x, costE, _]) => do
        -- The `pushItem` class: `ADDRESS`, `CALLER`, `CALLVALUE`, `ORIGIN`,
        -- `CALLDATASIZE`, `CODESIZE`, `BASEFEE`, … .  Written for the class,
        -- because `Rinst.runCore` routes all of them through the same one-line
        -- arm and the only thing that differs is the word.
        --
        -- **No hint is consumed**, for `CALLDATALOAD`'s reason: `x` is a
        -- projection of `sevm` or `devm` that the evaluation already names, not
        -- a computation the walk has to be told the answer to.  Consuming one
        -- here would silently eat the hint the next `EQ` or `SHR` was given.
        let some cost ← natOf? costE
          | throwError "func_run: the cost{indentExpr costE}is not a numeral"
        let gas' ← mkGas gb goff cost
        let succ ← mkState base (← mkAppM ``List.cons #[x, stk]) mem gas'
        fixPost post succ
        let gs ← applyLemma g ``Ninst.runCompiled_pushItem
          [(0, sevm), (1, d), (2, r'), (3, x), (4, costE), (5, gas')]
          [6, 7, 8, 9]
        match gs with
        | [hne, hdef, hg, hr] =>
          discharge hne [ne, ne']
          discharge hdef [rfl']
          discharge hg (← gasTacs)
          discharge hr (← roomTacs)
        | _ => throwError "func_run: pushItem opcode left {gs.length} obligations"
      | _ =>
        throwError m!"func_run: step {n + 1}: no forward rule for{indentExpr i'}" ++ m!"\nIts evaluation is{indentExpr core}"
  | _ =>
    throwError "func_run: step {n + 1}: cannot step{indentExpr i'}"

/-- The walk itself: the relation's five rules, applied where `funcInv` would
have inverted them.  Which relation is `Ctx.rel`, fixed once from the goal's own
head by `funcRunMain` and never re-decided mid-walk. -/
partial def funcWalk (g : MVarId) : ForwardM Unit := g.withContext do
  let rel := (← get).rel
  -- The budget, checked before anything is read: the goal handed back is
  -- exactly the one the previous rule produced, with the state the walk wrote.
  if let some b := (← get).budget then
    if (← get).step ≥ b then
      modify fun c => { c with side := c.side.push g }
      return
  -- `consumeMData`: a goal produced by `refine … ?_` under an expected type
  -- carries a `noImplicitLambda` annotation, and an annotated application has
  -- no head constant at all.  Reading through it is what lets a walk resume
  -- from a goal a *lemma* handed back rather than from one the walk wrote.
  let t := (← instantiateMVars (← g.getType)).consumeMData
  match t.getAppFnArgs with
  | (head, #[fs, sevm, d, f, post]) => do
    unless head == rel.head do
      throwError "func_run: the goal is not a `{rel.head}`{indentExpr t}"
    let f' ← whnf f
    let g ← g.change
      (mkAppN (mkConst rel.head) #[fs, sevm, d, f', post])
    let (base, stk, mem, gas) ← parseState d
    let (gb, goff) ← parseGas gas
    match f'.getAppFnArgs with
    | (``Blanc.Func.next, #[i, rest]) => do
      -- A **spawning** instruction is where this layer stops by construction:
      -- its successor is whatever `Resume.run` makes of a child the walk knows
      -- nothing about, which is `Blanc/ForwardCall.lean`'s business and not a
      -- rule here.  The whole node goes back to the caller rather than being
      -- stepped, so a walk that meets a `CALL` hands over instead of failing.
      if ((← whnfR i).getAppFn.constName? == some ``Jaune.Ninst.exec) then
        modify fun c => { c with side := c.side.push g, step := c.step + 1 }
        return
      let gs ← applyLemma g rel.next
        [(0, fs), (1, sevm), (2, d), (3, i), (5, rest)] [7, 8]
      match gs with
      | [gi, gr] => ninstStep gi; funcWalk gr
      | _ => throwError "func_run: `.next` left {gs.length} obligations"
    | (``Blanc.Func.branch, #[fArm, gArm]) => do
      modify fun c => { c with step := c.step + 1 }
      let ([w], s) ← popStack 1 stk | throwError "func_run: BRANCH"
      let takesZero ←
        if w.nat? == some 0 then pure true
        else if (w.nat?).isSome then pure false
        else pure false
      if takesZero then
        let gas' ← mkGas gb goff 13
        let succ ← mkState base s mem gas'
        let gs ← applyLemma g rel.branchZero
          [(0, fs), (1, sevm), (2, d), (3, fArm), (4, gArm), (6, s), (7, gas')]
          [8, 9, 10, 11]
        match gs with
        | [hstk, hr, hg, harm] =>
          discharge hstk (← rflTacs)
          discharge hr (← roomTacs)
          discharge hg (← gasTacs)
          funcWalk (← retarget rel.head harm succ)
        | _ => throwError "func_run: `.zero` left {gs.length} obligations"
      else
        let gas' ← mkGas gb goff 14
        let succ ← mkState base s mem gas'
        let gs ← applyLemma g rel.branchSucc
          [(0, fs), (1, sevm), (2, d), (3, fArm), (4, gArm), (6, w), (7, s),
            (8, gas')] [9, 10, 11, 12, 13]
        let dec ← `(tactic| decide)
        let deck ← `(tactic| decide +kernel)
        match gs with
        | [hne, hstk, hr, hg, harm] =>
          if ← (do if ← tryTacOn hne dec then pure true else tryTacOn hne deck)
          then pure ()
          else
            throwError m!"func_run: cannot tell whether the branch is taken. The JUMPI condition is{indentExpr w}" ++ m!"\nGive that value a hint."
          discharge hstk (← rflTacs)
          discharge hr (← roomTacs)
          discharge hg (← gasTacs)
          funcWalk (← retarget rel.head harm succ)
        | _ => throwError "func_run: `.succ` left {gs.length} obligations"
    | (``Blanc.Func.call, #[k]) => do
      modify fun c => { c with step := c.step + 1 }
      let gas' ← mkGas gb goff 12
      let succ ← mkState base stk mem gas'
      let gs ← applyLemma g rel.call
        [(0, fs), (1, sevm), (2, d), (3, k), (6, gas')] [7, 8, 9, 10]
      let rfl' ← `(tactic| rfl)
      let dec ← `(tactic| decide)
      match gs with
      | [hget, hr, hg, hbody] =>
        unless (← tryTacOn hget rfl') || (← tryTacOn hget dec) do
          throwError m!"func_run: cannot resolve the table entry that `.call` refers to:{indentExpr k}"
        discharge hr (← roomTacs)
        discharge hg (← gasTacs)
        funcWalk (← retarget rel.head hbody succ)
      | _ => throwError "func_run: `.call` left {gs.length} obligations"
    | (``Blanc.Func.last, #[_]) =>
      modify fun c => { c with side := c.side.push g }
    | _ => throwError "func_run: cannot see the shape of{indentExpr f'}"
  | _ =>
    throwError "func_run: the goal is not a `{rel.head}`{indentExpr t}"

/-- Entry point.  The relation is read off the goal once, here, so that every
recursive call builds the same one and a mixed goal is an error rather than a
silent switch. -/
def funcRunMain (hints : List Term) (budget : Option Nat := none) :
    TacticM Unit := do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some rel := t.getAppFn.constName?.bind specOf?
    | throwError m!"func_run: the goal's head is not a relation this walk builds{indentExpr t}"
        ++ m!"\nIt builds {relSpecs.map (·.head)}."
  let (_, c) ← (funcWalk g).run
    { rel := rel, hints := hints, side := #[], step := 0, budget := budget }
  if c.step == 0 then
    throwError "func_run: applied no rule; nothing was proved"
  unless c.hints.isEmpty do
    throwError "func_run: {c.hints.length} hint(s) were never used"
  replaceMainGoal c.side.toList

end Forward

/-- Build a walk of a compiled `Func` forward from the state the goal names.

`func_run [v₁, …, vₙ]` walks the goal's `Func` and applies one rule per node,
naming every intermediate state itself.  The bracketed terms are the values the
walk cannot compute — what a comparison decided, what a shift produced, what a
memory expansion cost — consumed left to right; with none given, value-producing
opcodes keep their unevaluated application.

It builds whichever registered relation the goal is stated with:
`Func.RunCompiled`, `Blanc/Reverts.lean`'s `Func.RunCompiledTo`,
`Blanc/ForwardCall.lean`'s `Func.ExecTo`, or its outcome-aware
`Func.ExecWitness`.  One walk serves all four (`Forward.RelSpec`); the goal
decides which.

Everything it could not close comes back as a goal, in the order the walk met
it, ending with the frame's terminal instruction — which is where a
`Func.RunCompiledTo` walk's `.rev` is evaluated.

`func_run (n) […]` walks at most `n` nodes and then hands the residual walk
back as a goal, which is how a **prefix** of a `Func` is walked: a `Func` is
concrete all the way down, so its tail cannot be abstracted and the walk
stopped that way.  A walk that meets a *spawning* instruction stops on its own
and hands the node back whether or not a budget was given — crossing a `CALL`
is `Blanc/ForwardCall.lean`'s business, not a rule here. -/
syntax (name := funcRun) "func_run" (ppSpace "(" num ")")?
  (ppSpace "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| func_run $[($n)]? $[[$hs,*]]?) =>
    Forward.funcRunMain
      (match hs with
        | some hs => hs.getElems.toList
        | none => [])
      (n.map (·.getNat))

end ForwardTactic

end Blanc
