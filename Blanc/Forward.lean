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
the frame, and evaluating it is the caller's. -/

section ForwardTactic

-- `Blanc.Lean` exists (`Blanc/Tactics.lean` adds to it), so an unqualified
-- `open Lean` inside this namespace would open that instead of the real one.
open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic

namespace Forward

/-- The walk's mutable state: the hints it has not spent, the obligations it
could not close, and how many `Ninst` steps it has taken (for messages). -/
structure Ctx where
  hints : List Term
  side : Array MVarId
  step : Nat

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

/-- The gas obligation: always `base - n = (base - m) + c` over numerals. -/
def gasTacs : ForwardM (List (TSyntax `tactic)) := do
  let t ← `(tactic|
    (simp only [Devm.gasLeft_setMach, gVerylow, gBase, gHigh, gMid, gJumpdest,
      gasColdSload, gMemory]; omega))
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

/-- Restate a `Func.RunCompiled` goal with the state the walk wrote, instead of
the projection chain the applied lemma's conclusion produced. -/
def retarget (g : MVarId) (state : Expr) : MetaM MVarId := do
  let t ← instantiateMVars (← g.getType)
  match t.getAppFnArgs with
  | (``Blanc.Func.RunCompiled, #[fs, sevm, _, f, post]) =>
    g.change (mkAppN (mkConst ``Blanc.Func.RunCompiled) #[fs, sevm, state, f, post])
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
        discharge hval (← valTacs)
        discharge hg (← gasTacs)
        discharge hr (← roomTacs)
      | _ => throwError "func_run: CALLDATALOAD left {gs.length} obligations"
    | (``Jaune.Rinst.sload, #[]) => do
      let ([k], s) ← popStack 1 stk | throwError "func_run: SLOAD"
      let tgt ← mkAppM ``Jaune.Sevm.currentTarget #[sevm]
      -- No hint either: the value read is `Devm.getStorVal` at the key that is
      -- already on the stack.
      let v ← mkAppM ``Jaune.Devm.getStorVal #[d, tgt, k]
      let base' ← mkAppM ``Jaune.addAccessedStorageKey #[d, tgt, k]
      let gas' ← mkGas gb goff 2100
      let succ ← mkState base' (← mkAppM ``List.cons #[v, s]) mem gas'
      fixPost post succ
      let gs ← applyLemma g ``Ninst.runCompiled_sload_cold
        [(0, sevm), (1, d), (2, k), (3, v), (4, s), (5, gas')] [6, 7, 8, 9, 10]
      let assum ← `(tactic| assumption)
      match gs with
      | [hstk, hcold, hval, hg, hr] =>
        discharge hstk (← rflTacs)
        discharge hcold [assum]
        discharge hval (← valTacs)
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
    | _ => do
      let core ← whnfUntilHead [``Jaune.applyBinary, ``Jaune.applyUnary] 16
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
          discharge hval (← valTacs)
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
          discharge hval (← valTacs)
          discharge hg (← gasTacs)
          discharge hr (← roomTacs)
        | _ => throwError "func_run: unary opcode left {gs.length} obligations"
      | _ =>
        throwError m!"func_run: step {n + 1}: no forward rule for{indentExpr i'}" ++ m!"\nIts evaluation is{indentExpr core}"
  | _ =>
    throwError "func_run: step {n + 1}: cannot step{indentExpr i'}"

/-- The walk itself: `Func.RunCompiled`'s five rules, applied where `funcInv`
would have inverted them. -/
partial def funcWalk (g : MVarId) : ForwardM Unit := g.withContext do
  let t ← instantiateMVars (← g.getType)
  match t.getAppFnArgs with
  | (``Blanc.Func.RunCompiled, #[fs, sevm, d, f, post]) => do
    let f' ← whnf f
    let g ← g.change
      (mkAppN (mkConst ``Blanc.Func.RunCompiled) #[fs, sevm, d, f', post])
    let (base, stk, mem, gas) ← parseState d
    let (gb, goff) ← parseGas gas
    match f'.getAppFnArgs with
    | (``Blanc.Func.next, #[i, rest]) => do
      let gs ← applyLemma g ``Blanc.Func.RunCompiled.next
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
        let gs ← applyLemma g ``Func.runCompiled_branch_zero
          [(0, fs), (1, sevm), (2, d), (3, fArm), (4, gArm), (6, s), (7, gas')]
          [8, 9, 10, 11]
        match gs with
        | [hstk, hr, hg, harm] =>
          discharge hstk (← rflTacs)
          discharge hr (← roomTacs)
          discharge hg (← gasTacs)
          funcWalk (← retarget harm succ)
        | _ => throwError "func_run: `.zero` left {gs.length} obligations"
      else
        let gas' ← mkGas gb goff 14
        let succ ← mkState base s mem gas'
        let gs ← applyLemma g ``Func.runCompiled_branch_succ
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
          funcWalk (← retarget harm succ)
        | _ => throwError "func_run: `.succ` left {gs.length} obligations"
    | (``Blanc.Func.call, #[k]) => do
      modify fun c => { c with step := c.step + 1 }
      let gas' ← mkGas gb goff 12
      let succ ← mkState base stk mem gas'
      let gs ← applyLemma g ``Func.runCompiled_call'
        [(0, fs), (1, sevm), (2, d), (3, k), (6, gas')] [7, 8, 9, 10]
      let rfl' ← `(tactic| rfl)
      let dec ← `(tactic| decide)
      match gs with
      | [hget, hr, hg, hbody] =>
        unless (← tryTacOn hget rfl') || (← tryTacOn hget dec) do
          throwError m!"func_run: cannot resolve the table entry that `.call` refers to:{indentExpr k}"
        discharge hr (← roomTacs)
        discharge hg (← gasTacs)
        funcWalk (← retarget hbody succ)
      | _ => throwError "func_run: `.call` left {gs.length} obligations"
    | (``Blanc.Func.last, #[_]) =>
      modify fun c => { c with side := c.side.push g }
    | _ => throwError "func_run: cannot see the shape of{indentExpr f'}"
  | _ =>
    throwError "func_run: the goal is not a `Func.RunCompiled`{indentExpr t}"

/-- Entry point. -/
def funcRunMain (hints : List Term) : TacticM Unit := do
  let g ← getMainGoal
  let (_, c) ← (funcWalk g).run { hints := hints, side := #[], step := 0 }
  if c.step == 0 then
    throwError "func_run: applied no rule; nothing was proved"
  unless c.hints.isEmpty do
    throwError "func_run: {c.hints.length} hint(s) were never used"
  replaceMainGoal c.side.toList

end Forward

/-- Build a `Func.RunCompiled` derivation forward from the state the goal names.

`func_run [v₁, …, vₙ]` walks the goal's `Func` and applies one rule per node,
naming every intermediate state itself.  The bracketed terms are the values the
walk cannot compute — what a comparison decided, what a shift produced, what a
memory expansion cost — consumed left to right; with none given, value-producing
opcodes keep their unevaluated application.

Everything it could not close comes back as a goal, in the order the walk met
it, ending with the frame's terminal instruction. -/
syntax (name := funcRun) "func_run" (ppSpace "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| func_run $[[$hs,*]]?) =>
    Forward.funcRunMain <| match hs with
      | some hs => hs.getElems.toList
      | none => []

end ForwardTactic

end Blanc
