import Blanc.TransientSettlement

/-!
# Spike evidence: a faithful ERC-1967 forwarding proxy, compiled

Branch-local evidence for goal `proxy-delegatecall-spike-v1`, row **P4**, and
the last open **P2** item (returndata re-emission).  Deliberately outside
`Blanc/`: it binds no gate and states no baseline.

`scripts/ProxySpikeSpawn.lean` established the `DELEGATECALL` *edge* and
`scripts/ProxySpikeExec.lean` ran the child.  Neither of them ever wrote the
proxy.  This file writes it, compiles it, and asks the two questions a
forwarding proxy actually turns on: can Blanc's four `Func` constructors
express one, and can the child's returndata be re-emitted verbatim by the
parent?

Files under `scripts/` may not import one another, so everything here is
restated rather than imported.
-/

namespace Blanc.ProxySpikeProxy

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## The ERC-1967 implementation slot, as a literal

`scripts/ProxySpikeSlots.lean` *derives* this word — it defines the slot as
`Blanc.String.keccak "eip1967.proxy.implementation" - 1` and proves it equals
the published digit string.  A program may not carry that derived term: a
`pushB256 (Blanc.String.keccak … - 1)` puts the hash inside the `Func`, and
`Prog.compile` is then forced *by the elaborator* during compilation rather
than by the kernel, which is the `maxRecDepth` hazard recorded at
`Blanc/CommonCore.lean:2250-2256`.

So the program carries the literal, and exactly one theorem ties the literal to
the derivation.  That theorem is a kernel decision on one fixed input; it
assumes nothing about Keccak-256 and would remain a proof if the hash were
broken. -/

def implementationSlotLit : B256 :=
  0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc

/-- The literal in the program is the derived ERC-1967 logic slot. -/
theorem implementationSlotLit_derived :
    implementationSlotLit
      = Blanc.String.keccak "eip1967.proxy.implementation" - 1 := by
  decide +kernel

/-! ## The proxy

Every operand order below was read off Jaune's own source rather than off the
EVM's documentation:

* `CALLDATACOPY` pops **memStart, dataStart, size** (`Jaune/Machine.lean`,
  the `.calldatacopy` arm of `Rinst.runCore`);
* `RETURNDATACOPY` pops **memStart, dataStart, size**, and its out-of-range
  read is an exceptional halt charged *after* the gas (the `.retdatacopy` arm);
* `DELEGATECALL` pops **gas, addr, argsOffset, argsSize, retOffset, retSize**
  — six words, no value (`Jaune/Execution.lean`, `Xinst.step`);
* `RETURN`/`REVERT` pop **offset then size** (`Linst.run`), so the size is
  pushed first;
* `Func.branch p q` compiles to `PUSH2 loc; JUMPI; <p>; JUMPDEST; <q>`
  (`Blanc.Func.compile`), so `p` is the **fall-through** arm taken when the
  condition word is zero and `q` is the **jumped-to** arm.  `Func.branch` is
  written out rather than the `<?>` notation, which flips the two.

The `retOffset`/`retSize` window is `(0, 0)`: this proxy never lets the
`DELEGATECALL` write the child's output into memory for it, because the size is
not known until `RETURNDATASIZE` can be asked.  It copies afterwards instead,
which is what a real ERC-1967 proxy does and what makes the returndata probe
below the load-bearing one. -/

def proxyFallback : Func :=
  -- 1. copy the whole calldata to memory[0 .. cds)
  calldatasize ::: pushB256 0 ::: pushB256 0 ::: calldatacopy :::
  -- 2. the six DELEGATECALL operands, deepest pushed first
  pushB256 0 :::                                   -- retSize   = 0
  pushB256 0 :::                                   -- retOffset = 0
  calldatasize :::                                 -- argsSize
  pushB256 0 :::                                   -- argsOffset
  pushB256 implementationSlotLit ::: sload :::     -- implementation address
  gas :::                                          -- forward all remaining gas
  delcall :::
  -- 3. copy the child's returndata verbatim to memory[0 .. rds)
  retdatasize ::: dup 0 ::: pushB256 0 ::: pushB256 0 ::: retdatacopy :::
  -- stack is now [rds, success]; bring success to the top for the branch
  swap 0 :::
  Func.branch
    (pushB256 0 ::: Func.last .rev)     -- success = 0   -> revert verbatim
    (pushB256 0 ::: Func.last .ret)     -- success /= 0  -> return verbatim

def proxyProg : Prog := ⟨proxyFallback, []⟩

def proxyBytes : Bytes := (Prog.compile proxyProg).getD []

def proxyCode : ByteArray := ByteArray.mk proxyBytes.toArray

theorem proxyProg_compiles : proxyProg.compiles = true := by decide

theorem proxyProg_compile : Prog.compile proxyProg = some proxyBytes :=
  Prog.compile_eq_some_getD_of_compiles _ proxyProg_compiles

/-- Sixty bytes:

```
5b                   JUMPDEST        -- Prog entry
36                   CALLDATASIZE
5f 5f                PUSH0 PUSH0
37                   CALLDATACOPY    -- memory[0 .. cds) := calldata
5f 5f                PUSH0 PUSH0     -- retSize, retOffset
36                   CALLDATASIZE    -- argsSize
5f                   PUSH0           -- argsOffset
7f 3608 94a1 3ba1 a321 0667 c828 492d b98d ca3e 2076 cc37 35a9 20a3 ca50 5d38 2bbc
                     PUSH32 <implementation slot>
54                   SLOAD
5a                   GAS
f4                   DELEGATECALL
3d                   RETURNDATASIZE
80                   DUP1
5f 5f                PUSH0 PUSH0
3e                   RETURNDATACOPY  -- memory[0 .. rds) := returndata
90                   SWAP1
61 00 39             PUSH2 0x0039
57                   JUMPI
5f                   PUSH0
fd                   REVERT          -- fall-through: the call failed
5b                   JUMPDEST        -- byte 0x39 = 57
5f                   PUSH0
f3                   RETURN          -- jumped-to: the call succeeded
```

The digits were read off `#eval` in a scratch file outside this repository, not
recalled; the length below is the kernel's own count of the same list. -/
theorem proxyBytes_length : proxyBytes.length = 60 := by decide +kernel

/-- Not an EIP-7702 designator, so a `DELEGATECALL` that lands on this code is
not accidentally testing 7702 resolution. -/
theorem proxyCode_notDelegation : getDelegatedCodeAddress proxyCode = none := by
  decide +kernel

/-! ## The implementation behind the proxy

Row P4 asks for a spike implementation carrying **a guarded persistent write, a
revert path, and a returndata-bearing success path**.  All three live in one
program rather than three, so that the branch is a real guard rather than a
selector-shaped decoration: the two arms are reached by the same entry with
different calldata.

`cdl 0` is `PUSH0; CALLDATALOAD` — calldata word 0, zero-padded past the end
(`Blanc.arg`'s recorded convention), so an empty call reads `0` and takes the
revert arm rather than halting.

The arm assignment follows the compiler, not intuition: `iszero` pushes `0`
when the guard word is nonzero, and a zero condition word **falls through**, so
the fall-through arm is the *write* arm and the jumped-to arm is the revert. -/

def implSlot : B256 := 7

def implGuarded : Func :=
  cdl 0 +++ iszero :::                       -- guard word = calldata word 0
  Func.branch
    -- guard /= 0: `iszero` pushed 0, so this fall-through arm runs
    ( pushB256 1 ::: pushB256 implSlot ::: sstore :::
      pushB256 42 ::: mstoreAt 0 +++ pushB256 32 ::: pushB256 0 :::
      Func.last .ret )
    -- guard = 0: `iszero` pushed 1, so control jumps here
    ( pushB256 0 ::: pushB256 0 ::: Func.last .rev )

def implGuardedProg : Prog := ⟨implGuarded, []⟩

def implGuardedBytes : Bytes := (Prog.compile implGuardedProg).getD []

def implGuardedCode : ByteArray := ByteArray.mk implGuardedBytes.toArray

/-- The word the success arm returns, so the returndata clauses below are
stated against a name rather than a numeral. -/
def implReturnWord : B256 := 42

theorem implGuardedProg_compiles : implGuardedProg.compiles = true := by decide

theorem implGuardedProg_compile :
    Prog.compile implGuardedProg = some implGuardedBytes :=
  Prog.compile_eq_some_getD_of_compiles _ implGuardedProg_compiles

/-- Twenty-five bytes:

```
5b                   JUMPDEST        -- Prog entry
5f 35                PUSH0 CALLDATALOAD
15                   ISZERO
61 00 15             PUSH2 0x0015
57                   JUMPI
60 01 60 07 55       PUSH1 1 PUSH1 7 SSTORE     -- guarded persistent write
60 2a 5f 52          PUSH1 42 PUSH0 MSTORE
60 20 5f f3          PUSH1 32 PUSH0 RETURN      -- 32-byte returndata
5b                   JUMPDEST        -- byte 0x15 = 21
5f 5f fd             PUSH0 PUSH0 REVERT         -- revert path
```

Read off `#eval` in a scratch file outside this repository. -/
theorem implGuardedBytes_length : implGuardedBytes.length = 25 := by
  decide +kernel

/-- Not an EIP-7702 designator. -/
theorem implGuardedCode_notDelegation :
    getDelegatedCodeAddress implGuardedCode = none := by decide +kernel


/-! ## Memory and gas arithmetic

The two charges a forwarding proxy pays that a fixed-shape contract does not:
one memory window whose width is the *caller's* calldata length, and a second
whose width is the *callee's* returndata length.  Both are named here as
functions of those two lengths, so that everything below is parametric in
`cds` and `rds` rather than instantiated at a chosen pair. -/

/-- `Devm.extCost` at a single window, with the `let` and the one-element
`memExtsSize` unfolded.  Memory expansion reads nothing but the image's *size*,
which is what makes every charge below a function of two numbers. -/
private lemma extCost_single (d : Devm) (i n : Nat) :
    d.extCost [⟨i, n⟩]
      = calculateMemoryGasCost (memExtSize d.memory.size i n)
        - calculateMemoryGasCost d.memory.size := rfl

/-- The charge for opening `[0, n)` over empty memory: what the proxy's
`CALLDATACOPY` pays to land `cds` bytes of calldata at offset `0`. -/
def openWindowGas (n : Nat) : Nat := calculateMemoryGasCost (memExtSize 0 0 n)

/-- The extra charge for widening an image that already covers `[0, cds)` so
that it also covers `[0, rds)`: what the proxy's `RETURNDATACOPY` pays.  It is
`0` whenever the returndata is no wider than the calldata, which is the common
case for a getter behind a proxy. -/
def widenWindowGas (cds rds : Nat) : Nat :=
  calculateMemoryGasCost (memExtSize (memExtSize 0 0 cds) 0 rds)
    - calculateMemoryGasCost (memExtSize 0 0 cds)

private lemma extCost_empty {d : Devm} {n : Nat} (h : d.memory = Mem.empty) :
    d.extCost [⟨0, n⟩] = openWindowGas n := by
  rw [extCost_single, h]
  rfl

private lemma extCost_open {d : Devm} {cds rds : Nat}
    (h : d.memory.size = memExtSize 0 0 cds) :
    d.extCost [⟨0, rds⟩] = widenWindowGas cds rds := by
  rw [extCost_single, h]
  rfl

/-! ### The 63/64 rule, read as a retention bound

`GAS` pushes the frame's whole remaining account, so the proxy asks the child
for everything it has.  `calculateMsgCallGas` refuses: the child's allowance is
capped at `except64th` of what is left once memory expansion and the access
charge are paid.  Stating that as an *allowance* bound says nothing a proxy
cares about; stating it as a **retention** bound says the thing the proxy's
tail depends on — that a 64th survives the call to pay for re-emission. -/

theorem parent_retains_64th (gw gl mc eg : Nat) (h : eg + mc ≤ gl) :
    (gl - mc - eg) / 64 ≤ gl - ((calculateMsgCallGas 0 gw gl mc eg).1 + mc) := by
  have hif : ¬ (gl < eg + mc) := by omega
  have hval : (calculateMsgCallGas 0 gw gl mc eg).1
      = min gw (except64th (gl - mc - eg)) + eg := by
    simp only [calculateMsgCallGas, if_neg hif]
  rw [hval, except64th]
  have hmin : min gw ((gl - mc - eg) - (gl - mc - eg) / 64)
      ≤ (gl - mc - eg) - (gl - mc - eg) / 64 := Nat.min_le_right _ _
  have hdiv : (gl - mc - eg) / 64 ≤ gl - mc - eg := Nat.div_le_self _ _
  omega


/-! ## The returndata re-emission probe

The last open **P2** item.  A forwarding proxy is only faithful if the child's
returndata reaches the caller *verbatim*, and Blanc had never crossed that:
`Blanc/ForwardCall.lean` reads a call's status word and its memory window, and
`scripts/ProxySpikeExec.lean` reads the child's `output` at the settlement, but
nothing had run `RETURNDATASIZE`/`RETURNDATACOPY` against a returned word.

**Altitude reached.**  The `Resume.run` step is Jaune's own CALL-family return
path, and the five instructions after it are `Ninst.RunCompiled` steps — the
same relation `Func.RunCompiledTo` is built from, applied through Blanc's own
forward step lemmas.  What is *not* here is the `Frame.enter`/`Xinst.step`
crossing that produces the settled child in the first place; that is
`scripts/ProxySpikeSpawn.lean`'s `Ninst.runCompiled_delcall_doneFrame`, whose
`h_enter`/`h_res` premises this chain supplies the second of.  So the claim is
about the parent's re-emission tail over an *arbitrary* successfully settled
child whose output is a 32-byte word, not about a whole proxy walk. -/

/-- The state a `(0, 0)`-window CALL-family return leaves the parent in.

The output window is `(0, 0)` because the proxy cannot know the returndata's
width until `RETURNDATASIZE` can be asked, so it declines the opcode's own
copy — and `Devm.memWrite _ []` is the identity, which is why this state's
memory is the parent's untouched. -/
def resumeState (parent child : Devm) : Devm :=
  (incorporateChildOnSuccess parent child child.output).setMach
    ⟨1 :: parent.stack, parent.memory, parent.gasLeft + child.gasLeft⟩

theorem resumeState_eq {parent child : Devm} (h_ok : child.error.isSome = false)
    (h_room : parent.stack.length < 1024) :
    Resume.run (.call parent 0 0) (.ok child)
      = .ok (resumeState parent child) := by
  rw [Resume.run_call_ok h_ok h_room, List.take_zero, Devm.memWrite_nil]
  rfl

/-- **The child's output is the parent's returndata.**  This is the
observability half of the probe, and it is `rfl`: `incorporateChildOnSuccess`
installs the third argument, and `Resume.run` passes `child.output` there. -/
theorem resumeState_returnData (parent child : Devm) :
    (resumeState parent child).returnData = child.output := rfl

theorem resumeState_memory (parent child : Devm) :
    (resumeState parent child).memory = parent.memory := rfl

theorem resumeState_stack (parent child : Devm) :
    (resumeState parent child).stack = 1 :: parent.stack := rfl

theorem resumeState_gasLeft (parent child : Devm) :
    (resumeState parent child).gasLeft = parent.gasLeft + child.gasLeft := rfl

/-- The re-emission tail's charge over a 32-byte returndata word and an
untouched memory: `RETURNDATASIZE`, `DUP1`, two `PUSH0`s, and a
`RETURNDATACOPY` that pays one word of copy and one word of expansion. -/
def reemitGas : Nat :=
  gBase + gVerylow + gBase + gBase
    + (gVerylow + gReturnDataCopy * 1 + gMemory)

theorem reemitGas_eq : reemitGas = 18 := by decide

/-- A 32-byte returndata word, copied out whole, is the whole of it. -/
theorem returndata_slice_whole (w : B256) :
    w.toBytes.sliceD 0 32 0 = w.toBytes := by
  show List.takeD 32 (List.drop 0 w.toBytes) 0 = w.toBytes
  rw [List.drop_zero, List.takeD_eq_self 0 (B256.length_toBytes w).symm]

/-- **The probe.**  After a successfully settled child that returned a 32-byte
word, the parent's `RETURNDATASIZE` observes `32` and its `RETURNDATACOPY`
lands exactly the child's bytes at `memory[0 .. 32)`, which the following
`RETURN` then re-emits.  The five instructions are the proxy's own tail, in
the order `Func.compile` emits them.

Note which way the out-of-bounds guard falls.  `RETURNDATACOPY` halts
exceptionally when `dataStart + size` exceeds the returndata, and charges the
gas *before* checking (`Jaune/Machine.lean`, the `.retdatacopy` arm) — so a
proxy that copied a guessed width could burn the frame and halt.  This one
takes its `size` from `RETURNDATASIZE` and its `dataStart` from `PUSH0`, so the
guard is discharged here at `0 + 32 ≤ 32`: an *equality*, not a margin.  Using
the observed size is what makes the halt unreachable. -/
theorem delcall_returndata_reemitted_verbatim
    (sevm : Sevm) (parent child : Devm) (w : B256) (G : Nat)
    (h_ok : child.error.isSome = false)
    (h_out : child.output = w.toBytes)
    (h_mem : parent.memory = Mem.empty)
    (h_room : parent.stack.length + 4 < 1024)
    (h_gas : parent.gasLeft + child.gasLeft = G + reemitGas) :
    ∃ d₁ d₂ d₃ d₄ d₅,
      -- the `DELEGATECALL`'s own return path, at a `(0, 0)` output window
      Resume.run (.call parent 0 0) (.ok child)
        = .ok (resumeState parent child) ∧
      (resumeState parent child).returnData = w.toBytes ∧
      (resumeState parent child).memory = Mem.empty ∧
      (resumeState parent child).stack = 1 :: parent.stack ∧
      -- `RETURNDATASIZE` observes 32
      Ninst.RunCompiled sevm (resumeState parent child) retdatasize d₁ ∧
      d₁.stack = (32 : B256) :: 1 :: parent.stack ∧
      -- the stack plumbing the proxy actually emits
      Ninst.RunCompiled sevm d₁ (dup 0) d₂ ∧
      Ninst.RunCompiled sevm d₂ (pushB256 0) d₃ ∧
      Ninst.RunCompiled sevm d₃ (pushB256 0) d₄ ∧
      d₄.stack = (0 : B256) :: 0 :: 32 :: 32 :: 1 :: parent.stack ∧
      -- `RETURNDATACOPY` copies exactly those bytes into the parent's memory
      Ninst.RunCompiled sevm d₄ retdatacopy d₅ ∧
      d₅.stack = (32 : B256) :: 1 :: parent.stack ∧
      d₅.memory = Mem.empty.write 0 w.toBytes ∧
      (d₅.memory.read 0 32).1 = w.toBytes ∧
      d₅.gasLeft = G := by
  rw [reemitGas_eq] at h_gas
  have h_room' : parent.stack.length < 1024 := by omega
  -- the resumed state's four projections
  have hR_rd : (resumeState parent child).returnData = w.toBytes := by
    rw [resumeState_returnData, h_out]
  have hR_mem : (resumeState parent child).memory = Mem.empty := by
    rw [resumeState_memory, h_mem]
  have hR_stk : (resumeState parent child).stack = 1 :: parent.stack :=
    resumeState_stack parent child
  have hR_gas : (resumeState parent child).gasLeft = G + 18 := by
    rw [resumeState_gasLeft, h_gas]
  have hzero : ((0 : B256)).toNat = 0 := by decide
  have h32 : ((32 : B256)).toNat = 32 := by decide
  -- 1. RETURNDATASIZE
  obtain ⟨d₁, step1, hs1, hm1, hr1, hg1⟩ :
      ∃ d₁, Ninst.RunCompiled sevm (resumeState parent child) retdatasize d₁ ∧
        d₁.stack = (32 : B256) :: 1 :: parent.stack ∧
        d₁.memory = Mem.empty ∧ d₁.returnData = w.toBytes ∧
        d₁.gasLeft = G + 16 := by
    refine ⟨_, Ninst.runCompiled_pushItem (x := (32 : B256)) (cost := gBase)
      (G := G + 16) (by rintro ⟨⟩) ?_ ?_ ?_, ?_, ?_, ?_, ?_⟩
    · show pushItem ((resumeState parent child).returnData.length).toB256
        gBase (resumeState parent child) = _
      rw [hR_rd, B256.length_toBytes]
      rfl
    · rw [hR_gas]; show G + 18 = G + 16 + 2; omega
    · rw [hR_stk]; simp only [List.length_cons]; omega
    · show (32 : B256) :: (resumeState parent child).stack = _
      rw [hR_stk]
    · show (resumeState parent child).memory = _; exact hR_mem
    · show (resumeState parent child).returnData = _; exact hR_rd
    · rfl
  -- 2. DUP1
  obtain ⟨d₂, step2, hs2, hm2, hr2, hg2⟩ :
      ∃ d₂, Ninst.RunCompiled sevm d₁ (dup 0) d₂ ∧
        d₂.stack = (32 : B256) :: 32 :: 1 :: parent.stack ∧
        d₂.memory = Mem.empty ∧ d₂.returnData = w.toBytes ∧
        d₂.gasLeft = G + 13 := by
    refine ⟨_, Ninst.runCompiled_dup (n := 0) (w := (32 : B256)) (G := G + 13)
      ?_ ?_ ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs1]; rfl
    · rw [hg1]; show G + 16 = G + 13 + 3; omega
    · rw [hs1]; simp only [List.length_cons]; omega
    · show (32 : B256) :: d₁.stack = _; rw [hs1]
    · show d₁.memory = _; exact hm1
    · show d₁.returnData = _; exact hr1
    · rfl
  -- 3. PUSH0
  obtain ⟨d₃, step3, hs3, hm3, hr3, hg3⟩ :
      ∃ d₃, Ninst.RunCompiled sevm d₂ (pushB256 0) d₃ ∧
        d₃.stack = (0 : B256) :: 32 :: 32 :: 1 :: parent.stack ∧
        d₃.memory = Mem.empty ∧ d₃.returnData = w.toBytes ∧
        d₃.gasLeft = G + 11 := by
    refine ⟨_, Ninst.runCompiled_pushB256 (w := (0 : B256)) (c := gBase)
      (G := G + 11) rfl ?_ ?_, ?_, ?_, ?_, ?_⟩
    · rw [hg2]; show G + 13 = G + 11 + 2; omega
    · rw [hs2]; simp only [List.length_cons]; omega
    · show (0 : B256) :: d₂.stack = _; rw [hs2]
    · show d₂.memory = _; exact hm2
    · show d₂.returnData = _; exact hr2
    · rfl
  -- 4. PUSH0
  obtain ⟨d₄, step4, hs4, hm4, hr4, hg4⟩ :
      ∃ d₄, Ninst.RunCompiled sevm d₃ (pushB256 0) d₄ ∧
        d₄.stack = (0 : B256) :: 0 :: 32 :: 32 :: 1 :: parent.stack ∧
        d₄.memory = Mem.empty ∧ d₄.returnData = w.toBytes ∧
        d₄.gasLeft = G + 9 := by
    refine ⟨_, Ninst.runCompiled_pushB256 (w := (0 : B256)) (c := gBase)
      (G := G + 9) rfl ?_ ?_, ?_, ?_, ?_, ?_⟩
    · rw [hg3]; show G + 11 = G + 9 + 2; omega
    · rw [hs3]; simp only [List.length_cons]; omega
    · show (0 : B256) :: d₃.stack = _; rw [hs3]
    · show d₃.memory = _; exact hm3
    · show d₃.returnData = _; exact hr3
    · rfl
  -- 5. RETURNDATACOPY
  obtain ⟨d₅, step5, hs5, hm5, hg5⟩ :
      ∃ d₅, Ninst.RunCompiled sevm d₄ retdatacopy d₅ ∧
        d₅.stack = (32 : B256) :: 1 :: parent.stack ∧
        d₅.memory = Mem.empty.write 0 w.toBytes ∧
        d₅.gasLeft = G := by
    refine ⟨_, Ninst.runCompiled_retdatacopy_of (di := (0 : B256))
      (ri := (0 : B256)) (sz := (32 : B256))
      (s := (32 : B256) :: 1 :: parent.stack) (c := 9) (G := G)
      (M := Mem.empty.write 0 w.toBytes) hs4 ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
    · rw [hzero, h32, extCost_empty hm4]; decide
    · rw [hzero, h32, hr4, B256.length_toBytes]
    · rw [hzero, h32, hm4, hr4, returndata_slice_whole]
    · rw [hg4]
    · rfl
    · rfl
    · rfl
  exact ⟨d₁, d₂, d₃, d₄, d₅, resumeState_eq h_ok h_room', hR_rd, hR_mem, hR_stk,
    step1, hs1, step2, step3, step4, hs4, step5, hs5, hm5,
    by rw [hm5]; exact Mem.read_write_word, hg5⟩

/-! ## Memory and gas realizability, parametric in `cds` and `rds`

Everything above is about one instruction or one edge.  This section asks the
question a *proxy* raises that a fixed-shape contract does not: the two memory
windows and the whole gas schedule are functions of two lengths the contract
does not choose — the caller's calldata length `cds` and the callee's
returndata length `rds` — so a proxy is only realizable if there is a gas
account that pays for the schedule *at every* `cds` and `rds`.

The premises are stated as Jaune's own expressions and the answer is a
**construction**: an explicit witness, not an existence argument. -/

/-- Rounding a byte count up to whole words: `ceilDiv (32 * k) 32 = k`. -/
private lemma ceilDiv_mul_32 (k : Nat) : ceilDiv (32 * k) 32 = k := by
  unfold ceilDiv
  split <;> omega

/-- **Re-accessing a window already open is free of expansion.**  The proxy
depends on this twice: its `DELEGATECALL` names the `[0, cds)` args window that
`CALLDATACOPY` has already opened, and its `RETURN` names the `[0, rds)` window
that `RETURNDATACOPY` has already opened. -/
private lemma memExtSize_idem (s i n : Nat) :
    memExtSize (memExtSize s i n) i n = memExtSize s i n := by
  by_cases h : n = 0
  · simp only [memExtSize, if_pos h]
  · have hs : ∀ c, memExtSize c i n
        = 32 * max (ceilDiv c 32) (ceilDiv (i + n) 32) := by
      intro c; simp only [memExtSize, if_neg h]
    rw [hs, hs, ceilDiv_mul_32]
    omega

/-- The `DELEGATECALL`'s own memory charge is zero: its args window is the one
`CALLDATACOPY` opened, and its `(0, 0)` output window is empty. -/
theorem extCost_delcall_window {d : Devm} {cds : Nat}
    (h : d.memory.size = memExtSize 0 0 cds) :
    d.extCost [⟨0, cds⟩, ⟨0, 0⟩] = 0 := by
  show calculateMemoryGasCost
      (memExtSize (memExtSize d.memory.size 0 cds) 0 0)
    - calculateMemoryGasCost d.memory.size = 0
  rw [h, show ∀ x, memExtSize x 0 0 = x from fun _ => rfl, memExtSize_idem]
  omega

/-- And the closing `RETURN` pays no expansion either. -/
theorem extCost_return_window {d : Devm} {cds rds : Nat}
    (h : d.memory.size = memExtSize (memExtSize 0 0 cds) 0 rds) :
    d.extCost [⟨0, rds⟩] = 0 := by
  rw [extCost_single, h, memExtSize_idem]
  omega

/-- `ceil32` — the rounding `Mem.write` applies when it grows an image — and
`memExtSize 0 0 ·` — the rounding the *charge* is computed against — are the
same function.

What this does and does not settle: it removes the only arithmetic gap between
the two roundings, so a memory-size premise phrased with `memExtSize` is the
one a `Mem.write` at offset `0` over empty memory produces.  It does **not**
discharge that premise: `Mem.write`'s own size law is a case split on whether
the window already fits, and Blanc states it (`Mem.size_write_word_at`) only
for a one-word payload, not for a `cds`-byte one.  The memory premises below
are therefore hypotheses, and this lemma is what makes them satisfiable rather
than a proof that they hold. -/
theorem ceil32_eq_memExtSize (n : Nat) : ceil32 n = memExtSize 0 0 n := by
  by_cases h : n = 0
  · subst h; rfl
  · have hz : ceilDiv 0 32 = 0 := rfl
    simp only [memExtSize, if_neg h, hz, Nat.max_eq_right (Nat.zero_le _)]
    unfold ceil32 ceilDiv
    split <;> split <;> omega

/-! ### The proxy's gas schedule

Written out instruction by instruction, in the order `Func.compile` emits them,
with the two length-dependent charges left as functions of `cds` and `rds`.
The `SLOAD` and the `DELEGATECALL`'s account access are left as parameters
because each is cold or warm depending on the caller, and a proxy cannot know
which. -/

/-- Everything charged before the `DELEGATECALL`, including the `JUMPDEST` a
compiled `Prog` is entered through. -/
def proxyPreCallGas (cds sloadCost : Nat) : Nat :=
  gJumpdest                                          -- Prog entry JUMPDEST
    + (gBase + gBase + gBase)                        -- CALLDATASIZE PUSH0 PUSH0
    + (gVerylow + gasCopy * ceilDiv cds 32 + openWindowGas cds)  -- CALLDATACOPY
    + (gBase + gBase + gBase + gBase)   -- PUSH0 PUSH0 CALLDATASIZE PUSH0
    + gVerylow                                       -- PUSH32 <slot>
    + sloadCost                                      -- SLOAD
    + gBase                                          -- GAS

/-- Everything charged after the `DELEGATECALL` returns, on the success arm.
`gVerylow + gHigh + gJumpdest` is the branch's own charge on the jumped-to arm,
which is what `Func.RunCompiledTo.succ` burns (`Blanc/Reverts.lean`); the
closing `RETURN` contributes no expansion once its window is open, which is
`extCost_return_window` under that lemma's memory-size hypothesis. -/
def proxyPostCallGas (cds rds : Nat) : Nat :=
  gBase                                              -- RETURNDATASIZE
    + gVerylow                                       -- DUP1
    + (gBase + gBase)                                -- PUSH0 PUSH0
    + (gVerylow + gReturnDataCopy * ceilDiv rds 32 + widenWindowGas cds rds)
                                                     -- RETURNDATACOPY
    + gVerylow                                       -- SWAP1
    + (gVerylow + gHigh + gJumpdest)                 -- PUSH2 JUMPI JUMPDEST
    + gBase                                          -- PUSH0

/-- **The tail is payable out of the 64th.**  Whatever word `GAS` pushed — the
proxy pushes its whole account — the child cannot take so much that the parent
is left unable to re-emit, provided the frame arrived at the call with 64 times
the tail's cost above the memory and access charges. -/
theorem proxy_tail_payable (cds rds mc eg gw gl : Nat)
    (h_room : eg + mc ≤ gl)
    (h_budget : 64 * proxyPostCallGas cds rds ≤ gl - mc - eg) :
    proxyPostCallGas cds rds
      ≤ gl - ((calculateMsgCallGas 0 gw gl mc eg).1 + mc) := by
  have h := parent_retains_64th gw gl mc eg h_room
  have hdiv : proxyPostCallGas cds rds ≤ (gl - mc - eg) / 64 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  omega

/-- **Realizability.**  For *every* calldata length and *every* returndata
length there is an explicit gas account at the `DELEGATECALL` that satisfies
all three premises at once — the frame can pay the memory and access charges,
it carries 64 times the re-emission tail above them, and consequently the tail
survives the 63/64 split whatever the child is handed.

No bound on `cds` or `rds` is needed: the witness is a function of them.  `mc`
and `eg` are left as parameters, and `extCost_delcall_window` above is what
lets a caller instantiate `mc := 0`. -/
theorem proxy_resources_realizable (cds rds mc eg : Nat) :
    ∃ gl,
      gl = mc + eg + 64 * proxyPostCallGas cds rds ∧
      eg + mc ≤ gl ∧
      64 * proxyPostCallGas cds rds ≤ gl - mc - eg ∧
      ∀ gw, proxyPostCallGas cds rds
        ≤ gl - ((calculateMsgCallGas 0 gw gl mc eg).1 + mc) :=
  ⟨mc + eg + 64 * proxyPostCallGas cds rds, rfl, by omega, by omega,
    fun gw => proxy_tail_payable cds rds mc eg gw _ (by omega) (by omega)⟩

/-- The whole message's requirement at the realizable witness: the pre-call
schedule plus the account the witness names. -/
def proxyMessageGas (cds rds sloadCost eg : Nat) : Nat :=
  proxyPreCallGas cds sloadCost + (eg + 64 * proxyPostCallGas cds rds)

/-- A worked instance, so the schedule is a number and not only a formula: a
four-byte selector-only call whose implementation returns one word, entered
with a cold implementation slot and a cold implementation account. -/
theorem proxyMessageGas_cold_4_32 :
    proxyMessageGas 4 32 gasColdSload gasColdAccountAccess = 6905 := by
  decide

/-- The same call once both the slot and the account are warm. -/
theorem proxyMessageGas_warm_4_32 :
    proxyMessageGas 4 32 gasWarmAccess gasWarmAccess = 2405 := by decide


/-! ## What the shape of this proxy settles

Four things about the *representation*, recorded here as the design facts they
are rather than re-proved:

1. **No new constructor.**  `proxyFallback` is built from `Func.next`,
   `Func.branch` and `Func.last` — three of the four constructors
   `Blanc/Semantics.lean` already declares.  The fourth, `Func.call`, is not
   used, and **no fifth constructor was needed**: a `DELEGATECALL` is an
   ordinary `Ninst.exec`, and the success/failure decision is an ordinary
   `.branch`.

2. **Every jump target is a static `PUSH2` literal.**  `Blanc.Func.compile`
   emits a branch as `[0x61] ++ [(loc >>> 8).toUInt8, loc.toUInt8] ++ [JUMPI]
   ++ <p> ++ [JUMPDEST] ++ <q>`, with `loc` computed at compile time from the
   length of the compiled fall-through arm and guarded by `loc < 2 ^ 16`; the
   only other jump-emitting node, `Func.call`, likewise pushes a literal from
   the compile-time table.  So **there is no computed jump** anywhere in a
   compiled Blanc program, and none was wanted here: `proxyBytes` above shows
   the single `61 00 39`, whose operand is the offset of the `5b` at byte 57.

3. **The forwarded address is data, not code.**  What a proxy varies at
   run time is the `DELEGATECALL`'s *address operand*, read from storage by
   `SLOAD`.  That is a stack word, not a jump target, which is why forwarding
   costs the representation nothing.

4. **Selector-free by design.**  `proxyFallback` never reads calldata word 0 as
   a selector and has no dispatcher: it copies the calldata whole and forwards
   it.  Blanc's mandatory-`.branch` rule constrains how control flow is
   *represented*, not whether a program dispatches on a selector — a contract
   that dispatches writes the dispatcher out of `.branch` nodes, and one that
   does not, like this proxy, simply has none.  The selector-free surface here
   is a property of what a forwarding proxy *is*, not a concession to Blanc.

`implGuarded` does read calldata word 0, but as a *guard* rather than a
selector: the branch it drives chooses between writing-and-returning and
reverting, which is what makes it a single program carrying all three features
row P4 asks for.

## Trust surface

Every theorem and lemma stated in this file, in order.  A subset of
`[propext, Classical.choice, Quot.sound]` is the pass; any `sorryAx`,
`Lean.ofReduceBool` or `Lean.ofReduceNat` is a failure.  There is no
`native_decide` and no `set_option maxRecDepth`/`maxHeartbeats` anywhere
above. -/

#print axioms implementationSlotLit_derived
#print axioms proxyProg_compiles
#print axioms proxyProg_compile
#print axioms proxyBytes_length
#print axioms proxyCode_notDelegation
#print axioms implGuardedProg_compiles
#print axioms implGuardedProg_compile
#print axioms implGuardedBytes_length
#print axioms implGuardedCode_notDelegation
#print axioms extCost_single
#print axioms extCost_empty
#print axioms extCost_open
#print axioms parent_retains_64th
#print axioms resumeState_eq
#print axioms resumeState_returnData
#print axioms resumeState_memory
#print axioms resumeState_stack
#print axioms resumeState_gasLeft
#print axioms reemitGas_eq
#print axioms returndata_slice_whole
#print axioms delcall_returndata_reemitted_verbatim
#print axioms ceilDiv_mul_32
#print axioms memExtSize_idem
#print axioms extCost_delcall_window
#print axioms extCost_return_window
#print axioms ceil32_eq_memExtSize
#print axioms proxy_tail_payable
#print axioms proxy_resources_realizable
#print axioms proxyMessageGas_cold_4_32
#print axioms proxyMessageGas_warm_4_32

end Blanc.ProxySpikeProxy
