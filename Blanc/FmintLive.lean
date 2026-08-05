import Blanc.Forward
import Blanc.Fmint

namespace Blanc
namespace Fmint

open Jaune

set_option maxRecDepth 8000

/-- Every gas constant the `totalSupply()` derivation charges, in the order it
charges them: the program's entry `JUMPDEST`; `fsig`'s four instructions; three
dispatch forks, two taken by the `.succ` arm and one falling through; the leaf's
`PUSH`/`EQ` and its taken arm; then `totalSupply`'s own body. -/
def totalSupplyGas : Nat :=
  gJumpdest
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gBase + gVerylow + gasColdSload)
    + (gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

/-- 2218 gas, of which `gasColdSload`'s 2100 is the storage read. -/
theorem totalSupplyGas_eq : totalSupplyGas = 2218 := by decide

/-! ### The dispatch path

`fmint`'s dispatcher is `DispatchTree.ofSorted fmintFuncs` over twelve
selectors, so a call walks three forks and then a leaf.  `totalSupply()` is
entry 2 of twelve, and `DispatchTree.build` splits at `⌈n/2⌉`, which puts it in
the left half at every fork.  The three pivots below are `leftmostFsig` of each
fork's right subtree, named here rather than left as tree projections so that
the step statements read.  Each equation is structural — `build`, `take`, `drop`
and `length` only — and forces no `String.keccak` call. -/

/-- The selector `totalSupply()` dispatches on.  There is no
`totalSupplySelector` in the tree and this is not one: it is local to this
module, and reaching `Blanc/FlashSpec.lean` for its neighbourhood would cost
two seconds of elaboration for a four-byte constant. -/
abbrev tsSel : B256 := selector "totalSupply" []

/-- Fork 1's pivot: entry 6 of twelve. -/
abbrev piv1 : B256 := selector "maxFlashLoan" [.address]

/-- Fork 2's pivot: entry 3 of six. -/
abbrev piv2 : B256 := selector "transferFrom" [.address, .address, .uint256]

/-- Fork 3's pivot: entry 2 of three — `totalSupply` itself, which is why this
fork is the one that falls through rather than jumping. -/
abbrev piv3 : B256 := tsSel

/-- Every state the derivation passes through is `pre` with a new machine:
`Devm.setMach_setMach` collapses the chain, so no state nests. -/
private abbrev W (pre : Devm) (S : List B256) (M : Mem) (G : Nat) : Devm :=
  pre.setMach ⟨S, M, G⟩

local macro "gas_ok" : tactic =>
  `(tactic| (simp only [W, Devm.gasLeft_setMach]; omega))

local macro "room_ok" : tactic =>
  `(tactic| (simp only [W, Devm.stack_setMach]; simp))

/-! ### The witness

The construction below is the first in this repository that **produces** a
`Func.RunCompiled` derivation instead of consuming one.  It is written out by
hand, one `have` per instruction, so that the split between what would serve
any target and what is specific to `totalSupply()` can be measured. -/

/-- A `totalSupply()` call on `fmint` has a gas-exact run, and it returns the
supply slot.

Every premise is what a fresh top-level message frame supplies: an empty stack,
empty memory, a storage key not yet warmed, and enough gas.  The conclusion
names the post-state's output, so this is not merely "some run exists". -/
theorem totalSupply_runCompiled {sevm : Sevm} {pre : Devm}
    (h_sel : Sevm.selector sevm = tsSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : totalSupplyGas ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre fmint post ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget supplySlot).toBytes := by
  rw [totalSupplyGas_eq] at h_gas
  have e1 : gJumpdest = 1 := rfl
  have e2 : gBase = 2 := rfl
  have e3 : gVerylow = 3 := rfl
  have e4 : gHigh = 10 := rfl
  have e6 : gasColdSload = 2100 := rfl
  have e7 : gMemory = 3 := rfl
  set g := pre.gasLeft with hg
  -- The word the storage read yields, and the memory image the `MSTORE` leaves.
  set v : B256 := Devm.getStorVal pre sevm.currentTarget supplySlot with hv
  set M : Mem := Mem.empty.write 0 v.toBytes with hM
  -- The state the `SLOAD` moves to: warming a key writes a `meta` field, so
  -- from here on the base state is no longer `pre`.
  set P : Devm := addAccessedStorageKey pre sevm.currentTarget supplySlot with hP
  -- The two memory-expansion charges this path incurs.  `MSTORE` grows memory
  -- from nothing to one word, which is `gMemory`; `RETURN` reads back the word
  -- that is already there, which is free.
  have hn0 : (0 : B256).toNat = 0 := rfl
  have hn32 : (32 : B256).toNat = 32 := rfl
  have hmemW : ∀ (X : Devm) (S : List B256) (N : Mem) (G : Nat),
      (W X S N G).memory = N := fun _ _ _ _ => rfl
  have hMsize : M.size = 32 := by
    rw [hM]
    rcases hb : v.toBytes with _ | ⟨b, bs⟩
    · exact absurd (hb ▸ B256.length_toBytes v) (by simp)
    · have hlen : (b :: bs).length = 32 := hb ▸ B256.length_toBytes v
      simp only [Mem.write, Mem.empty, hlen, if_neg (by simp : ¬ (0 + 32 ≤ 0))]
      rfl
  have hextM : ∀ (S : List B256) (G : Nat),
      (W P S Mem.empty G).extCost [⟨(0 : B256).toNat, 32⟩] = 3 :=
    fun _ _ => by
      simp [Devm.extCost, hmemW, hn0, memExtsSize, memExtSize,
        calculateMemoryGasCost, ceilDiv, Mem.empty, gMemory]
  have hextR : ∀ (S : List B256) (G : Nat),
      (W P S M G).extCost [⟨(0 : B256).toNat, (32 : B256).toNat⟩] = 0 :=
    fun _ _ => by
      simp [Devm.extCost, hmemW, hn0, hn32, memExtsSize, memExtSize,
        calculateMemoryGasCost, ceilDiv, hMsize, gMemory]
  ---------------------------------------------------------------- fsig
  have i1 : Ninst.RunCompiled sevm (W pre [] Mem.empty (g - 1))
      (Ninst.pushB256 0) (W pre [0] Mem.empty (g - 3)) :=
    Ninst.runCompiled_pushB256 pushCost_zero (by gas_ok) (by room_ok)
  have i2 : Ninst.RunCompiled sevm (W pre [0] Mem.empty (g - 3))
      Ninst.calldataload (W pre [Sevm.dataWord sevm 0] Mem.empty (g - 6)) :=
    Ninst.runCompiled_calldataload rfl rfl (by gas_ok) (by simp)
  have i3 : Ninst.RunCompiled sevm
      (W pre [Sevm.dataWord sevm 0] Mem.empty (g - 6)) (Ninst.pushB256 224)
      (W pre [224, Sevm.dataWord sevm 0] Mem.empty (g - 9)) :=
    Ninst.runCompiled_pushB256 (pushCost_of_ne_zero (by decide)) (by gas_ok) (by room_ok)
  have i4 : Ninst.RunCompiled sevm
      (W pre [224, Sevm.dataWord sevm 0] Mem.empty (g - 9)) Ninst.shr
      (W pre [tsSel] Mem.empty (g - 12)) :=
    Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl h_sel (by gas_ok) (by simp)
  ---------------------------------------------------------------- fork 1
  have i5 : Ninst.RunCompiled sevm (W pre [tsSel] Mem.empty (g - 12))
      (Ninst.dup 0) (W pre [tsSel, tsSel] Mem.empty (g - 15)) :=
    Ninst.runCompiled_dup rfl (by gas_ok) (by room_ok)
  have i6 : Ninst.RunCompiled sevm (W pre [tsSel, tsSel] Mem.empty (g - 15))
      (Ninst.pushB256 piv1) (W pre [piv1, tsSel, tsSel] Mem.empty (g - 18)) :=
    Ninst.runCompiled_pushB256 (pushCost_of_ne_zero (by decide +kernel))
      (by gas_ok) (by room_ok)
  have i7 : Ninst.RunCompiled sevm
      (W pre [piv1, tsSel, tsSel] Mem.empty (g - 18)) Ninst.gt
      (W pre [1, tsSel] Mem.empty (g - 21)) :=
    Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl (by decide +kernel)
      (by gas_ok) (by simp)
  ---------------------------------------------------------------- fork 2
  have i8 : Ninst.RunCompiled sevm (W pre [tsSel] Mem.empty (g - 35))
      (Ninst.dup 0) (W pre [tsSel, tsSel] Mem.empty (g - 38)) :=
    Ninst.runCompiled_dup rfl (by gas_ok) (by room_ok)
  have i9 : Ninst.RunCompiled sevm (W pre [tsSel, tsSel] Mem.empty (g - 38))
      (Ninst.pushB256 piv2) (W pre [piv2, tsSel, tsSel] Mem.empty (g - 41)) :=
    Ninst.runCompiled_pushB256 (pushCost_of_ne_zero (by decide +kernel))
      (by gas_ok) (by room_ok)
  have i10 : Ninst.RunCompiled sevm
      (W pre [piv2, tsSel, tsSel] Mem.empty (g - 41)) Ninst.gt
      (W pre [1, tsSel] Mem.empty (g - 44)) :=
    Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl (by decide +kernel)
      (by gas_ok) (by simp)
  ---------------------------------------------------------------- fork 3
  have i11 : Ninst.RunCompiled sevm (W pre [tsSel] Mem.empty (g - 58))
      (Ninst.dup 0) (W pre [tsSel, tsSel] Mem.empty (g - 61)) :=
    Ninst.runCompiled_dup rfl (by gas_ok) (by room_ok)
  have i12 : Ninst.RunCompiled sevm (W pre [tsSel, tsSel] Mem.empty (g - 61))
      (Ninst.pushB256 piv3) (W pre [piv3, tsSel, tsSel] Mem.empty (g - 64)) :=
    Ninst.runCompiled_pushB256 (pushCost_of_ne_zero (by decide +kernel))
      (by gas_ok) (by room_ok)
  have i13 : Ninst.RunCompiled sevm
      (W pre [piv3, tsSel, tsSel] Mem.empty (g - 64)) Ninst.gt
      (W pre [0, tsSel] Mem.empty (g - 67)) :=
    Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl (by decide +kernel)
      (by gas_ok) (by simp)
  ---------------------------------------------------------------- the leaf
  have i14 : Ninst.RunCompiled sevm (W pre [tsSel] Mem.empty (g - 80))
      (Ninst.pushB256 tsSel) (W pre [tsSel, tsSel] Mem.empty (g - 83)) :=
    Ninst.runCompiled_pushB256 (pushCost_of_ne_zero (by decide +kernel))
      (by gas_ok) (by room_ok)
  have i15 : Ninst.RunCompiled sevm (W pre [tsSel, tsSel] Mem.empty (g - 83))
      Ninst.eq (W pre [1] Mem.empty (g - 86)) :=
    Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl
      (by rw [B256.eqCheck, if_pos rfl]) (by gas_ok) (by simp)
  ---------------------------------------------------------- totalSupply body
  have i16 : Ninst.RunCompiled sevm (W pre [] Mem.empty (g - 100))
      (Ninst.pushB256 0) (W pre [0] Mem.empty (g - 102)) :=
    Ninst.runCompiled_pushB256 pushCost_zero (by gas_ok) (by room_ok)
  have i17 : Ninst.RunCompiled sevm (W pre [0] Mem.empty (g - 102))
      Ninst.not (W pre [supplySlot] Mem.empty (g - 105)) :=
    Ninst.runCompiled_unary (by rintro ⟨⟩) rfl rfl (by decide) (by gas_ok) (by simp)
  have i18 : Ninst.RunCompiled sevm (W pre [supplySlot] Mem.empty (g - 105))
      Ninst.sload (W P [v] Mem.empty (g - 2205)) :=
    Ninst.runCompiled_sload_cold rfl h_cold rfl (by gas_ok) (by simp)
  have i19 : Ninst.RunCompiled sevm (W P [v] Mem.empty (g - 2205))
      (Ninst.pushB256 0) (W P [0, v] Mem.empty (g - 2207)) :=
    Ninst.runCompiled_pushB256 pushCost_zero (by gas_ok) (by room_ok)
  have i20 : Ninst.RunCompiled sevm (W P [0, v] Mem.empty (g - 2207))
      Ninst.mstore (W P [] M (g - 2213)) :=
    Ninst.runCompiled_mstore rfl (by rw [hextM]; gas_ok) rfl
  have i21 : Ninst.RunCompiled sevm (W P [] M (g - 2213))
      (Ninst.pushB256 32) (W P [32] M (g - 2216)) :=
    Ninst.runCompiled_pushB256 (pushCost_of_ne_zero (by decide)) (by gas_ok) (by room_ok)
  have i22 : Ninst.RunCompiled sevm (W P [32] M (g - 2216))
      (Ninst.pushB256 0) (W P [0, 32] M (g - 2218)) :=
    Ninst.runCompiled_pushB256 pushCost_zero (by gas_ok) (by room_ok)
  ---------------------------------------------------------------- the RETURN
  -- What `MSTORE` left in memory is what `RETURN` reads back: `Mem.Reads`
  -- carries the image across the write, and the read is the whole of it
  -- because a `B256` is exactly 32 bytes.
  have h_reads : Mem.Reads M v.toBytes := by
    have h := Mem.Reads.write Mem.wf_empty Mem.reads_empty 0 v.toBytes
    rw [show Bytes.writeAt [] 0 v.toBytes = v.toBytes by
      simp [Bytes.writeAt]] at h
    exact h
  have h_read : (M.read 0 32).1 = v.toBytes := by
    rw [Mem.Reads.read h_reads 0 32]
    show List.takeD 32 (List.drop 0 v.toBytes) 0 = v.toBytes
    rw [List.drop_zero, List.takeD_eq_self 0 (B256.length_toBytes v).symm]
  have h_mr : ((W P [] M (g - 2218)).memRead 0 32).1 = v.toBytes := h_read
  have i23 : Func.RunCompiled (fmint.main :: fmint.aux) sevm
      (W P [0, 32] M (g - 2218)) (.last .ret)
      (((W P [] M (g - 2218)).memRead 0 32).2.withOutput v.toBytes) :=
    Func.runCompiled_ret (G := g - 2218) rfl (by rw [hextR]; gas_ok)
      (Prod.ext h_mr rfl)
  ---------------------------------------------------------------- composition
  have h_run : Prog.RunCompiled sevm pre fmint
      (((W P [] M (g - 2218)).memRead 0 32).2.withOutput v.toBytes) :=
    Prog.runCompiled_intro (G := g - 1) (mid := W pre [] Mem.empty (g - 1))
      (by omega) (by rw [h_stack, h_mem])
      (.next i1 (.next i2 (.next i3 (.next i4 (.next i5 (.next i6 (.next i7
        -- fork 1: `piv1 > totalSupply()`, so the dispatcher jumps left
        (Func.runCompiled_branch_succ (w := 1) (G := g - 35) (by decide) rfl
          (by room_ok) (by gas_ok)
        (.next i8 (.next i9 (.next i10
        -- fork 2: same again
        (Func.runCompiled_branch_succ (w := 1) (G := g - 58) (by decide) rfl
          (by room_ok) (by gas_ok)
        (.next i11 (.next i12 (.next i13
        -- fork 3: the pivot IS `totalSupply()`, so `GT` is 0 and this one
        -- falls through to the right subtree rather than jumping
        (Func.runCompiled_branch_zero (G := g - 80) rfl (by room_ok) (by gas_ok)
        (.next i14 (.next i15
        -- the leaf: `EQ` matches, so the selector's own body is taken and the
        -- `.call fallbackSlot` miss arm is not
        (Func.runCompiled_branch_succ (w := 1) (G := g - 100) (by decide) rfl
          (by room_ok) (by gas_ok)
        (.next i16 (.next i17 (.next i18 (.next i19 (.next i20
          (.next i21 (.next i22 i23))))))))))))))))))))))))))
  exact ⟨_, h_run, rfl⟩

/-- **`fmint`'s `totalSupply()` call succeeds.**

The first statement in this repository that a contract call *succeeds*.
Everything before it takes a successful execution as a hypothesis and factors
it; this one produces the execution, from a precondition on the frame alone.

What it does **not** say, so that nothing downstream overreads it:

* **It is one entrypoint of one contract.** `totalSupply()` is call-free — its
  compiled path emits no spawning instruction — which is exactly why the
  statement is unconditional. Every fmint entrypoint that makes an external
  call carries the callee's execution as a premise (`Xlot.Filled`) and cannot
  have a statement of this shape at all.
* **It is message-call altitude, not transaction level.** Intrinsic gas, the
  63/64 rule and transaction validity are a further layer; `pre` is a frame,
  and 2218 is the frame's gas, not a transaction's.
* **It says nothing about any other calldata.** The premise fixes the selector;
  a call with different calldata is a different execution about which this says
  nothing, in either direction.
* **The gas figure is exact, not a bound.** `Func.RunCompiled` pins each hidden
  instruction's cost, so 2218 is what this path charges under
  `Blanc/Compiled.lean`'s compiler-shape assumption — a `PUSH1` peephole or a
  shared-`JUMPDEST` optimisation would change it. -/
theorem fmint_totalSupply_succeeds {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = tsSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : totalSupplyGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget supplySlot).toBytes := by
  obtain ⟨post, h_run, h_out⟩ :=
    totalSupply_runCompiled h_sel h_stack h_mem h_cold h_gas
  exact ⟨post, Prog.exec_of_runCompiled h_run h_code, h_out⟩

end Fmint
end Blanc
