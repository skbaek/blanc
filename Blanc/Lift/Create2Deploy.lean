import Blanc.Lift.Deploy
import Blanc.ForwardCall

/-!
# `CREATE2`, spawned, constructed and resumed

Contract-neutral composition of the `CREATE2` opcode under a covered fork.

* `create2AddressOfHash`: the CREATE2 address computed from an init-code digest, with
  `create2NewAddress_eq_ofHash` its proved specialization to hashing the init code itself;
* `create2Prepared`: the parent world after the opcode's charge, memory extension, the
  EIP-150 withholding, the creator's nonce bump and the new address's warm access;
* `Xinst.step_create2_spawn`: an admitted `CREATE2` (non-static, affordable endowment, creator
  nonce below the maximum, positive depth, empty target) spawns exactly the creation frame of
  `createMsg` over `create2Prepared`, at the address `create2NewAddress` of the actual memory
  slice, with the `.create` resume;
* `create2_runCompiled`: a successful creation message (`processCreateMessage … = .ok child`,
  `child.error = none`) closes that spawn into a compiled step whose post-state has the new
  address on the stack, the child's world, empty return data and the withheld gas the child
  left back.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The CREATE2 address computed from the init-code digest `hash`. -/
def create2AddressOfHash (sender : Adr) (salt hash : B256) : Adr :=
  (Bytes.keccak ((0xFF : UInt8) :: (sender.toBytes ++ salt.toBytes ++ hash.toBytes))).toAdr

/-- Jaune's CREATE2 address is the digest view at the digest of the init code. -/
theorem create2NewAddress_eq_ofHash (sender : Adr) (salt : B256) (initCode : Bytes) :
    create2NewAddress sender salt initCode =
      create2AddressOfHash sender salt (Bytes.keccak initCode) := rfl

/-- The init code a `CREATE2` from memory `M` reads: the window `[i, i + sz)` of the extended
memory. -/
def create2InitCode (M : Mem) (i sz : B256) : Bytes :=
  (M.extends [⟨i.toNat, sz.toNat⟩]).data.sliceD i.toNat sz.toNat 0

/-- The parent after `CREATE2`'s charge and memory extension, the withheld child gas, cleared
return data, the creator's nonce bump and the warm access of the new address. -/
def create2Prepared (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat) (i sz : B256)
    (addr : Adr) : Devm :=
  let d := (St b S M G).memExtends [⟨i.toNat, sz.toNat⟩]
  addAccessedAddress (((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData
    []).incrNonce sevm.currentTarget) addr

/-- `CREATE2`'s own charge from memory `M`: access, init-code hashing, memory expansion and the
init-code word charge. -/
def create2Charge (sevm : Sevm) (M : Mem) (i sz : B256) : Nat :=
  sevm.benvStat.rules.gas.createAccess + gasKeccak256Word * ceilDiv sz.toNat 32 +
    (calculateMemoryGasCost (memExtsSize M.size [⟨i.toNat, sz.toNat⟩]) -
      calculateMemoryGasCost M.size) + gasInitCodeWordCost * ceilDiv sz.toNat 32

/-- The `CREATE2` collision check passes: the target has no nonce, code or storage. -/
def Create2TargetEmpty (d : Devm) (a : Adr) : Prop :=
  (d.state.get a).nonce = 0 ∧ (d.state.get a).code.size = 0 ∧ (d.state.get a).stor.size = 0

theorem Xinst.step_create2_spawn {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {v i sz salt : B256}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hmax : sz.toNat ≤ sevm.benvStat.rules.code.maxInitCodeSize)
    (hstatic : sevm.isStatic = false)
    (hbal : ¬ (b.state.get sevm.currentTarget).bal < v)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))) :
    Xinst.step sevm (St b (v :: i :: sz :: salt :: S) M
        (G + create2Charge sevm M i sz)) .create2 =
      .spawn (Frame.ofCreate (createMsg sevm
          (create2Prepared sevm b S M G i sz
            (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
          (except64th G) v
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))
          (create2InitCode M i sz)))
        (.create (create2Prepared sevm b S M G i sz
            (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))) := by
  have hsg := hfork.rules_stateGas_none
  have hc : chargeGas (create2Charge sevm M i sz) (St b S M (G + create2Charge sevm M i sz)) =
      .ok (St b S M G) := by
    rw [chargeGas_eq_ok (by simp only [St.gasLeft]; omega)]
    simp only [St.stack, St.memory, St.gasLeft, Nat.add_sub_cancel]
    rfl
  simp only [Xinst.step, hsg]
  rw [show (St b (v :: i :: sz :: salt :: S) M (G + create2Charge sevm M i sz)).pop =
    .ok (v, St b (i :: sz :: salt :: S) M (G + create2Charge sevm M i sz)) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (i :: sz :: salt :: S) M (G + create2Charge sevm M i sz)).popToNat =
    .ok (i.toNat, St b (sz :: salt :: S) M (G + create2Charge sevm M i sz)) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (sz :: salt :: S) M (G + create2Charge sevm M i sz)).popToNat =
    .ok (sz.toNat, St b (salt :: S) M (G + create2Charge sevm M i sz)) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (salt :: S) M (G + create2Charge sevm M i sz)).pop =
    .ok (salt, St b S M (G + create2Charge sevm M i sz)) from rfl]
  simp only [Except.bind_ok]
  have hc' : chargeGas (sevm.benvStat.rules.gas.createAccess +
      gasKeccak256Word * ceilDiv sz.toNat 32 +
      (St b S M (G + create2Charge sevm M i sz)).extCost [(i.toNat, sz.toNat)] +
      gasInitCodeWordCost * ceilDiv sz.toNat 32) (St b S M (G + create2Charge sevm M i sz)) =
      .ok (St b S M G) := hc
  rw [hc']
  simp only [Except.bind_ok]
  show genericCreate.step _ _ _ _ _ _ = _
  have hmax' : sz.toNat ≤ sevm.benvStat.rules.code.maxInitCodeSize := hmax
  simp only [genericCreate.step, Except.assert, ite_eq_left hmax', assertDynamic, hstatic,
    Bool.not_false, ite_true, Except.bind_ok]
  rw [ite_eq_right, ite_eq_right]
  · rfl
  · exact fun h => by
      rcases h with h | h | h
      · exact h hfresh.1
      · exact h hfresh.2.1
      · exact h hfresh.2.2
  · exact fun h => by
      rcases h with h | h | h
      · exact hbal h
      · exact hnonce h
      · exact hdepth h

/-- The parent after a successful creation resumes: the child's world and gas incorporated, empty
return data, and the new address on the stack. -/
def create2Post (D child : Devm) (addr : Adr) : Devm :=
  let d := incorporateChildOnSuccess D child []
  d.setMach ⟨addr.toB256 :: d.stack, d.memory, d.gasLeft, d.stateGas⟩

/-- **`CREATE2`, closed.**  An admitted `CREATE2` whose creation message succeeds without error
is a compiled step to `create2Post`. -/
theorem create2_runCompiled {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {v i sz salt : B256} {child : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hmax : sz.toNat ≤ sevm.benvStat.rules.code.maxInitCodeSize)
    (hstatic : sevm.isStatic = false)
    (hbal : ¬ (b.state.get sevm.currentTarget).bal < v)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
    (hchild : processCreateMessage (createMsg sevm
        (create2Prepared sevm b S M G i sz
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        (except64th G) v
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))
        (create2InitCode M i sz)) = .ok child)
    (herror : child.error = none) (hroom : S.length < 1024) :
    Ninst.RunCompiled sevm (St b (v :: i :: sz :: salt :: S) M
        (G + create2Charge sevm M i sz)) (.exec .create2)
      (create2Post (create2Prepared sevm b S M G i sz
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        child (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))) := by
  obtain ⟨xl, hfill, hrf⟩ := of_processCreateMessage _ _ hchild
  refine ⟨xl, hfill, fun pc => XStep.run_toStep.mpr ?_⟩
  show XStep.Run (Xinst.step _ _ _) xl _
  rw [Xinst.step_create2_spawn hfork hmax hstatic hbal hnonce hdepth hfresh]
  refine ⟨_, hrf, ?_⟩
  simp only [Resume.run, liftToExecution, Except.bind_ok, herror, Option.isSome_none,
    Bool.false_eq_true, ite_false]
  rw [Devm.push_eq_ok (by exact hroom)]
  rfl

end Blanc.Lift
