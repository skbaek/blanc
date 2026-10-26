import Blanc.Lift.CursorStateToward
import Blanc.Lift.Usdc.PermitRowRecoveryV2_1

/-! Actual V2_1 permit root prefixes toward a tracked row write. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift
open SolcSignedQuery

/-- The raw root reaches its actual ABI-decoded permit entry before the
observed SSTORE, including when the enclosing frame later fails. -/
theorem permitV2_1_root_decoded_toward_sstore {F target : Exec.Deriv}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateToward ImplV2_1.code ImplV2_1.cert F target
      ImplV2_1.t_3092_c24 F.devm
      [Sevm.dataWord F.sevm 196, Sevm.dataWord F.sevm 164,
       Sevm.dataWord F.sevm 132 &&& 255, Sevm.dataWord F.sevm 100, Sevm.dataWord F.sevm 68,
       (Sevm.dataWord F.sevm 36).toAdr.toB256, (Sevm.dataWord F.sevm 4).toAdr.toB256,
       0x452, 0xd505accf]
      (Mem.empty.write 64 (128 : B256).toBytes) [ImplV2_1.t_0452_c109]) := by
  let first : CursorStateToward ImplV2_1.code ImplV2_1.cert F target
      ImplV2_1.t_0000_c0 F.devm [] Mem.empty [] :=
    { toCursorStateAt := ⟨F, Cursor.start ImplV2_1.cert, .refl _, rfl, rfl,
        cursor_start ImplV2_1.cert_check pc code, rfl,
        ⟨F.devm.gasLeft, St.self stack memory⟩, rfl⟩, toward := path, store := store }
  obtain ⟨guard0⟩ := first.line ImplV2_1.cert_check hsg (prologue 0x00 0x10) rfl
    (by intro n member x same; subst n
        simp only [prologue, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [prologue, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (prologue_line)
  have take0 := guard0.guardSucc ImplV2_1.cert_check hsg rfl rfl
  obtain ⟨nonpayable⟩ := guard0.branchSucc ImplV2_1.cert_check hsg take0
  obtain ⟨opened0⟩ := nonpayable.dest ImplV2_1.cert_check hsg
  obtain ⟨guard1⟩ := opened0.line ImplV2_1.cert_check hsg (sizeLine 0x03 0x36) rfl
    (by intro n member x same; subst n
        simp only [sizeLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [sizeLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (size_line)
  have zero1 := guard1.guardZero ImplV2_1.cert_check hsg rfl rfl
  rw [zero1] at guard1
  obtain ⟨sized⟩ := guard1.branchZero ImplV2_1.cert_check hsg
  obtain ⟨selected⟩ := sized.line ImplV2_1.cert_check hsg (selectorLine) rfl
    (by intro n member x same; subst n
        simp only [selectorLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [selectorLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (fun run => by
      obtain ⟨gas, state⟩ := selector_line run
      rw [selector] at state
      exact ⟨gas, state⟩)
  obtain ⟨cmp0⟩ := selected.line ImplV2_1.cert_check hsg (compareLine .gt 0x7f 0x2e 0xec 0xc3 0x01 0xb2) rfl
    (by intro n member x same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (compare_gt_line)
  obtain ⟨branch0⟩ := cmp0.branchZero ImplV2_1.cert_check hsg
  let dispatch0 := branch0
  obtain ⟨cmp1⟩ := dispatch0.line ImplV2_1.cert_check hsg (compareLine .gt 0xb2 0x11 0x8a 0x8d 0x00 0xf9) rfl
    (by intro n member x same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (compare_gt_line)
  obtain ⟨branch1⟩ := cmp1.branchZero ImplV2_1.cert_check hsg
  let dispatch1 := branch1
  obtain ⟨cmp2⟩ := dispatch1.line ImplV2_1.cert_check hsg (compareLine .gt 0xe3 0xee 0x16 0x0e 0x00 0xa2) rfl
    (by intro n member x same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (compare_gt_line)
  obtain ⟨branch2⟩ := cmp2.branchSucc ImplV2_1.cert_check hsg (by decide)
  obtain ⟨dispatch2⟩ := branch2.dest ImplV2_1.cert_check hsg
  obtain ⟨cmp3⟩ := dispatch2.line ImplV2_1.cert_check hsg (compareLine .gt 0xd6 0x08 0xea 0x64 0x00 0xd3) rfl
    (by intro n member x same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (compare_gt_line)
  obtain ⟨branch3⟩ := cmp3.branchSucc ImplV2_1.cert_check hsg (by decide)
  obtain ⟨dispatch3⟩ := branch3.dest ImplV2_1.cert_check hsg
  obtain ⟨cmp4⟩ := dispatch3.line ImplV2_1.cert_check hsg (compareLine .eq 0xb2 0x11 0x8a 0x8d 0x0a 0xb8) rfl
    (by intro n member x same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (compare_eq_line)
  obtain ⟨branch4⟩ := cmp4.toZero ImplV2_1.cert_check hsg
  let dispatch4 := branch4
  obtain ⟨cmp5⟩ := dispatch4.line ImplV2_1.cert_check hsg (compareLine .eq 0xbd 0x10 0x24 0x30 0x0a 0xfb) rfl
    (by intro n member x same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (compare_eq_line)
  obtain ⟨branch5⟩ := cmp5.toZero ImplV2_1.cert_check hsg
  let dispatch5 := branch5
  obtain ⟨cmp6⟩ := dispatch5.line ImplV2_1.cert_check hsg (compareLine .eq 0xd5 0x05 0xac 0xcf 0x0b 0x03) rfl
    (by intro n member x same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [compareLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (compare_eq_line)
  obtain ⟨branch6⟩ := cmp6.toSucc ImplV2_1.cert_check hsg (by decide) rfl
  let dispatch6 := branch6
  obtain ⟨wrapper⟩ := dispatch6.dest ImplV2_1.cert_check hsg
  obtain ⟨width⟩ := wrapper.line ImplV2_1.cert_check hsg (wrapperLine 0x04 0x52 [0xe0] (by decide) 0x0b 0x19) rfl
    (by intro n member x same; subst n
        simp only [wrapperLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [wrapperLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (wrapper_line)
  have widthPass := width.guardSucc ImplV2_1.cert_check hsg rfl rfl
  obtain ⟨accepted⟩ := width.branchSucc ImplV2_1.cert_check hsg widthPass
  obtain ⟨decoder⟩ := accepted.dest ImplV2_1.cert_check hsg
  obtain ⟨decoded⟩ := decoder.line ImplV2_1.cert_check hsg (decodeLine 0x30 0x92) rfl
    (by intro n member x same; subst n
        simp only [decodeLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [decodeLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (decode_line)
  exact decoded.call ImplV2_1.cert_check hsg rfl

private theorem permit_blacklist_toward (second : Bool)
    {F target : Exec.Deriv} {b : Devm} {M : Mem}
    {a0 a1 a2 a3 a4 a5 : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateToward ImplV2_1.code ImplV2_1.cert F target
      (if second then ImplV2_1.t_319d_c24 else ImplV2_1.t_311c_c24) b
      (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ b' M', b'.state = b.state ∧ PtrMem 128 96 M' ∧
      Nonempty (CursorStateToward ImplV2_1.code ImplV2_1.cert F target
        (if second then ImplV2_1.t_321e_c24 else ImplV2_1.t_319d_c24) b'
        (owner.toB256 :: a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M' K) := by
  let d0 : UInt8 := if second then 0x32 else 0x31
  let d1 : UInt8 := if second then 0x1e else 0x9d
  let rejected := if second then ImplV2_1.t_31ce_c24 else ImplV2_1.t_314d_c24
  let accepted := if second then ImplV2_1.t_321e_c24 else ImplV2_1.t_319d_c24
  have shape : (if second then ImplV2_1.t_319d_c24 else ImplV2_1.t_311c_c24) =
      .dest ((blacklistReadLine 0x03).foldr SFunc.next
        (.next (.push [d0,d1] (by simp only [List.length_cons, List.length_nil]; decide)) (.branch rejected accepted))) := by
    cases second <;> rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check fork.stateGas
  obtain ⟨read⟩ := opened.line ImplV2_1.cert_check fork.stateGas (blacklistReadLine 0x03) rfl
    (by intro n member x same; subst n; simp only [blacklistReadLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n; simp only [blacklistReadLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (blacklist_read_line ptr fork)
  obtain ⟨guard⟩ := read.line ImplV2_1.cert_check fork.stateGas
    [.push [d0,d1] (by simp only [List.length_cons, List.length_nil]; decide)] rfl
    (by intro n member x same; subst n; simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n; simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro gas d run
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_push step
        cases run
        exact ⟨_, rfl⟩)
  have pass := guard.guardSucc ImplV2_1.cert_check fork.stateGas
    (by cases second <;> rfl) (by cases second <;> rfl)
  exact ⟨_, _, afterSloadH_state _ _ _,
    (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 3 (.inl (by decide)),
    guard.branchSucc ImplV2_1.cert_check fork.stateGas pass⟩

private theorem permit_call71_toward {F target : Exec.Deriv} {b : Devm} {M : Mem}
    {s r v deadline value spender owner : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_321e_c24 b
      (spender :: owner :: s :: r :: v :: deadline :: value :: spender :: owner :: S) M K)
    (fork : NeutralFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_410c_c71 b
      (s :: r :: v :: deadline :: value :: spender :: owner :: 0x322d ::
       spender :: owner :: s :: r :: v :: deadline :: value :: spender :: owner :: S)
      M (ImplV2_1.t_322d_c24 :: K)) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check fork.stateGas
  obtain ⟨args⟩ := opened.line ImplV2_1.cert_check fork.stateGas
    (SolcSignedQuery.sevenArgsCallLine 0x32 0x2d 0x41 0x0c) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.sevenArgsCallLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [SolcSignedQuery.sevenArgsCallLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    SolcSignedQuery.seven_args_call_line
  exact args.call ImplV2_1.cert_check fork.stateGas rfl

private theorem permit_deadline_guard_toward {F target : Exec.Deriv} {b : Devm} {M : Mem}
    {s r v deadline : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_410c_c71 b
      (s :: r :: v :: deadline :: S) M K)
    (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.benvStat.time.toNat ≤ deadline.toNat ∧
      Nonempty (CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_417b_c71 b
        (s :: r :: v :: deadline :: S) M K) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check fork.stateGas
  obtain ⟨guard⟩ := opened.line ImplV2_1.cert_check fork.stateGas
    (SolcSignedQuery.deadlineLine 0x41 0x7b) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.deadlineLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [SolcSignedQuery.deadlineLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    SolcSignedQuery.deadline_line
  have taken := guard.guardSucc ImplV2_1.cert_check fork.stateGas rfl rfl
  have zero := eq_zero_of_iszero_ne_zero taken
  exact ⟨toNat_ge_of_ltCheck_eq_zero zero,
    guard.branchSucc ImplV2_1.cert_check fork.stateGas taken⟩

/-- The actual decoded owner and spender reach the pre-nonce permit body. -/
theorem permitV2_1_root_nonce_toward_sstore {F target : Exec.Deriv}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore)) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ b M, b.state = F.devm.state ∧ PtrMem 128 96 M ∧
      Nonempty (CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_417b_c71 b
        [Sevm.dataWord F.sevm 196, Sevm.dataWord F.sevm 164,
          Sevm.dataWord F.sevm 132 &&& 255, Sevm.dataWord F.sevm 100, Sevm.dataWord F.sevm 68,
          (Sevm.dataWord F.sevm 36).toAdr.toB256, (Sevm.dataWord F.sevm 4).toAdr.toB256,
          0x322d, (Sevm.dataWord F.sevm 36).toAdr.toB256,
          (Sevm.dataWord F.sevm 4).toAdr.toB256,
          Sevm.dataWord F.sevm 196, Sevm.dataWord F.sevm 164,
          Sevm.dataWord F.sevm 132 &&& 255, Sevm.dataWord F.sevm 100, Sevm.dataWord F.sevm 68,
          (Sevm.dataWord F.sevm 36).toAdr.toB256, (Sevm.dataWord F.sevm 4).toAdr.toB256,
          0x452, 0xd505accf]
        M [ImplV2_1.t_322d_c24, ImplV2_1.t_0452_c109]) := by
  obtain ⟨decoded⟩ := permitV2_1_root_decoded_toward_sstore pc code stack memory selector path store fork.stateGas
  obtain ⟨opened⟩ := decoded.dest ImplV2_1.cert_check fork.stateGas
  obtain ⟨pause⟩ := opened.line ImplV2_1.cert_check fork.stateGas (pauseLine 0x01 0x31 0x1c) rfl
    (by intro n member x same; subst n
        simp only [pauseLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [pauseLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (pause_line fork)
  have pass := pause.guardSucc ImplV2_1.cert_check fork.stateGas rfl rfl
  obtain ⟨unpaused⟩ := pause.branchSucc ImplV2_1.cert_check fork.stateGas pass
  obtain ⟨b1, M1, state1, ptr1, ⟨ownerAllowed⟩⟩ :=
    permit_blacklist_toward false unpaused (PtrMem.init 128) fork
  obtain ⟨b2, M2, state2, ptr2, ⟨spenderAllowed⟩⟩ :=
    permit_blacklist_toward true ownerAllowed ptr1 fork
  obtain ⟨called⟩ := permit_call71_toward spenderAllowed fork
  obtain ⟨_, continued⟩ := permit_deadline_guard_toward called fork
  refine ⟨b2, M2, ?_, ptr2, continued⟩
  rw [state2, state1]
  exact afterSloadH_state _ _ _

private abbrev permitBufferHeadLine := SolcSignedQuery.bufferHeadLine [0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f, 0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10, 0x5f, 0xa2, 0xfa, 0xae, 0x01, 0x26, 0x11, 0x4a, 0x16, 0x9c, 0x64, 0x84, 0x5d, 0x61, 0x26, 0xc9] (by decide)

private abbrev permitBufferBodyLine := SolcSignedQuery.bufferBodyLine

private abbrev permitBufferTailLine := SolcSignedQuery.bufferTailLine 0x0f 0x42 0x1e 0x46 0xb5

private theorem permit_call83_toward {F target : Exec.Deriv} {b : Devm} {M : Mem}
    {s r v deadline value : B256} {spender owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_417b_c71 b
      (s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M) {targetKey : B256}
    (targetHead : target.devm.stack.head? = some targetKey)
    (separated : nonceSlot owner ≠ targetKey)
    (fork : NeutralFork F.sevm.benvStat.fork) :
    let nonce := b.getStorVal F.sevm.currentTarget (nonceSlot owner)
    let b' := afterSstoreH F.sevm (afterSloadH F.sevm b (nonceSlot owner)) (nonceSlot owner) (nonce + 1)
    let M' := (M.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes
    Nonempty (CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_46b5_c83
      (afterSloadH F.sevm b' 15)
      (128 :: s :: r :: v :: b'.getStorVal F.sevm.currentTarget 15 :: 0x421e :: owner.toB256 ::
       128 :: s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      ((SolcSignedQuery.structMemory 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9) M' owner spender value nonce deadline) (ImplV2_1.t_421e_c71 :: K)) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check fork.stateGas
  obtain ⟨before⟩ := opened.line ImplV2_1.cert_check fork.stateGas (nonceHeadLine 0x11) rfl
    (by intro n member x same; subst n
        simp only [nonceHeadLine, nonceLine, List.dropLast_cons_cons, List.dropLast_singleton,
          List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro n member same; subst n
        simp only [nonceHeadLine, nonceLine, List.dropLast_cons_cons, List.dropLast_singleton,
          List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (nonce_head_line ptr fork)
  have currentKey : before.node.devm.stack.head? = some (nonceSlot owner) := by
    obtain ⟨gas, state⟩ := before.state
    rw [state, St.stack]
    rfl
  have distinct : before.node ≠ target := by
    intro same
    rw [same] at currentKey
    exact separated (Option.some.inj (currentKey.symm.trans targetHead))
  obtain ⟨updated⟩ := before.next ImplV2_1.cert_check fork.stateGas distinct
    (by intro x same; cases same) (by
      intro gas d step
      obtain ⟨_, rfl⟩ := ri_sstoreH fork.stateGas fork.bal step
      exact ⟨_, rfl⟩)
  have ptr' := (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 17 (.inl (by decide))
  change PtrMem 128 96 ((M.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes) at ptr'
  obtain ⟨head⟩ := updated.line ImplV2_1.cert_check fork.stateGas permitBufferHeadLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBufferHeadLine, Blanc.Lift.SolcSignedQuery.bufferHeadLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [permitBufferHeadLine, Blanc.Lift.SolcSignedQuery.bufferHeadLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    ((SolcSignedQuery.buffer_head_line (tag := [0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f, 0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10, 0x5f, 0xa2, 0xfa, 0xae, 0x01, 0x26, 0x11, 0x4a, 0x16, 0x9c, 0x64, 0x84, 0x5d, 0x61, 0x26, 0xc9]) (le := by decide)) ptr')
  obtain ⟨body⟩ := head.line ImplV2_1.cert_check fork.stateGas permitBufferBodyLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBufferBodyLine, Blanc.Lift.SolcSignedQuery.bufferBodyLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [permitBufferBodyLine, Blanc.Lift.SolcSignedQuery.bufferBodyLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    SolcSignedQuery.buffer_body_line
  have ptrHead := (ptr'.write 160
    (0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9 : B256)
    (.inr (by decide))).write 192 owner.toB256 (.inr (by decide))
  have ptrBody : PtrMem 128 352
      (SolcSignedQuery.structBodyMemory ((SolcSignedQuery.structHeadMemory 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9) _ owner) spender value
        (b.getStorVal F.sevm.currentTarget (nonceSlot owner)) deadline) :=
    (((ptrHead.write 224 spender.toB256 (.inr (by decide))).write 256 value
      (.inr (by decide))).write 288 _ (.inr (by decide))).write 320 deadline (.inr (by decide))
  obtain ⟨tail⟩ := body.line ImplV2_1.cert_check fork.stateGas permitBufferTailLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBufferTailLine, Blanc.Lift.SolcSignedQuery.bufferTailLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [permitBufferTailLine, Blanc.Lift.SolcSignedQuery.bufferTailLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    ((SolcSignedQuery.buffer_tail_line (slot := 0x0f) (r0 := 0x42) (r1 := 0x1e) (d0 := 0x46) (d1 := 0xb5)) ptrBody fork)
  exact tail.call ImplV2_1.cert_check fork.stateGas rfl

private abbrev permitStructHashLine := SolcSignedQuery.structHashLine

private abbrev permitTypedWordsLine := SolcSignedQuery.typedWordsLine

private abbrev permitTypedLengthLine := SolcSignedQuery.typedLengthLine

private abbrev permitTypedHashLine := SolcSignedQuery.typedHashLine 0x47 0x1c 0x49 0x44

private theorem permit_call89_toward {F target : Exec.Deriv} {b : Devm} {M : Mem}
    {s r v domain hash : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_46b5_c83 b
      (128 :: s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S) M K)
    (ptr : PtrMem 352 352 M) (length : memWord M 128 = 192)
    (hashRead : (M.read 160 192).1.keccak = hash)
    (fork : NeutralFork F.sevm.benvStat.fork) :
    let digest := ([0x19, 0x01] ++ domain.toBytes ++ hash.toBytes : Bytes).keccak
    Nonempty (CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_4944_c89 b
      (s :: r :: v :: digest :: 0x471c :: digest :: 0 :: 128 ::
       s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S)
      (SolcSignedQuery.typedMemory M domain hash) (ImplV2_1.t_471c_c83 :: K)) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check fork.stateGas
  obtain ⟨hashed⟩ := opened.line ImplV2_1.cert_check fork.stateGas permitStructHashLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitStructHashLine, Blanc.Lift.SolcSignedQuery.structHashLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [permitStructHashLine, Blanc.Lift.SolcSignedQuery.structHashLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.struct_hash_line ptr length hashRead)
  obtain ⟨words⟩ := hashed.line ImplV2_1.cert_check fork.stateGas permitTypedWordsLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitTypedWordsLine, Blanc.Lift.SolcSignedQuery.typedWordsLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [permitTypedWordsLine, Blanc.Lift.SolcSignedQuery.typedWordsLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.typed_words_line ptr)
  obtain ⟨ptrWords, ptrTyped, lengthTyped, bytesTyped⟩ := SolcSignedQuery.typed_memory_facts (domain := domain) (hash := hash) ptr
  obtain ⟨sized⟩ := words.line ImplV2_1.cert_check fork.stateGas permitTypedLengthLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitTypedLengthLine, Blanc.Lift.SolcSignedQuery.typedLengthLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [permitTypedLengthLine, Blanc.Lift.SolcSignedQuery.typedLengthLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.typed_length_line ptrWords)
  obtain ⟨args⟩ := sized.line ImplV2_1.cert_check fork.stateGas permitTypedHashLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitTypedHashLine, Blanc.Lift.SolcSignedQuery.typedHashLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [permitTypedHashLine, Blanc.Lift.SolcSignedQuery.typedHashLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    ((SolcSignedQuery.typed_hash_line (r0 := 0x47) (r1 := 0x1c) (d0 := 0x49) (d1 := 0x44)) ptrTyped lengthTyped (congrArg Bytes.keccak bytesTyped))
  exact args.call ImplV2_1.cert_check fork.stateGas rfl

private abbrev permitLowSLine := SolcSignedQuery.lowSLine 0x49 0xbf

private abbrev permitV27Line := SolcSignedQuery.v27Line 0x49 0xd7

private abbrev permitV28Line := SolcSignedQuery.v28Line

private theorem permit_signature_cut_toward {F target : Exec.Deriv} {b : Devm} {M : Mem}
    {s r v : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_4944_c89 b
      (s :: r :: v :: S) M K)
    (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ flag, Nonempty (CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_49d7_c7 b
      (flag :: 0 :: s :: r :: v :: S) M K) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check fork.stateGas
  obtain ⟨low⟩ := opened.line ImplV2_1.cert_check fork.stateGas permitLowSLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitLowSLine, Blanc.Lift.SolcSignedQuery.lowSLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [permitLowSLine, Blanc.Lift.SolcSignedQuery.lowSLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.lows_line (d0 := 0x49) (d1 := 0xbf))
  have taken := low.guardSucc ImplV2_1.cert_check fork.stateGas rfl rfl
  obtain ⟨validS⟩ := low.branchSucc ImplV2_1.cert_check fork.stateGas taken
  obtain ⟨openedV⟩ := validS.dest ImplV2_1.cert_check fork.stateGas
  obtain ⟨v27⟩ := openedV.line ImplV2_1.cert_check fork.stateGas permitV27Line rfl
    (by intro ni member xi same; subst ni
        simp only [permitV27Line, Blanc.Lift.SolcSignedQuery.v27Line, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [permitV27Line, Blanc.Lift.SolcSignedQuery.v27Line, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.v27_line (d0 := 0x49) (d1 := 0xd7))
  by_cases takenV : B256.eqCheck (B256.eqCheck (B256.eqCheck 27 (255 &&& v)) 0) 0 ≠ 0
  · exact ⟨_, v27.toSucc ImplV2_1.cert_check fork.stateGas takenV rfl⟩
  · have zeroV := not_not.mp takenV
    rw [zeroV] at v27
    obtain ⟨otherV⟩ := v27.toZero ImplV2_1.cert_check fork.stateGas
    obtain ⟨v28⟩ := otherV.line ImplV2_1.cert_check fork.stateGas permitV28Line rfl
      (by intro ni member xi same; subst ni
          simp only [permitV28Line, Blanc.Lift.SolcSignedQuery.v28Line, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
      (by intro ni member same; subst ni
          simp only [permitV28Line, Blanc.Lift.SolcSignedQuery.v28Line, List.mem_cons,
            List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
      SolcSignedQuery.v28_line
    exact ⟨_, ⟨v28⟩⟩

private theorem permit_recovery_cut_toward {F target : Exec.Deriv} {b : Devm} {M : Mem}
    {s r v : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_4944_c89 b
      (s :: r :: v :: S) M K)
    (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ reached : CursorStateToward ImplV2_1.code ImplV2_1.cert F target ImplV2_1.t_4a2d_c7 b
      (0 :: s :: r :: v :: S) M K, reached.node.pc = 0x4a2d := by
  obtain ⟨flag, ⟨before⟩⟩ := permit_signature_cut_toward cut fork
  obtain ⟨opened⟩ := before.dest ImplV2_1.cert_check fork.stateGas
  obtain ⟨guard⟩ := opened.line ImplV2_1.cert_check fork.stateGas
    (SolcSignedQuery.iszeroJumpLine 0x4a 0x2d) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.iszeroJumpLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro ni member same; subst ni
        simp only [SolcSignedQuery.iszeroJumpLine, List.mem_cons, List.not_mem_nil, Ninst.reg.injEq, reduceCtorEq, or_self] at member)
    SolcSignedQuery.iszero_jump_line
  have taken := guard.guardSucc ImplV2_1.cert_check fork.stateGas rfl rfl
  exact guard.branchSuccAt ImplV2_1.cert_check fork.stateGas taken

/-- The original raw root reaches the actual recovery helper before the
observed write. The explicit nonce inequality excludes the earlier nonce
write; finite row separation discharges it for tracked allowance keys. -/
theorem permitV2_1_root_recovery_toward_sstore {F target : Exec.Deriv} {targetKey : B256}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (targetHead : target.devm.stack.head? = some targetKey)
    (separated : nonceSlot (Sevm.dataWord F.sevm 4).toAdr ≠ targetKey)
    (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (R : Exec.Deriv) (κ : Cursor) (b : Devm) (M : Mem) (G : Nat)
      (digest domain : B256) (S : List B256),
      R.pc = 0x4a2d ∧ Exec.Deriv.ExecFreeUntil F R ∧ Exec.Deriv.ParentPrefix R target ∧
      R.sevm = F.sevm ∧ CursorOK ImplV2_1.code ImplV2_1.cert R κ ∧ κ.f = ImplV2_1.t_4a2d_c7 ∧
      κ.K.map Cont.f = [ImplV2_1.t_471c_c83, ImplV2_1.t_421e_c71,
        ImplV2_1.t_322d_c24, ImplV2_1.t_0452_c109] ∧
      R.devm = St b
        (0 :: Sevm.dataWord F.sevm 196 :: Sevm.dataWord F.sevm 164 ::
          (Sevm.dataWord F.sevm 132 &&& 255) :: digest :: 0x471c :: digest :: 0 :: 128 ::
          Sevm.dataWord F.sevm 196 :: Sevm.dataWord F.sevm 164 ::
          (Sevm.dataWord F.sevm 132 &&& 255) :: domain :: 0x421e ::
          (Sevm.dataWord F.sevm 4).toAdr.toB256 :: S) M G ∧
      PtrMem 450 480 M ∧ b.getCode 1 = F.devm.getCode 1 := by
  obtain ⟨b0, M0, sameState, ptr0, ⟨before⟩⟩ :=
    permitV2_1_root_nonce_toward_sstore pc code stack memory selector path store fork
  let owner := (Sevm.dataWord F.sevm 4).toAdr
  let spender := (Sevm.dataWord F.sevm 36).toAdr
  let nonce := b0.getStorVal F.sevm.currentTarget (nonceSlot owner)
  let b1 := afterSstoreH F.sevm (afterSloadH F.sevm b0 (nonceSlot owner)) (nonceSlot owner) (nonce + 1)
  let M1 := (M0.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes
  have ptr1 : PtrMem 128 96 M1 :=
    (ptr0.write 0 owner.toB256 (.inl (by decide))).write 32 17 (.inl (by decide))
  obtain ⟨at83⟩ := permit_call83_toward before ptr0 targetHead separated fork
  obtain ⟨ptrStruct, lengthStruct, _⟩ := SolcSignedQuery.struct_memory_facts
    (tag := 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9)
    (owner := owner) (spender := spender) (value := Sevm.dataWord F.sevm 68)
    (nonce := nonce) (deadline := Sevm.dataWord F.sevm 100) ptr1
  generalize structMemory : (SolcSignedQuery.structMemory
    0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9) M1 owner spender
    (Sevm.dataWord F.sevm 68) nonce (Sevm.dataWord F.sevm 100) = Ms at at83 ptrStruct lengthStruct
  let hash := (Ms.read 160 192).1.keccak
  obtain ⟨at89⟩ := permit_call89_toward at83 ptrStruct lengthStruct (hash := hash) rfl fork
  have ptrFinal := (SolcSignedQuery.typed_memory_facts
    (domain := b1.getStorVal F.sevm.currentTarget 15) (hash := hash) ptrStruct).2.1
  generalize typedMemory : SolcSignedQuery.typedMemory Ms (b1.getStorVal F.sevm.currentTarget 15)
    hash = Mt at at89 ptrFinal
  obtain ⟨reached, actualPc⟩ := permit_recovery_cut_toward at89 fork
  obtain ⟨gas, state⟩ := reached.state
  refine ⟨reached.node, reached.cursor, afterSloadH F.sevm b1 15, Mt, gas,
    _, _, _, actualPc, reached.free, reached.toward, reached.sevm_eq, reached.placed,
    reached.tree, reached.continuations, state, ptrFinal, ?_⟩
  have outerState : (afterSloadH F.sevm b1 15).state = b1.state := afterSloadH_state _ _ _
  unfold Devm.getCode Devm.getAcct
  rw [outerState]
  change b1.getCode 1 = F.devm.getCode 1
  dsimp only [b1]
  rw [afterSstoreH_getCode]
  unfold Devm.getCode Devm.getAcct
  rw [afterSloadH_state, sameState]

end Blanc.Lift.Usdc
