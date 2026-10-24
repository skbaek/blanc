import Blanc.Lift.Usdc.RecoveryV2_1
import Blanc.Lift.Usdc.Slots
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.InvWalkStep
import Blanc.Lift.SolcSignedQuery

/-! Actual V2_1 permit inputs, typed-data query and retained owner consumer. -/
namespace Blanc.Lift.Usdc
open Jaune Blanc Blanc.Lift

/-- The actual six-word V2_1 permit struct preimage. -/
def permitV2_1StructHash (owner spender : Adr) (value nonce deadline : B256) : B256 :=
  ((0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9 : B256).toBytes ++
    owner.toB256.toBytes ++ spender.toB256.toBytes ++ value.toBytes ++ nonce.toBytes ++
    deadline.toBytes).keccak

/-- The query digest computed from the actual nonce and post-nonce domain word.
The definition does not assume that the nonce write is disjoint from slot15. -/
def permitV2_1Digest (sevm : Sevm) (pre : Devm) : B256 :=
  let owner := (Sevm.dataWord sevm 4).toAdr
  let spender := (Sevm.dataWord sevm 36).toAdr
  let storage := Devm.getStor pre sevm.currentTarget
  let nonce := storage.get (nonceSlot owner)
  let domain := (storage.set (nonceSlot owner) (nonce + 1)).get 15
  (([0x19, 0x01] ++ domain.toBytes ++
    (permitV2_1StructHash owner spender (Sevm.dataWord sevm 68) nonce
      (Sevm.dataWord sevm 100)).toBytes : Bytes)).keccak

/-- The domain loaded after the actual nonce increment, without a separation hypothesis. -/
def permitV2_1Domain (sevm : Sevm) (pre : Devm) : B256 :=
  let storage := Devm.getStor pre sevm.currentTarget
  let key := nonceSlot (Sevm.dataWord sevm 4).toAdr
  (storage.set key (storage.get key + 1)).get 15

/-- The complete entry stack produced by the permit route at the actual recovery jump. -/
private abbrev permitV2_1RecoveryStackWith (sevm : Sevm) (digest domain : B256) : List B256 :=
  let s := Sevm.dataWord sevm 196
  let r := Sevm.dataWord sevm 164
  let v := Sevm.dataWord sevm 132 &&& 255
  let deadline := Sevm.dataWord sevm 100
  let value := Sevm.dataWord sevm 68
  let spender := (Sevm.dataWord sevm 36).toAdr.toB256
  let owner := (Sevm.dataWord sevm 4).toAdr.toB256
  [0, s, r, v, digest, 0x471c, digest, 0, 128, s, r, v, domain, 0x421e, owner,
    128, s, r, v, deadline, value, spender, owner, 0x322d, spender, owner,
    s, r, v, deadline, value, spender, owner, 0x452, 0xd505accf]

/-- Complete concrete recovery registers, including its real471c immediate caller. -/
def permitV2_1RecoveryStack (sevm : Sevm) (pre : Devm) : List B256 :=
  permitV2_1RecoveryStackWith sevm (permitV2_1Digest sevm pre) (permitV2_1Domain sevm pre)

private abbrev permitPrologue := SolcSignedQuery.prologue 0x00 0x10

private theorem permit_prologue_shape : ImplV2_1.t_0000_c0 =
    permitPrologue.foldr SFunc.next (.branch ImplV2_1.t_000c_c0 ImplV2_1.t_0010_c0) := rfl

private theorem permit_root_nonpayable
    {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F
      ImplV2_1.t_0010_c0 F.devm [F.sevm.value]
      (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  have placed := cursor_start ImplV2_1.cert_check pc code
  have first : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_0000_c0
      F.devm [] Mem.empty [] :=
    ⟨F, Cursor.start ImplV2_1.cert, .refl _, rfl, rfl, placed, rfl,
      ⟨F.devm.gasLeft, St.self stack memory⟩, rfl⟩
  obtain ⟨guard⟩ := first.lineH ImplV2_1.cert_check success fork.stateGas permitPrologue
    permit_prologue_shape (by
      intro ni member xi same; subst ni
      simp only [permitPrologue, Blanc.Lift.SolcSignedQuery.prologue, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.prologue_line (d0 := 0x00) (d1 := 0x10))
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRunH ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork.stateGas)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have nonzero : B256.eqCheck F.sevm.value 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨taken, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact taken
  have valueZero : F.sevm.value = 0 := eq_zero_of_iszero_ne_zero nonzero
  exact ⟨valueZero, guard.branchSuccH ImplV2_1.cert_check success fork.stateGas nonzero⟩

private abbrev permitSizeLine := SolcSignedQuery.sizeLine 0x03 0x36

private theorem permit_root_size
    {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 4 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F
        ImplV2_1.t_001a_c0 F.devm [] (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  obtain ⟨valueZero, ⟨start⟩⟩ := permit_root_nonpayable pc code stack memory success fork
  obtain ⟨opened⟩ := start.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas permitSizeLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitSizeLine, Blanc.Lift.SolcSignedQuery.sizeLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.size_line (d0 := 0x03) (d1 := 0x36))
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRunH ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork.stateGas)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have condition : B256.ltCheck F.sevm.data.length.toB256 4 = 0 := by
    rcases rpw_branch actualRun with ⟨zero, _, _⟩ | ⟨_, _, rejected⟩
    · exact zero
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
  have bound := toNat_ge_of_ltCheck_eq_zero condition
  change 4 ≤ F.sevm.data.length.toB256.toNat at bound
  rw [condition] at guard
  exact ⟨valueZero, bound, guard.branchZeroH ImplV2_1.cert_check success fork.stateGas⟩

private theorem permit_root_dispatch
    {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 4 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F
        ImplV2_1.t_0b03_c109 F.devm [0xd505accf]
        (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  obtain ⟨valueZero, sizeBound, ⟨start⟩⟩ := permit_root_size pc code stack memory success fork
  obtain ⟨first⟩ := start.lineH ImplV2_1.cert_check success fork.stateGas
    [.push [0x00] (by decide), .reg .calldataload, .push [0xe0] (by decide), .reg .shr,
      .reg (.dup 0), .push [0x7f, 0x2e, 0xec, 0xc3] (by decide), .reg .gt,
      .push [0x01, 0xb2] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := [0x1b2, 0, 0xd505accf]) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_calldataload step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, state⟩ := ri_shr step
      change _ = St _ (Sevm.selector F.sevm :: _) _ _ at state
      rw [selector] at state
      subst state
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_gt step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      cases line
      exact ⟨_, rfl⟩)
  obtain ⟨c1⟩ := first.branchZeroH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard0⟩ := c1.lineH ImplV2_1.cert_check success fork.stateGas
    [.reg (.dup 0), .push [0xb2, 0x11, 0x8a, 0x8d] (by decide), .reg .gt,
      .push [0x00, 0xf9] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := [0xf9, 0, 0xd505accf]) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_gt step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      cases line
      exact ⟨_, rfl⟩)
  obtain ⟨c2⟩ := guard0.branchZeroH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard1⟩ := c2.lineH ImplV2_1.cert_check success fork.stateGas
    [.reg (.dup 0), .push [0xe3, 0xee, 0x16, 0x0e] (by decide), .reg .gt,
      .push [0x00, 0xa2] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := [0xa2, 1, 0xd505accf]) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_gt step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      cases line
      exact ⟨_, rfl⟩)
  obtain ⟨c3⟩ := guard1.branchSuccH ImplV2_1.cert_check success fork.stateGas (by decide : (1 : B256) ≠ 0)
  obtain ⟨opened2⟩ := c3.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard2⟩ := opened2.lineH ImplV2_1.cert_check success fork.stateGas
    [.reg (.dup 0), .push [0xd6, 0x08, 0xea, 0x64] (by decide), .reg .gt,
      .push [0x00, 0xd3] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := [0xd3, 1, 0xd505accf]) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_gt step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      cases line
      exact ⟨_, rfl⟩)
  obtain ⟨c4⟩ := guard2.branchSuccH ImplV2_1.cert_check success fork.stateGas (by decide : (1 : B256) ≠ 0)
  obtain ⟨opened3⟩ := c4.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard3⟩ := opened3.lineH ImplV2_1.cert_check success fork.stateGas
    [.reg (.dup 0), .push [0xb2, 0x11, 0x8a, 0x8d] (by decide), .reg .eq,
      .push [0x0a, 0xb8] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := [0xab8, 0, 0xd505accf]) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_eq step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      cases line
      exact ⟨_, rfl⟩)
  obtain ⟨c5⟩ := guard3.toZeroH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard4⟩ := c5.lineH ImplV2_1.cert_check success fork.stateGas
    [.reg (.dup 0), .push [0xbd, 0x10, 0x24, 0x30] (by decide), .reg .eq,
      .push [0x0a, 0xfb] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := [0xafb, 0, 0xd505accf]) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_eq step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      cases line
      exact ⟨_, rfl⟩)
  obtain ⟨c6⟩ := guard4.toZeroH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard5⟩ := c6.lineH ImplV2_1.cert_check success fork.stateGas
    [.reg (.dup 0), .push [0xd5, 0x05, 0xac, 0xcf] (by decide), .reg .eq,
      .push [0x0b, 0x03] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := [0xb03, 1, 0xd505accf]) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_eq step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      cases line
      exact ⟨_, rfl⟩)
  obtain ⟨finish⟩ := guard5.toSuccH ImplV2_1.cert_check success fork.stateGas (by decide : (1 : B256) ≠ 0) (by rfl)
  exact ⟨valueZero, sizeBound, ⟨finish⟩⟩

private theorem permit_wrapper_guard
    {F : Exec.Deriv} {post b : Devm} {M : Mem}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F
      ImplV2_1.t_0b03_c109 b [0xd505accf] M [])
    (sizeBound : 4 ≤ F.sevm.data.length.toB256.toNat)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    228 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F
        ImplV2_1.t_0b19_c109 b
        [F.sevm.data.length.toB256 - 4, 4, 0x452, 0xd505accf] M []) := by
  obtain ⟨opened⟩ := cut.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas
    [.push [0x04, 0x52] (by decide), .push [0x04] (by decide), .reg (.dup 0),
      .reg .calldatasize, .reg .sub, .push [0xe0] (by decide), .reg (.dup 1),
      .reg .lt, .reg .iszero, .push [0x0b, 0x19] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := [0xb19, B256.eqCheck (B256.ltCheck (F.sevm.data.length.toB256 - 4) 224) 0,
      F.sevm.data.length.toB256 - 4, 4, 0x452, 0xd505accf]) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_calldatasize step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_sub step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_lt step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      cases line
      exact ⟨_, rfl⟩)
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRunH ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork.stateGas)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck (B256.ltCheck (F.sevm.data.length.toB256 - 4) 224) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  have condition := eq_zero_of_iszero_ne_zero taken
  have bound := toNat_ge_of_ltCheck_eq_zero condition
  rw [B256.toNat_sub_eq_of_le _ _ (by
    rw [B256.le_iff_toNat_le_toNat]; exact sizeBound)] at bound
  change 224 ≤ F.sevm.data.length.toB256.toNat - 4 at bound
  exact ⟨by omega, guard.branchSuccH ImplV2_1.cert_check success fork.stateGas taken⟩

private abbrev permitDecodeLine := SolcSignedQuery.decodeLine 0x30 0x92

private theorem permit_root_decoded
    {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 228 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F
        ImplV2_1.t_3092_c24 F.devm
        [Sevm.dataWord F.sevm 196, Sevm.dataWord F.sevm 164,
          Sevm.dataWord F.sevm 132 &&& 255, Sevm.dataWord F.sevm 100, Sevm.dataWord F.sevm 68,
          (Sevm.dataWord F.sevm 36).toAdr.toB256, (Sevm.dataWord F.sevm 4).toAdr.toB256,
          0x452, 0xd505accf]
        (Mem.empty.write 64 (128 : B256).toBytes) [ImplV2_1.t_0452_c109]) := by
  obtain ⟨valueZero, sizeBound, ⟨wrapper⟩⟩ :=
    permit_root_dispatch pc code stack memory selector success fork
  obtain ⟨bound, ⟨accepted⟩⟩ := permit_wrapper_guard wrapper sizeBound success fork
  obtain ⟨opened⟩ := accepted.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨decoded⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas permitDecodeLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitDecodeLine, Blanc.Lift.SolcSignedQuery.decodeLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.decode_line (d0 := 0x30) (d1 := 0x92))
  exact ⟨valueZero, bound, decoded.callH ImplV2_1.cert_check success fork.stateGas rfl⟩

private abbrev permitPauseLine := SolcSignedQuery.pauseLine 0x01 0x31 0x1c

private theorem permit_pause_guard {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_3092_c24 b S M K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_311c_c24
      (afterSloadH F.sevm b 1) S M K) := by
  obtain ⟨opened⟩ := cut.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas permitPauseLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitPauseLine, Blanc.Lift.SolcSignedQuery.pauseLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    ((SolcSignedQuery.pause_line (slot := 0x01) (d0 := 0x31) (d1 := 0x1c)) fork)
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRunH ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork.stateGas)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck (255 &&& (b.getStorVal F.sevm.currentTarget 1 /
      (0x10000000000000000000000000000000000000000 : B256))) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  exact guard.branchSuccH ImplV2_1.cert_check success fork.stateGas taken

private abbrev permitBlacklistReadLine := SolcSignedQuery.blacklistReadLine 0x03

private theorem permit_owner_blacklist_guard {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {a0 a1 a2 a3 a4 a5 : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_311c_c24 b
      (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ b' M', b'.state = b.state ∧ PtrMem 128 96 M' ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_319d_c24 b'
        (owner.toB256 :: a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M' K) := by
  obtain ⟨opened⟩ := cut.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨read⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas permitBlacklistReadLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBlacklistReadLine, Blanc.Lift.SolcSignedQuery.blacklistReadLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    ((SolcSignedQuery.blacklist_read_line (base := 0x03)) ptr fork)
  obtain ⟨guard⟩ := read.lineH ImplV2_1.cert_check success fork.stateGas
    [.push [0x31, 0x9d] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro gas d run
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_push step
        cases run
        exact ⟨_, rfl⟩)
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRunH ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork.stateGas)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck (255 &&& b.getStorVal F.sevm.currentTarget
      (mapSlot owner.toB256 3)) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  refine ⟨_, _, ?_, ?_, guard.branchSuccH ImplV2_1.cert_check success fork.stateGas taken⟩
  · exact afterSloadH_state _ _ _
  · exact (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 3 (.inl (by decide))

private theorem permit_spender_blacklist_guard {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {a0 a1 a2 a3 a4 a5 : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_319d_c24 b
      (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ b' M', b'.state = b.state ∧ PtrMem 128 96 M' ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_321e_c24 b'
        (owner.toB256 :: a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M' K) := by
  obtain ⟨opened⟩ := cut.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨read⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas permitBlacklistReadLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBlacklistReadLine, Blanc.Lift.SolcSignedQuery.blacklistReadLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    ((SolcSignedQuery.blacklist_read_line (base := 0x03)) ptr fork)
  obtain ⟨guard⟩ := read.lineH ImplV2_1.cert_check success fork.stateGas
    [.push [0x32, 0x1e] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro gas d run
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_push step
        cases run
        exact ⟨_, rfl⟩)
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRunH ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork.stateGas)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck (255 &&& b.getStorVal F.sevm.currentTarget
      (mapSlot owner.toB256 3)) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  refine ⟨_, _, ?_, ?_, guard.branchSuccH ImplV2_1.cert_check success fork.stateGas taken⟩
  · exact afterSloadH_state _ _ _
  · exact (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 3 (.inl (by decide))

private theorem permit_call71 {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v deadline value spender owner : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_321e_c24 b
      (spender :: owner :: s :: r :: v :: deadline :: value :: spender :: owner :: S) M K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_410c_c71 b
      (s :: r :: v :: deadline :: value :: spender :: owner :: 0x322d ::
       spender :: owner :: s :: r :: v :: deadline :: value :: spender :: owner :: S)
      M (ImplV2_1.t_322d_c24 :: K)) := by
  obtain ⟨opened⟩ := cut.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨args⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas
    (SolcSignedQuery.sevenArgsCallLine 0x32 0x2d 0x41 0x0c) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.sevenArgsCallLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    SolcSignedQuery.seven_args_call_line
  exact args.callH ImplV2_1.cert_check success fork.stateGas rfl

private theorem permit_deadline_guard {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v deadline : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_410c_c71 b
      (s :: r :: v :: deadline :: S) M K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.benvStat.time.toNat ≤ deadline.toNat ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_417b_c71 b
        (s :: r :: v :: deadline :: S) M K) := by
  obtain ⟨opened⟩ := cut.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas
    (SolcSignedQuery.deadlineLine 0x41 0x7b) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.deadlineLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    SolcSignedQuery.deadline_line
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRunH ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork.stateGas)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck (B256.ltCheck deadline F.sevm.benvStat.time) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  have zero := eq_zero_of_iszero_ne_zero taken
  exact ⟨toNat_ge_of_ltCheck_eq_zero zero,
    guard.branchSuccH ImplV2_1.cert_check success fork.stateGas taken⟩

private theorem permit_root_417b {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 228 ≤ F.sevm.data.length.toB256.toNat ∧
    F.sevm.benvStat.time.toNat ≤ (Sevm.dataWord F.sevm 100).toNat ∧
    ∃ b M, b.state = F.devm.state ∧ PtrMem 128 96 M ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_417b_c71 b
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
  obtain ⟨valueZero, sizeBound, ⟨decoded⟩⟩ :=
    permit_root_decoded pc code stack memory selector success fork
  obtain ⟨unpaused⟩ := permit_pause_guard decoded success fork
  obtain ⟨b1, M1, state1, ptr1, ⟨ownerAllowed⟩⟩ :=
    permit_owner_blacklist_guard unpaused (PtrMem.init 128) success fork
  obtain ⟨b2, M2, state2, ptr2, ⟨spenderAllowed⟩⟩ :=
    permit_spender_blacklist_guard ownerAllowed ptr1 success fork
  obtain ⟨called⟩ := permit_call71 spenderAllowed success fork
  obtain ⟨deadlineBound, continued⟩ := permit_deadline_guard called success fork
  refine ⟨valueZero, sizeBound, deadlineBound, b2, M2, ?_, ptr2, continued⟩
  rw [state2, state1]
  exact afterSloadH_state _ _ _

private abbrev permitNonceLine := SolcSignedQuery.nonceLine 0x11

private abbrev permitBufferHeadLine := SolcSignedQuery.bufferHeadLine [0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f, 0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10, 0x5f, 0xa2, 0xfa, 0xae, 0x01, 0x26, 0x11, 0x4a, 0x16, 0x9c, 0x64, 0x84, 0x5d, 0x61, 0x26, 0xc9] (by decide)

private abbrev permitBufferBodyLine := SolcSignedQuery.bufferBodyLine

private abbrev permitBufferTailLine := SolcSignedQuery.bufferTailLine 0x0f 0x42 0x1e 0x46 0xb5

private theorem permit_call83 {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v deadline value : B256} {spender owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_417b_c71 b
      (s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    let nonce := b.getStorVal F.sevm.currentTarget (nonceSlot owner)
    let b' := afterSstoreH F.sevm (afterSloadH F.sevm b (nonceSlot owner)) (nonceSlot owner) (nonce + 1)
    let M' := (M.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes
    Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_46b5_c83
      (afterSloadH F.sevm b' 15)
      (128 :: s :: r :: v :: b'.getStorVal F.sevm.currentTarget 15 :: 0x421e :: owner.toB256 ::
       128 :: s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      ((SolcSignedQuery.structMemory 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9) M' owner spender value nonce deadline) (ImplV2_1.t_421e_c71 :: K)) := by
  obtain ⟨opened⟩ := cut.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨updated⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas permitNonceLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitNonceLine, Blanc.Lift.SolcSignedQuery.nonceLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    ((SolcSignedQuery.nonce_line (base := 0x11)) ptr fork)
  have ptr' := (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 17 (.inl (by decide))
  change PtrMem 128 96 ((M.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes) at ptr'
  obtain ⟨head⟩ := updated.lineH ImplV2_1.cert_check success fork.stateGas permitBufferHeadLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBufferHeadLine, Blanc.Lift.SolcSignedQuery.bufferHeadLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    ((SolcSignedQuery.buffer_head_line (tag := [0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f, 0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10, 0x5f, 0xa2, 0xfa, 0xae, 0x01, 0x26, 0x11, 0x4a, 0x16, 0x9c, 0x64, 0x84, 0x5d, 0x61, 0x26, 0xc9]) (le := by decide)) ptr')
  obtain ⟨body⟩ := head.lineH ImplV2_1.cert_check success fork.stateGas permitBufferBodyLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBufferBodyLine, Blanc.Lift.SolcSignedQuery.bufferBodyLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    SolcSignedQuery.buffer_body_line
  have ptrHead := (ptr'.write 160
    (0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9 : B256)
    (.inr (by decide))).write 192 owner.toB256 (.inr (by decide))
  have ptrBody : PtrMem 128 352
      (SolcSignedQuery.structBodyMemory ((SolcSignedQuery.structHeadMemory 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9) _ owner) spender value
        (b.getStorVal F.sevm.currentTarget (nonceSlot owner)) deadline) :=
    (((ptrHead.write 224 spender.toB256 (.inr (by decide))).write 256 value
      (.inr (by decide))).write 288 _ (.inr (by decide))).write 320 deadline (.inr (by decide))
  obtain ⟨tail⟩ := body.lineH ImplV2_1.cert_check success fork.stateGas permitBufferTailLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBufferTailLine, Blanc.Lift.SolcSignedQuery.bufferTailLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    ((SolcSignedQuery.buffer_tail_line (slot := 0x0f) (r0 := 0x42) (r1 := 0x1e) (d0 := 0x46) (d1 := 0xb5)) ptrBody fork)
  exact tail.callH ImplV2_1.cert_check success fork.stateGas rfl

private abbrev permitStructHashLine := SolcSignedQuery.structHashLine

private abbrev permitTypedWordsLine := SolcSignedQuery.typedWordsLine

private abbrev permitTypedLengthLine := SolcSignedQuery.typedLengthLine

private abbrev permitTypedHashLine := SolcSignedQuery.typedHashLine 0x47 0x1c 0x49 0x44

private theorem permit_call89 {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v domain hash : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_46b5_c83 b
      (128 :: s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S) M K)
    (ptr : PtrMem 352 352 M) (length : memWord M 128 = 192)
    (hashRead : (M.read 160 192).1.keccak = hash)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    let digest := ([0x19, 0x01] ++ domain.toBytes ++ hash.toBytes : Bytes).keccak
    Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_4944_c89 b
      (s :: r :: v :: digest :: 0x471c :: digest :: 0 :: 128 ::
       s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S)
      (SolcSignedQuery.typedMemory M domain hash) (ImplV2_1.t_471c_c83 :: K)) := by
  obtain ⟨opened⟩ := cut.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨hashed⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas permitStructHashLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitStructHashLine, Blanc.Lift.SolcSignedQuery.structHashLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.struct_hash_line ptr length hashRead)
  obtain ⟨words⟩ := hashed.lineH ImplV2_1.cert_check success fork.stateGas permitTypedWordsLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitTypedWordsLine, Blanc.Lift.SolcSignedQuery.typedWordsLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.typed_words_line ptr)
  obtain ⟨ptrWords, ptrTyped, lengthTyped, bytesTyped⟩ := SolcSignedQuery.typed_memory_facts (domain := domain) (hash := hash) ptr
  obtain ⟨sized⟩ := words.lineH ImplV2_1.cert_check success fork.stateGas permitTypedLengthLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitTypedLengthLine, Blanc.Lift.SolcSignedQuery.typedLengthLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.typed_length_line ptrWords)
  obtain ⟨args⟩ := sized.lineH ImplV2_1.cert_check success fork.stateGas permitTypedHashLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitTypedHashLine, Blanc.Lift.SolcSignedQuery.typedHashLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    ((SolcSignedQuery.typed_hash_line (r0 := 0x47) (r1 := 0x1c) (d0 := 0x49) (d1 := 0x44)) ptrTyped lengthTyped (congrArg Bytes.keccak bytesTyped))
  exact args.callH ImplV2_1.cert_check success fork.stateGas rfl

private abbrev permitLowSLine := SolcSignedQuery.lowSLine 0x49 0xbf

private abbrev permitV27Line := SolcSignedQuery.v27Line 0x49 0xd7

private abbrev permitV28Line := SolcSignedQuery.v28Line

private theorem permit_signature_cut {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_4944_c89 b
      (s :: r :: v :: S) M K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ flag, Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_49d7_c7 b
      (flag :: 0 :: s :: r :: v :: S) M K) := by
  obtain ⟨opened⟩ := cut.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨low⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas permitLowSLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitLowSLine, Blanc.Lift.SolcSignedQuery.lowSLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.lows_line (d0 := 0x49) (d1 := 0xbf))
  obtain ⟨gas, actualState⟩ := low.state
  obtain ⟨outcome, actualRun⟩ := low.placed.sourceRunH ImplV2_1.cert_check
    (low.exn_eq.trans success) (by rw [low.sevm_eq]; exact fork.stateGas)
  rw [low.tree, actualState, low.sevm_eq] at actualRun
  have taken : B256.eqCheck (B256.gtCheck s
      (0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0 : B256)) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  obtain ⟨validS⟩ := low.branchSuccH ImplV2_1.cert_check success fork.stateGas taken
  obtain ⟨openedV⟩ := validS.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨v27⟩ := openedV.lineH ImplV2_1.cert_check success fork.stateGas permitV27Line rfl
    (by intro ni member xi same; subst ni
        simp only [permitV27Line, Blanc.Lift.SolcSignedQuery.v27Line, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (SolcSignedQuery.v27_line (d0 := 0x49) (d1 := 0xd7))
  by_cases takenV : B256.eqCheck (B256.eqCheck (B256.eqCheck 27 (255 &&& v)) 0) 0 ≠ 0
  · exact ⟨_, v27.toSuccH ImplV2_1.cert_check success fork.stateGas takenV rfl⟩
  · have zeroV := not_not.mp takenV
    rw [zeroV] at v27
    obtain ⟨otherV⟩ := v27.toZeroH ImplV2_1.cert_check success fork.stateGas
    obtain ⟨v28⟩ := otherV.lineH ImplV2_1.cert_check success fork.stateGas permitV28Line rfl
      (by intro ni member xi same; subst ni
          simp only [permitV28Line, Blanc.Lift.SolcSignedQuery.v28Line, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
      SolcSignedQuery.v28_line
    exact ⟨_, ⟨v28⟩⟩

private theorem permit_recovery_cut {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_4944_c89 b
      (s :: r :: v :: S) M K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ reached : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_4a2d_c7 b
      (0 :: s :: r :: v :: S) M K, reached.node.pc = 0x4a2d := by
  obtain ⟨flag, ⟨before⟩⟩ := permit_signature_cut cut success fork
  obtain ⟨opened⟩ := before.destH ImplV2_1.cert_check success fork.stateGas
  obtain ⟨guard⟩ := opened.lineH ImplV2_1.cert_check success fork.stateGas
    (SolcSignedQuery.iszeroJumpLine 0x4a 0x2d) rfl
    (by intro ni member xi same; subst ni
        simp only [SolcSignedQuery.iszeroJumpLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    SolcSignedQuery.iszero_jump_line
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRunH ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork.stateGas)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck flag 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  have decoded := guard.placed.jumpiAt_of_branch guard.tree
  obtain ⟨N, next, edge, jumped, _, stateful, placed⟩ :=
    cursor_jinst_forwardH ImplV2_1.cert_check guard.placed decoded
      (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork.stateGas)
  have actualStep : ConfStep (Ninst.RunWith (Cursor.DescOf guard.node)) ImplV2_1.cert.prog F.sevm
      ⟨St b (0x4a2d :: B256.eqCheck flag 0 :: 0 :: s :: r :: v :: S) M gas,
        .branch ImplV2_1.t_49dd_c7 ImplV2_1.t_4a2d_c7, K⟩
      ⟨N.devm, next.f, next.K.map Cont.f⟩ := by
    simpa only [Cursor.conf, guard.sevm_eq, actualState, guard.tree, guard.continuations,
      show Bytes.toB256 [0x4a, 0x2d] = (0x4a2d : B256) from rfl] using stateful
  have shape : next.f = ImplV2_1.t_4a2d_c7 ∧ next.K.map Cont.f = K ∧
      ∃ G', N.devm = St b (0 :: s :: r :: v :: S) M G' := by
    generalize hf : next.f = f' at actualStep ⊢
    generalize hk : next.K.map Cont.f = K' at actualStep ⊢
    generalize hd : N.devm = d' at actualStep ⊢
    cases actualStep with
    | zero _ pop => exact (taken (St.of_pop2 pop).2.1).elim
    | succ _ _ _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩
  have actualPc : N.pc = 0x4a2d := by
    rcases of_jumpi_run jumped with ⟨x, _, pop⟩ | ⟨x, y, nextPc, pop, _, _⟩
    · rw [actualState] at pop
      exact (taken (St.of_pop2 pop).2.1).elim
    · rw [actualState] at pop
      rw [← (St.of_pop2 pop).1] at nextPc
      exact nextPc
  have sameExn : N.exn = guard.node.exn := by
    generalize origin : guard.node = D at edge ⊢
    cases edge <;> rfl
  exact ⟨⟨N, next, guard.free.trans (Exec.Deriv.ExecFreeUntil.ofStep edge
    (Blanc.Jinst.At.not_exec decoded)), (Cursor.parentStep_sevm edge).trans guard.sevm_eq,
    sameExn.trans guard.exn_eq, placed, shape.1, shape.2.2, shape.2.1⟩, actualPc⟩

/-- A successful fresh V2_1 permit execution produces its actual query registers,
free pointer and four real continuations. This is a local producer on
any `NeutralFork`; proxy/history entry remains an upstream obligation. -/
theorem permitV2_1_query_entry {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (b : Devm) (M : Mem) (R : Exec.Deriv) (κ : Cursor),
      R.pc = 0x4a2d ∧ Exec.Deriv.ExecFreeUntil F R ∧ R.sevm = F.sevm ∧ R.exn = F.exn ∧
      CursorOK ImplV2_1.code ImplV2_1.cert R κ ∧ κ.f = ImplV2_1.t_4a2d_c7 ∧
      κ.K.map Cont.f = [ImplV2_1.t_471c_c83, ImplV2_1.t_421e_c71, ImplV2_1.t_322d_c24, ImplV2_1.t_0452_c109] ∧
      (∃ G, R.devm = St b (permitV2_1RecoveryStack F.sevm F.devm) M G) ∧
      PtrMem 450 480 M ∧ b.getCode 1 = F.devm.getCode 1 := by
  obtain ⟨_, _, _, b0, M0, sameState, ptr0, ⟨before⟩⟩ :=
    permit_root_417b pc code stack memory selector success fork
  let owner := (Sevm.dataWord F.sevm 4).toAdr
  let spender := (Sevm.dataWord F.sevm 36).toAdr
  let nonce := b0.getStorVal F.sevm.currentTarget (nonceSlot owner)
  let b1 := afterSstoreH F.sevm (afterSloadH F.sevm b0 (nonceSlot owner)) (nonceSlot owner) (nonce + 1)
  let M1 := (M0.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes
  have ptr1 : PtrMem 128 96 M1 :=
    (ptr0.write 0 owner.toB256 (.inl (by decide))).write 32 17 (.inl (by decide))
  obtain ⟨at83⟩ := permit_call83 before ptr0 success fork
  obtain ⟨ptrStruct, lengthStruct, hashStruct⟩ := SolcSignedQuery.struct_memory_facts (tag := 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9)
    (owner := owner) (spender := spender) (value := Sevm.dataWord F.sevm 68)
    (nonce := nonce) (deadline := Sevm.dataWord F.sevm 100) ptr1
  generalize structMemory : (SolcSignedQuery.structMemory 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9) M1 owner spender (Sevm.dataWord F.sevm 68) nonce
    (Sevm.dataWord F.sevm 100) = Ms at at83 ptrStruct lengthStruct hashStruct
  change (Ms.read 160 192).1.keccak =
    permitV2_1StructHash owner spender (Sevm.dataWord F.sevm 68) nonce
      (Sevm.dataWord F.sevm 100) at hashStruct
  obtain ⟨at89⟩ := permit_call89 at83 ptrStruct lengthStruct hashStruct success fork
  have ptrFinal := (SolcSignedQuery.typed_memory_facts
    (domain := b1.getStorVal F.sevm.currentTarget 15)
    (hash := permitV2_1StructHash owner spender (Sevm.dataWord F.sevm 68) nonce
      (Sevm.dataWord F.sevm 100)) ptrStruct).2.1
  generalize typedMemory : SolcSignedQuery.typedMemory Ms (b1.getStorVal F.sevm.currentTarget 15)
    (permitV2_1StructHash owner spender (Sevm.dataWord F.sevm 68) nonce (Sevm.dataWord F.sevm 100)) = Mt at at89 ptrFinal
  obtain ⟨reached, actualPc⟩ := permit_recovery_cut at89 success fork
  have originalStorage : Devm.getStor b0 F.sevm.currentTarget = Devm.getStor F.devm F.sevm.currentTarget := by
    unfold Devm.getStor Devm.getAcct
    rw [sameState]
  have loadedState : (afterSloadH F.sevm b0 (nonceSlot owner)).state = b0.state := by
    exact afterSloadH_state _ _ _
  have loadedStorage : Devm.getStor (afterSloadH F.sevm b0 (nonceSlot owner)) F.sevm.currentTarget =
      Devm.getStor F.devm F.sevm.currentTarget := by
    unfold Devm.getStor Devm.getAcct
    rw [loadedState, sameState]
  have nonceEq : nonce = (Devm.getStor F.devm F.sevm.currentTarget).get (nonceSlot owner) := by
    change (Devm.getStor b0 F.sevm.currentTarget).get _ = _
    rw [originalStorage]
  have domainEq : b1.getStorVal F.sevm.currentTarget 15 = permitV2_1Domain F.sevm F.devm := by
    change (Devm.getStor b1 F.sevm.currentTarget).get 15 = _
    dsimp only [b1]
    rw [afterSstoreH_getStor_self, loadedStorage, nonceEq]
    rfl
  have digestEq :
      ([0x19, 0x01] ++ (b1.getStorVal F.sevm.currentTarget 15).toBytes ++
        (permitV2_1StructHash owner spender (Sevm.dataWord F.sevm 68) nonce
          (Sevm.dataWord F.sevm 100)).toBytes : Bytes).keccak = permitV2_1Digest F.sevm F.devm := by
    rw [domainEq, nonceEq]
    rfl
  obtain ⟨gas, actualState⟩ := reached.state
  have stackEq := congrArg₂ (permitV2_1RecoveryStackWith F.sevm) digestEq domainEq
  have reachedState : ∃ G, reached.node.devm = St (afterSloadH F.sevm b1 15)
      (permitV2_1RecoveryStack F.sevm F.devm) Mt G :=
    ⟨gas, actualState.trans (congrArg (fun S => St (afterSloadH F.sevm b1 15) S Mt gas) stackEq)⟩
  refine ⟨afterSloadH F.sevm b1 15, Mt, reached.node, reached.cursor, actualPc,
    reached.free, reached.sevm_eq, reached.exn_eq, reached.placed, reached.tree,
    reached.continuations, reachedState, ptrFinal, ?_⟩
  have outerState : (afterSloadH F.sevm b1 15).state = b1.state := by
    exact afterSloadH_state _ _ _
  unfold Devm.getCode Devm.getAcct
  rw [outerState]
  change b1.getCode 1 = F.devm.getCode 1
  dsimp only [b1]
  rw [afterSstoreH_getCode]
  unfold Devm.getCode Devm.getAcct
  rw [loadedState, sameState]

private theorem permit_owner_return {N : Exec.Deriv} {κ : Cursor} {post : Devm}
    {adr : Adr} {digest s r v domain owner : B256} {S : List B256} {K : List SFunc}
    (placed : CursorOK ImplV2_1.code ImplV2_1.cert N κ)
    (tree : κ.f = ImplV2_1.t_471c_c83)
    (stack : N.devm.stack = adr.toB256 :: digest :: 0 :: 128 :: s :: r :: v :: domain :: 0x421e :: owner :: S)
    (continuations : κ.K.map Cont.f = ImplV2_1.t_421e_c71 :: K)
    (success : N.exn = .ok post) (fork : NeutralFork N.sevm.benvStat.fork) :
    ∃ (Q : Exec.Deriv) (next : Cursor), Exec.Deriv.ExecFreeUntil N Q ∧
      CursorOK ImplV2_1.code ImplV2_1.cert Q next ∧ next.f = ImplV2_1.t_421e_c71 ∧
      Q.devm.stack = adr.toB256 :: owner :: S ∧ owner = adr.toB256 := by
  obtain ⟨Q, next, span, sameEnv, sameExn, finalPlaced, callerTree, _, returned⟩ :=
    placed.quietReturnH ImplV2_1.cert_check success fork.stateGas
      (E := []) (by rfl) (by rfl) (by rw [tree]; rfl) (by rw [tree]; rfl) continuations
  rw [tree, St.self stack rfl] at returned
  obtain ⟨gas, state⟩ := SolcSignedQuery.recovery_epilogue returned
  have comparisonStack : Q.devm.stack = adr.toB256 :: owner :: S := by rw [state, St.stack]
  have ownerEq := recoveryV2_1_owner_comparison finalPlaced callerTree comparisonStack
    (sameExn.trans success) (by rw [sameEnv]; exact fork)
  exact ⟨Q, next, span, finalPlaced, callerTree, comparisonStack, ownerEq⟩

/-- The actual fresh permit invocation consumes the answer to its derived query,
returns through471c and compares it to the calldata owner at421e. The original
filled slot, source spawn and native precompile entry are retained. This local
successful-route theorem does not enumerate other selectors or failed calls. -/
theorem permitV2_1_query_consumed {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (nodeleg : getDelegatedCodeAddress (F.devm.getCode 1) = none)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (R : Exec.Deriv) (call : CallOccurrenceStep R .staticcall) (parent child : Devm)
      (gas : Nat) (Q : Exec.Deriv) (next : Cursor),
      let owner := (Sevm.dataWord F.sevm 4).toAdr
      let input := (permitV2_1Digest F.sevm F.devm).toBytes ++
        (Sevm.dataWord F.sevm 132 &&& 255).toBytes ++
        (Sevm.dataWord F.sevm 164).toBytes ++ (Sevm.dataWord F.sevm 196).toBytes
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      R.pc = 0x4a2d ∧ Exec.Deriv.ExecFreeUntil F R ∧
      Exec.Deriv.ExecFreeUntil R call.occurrence.node ∧
      call.occurrence.node.pc = 0x4a78 ∧ call.occurrence.node.sevm = F.sevm ∧
      Ninst.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm, call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent 450 32) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧ call.occurrence.slot = .none ∧
      (Frame.ofCall msg).enter = .done
        ((Frame.ofCall msg).settle (executePrecomp (initEvm (msg.withBenv msg.benv)) 1)) ∧
      gasEcrecover ≤ gas ∧ child.error.isSome = false ∧ child.output = owner.toB256.toBytes ∧
      ecrecoverOutput input = owner.toB256.toBytes ∧ owner ≠ 0 ∧
      call.returned.devm.returnData = owner.toB256.toBytes ∧
      Exec.Deriv.ExecFreeUntil call.returned Q ∧
      CursorOK ImplV2_1.code ImplV2_1.cert Q next ∧ next.f = ImplV2_1.t_421e_c71 ∧
      ∃ S, Q.devm.stack = owner.toB256 :: owner.toB256 :: S := by
  obtain ⟨b, M, R, κ, actualPc, origin, sameEnv, sameExn, placed, tree,
    continuations, ⟨G, state⟩, ptr, code1⟩ :=
    permitV2_1_query_entry pc code stack memory selector success fork
  dsimp only [permitV2_1RecoveryStack, permitV2_1RecoveryStackWith] at state
  obtain ⟨call, parent, child, gas, adr, N, cursor, callPc, beforeSpan, spawned, process,
    emptySlot, native, paid, clean, childOutput, output, nonzero, returnData,
    suffix, suffixExn, suffixEnv, finalPlaced, callerTree, callerK, callerStack⟩ :=
    recoveryV2_1_consumes placed tree actualPc state ptr (by decide) (by decide)
      (by rw [code1]; exact nodeleg) continuations (sameExn.trans success)
      (by rw [sameEnv]; exact fork)
  obtain ⟨Q, next, epilogue, comparisonPlaced, comparisonTree, comparisonStack, ownerEq⟩ :=
    permit_owner_return finalPlaced callerTree callerStack callerK
      ((suffixExn.trans sameExn).trans success)
      (by rw [suffixEnv, sameEnv]; exact fork)
  have mask : (255 &&& (Sevm.dataWord F.sevm 132 &&& 255)) =
      (Sevm.dataWord F.sevm 132 &&& 255) := by
    rw [B256.and_comm, B256.and_idem_right]
  rw [mask] at spawned process native output
  rw [← ownerEq] at childOutput output returnData comparisonStack
  have ownerAdrEq : (Sevm.dataWord F.sevm 4).toAdr = adr := by
    simpa only [toAdr_toB256] using congrArg B256.toAdr ownerEq
  have ownerNonzero : (Sevm.dataWord F.sevm 4).toAdr ≠ 0 := by
    intro vanished
    exact nonzero (ownerAdrEq.symm.trans vanished)
  exact ⟨R, call, parent, child, gas, Q, next, actualPc, origin, beforeSpan, callPc,
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq beforeSpan.1).trans sameEnv, spawned, process, emptySlot, native, paid, clean,
    childOutput, output, ownerNonzero, returnData, suffix.trans epilogue,
    comparisonPlaced, comparisonTree, _, comparisonStack⟩

end Blanc.Lift.Usdc
