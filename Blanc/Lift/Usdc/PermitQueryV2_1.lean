import Blanc.Lift.Usdc.RecoveryV2_1
import Blanc.Lift.Usdc.Slots
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.InvWalkStep

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
private def permitV2_1RecoveryStackWith (sevm : Sevm) (digest domain : B256) : List B256 :=
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

private theorem permit_recovery_epilogue
    {sevm : Sevm} {b D : Devm} {M : Mem} {G : Nat}
    {answer digest s r v domain ret owner : B256} {S : List B256}
    (run : SFunc.Run ImplV2_1.cert.prog sevm
      (St b (answer :: digest :: 0 :: 128 :: s :: r :: v :: domain :: ret :: owner :: S) M G)
      ImplV2_1.t_471c_c83 (.returned D)) :
    ∃ G', D = St b (answer :: owner :: S) M G' := by
  unfold ImplV2_1.t_471c_c83 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  exact rpw_ret run

private def permitPrologue : List Ninst :=
  [.push [0x80] (by decide), .push [0x40] (by decide), .reg .mstore,
   .reg .callvalue, .reg (.dup 0), .reg .iszero, .push [0x00, 0x10] (by decide)]

private theorem permit_prologue_shape : ImplV2_1.t_0000_c0 =
    permitPrologue.foldr SFunc.next (.branch ImplV2_1.t_000c_c0 ImplV2_1.t_0010_c0) := rfl

private theorem permit_prologue_line {sevm : Sevm} {b d : Devm} {M : Mem}
    {G : Nat} {S : List B256}
    (run : Line.Run sevm (St b S M G) permitPrologue d) :
    ∃ G', d = St b (16 :: B256.eqCheck sevm.value 0 :: sevm.value :: S)
      (M.write 64 (128 : B256).toBytes) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_callvalue step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

private theorem permit_root_nonpayable
    {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F
      ImplV2_1.t_0010_c0 F.devm [F.sevm.value]
      (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  have placed := cursor_start ImplV2_1.cert_check pc code
  have first : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_0000_c0
      F.devm [] Mem.empty [] :=
    ⟨F, Cursor.start ImplV2_1.cert, .refl _, rfl, rfl, placed, rfl,
      ⟨F.devm.gasLeft, St.self stack memory⟩, rfl⟩
  obtain ⟨guard⟩ := first.line ImplV2_1.cert_check success fork permitPrologue
    permit_prologue_shape (by
      intro ni member xi same; subst ni
      simp only [permitPrologue, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    permit_prologue_line
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRun ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have nonzero : B256.eqCheck F.sevm.value 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨taken, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact taken
  have valueZero : F.sevm.value = 0 := eq_zero_of_iszero_ne_zero nonzero
  exact ⟨valueZero, guard.branchSucc ImplV2_1.cert_check success fork nonzero⟩

private def permitSizeLine : List Ninst :=
  [.reg .pop, .push [0x04] (by decide), .reg .calldatasize, .reg .lt,
   .push [0x03, 0x36] (by decide)]

private theorem permit_size_line {sevm : Sevm} {b d : Devm} {M : Mem}
    {G : Nat} {value : B256}
    (run : Line.Run sevm (St b [value] M G) permitSizeLine d) :
    ∃ G', d = St b [0x336, B256.ltCheck sevm.data.length.toB256 4] M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldatasize step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_lt step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

private theorem permit_root_size
    {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 4 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F
        ImplV2_1.t_001a_c0 F.devm [] (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  obtain ⟨valueZero, ⟨start⟩⟩ := permit_root_nonpayable pc code stack memory success fork
  obtain ⟨opened⟩ := start.dest ImplV2_1.cert_check success fork
  obtain ⟨guard⟩ := opened.line ImplV2_1.cert_check success fork permitSizeLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitSizeLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    permit_size_line
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRun ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have condition : B256.ltCheck F.sevm.data.length.toB256 4 = 0 := by
    rcases rpw_branch actualRun with ⟨zero, _, _⟩ | ⟨_, _, rejected⟩
    · exact zero
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
  have bound := toNat_ge_of_ltCheck_eq_zero condition
  change 4 ≤ F.sevm.data.length.toB256.toNat at bound
  rw [condition] at guard
  exact ⟨valueZero, bound, guard.branchZero ImplV2_1.cert_check success fork⟩

private theorem permit_root_dispatch
    {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    F.sevm.value = 0 ∧ 4 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F
        ImplV2_1.t_0b03_c109 F.devm [0xd505accf]
        (Mem.empty.write 64 (128 : B256).toBytes) []) := by
  obtain ⟨valueZero, sizeBound, ⟨start⟩⟩ := permit_root_size pc code stack memory success fork
  obtain ⟨first⟩ := start.line ImplV2_1.cert_check success fork
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
  obtain ⟨c1⟩ := first.branchZero ImplV2_1.cert_check success fork
  obtain ⟨guard0⟩ := c1.line ImplV2_1.cert_check success fork
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
  obtain ⟨c2⟩ := guard0.branchZero ImplV2_1.cert_check success fork
  obtain ⟨guard1⟩ := c2.line ImplV2_1.cert_check success fork
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
  obtain ⟨c3⟩ := guard1.branchSucc ImplV2_1.cert_check success fork (by decide : (1 : B256) ≠ 0)
  obtain ⟨opened2⟩ := c3.dest ImplV2_1.cert_check success fork
  obtain ⟨guard2⟩ := opened2.line ImplV2_1.cert_check success fork
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
  obtain ⟨c4⟩ := guard2.branchSucc ImplV2_1.cert_check success fork (by decide : (1 : B256) ≠ 0)
  obtain ⟨opened3⟩ := c4.dest ImplV2_1.cert_check success fork
  obtain ⟨guard3⟩ := opened3.line ImplV2_1.cert_check success fork
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
  obtain ⟨c5⟩ := guard3.toZero ImplV2_1.cert_check success fork
  obtain ⟨guard4⟩ := c5.line ImplV2_1.cert_check success fork
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
  obtain ⟨c6⟩ := guard4.toZero ImplV2_1.cert_check success fork
  obtain ⟨guard5⟩ := c6.line ImplV2_1.cert_check success fork
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
  obtain ⟨finish⟩ := guard5.toSucc ImplV2_1.cert_check success fork (by decide : (1 : B256) ≠ 0) (by rfl)
  exact ⟨valueZero, sizeBound, ⟨finish⟩⟩

private theorem permit_wrapper_guard
    {F : Exec.Deriv} {post b : Devm} {M : Mem}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F
      ImplV2_1.t_0b03_c109 b [0xd505accf] M [])
    (sizeBound : 4 ≤ F.sevm.data.length.toB256.toNat)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    228 ≤ F.sevm.data.length.toB256.toNat ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F
        ImplV2_1.t_0b19_c109 b
        [F.sevm.data.length.toB256 - 4, 4, 0x452, 0xd505accf] M []) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check success fork
  obtain ⟨guard⟩ := opened.line ImplV2_1.cert_check success fork
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
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRun ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork)
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
  exact ⟨by omega, guard.branchSucc ImplV2_1.cert_check success fork taken⟩

private def permitDecodeLine : List Ninst :=
  [.reg .pop,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg (.dup 1),
   .reg .calldataload,
   .reg (.dup 1),
   .reg .and,
   .reg (.swap 1),
   .push [0x20] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .and,
   .reg (.swap 0),
   .push [0x40] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0x60] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0xff] (by decide),
   .push [0x80] (by decide),
   .reg (.dup 2),
   .reg .add,
   .reg .calldataload,
   .reg .and,
   .reg (.swap 0),
   .push [0xa0] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0xc0] (by decide),
   .reg .add,
   .reg .calldataload,
   .push [0x30, 0x92] (by decide)]

private theorem permit_decode_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {available : B256}
    (run : Line.Run sevm (St b [available, 4, 0x452, 0xd505accf] M G) permitDecodeLine d) :
    ∃ G', d = St b
      [0x3092, Sevm.dataWord sevm 196, Sevm.dataWord sevm 164,
        Sevm.dataWord sevm 132 &&& 255, Sevm.dataWord sevm 100, Sevm.dataWord sevm 68,
        (Sevm.dataWord sevm 36).toAdr.toB256, (Sevm.dataWord sevm 4).toAdr.toB256,
        0x452, 0xd505accf] M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  simp only [ff20_and_word]
  exact ⟨_, rfl⟩

private theorem permit_root_decoded
    {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
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
  obtain ⟨opened⟩ := accepted.dest ImplV2_1.cert_check success fork
  obtain ⟨decoded⟩ := opened.line ImplV2_1.cert_check success fork permitDecodeLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitDecodeLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    permit_decode_line
  exact ⟨valueZero, bound, decoded.call ImplV2_1.cert_check success fork rfl⟩

private def permitPauseLine : List Ninst :=
  [.push [0x01] (by decide), .reg .sload,
   .push [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
   .reg (.swap 0), .reg .div, .push [0xff] (by decide), .reg .and,
   .reg .iszero, .push [0x31, 0x1c] (by decide)]

private theorem permit_pause_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {S : List B256} (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm (St b S M G) permitPauseLine d) :
    ∃ G', d = St (afterSload sevm b 1)
      (0x311c :: B256.eqCheck (255 &&& (b.getStorVal sevm.currentTarget 1 /
        (0x10000000000000000000000000000000000000000 : B256))) 0 :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_div step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

private theorem permit_pause_guard {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_3092_c24 b S M K)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_311c_c24
      (afterSload F.sevm b 1) S M K) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check success fork
  obtain ⟨guard⟩ := opened.line ImplV2_1.cert_check success fork permitPauseLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitPauseLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_pause_line fork)
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRun ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck (255 &&& (b.getStorVal F.sevm.currentTarget 1 /
      (0x10000000000000000000000000000000000000000 : B256))) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  exact guard.branchSucc ImplV2_1.cert_check success fork taken

private def permitBlacklistReadLine : List Ninst :=
  [.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg (.dup 7),
   .reg .and,
   .push [0x00] (by decide),
   .reg (.swap 0),
   .reg (.dup 1),
   .reg .mstore,
   .push [0x03] (by decide),
   .push [0x20] (by decide),
   .reg .mstore,
   .push [0x40] (by decide),
   .reg (.swap 0),
   .reg .keccak256,
   .reg .sload,
   .reg (.dup 7),
   .reg (.swap 0),
   .push [0xff] (by decide),
   .reg .and,
   .reg .iszero]

private theorem permit_blacklist_read_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {a0 a1 a2 a3 a4 a5 : B256} {owner : Adr} {S : List B256}
    (ptr : PtrMem 128 96 M) (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm
      (St b (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M G)
      permitBlacklistReadLine d) :
    ∃ G', d = St (afterSload sevm b (mapSlot owner.toB256 3))
      (B256.eqCheck (255 &&& b.getStorVal sevm.currentTarget (mapSlot owner.toB256 3)) 0 ::
        owner.toB256 :: a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S)
      ((M.write 0 owner.toB256.toBytes).write 32 (3 : B256).toBytes) G' := by
  have ptr' := (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 3 (.inl (by decide))
  change PtrMem 128 96 ((M.write 0 owner.toB256.toBytes).write 32 (3 : B256).toBytes) at ptr'
  have noGrowth := ptr'.read_self (i := 0) (sz := 64) (by decide)
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_and step
  rw [B256.and_comm, ff20_and_word, toAdr_toB256] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_keccak step
  rw [keccak_scratch] at state
  rw [show (Bytes.toB256 [0x00]).toNat = 0 from rfl,
    show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    show (Bytes.toB256 [0x20]).toNat = 32 from rfl,
    show Bytes.toB256 [0x03] = (3 : B256) from rfl, noGrowth] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  cases run
  exact ⟨_, rfl⟩

private theorem permit_owner_blacklist_guard {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {a0 a1 a2 a3 a4 a5 : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_311c_c24 b
      (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ b' M', b'.state = b.state ∧ PtrMem 128 96 M' ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_319d_c24 b'
        (owner.toB256 :: a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M' K) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check success fork
  obtain ⟨read⟩ := opened.line ImplV2_1.cert_check success fork permitBlacklistReadLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBlacklistReadLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_blacklist_read_line ptr fork)
  obtain ⟨guard⟩ := read.line ImplV2_1.cert_check success fork
    [.push [0x31, 0x9d] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro gas d run
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_push step
        cases run
        exact ⟨_, rfl⟩)
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRun ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck (255 &&& b.getStorVal F.sevm.currentTarget
      (mapSlot owner.toB256 3)) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  refine ⟨_, _, ?_, ?_, guard.branchSucc ImplV2_1.cert_check success fork taken⟩
  · unfold afterSload
    split <;> rfl
  · exact (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 3 (.inl (by decide))

private theorem permit_spender_blacklist_guard {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {a0 a1 a2 a3 a4 a5 : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_319d_c24 b
      (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ b' M', b'.state = b.state ∧ PtrMem 128 96 M' ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_321e_c24 b'
        (owner.toB256 :: a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M' K) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check success fork
  obtain ⟨read⟩ := opened.line ImplV2_1.cert_check success fork permitBlacklistReadLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBlacklistReadLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_blacklist_read_line ptr fork)
  obtain ⟨guard⟩ := read.line ImplV2_1.cert_check success fork
    [.push [0x32, 0x1e] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by intro gas d run
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_push step
        cases run
        exact ⟨_, rfl⟩)
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRun ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck (255 &&& b.getStorVal F.sevm.currentTarget
      (mapSlot owner.toB256 3)) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  refine ⟨_, _, ?_, ?_, guard.branchSucc ImplV2_1.cert_check success fork taken⟩
  · unfold afterSload
    split <;> rfl
  · exact (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 3 (.inl (by decide))

private theorem permit_call71 {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v deadline value spender owner : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_321e_c24 b
      (spender :: owner :: s :: r :: v :: deadline :: value :: spender :: owner :: S) M K)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_410c_c71 b
      (s :: r :: v :: deadline :: value :: spender :: owner :: 0x322d ::
       spender :: owner :: s :: r :: v :: deadline :: value :: spender :: owner :: S)
      M (ImplV2_1.t_322d_c24 :: K)) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check success fork
  obtain ⟨args⟩ := opened.line ImplV2_1.cert_check success fork
    [.push [0x32, 0x2d] (by decide), .reg (.dup 9), .reg (.dup 9), .reg (.dup 9),
      .reg (.dup 9), .reg (.dup 9), .reg (.dup 9), .reg (.dup 9),
      .push [0x41, 0x0c] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by
      intro gas d run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_push step
      cases run
      exact ⟨_, rfl⟩)
  exact args.call ImplV2_1.cert_check success fork rfl

private theorem permit_deadline_guard {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v deadline : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_410c_c71 b
      (s :: r :: v :: deadline :: S) M K)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    F.sevm.benvStat.time.toNat ≤ deadline.toNat ∧
      Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_417b_c71 b
        (s :: r :: v :: deadline :: S) M K) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check success fork
  obtain ⟨guard⟩ := opened.line ImplV2_1.cert_check success fork
    [.reg .timestamp, .reg (.dup 4), .reg .lt, .reg .iszero,
      .push [0x41, 0x7b] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by
      intro gas d run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_timestamp step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_lt step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_push step
      cases run
      exact ⟨_, rfl⟩)
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRun ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck (B256.ltCheck deadline F.sevm.benvStat.time) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  have zero := eq_zero_of_iszero_ne_zero taken
  exact ⟨toNat_ge_of_ltCheck_eq_zero zero,
    guard.branchSucc ImplV2_1.cert_check success fork taken⟩

private theorem permit_root_417b {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
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
  unfold afterSload
  split <;> rfl

private def permitNonceLine : List Ninst :=
  [.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg (.dup 0),
   .reg (.dup 8),
   .reg .and,
   .push [0x00] (by decide),
   .reg (.dup 1),
   .reg (.dup 1),
   .reg .mstore,
   .push [0x11] (by decide),
   .push [0x20] (by decide),
   .reg (.swap 0),
   .reg (.dup 1),
   .reg .mstore,
   .push [0x40] (by decide),
   .reg (.swap 1),
   .reg (.dup 2),
   .reg (.swap 0),
   .reg .keccak256,
   .reg (.dup 0),
   .reg .sload,
   .push [0x01] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .sstore]

private theorem permit_nonce_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v deadline value : B256} {spender owner : Adr} {S : List B256}
    (ptr : PtrMem 128 96 M) (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm (St b
      (s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M G)
      permitNonceLine d) :
    let nonce := b.getStorVal sevm.currentTarget (nonceSlot owner)
    ∃ G', d = St (afterSstore sevm (afterSload sevm b (nonceSlot owner))
      (nonceSlot owner) (nonce + 1))
      (nonce :: 32 :: 64 :: owner.toB256 ::
        (0xffffffffffffffffffffffffffffffffffffffff : B256) ::
        s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      ((M.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes) G' := by
  have ptr' := (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 17 (.inl (by decide))
  change PtrMem 128 96 ((M.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes) at ptr'
  have noGrowth := ptr'.read_self (i := 0) (sz := 64) (by decide)
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_and step
  rw [B256.and_comm, ff20_and_word, toAdr_toB256] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_keccak step
  rw [keccak_scratch] at state
  rw [show (Bytes.toB256 [0x00]).toNat = 0 from rfl,
    show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    show (Bytes.toB256 [0x20]).toNat = 32 from rfl,
    show Bytes.toB256 [0x11] = (17 : B256) from rfl, noGrowth] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sstore fork step
  cases run
  exact ⟨_, rfl⟩

private def permitStructHeadMemory (M : Mem) (owner : Adr) : Mem :=
  (M.write 160 (0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9 : B256).toBytes).write
    192 owner.toB256.toBytes

private def permitStructBodyMemory (M : Mem) (spender : Adr) (value nonce deadline : B256) : Mem :=
  (((M.write 224 spender.toB256.toBytes).write 256 value.toBytes).write
    288 nonce.toBytes).write 320 deadline.toBytes

private def permitStructMemory (M : Mem) (owner spender : Adr) (value nonce deadline : B256) : Mem :=
  let M := permitStructHeadMemory M owner
  let M := permitStructBodyMemory M spender value nonce deadline
  (M.write 128 (192 : B256).toBytes).write 64 (352 : B256).toBytes

private def permitBufferHeadLine : List Ninst :=
  [.reg (.dup 2),
   .reg .mload,
   .push [0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f, 0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10, 0x5f, 0xa2, 0xfa, 0xae, 0x01, 0x26, 0x11, 0x4a, 0x16, 0x9c, 0x64, 0x84, 0x5d, 0x61, 0x26, 0xc9] (by decide),
   .reg (.swap 2),
   .reg (.dup 1),
   .reg .add,
   .reg (.swap 2),
   .reg (.swap 0),
   .reg (.swap 2),
   .reg .mstore,
   .reg (.dup 1),
   .reg (.dup 3),
   .reg .add,
   .reg (.dup 4),
   .reg (.swap 0),
   .reg .mstore,
   .reg (.swap 3)]

private theorem permit_buffer_head_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {nonce s r v deadline value : B256} {spender owner : Adr} {S : List B256}
    (ptr : PtrMem 128 96 M)
    (run : Line.Run sevm (St b
      (nonce :: 32 :: 64 :: owner.toB256 :: (0xffffffffffffffffffffffffffffffffffffffff : B256) ::
       s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M G)
      permitBufferHeadLine d) :
    ∃ G', d = St b
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) :: 128 :: 64 :: owner.toB256 :: nonce ::
       s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      (permitStructHeadMemory M owner) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 64 :: _) (Mem.read M 64 32).2 _ at state
  rw [ptr.word, ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  simp only at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  cases run
  exact ⟨_, rfl⟩

private def permitBufferBodyLine : List Ninst :=
  [.reg (.dup 10),
   .reg .and,
   .push [0x60] (by decide),
   .reg (.dup 2),
   .reg .add,
   .reg .mstore,
   .push [0x80] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg (.dup 9),
   .reg (.swap 0),
   .reg .mstore,
   .push [0xa0] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg (.swap 3),
   .reg (.swap 0),
   .reg (.swap 3),
   .reg .mstore,
   .push [0xc0] (by decide),
   .reg (.dup 0),
   .reg (.dup 4),
   .reg .add,
   .reg (.dup 8),
   .reg (.swap 0),
   .reg .mstore]

private theorem permit_buffer_body_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {nonce s r v deadline value : B256} {spender owner : Adr} {S : List B256}
    (run : Line.Run sevm (St b
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) :: 128 :: 64 :: owner.toB256 :: nonce ::
       s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M G)
      permitBufferBodyLine d) :
    ∃ G', d = St b
      (192 :: 64 :: owner.toB256 :: 128 :: s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      (permitStructBodyMemory M spender value nonce deadline) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_and step
  have canonical : (spender.toB256 &&& (0xffffffffffffffffffffffffffffffffffffffff : B256)) = spender.toB256 := by
    change (spender.toB256 &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) = _
    rw [B256.and_comm, ff20_and_word, toAdr_toB256]
  rw [canonical] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  simp only at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  cases run
  exact ⟨_, rfl⟩

private def permitBufferTailLine : List Ninst :=
  [.reg (.dup 1),
   .reg .mload,
   .reg (.dup 0),
   .reg (.dup 5),
   .reg .sub,
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .add,
   .reg (.dup 1),
   .reg .mstore,
   .push [0xe0] (by decide),
   .reg (.swap 0),
   .reg (.swap 3),
   .reg .add,
   .reg (.swap 0),
   .reg .mstore,
   .push [0x0f] (by decide),
   .reg .sload,
   .push [0x42, 0x1e] (by decide),
   .reg (.swap 0),
   .reg (.dup 6),
   .reg (.dup 6),
   .reg (.dup 6),
   .reg (.dup 6),
   .push [0x46, 0xb5] (by decide)]

private theorem permit_buffer_tail_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v deadline value : B256} {spender owner : Adr} {S : List B256}
    (ptr : PtrMem 128 352 M) (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm (St b
      (192 :: 64 :: owner.toB256 :: 128 :: s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      M G) permitBufferTailLine d) :
    ∃ G', d = St (afterSload sevm b 15)
      (0x46b5 :: 128 :: s :: r :: v :: b.getStorVal sevm.currentTarget 15 :: 0x421e ::
       owner.toB256 :: 128 :: s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      ((M.write 128 (192 : B256).toBytes).write 64 (352 : B256).toBytes) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 64 :: _) (Mem.read M 64 32).2 _ at state
  rw [ptr.word, ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sub step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  simp only [List.set_cons_zero] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  simp only at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

private theorem permit_struct_memory_facts {M : Mem} {owner spender : Adr}
    {value nonce deadline : B256} (ptr : PtrMem 128 96 M) :
    PtrMem 352 352 (permitStructMemory M owner spender value nonce deadline) ∧
    memWord (permitStructMemory M owner spender value nonce deadline) 128 = 192 ∧
    ((permitStructMemory M owner spender value nonce deadline).read 160 192).1.keccak =
      permitV2_1StructHash owner spender value nonce deadline := by
  have p1 := (ptr.write 160
    (0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9 : B256)
    (.inr (by decide))).write 192 owner.toB256 (.inr (by decide))
  have p2 := (((p1.write 224 spender.toB256 (.inr (by decide))).write 256 value
    (.inr (by decide))).write 288 nonce (.inr (by decide))).write 320 deadline (.inr (by decide))
  have p3 := (p2.write 128 192 (.inr (by decide))).set (q := 352)
  refine ⟨p3, ?_, ?_⟩
  · unfold permitStructMemory
    rw [memWord_congr (μ := (permitStructBodyMemory (permitStructHeadMemory M owner) spender value nonce deadline).write 128 (192 : B256).toBytes)
      (fun j hj => ?_)]
    · exact (Mem.memWord_write_word _ 128 192).1
    · exact (Mem.write_agree _ 64 (352 : B256).toBytes).2 (128 + j)
        (by
          have hs : ((permitStructBodyMemory (permitStructHeadMemory M owner) spender value nonce deadline).write
            128 (192 : B256).toBytes).size = 352 := (p2.write 128 192 (.inr (by decide))).size
          rw [hs]
          omega)
        (by rw [B256.length_toBytes]; omega)
  · have image := (Mem.reads_data M).write ptr.wf 160
      (0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9 : B256).toBytes
    have wf := ptr.wf.write 160
      (0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9 : B256).toBytes
    have image := image.write wf 192 owner.toB256.toBytes
    have wf := wf.write 192 owner.toB256.toBytes
    have image := image.write wf 224 spender.toB256.toBytes
    have wf := wf.write 224 spender.toB256.toBytes
    have image := image.write wf 256 value.toBytes
    have wf := wf.write 256 value.toBytes
    have image := image.write wf 288 nonce.toBytes
    have wf := wf.write 288 nonce.toBytes
    have image := image.write wf 320 deadline.toBytes
    have wf := wf.write 320 deadline.toBytes
    have image := image.write wf 128 (192 : B256).toBytes
    have wf := wf.write 128 (192 : B256).toBytes
    have image := image.write wf 64 (352 : B256).toBytes
    unfold permitStructMemory permitStructBodyMemory permitStructHeadMemory
    rw [Mem.Reads.read image,
      Bytes.sliceD_writeAt_word_after _ 64 160 192 352 (by decide),
      Bytes.sliceD_writeAt_word_after _ 128 160 192 192 (by decide),
      Bytes.sliceD_writeAt_word_last _ 160 160 320 192 deadline rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 128 288 160 nonce rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 96 256 128 value rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 64 224 96 spender.toB256 rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 32 192 64 owner.toB256 rfl rfl,
      sliceD_word_same]
    rfl

private theorem permit_call83 {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v deadline value : B256} {spender owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_417b_c71 b
      (s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M K)
    (ptr : PtrMem 128 96 M)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    let nonce := b.getStorVal F.sevm.currentTarget (nonceSlot owner)
    let b' := afterSstore F.sevm (afterSload F.sevm b (nonceSlot owner)) (nonceSlot owner) (nonce + 1)
    let M' := (M.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes
    Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_46b5_c83
      (afterSload F.sevm b' 15)
      (128 :: s :: r :: v :: b'.getStorVal F.sevm.currentTarget 15 :: 0x421e :: owner.toB256 ::
       128 :: s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      (permitStructMemory M' owner spender value nonce deadline) (ImplV2_1.t_421e_c71 :: K)) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check success fork
  obtain ⟨updated⟩ := opened.line ImplV2_1.cert_check success fork permitNonceLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitNonceLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_nonce_line ptr fork)
  have ptr' := (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 17 (.inl (by decide))
  change PtrMem 128 96 ((M.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes) at ptr'
  obtain ⟨head⟩ := updated.line ImplV2_1.cert_check success fork permitBufferHeadLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBufferHeadLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_buffer_head_line ptr')
  obtain ⟨body⟩ := head.line ImplV2_1.cert_check success fork permitBufferBodyLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBufferBodyLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    permit_buffer_body_line
  have ptrHead := (ptr'.write 160
    (0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9 : B256)
    (.inr (by decide))).write 192 owner.toB256 (.inr (by decide))
  have ptrBody : PtrMem 128 352
      (permitStructBodyMemory (permitStructHeadMemory _ owner) spender value
        (b.getStorVal F.sevm.currentTarget (nonceSlot owner)) deadline) :=
    (((ptrHead.write 224 spender.toB256 (.inr (by decide))).write 256 value
      (.inr (by decide))).write 288 _ (.inr (by decide))).write 320 deadline (.inr (by decide))
  obtain ⟨tail⟩ := body.line ImplV2_1.cert_check success fork permitBufferTailLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitBufferTailLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_buffer_tail_line ptrBody fork)
  exact tail.call ImplV2_1.cert_check success fork rfl

private def permitTypedWords (M : Mem) (domain structHash : B256) : Mem :=
  ((M.write 384
    (0x1901000000000000000000000000000000000000000000000000000000000000 : B256).toBytes).write
    386 domain.toBytes).write 418 structHash.toBytes

private def permitTypedMemory (M : Mem) (domain structHash : B256) : Mem :=
  ((permitTypedWords M domain structHash).write 352 (66 : B256).toBytes).write 64 (450 : B256).toBytes

private def permitStructHashLine : List Ninst :=
  [.reg (.dup 0),
   .reg .mload,
   .push [0x20] (by decide),
   .reg (.dup 0),
   .reg (.dup 3),
   .reg .add,
   .reg (.swap 1),
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .keccak256]

private theorem permit_struct_hash_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v domain hash : B256} {owner : Adr} {S : List B256}
    (ptr : PtrMem 352 352 M) (length : memWord M 128 = 192)
    (hashRead : (M.read 160 192).1.keccak = hash)
    (run : Line.Run sevm (St b
      (128 :: s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S) M G)
      permitStructHashLine d) :
    ∃ G', d = St b
      (hash :: 32 :: 128 :: s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 128 :: _) (Mem.read M 128 32).2 _ at state
  rw [length, ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_keccak step
  change _ = St _ ((M.read 160 192).1.keccak :: _) (Mem.read M 160 192).2 _ at state
  rw [hashRead, ptr.read_self (by decide)] at state
  subst state
  cases run
  exact ⟨_, rfl⟩

private def permitTypedWordsLine : List Ninst :=
  [.push [0x40] (by decide),
   .reg (.dup 0),
   .reg .mload,
   .push [0x19, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
   .reg (.dup 1),
   .reg (.dup 5),
   .reg .add,
   .reg .mstore,
   .push [0x22] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg (.dup 9),
   .reg (.swap 0),
   .reg .mstore,
   .push [0x42] (by decide),
   .reg (.dup 0),
   .reg (.dup 2),
   .reg .add,
   .reg (.swap 3),
   .reg (.swap 0),
   .reg (.swap 3),
   .reg .mstore]

private theorem permit_typed_words_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v domain hash : B256} {owner : Adr} {S : List B256}
    (ptr : PtrMem 352 352 M)
    (run : Line.Run sevm (St b
      (hash :: 32 :: 128 :: s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S) M G)
      permitTypedWordsLine d) :
    ∃ G', d = St b
      (352 :: 64 :: 66 :: 32 :: 128 :: s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S)
      (permitTypedWords M domain hash) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 64 :: _) (Mem.read M 64 32).2 _ at state
  rw [ptr.word, ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  cases run
  exact ⟨_, rfl⟩

private def permitTypedLengthLine : List Ninst :=
  [.reg (.dup 1),
   .reg .mload,
   .reg (.dup 0),
   .reg (.dup 2),
   .reg .sub,
   .reg (.swap 0),
   .reg (.swap 3),
   .reg .add,
   .reg (.dup 3),
   .reg .mstore,
   .push [0x62] (by decide),
   .reg .add,
   .reg (.swap 0),
   .reg .mstore]

private theorem permit_typed_length_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v domain : B256} {owner : Adr} {S : List B256}
    (ptr : PtrMem 352 480 M)
    (run : Line.Run sevm (St b
      (352 :: 64 :: 66 :: 32 :: 128 :: s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S) M G)
      permitTypedLengthLine d) :
    ∃ G', d = St b
      (352 :: 32 :: 128 :: s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S)
      ((M.write 352 (66 : B256).toBytes).write 64 (450 : B256).toBytes) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 64 :: _) (Mem.read M 64 32).2 _ at state
  rw [ptr.word, ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sub step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  cases run
  exact ⟨_, rfl⟩

private def permitTypedHashLine : List Ninst :=
  [.reg (.dup 0),
   .reg .mload,
   .reg (.swap 1),
   .reg .add,
   .reg .keccak256,
   .push [0x00] (by decide),
   .reg (.swap 0),
   .push [0x47, 0x1c] (by decide),
   .reg (.dup 1),
   .reg (.dup 7),
   .reg (.dup 7),
   .reg (.dup 7),
   .push [0x49, 0x44] (by decide)]

private theorem permit_typed_hash_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v domain hash : B256} {owner : Adr} {S : List B256}
    (ptr : PtrMem 450 480 M) (length : memWord M 352 = 66)
    (hashRead : (M.read 384 66).1.keccak = hash)
    (run : Line.Run sevm (St b
      (352 :: 32 :: 128 :: s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S) M G)
      permitTypedHashLine d) :
    ∃ G', d = St b
      (0x4944 :: s :: r :: v :: hash :: 0x471c :: hash :: 0 :: 128 ::
       s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 352 :: _) (Mem.read M 352 32).2 _ at state
  rw [length, ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_keccak step
  change _ = St _ ((M.read 384 66).1.keccak :: _) (Mem.read M 384 66).2 _ at state
  rw [hashRead, ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

private theorem permit_typed_memory_facts {M : Mem} {domain hash : B256}
    (ptr : PtrMem 352 352 M) :
    PtrMem 352 480 (permitTypedWords M domain hash) ∧
    PtrMem 450 480 (permitTypedMemory M domain hash) ∧
    memWord (permitTypedMemory M domain hash) 352 = 66 ∧
    ((permitTypedMemory M domain hash).read 384 66).1 =
      ([0x19, 0x01] ++ domain.toBytes ++ hash.toBytes : Bytes) := by
  have p1 := ((ptr.write 384
    (0x1901000000000000000000000000000000000000000000000000000000000000 : B256)
    (.inr (by decide))).write 386 domain (.inr (by decide))).write 418 hash (.inr (by decide))
  have p2 := (p1.write 352 66 (.inr (by decide))).set (q := 450)
  refine ⟨p1, p2, ?_, ?_⟩
  · unfold permitTypedMemory
    rw [memWord_congr (μ := (permitTypedWords M domain hash).write 352 (66 : B256).toBytes)
      (fun j hj => ?_)]
    · exact (Mem.memWord_write_word _ 352 66).1
    · exact (Mem.write_agree _ 64 (450 : B256).toBytes).2 (352 + j)
        (by
          have hs : ((permitTypedWords M domain hash).write 352 (66 : B256).toBytes).size = 480 :=
            (p1.write 352 66 (.inr (by decide))).size
          rw [hs]
          omega)
        (by rw [B256.length_toBytes]; omega)
  · have image := (Mem.reads_data M).write ptr.wf 384
      (0x1901000000000000000000000000000000000000000000000000000000000000 : B256).toBytes
    have wf := ptr.wf.write 384
      (0x1901000000000000000000000000000000000000000000000000000000000000 : B256).toBytes
    have image := image.write wf 386 domain.toBytes
    have wf := wf.write 386 domain.toBytes
    have image := image.write wf 418 hash.toBytes
    have wf := wf.write 418 hash.toBytes
    have image := image.write wf 352 (66 : B256).toBytes
    have wf := wf.write 352 (66 : B256).toBytes
    have image := image.write wf 64 (450 : B256).toBytes
    unfold permitTypedMemory permitTypedWords
    rw [Mem.Reads.read image,
      Bytes.sliceD_writeAt_word_after _ 64 384 66 450 (by decide),
      Bytes.sliceD_writeAt_word_after _ 352 384 66 66 (by decide),
      Bytes.sliceD_writeAt_word_last _ 384 34 418 66 hash rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 384 2 386 34 domain rfl rfl,
      Bytes.sliceD_writeAt_inside _ _ 384 384 2 (by decide) (by rw [B256.length_toBytes]; decide)]
    rfl

private theorem permit_call89 {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v domain hash : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_46b5_c83 b
      (128 :: s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S) M K)
    (ptr : PtrMem 352 352 M) (length : memWord M 128 = 192)
    (hashRead : (M.read 160 192).1.keccak = hash)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    let digest := ([0x19, 0x01] ++ domain.toBytes ++ hash.toBytes : Bytes).keccak
    Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_4944_c89 b
      (s :: r :: v :: digest :: 0x471c :: digest :: 0 :: 128 ::
       s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S)
      (permitTypedMemory M domain hash) (ImplV2_1.t_471c_c83 :: K)) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check success fork
  obtain ⟨hashed⟩ := opened.line ImplV2_1.cert_check success fork permitStructHashLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitStructHashLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_struct_hash_line ptr length hashRead)
  obtain ⟨words⟩ := hashed.line ImplV2_1.cert_check success fork permitTypedWordsLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitTypedWordsLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_typed_words_line ptr)
  obtain ⟨ptrWords, ptrTyped, lengthTyped, bytesTyped⟩ := permit_typed_memory_facts (domain := domain) (hash := hash) ptr
  obtain ⟨sized⟩ := words.line ImplV2_1.cert_check success fork permitTypedLengthLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitTypedLengthLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_typed_length_line ptrWords)
  obtain ⟨args⟩ := sized.line ImplV2_1.cert_check success fork permitTypedHashLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitTypedHashLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_typed_hash_line ptrTyped lengthTyped (congrArg Bytes.keccak bytesTyped))
  exact args.call ImplV2_1.cert_check success fork rfl

private def permitLowSLine : List Ninst :=
  [.push [0x00] (by decide),
   .push [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x5d, 0x57, 0x6e, 0x73, 0x57, 0xa4, 0x50, 0x1d, 0xdf, 0xe9, 0x2f, 0x46, 0x68, 0x1b, 0x20, 0xa0] (by decide),
   .reg (.dup 2),
   .reg .gt,
   .reg .iszero,
   .push [0x49, 0xbf] (by decide)]

private theorem permit_lows_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v : B256} {S : List B256}
    (run : Line.Run sevm (St b (s :: r :: v :: S) M G) permitLowSLine d) :
    ∃ G', d = St b (0x49bf :: B256.eqCheck (B256.gtCheck s
        (0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0 : B256)) 0 :: 0 :: s :: r :: v :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_gt step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

private def permitV27Line : List Ninst :=
  [.reg (.dup 3),
   .push [0xff] (by decide),
   .reg .and,
   .push [0x1b] (by decide),
   .reg .eq,
   .reg .iszero,
   .reg (.dup 0),
   .reg .iszero,
   .push [0x49, 0xd7] (by decide)]

private theorem permit_v27_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v : B256} {S : List B256}
    (run : Line.Run sevm (St b (0 :: s :: r :: v :: S) M G) permitV27Line d) :
    ∃ G', d = St b (0x49d7 :: B256.eqCheck (B256.eqCheck (B256.eqCheck 27 (255 &&& v)) 0) 0 :: B256.eqCheck (B256.eqCheck 27 (255 &&& v)) 0 :: 0 :: s :: r :: v :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

private def permitV28Line : List Ninst :=
  [.reg .pop,
   .reg (.dup 3),
   .push [0xff] (by decide),
   .reg .and,
   .push [0x1c] (by decide),
   .reg .eq,
   .reg .iszero]

private theorem permit_v28_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v : B256} {S : List B256}
    {flag : B256}
    (run : Line.Run sevm (St b (flag :: 0 :: s :: r :: v :: S) M G) permitV28Line d) :
    ∃ G', d = St b ((B256.eqCheck (B256.eqCheck 28 (255 &&& v)) 0) :: 0 :: s :: r :: v :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  cases run
  exact ⟨_, rfl⟩

private theorem permit_signature_cut {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_4944_c89 b
      (s :: r :: v :: S) M K)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ flag, Nonempty (CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_49d7_c7 b
      (flag :: 0 :: s :: r :: v :: S) M K) := by
  obtain ⟨opened⟩ := cut.dest ImplV2_1.cert_check success fork
  obtain ⟨low⟩ := opened.line ImplV2_1.cert_check success fork permitLowSLine rfl
    (by intro ni member xi same; subst ni
        simp only [permitLowSLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    permit_lows_line
  obtain ⟨gas, actualState⟩ := low.state
  obtain ⟨outcome, actualRun⟩ := low.placed.sourceRun ImplV2_1.cert_check
    (low.exn_eq.trans success) (by rw [low.sevm_eq]; exact fork)
  rw [low.tree, actualState, low.sevm_eq] at actualRun
  have taken : B256.eqCheck (B256.gtCheck s
      (0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0 : B256)) 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  obtain ⟨validS⟩ := low.branchSucc ImplV2_1.cert_check success fork taken
  obtain ⟨openedV⟩ := validS.dest ImplV2_1.cert_check success fork
  obtain ⟨v27⟩ := openedV.line ImplV2_1.cert_check success fork permitV27Line rfl
    (by intro ni member xi same; subst ni
        simp only [permitV27Line, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    permit_v27_line
  by_cases takenV : B256.eqCheck (B256.eqCheck (B256.eqCheck 27 (255 &&& v)) 0) 0 ≠ 0
  · exact ⟨_, v27.toSucc ImplV2_1.cert_check success fork takenV rfl⟩
  · have zeroV := not_not.mp takenV
    rw [zeroV] at v27
    obtain ⟨otherV⟩ := v27.toZero ImplV2_1.cert_check success fork
    obtain ⟨v28⟩ := otherV.line ImplV2_1.cert_check success fork permitV28Line rfl
      (by intro ni member xi same; subst ni
          simp only [permitV28Line, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
      permit_v28_line
    exact ⟨_, ⟨v28⟩⟩

private theorem permit_recovery_cut {F : Exec.Deriv} {post b : Devm} {M : Mem}
    {s r v : B256} {S : List B256} {K : List SFunc}
    (cut : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_4944_c89 b
      (s :: r :: v :: S) M K)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ reached : CursorStateAt ImplV2_1.code ImplV2_1.cert F ImplV2_1.t_4a2d_c7 b
      (0 :: s :: r :: v :: S) M K, reached.node.pc = 0x4a2d := by
  obtain ⟨flag, ⟨before⟩⟩ := permit_signature_cut cut success fork
  obtain ⟨opened⟩ := before.dest ImplV2_1.cert_check success fork
  obtain ⟨guard⟩ := opened.line ImplV2_1.cert_check success fork
    [.reg .iszero, .push [0x4a, 0x2d] (by decide)] rfl
    (by intro ni member xi same; subst ni
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by
      intro gas d run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_push step
      cases run
      exact ⟨_, rfl⟩)
  obtain ⟨gas, actualState⟩ := guard.state
  obtain ⟨outcome, actualRun⟩ := guard.placed.sourceRun ImplV2_1.cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork)
  rw [guard.tree, actualState, guard.sevm_eq] at actualRun
  have taken : B256.eqCheck flag 0 ≠ 0 := by
    rcases rpw_branch actualRun with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
    · exact nonzero
  have decoded := guard.placed.jumpiAt_of_branch guard.tree
  obtain ⟨N, next, edge, jumped, _, stateful, placed⟩ :=
    cursor_jinst_forward ImplV2_1.cert_check guard.placed decoded
      (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact fork)
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
free pointer and four real continuations. This is a local modern-fork producer;
proxy/history entry and historical-fork delivery remain upstream obligations. -/
theorem permitV2_1_query_entry {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
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
  let b1 := afterSstore F.sevm (afterSload F.sevm b0 (nonceSlot owner)) (nonceSlot owner) (nonce + 1)
  let M1 := (M0.write 0 owner.toB256.toBytes).write 32 (17 : B256).toBytes
  have ptr1 : PtrMem 128 96 M1 :=
    (ptr0.write 0 owner.toB256 (.inl (by decide))).write 32 17 (.inl (by decide))
  obtain ⟨at83⟩ := permit_call83 before ptr0 success fork
  obtain ⟨ptrStruct, lengthStruct, hashStruct⟩ := permit_struct_memory_facts
    (owner := owner) (spender := spender) (value := Sevm.dataWord F.sevm 68)
    (nonce := nonce) (deadline := Sevm.dataWord F.sevm 100) ptr1
  generalize structMemory : permitStructMemory M1 owner spender (Sevm.dataWord F.sevm 68) nonce
    (Sevm.dataWord F.sevm 100) = Ms at at83 ptrStruct lengthStruct hashStruct
  obtain ⟨at89⟩ := permit_call89 at83 ptrStruct lengthStruct hashStruct success fork
  have ptrFinal := (permit_typed_memory_facts
    (domain := b1.getStorVal F.sevm.currentTarget 15)
    (hash := permitV2_1StructHash owner spender (Sevm.dataWord F.sevm 68) nonce
      (Sevm.dataWord F.sevm 100)) ptrStruct).2.1
  generalize typedMemory : permitTypedMemory Ms (b1.getStorVal F.sevm.currentTarget 15)
    (permitV2_1StructHash owner spender (Sevm.dataWord F.sevm 68) nonce (Sevm.dataWord F.sevm 100)) = Mt at at89 ptrFinal
  obtain ⟨reached, actualPc⟩ := permit_recovery_cut at89 success fork
  have originalStorage : Devm.getStor b0 F.sevm.currentTarget = Devm.getStor F.devm F.sevm.currentTarget := by
    unfold Devm.getStor Devm.getAcct
    rw [sameState]
  have loadedState : (afterSload F.sevm b0 (nonceSlot owner)).state = b0.state := by
    unfold afterSload
    split <;> rfl
  have loadedStorage : Devm.getStor (afterSload F.sevm b0 (nonceSlot owner)) F.sevm.currentTarget =
      Devm.getStor F.devm F.sevm.currentTarget := by
    unfold Devm.getStor Devm.getAcct
    rw [loadedState, sameState]
  have nonceEq : nonce = (Devm.getStor F.devm F.sevm.currentTarget).get (nonceSlot owner) := by
    change (Devm.getStor b0 F.sevm.currentTarget).get _ = _
    rw [originalStorage]
  have domainEq : b1.getStorVal F.sevm.currentTarget 15 = permitV2_1Domain F.sevm F.devm := by
    change (Devm.getStor b1 F.sevm.currentTarget).get 15 = _
    dsimp only [b1]
    rw [afterSstore_getStor_self, loadedStorage, nonceEq]
    rfl
  have digestEq :
      ([0x19, 0x01] ++ (b1.getStorVal F.sevm.currentTarget 15).toBytes ++
        (permitV2_1StructHash owner spender (Sevm.dataWord F.sevm 68) nonce
          (Sevm.dataWord F.sevm 100)).toBytes : Bytes).keccak = permitV2_1Digest F.sevm F.devm := by
    rw [domainEq, nonceEq]
    rfl
  obtain ⟨gas, actualState⟩ := reached.state
  have stackEq := congrArg₂ (permitV2_1RecoveryStackWith F.sevm) digestEq domainEq
  have reachedState : ∃ G, reached.node.devm = St (afterSload F.sevm b1 15)
      (permitV2_1RecoveryStack F.sevm F.devm) Mt G :=
    ⟨gas, actualState.trans (congrArg (fun S => St (afterSload F.sevm b1 15) S Mt gas) stackEq)⟩
  refine ⟨afterSload F.sevm b1 15, Mt, reached.node, reached.cursor, actualPc,
    reached.free, reached.sevm_eq, reached.exn_eq, reached.placed, reached.tree,
    reached.continuations, reachedState, ptrFinal, ?_⟩
  have outerState : (afterSload F.sevm b1 15).state = b1.state := by
    unfold afterSload
    split <;> rfl
  unfold Devm.getCode Devm.getAcct
  rw [outerState]
  change b1.getCode 1 = F.devm.getCode 1
  dsimp only [b1]
  rw [afterSstore_getCode]
  unfold Devm.getCode Devm.getAcct
  rw [loadedState, sameState]

private theorem permit_owner_return {N : Exec.Deriv} {κ : Cursor} {post : Devm}
    {adr : Adr} {digest s r v domain owner : B256} {S : List B256} {K : List SFunc}
    (placed : CursorOK ImplV2_1.code ImplV2_1.cert N κ)
    (tree : κ.f = ImplV2_1.t_471c_c83)
    (stack : N.devm.stack = adr.toB256 :: digest :: 0 :: 128 :: s :: r :: v :: domain :: 0x421e :: owner :: S)
    (continuations : κ.K.map Cont.f = ImplV2_1.t_421e_c71 :: K)
    (success : N.exn = .ok post) (fork : CoveredFork N.sevm.benvStat.fork) :
    ∃ (Q : Exec.Deriv) (next : Cursor), Exec.Deriv.ExecFreeUntil N Q ∧
      CursorOK ImplV2_1.code ImplV2_1.cert Q next ∧ next.f = ImplV2_1.t_421e_c71 ∧
      Q.devm.stack = adr.toB256 :: owner :: S ∧ owner = adr.toB256 := by
  obtain ⟨Q, next, span, sameEnv, sameExn, finalPlaced, callerTree, _, returned⟩ :=
    placed.quietReturn ImplV2_1.cert_check success fork
      (E := []) (by rfl) (by rfl) (by rw [tree]; rfl) (by rw [tree]; rfl) continuations
  rw [tree, St.self stack rfl] at returned
  obtain ⟨gas, state⟩ := permit_recovery_epilogue returned
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
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
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
