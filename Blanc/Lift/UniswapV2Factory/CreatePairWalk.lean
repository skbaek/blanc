import Blanc.Lift.UniswapV2Factory.CreatePairMemory
import Blanc.Lift.UniswapV2Factory.Check
import Blanc.Lift.HistCreate
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.WalkSteps
import Blanc.Lift.Deploy
import Blanc.Lift.CallSiteChildren

/-!
# The factory's `createPair(WETH, USDC)`, walked under Muir Glacier

Gas-exact segments (`SFunc.RunExact`) of the certified factory runtime on the recorded Pair
creation call, at the fork the mainnet schedule selects at the Pair's deployment coordinates
(Muir Glacier: flat access prices, `SLOAD` 800, `EXTCODESIZE` 700, EIP-2200 `SSTORE`):

* `createPair_dispatch`: the dispatcher and the external `createPair` wrapper, from pc `0` to the
  internal call of the body;
* `createPair_prefix`: the body from its entry to the `CREATE2` node: the identical-address and
  zero-address checks, the token sort (`token0 = USDC`, `token1 = WETH`), the `getPair` check
  (an empty slot), the creation-code copy (`CODECOPY` of 11,636 bytes) and the salt
  `keccak(USDC ‖ WETH)`;
* `createPair_window`: from the `CREATE2` result to the `initialize` `CALL`: the calldata
  `initialize(USDC, WETH)` and the `EXTCODESIZE` check of the new address;
* `createPair_return`: the wrapper's return of the pair address.

The two spawns and the storage suffix are separate modules.
-/

namespace Blanc.Lift.UniswapV2Factory

open Jaune Blanc.Lift

/-! ## Muir Glacier steps -/

section Muir

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {o : Outcome}
  {S : List B256} {M : Mem} {G : Nat}

theorem muir_rules (hfork : sevm.benvStat.fork = .muirGlacier) :
    sevm.benvStat.rules = Fork.ruleSet .muirGlacier := by
  rw [BenvStat.rules, hfork]

theorem muir_stateGas (hfork : sevm.benvStat.fork = .muirGlacier) :
    sevm.benvStat.rules.stateGas = none := by rw [muir_rules hfork]; rfl

/-- `SLOAD` at Muir Glacier: 800 gas, the value named. -/
theorem rx_sload_muir (hfork : sevm.benvStat.fork = .muirGlacier) {k' v : B256}
    (hv : b.getStorVal sevm.currentTarget k' = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St (afterSloadH sevm b k') (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + 800)) (.next (.reg .sload) f) o := by
  have hc : sloadCostH sevm b k' = 800 := by unfold sloadCostH; rw [muir_rules hfork]; rfl
  rw [← hc]
  subst hv
  exact rx_sload_selH (muir_stateGas hfork) hroom k

/-- `EXTCODESIZE` at Muir Glacier: 700 gas, no warm set, the size named. -/
theorem rx_extcodesize_muir (hfork : sevm.benvStat.fork = .muirGlacier) {x v : B256}
    (hv : (b.getCode x.toAdr).size.toB256 = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: S) M (G + 700)) (.next (.reg .extcodesize) f) o := by
  have hc : extcodesizeCostH sevm b x.toAdr = 700 := by
    unfold extcodesizeCostH; rw [muir_rules hfork]; rfl
  have hb : accountAccessH sevm b x.toAdr = b := by
    unfold accountAccessH; rw [muir_rules hfork]; rfl
  rw [← hc]
  subst hv
  have h := rx_extcodesizeH (fs := fs) (f := f) (o := o) (S := S) (M := M) (G := G) (b := b)
    (x := x) (by rw [muir_rules hfork]; rfl) hroom
  rw [hb] at h
  exact h k

/-- `SSTORE` at Muir Glacier, charged `sstoreCostH` (EIP-2200 under flat access). -/
theorem rx_sstore_muir (hfork : sevm.benvStat.fork = .muirGlacier) (hstatic : sevm.isStatic = false)
    {k' v : B256} (hsentry : gCallStipend < G + sstoreCostH sevm b k' v)
    (k : SFunc.RunExact fs sevm (St (afterSstoreH sevm b k' v) S M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: v :: S) M (G + sstoreCostH sevm b k' v))
      (.next (.reg .sstore) f) o :=
  rx_sstoreH (muir_stateGas hfork) (fun _ => hsentry) hstatic k

end Muir

/-! ## The segments -/

variable {sevm : Sevm} {o : Outcome}

/-- **The dispatcher and the `createPair` wrapper.**  From pc `0` with the recorded calldata and
no value, the factory runs to the internal call of `createPair`'s body with the two decoded token
words `[USDC, WETH]`, the wrapper's return address and the selector; when the body returns `D`, the
wrapper continues from `D` at its return tree. -/
theorem createPair_dispatch {b D : Devm} {G : Nat}
    (hvalue : sevm.value = 0) (hsize : sevm.data.length.toB256 = 0x44)
    (hword0 : Sevm.dataWord sevm 0 =
      0xc9c65396000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead908)
    (hword4 : Sevm.dataWord sevm 4 = 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2)
    (hword24 : Sevm.dataWord sevm 0x24 = 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48)
    (hshifts : sevm.benvStat.rules.op.shifts = true)
    (hbody : SFunc.RunExact cert.prog sevm (St b [(0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)] fm1 G)
      t_031a_c2 (.returned D))
    (hret : SFunc.RunExact cert.prog sevm D t_0095_c13 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 225)) t_0000_c0 o := by
  unfold t_0000_c0
  refine rx_push (w := (0x80 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 12) (M' := fm1) (by rw [St.extCost_eq fm0_size]; decide) rfl ?_
  refine rx_callvalue (Nat.le_of_ble_eq_true rfl) ?_
  rw [hvalue]
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_iszero (v := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x10 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0010_c0
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := (0x4 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_calldatasize (Nat.le_of_ble_eq_true rfl) ?_
  rw [hsize]
  refine rx_lt (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x88 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_zero ?_
  unfold t_001a_c0
  refine rx_push (w := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_calldataload (Nat.le_of_ble_eq_true rfl) ?_
  rw [show Sevm.dataWord sevm (0x0 : B256) = (0xc9c65396000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead908 : B256) from hword0]
  refine rx_push (w := (0xe0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_shr (h_shifts := hshifts) (v := (0xc9c65396 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xa2e74af6 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_gt (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x5b : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_zero ?_
  unfold t_002b_c0
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xa2e74af6 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_eq (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xfd : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branchTo_zero ?_
  unfold t_0036_c0
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xc9c65396 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_eq (v := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x132 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branchTo_succ (by decide) rfl ?_
  unfold t_0132_c13
  refine rx_dest ?_
  refine rx_push (w := (0x95 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x4 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_calldatasize (Nat.le_of_ble_eq_true rfl) ?_
  rw [hsize]
  refine rx_sub' (v := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_lt (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_iszero (v := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x148 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0148_c13
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_calldataload (Nat.le_of_ble_eq_true rfl) ?_
  rw [show Sevm.dataWord sevm (0x4 : B256) = (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256) from hword4]
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 1) (S' := [(0x4 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x24 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_calldataload (Nat.le_of_ble_eq_true rfl) ?_
  rw [show Sevm.dataWord sevm (0x24 : B256) = (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256) from hword24]
  refine rx_and (v := (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x31a : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  exact rx_callRet (g := t_031a_c2) rfl hbody hret

/-- **`createPair`'s body up to `CREATE2`.**  With the slot `getPair[USDC][WETH]` empty, the body
passes its checks, sorts the tokens, copies the Pair creation code to `[0xa0, 0xa0 + 11636)`,
hashes the salt `keccak(USDC ‖ WETH)` and reaches the `CREATE2` node with operands
`0, 0xa0, 0x2d74, salt`. -/
theorem createPair_prefix {b : Devm} {G : Nat}
    (hfork : sevm.benvStat.fork = .muirGlacier) (hcode : sevm.code = code)
    (hshifts : sevm.benvStat.rules.op.shifts = true)
    (hv1 : b.getStorVal sevm.currentTarget fk2 = 0)
    (k : SFunc.RunExact cert.prog sevm (St (afterSloadH sevm b fk2) [(0x0 : B256), (0xa0 : B256), (0x2d74 : B256), fk3, fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)] fm12 G)
      (SFunc.lineDrop 80 t_0531_c10) o) :
    SFunc.RunExact cert.prog sevm (St b [(0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)] fm1 (G + 3920))
      t_031a_c2 o := by
  unfold t_031a_c2
  refine rx_dest ?_
  refine rx_push (w := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_eq (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_iszero (v := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x3b7 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_03b7_c2
  refine rx_dest ?_
  refine rx_push (w := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 5) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_lt (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x3f4 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_zero ?_
  unfold t_03ee_c2
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 5) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x3f7 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_jump (g := t_03f7_c10) rfl ?_
  unfold t_03f7_c10
  refine rx_dest ?_
  refine rx_swap (n := 0) (S' := [(0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x0 : B256), (0x0 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 2) (S' := [(0x0 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) (S' := [(0x0 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_pop ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x47e : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_047e_c10
  refine rx_dest ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm2) (by rw [St.extCost_eq fm1_size]; decide) rfl ?_
  refine rx_push (w := (0x2 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x2 : B256), (0x20 : B256), (0x0 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm3) (by rw [St.extCost_eq fm2_size]; decide) rfl ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_keccak (c := 42) (v := fk1) (by rw [St.extCost_eq fm3_size]; decide) fm3_keccak_0 (read_covered_len fm3_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 5) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 5) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 4) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm4) (by rw [St.extCost_eq fm3_size]; decide) rfl ?_
  refine rx_swap (n := 0) (S' := [(0x40 : B256), fk1, (0x20 : B256), (0x0 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 1) (S' := [(0x20 : B256), fk1, (0x40 : B256), (0x0 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_mstore (c := 3) (M' := fm5) (by rw [St.extCost_eq fm4_size]; decide) rfl ?_
  refine rx_swap (n := 0) (S' := [(0x0 : B256), (0x40 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_keccak (c := 42) (v := fk2) (by rw [St.extCost_eq fm5_size]; decide) fm5_keccak_0 (read_covered_len fm5_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sload_muir hfork (v := (0x0 : B256)) hv1 (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_iszero (v := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x51f : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_051f_c10
  refine rx_dest ?_
  refine rx_push (w := (0x60 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x80 : B256)) (by rw [St.extCost_eq fm5_size]; decide) fm5_mload_40 (read_covered fm5_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0xa0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x531 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0xa0 : B256), (0x531 : B256), (0x80 : B256), (0x60 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_push (w := (0x86d : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  apply rx_callRet (g := t_086d_c11) rfl
  · unfold t_086d_c11
    refine rx_dest ?_
    refine rx_push (w := (0x2d74 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
    refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
    refine rx_push (w := (0x87b : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
    refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
    refine rx_codecopy (c := 2458) (M' := fm6) (by rw [St.extCost_eq fm5_size]; decide) (by rw [hcode]; exact fm6_codecopy) ?_
    refine rx_add' (v := (0x2e14 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
    refine rx_swap (n := 0) (S' := [(0x531 : B256), (0x2e14 : B256), (0x80 : B256), (0x60 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
    exact rx_ret
    -- RET cost-so-far 3635 stack [(0x2e14 : B256), (0x80 : B256), (0x60 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)] mem fm6
  unfold t_0531_c10
  refine rx_dest ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0xa0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sub' (v := (0x2d74 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm7) (by rw [St.extCost_eq fm6_size]; decide) rfl ?_
  refine rx_push (w := (0x1f : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_not (v := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x1f : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x2e33 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0x2e20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm8) (by rw [St.extCost_eq fm7_size]; decide) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) (S' := [(0x60 : B256), (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_pop ?_
  refine rx_push (w := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x2e20 : B256)) (by rw [St.extCost_eq fm8_size]; decide) fm8_mload_40 (read_covered fm8_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x2e40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x60 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_shl (h_shifts := hshifts) (v := (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48000000000000000000000000 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 12) (M' := fm9) (by rw [St.extCost_eq fm8_size]; decide) rfl ?_
  refine rx_push (w := (0x14 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x2e54 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x60 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_shl (h_shifts := hshifts) (v := (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2000000000000000000000000 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 8) (M' := fm10) (by rw [St.extCost_eq fm9_size]; decide) rfl ?_
  refine rx_push (w := (0x14 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x2e68 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 2) (S' := [(0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x2e40 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x2e68 : B256), (0x0 : B256), (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x2e20 : B256)) (by rw [St.extCost_eq fm10_size]; decide) fm10_mload_40 (read_covered fm10_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sub' (v := (0x48 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sub' (v := (0x28 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm11) (by rw [St.extCost_eq fm10_size]; decide) rfl ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0x2e20 : B256), (0x0 : B256), (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm12) (by rw [St.extCost_eq fm11_size]; decide) rfl ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x28 : B256)) (by rw [St.extCost_eq fm12_size]; decide) fm12_mload_2e20 (read_covered fm12_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x2e20 : B256), (0x28 : B256), (0x0 : B256), (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x2e40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_keccak (c := 42) (v := fk3) (by rw [St.extCost_eq fm12_size]; decide) fm12_keccak_2e40 (read_covered_len fm12_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x0 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x2d74 : B256)) (by rw [St.extCost_eq fm12_size]; decide) fm12_mload_80 (read_covered fm12_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 4) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0xa0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  exact k

/-- **From the `CREATE2` result to the `initialize` `CALL`.**  With the new address holding code of
size `0x2c1d`, the factory writes `initialize(USDC, WETH)` at `[0x2e68, 0x2eac)`, passes the
`EXTCODESIZE` check and reaches the `GAS; CALL` pair with operands
`pair, 0, 0x2e68, 0x44, 0x2e68, 0`. -/
theorem createPair_window {b : Devm} {G : Nat}
    (hfork : sevm.benvStat.fork = .muirGlacier)
    (hcodesize : (b.getCode (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256).toAdr).size.toB256 = 0x2c1d)
    (k : SFunc.RunExact cert.prog sevm (St b [(0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0x0 : B256), (0x2e68 : B256), (0x44 : B256), (0x2e68 : B256), (0x0 : B256), (0x2eac : B256), (0x485cc955 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)] fm15 G) (SFunc.lineDrop 2 t_065e_c10) o) :
    SFunc.RunExact cert.prog sevm (St b ((0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) :: [fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) fm12 (G + 883))
      (SFunc.lineDrop 81 t_0531_c10) o := by
  unfold t_0531_c10
  simp only [SFunc.lineDrop]
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x2e68 : B256)) (by rw [St.extCost_eq fm12_size]; decide) fm12_mload_40 (read_covered fm12_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x485cc95500000000000000000000000000000000000000000000000000000000 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 7) (M' := fm13) (by rw [St.extCost_eq fm12_size]; decide) rfl ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 7) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x4 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x2e6c : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm14) (by rw [St.extCost_eq fm13_size]; decide) rfl ?_
  refine rx_dup (n := 6) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x24 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x2e8c : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 8) (M' := fm15) (by rw [St.extCost_eq fm14_size]; decide) rfl ?_
  refine rx_swap (n := 1) (S' := [(0x40 : B256), (0x2e68 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_mload (c := 3) (v := (0x2e68 : B256)) (by rw [St.extCost_eq fm15_size]; decide) fm15_mload_40 (read_covered fm15_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 2) (S' := [(0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0x2e68 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0x2e68 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 7) (S' := [(0x0 : B256), (0x2e68 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0x2e68 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) (S' := [(0xffffffffffffffffffffffffffffffffffffffff : B256), (0x2e68 : B256), (0x2e68 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 7) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 1) (S' := [(0x2e68 : B256), (0x2e68 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_push (w := (0x485cc955 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 1) (S' := [(0x2e68 : B256), (0x2e68 : B256), (0x485cc955 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_push (w := (0x44 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x2eac : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 2) (S' := [(0x2e68 : B256), (0x44 : B256), (0x2e68 : B256), (0x2eac : B256), (0x485cc955 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_push (w := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 2) (S' := [(0x2e68 : B256), (0x2e68 : B256), (0x44 : B256), (0x0 : B256), (0x2eac : B256), (0x485cc955 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0x2e68 : B256), (0x44 : B256), (0x0 : B256), (0x2eac : B256), (0x485cc955 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 1) (S' := [(0x44 : B256), (0x2e68 : B256), (0x2e68 : B256), (0x0 : B256), (0x2eac : B256), (0x485cc955 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0x44 : B256), (0x2e68 : B256), (0x0 : B256), (0x2eac : B256), (0x485cc955 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0x2e68 : B256), (0x44 : B256), (0x2e68 : B256), (0x0 : B256), (0x2eac : B256), (0x485cc955 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_sub' (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x44 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 7) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_extcodesize_muir hfork (v := (0x2c1d : B256)) hcodesize (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_iszero (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_iszero (v := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x65e : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_065e_c10
  refine rx_dest ?_
  refine rx_pop ?_
  exact k

/-- **The wrapper's return.**  The returned pair word is written at the free pointer and returned
as the frame's 32-byte output. -/
theorem createPair_return {b : Devm} {G : Nat} {v : B256} :
    SFunc.RunExact cert.prog sevm (St b [(0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xc9c65396 : B256)] (fm25 v) (G + 52)) t_0095_c13
      (.halted (returnPost (St b [(0x2e68 : B256), (0x20 : B256), (0xc9c65396 : B256)] (fm26 v) G)
        (0x2e68 : B256) (0x20 : B256) [(0xc9c65396 : B256)])) := by
  unfold t_0095_c13
  refine rx_dest ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x2e68 : B256)) (by rw [St.extCost_eq (fm25_size v)]; decide) (fm25_mload_40 v) (read_covered (fm25_size v) (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0x40 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 2) (S' := [(0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), (0x40 : B256), (0x2e68 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_and (v := (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm26 v) (by rw [St.extCost_eq (fm25_size v)]; decide) rfl ?_
  refine rx_mload (c := 3) (v := (0x2e68 : B256)) (by rw [St.extCost_eq (fm26_size v)]; decide) (fm26_mload_40 v) (read_covered (fm26_size v) (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0x2e68 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0x2e68 : B256), (0x2e68 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_sub' (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0x20 : B256), (0xc9c65396 : B256)]) rfl ?_
  exact rx_return_any (S := [(0xc9c65396 : B256)]) rfl (by rw [St.extCost_eq (fm26_size v)]; decide)

/-! ## The storage suffix

After the `initialize` call returns, the body writes `getPair[USDC][WETH]` and
`getPair[WETH][USDC]`, pushes the pair onto `allPairs` (slot 3, then the slot `keccak(3) + n`),
re-reads the length and logs `PairCreated`. The worlds of the suffix are named from the world `b`
the call returned. -/

/-- The pair word merged into a mapping slot's old word: `pair | (old & ~mask)`. -/
def sfxMerge (old : B256) : B256 := (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) ||| ((0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256) &&& old)

def sfxB1 (sevm : Sevm) (b : Devm) : Devm := afterSloadH sevm b fk2
def sfxB2 (sevm : Sevm) (b : Devm) : Devm := afterSstoreH sevm (sfxB1 sevm b) fk2 (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256)
def sfxW10 (sevm : Sevm) (b : Devm) : B256 := (sfxB2 sevm b).getStorVal sevm.currentTarget fk5
def sfxB3 (sevm : Sevm) (b : Devm) : Devm := afterSloadH sevm (sfxB2 sevm b) fk5
def sfxB4 (sevm : Sevm) (b : Devm) : Devm :=
  afterSstoreH sevm (sfxB3 sevm b) fk5 (sfxMerge (sfxW10 sevm b))
def sfxN (sevm : Sevm) (b : Devm) : B256 := (sfxB4 sevm b).getStorVal sevm.currentTarget 3
def sfxB5 (sevm : Sevm) (b : Devm) : Devm := afterSloadH sevm (sfxB4 sevm b) 3
def sfxB6 (sevm : Sevm) (b : Devm) : Devm :=
  afterSstoreH sevm (sfxB5 sevm b) 3 (sfxN sevm b + 1)
def sfxSlot (sevm : Sevm) (b : Devm) : B256 := sfxN sevm b + (0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b : B256)
def sfxWAll (sevm : Sevm) (b : Devm) : B256 := (sfxB6 sevm b).getStorVal sevm.currentTarget (sfxSlot sevm b)
def sfxB7 (sevm : Sevm) (b : Devm) : Devm := afterSloadH sevm (sfxB6 sevm b) (sfxSlot sevm b)
def sfxB8 (sevm : Sevm) (b : Devm) : Devm :=
  afterSstoreH sevm (sfxB7 sevm b) (sfxSlot sevm b) (sfxMerge (sfxWAll sevm b))
def sfxNEv (sevm : Sevm) (b : Devm) : B256 := (sfxB8 sevm b).getStorVal sevm.currentTarget 3
def sfxB9 (sevm : Sevm) (b : Devm) : Devm := afterSloadH sevm (sfxB8 sevm b) 3
/-- The world after `PairCreated`. -/
def sfxB10 (sevm : Sevm) (b : Devm) : Devm :=
  (sfxB9 sevm b).addLog ⟨sevm.currentTarget, [(0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256)],
    ((fm25 (sfxNEv sevm b)).read (0x2e68 : B256).toNat (0x40 : B256).toNat).1⟩

/-- The four `SSTORE` charges of the suffix. -/
def sfxCost1 (sevm : Sevm) (b : Devm) : Nat := sstoreCostH sevm (sfxB1 sevm b) fk2 (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256)
def sfxCost2 (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCostH sevm (sfxB3 sevm b) fk5 (sfxMerge (sfxW10 sevm b))
def sfxCost3 (sevm : Sevm) (b : Devm) : Nat := sstoreCostH sevm (sfxB5 sevm b) 3 (sfxN sevm b + 1)
def sfxCost4 (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCostH sevm (sfxB7 sevm b) (sfxSlot sevm b) (sfxMerge (sfxWAll sevm b))

/-- **The storage suffix.**  From the `CALL`'s success flag over the world `b` the call returned,
with `getPair[USDC][WETH]` still empty there, the body records the pair in both directions of
`getPair`, appends it to `allPairs`, logs `PairCreated` and returns the pair word. -/
theorem createPair_suffix {b : Devm} {G : Nat}
    (hfork : sevm.benvStat.fork = .muirGlacier) (hstatic : sevm.isStatic = false)
    (hv2 : b.getStorVal sevm.currentTarget fk2 = 0) (hG : 2300 ≤ G) :
    SFunc.RunExact cert.prog sevm (St b ((1 : B256) :: [(0x2eac : B256), (0x485cc955 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) fm15
      (G + 2904 + sfxCost4 sevm b + 848 + sfxCost3 sevm b + 818 + sfxCost2 sevm b + 938 +
        sfxCost1 sevm b + 1032))
      (SFunc.lineDrop 4 t_065e_c10)
      (.returned (St (sfxB10 sevm b) [(0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xc9c65396 : B256)] (fm25 (sfxNEv sevm b)) G)) := by
  unfold t_065e_c10
  simp only [SFunc.lineDrop]
  refine rx_iszero (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_iszero (v := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x672 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0672_c10
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := (0xffffffffffffffffffffffffffffffffffffffff : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 4) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm16) (by rw [St.extCost_eq fm15_size]; decide) rfl ?_
  refine rx_push (w := (0x2 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x20 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm17) (by rw [St.extCost_eq fm16_size]; decide) rfl ?_
  refine rx_push (w := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 4) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_keccak (c := 42) (v := fk1) (by rw [St.extCost_eq fm17_size]; decide) fm17_keccak_0 (read_covered_len fm17_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 9) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 7) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 6) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm18) (by rw [St.extCost_eq fm17_size]; decide) rfl ?_
  refine rx_swap (n := 0) (S' := [fk1, (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0x2 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffffffffffffffffffff : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm19) (by rw [St.extCost_eq fm18_size]; decide) rfl ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 5) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_keccak (c := 42) (v := fk2) (by rw [St.extCost_eq fm19_size]; decide) fm19_keccak_0 (read_covered_len fm19_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sload_muir hfork (v := (0x0 : B256)) hv2 (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 7) (S' := [(0xffffffffffffffffffffffffffffffffffffffff : B256), fk2, (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0x2 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 13) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 8) (S' := [(0x0 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk2, (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0x2 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 9) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_or (v := (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk2, (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0x2 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 1) (S' := [fk2, (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0x2 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_sstore_muir hfork hstatic (by unfold gCallStipend; omega) ?_
  refine rx_swap (n := 3) (S' := [(0x2 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm20) (by rw [St.extCost_eq fm19_size]; decide) rfl ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 5) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_keccak (c := 42) (v := fk4) (by rw [St.extCost_eq fm20_size]; decide) fm20_keccak_0 (read_covered_len fm20_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 6) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 6) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm21) (by rw [St.extCost_eq fm20_size]; decide) rfl ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm22) (by rw [St.extCost_eq fm21_size]; decide) rfl ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 5) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_keccak (c := 42) (v := fk5) (by rw [St.extCost_eq fm22_size]; decide) fm22_keccak_0 (read_covered_len fm22_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sload_muir hfork (v := sfxW10 sevm b) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 8) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_and (v := ((0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256) &&& (sfxW10 sevm b))) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 5) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_or (v := ((0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) ||| ((0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256) &&& (sfxW10 sevm b)))) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [fk5, ((0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) ||| ((0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256) &&& (sfxW10 sevm b))), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_sstore_muir hfork hstatic (by unfold gCallStipend; omega) ?_
  refine rx_push (w := (0x3 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sload_muir hfork (v := sfxN sevm b) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0x1 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := ((sfxN sevm b) + (0x1 : B256))) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sstore_muir hfork hstatic (by unfold gCallStipend; omega) ?_
  refine rx_swap (n := 5) (S' := [(0x0 : B256), (0x3 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (sfxN sevm b), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x0 : B256), (0x3 : B256), (0x3 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (sfxN sevm b), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_mstore (c := 3) (M' := fm23) (by rw [St.extCost_eq fm22_size]; decide) rfl ?_
  refine rx_push (w := (0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x3 : B256), (0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (sfxN sevm b), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 5) (S' := [(sfxN sevm b), (0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0x3 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_add' (v := ((sfxN sevm b) + (0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b : B256))) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 0) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_sload_muir hfork (v := sfxWAll sevm b) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [((sfxN sevm b) + (0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b : B256)), (sfxWAll sevm b), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0x3 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 7) (S' := [(0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256), (sfxWAll sevm b), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x40 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0x3 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), ((sfxN sevm b) + (0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b : B256)), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_and (v := ((0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256) &&& (sfxWAll sevm b))) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 4) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_or (v := ((0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) ||| ((0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256) &&& (sfxWAll sevm b)))) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), ((0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) ||| ((0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256) &&& (sfxWAll sevm b))), (0x40 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0x3 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), ((sfxN sevm b) + (0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b : B256)), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 6) (S' := [((sfxN sevm b) + (0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b : B256)), ((0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) ||| ((0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : B256) &&& (sfxWAll sevm b))), (0x40 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0x3 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_sstore_muir hfork hstatic (by unfold gCallStipend; omega) ?_
  refine rx_swap (n := 2) (S' := [(0x3 : B256), (0x20 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0x40 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_sload_muir hfork (v := sfxNEv sevm b) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x2e68 : B256)) (by rw [St.extCost_eq fm23_size]; decide) fm23_mload_40 (read_covered fm23_size (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 2) (S' := [(0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (sfxNEv sevm b), (0x20 : B256), (0x2e68 : B256), (0x40 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 3) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm24) (by rw [St.extCost_eq fm23_size]; decide) rfl ?_
  refine rx_swap (n := 0) (S' := [(0x20 : B256), (sfxNEv sevm b), (0x2e68 : B256), (0x40 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 2) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_add' (v := (0x2e88 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mstore (c := 3) (M' := fm25 (sfxNEv sevm b)) (by rw [St.extCost_eq fm24_size]; decide) rfl ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_mload (c := 3) (v := (0x2e68 : B256)) (by rw [St.extCost_eq (fm25_size (sfxNEv sevm b))]; decide) (fm25_mload_40 (sfxNEv sevm b)) (read_covered (fm25_size (sfxNEv sevm b)) (by decide) (by decide)) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_push (w := (0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 2) (S' := [(0x40 : B256), (0x2e68 : B256), (0x2e68 : B256), (0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 1) (S' := [(0x2e68 : B256), (0x2e68 : B256), (0x40 : B256), (0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_dup (n := 1) rfl (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0x2e68 : B256), (0x2e68 : B256), (0x40 : B256), (0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_sub' (v := (0x0 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0x0 : B256), (0x40 : B256), (0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 1) (S' := [(0x40 : B256), (0x0 : B256), (0x2e68 : B256), (0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_add' (v := (0x40 : B256)) (by decide) (Nat.le_of_ble_eq_true rfl) ?_
  refine rx_swap (n := 0) (S' := [(0x2e68 : B256), (0x40 : B256), (0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_log3 (c := 2012) hstatic (by rw [St.extCost_eq (fm25_size (sfxNEv sevm b))]; decide) rfl (read_covered_len (fm25_size (sfxNEv sevm b)) (by decide) (by decide)) ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_swap (n := 2) (S' := [(0x95 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_swap (n := 1) (S' := [(0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x95 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xc9c65396 : B256)]) rfl ?_
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

end Blanc.Lift.UniswapV2Factory
