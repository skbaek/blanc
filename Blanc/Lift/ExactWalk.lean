import Blanc.Lift.Exact
import Blanc.ForwardCall

/-!
# Forward construction of gas-exact synthetic runs

`SFunc.RunExact` (`Blanc/Lift/Exact.lean`) is the gas-exact run of a lifted
program; `lift_exact` turns one into a Jaune execution.  This module builds
such runs forward, one tree node at a time.

Every state is written `St b S M G`: a fixed base `b` (world, metadata) with
the machine's stack, memory and gas replaced.  Each step lemma is stated
backwards — the run of the node from `St b S M (G + c)` follows from the run of
its continuation from `St b S' M' G` — with the charge `c` a numeral, so that
applying the lemma to a goal whose gas is `g + N` solves the continuation's gas
as `g + (N - c)` by Lean's Nat-offset unification and every gas obligation
disappears into unification.
-/

namespace Blanc.Lift

open Jaune

/-- A machine state over the base `b`: stack, memory and gas replaced. -/
def St (b : Devm) (S : List B256) (M : Mem) (G : Nat) : Devm :=
  b.setMach ⟨S, M, G, b.stateGas⟩

@[simp] theorem St.stack {b : Devm} {S : List B256} {M : Mem} {G : Nat} :
    (St b S M G).stack = S := rfl
@[simp] theorem St.memory {b : Devm} {S : List B256} {M : Mem} {G : Nat} :
    (St b S M G).memory = M := rfl
@[simp] theorem St.gasLeft {b : Devm} {S : List B256} {M : Mem} {G : Nat} :
    (St b S M G).gasLeft = G := rfl
@[simp] theorem St.getStorVal {b : Devm} {S : List B256} {M : Mem} {G : Nat} {a : Adr}
    {k : B256} : (St b S M G).getStorVal a k = b.getStorVal a k := rfl
@[simp] theorem St.accessedStorageKeys {b : Devm} {S : List B256} {M : Mem} {G : Nat} :
    (St b S M G).accessedStorageKeys = b.accessedStorageKeys := rfl

/-- The expansion charge of a window over an image of known size. -/
theorem St.extCost_eq {b : Devm} {S : List B256} {M : Mem} {G n : Nat} (hn : M.size = n)
    (i sz : Nat) :
    (St b S M G).extCost [⟨i, sz⟩] =
      calculateMemoryGasCost (memExtSize n i sz) - calculateMemoryGasCost n :=
  Devm.extCost_of_size hn rfl

/-- A state whose stack and memory are given is an `St` over itself. -/
theorem St.self {d : Devm} {S : List B256} {M : Mem} (hS : d.stack = S) (hM : d.memory = M) :
    d = St d S M d.gasLeft := by
  rcases d with ⟨⟨s, m, g, sg⟩, v, w⟩
  simp only [Devm.stack, Devm.memory] at hS hM
  subst hS hM
  rfl

/-- `EXP`, evaluated forward. -/
theorem Rinst.runCore_exp_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {x y : B256} {s : List B256} (h_stk : devm.stack = x :: y :: s)
    (h_gas : gExp + gExpbyte * y.bytecount ≤ devm.gasLeft) (h_room : s.length < 1024) :
    Rinst.runCore pc devm sevm .exp =
      .ok (devm.setMach ⟨B256.bexp x y :: s, devm.memory,
        devm.gasLeft - (gExp + gExpbyte * y.bytecount), devm.stateGas⟩) := by
  show (devm.pop >>= fun p => p.2.pop >>= fun q =>
    chargeGas (gExp + gExpbyte * q.1.bytecount) q.2 >>= fun d =>
      d.push (B256.bexp p.1 q.1)) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach ⟨y :: s, devm.memory, devm.gasLeft, devm.stateGas⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stateGas_setMach]
  rw [chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stack_setMach, Devm.stateGas_setMach]
  rw [Devm.push_eq_ok (devm := devm.setMach ⟨s, devm.memory,
    devm.gasLeft - (gExp + gExpbyte * y.bytecount), devm.stateGas⟩) h_room]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stack_setMach, Devm.stateGas_setMach]

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f g : SFunc} {o : Outcome}
  {S : List B256} {M : Mem} {G : Nat}

theorem rx_dest (k : SFunc.RunExact fs sevm (St b S M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 1)) (.dest f) o :=
  .dest (Devm.burnBy_setMach_gas (devm := St b S M (G + 1)) rfl) k

theorem popBurnBy_St1 {d : B256} {c : Nat} :
    Devm.PopBurnBy [d] c (St b (d :: S) M (G + c)) (St b S M G) :=
  Devm.popBurnBy_setMach (devm := St b (d :: S) M (G + c)) rfl rfl

theorem popBurnBy_St2 {d w : B256} {c : Nat} :
    Devm.PopBurnBy [d, w] c (St b (d :: w :: S) M (G + c)) (St b S M G) :=
  { stack := rfl, memory := rfl, gasLeft := rfl,
    logs := rfl, refundCounter := rfl, output := rfl, accountsToDelete := rfl,
    returnData := rfl, error := rfl, accessedAddresses := rfl,
    accessedStorageKeys := rfl, state := rfl, createdAccounts := rfl,
    transientStorage := rfl, stateGas := rfl, accountReads := rfl,
    storageReads := rfl }

/-- A `JUMPI` that falls through. -/
theorem rx_branch_zero {d : B256} (k : SFunc.RunExact fs sevm (St b S M G) f o) :
    SFunc.RunExact fs sevm (St b (d :: 0 :: S) M (G + 10)) (.branch f g) o :=
  .zero d popBurnBy_St2 k

/-- A `JUMPI` that jumps. -/
theorem rx_branch_succ {d w : B256} (hw : w ≠ 0)
    (k : SFunc.RunExact fs sevm (St b S M G) g o) :
    SFunc.RunExact fs sevm (St b (d :: w :: S) M (G + 10)) (.branch f g) o :=
  .succ d w hw popBurnBy_St2 k

theorem rx_branchTo_zero {d : B256} {j : Nat} (k : SFunc.RunExact fs sevm (St b S M G) f o) :
    SFunc.RunExact fs sevm (St b (d :: 0 :: S) M (G + 10)) (.branchTo f j) o :=
  .toZero d popBurnBy_St2 k

theorem rx_branchTo_succ {d w : B256} {j : Nat} (hw : w ≠ 0) (hj : fs[j]? = some g)
    (k : SFunc.RunExact fs sevm (St b S M G) g o) :
    SFunc.RunExact fs sevm (St b (d :: w :: S) M (G + 10)) (.branchTo f j) o :=
  .toSucc d w hw hj popBurnBy_St2 k

/-- A callee's `JUMP` back to its return address. -/
theorem rx_ret {d : B256} :
    SFunc.RunExact fs sevm (St b (d :: S) M (G + 8)) .ret (.returned (St b S M G)) :=
  .ret d popBurnBy_St1

/-- An internal call that returns. -/
theorem rx_callRet {d : B256} {j : Nat} {D : Devm} (hj : fs[j]? = some g)
    (hcall : SFunc.RunExact fs sevm (St b S M G) g (.returned D))
    (k : SFunc.RunExact fs sevm D f o) :
    SFunc.RunExact fs sevm (St b (d :: S) M (G + 8)) (.callNext j f) o :=
  .callRet d hj popBurnBy_St1 hcall k

theorem rx_push {x : UInt8} {xs : Bytes} {le : (x :: xs).length ≤ 32} {w : B256}
    (hw : Bytes.toB256 (x :: xs) = w) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (w :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 3)) (.next (.push (x :: xs) le) f) o := by
  subst hw
  exact .next (Ninst.runCompiled_pushBytes (devm := St b S M (G + 3)) (c := gVerylow)
    (G := G) rfl rfl hroom) k

theorem rx_binary {r : Rinst} {fn : B256 → B256 → B256} {c : Nat} {x y v : B256}
    (hne : r ≠ .pc) (hdef : ∀ d : Devm, Rinst.runCore 0 d sevm r = applyBinary fn c d)
    (hv : fn x y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + c)) (.next (.reg r) f) o :=
  .next (Ninst.runCompiled_binary (devm := St b (x :: y :: S) M (G + c)) (G := G) hne
    (hdef _) rfl hv rfl hroom) k

theorem rx_unary {r : Rinst} {fn : B256 → B256} {c : Nat} {x v : B256}
    (hne : r ≠ .pc) (hdef : ∀ d : Devm, Rinst.runCore 0 d sevm r = applyUnary fn c d)
    (hv : fn x = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: S) M (G + c)) (.next (.reg r) f) o :=
  .next (Ninst.runCompiled_unary (devm := St b (x :: S) M (G + c)) (G := G) hne
    (hdef _) rfl hv rfl hroom) k

theorem rx_add {x y : B256} (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b ((x + y) :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .add) f) o :=
  rx_binary (fn := (· + ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl hroom k

theorem rx_sub {x y : B256} (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b ((x - y) :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .sub) f) o :=
  rx_binary (fn := (· - ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl hroom k

theorem rx_and {x y v : B256} (hv : (x &&& y) = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .and) f) o :=
  rx_binary (fn := B256.and) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rx_eq {x y v : B256} (hv : B256.eqCheck x y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .eq) f) o :=
  rx_binary (fn := B256.eqCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rx_lt {x y v : B256} (hv : B256.ltCheck x y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .lt) f) o :=
  rx_binary (fn := B256.ltCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rx_div {x y v : B256} (hv : x / y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 5)) (.next (.reg .div) f) o :=
  rx_binary (fn := (· / ·)) (c := gLow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rx_iszero {x v : B256} (hv : B256.eqCheck x 0 = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: S) M (G + 3)) (.next (.reg .iszero) f) o :=
  rx_unary (fn := (B256.eqCheck · 0)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rx_callvalue (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (sevm.value :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .callvalue) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

theorem rx_calldatasize (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (sevm.data.length.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .calldatasize) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

theorem rx_calldataload {x : B256} (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (Sevm.dataWord sevm x :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: S) M (G + 3)) (.next (.reg .calldataload) f) o :=
  .next (Ninst.runCompiled_calldataload (devm := St b (x :: S) M (G + 3)) (G := G) rfl rfl rfl
    hroom) k

theorem rx_dup {n : Fin 16} {w : B256} (hget : S[n.val]? = some w) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (w :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 3)) (.next (.reg (.dup n)) f) o :=
  .next (Ninst.runCompiled_dup (devm := St b S M (G + 3)) (G := G) hget rfl hroom) k

theorem rx_swap {n : Fin 16} {S' : List B256} (hsw : Jaune.List.swap S n.val = some S')
    (k : SFunc.RunExact fs sevm (St b S' M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 3)) (.next (.reg (.swap n)) f) o :=
  .next (Ninst.runCompiled_swap (devm := St b S M (G + 3)) (G := G) hsw rfl) k

theorem rx_dup1 {x : B256} (hroom : (x :: S).length < 1024)
    (k : SFunc.RunExact fs sevm (St b (x :: x :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: S) M (G + 3)) (.next (.reg (.dup 0)) f) o :=
  rx_dup (n := 0) rfl hroom k

theorem rx_dup2 {x y : B256} (hroom : (x :: y :: S).length < 1024)
    (k : SFunc.RunExact fs sevm (St b (y :: x :: y :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg (.dup 1)) f) o :=
  rx_dup (n := 1) rfl hroom k

theorem rx_dup3 {x y z : B256} (hroom : (x :: y :: z :: S).length < 1024)
    (k : SFunc.RunExact fs sevm (St b (z :: x :: y :: z :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: z :: S) M (G + 3)) (.next (.reg (.dup 2)) f) o :=
  rx_dup (n := 2) rfl hroom k

theorem rx_swap1 {x y : B256}
    (k : SFunc.RunExact fs sevm (St b (y :: x :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg (.swap 0)) f) o :=
  rx_swap (n := 0) rfl k

theorem rx_swap2 {x y z : B256}
    (k : SFunc.RunExact fs sevm (St b (z :: y :: x :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: z :: S) M (G + 3)) (.next (.reg (.swap 1)) f) o :=
  rx_swap (n := 1) rfl k

theorem rx_pop {x : B256}
    (k : SFunc.RunExact fs sevm (St b S M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: S) M (G + 2)) (.next (.reg .pop) f) o :=
  .next (Ninst.runCompiled_pop (devm := St b (x :: S) M (G + 2)) (G := G) rfl rfl) k

theorem rx_exp {x y : B256} (hy : y.bytecount = 0) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (B256.bexp x y :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 10)) (.next (.reg .exp) f) o := by
  refine .next ?_ k
  have h := Ninst.runCompiled_reg (sevm := sevm) (r := .exp) (by rintro ⟨⟩)
    (Rinst.runCore_exp_eq_ok (devm := St b (x :: y :: S) M (G + 10)) rfl
      (by simp [hy, gExp]) hroom)
  simpa [hy, gExp, St, Devm.setMach_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using h

theorem rx_sload_cold {k' : B256} (hlegacy : sevm.benvStat.rules.stateGas = none)
    (hcold : (⟨sevm.currentTarget, k'⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St (addAccessedStorageKey b sevm.currentTarget k')
        (b.getStorVal sevm.currentTarget k' :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + 2100)) (.next (.reg .sload) f) o :=
  .next (Ninst.runCompiled_sload_cold (devm := St b (k' :: S) M (G + 2100)) (G := G)
    hlegacy rfl hcold rfl rfl hroom) k

theorem rx_sload_warm {k' : B256} (hlegacy : sevm.benvStat.rules.stateGas = none)
    (hwarm : (⟨sevm.currentTarget, k'⟩ : Adr × B256) ∈ b.accessedStorageKeys)
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (b.getStorVal sevm.currentTarget k' :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + 100)) (.next (.reg .sload) f) o :=
  .next (Ninst.runCompiled_sload_warm (devm := St b (k' :: S) M (G + 100)) (G := G)
    hlegacy rfl hwarm rfl rfl hroom) k

/-- `MSTORE`, with the whole charge `c = 3 + expansion` named. -/
theorem rx_mstore {i v : B256} {c : Nat} {M' : Mem}
    (hc : gVerylow + (St b (i :: v :: S) M (G + c)).extCost [⟨i.toNat, 32⟩] = c)
    (hw : M.write i.toNat v.toBytes = M')
    (k : SFunc.RunExact fs sevm (St b S M' G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + c)) (.next (.reg .mstore) f) o :=
  .next (Ninst.runCompiled_mstore (devm := St b (i :: v :: S) M (G + c)) (G := G) rfl
    (by rw [hc]; rfl) hw) k

/-- `MLOAD` of a window the image covers. -/
theorem rx_mload {i v : B256} {c : Nat}
    (hc : gVerylow + (St b (i :: S) M (G + c)).extCost [⟨i.toNat, 32⟩] = c)
    (hv : Bytes.toB256 (M.read i.toNat 32).1 = v) (hM : (M.read i.toNat 32).2 = M)
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: S) M (G + c)) (.next (.reg .mload) f) o :=
  .next (Ninst.runCompiled_mload_of (devm := St b (i :: S) M (G + c)) (G := G) rfl hc hv hM
    rfl hroom) k

/-- `KECCAK256` of a window the image covers. -/
theorem rx_keccak {i sz v : B256} {c : Nat}
    (hc : gKeccak256 + gasKeccak256Word * ceilDiv sz.toNat 32
      + (St b (i :: sz :: S) M (G + c)).extCost [⟨i.toNat, sz.toNat⟩] = c)
    (hv : Bytes.keccak (M.read i.toNat sz.toNat).1 = v) (hM : (M.read i.toNat sz.toNat).2 = M)
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: S) M (G + c)) (.next (.reg .keccak256) f) o :=
  .next (Ninst.runCompiled_keccak256_of (devm := St b (i :: sz :: S) M (G + c)) (G := G) rfl hc
    hv hM rfl hroom) k

/-- `RETURN` of a window the image covers, at no expansion charge. -/
theorem rx_return {i sz : B256} {out : Bytes}
    (hext : (St b (i :: sz :: S) M G).extCost [⟨i.toNat, sz.toNat⟩] = 0)
    (hout : (M.read i.toNat sz.toNat).1 = out) :
    SFunc.RunExact fs sevm (St b (i :: sz :: S) M G) (.last .return_)
      (.halted (((St b S M G).memRead i.toNat sz.toNat).2.withOutput out)) := by
  refine .last ?_
  show Linst.run sevm _ .return_ = _
  exact Linst.run_return_eq_ok (out := out) rfl (by rw [hext]; exact Nat.zero_le _)
    (by rw [hext, Nat.sub_zero]; exact Prod.ext hout rfl)

end Steps

end Blanc.Lift
