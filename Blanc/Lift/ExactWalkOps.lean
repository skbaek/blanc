import Blanc.Lift.ExactWalk

/-!
# More forward walk steps for gas-exact lifted runs

Companions to `Blanc/Lift/ExactWalk.lean` for the instructions a solc 0.6
runtime uses beyond WETH9's: the shifts, `BYTE`, `NOT`, `GT`, `MSTORE8`,
`CALLDATACOPY`, `LOG1`, `EXP` with a nonzero exponent, and the `JUMP` goto.  Every
lemma has the same backwards shape as its siblings there: the run of the node
from `St b S M (G + c)` follows from the run of its continuation from
`St b S' M' G`.
-/

namespace Blanc.Lift

open Jaune

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f g : SFunc} {o : Outcome}
  {S : List B256} {M : Mem} {G : Nat}

theorem rx_shl {x y v : B256} (hv : y <<< x.toNat = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .shl) f) o :=
  rx_binary (fn := fun x y => y <<< x.toNat) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv
    hroom k

theorem rx_shr {x y v : B256} (hv : y >>> x.toNat = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .shr) f) o :=
  rx_binary (fn := fun x y => y >>> x.toNat) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv
    hroom k

theorem rx_byte {x y v : B256} (hv : (List.getD y.toBytes x.toNat 0).toB256 = v)
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .byte) f) o :=
  rx_binary (fn := fun x y => (List.getD y.toBytes x.toNat 0).toB256) (c := gVerylow)
    (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

/-- `ADD` with the sum named (to keep a walk's stack in normal form). -/
theorem rx_add' {x y v : B256} (hv : x + y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .add) f) o :=
  rx_binary (fn := (· + ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

/-- `SUB` with the difference named. -/
theorem rx_sub' {x y v : B256} (hv : x - y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .sub) f) o :=
  rx_binary (fn := (· - ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rx_gt {x y v : B256} (hv : B256.gtCheck x y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .gt) f) o :=
  rx_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rx_or {x y v : B256} (hv : (x ||| y) = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .or) f) o :=
  rx_binary (fn := B256.or) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rx_xor {x y v : B256} (hv : (x ^^^ y) = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .xor) f) o :=
  rx_binary (fn := B256.xor) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rx_mul {x y v : B256} (hv : x * y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 5)) (.next (.reg .mul) f) o :=
  rx_binary (fn := (· * ·)) (c := gLow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rx_not {x v : B256} (hv : (~~~ x) = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: S) M (G + 3)) (.next (.reg .not) f) o :=
  rx_unary (fn := (~~~ ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

/-- A `JUMP` to entry `j`, taken as a goto. -/
theorem rx_jump {d : B256} {j : Nat} (hj : fs[j]? = some g)
    (k : SFunc.RunExact fs sevm (St b S M G) g o) :
    SFunc.RunExact fs sevm (St b (d :: S) M (G + 8)) (.jump j) o :=
  .jump d hj popBurnBy_St1 k

/-- `MSTORE8`, with the whole charge `c = 3 + expansion` named. -/
theorem rx_mstore8 {i v : B256} {c : Nat} {M' : Mem}
    (hc : gVerylow + (St b (i :: v :: S) M (G + c)).extCost [⟨i.toNat, 1⟩] = c)
    (hw : M.write i.toNat [v.2.2.toUInt8] = M')
    (k : SFunc.RunExact fs sevm (St b S M' G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + c)) (.next (.reg .mstore8) f) o :=
  .next (Ninst.runCompiled_mstore8 (devm := St b (i :: v :: S) M (G + c)) (G := G) rfl
    (by rw [hc]; rfl) hw) k

/-- `CALLDATACOPY`, with the whole charge named. -/
theorem rx_calldatacopy {di si sz : B256} {c : Nat} {M' : Mem}
    (hc : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + (St b (di :: si :: sz :: S) M (G + c)).extCost [⟨di.toNat, sz.toNat⟩] = c)
    (hw : M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0) = M')
    (k : SFunc.RunExact fs sevm (St b S M' G) f o) :
    SFunc.RunExact fs sevm (St b (di :: si :: sz :: S) M (G + c))
      (.next (.reg .calldatacopy) f) o :=
  .next (Ninst.runCompiled_calldatacopy_of (devm := St b (di :: si :: sz :: S) M (G + c))
    (G := G) rfl hc hw rfl) k

/-- `LOG1`, with the whole charge named: the entry appended to the base carries the executing
address, the topic and the bytes of the window; memory is the window read's image. -/
theorem rx_log1 {i sz t : B256} {c : Nat} {data : Bytes}
    (hstatic : sevm.isStatic = false)
    (hc : gLog + gLogdata * sz.toNat + gLogtopic * 1 +
      (St b (i :: sz :: t :: S) M (G + c)).extCost [⟨i.toNat, sz.toNat⟩] = c)
    (hd : (M.read i.toNat sz.toNat).1 = data) (hM : (M.read i.toNat sz.toNat).2 = M)
    (k : SFunc.RunExact fs sevm (St (b.addLog ⟨sevm.currentTarget, [t], data⟩) S M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: t :: S) M (G + c)) (.next (.reg (.log 1)) f) o :=
  .next (Ninst.runCompiled_log_of (n := 1) (topics := [t]) (s := S) rfl rfl hstatic hc hd hM
    rfl) k

/-- `EXP` with its exponent's byte charge named. -/
theorem rx_exp' {x y : B256} {c : Nat} (hc : gExp + gExpbyte * y.bytecount = c)
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (B256.bexp x y :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + c)) (.next (.reg .exp) f) o := by
  subst hc
  refine .next ?_ k
  have h := Ninst.runCompiled_reg (sevm := sevm) (r := .exp) (by rintro ⟨⟩)
    (Rinst.runCore_exp_eq_ok (devm := St b (x :: y :: S) M (G + (gExp + gExpbyte * y.bytecount)))
      rfl (by simp only [St.gasLeft, le_add_iff_nonneg_left, zero_le]) hroom)
  simpa only [St, Devm.memory_setMach, Devm.setMach_gasLeft, add_tsub_cancel_right,
    Devm.stateGas_setMach, Devm.setMach_setMach] using h

theorem rx_dup4 {x y z w : B256} (hroom : (x :: y :: z :: w :: S).length < 1024)
    (k : SFunc.RunExact fs sevm (St b (w :: x :: y :: z :: w :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: z :: w :: S) M (G + 3)) (.next (.reg (.dup 3)) f) o :=
  rx_dup (n := 3) rfl hroom k

theorem rx_swap3 {x y z w : B256}
    (k : SFunc.RunExact fs sevm (St b (w :: y :: z :: x :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: z :: w :: S) M (G + 3)) (.next (.reg (.swap 2)) f) o :=
  rx_swap (n := 2) rfl k

end Steps

end Blanc.Lift
