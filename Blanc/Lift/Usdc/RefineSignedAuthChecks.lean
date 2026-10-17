import Blanc.Lift.Usdc.ShuffleSegments
import Blanc.Lift.Usdc.RefineSignedAuthReach
import Blanc.Lift.Usdc.SignedSkip
import Blanc.Lift.InvWalkStep

/-!
# Kernel checks of the authorization selectors (U6e3)

The decisions the walks of `transferWithAuthorization` and `receiveWithAuthorization` (both
overloads: wrappers 129/138 and 125/151, bodies 20/30 and 15/43, internal 87/90 and 84/95) rest on:

* `auth_noHalt`: no callee of the four wrappers halts the frame;
* `auth_silent`, `auth_execFree`, `auth_preExec`: the before-phase sets of
  `Reach.preExec_state` (`RefineSignedAuthReach.lean`) — every path of the four wrappers reaches at
  most the library `DELEGATECALL`, with the world unchanged;
* the shuffle segments (route C, C3) the walks cross by one decision each: `abi.encodePacked(r, s,
  v)` in entries 87 and 84, and the `bytes` decoding tails of wrappers 138 and 151;
* `skip_sigRet`: crossing `_requireValidSignature` (entry 111) returns, keeping the proxy's storage
  and the library code.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc.Lift Impl

/-- The callees of the authorization selectors' bodies. -/
def authCallees : List Nat := [4, 6, 7, 11, 15, 20, 30, 43, 76, 77, 78, 79, 83, 84, 87, 90, 93, 95,
  96, 98, 99, 100, 106, 107, 110, 111, 112, 113, 117]

theorem auth_noHalt : NoHaltSet cert.prog authCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `authCallees` from a cut run `h`. -/
macro "icallA " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry auth_noHalt
      (by decide : $k ∈ authCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- The silent closures the authorization paths call before the library call. -/
def authW0 : List Nat := [4, 6, 76, 77, 78, 79, 83, 106, 107, 110, 112]

/-- The trees that may reach the library call. -/
def authW : List Nat := [11, 15, 20, 30, 43, 84, 87, 90, 95, 111, 117, 125, 129, 138, 151]

/-- What runs after the library call: exec-free. -/
def authE : List Nat := [4, 7, 83, 93, 96, 98, 99, 100, 113]

theorem auth_silent : SilentSet cert.prog authW0 = true := by decide +kernel

theorem auth_execFree : ExecFreeSet cert.prog authE = true := by decide +kernel

theorem auth_preExec :
    PreExecSet cert.prog (· == Xinst.delegatecall) authW0 authW authE = true := by
  decide +kernel

/-! ## Shuffle segments -/

theorem seg_e87_check : shuffle cert.prog cert.entries [] (.callNext 90 t_2d6f_c87) 0x4c82 1000
    0x4c3f (argFrame 9) t_4c3f_c87 = some (some [.lit (Nat.toB256 0x4b49), .unk, .arg 3, .arg 4,
      .arg 5, .arg 6, .arg 7, .arg 8, .lit (Nat.toB256 0x2d6f), .arg 0, .arg 1, .arg 2, .arg 3,
      .arg 4, .arg 5, .arg 6, .arg 7, .arg 8]) := by
  decide +kernel

/-- **Walk step over entry 87 (`transferWithAuthorization(…, v, r, s)`): `abi.encodePacked(r, s,
v)`, to the call of entry 90.** -/
theorem ric_seg_e87 {sevm : Sevm} {C : List Nat} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 x3 x4 x5 x6 x7 x8 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCut cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8
        :: R) M G) t_4c3f_c87 r) :
    ∃ b' u0 M' G', b'.state = b.state ∧
      SFunc.RunCut cert.prog sevm C (St b' (Nat.toB256 0x4b49 :: u0 :: x3 :: x4 :: x5 :: x6 :: x7
        :: x8 :: Nat.toB256 0x2d6f :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) M' G')
        (.callNext 90 t_2d6f_c87) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle (X := [x0, x1, x2, x3, x4, x5, x6, x7, x8]) fork
    (fun _ hk => absurd hk List.not_mem_nil) seg_e87_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

theorem seg_e84_check : shuffle cert.prog cert.entries [] (.callNext 95 t_2d6f_c84) 0x4cc6 1000
    0x4c83 (argFrame 9) t_4c83_c84 = some (some [.lit (Nat.toB256 0x4571), .unk, .arg 3, .arg 4,
      .arg 5, .arg 6, .arg 7, .arg 8, .lit (Nat.toB256 0x2d6f), .arg 0, .arg 1, .arg 2, .arg 3,
      .arg 4, .arg 5, .arg 6, .arg 7, .arg 8]) := by
  decide +kernel

/-- **Walk step over entry 84 (`receiveWithAuthorization(…, v, r, s)`): `abi.encodePacked(r, s,
v)`, to the call of entry 95.** -/
theorem ric_seg_e84 {sevm : Sevm} {C : List Nat} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 x3 x4 x5 x6 x7 x8 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCut cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8
        :: R) M G) t_4c83_c84 r) :
    ∃ b' u0 M' G', b'.state = b.state ∧
      SFunc.RunCut cert.prog sevm C (St b' (Nat.toB256 0x4571 :: u0 :: x3 :: x4 :: x5 :: x6 :: x7
        :: x8 :: Nat.toB256 0x2d6f :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) M' G')
        (.callNext 95 t_2d6f_c84) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle (X := [x0, x1, x2, x3, x4, x5, x6, x7, x8]) fork
    (fun _ hk => absurd hk List.not_mem_nil) seg_e84_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

theorem seg_w138_check : shuffle cert.prog cert.entries [] (.callNext 30 t_0489_c138) 0xf63 1000
    0xf01 (argFrame 4) t_0f01_c138 = some (some [.lit (Nat.toB256 0x3549), .unk]) := by
  decide +kernel

/-- **Walk step over wrapper 138 (`transferWithAuthorization(…, bytes)`): the `bytes` decoding,
to the call of the body (entry 30).** -/
theorem ric_seg_w138 {sevm : Sevm} {C : List Nat} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 x3 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCut cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: R) M G) t_0f01_c138 r) :
    ∃ b' u0 M' G', b'.state = b.state ∧
      SFunc.RunCut cert.prog sevm C (St b' (Nat.toB256 0x3549 :: u0 :: R) M' G')
        (.callNext 30 t_0489_c138) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle (X := [x0, x1, x2, x3]) fork
    (fun _ hk => absurd hk List.not_mem_nil) seg_w138_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

theorem seg_w151_check : shuffle cert.prog cert.entries [] (.callNext 43 t_0489_c151) 0xb36 1000
    0xad4 (argFrame 4) t_0ad4_c151 = some (some [.lit (Nat.toB256 0x2c16), .unk]) := by
  decide +kernel

/-- **Walk step over wrapper 151 (`receiveWithAuthorization(…, bytes)`): the `bytes` decoding,
to the call of the body (entry 43).** -/
theorem ric_seg_w151 {sevm : Sevm} {C : List Nat} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 x3 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCut cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: R) M G) t_0ad4_c151 r) :
    ∃ b' u0 M' G', b'.state = b.state ∧
      SFunc.RunCut cert.prog sevm C (St b' (Nat.toB256 0x2c16 :: u0 :: R) M' G')
        (.callNext 43 t_0489_c151) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle (X := [x0, x1, x2, x3]) fork
    (fun _ hk => absurd hk List.not_mem_nil) seg_w151_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

/-! ## Crossing `_requireValidSignature`, returning -/

/-- **Crossing `_requireValidSignature`** (entry 111): the callee returns (it cannot halt the
frame), keeping the proxy's storage and the library's code, and drops its four frame words. -/
theorem skip_sigRet {sevm : Sevm} {C : List Nat} {b : Devm}
    {dd x0 x1 x2 x3 : B256} {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {r : Seg}
    (hfork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.RunCut Impl.cert.prog sevm C (St b (dd :: x0 :: x1 :: x2 :: x3 :: S) M G)
      (.callNext 111 f) r) :
    ∃ b' M' G', Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
      b'.getCode usdcLib = Lib.code ∧ SFunc.RunCut Impl.cert.prog sevm C (St b' S M' G') f r := by
  have he : certL.entries[111]? = some ⟨0x4e88, [.unk, .unk, .unk, .ret], 0⟩ := by
    rw [certL_entries_ne (by decide)]
    rfl
  have hg : certL.prog[111]? = some Impl.t_4e88_c111 := by
    rw [certL_prog]
    rfl
  have hS : QuietDelegateSet certL.prog sigClosure = true := by
    rw [certL_prog]
    exact signed_closure_quiet
  have hgS : Impl.t_4e88_c111.quietDelegate = true ∧
      Impl.t_4e88_c111.refs.all (· ∈ sigClosure) = true := by
    have h := (List.all_eq_true.mp hS) 111 (by decide)
    rw [hg] at h
    simpa only [Bool.and_eq_true] using h
  have hcode' : b.getCode usdcLib.toB256.toAdr = Lib.code := by rw [usdcLib_word]; exact hcode
  have hframe : FrameMatches x3 [.unk, .unk, .unk, .ret]
      ((x0 :: x1 :: x2 :: x3 :: S).take 4) :=
    List.Forall₂.cons (R := AVal.Matches x3) trivial (.cons trivial (.cons trivial
      (.cons rfl .nil)))
  obtain ⟨G', D, callee, cont⟩ := ric_callR (k := 111) (g := Impl.t_4e88_c111) rfl
    (fun hh => SFunc.RunP.not_halted_entry auth_noHalt (by decide : 111 ∈ authCallees) rfl hh rfl)
    run
  rw [← certL_prog] at callee cont
  have keep := (callee.framed certL_check certL_framesSat hfork (FrameSat.enter certL_check
    certL_framesSat he hg rfl (by rw [St.stack, List.take_append_drop]) hframe)).qdKeep
    lib_quietCode implP_delegatecall lib_undelegated lib_nonempty hfork hS hgS.1 hgS.2 hcode'
  obtain ⟨Y, hY, hlen⟩ := callee.entry_stack_below id certL_check hfork he hg
    (List.take_append_drop _ _).symm hframe
  rw [St.stack] at hY
  obtain rfl : Y = [] := List.eq_nil_of_length_eq_zero hlen
  rw [certL_prog] at cont
  refine ⟨D, D.memory, D.gasLeft, keep.1, by rw [← usdcLib_word]; exact keep.2.trans hcode', ?_⟩
  rw [← St.self (d := D) (by rw [hY]; rfl) rfl]
  exact cont

end Blanc.Lift.Usdc
