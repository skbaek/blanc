import Blanc.Lift.ExactWalkCut
import Blanc.ForwardSha256
import Blanc.ForwardStorageAccess

/-!
# More walk steps for exact runs and exact cut runs

Companions to `Blanc/Lift/ExactWalk.lean`, `ExactWalkOps.lean` and
`ExactWalkCut.lean` for what a solc `sha256(abi.encodePacked(…))` site and a
storage read of a state-dependent key need:

* `SLOAD` with the warm/cold choice left to the neutral carriers `sloadCost`
  and `afterSload` (`Blanc/ForwardCall.lean`), so one lemma covers both;
* `GAS`, `RETURNDATASIZE`, an `MLOAD` that extends memory;
* the `STATICCALL` of the SHA-256 precompile over a 64-byte window
  (`Ninst.runCompiled_staticcall_sha256_64_warm`), whose successor's world
  is only known through `ShaCallPost`;
* for exact cut runs (`SFunc.RunExactCut`), the same steps and the named-value
  binary operations, plus the goto `rxc_jump` into an entry outside the cut.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## Word arithmetic on small pointers -/

theorem toB256_add_toB256 {a b : Nat} (h : a + b < 2 ^ 256) :
    Nat.toB256 a + Nat.toB256 b = Nat.toB256 (a + b) := by
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt (by omega),
    B256.toNat_toB256_of_lt h, Nat.lo_eq_of_lt h]

theorem toB256_sub_toB256 {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 256) :
    Nat.toB256 a - Nat.toB256 b = Nat.toB256 (a - b) := by
  apply B256.toNat_inj
  rw [B256.toNat_sub_eq_of_le _ _ (by
      rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt (by omega),
        B256.toNat_toB256_of_lt ha]; exact hb),
    B256.toNat_toB256_of_lt ha, B256.toNat_toB256_of_lt (show b < 2 ^ 256 by omega),
    B256.toNat_toB256_of_lt (show a - b < 2 ^ 256 by omega)]

/-! ## What the SHA-256 precompile call leaves -/

/-- The world after a successful precompile call, relative to the one before:
storage, code, access sets, logs, output and error unchanged, and the return
data set to `rd`. -/
structure ShaCallPost (b b' : Devm) (rd : Bytes) : Prop where
  stor : ∀ a, Devm.getStor b' a = Devm.getStor b a
  code : ∀ a, b'.getCode a = b.getCode a
  addrs : b'.accessedAddresses = b.accessedAddresses
  keys : b'.accessedStorageKeys = b.accessedStorageKeys
  logs : b'.logs = b.logs
  output : b'.output = b.output
  error : b'.error = b.error
  returnData : b'.returnData = rd

theorem ShaCallPost.getStorVal {b b' : Devm} {rd : Bytes} (h : ShaCallPost b b' rd) (a : Adr)
    (k : B256) : b'.getStorVal a k = b.getStorVal a k := by
  show (Devm.getStor b' a).get k = (Devm.getStor b a).get k
  rw [h.stor]

/-- The successor of `Ninst.runCompiled_staticcall_sha256_64_warm` from `St b …`, as an `St`
over a base that satisfies `ShaCallPost`. -/
theorem staticcall_sha_step {sevm : Sevm} {b : Devm} {iiw oiw : B256} {S : List B256}
    {M : Mem} {G : Nat}
    (hcov : memExtsSize M.size [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = M.size)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hbound : G + 184 < 2 ^ 256) (hroom : S.length < 1024) (hG : 1 ≤ G) :
    ∃ b', ShaCallPost b b' (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes ∧
      Ninst.RunCompiled sevm
        (St b (Nat.toB256 (G + 184) :: 2 :: iiw :: 64 :: oiw :: 32 :: S) M (G + 184))
        (.exec .staticcall)
        (St b' (1 :: S) (M.write oiw.toNat (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes) G) := by
  obtain ⟨post, hrun, hstack, hmem, hgas, hrd, hstor, hcode, haddr, hkeys, hlogs, hout, herr,
      -⟩ :=
    Ninst.runCompiled_staticcall_sha256_64_warm (sevm := sevm)
      (devm := St b (Nat.toB256 (G + 184) :: 2 :: iiw :: 64 :: oiw :: 32 :: S) M (G + 184))
      (G := G + 184) (s := S) rfl rfl hcov hnodeleg hwarm hpre hfork hdepth (by omega) hbound
      hroom
  refine ⟨post, ⟨hstor, hcode, haddr, hkeys, hlogs, hout, herr, hrd⟩, ?_⟩
  have hG' : G + 184 - 184 = G := by omega
  rw [hG'] at hgas
  have := St.self (d := post) hstack hmem
  rw [hgas] at this
  rw [show St post (1 :: S) (M.write oiw.toNat (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes) G
    = post from this.symm]
  exact hrun

/-! ## Exact-run steps -/

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f g : SFunc} {o : Outcome}
  {S : List B256} {M : Mem} {G : Nat}

/-- `SLOAD` of any key, warm or cold. -/
theorem rx_sload_sel {k' : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St (afterSload sevm b k') (b.getStorVal sevm.currentTarget k' :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + sloadCost sevm b k'))
      (.next (.reg .sload) f) o := by
  refine .next ?_ k
  have h := Ninst.runCompiled_sload_selected (sevm := sevm) (base := b) (key := k') (stack := S)
    (memory := M) (G := G) hfork rfl hroom
  simpa [St, afterSload_stateGas] using h

theorem rx_gas (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (Nat.toB256 G :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .gas) f) o :=
  .next (Ninst.runCompiled_gas (devm := St b S M (G + 2)) rfl hroom) k

theorem rx_returndatasize (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (b.returnData.length.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .returndatasize) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

/-- `MLOAD` whose window may extend memory to `M'`. -/
theorem rx_mload_ext {i v : B256} {c : Nat} {M' : Mem}
    (hc : gVerylow + (St b (i :: S) M (G + c)).extCost [⟨i.toNat, 32⟩] = c)
    (hv : Bytes.toB256 (M.read i.toNat 32).1 = v) (hM : (M.read i.toNat 32).2 = M')
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M' G) f o) :
    SFunc.RunExact fs sevm (St b (i :: S) M (G + c)) (.next (.reg .mload) f) o :=
  .next (Ninst.runCompiled_mload_of (devm := St b (i :: S) M (G + c)) (G := G) rfl hc hv hM
    rfl hroom) k

/-- The SHA-256 precompile `STATICCALL` after solc's `GAS`, over covered windows. -/
theorem rx_staticcall_sha {iiw oiw : B256}
    (hcov : memExtsSize M.size [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = M.size)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hbound : G + 184 < 2 ^ 256) (hroom : S.length < 1024) (hG : 1 ≤ G)
    (k : ∀ b', ShaCallPost b b' (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes →
      SFunc.RunExact fs sevm
        (St b' (1 :: S) (M.write oiw.toNat (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes) G) f o) :
    SFunc.RunExact fs sevm
      (St b (Nat.toB256 (G + 184) :: 2 :: iiw :: 64 :: oiw :: 32 :: S) M (G + 184))
      (.next (.exec .staticcall) f) o := by
  obtain ⟨b', hpost, hrun⟩ := staticcall_sha_step hcov hnodeleg hwarm hpre hfork hdepth hbound
    hroom hG
  exact .next hrun (k b' hpost)

end Steps

/-! ## Exact cut-run steps -/

section CutSteps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f g : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

/-- A `JUMP` to an entry outside the cut list, taken as a goto. -/
theorem rxc_jump {d : B256} {j : Nat} (hj : fs[j]? = some g) (hjC : j ∉ C)
    (k : SFunc.RunExactCut fs sevm C (St b S M G) g r) :
    SFunc.RunExactCut fs sevm C (St b (d :: S) M (G + 8)) (.jump j) r :=
  .jump d hjC hj popBurnBy_St1 k

theorem rxc_add' {x y v : B256} (hv : x + y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 3)) (.next (.reg .add) f) r :=
  rxc_binary (fn := (· + ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_sub' {x y v : B256} (hv : x - y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 3)) (.next (.reg .sub) f) r :=
  rxc_binary (fn := (· - ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_and {x y v : B256} (hv : (x &&& y) = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 3)) (.next (.reg .and) f) r :=
  rxc_binary (fn := B256.and) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_or {x y v : B256} (hv : (x ||| y) = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 3)) (.next (.reg .or) f) r :=
  rxc_binary (fn := B256.or) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_eq {x y v : B256} (hv : B256.eqCheck x y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 3)) (.next (.reg .eq) f) r :=
  rxc_binary (fn := B256.eqCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_div {x y v : B256} (hv : x / y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 5)) (.next (.reg .div) f) r :=
  rxc_binary (fn := (· / ·)) (c := gLow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_not {x v : B256} (hv : (~~~ x) = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: S) M (G + 3)) (.next (.reg .not) f) r :=
  rxc_unary (fn := (~~~ ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_exp' {x y : B256} {c : Nat} (hc : gExp + gExpbyte * y.bytecount = c)
    (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (B256.bexp x y :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + c)) (.next (.reg .exp) f) r := by
  subst hc
  refine .next ?_ k
  have h := Ninst.runCompiled_reg (sevm := sevm) (r := .exp) (by rintro ⟨⟩)
    (Rinst.runCore_exp_eq_ok (devm := St b (x :: y :: S) M (G + (gExp + gExpbyte * y.bytecount)))
      rfl (by simp) hroom)
  simpa [St, Devm.setMach_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using h

theorem rxc_sload_sel {k' : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C
      (St (afterSload sevm b k') (b.getStorVal sevm.currentTarget k' :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (k' :: S) M (G + sloadCost sevm b k'))
      (.next (.reg .sload) f) r := by
  refine .next ?_ k
  have h := Ninst.runCompiled_sload_selected (sevm := sevm) (base := b) (key := k') (stack := S)
    (memory := M) (G := G) hfork rfl hroom
  simpa [St, afterSload_stateGas] using h

theorem rxc_gas (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (Nat.toB256 G :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 2)) (.next (.reg .gas) f) r :=
  .next (Ninst.runCompiled_gas (devm := St b S M (G + 2)) rfl hroom) k

theorem rxc_returndatasize (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (b.returnData.length.toB256 :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 2)) (.next (.reg .returndatasize) f) r :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

theorem rxc_mload_ext {i v : B256} {c : Nat} {M' : Mem}
    (hc : gVerylow + (St b (i :: S) M (G + c)).extCost [⟨i.toNat, 32⟩] = c)
    (hv : Bytes.toB256 (M.read i.toNat 32).1 = v) (hM : (M.read i.toNat 32).2 = M')
    (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M' G) f r) :
    SFunc.RunExactCut fs sevm C (St b (i :: S) M (G + c)) (.next (.reg .mload) f) r :=
  .next (Ninst.runCompiled_mload_of (devm := St b (i :: S) M (G + c)) (G := G) rfl hc hv hM
    rfl hroom) k

theorem rxc_staticcall_sha {iiw oiw : B256}
    (hcov : memExtsSize M.size [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = M.size)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hbound : G + 184 < 2 ^ 256) (hroom : S.length < 1024) (hG : 1 ≤ G)
    (k : ∀ b', ShaCallPost b b' (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes →
      SFunc.RunExactCut fs sevm C
        (St b' (1 :: S) (M.write oiw.toNat (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes) G) f r) :
    SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 (G + 184) :: 2 :: iiw :: 64 :: oiw :: 32 :: S) M (G + 184))
      (.next (.exec .staticcall) f) r := by
  obtain ⟨b', hpost, hrun⟩ := staticcall_sha_step hcov hnodeleg hwarm hpre hfork hdepth hbound
    hroom hG
  exact .next hrun (k b' hpost)

end CutSteps

end Blanc.Lift
