import Blanc.Lift.Curve3Pool.Walk.AdminBalances

/-!
# Safety: `donate_admin_fees()`, inverted

Body `t_4f60_c0` (selector test at 0x4f52): non-payable and owner guards, then
`for i in range(3): self.balances[i] = ERC20(self.coins[i]).balanceOf(self)`. The certificate
peels the loop into entry 0 (`t_4f84_c0`), entry 38 (`t_4f84_c38`) and entry 63 (`t_4f84_c63`),
each with the counter word at `0x140` known; the index checks against `3` are `.undefined` on
their failing arm. One iteration (`donateIter`, `ric_donateIter`) and the loop tail
(`donateTail`, `ric_donateTail`) are inverted once and applied to the three copies (the tree
equalities are definitional).

`safe_donateAdminFees` gives the three answers (static child messages to `coins[k]` with
`balanceOf(self)` calldata, at least 32 bytes) and the model step under `donEnv`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-- One iteration of `donate_admin_fees`' loop (`for i in range(3)`): `balanceOf(self)` of
`coins[i]` (`i` the counter word at `0x140`) into `balances[i]`, then `tail`. -/
def donateIter (f1 f2 tail : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.push [0x01, 0xe0] (by decide)) (.next (.push [0x24] (by decide)) (.next (.push [0x70, 0xa0, 0x82, 0x31] (by decide)) (.next (.push [0x01, 0x60] (by decide)) (.next (.reg .mstore) (.next (.reg .address) (.next (.push [0x01, 0x80] (by decide)) (.next (.reg .mstore) (.next (.push [0x01, 0x7c] (by decide)) (.next (.push [0x01, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x4f, 0xad] (by decide)) (.branch .undefined
  (.dest (.next (.push [0x00] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .keccak256) (.next (.reg .add) (.next (.reg .sload) (.next (.reg .gas) (.next (.exec .staticcall) (.next (.push [0x4f, 0xc4] (by decide)) (.branch f1
  (.dest (.next (.push [0x1f] (by decide)) (.next (.reg .returndatasize) (.next (.reg .gt) (.next (.push [0x4f, 0xd1] (by decide)) (.branch f2
  (.dest (.next (.push [0x00] (by decide)) (.next (.reg .pop) (.next (.push [0x01, 0xe0] (by decide)) (.next (.reg .mload) (.next (.push [0x01, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x4f, 0xe9] (by decide)) (.branch .undefined
  (.dest (.next (.push [0x01] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .keccak256) (.next (.reg .add) (.next (.reg .sstore) tail)))))))))
  ))))))))))))
  ))))))
  )))))))))))))
  ))))))))))))))))))

example : t_4f84_c0 = donateIter t_4fc0_c0 t_4fcd_c0 t_4ff6_c0 := rfl
example : t_4f84_c38 = donateIter t_4fc0_c38 t_4fcd_c38 t_4ff6_c38 := rfl
example : t_4f84_c63 = donateIter t_4fc0_c63 t_4fcd_c63 t_4ff6_c63 := rfl

/-- The `balanceOf(self)` call data staged at `p` (selector word) and `p + 32` (self), read
from `p + 28`. -/
theorem balanceOf_window' {M : Mem} (hwf : Mem.Wf M) (self : Adr) (z : B256) {p : Nat}
    (hp : 224 ≤ p + 28) :
    (((((M.write p (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes).write (p + 32)
      self.toB256.toBytes).write 192 z.toBytes).extend 192 32).read (p + 28) 36).1 =
      balanceOfData self := by
  have w1 := hwf.write p (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
  have w2 := w1.write (p + 32) self.toB256.toBytes
  rw [Mem.extend_read_fst, ((((Mem.reads_data M).write hwf p _).write w1 (p + 32) _).write w2 192
    _).read, show (36 : Nat) = 4 + 32 from rfl, List.sliceD_split]
  generalize hA : (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes = A
  have lA : A.length = 32 := by rw [← hA, B256.length_toBytes]
  have lB : self.toB256.toBytes.length = 32 := B256.length_toBytes _
  have lZ : z.toBytes.length = 32 := B256.length_toBytes _
  rw [Bytes.sliceD_writeAt_after _ z.toBytes (p + 28) 4 192 (by rw [lZ]; omega),
    Bytes.sliceD_writeAt_after _ z.toBytes (p + 28 + 4) 32 192 (by rw [lZ]; omega),
    Bytes.sliceD_writeAt_before _ _ (p + 28) 4 (p + 32) (by omega),
    show p + 28 + 4 = p + 32 by omega, ← lB, Bytes.sliceD_writeAt,
    Bytes.sliceD_writeAt_inside _ _ p (p + 28) 4 (by omega) (by rw [lA]),
    show p + 28 - p = 28 by omega, ← hA]
  rfl

section
variable {sevm : Sevm}

/-- **One loop iteration of `donate_admin_fees`, inverted.** -/
theorem ric_donateIter {C : List Nat} {r : Seg} {B : Devm} {S : List B256} {M : Mem} {G i : Nat}
    {f1 f2 tail : SFunc} (hfork : CoveredFork sevm.benvStat.fork) (hf1 : f1.noOk = true)
    (hf2 : f2.noOk = true) (hwf : Mem.Wf M) (hi : i < 3)
    (hctr : (M.read 320 32).1 = (Nat.toB256 i).toBytes)
    (run : SFunc.RunCut cert.prog sevm C (St B S M G) (donateIter f1 f2 tail) r) :
    ∃ out d1 M' G', 32 ≤ out.length ∧
      StaticAnswered sevm B (B.getStorVal sevm.currentTarget (coinsBase + Nat.toB256 i)).toAdr
        (balanceOfData sevm.currentTarget) out ∧
      QStep sevm B d1 (B.getStor sevm.currentTarget) ∧ Mem.Wf M' ∧
      (M'.read 320 32).1 = (Nat.toB256 i).toBytes ∧
      SFunc.RunCut cert.prog sevm C (St (afterSstore sevm d1 (balancesBase + Nat.toB256 i)
        (Bytes.toB256 (out.take 32))) S M' G') tail r := by
  unfold donateIter at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_mstore s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_address s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_mstore s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_mload s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_lt s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s2
  rcases ric_branch run with ⟨-, G18, run⟩ | ⟨-, G18, run⟩
  · exact (ric_undefined run).elim
  obtain ⟨G19, run⟩ := ric_dest run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_mstore s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_keccak s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_add s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_sload hfork s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨gw, G28, rfl⟩ := ri_gas s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨flag, out, hpost, hlenb, hans⟩ := ri_staticcall_bounded hfork s2
  rw [hpost.eq_St] at run
  obtain ⟨hfl, G29, run⟩ := ric_assertJump hf1 run
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_push s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_returndatasize s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_gt s3
  obtain ⟨hrds, G33, run⟩ := ric_assertJump hf2 run
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_push s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_pop s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_mload s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_push s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_mload s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_push s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G41, rfl⟩ := ri_dup rfl s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_lt s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_push s3
  rcases ric_branch run with ⟨-, G44, run⟩ | ⟨-, G44, run⟩
  · exact (ric_undefined run).elim
  obtain ⟨G45, run⟩ := ric_dest run
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G46, rfl⟩ := ri_push s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G47, rfl⟩ := ri_push s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G48, rfl⟩ := ri_mstore s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G49, rfl⟩ := ri_push s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G50, rfl⟩ := ri_push s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G51, rfl⟩ := ri_keccak s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G52, rfl⟩ := ri_add s3
  obtain ⟨d3, s3, run⟩ := ric_next run; obtain ⟨G53, rfl⟩ := ri_sstore hfork s3
  clear s2 s3
  clear * - hctr hwf hi hpost hlenb hans hfl hrds run hfork
  simp only [show (Bytes.toB256 [1, 64]).toNat = 320 from by decide,
    show (Bytes.toB256 [1, 96]).toNat = 352 from by decide,
    show (Bytes.toB256 [1, 128]).toNat = 384 from by decide,
    show (Bytes.toB256 [192]).toNat = 192 from by decide,
    show (Bytes.toB256 [32]).toNat = 32 from by decide,
    show (Bytes.toB256 [1, 124]).toNat = 380 from by decide,
    show (Bytes.toB256 [36]).toNat = 36 from by decide,
    show (Bytes.toB256 [1, 224]).toNat = 480 from by decide,
    show Bytes.toB256 [0] = 0 from by decide, show Bytes.toB256 [1] = 1 from by decide]
    at hpost hans run
  rw [show (36 : Nat) = 4 + 32 from rfl] at hans
  simp (disch := first | mem_wf | omega) only [Mem.read_snd_eq, Mem.extend_read_fst,
    Mem.extends_read_fst, Mem.read_write_word_disjoint, Mem.read_write_word_of_wf,
    Mem.read_split, Mem.read_write_word_inside, hctr, B256.toB256_toBytes, coinsBase_eq,
    balancesBase_eq] at hpost hans run
  rw [hpost.returnData] at hrds
  have h32 : 32 ≤ out.length := by
    have h := hrds
    unfold B256.gtCheck at h
    split at h
    · rename_i hgt
      have := B256.lt_iff_toNat_lt_toNat.mp hgt
      rw [Jaune.B256.toNat_toB256_of_lt hlenb] at this
      have c : (Bytes.toB256 [31]).toNat = 31 := by decide
      omega
    · exact absurd rfl h
  have ht : (out.take 32).length = 32 := by rw [List.length_take]; omega
  have hsel : (Bytes.toB256 [112, 160, 130, 49]).toBytes.sliceD (380 - 352) 4 0 = balanceOfSel := by
    decide
  simp (disch := first | mem_wf | omega) only [Mem.read_write_len _ 480 ht,
    Mem.read_write_disjoint, Mem.read_snd_eq, Mem.extend_read_fst, Mem.extends_read_fst,
    Mem.read_write_word_disjoint, hctr, B256.toB256_toBytes, Jaune.toB256_toNat] at run
  rw [hsel] at hans
  have hf1 : flag = 1 := hpost.flag.resolve_left hfl
  refine ⟨out, d2, _, _, h32, StaticAnswered.of_afterSload (hans hf1),
    ⟨by rw [hpost.stor, afterSload_getStor], fun a _ => by rw [hpost.stor, afterSload_getStor],
      by rw [hpost.logs, afterSload_logs], by rw [hpost.output hf1, afterSload_output]⟩,
    ?_, ?_, run⟩
  · mem_wf
  · simp (disch := first | mem_wf | omega) only [Mem.extend_read_fst, Mem.extends_read_fst,
      Mem.read_write_word_disjoint, Mem.read_write_disjoint, hctr]

/-- The loop tail of `donate_admin_fees`: increment the counter word at `0x140`, test it
against `3`, then `X` (the back edge or the exit). -/
def donateTail (X : SFunc) : SFunc :=
  .dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide))
    (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore)
      (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero)
        (.next (.push [0x4f, 0x84] (by decide)) X)))))))))))

example : t_4ff6_c0 = donateTail (.branchTo .undefined 38) := rfl
example : t_4ff6_c38 = donateTail (.branchTo .undefined 63) := rfl
example : t_4ff6_c63 = donateTail (.branch t_5006_c63 .undefined) := rfl

/-- **The loop tail, inverted**: the counter word becomes `i + 1`. -/
theorem ric_donateTail {C : List Nat} {r : Seg} {B : Devm} {M : Mem} {G i : Nat} {X : SFunc}
    (hwf : Mem.Wf M) (hctr : (M.read 320 32).1 = (Nat.toB256 i).toBytes)
    (run : SFunc.RunCut cert.prog sevm C
      (St B [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) (donateTail X) r) :
    ∃ dd w M' G', Mem.Wf M' ∧
      (M'.read 320 32).1 = (Bytes.toB256 [0x01] + Nat.toB256 i).toBytes ∧
      SFunc.RunCut cert.prog sevm C
        (St B [dd, w, Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') X r := by
  unfold donateTail at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_mload s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_add s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_mstore s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_eq s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s2
  have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  rw [h320, hctr, B256.toB256_toBytes] at run
  clear * - run hwf
  rw [Mem.read_snd_eq] at run
  refine ⟨_, _, _, _, ?_, ?_, run⟩
  · mem_wf
  · rw [Mem.read_write_word_of_wf (by mem_wf)]

end

/-- Three numbers as a function of the coin index. -/
def fn3 (a b c : Nat) : Fin 3 → Nat := fun k => if k.val = 0 then a else if k.val = 1 then b else c

/-- The environment of `donate_admin_fees`: coin `k`'s `balanceOf(self)` answered with `w k`. -/
def donEnv (sevm : Sevm) (w : Fin 3 → Nat) : Env :=
  { quietEnv sevm with coin := fun k => ⟨some (w k), none, false, false⟩ }

theorem donate_step {sevm : Sevm} {s : State} (w : Fin 3 → Nat) (hv : sevm.value = 0)
    (hown : (quietEnv sevm).caller = s.owner) :
    step s (donEnv sevm w) .donateAdminFees =
      some ⟨{ s with balances := ⟨w 0, w 1, w 2⟩ }, none, [], []⟩ := by
  have hv' : (quietEnv sevm).value = 0 := by
    show sevm.value.toNat = 0
    rw [hv]; rfl
  simp only [step, body, donateAdminFees, donEnv, hv', hown, req, ite_true, V3.ofFnM, bind,
    Option.bind]

section
variable {sevm : Sevm} {b : Devm} {s : State}
local notation "stor₀" => Devm.getStor b sevm.currentTarget

-- SEGMENT: safeDonateAdminFees
theorem safe_donateAdminFees (hfork : CoveredFork sevm.benvStat.fork)
    (hc : Checkpoint stor₀ s) (hsel : Sevm.selector sevm = selDonateAdminFees)
    (hlen : 4 ≤ sevm.data.length) :
    ∀ G post, SFunc.Run cert.prog sevm (quietSt sevm b G) t_4f60_c0 (.halted post) →
      ∃ out0 out1 out2 : Bytes, 32 ≤ out0.length ∧ 32 ≤ out1.length ∧ 32 ≤ out2.length ∧
        (∃ B, StaticAnswered sevm B ((stor₀).get (coinSlot 0)).toAdr
          (balanceOfData sevm.currentTarget) out0) ∧
        (∃ B, StaticAnswered sevm B ((stor₀).get (coinSlot 1)).toAdr
          (balanceOfData sevm.currentTarget) out1) ∧
        (∃ B, StaticAnswered sevm B ((stor₀).get (coinSlot 2)).toAdr
          (balanceOfData sevm.currentTarget) out2) ∧
        ∃ o, step s (donEnv sevm (fn3 (answerWord out0) (answerWord out1) (answerWord out2)))
          (decodeCall sevm) = some o ∧ QuietLands sevm b post o := by
  intro G post run
  have hdec : decodeCall sevm = .donateAdminFees := decodeCall_at (k := 21) rfl hsel hlen
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (fail := t_4f66_c0) rfl run
  obtain ⟨hown, G2, run⟩ := ric_ownerGuard hfork rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_add s1
  clear s1
  have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  have h03 : Bytes.toB256 [0x03] + Bytes.toB256 [0x00] = Bytes.toB256 [0x03] := by decide
  rw [h320, h03] at run
  have hctr0 : (((vyMem Mem.empty (Sevm.dataWord sevm 0)).write 320
      (Bytes.toB256 [0x00]).toBytes).read 320 32).1 = (Nat.toB256 0).toBytes := by
    rw [Mem.read_write_word_of_wf hwf0]; rfl
  obtain ⟨out0, e1, M1, G10, h0, hans0, hq0, hwf1, hctr1, run⟩ :=
    ric_donateIter (f1 := t_4fc0_c0) (f2 := t_4fcd_c0) (tail := t_4ff6_c0) hfork rfl rfl
      (hwf0.write _ _) (by decide) hctr0 run
  obtain ⟨dd, w, M2, G11, hwf2, hctr2, run⟩ :=
    ric_donateTail (X := .branchTo .undefined 38) hwf1 hctr1 run
  rcases ric_branchTo (k := 38) (List.not_mem_nil) rfl run with ⟨-, G12, run⟩ | ⟨-, G12, run⟩
  · exact (ric_undefined run).elim
  rw [show Bytes.toB256 [0x01] + Nat.toB256 0 = Nat.toB256 1 from by decide] at hctr2
  obtain ⟨out1, e2, M3, G13, h1, hans1, hq1, hwf3, hctr3, run⟩ :=
    ric_donateIter (f1 := t_4fc0_c38) (f2 := t_4fcd_c38) (tail := t_4ff6_c38) hfork rfl rfl
      hwf2 (by decide) hctr2 run
  obtain ⟨dd, w, M4, G14, hwf4, hctr4, run⟩ :=
    ric_donateTail (X := .branchTo .undefined 63) hwf3 hctr3 run
  rcases ric_branchTo (k := 63) (List.not_mem_nil) rfl run with ⟨-, G15, run⟩ | ⟨-, G15, run⟩
  · exact (ric_undefined run).elim
  rw [show Bytes.toB256 [0x01] + Nat.toB256 1 = Nat.toB256 2 from by decide] at hctr4
  obtain ⟨out2, e3, M5, G16, h2, hans2, hq2, hwf5, hctr5, run⟩ :=
    ric_donateIter (f1 := t_4fc0_c63) (f2 := t_4fcd_c63) (tail := t_4ff6_c63) hfork rfl rfl
      hwf4 (by decide) hctr4 run
  obtain ⟨dd, w, M6, G17, -, -, run⟩ :=
    ric_donateTail (X := .branch t_5006_c63 .undefined) hwf5 hctr5 run
  rcases ric_branch run with ⟨-, G18, run⟩ | ⟨-, G18, run⟩
  swap
  · exact (ric_undefined run).elim
  unfold t_5006_c63 at run
  obtain ⟨G19, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_pop s1
  cases run with
  | last hl =>
  cases hl
  clear * - hc hdec hv hown h0 h1 h2 hans0 hans1 hans2 hq0 hq1 hq2
  have hqA : QStep sevm b (afterSload sevm b ownerSlot) (stor₀) :=
    (QStep.refl sevm b).sload ownerSlot
  have hqB := (hqA.chain hq0).sstore (balancesBase + Nat.toB256 0) (Bytes.toB256 (List.take 32 out0))
  have hqC := (hqB.chain hq1).sstore (balancesBase + Nat.toB256 1) (Bytes.toB256 (List.take 32 out1))
  have hqD := (hqC.chain hq2).sstore (balancesBase + Nat.toB256 2) (Bytes.toB256 (List.take 32 out2))
  have ec0 : (afterSload sevm b ownerSlot).getStorVal sevm.currentTarget
      (coinsBase + Nat.toB256 0) = (stor₀).get (coinSlot 0) := by
    rw [hqA.getStorVal]; rfl
  have ec1 : (afterSstore sevm e1 (balancesBase + Nat.toB256 0)
      (Bytes.toB256 (List.take 32 out0))).getStorVal sevm.currentTarget
      (coinsBase + Nat.toB256 1) = (stor₀).get (coinSlot 1) := by
    rw [hqB.getStorVal, Stor.get_set_ne _ (by decide)]; rfl
  have ec2 : (afterSstore sevm e2 (balancesBase + Nat.toB256 1)
      (Bytes.toB256 (List.take 32 out1))).getStorVal sevm.currentTarget
      (coinsBase + Nat.toB256 2) = (stor₀).get (coinSlot 2) := by
    rw [hqC.getStorVal, Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide)]; rfl
  rw [ec0] at hans0
  rw [ec1] at hans1
  rw [ec2] at hans2
  refine ⟨out0, out1, out2, h0, h1, h2, ⟨_, hans0⟩, ⟨_, hans1⟩, ⟨_, hans2⟩, _,
    by rw [hdec]; exact donate_step _ hv (quietEnv_owner hc hown), ?_⟩
  refine quietLands_stop hqD ⟨fun x hx => ?_, fun f hf => ?_⟩ rfl rfl rfl
  · rw [hdec] at hx
    simp only [footprint, balFlds, List.mem_cons, forall_eq_or_imp, Fld.slot, balanceSlot,
      Fin.val_zero, Fin.val_one, Fin.val_two] at hx
    obtain ⟨k0, k1, k2, -⟩ := hx
    rw [Stor.get_set_ne _ k2, Stor.get_set_ne _ k1, Stor.get_set_ne _ k0]
  · rw [hdec] at hf
    simp only [footprint, balFlds, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;>
      simp (disch := decide) only [Fld.Reads, balanceSlot, Fin.val_zero, Fin.val_one,
        Fin.val_two, Stor.get_set_ne, Stor.get_set_self] <;> rfl

end

end Blanc.Lift.Curve3Pool
