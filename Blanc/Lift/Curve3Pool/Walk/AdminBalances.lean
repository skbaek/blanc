import Blanc.Lift.Curve3Pool.Walk.Quiet
import Blanc.Lift.StaticCall

/-!
# Safety: `admin_balances(i)`, inverted

Body `t_4c93_c0` (selector test at 0x4c85). The body stages `balanceOf(self)` at `0x15c`
(`mstore(0x140, 0x70a08231); mstore(0x160, self)`), checks `i < 3`, loads `coins[i]` at
`keccak(0) + i`, `STATICCALL`s it with the output window `0x1c0`, asserts the call flag and
`RETURNDATASIZE > 31`, re-checks `i < 3`, loads `balances[i]` at `keccak(1) + i`, asserts the
answer covers it and returns the difference.

`safe_adminBalances` states the frame's one observation directly at the step: the answer `out`
of a successful static child message to `coins[i]` with calldata `balanceOfData self`
(`StaticAnswered`, `Blanc/Lift/StaticCall.lean`), at least 32 bytes long, and the model's step
under `balEnv` (coin `i`'s `balPre` its first word, every other answer absent). Tying that answer
to the frame's committed child (`EnvOf`'s `ReplyAt`) is the frame-level bridge, not a walk fact.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

section AB
variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- `ADDRESS`, inverted. -/
theorem ri_address {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg .address) d) :
    ∃ G', d = St b (sevm.currentTarget.toB256 :: S) M G' := by
  have hp := of_run_address h
  have hs : d.stack = sevm.currentTarget.toB256 :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

end AB

/-- The environment of a frame whose only external call is coin `k`'s `balanceOf(self)`,
answered with the word `w`. -/
def balEnv (sevm : Sevm) (k : Fin 3) (w : Nat) : Env :=
  { quietEnv sevm with
    coin := fun j => if j = k then ⟨some w, none, false, false⟩ else ⟨none, none, false, false⟩ }

/-- A selected `SLOAD` keeps the world state. -/
theorem afterSload_state' {sevm : Sevm} {b : Devm} {k : B256} :
    (afterSload sevm b k).state = b.state := by
  unfold afterSload; split <;> rfl

/-- A static answer over a load's base is one over the base. -/
theorem StaticAnswered.of_afterSload {sevm : Sevm} {b : Devm} {k : B256} {t : Adr}
    {input out : Bytes} (h : StaticAnswered sevm (afterSload sevm b k) t input out) :
    StaticAnswered sevm b t input out := by
  have hc : ∀ a, (afterSload sevm b k).getCode a = b.getCode a := fun a => by
    simp only [Devm.getCode, Devm.getAcct, afterSload_state']
  unfold StaticAnswered at h ⊢
  simp only [hc, afterSload_state'] at h
  exact h

/-- A write of `k` bytes reads back. -/
theorem Mem.read_write_len {M : Mem} (hwf : Mem.Wf M) (n : Nat) {xs : Bytes} {k : Nat}
    (h : xs.length = k) : ((M.write n xs).read n k).1 = xs := by
  rw [((Mem.reads_data M).write hwf n xs).read, ← h, Bytes.sliceD_writeAt]

/-- The `balanceOf(self)` call data staged by `mstore(0x140, 0x70a08231); mstore(0x160, self)`
and read from `0x15c`. -/
theorem balanceOf_window {M : Mem} (hwf : Mem.Wf M) (self : Adr) (z : B256) :
    (((((M.write 320 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes).write 352
      self.toB256.toBytes).write 192 z.toBytes).extend 192 32).read 348 36).1 =
      balanceOfData self := by
  have w1 := hwf.write 320 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
  have w2 := w1.write 352 self.toB256.toBytes
  rw [Mem.extend_read_fst, ((((Mem.reads_data M).write hwf 320 _).write w1 352 _).write w2 192
    _).read, show (36 : Nat) = 4 + 32 from rfl, List.sliceD_split]
  generalize hA : (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes = A
  have lA : A.length = 32 := by rw [← hA, B256.length_toBytes]
  have lB : self.toB256.toBytes.length = 32 := B256.length_toBytes _
  have lZ : z.toBytes.length = 32 := B256.length_toBytes _
  rw [Bytes.sliceD_writeAt_after _ z.toBytes 348 4 192 (by rw [lZ]; norm_num),
    Bytes.sliceD_writeAt_after _ z.toBytes (348 + 4) 32 192 (by rw [lZ]; norm_num),
    Bytes.sliceD_writeAt_before _ _ 348 4 352 (by norm_num), show 348 + 4 = 352 from rfl,
    ← lB, Bytes.sliceD_writeAt,
    Bytes.sliceD_writeAt_inside _ _ 320 348 4 (by norm_num) (by rw [lA]), ← hA]
  rfl

/-- The model's `admin_balances(i)` under the frame's one answer. -/
theorem adminBalances_step {sevm : Sevm} {s : State} (hv : sevm.value = 0) (k : Fin 3)
    (hk : arg sevm 0 = k.val) (w : Nat) (hle : s.balances.get k ≤ w) :
    step s (balEnv sevm k w) (.adminBalances (arg sevm 0)) =
      some (viewOut s (w - s.balances.get k)) := by
  have hv' : (balEnv sevm k w).value = 0 := by
    show sevm.value.toNat = 0
    rw [hv]; rfl
  have hidx : idx (arg sevm 0) = some k := by
    rw [hk, idx, dif_pos k.isLt]
  have hv'' : (quietEnv sevm).value = 0 := hv'
  simp only [step, body, hv', ite_true, hidx, adminBalances, balEnv, ite_true, chkSub, hle,
    bind, Option.bind, hv'']

section
variable {sevm : Sevm} {b : Devm} {s : State}
local notation "stor₀" => Devm.getStor b sevm.currentTarget

-- SEGMENT: safeAdminBalances
theorem safe_adminBalances (hfork : CoveredFork sevm.benvStat.fork)
    (hc : Checkpoint stor₀ s) (hsel : Sevm.selector sevm = selAdminBalances)
    (hlen : 4 ≤ sevm.data.length) :
    ∀ G post, SFunc.Run cert.prog sevm (quietSt sevm b G) t_4c93_c0 (.halted post) →
      ∃ (k : Fin 3) (out : Bytes), (Sevm.argWord sevm 0).toNat = k.val ∧
        StaticAnswered sevm b ((stor₀).get (coinSlot k)).toAdr
          (balanceOfData sevm.currentTarget) out ∧ 32 ≤ out.length ∧
        ∃ o, step s (balEnv sevm k (answerWord out)) (decodeCall sevm) = some o ∧
          QuietLands sevm b post o := by
  intro G post run
  have hdec : decodeCall sevm = .adminBalances (arg sevm 0) :=
    decodeCall_at (k := 19) rfl hsel hlen
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (fail := t_4c99_c0) rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_address s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_lt s1
  obtain ⟨hi, G17, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_keccak s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨gw, G26, rfl⟩ := ri_gas s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨flag, out, hpost, hlenb, hans⟩ := ri_staticcall_bounded hfork s1
  rw [hpost.eq_St] at run
  obtain ⟨hfl, G27, run⟩ := ric_assertJump rfl run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_returndatasize s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_gt s2
  obtain ⟨hrds, G31, run⟩ := ric_assertJump rfl run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_mload s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_calldataload s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_lt s2
  obtain ⟨-, G41, run⟩ := ric_assertJump rfl run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_mstore s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G45, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G46, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G47, rfl⟩ := ri_keccak s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G48, rfl⟩ := ri_add s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G49, rfl⟩ := ri_sload hfork s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G50, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G51, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G52, rfl⟩ := ri_lt s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G53, rfl⟩ := ri_iszero s2
  obtain ⟨hge, G54, run⟩ := ric_assertJump rfl run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G55, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G56, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G57, rfl⟩ := ri_sub s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G58, rfl⟩ := ri_swap rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G59, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G60, rfl⟩ := ri_swap rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G61, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G62, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G63, rfl⟩ := ri_mstore s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G64, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G65, rfl⟩ := ri_push s2
  cases run with
  | last hl =>
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
  clear * - hout hstor hlogs hi hfl hrds hge hpost hans hv hdec hc hwf0 hfork hlenb
  generalize vyMem Mem.empty (Sevm.dataWord sevm 0) = M0 at hwf0 hout hstor hlogs hge hpost hans
  have ha0 : Sevm.dataWord sevm (Bytes.toB256 [4]) = Sevm.argWord sevm 0 := rfl
  simp only [show (Bytes.toB256 [1, 64]).toNat = 320 from by decide,
    show (Bytes.toB256 [1, 96]).toNat = 352 from by decide,
    show (Bytes.toB256 [192]).toNat = 192 from by decide,
    show (Bytes.toB256 [32]).toNat = 32 from by decide,
    show (Bytes.toB256 [1, 92]).toNat = 348 from by decide,
    show (Bytes.toB256 [36]).toNat = 36 from by decide,
    show (Bytes.toB256 [1, 192]).toNat = 448 from by decide,
    show (Bytes.toB256 [0]).toNat = 0 from by decide,
    show Bytes.toB256 [0] = 0 from by decide, show Bytes.toB256 [1] = 1 from by decide,
    ha0] at hi hout hstor hlogs hge hpost hans
  have hiN : (Sevm.argWord sevm 0).toNat < 3 := by
    have h := hi
    unfold B256.ltCheck at h
    split at h
    · rename_i hlt
      exact (B256.lt_iff_toNat_lt_toNat.mp hlt).trans_eq (by decide)
    · exact absurd rfl h
  have hk : Nat.toB256 (Sevm.argWord sevm 0).toNat = Sevm.argWord sevm 0 := Jaune.toB256_toNat _
  have hf1 : flag = 1 := hpost.flag.resolve_left hfl
  have hwfA := (hwf0.write 320 (Bytes.toB256 [112, 160, 130, 49]).toBytes).write 352
    sevm.currentTarget.toB256.toBytes
  simp only [Mem.read_write_word_of_wf hwfA, coinsBase_eq, B256.toNat_zero] at hans hpost hge hout hstor hlogs
  simp only [Mem.read_snd_eq] at hans hpost hge hout hstor hlogs
  rw [balanceOf_window hwf0] at hans
  simp (disch := mem_wf) only [Mem.read_write_word_of_wf, balancesBase_eq] at hge hout hstor hlogs
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
  simp (disch := mem_wf) only [Mem.read_write_len _ 448 ht] at hge hout
  have hq : QStep sevm b d1 (b.getStor sevm.currentTarget) :=
    ⟨by rw [hpost.stor, afterSload_getStor], fun a _ => by rw [hpost.stor, afterSload_getStor],
      by rw [hpost.logs, afterSload_logs], by rw [hpost.output hf1, afterSload_output]⟩
  let k : Fin 3 := ⟨_, hiN⟩
  have hbal : d1.getStorVal sevm.currentTarget (balancesBase + Sevm.argWord sevm 0) =
      (b.getStor sevm.currentTarget).get (balanceSlot k) := by
    rw [hq.getStorVal]
    show _ = (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 (Sevm.argWord sevm 0).toNat)
    rw [hk]
  rw [hbal] at hge hout
  have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hge)
  rw [hc.abs.balances k] at hle
  refine ⟨k, out, rfl, ?_, h32, ⟨viewOut s (answerWord out - s.balances.get k), ?_, ?_⟩⟩
  · have h := StaticAnswered.of_afterSload (hans hf1)
    rw [getStorVal_eq_getStor] at h
    show StaticAnswered sevm b ((b.getStor sevm.currentTarget).get
      (coinsBase + Nat.toB256 (Sevm.argWord sevm 0).toNat)).toAdr _ out
    rw [hk]
    exact h
  · rw [hdec]
    exact adminBalances_step hv k rfl _ hle
  · refine quietLands_ret (hq.sload _) (by rw [hdec]; rfl) rfl rfl rfl ?_ hstor hlogs
    have hle' : (b.getStor sevm.currentTarget).get (balanceSlot k) ≤ Bytes.toB256 (List.take 32 out) := by
      rw [B256.le_iff_toNat_le_toNat, hc.abs.balances k]; exact hle
    rw [hout, word, answerWord, ← hc.abs.balances k, ← B256.toNat_sub_eq_of_le _ _ hle',
      Jaune.toB256_toNat]

end

end Blanc.Lift.Curve3Pool
