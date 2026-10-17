import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXSpec
import Blanc.Lift.Curve3Pool.Walk.ViewsGvpRaw

/-!
# `calc_withdraw_one_coin(_token_amount, i)`: the frame and its raw effect

The body (`0x4398`): the non-payable guard, the `int128` clamp of `i`, the arguments stored, the
child-aware `_calc_withdraw_one_coin` walk (`xa_cw`), and `dy` returned.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

-- SEGMENT: cwo
/-- **The `calc_withdraw_one_coin` body** on the derivation. -/
theorem xa_cwo (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (h : XAt sevm post 0x4398 (St b [] (vdMem sevm) G) L) :
    sevm.value = 0 ∧ ∃ (c : Exec.Frame) (hi : (Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat < 3)
      (dy fee : B256), L = [c] ∧
      StaticWordChild ((b.getStor sevm.currentTarget).get tokenSlot).toAdr totalSupplyData c ∧
      (∀ e : Env, e.time = sevm.benvStat.time.toNat → e.supply = some (vSupply c).toNat →
        calcWithdrawOne s e (Sevm.dataWord sevm (Bytes.toB256 [4])).toNat
          ⟨(Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat, hi⟩ = some (dy.toNat, fee.toNat)) ∧
      (∀ a, post.getStor a = b.getStor a) ∧ post.logs = b.logs ∧ post.output = dy.toBytes := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xs 0x4399 (.reg .callvalue) ri_callvalue  -- 4398 CALLVALUE
  xs 0x439a (.reg .iszero) ri_iszero  -- 4399 ISZERO
  xs 0x439d (.push [0x43, 0xa2] (by decide)) ri_push  -- 439a PUSH2 0x43a2
  xji 0x439e 0x43a2 hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x43a3  -- 43a2 JUMPDEST
  xs 0x43a5 (.push [0x60] (by decide)) ri_push  -- 43a3 PUSH1 0x60
  xlu 0x43a6  -- 43a5 MLOAD
  xs 0x43a8 (.push [0x24] (by decide)) ri_push  -- 43a6 PUSH1 0x24
  xs 0x43a9 (.reg .calldataload) ri_calldataload  -- 43a8 CALLDATALOAD
  xs 0x43aa (.reg (.dup 0)) (ri_dup (by rfl))  -- 43a9 DUP1
  xs 0x43ac (.push [0x40] (by decide)) ri_push  -- 43aa PUSH1 0x40
  xlu 0x43ad  -- 43ac MLOAD
  xs 0x43ae (.reg (.swap 0)) (ri_swap (by rfl))  -- 43ad SWAP1
  xs2 0x43af (.reg .sgt) ri_sgt  -- 43ae SGT
  xs 0x43b0 (.reg .iszero) ri_iszero  -- 43af ISZERO
  xs 0x43b3 (.push [0x43, 0xb8] (by decide)) ri_push  -- 43b0 PUSH2 0x43b8
  xji 0x43b4 0x43b8 hw
  · xdead
  clear hw
  xjd 0x43b9  -- 43b8 JUMPDEST
  xs 0x43ba (.reg (.dup 0)) (ri_dup (by rfl))  -- 43b9 DUP1
  xs 0x43bb (.reg (.swap 1)) (ri_swap (by rfl))  -- 43ba SWAP2
  xs 0x43bc (.reg (.swap 0)) (ri_swap (by rfl))  -- 43bb SWAP1
  xs2 0x43bd (.reg .slt) ri_slt  -- 43bc SLT
  xs 0x43be (.reg .iszero) ri_iszero  -- 43bd ISZERO
  xs 0x43c1 (.push [0x43, 0xc6] (by decide)) ri_push  -- 43be PUSH2 0x43c6
  xji 0x43c2 0x43c6 hw
  · xdead
  clear hw
  xjd 0x43c7  -- 43c6 JUMPDEST
  xs 0x43c8 (.reg .pop) ri_pop  -- 43c7 POP
  xs 0x43ca (.push [0x04] (by decide)) ri_push  -- 43c8 PUSH1 0x04
  xs 0x43cb (.reg .calldataload) ri_calldataload  -- 43ca CALLDATALOAD
  xs 0x43ce (.push [0x01, 0x40] (by decide)) ri_push  -- 43cb PUSH2 0x0140
  xsw 0x43cf 0x140  -- 43ce MSTORE
  xs 0x43d1 (.push [0x24] (by decide)) ri_push  -- 43cf PUSH1 0x24
  xs 0x43d2 (.reg .calldataload) ri_calldataload  -- 43d1 CALLDATALOAD
  xs 0x43d5 (.push [0x01, 0x60] (by decide)) ri_push  -- 43d2 PUSH2 0x0160
  xsw 0x43d6 0x160  -- 43d5 MSTORE
  xs 0x43d9 (.push [0x01, 0x60] (by decide)) ri_push  -- 43d6 PUSH2 0x0160
  xl 0x43da 0x160  -- 43d9 MLOAD
  xs 0x43dd (.push [0x01, 0x40] (by decide)) ri_push  -- 43da PUSH2 0x0140
  xl 0x43de 0x140  -- 43dd MLOAD
  xs 0x43e0 (.push [0x06] (by decide)) ri_push  -- 43de PUSH1 0x06
  cvpc 0x43e1  -- 43e0 PC
  xs 0x43e2 (.reg .add) ri_add  -- 43e1 ADD
  xs 0x43e5 (.push [0x3c, 0xca] (by decide)) ri_push  -- 43e2 PUSH2 0x3cca
  xjmp 0x3cca  -- 43e5 JUMP
  obtain ⟨c, L', hi, dy, fee, b', M1, G1, hL, hsw, hmod, -, hst, hlg, h, hV1⟩ :=
    xa_cw hc hcode hfork ha (hV.sub (List.nil_subset _)) htok h
  clear hV
  have hV := hV1
  clear hV1
  xjd 0x43e7  -- 43e6 JUMPDEST
  xs 0x43ea (.push [0x01, 0xc0] (by decide)) ri_push  -- 43e7 PUSH2 0x01c0
  xsw 0x43eb 0x1c0  -- 43ea MSTORE
  xs 0x43ee (.push [0x01, 0xe0] (by decide)) ri_push  -- 43eb PUSH2 0x01e0
  xsw 0x43ef 0x1e0  -- 43ee MSTORE
  xs 0x43f2 (.push [0x01, 0xc0] (by decide)) ri_push  -- 43ef PUSH2 0x01c0
  xl 0x43f3 0x1c0  -- 43f2 MLOAD
  xs 0x43f5 (.push [0x00] (by decide)) ri_push  -- 43f3 PUSH1 0x00
  have hfinalwf := hV.wf
  xsw 0x43f6 0x0  -- 43f5 MSTORE
  xs 0x43f8 (.push [0x20] (by decide)) ri_push  -- 43f6 PUSH1 0x20
  xs 0x43fa (.push [0x00] (by decide)) ri_push  -- 43f8 PUSH1 0x00
  obtain ⟨hrun, rfl⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hrun
  refine ⟨hval, c, hi, dy, fee, by rw [hL], hsw, hmod, fun a => by rw [hstor, hst],
    by rw [hlogs, hlg], ?_⟩
  rw [hout, show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl, Mem.read_write_word_of_wf hfinalwf]

/-- **`calc_withdraw_one_coin`'s raw effect**, given the certificate's checkedness. -/
theorem cwo_raw_of (hc : Cert.CheckedM code cert mems true) {pre : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCalcWithdrawOneCoin)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have h : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨_, h⟩ := xa_vd_calcWithdrawOneCoin hcode hlen hcd hsel h
  obtain ⟨hval, c, hi, dy, fee, hL, ⟨htgt, hdata, hstat, hlen', hclogs⟩, hmod, hstor, hlogs,
    hout⟩ := xa_cwo hc hcode hfork hck.abs htok h
  have ha0 : arg sevm 0 = (Sevm.dataWord sevm (Bytes.toB256 [4])).toNat := by
    unfold arg Sevm.argWord
    rw [show (32 * 0 + 4 : B256) = Bytes.toB256 [4] by decide]
  have ha1 : arg sevm 1 = (Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat := by
    unfold arg Sevm.argWord
    rw [show (32 * 1 + 4 : B256) = Bytes.toB256 [0x24] by decide]
  have hdec : decodeCall sevm = .calcWithdrawOneCoin (arg sevm 0) (arg sevm 1) :=
    decodeCall_at (k := 9) rfl hsel hlen
  have hi1 : arg sevm 1 < 3 := by rw [ha1]; exact hi
  have hg := hmod (vEnv sevm (some (vSupply c).toNat)) rfl rfl
  refine ⟨vEnv sevm (some (vSupply c).toNat), viewOut s dy.toNat, ?_, ?_⟩
  · rw [hdec]
    show (if (vEnv sevm _).value = 0 then body s _ (.calcWithdrawOneCoin _ _) else none) = _
    rw [show (vEnv sevm (some (vSupply c).toNat)).value = 0 by rw [vEnv, hval]; rfl,
      ite_eq_left rfl]
    simp only [body, idx, hi1, ↓reduceDIte, Option.bind_eq_bind, Option.bind_some]
    rw [show (⟨arg sevm 1, hi1⟩ : Fin 3) =
      ⟨(Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat, hi⟩ from Fin.ext ha1, ha0, hg,
      Option.bind_some]
  · have hch : children ⟨0, sevm, pre, .ok post, exc⟩ = [c] := hL
    refine rawEffect_view (envOf_vEnv hch htgt hdata hlen') (by rw [hdec]; rfl)
      (fun x => by rw [hstor]; rfl) ?_ ?_ ?_
    · rw [hch, hlogs]
      simp only [List.flatMap_cons, List.flatMap_nil, hclogs, List.append_nil]
    · rw [hout, word, toB256_toNat]
    · intro c' hc'
      rw [hch, List.mem_singleton] at hc'
      rw [hc']
      exact hstat

end

end Blanc.Lift.Curve3Pool
