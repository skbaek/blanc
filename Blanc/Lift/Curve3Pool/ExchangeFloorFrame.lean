import Blanc.Lift.Curve3Pool.ExchangeExactLive
import Blanc.Lift.Curve3Pool.ExactStaticGas
import Blanc.Lift.Curve3Pool.Walk.ExchangeFloorWalk
import Blanc.Lift.StaticGasMessage

/-!
# `exchange` live at the true gas minimum

`exchange_live_floor` is `exchange_live_exact` for every `R ≥ 2201`, and `exchange_msg_floor` its message form. The run
comes from `rx_ex_frame_floor`; the effect comes from the safety theorem read on that run, as in `exchange_live`, whose
own walk would need `costExchange + 4 U`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **`exchange` at the true minimum.** As `exchange_live_exact`, with the calls at their floors and every `R ≥ 2201`. -/
theorem exchange_live_floor {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {i j : Fin 3}
    {B1 B2 : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : ExchangeExactCalls)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (hi : i.val = (exI sevm).toNat) (hj : j.val = (exJ sevm).toNat)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall sevm) = some o)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre)
    (hbal : i = feeIndex →
      StaticWordFloorProfile sevm W W ((pre.getStor sevm.currentTarget).get (coinSlot i))
        (balanceOfData sevm.currentTarget) B1 U 1000 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧
      (∀ b S M, W b → (M.read (0x3dc : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget →
        P.balD1 b S M ≤ 8047) ∧
      StaticWordFloorProfile sevm W' W' ((pre.getStor sevm.currentTarget).get (coinSlot i))
        (balanceOfData sevm.currentTarget) B2 U 1000 0x71c 0x24 0x780 P.balD2 P.balN2 ∧
      (∀ b S M, W' b → (M.read (0x71c : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget →
        P.balD2 b S M ≤ 8047))
    (hpull : MutableFloorProfile sevm W W' ((pre.getStor sevm.currentTarget).get (coinSlot i))
      (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
        (exDx sevm).toBytes) RawCallOk U 5850 0x600 0x64 0x6c0 P.pullD P.pullN)
    (hW''c : WClosed sevm W'')
    (hpush : MutableFloorProfile sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinSlot j))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Nat.toB256 (exPushAmt o)).toBytes) RawCallOk U 4650
      0xb60 0x44 0xc00 P.pushD P.pushN) :
    ∃ (x0 x1 x2 : B256) (amp v : Nat),
      xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
        (balAt (pre.getStor sevm.currentTarget) 1).toNat,
        (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      aChk s sevm.benvStat.time.toNat = some amp ∧
      (∃ (hi3 : (exI sevm).toNat < 3) (hj3 : (exJ sevm).toNat < 3),
        getYChk amp ⟨(exI sevm).toNat, hi3⟩ ⟨(exJ sevm).toNat, hj3⟩
          (exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat /
            exR0).toNat (V3.mk x0.toNat x1.toNat x2.toNat).get = some v) ∧
      ∀ R, 2201 ≤ R →
        (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)).gasMeasure <
          2 ^ 256 →
        (∀ post (exc : Exec 0 sevm
            (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty
            (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v), .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
        ∃ post, ∃ exc : Exec 0 sevm
            (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)) (.ok post),
          ∃ bp bq,
          pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat =
            pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty
            (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v), .ok post, exc⟩ post
            (exEnv sevm i j bp bq) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post ∧ post.gasLeft = R := by
  have hi3 : (exI sevm).toNat < 3 := hi ▸ i.isLt
  have hj3 : (exJ sevm).toNat < 3 := hj ▸ j.isLt
  obtain rfl : i = ⟨(exI sevm).toNat, hi3⟩ := Fin.ext hi
  obtain rfl : j = ⟨(exJ sevm).toNat, hj3⟩ := Fin.ext hj
  obtain ⟨hv0, hex⟩ := ex_body hi3 hj3 hlen hsel hstep
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [show sevm.value.toNat = 0 from hv0]; rfl)
  obtain ⟨x0, x1, x2, amp, v, hi3', hj3', hk, hX, hsub, hmx, hax, hA, hres, hy1, hy2, hmf, hsf, hmo,
    hmin, hma, hmap, hbi, hbj1, hbj2, hpa, hij, hob, -, -⟩ := ex_words hck.abs rfl rfl hex
  have hne : (exI sevm).toNat ≠ (exJ sevm).toNat := fun h => hij (Fin.ext h)
  refine ⟨x0, x1, x2, amp, v, hX, hA, ⟨hi3', hj3', hres⟩, fun R hR hGm hkeep => ?_⟩
  have hG256 : R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v < 2 ^ 256 := by
    have e : (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)).gasMeasure =
      R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v + pre.mach.stateGas.spilled +
        pre.mach.stateGas.committedSpill := rfl
    omega
  have hci : coinSlot ⟨(exI sevm).toNat, hi3⟩ = coinsBase + exI sevm := by
    simp only [coinSlot, toB256_toNat]
  have hcj : coinSlot ⟨(exJ sevm).toNat, hj3⟩ = coinsBase + exJ sevm := by
    simp only [coinSlot, toB256_toNat]
  have hpull' := hpull
  rw [hci] at hpull'
  have hpush' := hpush
  rw [hcj, hpa, toB256_toNat] at hpush'
  -- the exact run
  obtain ⟨r, hr, D, rfl, hL, hDg⟩ := rx_ex_frame_floor (pre := pre) (s0 := s) (B1 := B1) (B2 := B2)
    (Q := fun r => ∃ D', r = .halted D' ∧ ExLive sevm W'' D'
      (exFinal ((pre.getStor sevm.currentTarget).set lockSlot 1) sevm
        (exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi3⟩ + exCred sevm B1 B2) _) ∧ D'.gasLeft = R) P
    hfork hstatic hdepth hlen hcd hsel hid hWc hW'c hWb hck.abs hck.unlocked hval
    (by rw [hck.abs.isKilled, hk]; rfl) hi3 hj3 hX
    (fun h2 => by
      have hb := hbal (Fin.ext (show (exI sevm).toNat = 2 by rw [h2]; rfl))
      rw [hci] at hb
      exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hsub h2⟩)
    hpull' hmx hax hA hres hy1 hy2 hmf hsf hmo hmin hma hmap hbi hbj1 hbj2 hW''c hpush'
    hR hG256 (fun D' h hg => ⟨D', rfl, h, hg⟩)
  obtain ⟨exc⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  -- the safety theorem on that execution
  obtain ⟨hkp, hidk⟩ := hkeep D exc
  obtain ⟨hi3'', hj3'', bp, bq, o', hstep', hraw⟩ :=
    exchange_rawE exc hcode hfork.histFork hlen hcd hsel rfl rfl hGm
    hck hcoin hpc (hid.toH.of_rel ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩) hkp hidk
  obtain ⟨-, hex'⟩ := ex_body hi3 hj3 hlen hsel hstep'
  -- the stored balance of coin `i` pins the credited amount
  have hbI : balancesBase + exI sevm = balancesBase + Nat.toB256 (exI sevm).toNat := by
    rw [toB256_toNat]
  have hbJ : balancesBase + exJ sevm = balancesBase + Nat.toB256 (exJ sevm).toNat := by
    rw [toB256_toNat]
  have hsI : (D.getStor sevm.currentTarget).get (balancesBase + exI sevm) =
      exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi3⟩ + exCred sevm B1 B2 := by
    rw [hL.stor]
    exact (Stor.get_set_ne _ (by rw [hbI]; exact bal_ne_lock hi3) _).trans
      ((Stor.get_set_ne _ (by rw [hbI, hbJ]; exact bal_ne_bal hj3 hi3 (Ne.symm hne)) _).trans
        (Stor.get_set_self _ _ _))
  have hw : ((D.getStor sevm.currentTarget).get (balancesBase + exI sevm)).toNat =
      o'.state.balances.get ⟨(exI sevm).toNat, hi3⟩ := by
    rw [hbI]
    exact hraw.stor.written (.bal ⟨(exI sevm).toNat, hi3⟩)
      (show Fld.bal _ ∈ footprint (decodeCall sevm) by
        rw [ex_decode hlen hsel]; exact bal_mem _)
  rw [hsI, ← hob] at hw
  obtain ⟨-, _, Dm, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bi, _, _,
    -, hDm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbim, -, -, -, ho⟩ :=
    exchange_inv hex
  obtain ⟨-, _, Dm', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bi', _, _,
    -, hDm', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbim', -, -, -, ho'⟩ :=
    exchange_inv hex'
  have hgi : ∀ (v : V3) (a b : Nat), ((v.set ⟨(exI sevm).toNat, hi3⟩ a).set
      ⟨(exJ sevm).toNat, hj3⟩ b).get ⟨(exI sevm).toNat, hi3⟩ = a := fun v a b =>
    (V3.get_set_ne _ hij _).trans (V3.get_set_self _ _ _)
  have h0 : o.state.balances.get ⟨(exI sevm).toNat, hi3⟩ = bi := by rw [ho]; exact hgi _ _ _
  have h1 : o'.state.balances.get ⟨(exI sevm).toNat, hi3⟩ = bi' := by rw [ho']; exact hgi _ _ _
  have hb0 := ex_chkAdd_eq hbim
  have hb1 := ex_chkAdd_eq hbim'
  clear ho ho'
  have hpeq : pullIn (exEnv sevm ⟨_, hi3⟩ ⟨_, hj3⟩ bp bq) ⟨_, hi3⟩ (exDx sevm).toNat =
      pullIn (exEnv sevm ⟨_, hi3⟩ ⟨_, hj3⟩ (exBalOpt ⟨_, hi3⟩ B1) (exBalOpt ⟨_, hi3⟩ B2))
        ⟨_, hi3⟩ (exDx sevm).toNat := by
    rw [hDm, hDm']; congr 1; omega
  rw [exchange_congr (e := exEnv sevm ⟨_, hi3⟩ ⟨_, hj3⟩ bp bq) 
    (e' := exEnv sevm ⟨_, hi3⟩ ⟨_, hj3⟩ (exBalOpt ⟨_, hi3⟩ B1)
    (exBalOpt ⟨_, hi3⟩ B2)) rfl rfl hpeq rfl, hex] at hex'
  cases Option.some.inj hex'
  refine ⟨D, exc, bp, bq, hpeq, hraw, ?_, hL.w, hDg⟩
  exact (rawEffect_refines (D := ⟨0, sevm, St pre [] Mem.empty
    (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v), .ok D, exc⟩) hck hstep' hraw).1

/-- **`exchange` at the true minimum, at message entry.** -/
theorem exchange_msg_floor {msg : Msg} {s : State} {o : Out} {i j : Fin 3}
    {B1 B2 : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : ExchangeExactCalls)
    (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = selExchange)
    (hi : i.val = (exI (initSevm msg)).toNat) (hj : j.val = (exJ (initSevm msg)).toNat)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : step s (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2))
      (decodeCall (initSevm msg)) = some o)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
    (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : WClosed (initSevm msg) W) (hW'c : WClosed (initSevm msg) W') (hWb : W (initDevm msg))
    (hbal : i = feeIndex →
      StaticWordFloorProfile (initSevm msg) W W
        (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
        (balanceOfData msg.currentTarget) B1 U 1000 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧
      (∀ b S M, W b → (M.read (0x3dc : B256).toNat (0x24 : B256).toNat).1 = balanceOfData msg.currentTarget →
        P.balD1 b S M ≤ 8047) ∧
      StaticWordFloorProfile (initSevm msg) W' W'
        (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
        (balanceOfData msg.currentTarget) B2 U 1000 0x71c 0x24 0x780 P.balD2 P.balN2 ∧
      (∀ b S M, W' b → (M.read (0x71c : B256).toNat (0x24 : B256).toNat).1 = balanceOfData msg.currentTarget →
        P.balD2 b S M ≤ 8047))
    (hpull : MutableFloorProfile (initSevm msg) W W'
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
      (transferFromSel ++ msg.caller.toB256.toBytes ++ msg.currentTarget.toB256.toBytes ++
        (exDx (initSevm msg)).toBytes) RawCallOk U 5850 0x600 0x64 0x6c0 P.pullD P.pullN)
    (hW''c : WClosed (initSevm msg) W'')
    (hpush : MutableFloorProfile (initSevm msg) W' W''
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot j))
      (transferSel ++ msg.caller.toB256.toBytes ++ (Nat.toB256 (exPushAmt o)).toBytes) RawCallOk U 4650
      0xb60 0x44 0xc00 P.pushD P.pushN) :
    ∃ (x0 x1 x2 : B256) (amp v : Nat),
      xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
        (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
        (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ =
          some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
      (∃ (hi3 : (exI (initSevm msg)).toNat < 3) (hj3 : (exJ (initSevm msg)).toNat < 3),
        getYChk amp ⟨(exI (initSevm msg)).toNat, hi3⟩ ⟨(exJ (initSevm msg)).toNat, hj3⟩
          (exW3 x0 x1 x2 (exI (initSevm msg)).toNat + exCred (initSevm msg) B1 B2 *
            exRate (exI (initSevm msg)).toNat / exR0).toNat (V3.mk x0.toNat x1.toNat x2.toNat).get =
          some v) ∧
      ∀ R, 2201 ≤ R →
        R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v < 2 ^ 256 →
        (∀ post (exc : Exec 0 (initSevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v)))
            (initDevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) (.ok post)),
          PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
        ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v)))
            (initDevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) (.ok post),
          exec (initEvm (msg.withGas
            (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) = .ok post ∧
          post.gasLeft = R ∧ ∃ bp bq,
          pullIn (exEnv (initSevm msg) i j bp bq) i (exDx (initSevm msg)).toNat =
            pullIn (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i
              (exDx (initSevm msg)).toNat ∧
          RawEffect ⟨0, _, _, .ok post, exc⟩ post (exEnv (initSevm msg) i j bp bq) o ∧
          Checkpoint (post.getStor msg.currentTarget) o.state ∧ W'' post := by
  obtain ⟨x0, x1, x2, amp, v, hX, hA, hY, -⟩ := exchange_live_floor (sevm := initSevm msg)
    (pre := initDevm msg) P hcode hfork hstatic hdepth hlen hcd hsel hi hj hck hstep hcoin hpc hid
    hWc hW'c hWb hbal hpull hW''c hpush
  refine ⟨x0, x1, x2, amp, v, hX, hA, hY, fun R hR hGm hkeep => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F, F = R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v :=
    ⟨_, rfl⟩
  obtain ⟨x0', x1', x2', amp', v', hX', hA', hY', h⟩ := exchange_live_floor
    (sevm := {initSevm msg with gas := F})
    (pre := initDevm msg) P hcode hfork hstatic hdepth hlen hcd hsel hi hj hck hstep hcoin hpc
    (hid.withStaticGas F) (hWc.withStaticGas F) (hW'c.withStaticGas F) hWb
    (fun e => ⟨(hbal e).1.withStaticGas F, (hbal e).2.1, (hbal e).2.2.1.withStaticGas F, (hbal e).2.2.2⟩) (hpull.withStaticGas F)
    (hW''c.withStaticGas F) (hpush.withStaticGas F)
  obtain ⟨rfl, rfl, rfl⟩ := xpWords_unique hX hX'
  obtain rfl : amp = amp' := Option.some.inj (hA.symm.trans hA')
  obtain ⟨hi3, hj3, hY⟩ := hY
  obtain ⟨hi3', hj3', hY'⟩ := hY'
  obtain rfl : v = v' := Option.some.inj (hY.symm.trans hY')
  rw [exExactCost_withStaticGas (initSevm msg) F] at h
  have h' := h R
  rw [← hF] at h' hGm hkeep ⊢
  obtain ⟨post, exc, bp, bq, hpe, hraw, hckp, hW'', hg⟩ := h' hR hGm hkeep
  exact ⟨post, exc, exec_withGas_of_frame exc, hg, bp, bq, hpe, hraw, hckp, hW''⟩

end Blanc.Lift.Curve3Pool
