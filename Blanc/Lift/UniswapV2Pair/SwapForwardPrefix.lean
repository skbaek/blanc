import Blanc.Lift.UniswapV2Pair.SwapFront
import Blanc.Lift.ExactWalkSolc

/-! Forward (gas-exact) swap body prefix, the mirror of `swapBody_prefix_inv`: the lock test
and lock store, the output-amount guard, the internal `getReserves` call, the liquidity
guards, the token loads and the recipient guard, from the body entry `t_0683_c54` to the
optimistic-transfer branch `t_08bf_c4`, with a closed charge in the five named storage
costs. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

private theorem swapFwd_gas {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G G' : Nat} {f : SFunc} {o : Outcome} (h : G = G')
    (k : SFunc.RunExact fs sevm (St b S M G') f o) :
    SFunc.RunExact fs sevm (St b S M G) f o := h ▸ k

private theorem swapFwd_branchTo_zero {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {o : Outcome} {d w : B256} {j : Nat}
    (hw : w = 0) (k : SFunc.RunExact fs sevm (St b S M G) f o) :
    SFunc.RunExact fs sevm (St b (d :: w :: S) M (G + 10)) (.branchTo f j) o := by
  subst hw
  exact rx_branchTo_zero k

/-- One straight-line forward step over a stack with an abstract tail of bounded length. -/
macro "sfw_rx" : tactic => `(tactic| first
  | apply rx_dest
  | apply rx_push rfl (by simp only [List.length_cons]; omega)
  | apply rx_dup rfl (by simp only [List.length_cons]; omega)
  | (apply rx_swap rfl; dsimp only [List.set])
  | apply rx_pop
  | apply rx_and rfl (by simp only [List.length_cons]; omega)
  | apply rx_lt rfl (by simp only [List.length_cons]; omega)
  | apply rx_gt rfl (by simp only [List.length_cons]; omega)
  | apply rx_eq rfl (by simp only [List.length_cons]; omega)
  | apply rx_iszero rfl (by simp only [List.length_cons]; omega))

/-- The reserve read after a nonzero output flag: 105 gas around the packed slot-8 load. -/
theorem swapFwdReserves_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G rs : Nat} {flag len start toWord a1 a0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1000)
    (flagNz : flag ≠ 0) (cost : rs = sloadCost sevm b 8)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 8)
        (reserveTimestampRead (b.getStorVal sevm.currentTarget 8) ::
         reserve1Read (b.getStorVal sevm.currentTarget 8) ::
         reserve0Read (b.getStorVal sevm.currentTarget 8) ::
         0 :: 0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G) t_0767_c2 o) :
    SFunc.RunExact cert.prog sevm
      (St b (flag :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M (G + rs + 105))
      t_0707_c2 o := by
  unfold t_0707_c2
  sfw_rx; sfw_rx
  apply rx_branch_succ flagNz
  unfold t_075c_c2
  sfw_rx; sfw_rx; sfw_rx; sfw_rx; sfw_rx
  exact rx_callRet (show cert.prog[56]? = some t_0d90_c56 from rfl)
    (reserves_callee_exact fork cost (by simp only [List.length_cons]; omega)) body

/-- The lock test, lock store, output-amount guard and reserve read, from the body entry to
`t_0767_c2`. A zero `amount0Out` takes the `amount1Out` comparison (11 more gas). -/
theorem swapFwdLock_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G s12 st rs : Nat} {len start toWord a1 a0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1000)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1) (nonstatic : sevm.isStatic = false)
    (output : a0 ≠ 0 ∨ a1 ≠ 0)
    (c12 : s12 = sloadCost sevm b 12) (cStore : st = sstoreCost sevm (afterSload sevm b 12) 12 0)
    (crs : rs = sloadCost sevm (mintLockedWorld sevm b) 8)
    (sentry : gCallStipend < G + st)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm (mintLockedWorld sevm b) 8)
        (reserveTimestampRead ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
         reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
         reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
         0 :: 0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G) t_0767_c2 o) :
    SFunc.RunExact cert.prog sevm
      (St b (len :: start :: toWord :: a1 :: a0 :: ρ :: R) M
        (G + rs + (if a0 = 0 then 11 else 0) + st + s12 + 160)) t_0683_c54 o := by
  unfold t_0683_c54
  apply swapFwd_gas (G' := ((G + rs + 105 + (if a0 = 0 then 11 else 0) + st + 51) + s12) + 4)
    (by omega)
  sfw_rx; sfw_rx
  apply rx_sload_selC fork c12 (by simp only [List.length_cons]; omega)
  sfw_rx; sfw_rx; sfw_rx
  apply rx_branch_succ (by rw [unlocked]; decide)
  unfold t_06f4_c54
  sfw_rx; sfw_rx; sfw_rx
  apply swapFwd_gas (G' := (G + rs + 105 + (if a0 = 0 then 11 else 0) + 25) + st) (by omega)
  apply rx_sstoreC fork cStore (by omega) nonstatic
  sfw_rx; sfw_rx; sfw_rx; sfw_rx; sfw_rx
  by_cases zero : a0 = 0
  · simp only [zero, ↓reduceIte]
    subst zero
    have nz : a1 ≠ 0 := output.resolve_left (fun h => h rfl)
    rw [show B256.eqCheck (B256.eqCheck (0 : B256) 0) 0 = 0 from by decide]
    apply rx_branchTo_zero
    unfold t_0702_c54
    sfw_rx; sfw_rx; sfw_rx; sfw_rx
    refine swapFwdReserves_exact fork room ?_ crs body
    intro h
    have lt : Bytes.toB256 [0] < a1 := by
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0]).toNat = 0 from rfl]
      rcases Nat.eq_zero_or_pos a1.toNat with h0 | h0
      · exact absurd (B256.toNat_inj a1 0 (h0.trans rfl)) nz
      · exact h0
    simp only [B256.gtCheck, gt_iff_lt, lt, ite_true] at h
    exact absurd h (by decide)
  · simp only [zero, ↓reduceIte]
    refine rx_branchTo_succ ?_ (show cert.prog[2]? = some t_0707_c2 from rfl) ?_
    · simp only [B256.eqCheck, zero, ite_false]
      decide
    · refine swapFwdReserves_exact fork room ?_ crs body
      simp only [B256.eqCheck, zero, ite_false]
      decide

/-- The liquidity guards, the two token loads and the recipient guard, from `t_0767_c2` to the
optimistic-transfer branch: 198 gas plus the two token-slot loads. -/
theorem swapFwdGuards_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G s6 s7 : Nat} {ts r1 r0 len start toWord a1 a0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1000)
    (c6 : s6 = sloadCost sevm b 6) (c7 : s7 = sloadCost sevm (afterSload sevm b 6) 7)
    (lt0 : a0.toNat < (reserveMask112 &&& r0).toNat)
    (lt1 : a1.toNat < (reserveMask112 &&& r1).toNat)
    (ne0 : (0xffffffffffffffffffffffffffffffffffffffff &&& b.getStorVal sevm.currentTarget 6) ≠
      (toWord &&& 0xffffffffffffffffffffffffffffffffffffffff))
    (ne1 : (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) ≠
      (0xffffffffffffffffffffffffffffffffffffffff &&&
        (0xffffffffffffffffffffffffffffffffffffffff &&& b.getStorVal sevm.currentTarget 7)))
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm (afterSload sevm b 6) 7)
        ((0xffffffffffffffffffffffffffffffffffffffff &&& b.getStorVal sevm.currentTarget 7) ::
          (0xffffffffffffffffffffffffffffffffffffffff &&& b.getStorVal sevm.currentTarget 6) ::
          0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G) t_08bf_c4 o) :
    SFunc.RunExact cert.prog sevm
      (St b (ts :: r1 :: r0 :: 0 :: 0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M
        (G + s6 + s7 + 198)) t_0767_c2 o := by
  have lt1of : ∀ x y : B256, x.toNat < y.toNat → B256.ltCheck x y = 1 := by
    intro x y h
    have lt : x < y := B256.lt_iff_toNat_lt_toNat.mpr h
    simp only [B256.ltCheck, lt, ite_true]
  have eq0of : ∀ x y : B256, x ≠ y → B256.eqCheck x y = 0 := by
    intro x y h
    simp only [B256.eqCheck, h, ite_false]
  have s7eq : (afterSload sevm b 6).getStorVal sevm.currentTarget 7 =
      b.getStorVal sevm.currentTarget 7 := by
    change ((afterSload sevm b 6).getStor sevm.currentTarget).get 7 =
      (b.getStor sevm.currentTarget).get 7
    rw [afterSload_getStor]
  unfold t_0767_c2
  apply swapFwd_gas (G' := ((G + 113 + s7) + 3 + s6) + 82) (by omega)
  repeat sfw_rx
  refine swapFwd_branchTo_zero ?_ ?_
  · rw [show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] = reserveMask112 from rfl, lt1of _ _ lt0]
    decide
  unfold t_0786_c2
  repeat sfw_rx
  refine rx_branch_succ ?_ ?_
  · rw [show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] = reserveMask112 from rfl, lt1of _ _ lt1]
    decide
  unfold t_07ef_c3
  sfw_rx; sfw_rx
  apply rx_sload_selC fork c6 (by simp only [List.length_cons]; omega)
  sfw_rx
  apply rx_sload_selC fork c7 (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  refine swapFwd_branchTo_zero ?_ ?_
  · rw [show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] = (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl]
    exact eq0of _ _ ne0
  unfold t_0823_c3
  repeat sfw_rx
  refine rx_branch_succ ?_ ?_
  · rw [show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] = (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl, s7eq, eq0of _ _ ne1]
    decide
  rw [show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] = (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl, s7eq, show Bytes.toB256 [0] = (0 : B256) from rfl]
  exact body


/-- The prefix's closed storage charge: lock load and store, packed reserve load, the two token
loads, 358 gas of straight-line code, and 11 more when `amount0Out` is zero. -/
def swapPrefixGas (sevm : Sevm) (b : Devm) (a0 : B256) : Nat :=
  let locked := mintLockedWorld sevm b
  sloadCost sevm b 12 + sstoreCost sevm (afterSload sevm b 12) 12 0 + sloadCost sevm locked 8 +
    sloadCost sevm (afterSload sevm locked 8) 6 +
    sloadCost sevm (afterSload sevm (afterSload sevm locked 8) 6) 7 +
    (if a0 = 0 then 11 else 0) + 358

/-- **Forward swap body prefix** (mirror of `swapBody_prefix_inv`). Under the finite entry
storage and the source guards of `startTyped` (lock open, nonzero output, liquidity, recipient
not a token), the body runs from its entry to the transfer branch with the source-named locals,
charging exactly `swapPrefixGas`. `sentry` is the `SSTORE` stipend check at the lock store. -/
theorem swapBody_prefix_exact {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (unlocked : st.unlocked = 1) (nonstatic : sevm.isStatic = false)
    (output : swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0)
    (liquidity0 : (swapAmount0Out sevm).toNat < st.reserve0.val)
    (liquidity1 : (swapAmount1Out sevm).toNat < st.reserve1.val)
    (to0 : swapRecipient sevm ≠ st.token0) (to1 : swapRecipient sevm ≠ st.token1)
    (sentry : gCallStipend < G + sstoreCost sevm (afterSload sevm b 12) 12 0)
    (body : SFunc.RunExact cert.prog sevm
      (St (swapPrefixWorld sevm b) (swapLocalsStack sevm st) M G) t_08bf_c4 o) :
    SFunc.RunExact cert.prog sevm
      (St b (swapBodyStack sevm) M (G + swapPrefixGas sevm b (swapAmount0Out sevm)))
      t_0683_c54 o := by
  have lockedRep := rep.mint_locked_world (sevm := sevm) (b := b)
  rcases lockedRep.fixed with ⟨_, _, _, token0Fixed, token1Fixed, cache0, cache1, _, _, _, _, _⟩
  have unlockedRaw : b.getStorVal sevm.currentTarget 12 = 1 := by
    rcases rep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, _, fixed⟩
    exact fixed.trans unlocked
  let m : B256 := 0xffffffffffffffffffffffffffffffffffffffff
  have maskWord : ∀ x : B256, m &&& x = x.toAdr.toB256 := ff20_and_word
  have resIdem : ∀ w : B256, reserveMask112 &&& reserve0Read w = reserve0Read w := by
    intro w
    rw [reserve0Read, B256.and_comm, B256.and_idem_right]
  have resIdem1 : ∀ w : B256, reserveMask112 &&& reserve1Read w = reserve1Read w := by
    intro w
    rw [reserve1Read, B256.and_comm, B256.and_idem_right]
  have slot (k : B256) : (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget k =
      ((mintLockedWorld sevm b).getStor sevm.currentTarget).get k := by
    change ((afterSload sevm (mintLockedWorld sevm b) 8).getStor sevm.currentTarget).get k = _
    rw [afterSload_getStor]
  change reserve0Read (((mintLockedWorld sevm b).getStor sevm.currentTarget).get 8) = _ at cache0
  change reserve1Read (((mintLockedWorld sevm b).getStor sevm.currentTarget).get 8) = _ at cache1
  change reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) = _ at cache0
  change reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) = _ at cache1
  have word0 : m &&& (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6 =
      st.token0.toB256 := by
    rw [maskWord, slot, token0Fixed]
  have word1 : m &&& (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 7 =
      st.token1.toB256 := by
    rw [maskWord, slot, token1Fixed]
  have recipientWord : swapRecipientWord sevm &&& m = (swapRecipient sevm).toB256 := by
    rw [swapRecipientWord, B256.and_idem_right, B256.and_comm, maskWord]
    rfl
  have recipientWord' : m &&& swapRecipientWord sevm = (swapRecipient sevm).toB256 := by
    rw [B256.and_comm, recipientWord]
  have word1' : m &&& (m &&& (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 7) =
      st.token1.toB256 := by
    rw [word1, maskWord, toAdr_toB256]
  have lt0 : (swapAmount0Out sevm).toNat <
      (reserveMask112 &&& reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat := by
    rw [resIdem, cache0, B256.toNat_toB256_of_lt
      (lt_trans st.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
    exact liquidity0
  have lt1 : (swapAmount1Out sevm).toNat <
      (reserveMask112 &&& reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat := by
    rw [resIdem1, cache1, B256.toNat_toB256_of_lt
      (lt_trans st.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
    exact liquidity1
  have ne0 : m &&& (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6 ≠
      swapRecipientWord sevm &&& m := by
    rw [word0, recipientWord]
    intro eq
    exact to0 (by rw [← toAdr_toB256 (swapRecipient sevm), ← eq, toAdr_toB256])
  have ne1 : m &&& swapRecipientWord sevm ≠
      m &&& (m &&& (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 7) := by
    rw [recipientWord', word1']
    intro eq
    exact to1 (by rw [← toAdr_toB256 (swapRecipient sevm), eq, toAdr_toB256])
  have guarded := swapFwdGuards_exact (ts := reserveTimestampRead ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
    (len := swapDataLength sevm) (start := swapDataStart sevm) (toWord := swapRecipientWord sevm)
    (a1 := swapAmount1Out sevm) (a0 := swapAmount0Out sevm) (ρ := 0x257) (R := [0x022c0d9f])
    (M := M) (G := G) (o := o) fork (by decide) rfl rfl lt0 lt1 ne0 ne1 (by
      rw [word0, word1, cache0, cache1]
      exact body)
  have lockRun := swapFwdLock_exact (s12 := sloadCost sevm b 12)
    (st := sstoreCost sevm (afterSload sevm b 12) 12 0)
    (rs := sloadCost sevm (mintLockedWorld sevm b) 8) fork (by decide) unlockedRaw nonstatic output rfl rfl rfl
    (by omega) guarded
  dsimp only [swapPrefixGas]
  refine swapFwd_gas ?_ lockRun
  omega

end Blanc.Lift.UniswapV2Pair
