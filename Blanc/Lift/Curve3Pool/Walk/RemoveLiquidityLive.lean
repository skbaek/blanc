import Blanc.Lift.Curve3Pool.LivePremises
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquiditySafe

/-!
# `remove_liquidity`, forward: an exact run from the frame's entry

The liveness walk builds `SFunc.RunEx` over the certificate's trees, read forwards: the
dispatcher (`rx_dispatch_rl`), the guarded prologue with the `totalSupply` call
(`rx_rl_pre`), the loop (`rx_rl_iter`), and the burn, event and lock clear (`rx_rl_postW`).
Each segment is continuation-passing: it builds the run of its tree from the run of the rest.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **`remove_liquidity`'s `burnFrom(msg.sender, amt)` succeeds** (window `0x61c`/`0x6a0`) from
the call-site world `W` into `W'`, with at least 32 bytes back and the pool's storage kept. The
burn is the frame's last call and its walk (`rx_rl_postW`) uses nothing of the world it leaves,
so this is `BurnOkAt` without the `IdReady` conjunct (`BurnOkAt.burnOkTo`). -/
def BurnOkTo (sevm : Sevm) (W W' : Devm → Prop) (t amt : B256) (U : Nat) : Prop :=
  ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → U ≤ G → G < 2 ^ 256 →
    (M.read 0x61c 0x44).1 = burnFromSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes →
    S.length < 1024 →
    ∃ d, Ninst.RunCompiled sevm
        (St b (Nat.toB256 G :: t :: 0 :: 0x61c :: 0x44 :: 0x6a0 :: 0x20 :: S) M G) (.exec .call) d ∧
      MutableCallPost b d S M 0x61c 0x44 0x6a0 0x20 1 ∧ 32 ≤ d.returnData.length ∧
      d.returnData.length < 2 ^ 256 ∧ G ≤ d.gasLeft + U ∧ d.gasLeft ≤ G ∧
      d.getStor sevm.currentTarget = b.getStor sevm.currentTarget ∧ W' d

/-- The generalized burn premise at `remove_liquidity`'s window gives `BurnOkTo`. -/
theorem BurnOkAt.burnOkTo {sevm : Sevm} {W W' : Devm → Prop} {t amt : B256} {U : Nat}
    (h : BurnOkAt sevm W W' t amt U 0x61c 0x6a0) : BurnOkTo sevm W W' t amt U := by
  intro b S M G hW hU hG hin hS
  obtain ⟨d, hr, hp, hok, hl, h1, h2, hs, hWd, -⟩ := h b S M G hW hU hG hin hS
  exact ⟨d, hr, hp, hok, hl, h1, h2, hs, hWd⟩

/-- `BurnOkTo` whose answer also satisfies a relation `E` to the call's actual input. -/
def BurnOkToE (sevm : Sevm) (W W' : Devm → Prop) (t amt : B256) (U : Nat)
    (E : Devm → List B256 → Mem → Nat → Devm → Prop) : Prop :=
  ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → U ≤ G → G < 2 ^ 256 →
    (M.read 0x61c 0x44).1 = burnFromSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes →
    S.length < 1024 →
    ∃ d, Ninst.RunCompiled sevm
        (St b (Nat.toB256 G :: t :: 0 :: 0x61c :: 0x44 :: 0x6a0 :: 0x20 :: S) M G) (.exec .call) d ∧
      MutableCallPost b d S M 0x61c 0x44 0x6a0 0x20 1 ∧ 32 ≤ d.returnData.length ∧
      d.returnData.length < 2 ^ 256 ∧ G ≤ d.gasLeft + U ∧ d.gasLeft ≤ G ∧
      d.getStor sevm.currentTarget = b.getStor sevm.currentTarget ∧ W' d ∧ E b S M G d

/-- The bounded burn premise, with the trivial relation. -/
theorem BurnOkTo.withE {sevm : Sevm} {W W' : Devm → Prop} {t amt : B256} {U : Nat}
    (h : BurnOkTo sevm W W' t amt U) : BurnOkToE sevm W W' t amt U (fun _ _ _ _ _ => True) := by
  intro b S M G hW hU hG hin hS
  obtain ⟨d, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h b S M G hW hU hG hin hS
  exact ⟨d, h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩

/-- **The dispatcher, forward**: with the `remove_liquidity` selector, the frame's entry tree
runs to the arm's body `t_2c68_c0` over the prologue's memory, at 451 gas. -/
theorem rx_dispatch_rl {sevm : Sevm} {b : Devm} {G : Nat} {Q : Outcome → Prop}
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (k : SFunc.RunEx cert.prog sevm (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G)
      t_2c68_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [] Mem.empty (G + 451)) t_0000_c0 Q := by
  have hR0 := vyMem_reads Mem.wf_empty Mem.reads_empty (Sevm.dataWord sevm 0)
  have hsz0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hX : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD 0 32 0) = 0xecb586a5 := by
    rw [vyImg_selector]; exact hsel
  have hlen4 : B256.eqCheck (B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [0x04]))
      0 ≠ 0 := by
    rw [ltCheck_eq_zero_of_le (by rw [B256.toNat_toB256_of_lt hcd]; exact hlen)]; decide
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldatasize (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hlen4 ·)
  xr (rx_dest ·)
  xr (rx_vyPrologue (by simp only [List.length_nil]; omega) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq (v := 1) (by rw [hX]; decide) (by hr) ·)
  xr (rx_iszero (v := 0) (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_zero ·)
  exact k

theorem gtCheck_ne_zero_of_lt {x y : B256} (h : y < x) : B256.gtCheck x y ≠ 0 := by
  unfold B256.gtCheck
  simp only [gt_iff_lt, h, ↓reduceIte]
  decide

/-! ## Reply-relation premises

The exact walk prices every external call at its literal input memory, so the stage cores below
keep the `Mem` term itself, not only its image; the literal-memory steps they use
(`rxe_mstoreL`, `rxe_calldatacopyL`, `rxe_identityL`, `rxe_sstoreX`) are `LiveKit`'s.

`StaticWordOkAtE` and `MutCallOkAtE` are the bounded call premises with one extra relation `E`
between the call's actual input and its post. The bounded clients choose `E := True`; the exact
walk chooses the profile's debit equation and canonical successor. -/

/-- `StaticWordOkAt` whose answer also satisfies a relation `E` to the call's actual input. -/
def StaticWordOkAtE (sevm : Sevm) (W W' : Devm → Prop) (t : B256) (data : Bytes) (A : B256)
    (U : Nat) (ii is oi : B256) (E : Devm → List B256 → Mem → Nat → Devm → Prop) : Prop :=
  ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → U ≤ G → G < 2 ^ 256 →
    (M.read ii.toNat is.toNat).1 = data → S.length < 1024 →
    ∃ d out, Ninst.RunCompiled sevm
        (St b (Nat.toB256 G :: t :: ii :: is :: oi :: 0x20 :: S) M G) (.exec .staticcall) d ∧
      StaticCallPost b d S M ii is oi 0x20 1 out ∧ 32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
      Bytes.toB256 (out.take 32) = A ∧ G ≤ d.gasLeft + U ∧ d.gasLeft ≤ G ∧ W' d ∧
      (IdReady sevm b → IdReady sevm d) ∧ E b S M G d

/-- `MutCallOkAt` whose answer also satisfies a relation `E` to the call's actual input. -/
def MutCallOkAtE (sevm : Sevm) (W W' : Devm → Prop) (t : B256) (data : Bytes)
    (ok : Bytes → Prop) (U : Nat) (ii is oi : B256)
    (E : Devm → List B256 → Mem → Nat → Devm → Prop) : Prop :=
  ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → U ≤ G → G < 2 ^ 256 →
    (M.read ii.toNat is.toNat).1 = data → S.length < 1024 →
    ∃ d, Ninst.RunCompiled sevm
        (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G) (.exec .call) d ∧
      MutableCallPost b d S M ii is oi 0x20 1 ∧ ok d.returnData ∧
      d.returnData.length < 2 ^ 256 ∧ G ≤ d.gasLeft + U ∧ d.gasLeft ≤ G ∧
      d.getStor sevm.currentTarget = b.getStor sevm.currentTarget ∧ W' d ∧
      (IdReady sevm b → IdReady sevm d) ∧ E b S M G d

/-- The bounded static premise, with the trivial relation. -/
theorem StaticWordOkAt.withE {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes}
    {A : B256} {U : Nat} {ii is oi : B256} (h : StaticWordOkAt sevm W W' t data A U ii is oi) :
    StaticWordOkAtE sevm W W' t data A U ii is oi (fun _ _ _ _ _ => True) := by
  intro b S M G hW hU hG hin hS
  obtain ⟨d, out, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h b S M G hW hU hG hin hS
  exact ⟨d, out, h1, h2, h3, h4, h5, h6, h7, h8, h9, trivial⟩

/-- The bounded mutable premise, with the trivial relation. -/
theorem MutCallOkAt.withE {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes}
    {ok : Bytes → Prop} {U : Nat} {ii is oi : B256}
    (h : MutCallOkAt sevm W W' t data ok U ii is oi) :
    MutCallOkAtE sevm W W' t data ok U ii is oi (fun _ _ _ _ _ => True) := by
  intro b S M G hW hU hG hin hS
  obtain ⟨d, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h b S M G hW hU hG hin hS
  exact ⟨d, h1, h2, h3, h4, h5, h6, h7, h8, h9, trivial⟩

/-- The base `remove_liquidity`'s `totalSupply` call runs from: the lock read and set, the token
slot read. -/
def rlSupplyBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
    (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (Bytes.toB256 [5])

/-- The memory `remove_liquidity`'s `totalSupply` call runs over: the prologue's, with the
selector written at `0x160`. -/
def rlSupplyMem (sevm : Sevm) : Mem :=
  (vyMem Mem.empty (Sevm.dataWord sevm 0)).write 0x160 (Bytes.toB256 [24, 22, 13, 221]).toBytes

/-- The loop head's memory after the `totalSupply` reply over `M`: `T` at `0x140`, the amounts
and fees zeroed by `CALLDATACOPY` past the calldata, and counter `0`. -/
def rlLoopMem0 (sevm : Sevm) (T : B256) (M : Mem) : Mem :=
  (((M.write 0x140 T.toBytes).write 0x1e0
    (sevm.data.sliceD (Nat.toB256 sevm.data.length).toNat 96 0)).write 0x240
    (sevm.data.sliceD (Nat.toB256 sevm.data.length).toNat 96 0)).write 0x2a0
    (Bytes.toB256 [0]).toBytes

/-- `remove_liquidity`'s gas up to the `totalSupply` call (`Gs` is left at the call). -/
def rlPreCost (sevm : Sevm) (b : Devm) : Nat :=
  89 + sloadCost sevm b (Bytes.toB256 [0xff, 0xff, 0xff]) +
    sstoreCost sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1]) +
    sloadCost sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (Bytes.toB256 [5])

/-- **The guarded prologue, forward, with the supply call's relation `E`**: `rx_rl_pre`, whose
continuation also receives `E` at the call's literal input, the exact gas the call left, and the
loop head's memory as a term. As `rx_rl_pre` (`0x2c68` → the loop head): the lock is clear, no value,
`totalSupply` answers `T` (`SupplyOk`); the loop head runs over a base whose pool storage is the
entry's with the lock set, with `T` at `0x140`, zero amounts and fees, and counter `0`. -/
theorem rx_rl_preE {sevm : Sevm} {b : Devm} {Gs : Nat} {Q : Outcome → Prop} {W : Devm → Prop}
    {U : Nat} {T : B256} {E : Devm → List B256 → Mem → Nat → Devm → Prop} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hcd : sevm.data.length < 2 ^ 256)
    (hlock : (b.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hWc : WClosed sevm W) (hWb : W b)
    (hsup : StaticWordOkAtE sevm W W ((b.getStor sevm.currentTarget).get tokenSlot)
      totalSupplyData T U 0x17c 4 0x1c0 E)
    (hGs : U + 135 ≤ Gs) (hGs2 : 2300 < Gs) (hGs' : Gs < 2 ^ 256)
    (k : ∀ b1 M1 img1 G1, W b1 → (IdReady sevm b → IdReady sevm b1) →
      (∀ x, (b1.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 1).get x) →
      b1.logs = b.logs → b1.output = b.output →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x2c0 → LoopImg img1 0 T (fun _ => 0) →
      Gs ≤ G1 + U + 135 → G1 ≤ Gs →
      E (rlSupplyBase sevm b) [] (rlSupplyMem sevm) Gs b1 → b1.gasLeft = G1 + 135 →
      M1 = rlLoopMem0 sevm T b1.memory →
      SFunc.RunEx cert.prog sevm (St b1 [3, 0x2a0] M1 G1) t_2cdb_c0 Q) :
    SFunc.RunEx cert.prog sevm
      (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) (Gs + rlPreCost sevm b)) t_2c68_c0 Q := by
  have hR := vyMem_reads Mem.wf_empty Mem.reads_empty (Sevm.dataWord sevm 0)
  have hW := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have hsz := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hlk : B256.eqCheck (b.getStorVal sevm.currentTarget (Bytes.toB256 [0xff, 0xff, 0xff])) 0 ≠
      0 := by
    rw [getStorVal_eq, lockSlot_lit, hlock]; decide
  unfold rlPreCost
  rw [show Gs + (89 + sloadCost sevm b (Bytes.toB256 [0xff, 0xff, 0xff]) +
    sstoreCost sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1]) +
    sloadCost sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (Bytes.toB256 [5])) =
    Gs + 2 + sloadCost sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (Bytes.toB256 [5]) + 3 + 3 + 21 + 3 +
      3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b
      (Bytes.toB256 [0xff, 0xff, 0xff])) (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1]) + 3 +
      3 + 1 + 10 + 3 + 3 + sloadCost sevm b (Bytes.toB256 [0xff, 0xff, 0xff]) + 3 by omega]
  xr (rx_push rfl (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hlk ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic ·)
  xr (rx_callvalue (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hval]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x160) (c := 21) hR hW hsz rfl (by decide) ?_; intro M hM0x160 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  xr (rx_gas (by hr) ·)
  have htokv : (afterSstore sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])).getStorVal sevm.currentTarget
      (Bytes.toB256 [5]) = (b.getStor sevm.currentTarget).get tokenSlot := by
    rw [lockSlot_lit, tokenSlot_lit, getStorVal_afterSstore_ne lock_ne_token, getStorVal_afterSload]
    rfl
  rw [htokv, show Bytes.toB256 [1, 124] = 0x17c by decide, show Bytes.toB256 [4] = 4 by decide,
    show Bytes.toB256 [1, 192] = 0x1c0 by decide, show Bytes.toB256 [32] = 0x20 by decide]
  have hWb2 : W (afterSload sevm (afterSstore sevm (afterSload sevm b
      (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]))
      (Bytes.toB256 [5])) := hWc.sload _ _ (hWc.sstore _ _ _ (hWc.sload _ _ hWb))
  have hin : (M.read 0x17c 4).1 = totalSupplyData := by
    rw [hR.read, Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide) (by rw [B256.length_toBytes])]
    decide
  obtain ⟨d, out, hrun, hpost, hlen32, hlt, hT, hgas, hgle, hWd, hidd, hE⟩ :=
    hsup _ [] M Gs hWb2 (by omega) hGs' hin (by decide)
  xr (.next hrun ·)
  have hd := hpost.eq_St
  rw [show (0x17c : B256).toNat = 0x17c by decide, show (4 : B256).toNat = 4 by decide,
    show (0x1c0 : B256).toNat = 0x1c0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hd
  rw [hd]
  obtain ⟨G1, hG1⟩ : ∃ G1, d.gasLeft = G1 + 135 := ⟨d.gasLeft - 135, by omega⟩
  rw [hG1]
  have hrds : B256.gtCheck d.returnData.length.toB256 (Bytes.toB256 [0x1f]) ≠ 0 := by
    rw [hpost.returnData]
    apply gtCheck_ne_zero_of_lt
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hlt,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide]
    omega
  have hW1 := (hW.extends [(0x17c, 4), (0x1c0, 0x20)]).write 0x1c0 (out.take 0x20)
  replace hR := (hR.extends [(0x17c, 4), (0x1c0, 0x20)]).write (hW.extends _) 0x1c0 (out.take 0x20)
  have hext : (M.extends [(0x17c, 4), (0x1c0, 0x20)]).size = 0x1e0 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  replace hsz : ((M.extends [(0x17c, 4), (0x1c0, 0x20)]).write 0x1c0 (out.take 0x20)).size =
      0x1e0 := by
    rw [Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  replace hW := hW1
  clear hW1
  have hT1 : Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (vyImg [] (Sevm.dataWord sevm 0)) 352
      (Bytes.toB256 [24, 22, 13, 221]).toBytes) 448 (out.take 32)).sliceD 448 32 0) = T := by
    have h := Bytes.sliceD_writeAt (Bytes.writeAt (vyImg [] (Sevm.dataWord sevm 0)) 352
      (Bytes.toB256 [24, 22, 13, 221]).toBytes) (out.take 32) 448
    rw [List.length_take, Nat.min_eq_left hlen32] at h
    rw [h, hT]
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_returndatasize (by hr) ·)
  xr (rx_gt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hrds ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hr) ·)
  rw [hT1]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM0x140 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldatasize (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_calldatacopyL (o := 0x1e0) (z := 0x60) (c := 21) hR hW hsz rfl rfl (by decide) ?_; intro M hM0x1e0 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldatasize (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_calldatacopyL (o := 0x240) (z := 0x60) (c := 21) hR hW hsz rfl rfl (by decide) ?_; intro M hM0x240 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_dup (n := 3) rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x2a0) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM0x2a0 hR hW hsz
  xr (rx_add (by hr) ·)
  rw [show [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [2, 160]] = ([3, 0x2a0] : List B256)
    by decide]
  have hZ : List.sliceD sevm.data (Nat.toB256 (List.length sevm.data)).toNat 96 0 =
      List.replicate 96 0 := by
    rw [B256.toNat_toB256_of_lt hcd]; exact List.sliceD_length_eq
  refine k _ _ _ _ hWd (fun hid => hidd (((hid.afterSload _).afterSstore _ _).afterSload _))
    (fun x => ?_) ?_ ?_ hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ (by omega) (by omega)
    (by rw [hM0x160] at hE; exact hE) hG1
    (by rw [hM0x2a0, hM0x240, hM0x1e0, hM0x140, hpost.memory]; rfl)
  · rw [hpost.stor, afterSload_getStor, afterSstore_getStor_self, afterSload_getStor, lockSlot_lit]
    rfl
  · rw [hpost.logs, afterSload_logs, afterSstore_logs, afterSload_logs]
  · rw [hpost.output rfl, afterSload_output, afterSstore_output, afterSload_output]
  · rw [show Nat.toB256 0 = Bytes.toB256 [0] by decide]
    exact WordAt.write_self _ _ _
  · rw [hZ]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_self _ _ _)
      (.inl (by decide))) (.inl (by decide))) (.inl (by decide))
  · rw [hZ]
    intro j hj
    refine WordAt.write_other ?_ (.inl (by omega))
    by_cases hj3 : j < 3
    · refine WordAt.write_other ?_ (.inl (by omega))
      unfold WordAt
      rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_replicate]; omega),
        List.sliceD_replicate_zero]
      decide
    · unfold WordAt
      rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_replicate]; omega),
        List.sliceD_replicate_zero]
      decide

/-- **The guarded prologue, forward** (`0x2c68` → the loop head): the lock is clear, no value,
`totalSupply` answers `T` (`SupplyOk`); the loop head runs over a base whose pool storage is the
entry's with the lock set, with `T` at `0x140`, zero amounts and fees, and counter `0`. -/
theorem rx_rl_pre {sevm : Sevm} {b : Devm} {Gs : Nat} {Q : Outcome → Prop} {W : Devm → Prop}
    {U : Nat} {T : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hcd : sevm.data.length < 2 ^ 256)
    (hlock : (b.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hWc : WClosed sevm W) (hWb : W b)
    (hsup : SupplyOk sevm W ((b.getStor sevm.currentTarget).get tokenSlot) T U)
    (hGs : U + 135 ≤ Gs) (hGs2 : 2300 < Gs) (hGs' : Gs < 2 ^ 256)
    (k : ∀ b1 M1 img1 G1, W b1 → (IdReady sevm b → IdReady sevm b1) →
      (∀ x, (b1.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 1).get x) →
      b1.logs = b.logs → b1.output = b.output →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x2c0 → LoopImg img1 0 T (fun _ => 0) →
      Gs ≤ G1 + U + 135 → G1 ≤ Gs →
      SFunc.RunEx cert.prog sevm (St b1 [3, 0x2a0] M1 G1) t_2cdb_c0 Q) :
    SFunc.RunEx cert.prog sevm
      (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) (Gs + rlPreCost sevm b)) t_2c68_c0 Q :=
  rx_rl_preE hfork hstatic hcd hlock hval hWc hWb hsup.withE hGs hGs2 hGs'
    fun b1 M1 img1 G1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 _ _ _ =>
      k b1 M1 img1 G1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

/-- The loop body's memory to `0x2e0c` over `M`, with amount `V`: the `balances` key word, `V` at
`0x2c0`, the six error-buffer words written on the successful path too, the key word again. -/
def rlS1Mem (M : Mem) (V : B256) : Mem :=
  (((((((M.write 192 (Bytes.toB256 [1]).toBytes).write 704 V.toBytes).write 736
    (Bytes.toB256 [8, 195, 121, 160]).toBytes).write 768 (Bytes.toB256 [32]).toBytes).write 800
    (Bytes.toB256 [48]).toBytes).write 832
    (Bytes.toB256 [87, 105, 116, 104, 100, 114, 97, 119, 97, 108, 32, 114, 101, 115, 117, 108, 116,
      101, 100, 32, 105, 110, 32, 102, 101, 119, 101, 114, 32, 99, 111, 105]).toBytes).write 864
    (Bytes.toB256 [110, 115, 32, 116, 104, 97, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).toBytes).write 192 (Bytes.toB256 [1]).toBytes

/-- `remove_liquidity`'s loop body gas up to `0x2e0c` (variant A). -/
def rlS1CostA (sevm : Sevm) (b : Devm) (i : Nat) (B T : B256) : Nat :=
  10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) + 3 + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 7 + 3 + 2 + 3 + 2 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 2 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + sloadCost sevm b (balancesBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1

/-- `rx_rl_s1A`, whose continuation also receives its memory as a term. As `rx_rl_s1A`:
`remove_liquidity`'s loop body up to `0x2e0c`, forward (variant A: loop head t_2cdb_c0,
memory size 0x2c0). -/
theorem rx_rl_s1AL {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T B : B256} {a : Nat → B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x2c0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = B)
    (hmulw : (B256.eqCheck (B * rlAmt sevm / B) (rlAmt sevm) ||| B256.eqCheck B 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (B * rlAmt sevm / T) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck B (B * rlAmt sevm / T)) 0 ≠ 0) (hG : 2300 < Gc)
    (k : ∀ M' img', M' = rlS1Mem M (B * rlAmt sevm / T) → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x380 → LoopImg img' i T a →
      WordAt img' 0x2c0 (B * rlAmt sevm / T) →
      SFunc.RunEx cert.prog sevm (St (afterSstore sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i))
        (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T))
        [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], B * rlAmt sevm / T, 3, 0x2a0] M' Gc) t_2e0c_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M (Gc + rlS1CostA sevm b i B T)) t_2cdb_c0 Q := by
  rw [show Gc + rlS1CostA sevm b i B T = Gc + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) + 3 + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 7 + 3 + 2 + 3 + 2 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 2 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + sloadCost sevm b (balancesBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 by unfold rlS1CostA; omega]
  have hctr := hL.ctr
  have hT := hL.supply
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  rw [hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM1 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_eq, hB]
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_dup (n := 3) rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_or rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hmulw ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hT.read]
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hT0 ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x2c0) (c := 7) hR hW hsz rfl (by decide) ?_; intro M hM2 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x2e0) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM3 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x300) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM4 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x320) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM5 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x340) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM6 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x360) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM7 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hminw ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM8 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_afterSload, getStorVal_eq, hB]
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hlew ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  refine k _ _ (by rw [hM8, hM7, hM6, hM5, hM4, hM3, hM2, hM1]; rfl) hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ ?_
  · wchainT; exact hctr
  · wchainT; exact hT
  · intro j hj; wchainT; exact hL.amt j hj
  · wchainT

/-- `remove_liquidity`'s loop body up to `0x2e0c`, forward (variant A: loop head t_2cdb_c0,
memory size 0x2c0). -/
theorem rx_rl_s1A {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T B : B256} {a : Nat → B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x2c0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = B)
    (hmulw : (B256.eqCheck (B * rlAmt sevm / B) (rlAmt sevm) ||| B256.eqCheck B 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (B * rlAmt sevm / T) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck B (B * rlAmt sevm / T)) 0 ≠ 0) (hG : 2300 < Gc)
    (k : ∀ M' img', Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x380 → LoopImg img' i T a →
      WordAt img' 0x2c0 (B * rlAmt sevm / T) →
      SFunc.RunEx cert.prog sevm (St (afterSstore sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i))
        (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T))
        [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], B * rlAmt sevm / T, 3, 0x2a0] M' Gc) t_2e0c_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M (Gc + rlS1CostA sevm b i B T)) t_2cdb_c0 Q :=
  rx_rl_s1AL hfork hstatic hi hR hW hsz hL hB hmulw hT0 hminw hlew hG
    fun M' img' _ => k M' img'

/-- `remove_liquidity`'s loop body gas up to `0x2e0c` (variant B). -/
def rlS1CostB (sevm : Sevm) (b : Devm) (i : Nat) (B T : B256) : Nat :=
  10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) + 3 + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 2 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + sloadCost sevm b (balancesBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1

/-- `rx_rl_s1B`, whose continuation also receives its memory as a term. As `rx_rl_s1B`:
`remove_liquidity`'s loop body up to `0x2e0c`, forward (variant B: loop head t_2cdb_c46,
memory size 0x5e0). -/
theorem rx_rl_s1BL {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T B : B256} {a : Nat → B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = B)
    (hmulw : (B256.eqCheck (B * rlAmt sevm / B) (rlAmt sevm) ||| B256.eqCheck B 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (B * rlAmt sevm / T) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck B (B * rlAmt sevm / T)) 0 ≠ 0) (hG : 2300 < Gc)
    (k : ∀ M' img', M' = rlS1Mem M (B * rlAmt sevm / T) → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 → LoopImg img' i T a →
      WordAt img' 0x2c0 (B * rlAmt sevm / T) →
      SFunc.RunEx cert.prog sevm (St (afterSstore sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i))
        (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T))
        [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], B * rlAmt sevm / T, 3, 0x2a0] M' Gc) t_2e0c_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M (Gc + rlS1CostB sevm b i B T)) t_2cdb_c46 Q := by
  rw [show Gc + rlS1CostB sevm b i B T = Gc + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) + 3 + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 2 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + sloadCost sevm b (balancesBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 by unfold rlS1CostB; omega]
  have hctr := hL.ctr
  have hT := hL.supply
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  rw [hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM1 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_eq, hB]
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_dup (n := 3) rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_or rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hmulw ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hT.read]
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hT0 ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x2c0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM2 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x2e0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM3 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x300) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM4 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x320) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM5 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x340) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM6 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x360) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM7 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hminw ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM8 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_afterSload, getStorVal_eq, hB]
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hlew ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  refine k _ _ (by rw [hM8, hM7, hM6, hM5, hM4, hM3, hM2, hM1]; rfl) hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ ?_
  · wchainT; exact hctr
  · wchainT; exact hT
  · intro j hj; wchainT; exact hL.amt j hj
  · wchainT

/-- `remove_liquidity`'s loop body up to `0x2e0c`, forward (variant B: loop head t_2cdb_c46,
memory size 0x5e0). -/
theorem rx_rl_s1B {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T B : B256} {a : Nat → B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = B)
    (hmulw : (B256.eqCheck (B * rlAmt sevm / B) (rlAmt sevm) ||| B256.eqCheck B 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (B * rlAmt sevm / T) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck B (B * rlAmt sevm / T)) 0 ≠ 0) (hG : 2300 < Gc)
    (k : ∀ M' img', Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 → LoopImg img' i T a →
      WordAt img' 0x2c0 (B * rlAmt sevm / T) →
      SFunc.RunEx cert.prog sevm (St (afterSstore sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i))
        (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T))
        [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], B * rlAmt sevm / T, 3, 0x2a0] M' Gc) t_2e0c_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M (Gc + rlS1CostB sevm b i B T)) t_2cdb_c46 Q :=
  rx_rl_s1BL hfork hstatic hi hR hW hsz hL hB hmulw hT0 hminw hlew hG
    fun M' img' _ => k M' img'

/-- The `transfer` payload's copy length word (`0x64`), as the bytecode computes it. -/
abbrev rlCopyLen : B256 :=
  Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32])

/-- The payload's memory at its first identity copy: amount `V` in slot `i`, the selector's
length word `4` at `0x400`, the padded `transfer` selector at `0x420`. -/
def rlS2Mem1 (M : Mem) (i : Nat) (V : B256) : Mem :=
  ((M.write (480 + 32 * i) V.toBytes).write 1024 (Bytes.toB256 [4]).toBytes).write 1056
    (Bytes.toB256 [169, 5, 156, 187, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0]).toBytes

/-- The canonical base after the payload's first identity copy (the selector). -/
def rlS2Base1 (sevm : Sevm) (b : Devm) (M : Mem) (i : Nat) (V : B256) : Devm :=
  identityCallNext sevm b [Bytes.toB256 [4], Bytes.toB256 [4, 0], Bytes.toB256 [0], 3, 672]
    (rlS2Mem1 M i V) (Bytes.toB256 [4, 0] + Bytes.toB256 [32]) (Bytes.toB256 [4])
    (Bytes.toB256 [4, 96] + Bytes.toB256 [0] + Bytes.toB256 [32]) (Bytes.toB256 [4])

/-- The payload's memory at its second identity copy: the copied selector, the caller and `V`
after it, the payload length word at `0x460`. -/
def rlS2Mem2 (sevm : Sevm) (M : Mem) (i : Nat) (V : B256) : Mem :=
  (((((rlS2Mem1 M i V).extends [(1056, 4), (1152, 4)]).write 1152
    (((rlS2Mem1 M i V).read 1056 4).1.take 4)).write 1156 sevm.caller.toB256.toBytes).write 1188
    V.toBytes).write 1120
    (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32]).toBytes

/-- The canonical base after the payload's second identity copy (the whole calldata). -/
def rlS2Next (sevm : Sevm) (b : Devm) (M : Mem) (i : Nat) (V : B256) : Devm :=
  identityCallNext sevm (rlS2Base1 sevm b M i V) [rlCopyLen, Bytes.toB256 [4, 96], 3, 672]
    (rlS2Mem2 sevm M i V) (Bytes.toB256 [4, 96]) rlCopyLen (Bytes.toB256 [5, 0]) rlCopyLen

/-- The payload's memory after both identity copies. -/
def rlS2Mem (sevm : Sevm) (M : Mem) (i : Nat) (V : B256) : Mem :=
  ((rlS2Mem2 sevm M i V).extends [(1120, 100), (1280, 100)]).write 1280
    (((rlS2Mem2 sevm M i V).read 1120 100).1.take 100)

/-- The payload's canonical base is stable modulo gas in its entry base. -/
theorem rlS2Next_congr (sevm : Sevm) {b b' : Devm} (M : Mem) (i : Nat) (V : B256)
    (h : Devm.EqModGas b b') : Devm.EqModGas (rlS2Next sevm b M i V) (rlS2Next sevm b' M i V) :=
  identityCallNext_congr sevm _ _ _ _ _ _ (identityCallNext_congr sevm _ _ _ _ _ _ h)

/-- `rx_rl_s2A`, whose continuation also receives the canonical base and the literal memory.
As `rx_rl_s2A`: the `transfer` payload with its two identity copies, forward (variant A: memory 0x380). -/
theorem rx_rl_s2AL {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T V : B256} {a : Nat → B256} (hi : i < 3)
    (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x380) (hL : LoopImg img i T a)
    (hv : WordAt img 0x2c0 V) (hG : 2000 ≤ Gc) (hGb : Gc + 532 < 2 ^ 256)
    {W : Devm → Prop} (hWc : WClosed sevm W) (hWb : W b)
    (k : ∀ b' M' img', BaseRel b b' → W b' → IdReady sevm b' →
      Devm.EqModGas b' (rlS2Next sevm b M i V) → M' = rlS2Mem sevm M i V →
      Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x580 →
      LoopImg img' i T (Function.update a i V) →
      Region img' 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)) →
      ∀ x y, SFunc.RunEx cert.prog sevm (St b' (x :: y :: [3, 0x2a0]) M' Gc) t_2ea7_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], V, 3, 0x2a0] M
      (Gc + 532)) t_2e0c_c0 Q := by
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x1e0 + 32 * i) (c := 3) hR hW hsz (off_amt hi)
    ⟨by rw [memExtSize_of_le (by decide) (by omega), Nat.sub_self]; rfl, by decide⟩ ?_
  intro M hM0 hR hW hsz
  rw [memExtSize_of_le (by decide) (by omega)] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x400) (c := 19) hR hW hsz rfl (by decide) ?_; intro M hM1 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x420) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM2 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 5) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  have e1 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img1, hR, hI⟩ := e1
  have f_ctr : WordAt img1 0x2a0 (Nat.toB256 i) := by rw [hI]; wchainT; exact hL.ctr
  have f_T : WordAt img1 0x140 T := by rw [hI]; wchainT; exact hL.supply
  have f_v : WordAt img1 0x2c0 V := by rw [hI]; wchainT; exact hv
  have f_400 : WordAt img1 0x400 (Bytes.toB256 [4]) := by rw [hI]; wchainT
  have f_sel : WordAt img1 0x420 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) := by
    rw [hI]; wchainT
  have f_amt : ∀ j, j < 6 → WordAt img1 (0x1e0 + 32 * j) (Function.update a i V j) := by
    intro j hj
    rw [hI]
    by_cases e : j = i
    · subst e; rw [Function.update_self]; wchainT
    · rw [Function.update_of_ne e]; wchainT; exact hL.amt j hj
  clear hI hL hv
  refine rxe_identityL (i := 0x420) (n := 4) (o := 0x480) (z := 4) (ext := 9) (X := 127) hid hdepth hR hW
    hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 4 = 18 by decide]; omega) (by omega) (by hr) ?_
  intro b2 M hsha hcan1 hMi1 hR hW hsz
  have hsel4 : (img1.sliceD 0x420 4 0).take 4 = transferSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel b b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  have hWb2 : W b2 := hWc.sha _ _ _ hsha hWb
  clear hsha hsel4
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rxm_mload (o := 0x400) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_400.read]
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 1) rfl ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x484) (c := 6) hR hW hsz (by decide) (by decide) ?_; intro M hM3 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_v.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x4a4) (c := 6) hR hW hsz (by decide) (by decide) ?_; intro M hM4 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM5 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_self]
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  refine rxe_identityL (i := 0x460) (n := 0x64) (o := 0x500) (z := 0x64) (ext := 16) (X := 143)
    (hid.of_rel hb12) hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 0x64 = 27 by decide]; omega) (by omega) (by hr) ?_
  intro b3 M hsha2 hcan2 hMi2 hR hW hsz
  rw [transfer_copy] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  have hWb3 : W b3 := hWc.sha _ _ _ hsha2 hWb2
  clear hsha2

  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  have e3 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img3, hR, hI⟩ := e3
  subst hMi2 hM5 hM4 hM3 hMi1 hM2 hM1 hM0
  refine k b3 _ img3 (hb12.trans hb23) hWb3 (hid.of_rel (hb12.trans hb23))
    (hcan2.trans (identityCallNext_congr sevm _ _ _ _ _ _ hcan1)) rfl hR hW
    (by refine hsz.trans ?_; decide) ⟨?_, ?_, ?_⟩ ?_ _ _
  · rw [hI]; wchainT; exact f_ctr
  · rw [hI]; wchainT; exact f_T
  · intro j hj; rw [hI]; wchainT; exact f_amt j hj
  · rw [hI]; exact Region.write_self _ _ _

/-- The `transfer` payload with its two identity copies, forward (variant A: memory 0x380). -/
theorem rx_rl_s2A {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T V : B256} {a : Nat → B256} (hi : i < 3)
    (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x380) (hL : LoopImg img i T a)
    (hv : WordAt img 0x2c0 V) (hG : 2000 ≤ Gc) (hGb : Gc + 532 < 2 ^ 256)
    {W : Devm → Prop} (hWc : WClosed sevm W) (hWb : W b)
    (k : ∀ b' M' img', BaseRel b b' → W b' → IdReady sevm b' → Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x580 →
      LoopImg img' i T (Function.update a i V) →
      Region img' 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)) →
      ∀ x y, SFunc.RunEx cert.prog sevm (St b' (x :: y :: [3, 0x2a0]) M' Gc) t_2ea7_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], V, 3, 0x2a0] M
      (Gc + 532)) t_2e0c_c0 Q :=
  rx_rl_s2AL hi hid hdepth hR hW hsz hL hv hG hGb hWc hWb
    fun b' M' img' h1 h2 h3 _ _ => k b' M' img' h1 h2 h3

/-- `rx_rl_s2B`, whose continuation also receives the canonical base and the literal memory.
As `rx_rl_s2B`: the `transfer` payload with its two identity copies, forward (variant B: memory 0x5e0). -/
theorem rx_rl_s2BL {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T V : B256} {a : Nat → B256} (hi : i < 3)
    (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img i T a)
    (hv : WordAt img 0x2c0 V) (hG : 2000 ≤ Gc) (hGb : Gc + 482 < 2 ^ 256)
    {W : Devm → Prop} (hWc : WClosed sevm W) (hWb : W b)
    (k : ∀ b' M' img', BaseRel b b' → W b' → IdReady sevm b' →
      Devm.EqModGas b' (rlS2Next sevm b M i V) → M' = rlS2Mem sevm M i V →
      Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x5e0 →
      LoopImg img' i T (Function.update a i V) →
      Region img' 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)) →
      ∀ x y, SFunc.RunEx cert.prog sevm (St b' (x :: y :: [3, 0x2a0]) M' Gc) t_2ea7_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], V, 3, 0x2a0] M
      (Gc + 482)) t_2e0c_c0 Q := by
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x1e0 + 32 * i) (c := 3) hR hW hsz (off_amt hi)
    ⟨by rw [memExtSize_of_le (by decide) (by omega), Nat.sub_self]; rfl, by decide⟩ ?_
  intro M hM0 hR hW hsz
  rw [memExtSize_of_le (by decide) (by omega)] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x400) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM1 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x420) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM2 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 5) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  have e1 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img1, hR, hI⟩ := e1
  have f_ctr : WordAt img1 0x2a0 (Nat.toB256 i) := by rw [hI]; wchainT; exact hL.ctr
  have f_T : WordAt img1 0x140 T := by rw [hI]; wchainT; exact hL.supply
  have f_v : WordAt img1 0x2c0 V := by rw [hI]; wchainT; exact hv
  have f_400 : WordAt img1 0x400 (Bytes.toB256 [4]) := by rw [hI]; wchainT
  have f_sel : WordAt img1 0x420 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) := by
    rw [hI]; wchainT
  have f_amt : ∀ j, j < 6 → WordAt img1 (0x1e0 + 32 * j) (Function.update a i V j) := by
    intro j hj
    rw [hI]
    by_cases e : j = i
    · subst e; rw [Function.update_self]; wchainT
    · rw [Function.update_of_ne e]; wchainT; exact hL.amt j hj
  clear hI hL hv
  refine rxe_identityL (i := 0x420) (n := 4) (o := 0x480) (z := 4) (ext := 0) (X := 118) hid hdepth hR hW
    hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 4 = 18 by decide]; omega) (by omega) (by hr) ?_
  intro b2 M hsha hcan1 hMi1 hR hW hsz
  have hsel4 : (img1.sliceD 0x420 4 0).take 4 = transferSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel b b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  have hWb2 : W b2 := hWc.sha _ _ _ hsha hWb
  clear hsha hsel4
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rxm_mload (o := 0x400) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_400.read]
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 1) rfl ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x484) (c := 3) hR hW hsz (by decide) (by decide) ?_; intro M hM3 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_v.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x4a4) (c := 3) hR hW hsz (by decide) (by decide) ?_; intro M hM4 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hM5 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_self]
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  refine rxe_identityL (i := 0x460) (n := 0x64) (o := 0x500) (z := 0x64) (ext := 0) (X := 127)
    (hid.of_rel hb12) hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 0x64 = 27 by decide]; omega) (by omega) (by hr) ?_
  intro b3 M hsha2 hcan2 hMi2 hR hW hsz
  rw [transfer_copy] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  have hWb3 : W b3 := hWc.sha _ _ _ hsha2 hWb2
  clear hsha2

  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  have e3 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img3, hR, hI⟩ := e3
  subst hMi2 hM5 hM4 hM3 hMi1 hM2 hM1 hM0
  refine k b3 _ img3 (hb12.trans hb23) hWb3 (hid.of_rel (hb12.trans hb23))
    (hcan2.trans (identityCallNext_congr sevm _ _ _ _ _ _ hcan1)) rfl hR hW
    (by refine hsz.trans ?_; decide) ⟨?_, ?_, ?_⟩ ?_ _ _
  · rw [hI]; wchainT; exact f_ctr
  · rw [hI]; wchainT; exact f_T
  · intro j hj; rw [hI]; wchainT; exact f_amt j hj
  · rw [hI]; exact Region.write_self _ _ _

/-- The `transfer` payload with its two identity copies, forward (variant B: memory 0x5e0). -/
theorem rx_rl_s2B {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T V : B256} {a : Nat → B256} (hi : i < 3)
    (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img i T a)
    (hv : WordAt img 0x2c0 V) (hG : 2000 ≤ Gc) (hGb : Gc + 482 < 2 ^ 256)
    {W : Devm → Prop} (hWc : WClosed sevm W) (hWb : W b)
    (k : ∀ b' M' img', BaseRel b b' → W b' → IdReady sevm b' → Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x5e0 →
      LoopImg img' i T (Function.update a i V) →
      Region img' 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)) →
      ∀ x y, SFunc.RunEx cert.prog sevm (St b' (x :: y :: [3, 0x2a0]) M' Gc) t_2ea7_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], V, 3, 0x2a0] M
      (Gc + 482)) t_2e0c_c0 Q :=
  rx_rl_s2BL hi hid hdepth hR hW hsz hL hv hG hGb hWc hWb
    fun b' M' img' h1 h2 h3 _ _ => k b' M' img' h1 h2 h3

/-! ## The `transfer` call's `raw_call` tail -/

/-- The `raw_call` site of `remove_liquidity`'s transfer: length word at `0x5a0`, copy buffer at
`0x3a0`, and its eight jump targets. -/
def rlSite : VyRawSite := ⟨0x05, 0xa0, 0x03, 0xa0, 0x2e, 0xdf, 0x2e, 0xf0, 0x2e, 0xf2, 0x2f, 0x17,
  0x2f, 0x6a, 0x2f, 0x40, 0x2f, 0x4e, 0x2f, 0x69⟩

theorem rl_join : cert.prog[15]? =
    some (vyRawCallJoin rlSite t_2f13_c15 t_2f3c_c15 t_2f4a_c15 t_2f65_c15 t_2f6a_c15) := rfl

theorem rl_tail : (SFunc.next (.push [0x2e, 0xdf] (by decide)) (.branch t_2edb_c0 t_2edf_c0)) =
    vyRawCallTail rlSite 15 t_2edb_c0 t_2f13_c15 t_2f3c_c15 t_2f4a_c15 t_2f65_c15 t_2f6a_c15 := rfl

/-- `remove_liquidity`'s gas from `0x2ea7` to the `transfer` call. -/
def rlS3Cost (sevm : Sevm) (b : Devm) (i : Nat) : Nat :=
  108 + sloadCost sevm b (coinsBase + Nat.toB256 i)

/-- The loop's next tree: its exit after the last coin, its head otherwise. -/
def rlNext (i : Nat) : SFunc := if i + 1 = 3 then t_2f7b_c15 else t_2cdb_c46

/-- **The transfer call and its tail, forward, with the call's relation `E`**: `rx_rl_s3`, whose
continuation also receives the call's post `d` with `E` at its literal input, the exact gas left,
the tail's canonical identity base and the literal memory. As `rx_rl_s3` (`0x2ea7` → the loop's next tree): `coins[i]`,
the `CALL` answered by `CoinPushOkAt`, the `raw_call` success test (`rxc_vyRawCallTail`), and
`i += 1`. -/
theorem rx_rl_s3E {sevm : Sevm} {b : Devm} {Gx : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {s i : Nat} {T V C : B256} {a : Nat → B256} {W W' : Devm → Prop} {U : Nat}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hdepth : sevm.depth ≠ 0)
    (hid : IdReady sevm b) (hWc : WClosed sevm W) (hWb : W b) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s) (hs : s = 0x580 ∨ s = 0x5e0)
    (hL : LoopImg img i T a)
    (hdata : Region img 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)))
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = C)
    (hpush : MutCallOkAtE sevm W W' C (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)
      RawCallOk U 0x520 0x44 0x5c0 E) (hGx : U + 2000 ≤ Gx)
    (hGb : Gx + 1000 < 2 ^ 256)
    (k : ∀ b' M' img' G', W' b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 → LoopImg img' (i + 1) T a →
      Gx ≤ G' + U + 600 → G' ≤ Gx → ∀ d : Devm,
      E (afterSload sevm b (coinsBase + Nat.toB256 i)) [3, 0x2a0]
        (M.write 0xc0 (Bytes.toB256 [0]).toBytes) Gx d →
      d.gasLeft = G' + 45 + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d [3, 0x2a0] d.memory rlSite) →
      M' = (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32)).write 0x2a0
        (Nat.toB256 (i + 1)).toBytes →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G') (rlNext i) Q) :
    ∀ x y, SFunc.RunEx cert.prog sevm (St b (x :: y :: [3, 0x2a0]) M (Gx + rlS3Cost sevm b i))
      t_2ea7_c0 Q := by
  intro x y
  have hs32 : s % 32 = 0 := by rcases hs with rfl | rfl <;> decide
  have hs0 : 0x580 ≤ s := by rcases hs with rfl | rfl <;> decide
  unfold rlS3Cost
  rw [show Gx + (108 + sloadCost sevm b (coinsBase + Nat.toB256 i)) = Gx + 2 +
    sloadCost sevm b (coinsBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 +
    3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 2 + 1 by omega]
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x500) hR hsz rfl ⟨by omega, hs32⟩ (by hr) ·)
  rw [(Region.word hdata.left).read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl ⟨by omega, hs32⟩ (by hr) ·)
  rw [hL.ctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl
    ⟨by rw [memExtSize_of_le hs32 (by omega), Nat.sub_self]; rfl, hs32⟩ ?_
  intro M hM1 hR hW hsz
  rw [memExtSize_of_le hs32 (by omega)] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl ⟨by omega, hs32⟩ (by hr) (by decide) ·)
  rw [keccak_zero]
  xr (rx_add (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_eq, hC]
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] =
      (0x44 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [5, 32] = (0x520 : B256) by decide,
    show Bytes.toB256 [5, 192] = (0x5c0 : B256) by decide,
    show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read 0x520 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes := by
    rw [hR.read]
    exact Region.slice (Region.write_other hdata.right (by simp only [B256.length_toBytes]; omega))
      (by simp only [List.length_append, B256.length_toBytes]; rfl)
  obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd, hE⟩ :=
    hpush _ [3, 0x2a0] M Gx (hWc.sload _ _ hWb) (by omega) (by omega) hin (by decide)
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x520 : B256).toNat = 0x520 by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0x5c0 : B256).toNat = 0x5c0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d (1 :: [3, 0x2a0]) d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd, rl_tail]
  have hext : (M.extends [(0x520, 0x44), (0x5c0, 0x20)]).size = 0x5e0 := by
    show memExtsSize M.size _ = _
    rw [hsz]; rcases hs with rfl | rfl <;> decide
  have hsz5 : d.memory.size = 0x5e0 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 : Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x5c0 (d.returnData.take 0x20)) := by
    rw [hmem]; exact (hR.extends _).write (hW.extends _) _ _
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have htc : rawTailCost (min d.returnData.length 32) ≤ 500 := by
    unfold rawTailCost rawJoinCost rawCheckCost idCost ceilDiv
    split_ifs <;> omega
  obtain ⟨G2, hG2⟩ : ∃ G2, d.gasLeft = G2 + rawTailCost (min d.returnData.length 32) :=
    ⟨d.gasLeft - rawTailCost (min d.returnData.length 32), by omega⟩
  rw [hG2]
  refine SFunc.runEx_iff_runExCut_nil.mpr (rxce_vyRawCallTail_canonical (hidd (hid.afterSload _))
    hdepth (by decide) rl_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
    ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega) (by hr)
    ?_)
  · rw [show (Bytes.toB256 [rlSite.lh, rlSite.ll]).toNat + 32 = 0x5c0 by decide]
    intro j hj
    exact (rawCall_window hmem rfl j hj).2
  intro b' rd' hsha hcanT
  refine SFunc.runEx_iff_runExCut_nil.mp ?_
  clear hrun
  rw [show (Bytes.toB256 [rlSite.lh, rlSite.ll]).toNat = 0x5a0 by decide,
    show (Bytes.toB256 [rlSite.bh, rlSite.bl]).toNat = 0x3a0 by decide]
  have hn32 : min d.returnData.length 32 ≤ 32 := by omega
  have hR6 : Mem.Reads (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32))
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
        (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
        (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x3a0 ((Bytes.writeAt (Bytes.writeAt
        (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
        (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x5a0
        (min d.returnData.length 32 + 32) 0)) := by
    unfold vyRawMem
    rw [(hR5.write hW5 _ _).read]
    exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
  have hW6 : Mem.Wf (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32)) := by
    unfold vyRawMem; exact (hW5.write _ _).write _ _
  have hsz6 : (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32)).size = 0x5e0 := by
    unfold vyRawMem
    have h1 : (d.memory.write 0x5a0 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
        0x5e0 := by
      rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
    rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
  obtain ⟨G', hG'⟩ : ∃ G', G2 = G' + 45 := ⟨G2 - 45, by omega⟩
  rw [hG']
  have hctr6 : WordAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x3a0 ((Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x5a0
      (min d.returnData.length 32 + 32) 0)) 0x2a0 (Nat.toB256 i) := by
    wchain; exact hL.ctr
  xr (fun h => rx_dest (rx_dest h))
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR6 hsz6 rfl ⟨by decide, by decide⟩ (by hr) ·)
  rw [hctr6.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  rw [succ_lit hi]
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 3) rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x2a0) (c := 3) hR6 hW6 hsz6 rfl (by decide) ?_
  intro M7 hM7 hR7 hW7 hsz7
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  have hWb' : W' b' := hW'c.sha _ _ _ hsha hWd
  have hidb' : IdReady sevm b' := (hidd (hid.afterSload _)).of_rel
    ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  have hstb' : ∀ x, (b'.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x := by
    intro x; rw [hsha.stor, hstor, afterSload_getStor]
  have hLI : LoopImg (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x3a0 ((Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x5a0
      (min d.returnData.length 32 + 32) 0)) 0x2a0 (Nat.toB256 (i + 1)).toBytes) (i + 1) T a :=
    ⟨WordAt.write_self _ _ _, by wchain; exact hL.supply,
      fun j hj => by wchain; exact hL.amt j hj⟩
  have hgas' : Gx ≤ G' + U + 600 := by omega
  have hsz7' : M7.size = 0x5e0 := by rw [hsz7]; decide
  rcases (show i + 1 = 3 ∨ i + 1 < 3 by omega) with h3 | h3
  · have hn : rlNext i = t_2f7b_c15 := by unfold rlNext; simp only [h3, ↓reduceIte]
    have e0 : B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 = 0 := by rw [h3]; decide
    rw [e0]
    xr (rx_branchTo_zero ·)
    have := k b' M7 _ G' hWb' hidb' hstb' hR7 hW7 hsz7' hLI hgas' (by omega) d
      (by rw [hM1] at hE; exact hE) (by omega) hcanT hM7
    rwa [hn] at this
  · have hn : rlNext i = t_2cdb_c46 := by unfold rlNext; simp only [show i + 1 ≠ 3 by omega, ↓reduceIte]
    xr (rx_branchTo_succ (by rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> decide)
      rfl ·)
    have := k b' M7 _ G' hWb' hidb' hstb' hR7 hW7 hsz7' hLI hgas' (by omega) d
      (by rw [hM1] at hE; exact hE) (by omega) hcanT hM7
    rwa [hn] at this

/-- **The transfer call and its tail, forward** (`0x2ea7` → the loop's next tree): `coins[i]`,
the `CALL` answered by `CoinPushOkAt`, the `raw_call` success test (`rxc_vyRawCallTail`), and
`i += 1`. -/
theorem rx_rl_s3 {sevm : Sevm} {b : Devm} {Gx : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {s i : Nat} {T V C : B256} {a : Nat → B256} {W W' : Devm → Prop} {U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hdepth : sevm.depth ≠ 0)
    (hid : IdReady sevm b) (hWc : WClosed sevm W) (hWb : W b) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s) (hs : s = 0x580 ∨ s = 0x5e0)
    (hL : LoopImg img i T a)
    (hdata : Region img 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)))
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = C)
    (hpush : CoinPushOkAt sevm W W' C V U 0x520 0x5c0) (hGx : U + 2000 ≤ Gx)
    (hGb : Gx + 1000 < 2 ^ 256)
    (k : ∀ b' M' img' G', W' b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 → LoopImg img' (i + 1) T a →
      Gx ≤ G' + U + 600 → G' ≤ Gx →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G') (rlNext i) Q) :
    ∀ x y, SFunc.RunEx cert.prog sevm (St b (x :: y :: [3, 0x2a0]) M (Gx + rlS3Cost sevm b i))
      t_2ea7_c0 Q :=
  rx_rl_s3E hfork hi hdepth hid hWc hWb hW'c hR hW hsz hs hL hdata hC hpush.withE hGx hGb
    fun b' M' img' G' h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ _ _ => k b' M' img' G' h1 h2 h3 h4 h5 h6 h7 h8 h9

/-! ## After the loop -/

/-- `remove_liquidity`'s gas from the loop's exit to the `burnFrom` call. -/
def rlPostCost (sevm : Sevm) (b : Devm) : Nat := 67 + sloadCost sevm b tokenSlot

/-- The memory `remove_liquidity`'s `burnFrom` call runs over: the loop exit's, with the selector,
the caller and `_amount` written at `0x600`. -/
def rlBurnMem (sevm : Sevm) (M : Mem) : Mem :=
  ((M.write 1536 (Bytes.toB256 [121, 204, 103, 144]).toBytes).write 1568
    sevm.caller.toB256.toBytes).write 1600 (Sevm.dataWord sevm (Bytes.toB256 [4])).toBytes

/-- **After the loop, forward, exact**: `rx_rl_postW` with the burn's relation `E`, the lock's
reset at its actual `SSTORE` charge, and the final gas named to `hQ`. As `rx_rl_postW`
(`0x2f7b` → `STOP`): `token.burnFrom(msg.sender, _amount)`
answered by `BurnOkTo`, its reply length check, the `RemoveLiquidity` event (with
`total_supply - _amount` checked) and the lock cleared. -/
theorem rx_rl_postE {sevm : Sevm} {b : Devm} {Gx : Nat} {Q : Outcome → Prop} {M : Mem}
    {img : Bytes} {T : B256} {a : Nat → B256} {W W' : Devm → Prop} {U : Nat}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hWc : WClosed sevm W) (hWb : W b)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img 3 T a)
    (hTa : (rlAmt sevm).toNat ≤ T.toNat)
    (hburn : BurnOkToE sevm W W' ((b.getStor sevm.currentTarget).get tokenSlot) (rlAmt sevm) U E)
    (hGx : U + 30000 ≤ Gx) (hGb : Gx < 2 ^ 256)
    (hQ : ∀ D d, E (afterSload sevm b tokenSlot) [] (rlBurnMem sevm M) Gx d →
      d.gasLeft = D.gasLeft + 3138 +
        sstoreCost sevm d (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0]) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
      Bytes.toB256 (data.sliceD 0xc0 32 0) = T - rlAmt sevm) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M (Gx + rlPostCost sevm b)) t_2f7b_c15 Q := by
  unfold rlPostCost
  rw [show Gx + (67 + sloadCost sevm b tokenSlot) = Gx + 2 + sloadCost sevm b tokenSlot + 3 + 3 +
    3 + 7 + 3 + 3 + 3 + 6 + 3 + 2 + 9 + 3 + 3 + 3 + 3 + 3 + 2 + 2 + 1 by omega, ← tokenSlot_lit]
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x600) (c := 9) hR hW hsz rfl (by decide) ?_; intro M hM1 hR hW hsz
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x620) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM2 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x640) (c := 7) hR hW hsz rfl (by decide) ?_; intro M hM3 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [tokenSlot_lit, getStorVal_eq]
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [0x06, 0x1c] = (0x61c : B256) by decide,
    show Bytes.toB256 [0x44] = (0x44 : B256) by decide,
    show Bytes.toB256 [0x06, 0xa0] = (0x6a0 : B256) by decide,
    show Bytes.toB256 [0x20] = (0x20 : B256) by decide]
  have hin : (M.read 0x61c 0x44).1 =
      burnFromSel ++ sevm.caller.toB256.toBytes ++ (rlAmt sevm).toBytes := by
    rw [hR.read, burn_input]
  obtain ⟨d, hrun, hpost, hrd32, hrdlt, hgas, hgle, -, -, hE⟩ :=
    hburn _ [] M Gx (hWc.sload _ _ hWb) (by omega) hGb hin (by decide)
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x61c : B256).toNat = 0x61c by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0x6a0 : B256).toNat = 0x6a0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d [1] d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd]
  have hext : (M.extends [(0x61c, 0x44), (0x6a0, 0x20)]).size = 0x6c0 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz2 : d.memory.size = 0x6c0 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR2 := (hR.extends [(0x61c, 0x44), (0x6a0, 0x20)]).write (hW.extends _) 0x6a0
    (d.returnData.take 0x20)
  rw [← hmem] at hR2
  have hW2 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  clear hR hW hsz hext hmem hrun hpost
  obtain ⟨img2, hR, hI⟩ := Mem.Reads.forget hR2
  have f_T : WordAt img2 0x140 T := by rw [hI]; wchain; exact hL.supply
  clear hI hR2
  obtain ⟨G3, hG3⟩ : ∃ G3, d.gasLeft = G3 + 3 + 3 + 2917 + 3 + 3 + 3 + 2 + 6 + 3 + 2 + 3 + 2 +
      3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 7 + 3 + 3 + 3 + 6 + 3 + 3 + 3 +
      6 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 7 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 1 + 10 + 3 +
      3 + 2 + 3 + 1 + 10 + 3 := ⟨d.gasLeft - 3138, by omega⟩
  rw [hG3]
  have hgt : B256.gtCheck (Nat.toB256 d.returnData.length) (Bytes.toB256 [0x1f]) ≠ 0 := by
    apply gtCheck_ne_zero_of_lt
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrdlt,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide]
    omega
  have hlt : B256.eqCheck (B256.ltCheck T (rlAmt sevm)) 0 ≠ 0 := by
    rw [ltCheck_eq_zero_of_le hTa]; decide
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_returndatasize (by hr) ·)
  xr (rx_gt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hgt ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1e0) hR hsz2 rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x6c0) (c := 6) hR hW2 hsz2 rfl (by decide) ?_; intro M hM4 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x200) hR hsz rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x6e0) (c := 7) hR hW hsz rfl (by decide) ?_; intro M hM5 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x220) hR hsz rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x700) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM6 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x240) hR hsz rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x720) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM7 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x260) hR hsz rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x740) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM8 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x280) hR hsz rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x760) (c := 7) hR hW hsz rfl (by decide) ?_; intro M hM9 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  obtain ⟨img4, hR, hI⟩ := Mem.Reads.forget hR
  have f_T4 : WordAt img4 0x140 T := by rw [hI]; wchain; exact f_T
  clear hI
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·)
  rw [f_T4.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hlt ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x780) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM10 hR hW hsz
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_log2 (c := 2917) hstatic (by rw [St.extCost_eq hsz]; decide) rfl
    (read_covered_len hsz (by decide) (by decide)) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_sstoreX hfork hstatic (by omega) ?_
  intro G' hG'
  refine ⟨_, .last rfl, hQ _ d (by rw [hM3, hM2, hM1] at hE; exact hE) (by
    have e : ∀ l : Log, sstoreCost sevm (d.addLog l) (Bytes.toB256 [255, 255, 255])
        (Bytes.toB256 [0]) = sstoreCost sevm d (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0]) :=
      fun _ => rfl
    rw [e] at hG'
    change d.gasLeft = G' + 3138 + _
    omega) ⟨_, _, _, (afterSstore_logs _ _ _ _).trans rfl, ?_⟩⟩
  rw [hR.read, Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by decide),
    show (Bytes.toB256 [0x06, 0xc0]).toNat + 0xc0 = 0x780 by decide]
  exact (congrArg Bytes.toB256 (WordAt.write_self _ _ _)).trans (B256.toB256_toBytes _)

/-- **After the loop, forward** (`0x2f7b` → `STOP`): `token.burnFrom(msg.sender, _amount)`
answered by `BurnOkTo`, its reply length check, the `RemoveLiquidity` event (with
`total_supply - _amount` checked) and the lock cleared. -/
theorem rx_rl_postW {sevm : Sevm} {b : Devm} {Gx : Nat} {Q : Outcome → Prop} {M : Mem}
    {img : Bytes} {T : B256} {a : Nat → B256} {W W' : Devm → Prop} {U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hWc : WClosed sevm W) (hWb : W b)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img 3 T a)
    (hTa : (rlAmt sevm).toNat ≤ T.toNat)
    (hburn : BurnOkTo sevm W W' ((b.getStor sevm.currentTarget).get tokenSlot) (rlAmt sevm) U)
    (hGx : U + 30000 ≤ Gx) (hGb : Gx < 2 ^ 256)
    (hQ : ∀ D, (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
      Bytes.toB256 (data.sliceD 0xc0 32 0) = T - rlAmt sevm) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M (Gx + rlPostCost sevm b)) t_2f7b_c15 Q :=
  rx_rl_postE hfork hstatic hWc hWb hR hW hsz hL hTa hburn.withE hGx hGb
    fun D _ _ _ h => hQ D h

/-- `rlS1CostA` is at most `30000`. -/
theorem rlS1CostA_le (sevm : Sevm) (b : Devm) (i : Nat) (B T : B256) :
    rlS1CostA sevm b i B T ≤ 30000 := by
  unfold rlS1CostA
  have h1 := sloadCost_le sevm b (balancesBase + Nat.toB256 i)
  have h2 := sloadCost_le sevm (afterSload sevm b (balancesBase + Nat.toB256 i))
    (balancesBase + Nat.toB256 i)
  have h3 := sstoreCost_le_22100 sevm (afterSload sevm (afterSload sevm b
    (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)
    (B - B * rlAmt sevm / T)
  have e : gasColdSload = 2100 := rfl
  omega

/-- **One loop iteration, forward** (variant A: head `t_2cdb_c0`, memory `0x2c0`): `balances[i]` debited
by `B * _amount / T`, the `transfer` to the caller answered by `CoinPushOkAt`, `i += 1`. At most
`U + 35000` gas is used. -/
theorem rx_rl_iterA {sevm : Sevm} {b : Devm} {G : Nat} {Q : Outcome → Prop} {M : Mem}
    {img : Bytes} {i : Nat} {T B C : B256} {a : Nat → B256} {W W' : Devm → Prop} {U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hdepth : sevm.depth ≠ 0) (hid : IdReady sevm b) (hWc : WClosed sevm W) (hWb : W b)
    (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x2c0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = B)
    (hmulw : (B256.eqCheck (B * rlAmt sevm / B) (rlAmt sevm) ||| B256.eqCheck B 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (B * rlAmt sevm / T) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck B (B * rlAmt sevm / T)) 0 ≠ 0)
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = C)
    (hpush : CoinPushOkAt sevm W W' C (B * rlAmt sevm / T) U 0x520 0x5c0)
    (hG : U + 35000 ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ b' M' img' G', W' b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
        (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T)).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 →
      LoopImg img' (i + 1) T (Function.update a i (B * rlAmt sevm / T)) →
      G ≤ G' + U + 35000 → G' ≤ G →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G') (rlNext i) Q) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M G) t_2cdb_c0 Q := by
  have hS1 := rlS1CostA_le sevm b i B T
  have hS1' : 500 ≤ rlS1CostA sevm b i B T := by unfold rlS1CostA; omega
  obtain ⟨G2, rfl⟩ : ∃ G2, G = G2 + 532 + rlS1CostA sevm b i B T :=
    ⟨G - (532 + rlS1CostA sevm b i B T), by omega⟩
  refine rx_rl_s1A hfork hstatic hi hR hW hsz hL hB hmulw hT0 hminw hlew (by omega) ?_
  intro M1 img1 hR1 hW1 hsz1 hL1 hv1
  have hWb1 := hWc.sstore _ (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T)
    (hWc.sload _ (balancesBase + Nat.toB256 i) (hWc.sload _ (balancesBase + Nat.toB256 i) hWb))
  have hid1 := ((hid.afterSload (balancesBase + Nat.toB256 i)).afterSload
    (balancesBase + Nat.toB256 i)).afterSstore (balancesBase + Nat.toB256 i)
    (B - B * rlAmt sevm / T)
  refine rx_rl_s2A hi hid1 hdepth hR1 hW1 hsz1 hL1 hv1 (by omega) (by omega) hWc hWb1 ?_
  intro b2 M2 img2 hrel hWb2 hid2 hR2 hW2 hsz2 hL2 hdata x y
  have hst2 : ∀ x, (b2.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
      (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T)).get x := by
    intro x
    rw [hrel.stor, afterSstore_getStor_self, afterSload_getStor, afterSload_getStor]
  have hC2 : (b2.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = C := by
    rw [hst2, Stor.get_set_ne _ (by rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
      decide), hC]
  have hS3 : rlS3Cost sevm b2 i ≤ 2208 := by
    unfold rlS3Cost
    have := sloadCost_le sevm b2 (coinsBase + Nat.toB256 i)
    have e : gasColdSload = 2100 := rfl
    omega
  have hS3' : 108 ≤ rlS3Cost sevm b2 i := by unfold rlS3Cost; omega
  obtain ⟨Gx, hGx⟩ : ∃ Gx, G2 = Gx + rlS3Cost sevm b2 i := ⟨G2 - rlS3Cost sevm b2 i, by omega⟩
  rw [hGx]
  refine rx_rl_s3 hfork hi hdepth hid2 hWc hWb2 hW'c hR2 hW2 hsz2 (Or.inl rfl) hL2 hdata hC2 hpush
    (by omega) (by omega) ?_ x y
  intro b' M' img' G' hWb' hid' hst' hR' hW' hsz' hL' hg1 hg2
  exact k b' M' img' G' hWb' hid' (fun x => (hst' x).trans (hst2 x)) hR' hW' hsz' hL'
    (by omega) (by omega)

/-- `rlS1CostB` is at most `30000`. -/
theorem rlS1CostB_le (sevm : Sevm) (b : Devm) (i : Nat) (B T : B256) :
    rlS1CostB sevm b i B T ≤ 30000 := by
  unfold rlS1CostB
  have h1 := sloadCost_le sevm b (balancesBase + Nat.toB256 i)
  have h2 := sloadCost_le sevm (afterSload sevm b (balancesBase + Nat.toB256 i))
    (balancesBase + Nat.toB256 i)
  have h3 := sstoreCost_le_22100 sevm (afterSload sevm (afterSload sevm b
    (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)
    (B - B * rlAmt sevm / T)
  have e : gasColdSload = 2100 := rfl
  omega

/-- **One loop iteration, forward** (variant B: head `t_2cdb_c46`, memory `0x5e0`): `balances[i]` debited
by `B * _amount / T`, the `transfer` to the caller answered by `CoinPushOkAt`, `i += 1`. At most
`U + 35000` gas is used. -/
theorem rx_rl_iterB {sevm : Sevm} {b : Devm} {G : Nat} {Q : Outcome → Prop} {M : Mem}
    {img : Bytes} {i : Nat} {T B C : B256} {a : Nat → B256} {W W' : Devm → Prop} {U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hdepth : sevm.depth ≠ 0) (hid : IdReady sevm b) (hWc : WClosed sevm W) (hWb : W b)
    (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = B)
    (hmulw : (B256.eqCheck (B * rlAmt sevm / B) (rlAmt sevm) ||| B256.eqCheck B 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (B * rlAmt sevm / T) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck B (B * rlAmt sevm / T)) 0 ≠ 0)
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = C)
    (hpush : CoinPushOkAt sevm W W' C (B * rlAmt sevm / T) U 0x520 0x5c0)
    (hG : U + 35000 ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ b' M' img' G', W' b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
        (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T)).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 →
      LoopImg img' (i + 1) T (Function.update a i (B * rlAmt sevm / T)) →
      G ≤ G' + U + 35000 → G' ≤ G →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G') (rlNext i) Q) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M G) t_2cdb_c46 Q := by
  have hS1 := rlS1CostB_le sevm b i B T
  have hS1' : 500 ≤ rlS1CostB sevm b i B T := by unfold rlS1CostB; omega
  obtain ⟨G2, rfl⟩ : ∃ G2, G = G2 + 482 + rlS1CostB sevm b i B T :=
    ⟨G - (482 + rlS1CostB sevm b i B T), by omega⟩
  refine rx_rl_s1B hfork hstatic hi hR hW hsz hL hB hmulw hT0 hminw hlew (by omega) ?_
  intro M1 img1 hR1 hW1 hsz1 hL1 hv1
  have hWb1 := hWc.sstore _ (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T)
    (hWc.sload _ (balancesBase + Nat.toB256 i) (hWc.sload _ (balancesBase + Nat.toB256 i) hWb))
  have hid1 := ((hid.afterSload (balancesBase + Nat.toB256 i)).afterSload
    (balancesBase + Nat.toB256 i)).afterSstore (balancesBase + Nat.toB256 i)
    (B - B * rlAmt sevm / T)
  refine rx_rl_s2B hi hid1 hdepth hR1 hW1 hsz1 hL1 hv1 (by omega) (by omega) hWc hWb1 ?_
  intro b2 M2 img2 hrel hWb2 hid2 hR2 hW2 hsz2 hL2 hdata x y
  have hst2 : ∀ x, (b2.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
      (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T)).get x := by
    intro x
    rw [hrel.stor, afterSstore_getStor_self, afterSload_getStor, afterSload_getStor]
  have hC2 : (b2.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = C := by
    rw [hst2, Stor.get_set_ne _ (by rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
      decide), hC]
  have hS3 : rlS3Cost sevm b2 i ≤ 2208 := by
    unfold rlS3Cost
    have := sloadCost_le sevm b2 (coinsBase + Nat.toB256 i)
    have e : gasColdSload = 2100 := rfl
    omega
  have hS3' : 108 ≤ rlS3Cost sevm b2 i := by unfold rlS3Cost; omega
  obtain ⟨Gx, hGx⟩ : ∃ Gx, G2 = Gx + rlS3Cost sevm b2 i := ⟨G2 - rlS3Cost sevm b2 i, by omega⟩
  rw [hGx]
  refine rx_rl_s3 hfork hi hdepth hid2 hWc hWb2 hW'c hR2 hW2 hsz2 (Or.inr rfl) hL2 hdata hC2 hpush
    (by omega) (by omega) ?_ x y
  intro b' M' img' G' hWb' hid' hst' hR' hW' hsz' hL' hg1 hg2
  exact k b' M' img' G' hWb' hid' (fun x => (hst' x).trans (hst2 x)) hR' hW' hsz' hL'
    (by omega) (by omega)

/-! ## The whole frame -/

theorem rlPreCost_le (sevm : Sevm) (b : Devm) : rlPreCost sevm b ≤ 26389 := by
  unfold rlPreCost
  have h1 := sloadCost_le sevm b (Bytes.toB256 [0xff, 0xff, 0xff])
  have h2 := sstoreCost_le_22100 sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
    (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])
  have h3 := sloadCost_le sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
    (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (Bytes.toB256 [5])
  have e : gasColdSload = 2100 := rfl
  omega

/-- **`remove_liquidity`, the whole frame forward.** From the frame's entry (empty stack and
memory) with the `remove_liquidity` selector, the lock clear, no value, every check of the
model passing on the entry storage `σ` and the supply `T`, and the callees answering along a
world chain `W 0 → W 1 → W 2 → W 3 → W 4` (`SupplyOk` in `W 0`, coin `i`'s transfer with its
amount from `W i` to `W (i + 1)`, the burn from `W 3` to `W 4`: the burn is the last call, so
nothing after it reads `W 4`), every gas
`G ≥ 167000 + 5 U` runs the frame to `STOP`, whose last log carries `T - _amount`. -/
theorem rx_rl_frame {sevm : Sevm} {b : Devm} {σ : Stor} {G : Nat} {Q : Outcome → Prop}
    {W : Nat → Devm → Prop} {U : Nat} {T : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity) (hid : IdReady sevm b)
    (hσ : b.getStor sevm.currentTarget = σ) (hlock : σ.get lockSlot = 0) (hval : sevm.value = 0)
    (hWc : ∀ k, k ≤ 3 → WClosed sevm (W k)) (hWb : W 0 b)
    (hsup : SupplyOk sevm (W 0) (σ.get tokenSlot) T U)
    (hpush : ∀ i, i < 3 → CoinPushOkAt sevm (W i) (W (i + 1)) (coinAt σ i)
      (balAt σ i * rlAmt sevm / T) U 0x520 0x5c0)
    (hburn : BurnOkTo sevm (W 3) (W 4) (σ.get tokenSlot) (rlAmt sevm) U)
    (hmulw : ∀ i, i < 3 →
      (B256.eqCheck (balAt σ i * rlAmt sevm / balAt σ i) (rlAmt sevm) ||| B256.eqCheck (balAt σ i) 0)
        ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : ∀ i, i < 3 →
      B256.eqCheck (B256.ltCheck (balAt σ i * rlAmt sevm / T) (rlMin sevm i)) 0 ≠ 0)
    (hlew : ∀ i, i < 3 → B256.eqCheck (B256.ltCheck (balAt σ i) (balAt σ i * rlAmt sevm / T)) 0 ≠ 0)
    (hTa : (rlAmt sevm).toNat ≤ T.toNat)
    (hG : 167000 + 5 * U ≤ G) (hGb : G < 2 ^ 256)
    (hQ : ∀ D, (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
      Bytes.toB256 (data.sliceD 0xc0 32 0) = T - rlAmt sevm) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b [] Mem.empty G) t_0000_c0 Q := by
  subst hσ
  obtain ⟨G0, rfl⟩ : ∃ G0, G = G0 + 451 := ⟨G - 451, by omega⟩
  refine rx_dispatch_rl hlen hcd hsel ?_
  have hpc := rlPreCost_le sevm b
  obtain ⟨Gs, rfl⟩ : ∃ Gs, G0 = Gs + rlPreCost sevm b := ⟨G0 - rlPreCost sevm b, by omega⟩
  refine rx_rl_pre (T := T) hfork hstatic hcd hlock hval (hWc 0 (by decide)) hWb hsup (by omega) (by omega)
    (by omega) ?_
  intro b1 M1 img1 G1 hWb1 hid1 hst1 _ _ hR1 hW1 hsz1 hL1 hg1 hg1'
  have hs1 : ∀ x, lockSlot ≠ x →
      (b1.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x :=
    fun x hx => by rw [hst1, Stor.get_set_ne _ hx]
  -- iteration 0
  refine rx_rl_iterA (i := 0) (B := balAt (b.getStor sevm.currentTarget) 0)
    (C := coinAt (b.getStor sevm.currentTarget) 0) hfork hstatic (by decide) hdepth (hid1 hid)
    (hWc 0 (by decide)) hWb1 (hWc 1 (by decide)) hR1 hW1 hsz1 hL1 (hs1 _ (by decide)) (hmulw 0 (by decide)) hT0 (hminw 0 (by decide))
    (hlew 0 (by decide)) (hs1 _ (by decide)) (hpush 0 (by decide)) (by omega) (by omega) ?_
  intro b2 M2 img2 G2 hWb2 hid2 hst2 hR2 hW2 hsz2 hL2 hg2 hg2'
  rw [show rlNext 0 = t_2cdb_c46 by unfold rlNext; rfl]
  have hs2 : ∀ x, lockSlot ≠ x → balancesBase + Nat.toB256 0 ≠ x →
      (b2.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x :=
    fun x hx hx0 => by rw [hst2, Stor.get_set_ne _ hx0, hs1 _ hx]
  -- iteration 1
  refine rx_rl_iterB (i := 1) (B := balAt (b.getStor sevm.currentTarget) 1)
    (C := coinAt (b.getStor sevm.currentTarget) 1) hfork hstatic (by decide) hdepth hid2
    (hWc 1 (by decide)) hWb2 (hWc 2 (by decide)) hR2 hW2 hsz2 hL2 (hs2 _ (by decide) (by decide)) (hmulw 1 (by decide)) hT0
    (hminw 1 (by decide)) (hlew 1 (by decide)) (hs2 _ (by decide) (by decide))
    (hpush 1 (by decide)) (by omega) (by omega) ?_
  intro b3 M3 img3 G3 hWb3 hid3 hst3 hR3 hW3 hsz3 hL3 hg3 hg3'
  rw [show rlNext 1 = t_2cdb_c46 by unfold rlNext; rfl]
  have hs3 : ∀ x, lockSlot ≠ x → balancesBase + Nat.toB256 0 ≠ x → balancesBase + Nat.toB256 1 ≠ x →
      (b3.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x :=
    fun x hx hx0 hx1 => by rw [hst3, Stor.get_set_ne _ hx1, hs2 _ hx hx0]
  -- iteration 2
  refine rx_rl_iterB (i := 2) (B := balAt (b.getStor sevm.currentTarget) 2)
    (C := coinAt (b.getStor sevm.currentTarget) 2) hfork hstatic (by decide) hdepth hid3
    (hWc 2 (by decide)) hWb3 (hWc 3 (by decide)) hR3 hW3 hsz3 hL3 (hs3 _ (by decide) (by decide) (by decide)) (hmulw 2 (by decide)) hT0
    (hminw 2 (by decide)) (hlew 2 (by decide)) (hs3 _ (by decide) (by decide) (by decide))
    (hpush 2 (by decide)) (by omega) (by omega) ?_
  intro b4 M4 img4 G4 hWb4 hid4 hst4 hR4 hW4 hsz4 hL4 hg4 hg4'
  rw [show rlNext 2 = t_2f7b_c15 by unfold rlNext; rfl]
  have htok : (b4.getStor sevm.currentTarget).get tokenSlot = (b.getStor sevm.currentTarget).get tokenSlot := by
    rw [hst4, Stor.get_set_ne _ (by decide), hs3 _ (by decide) (by decide) (by decide)]
  have hpo : rlPostCost sevm b4 ≤ 2167 := by
    unfold rlPostCost
    have := sloadCost_le sevm b4 tokenSlot
    have e : gasColdSload = 2100 := rfl
    omega
  obtain ⟨Gx, rfl⟩ : ∃ Gx, G4 = Gx + rlPostCost sevm b4 := ⟨G4 - rlPostCost sevm b4, by omega⟩
  exact rx_rl_postW hfork hstatic (hWc 3 (by decide)) hWb4 hR4 hW4 hsz4 hL4 hTa (by rw [htok]; exact hburn)
    (by omega) (by omega) hQ

end Blanc.Lift.Curve3Pool

