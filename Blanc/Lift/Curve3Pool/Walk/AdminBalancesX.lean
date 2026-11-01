import Blanc.Lift.Curve3Pool.Walk.Dispatch
import Blanc.Lift.Curve3Pool.Walk.AdminBalances
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLoop
import Blanc.Lift.Curve3Pool.Spec
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `admin_balances`, on the actual derivation

From the frame's entry with the `admin_balances` selector the dispatcher reaches the arm's
body (`0x4c93`, past its test at `0x4c85`): the non-payable guard, the `balanceOf(self)`
staging at `0x140`/`0x160`, the `i < 3` check, the `coins[i]` load at `keccak(0) + i`, one
`STATICCALL` with the output window `0x1c0`, the flag and `RETURNDATASIZE > 31` asserts, the
second `i < 3` check, the `balances[i]` load at `keccak(1) + i`, the coverage assert, and the
difference returned.

`xa_adminBalances` is the frame theorem: a successful frame found no value, spawned exactly
one direct child (coin `k`'s `balanceOf(self)`, static, at least 32 bytes back), left storage
and logs as the child left them, and returned `w - balances[k]`. `adminBalances_raw` is the
`<entry>_raw` safety: the model's step on the decoded call with the `RawEffect` Spec states.

Reuse: the `xs`/`xji`/`xjd`/`xdead` walk macros and `xa_staticcall_img`, `WordAt`/`Region`,
`wchain` from `Blanc/Lift/FrameWalkKit.lean` via `Walk.Kit`; `balEnv`, `adminBalances_step`,
`ri_address` from the lifted-program walk `Walk.AdminBalances`; `EnvOf`/`ReplyAt` from
`Observe.lean`; `RawEffect`/`StorEffect` from `Spec.lean`; the dispatcher walk `xa_dispatch`
from `Walk.Dispatch`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-! ## The `balanceOf` calldata in the image -/

theorem adminBal_sel_bytes :
    (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes = List.replicate 28 0 ++ balanceOfSel := by
  decide

/-- The `balanceOf(self)` calldata the staging writes leave at `0x15c` (the later zero word at
`0xc0` is disjoint from the window). -/
theorem adminBal_input (img : Bytes) (self : Adr) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x140
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x160 self.toB256.toBytes) 0xc0
      (Bytes.toB256 [0]).toBytes).sliceD 0x15c 0x24 0) = balanceOfData self := by
  show ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x140
    (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x160 self.toB256.toBytes) 0xc0
    (Bytes.toB256 [0]).toBytes).sliceD 0x15c 0x24 0) = balanceOfSel ++ self.toB256.toBytes
  have hsel : Region (Bytes.writeAt img 0x140 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes)
      0x15c balanceOfSel := by
    have := Region.write_self img 0x140 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
    rw [adminBal_sel_bytes] at this
    exact this.right
  have hsel2 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x140
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x160 self.toB256.toBytes) 0xc0
      (Bytes.toB256 [0]).toBytes) 0x15c balanceOfSel :=
    Region.write_other
      (Region.write_other hsel (by simp only [balanceOfSel, B256.length_toBytes,
        List.length_cons, List.length_nil]; omega)) (Or.inr (by decide))
  refine Region.slice (Region.append' (o' := 0x160) ?_ ?_ (by rfl))
    (by simp only [balanceOfSel, List.length_append, B256.length_toBytes, List.length_cons,
      List.length_nil])
  · exact hsel2
  · exact Region.write_other (Region.write_self _ _ _) (Or.inr (by decide))

/-- The answer word the `STATICCALL` wrote at `0x1c0` reads back. -/
theorem adminBal_read_ans (img : Bytes) (out : Bytes) (hlen : (out.take 32).length = 32) :
    Bytes.toB256 ((Bytes.writeAt img 0x1c0 (out.take 32)).sliceD 0x1c0 32 0) =
      Bytes.toB256 (out.take 32) :=
  Region.read (Region.write_self img 0x1c0 (out.take 32)) hlen

/-! ## The arm's body -/

/-- **The `admin_balances` body** (`0x4c93` → `RETURN`): no value; one static child (coin `k`'s
`balanceOf(self)`, at least 32 bytes back); storage kept; logs the child's; the difference
returned. -/
theorem adminBal_body {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcoin : ∀ i, i < 3 → ¬ sevm.benvStat.rules.isPrecomp
      (((b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i)).toAdr))
    (h : XAt sevm post 0x4c93 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    sevm.value = 0 ∧
    ∃ (k : Fin 3) (c : Exec.Frame) (out : Bytes),
      L = [c] ∧
      (Sevm.argWord sevm 0).toNat = k.val ∧
      c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr ∧
      c.sevm.data = balanceOfData sevm.currentTarget ∧
      c.sevm.isStatic = true ∧
      c.post.output = out ∧ 32 ≤ out.length ∧
      c.post.logs = [] ∧
      (∀ x, (post.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) ∧
      post.logs = b.logs ++ c.post.logs ∧
      post.output = ((Bytes.toB256 (out.take 32)) -
        (b.getStor sevm.currentTarget).get (balanceSlot k)).toBytes ∧
      ((b.getStor sevm.currentTarget).get (balanceSlot k)).toNat ≤
        (Bytes.toB256 (out.take 32)).toNat := by
  have hR : Mem.Reads (vyMem Mem.empty (Sevm.dataWord sevm 0))
      (vyImg [] (Sevm.dataWord sevm 0)) :=
    vyMem_reads Mem.wf_empty Mem.reads_empty _
  have hW : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  xa 3
  xji 0x4c99 0x4c9d hw
  · xdead
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 6
  xmo 0x4cae (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  xa 2
  xmo 0x4cb3 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  xa 7
  xji 0x4cc1 0x4cc5 hw
  · xdead
  have hlt : Sevm.dataWord sevm (Bytes.toB256 [4]) < Bytes.toB256 [3] := by
    by_contra hcon
    exact absurd (ite_eq_right hcon) hw
  clear hw
  have hltN : (Sevm.dataWord sevm (Bytes.toB256 [4])).toNat < 3 := by
    rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [3]).toNat = 3 by decide] at hlt
    exact hlt
  obtain ⟨k, hk_def⟩ : ∃ k : Fin 3, k.val = (Sevm.dataWord sevm (Bytes.toB256 [4])).toNat :=
    ⟨⟨_, hltN⟩, rfl⟩
  have hargv : Sevm.dataWord sevm (Bytes.toB256 [4]) = Nat.toB256 k.val := by
    apply B256.toNat_inj
    rw [hk_def, B256.toNat_toB256_of_lt (by omega)]
  have hslot : coinsBase + Sevm.dataWord sevm (Bytes.toB256 [4]) = coinSlot k := by
    rw [hargv]; rfl
  xa 3
  xmo 0x4ccb (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xa 2
  xmo 0x4cd0 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x4cd1 (.reg .add) ri_add
  rw [hslot] at h
  xw 0x4cd2 (.reg .sload) ri_sload
  rw [getStorVal_eq] at h
  xs 0x4cd3 (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_img (pc' := 0x4cd4) (i := 0x15c) (n := 0x24) (o := 0x1c0)
    (z := 0x20) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M', L1, h, _, hR, hW, hrd, hob, hstor1, hlogs1, hk⟩ := h
  xs 0x4cd7 (.push [0x4c, 0xdc] (by decide)) ri_push
  xji 0x4cd8 0x4cdc hw
  · xdead
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, -, -, -, -, htgt, hdata, hstat, hout, hclogs, -, -⟩
  · exact absurd hpre (hcoin k.val k.isLt)
  clear hk hw
  rw [adminBal_input] at hdata
  xa 5
  xji 0x4ce5 0x4ce9 hw
  · xdead
  have hlen32 : 32 ≤ out.length := by
    have hgt := B256.lt_of_gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, hrd, B256.toNat_toB256_of_lt hob,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at hgt
    omega
  clear hw
  xa 4
  xmo 0x4cf1 (.reg .mload) (ri_mload_imgAt (o := 0x1c0) rfl)
  have hlen : (out.take 32).length = 32 := by rw [List.length_take]; omega
  rw [adminBal_read_ans _ _ hlen] at h
  clear hlen
  xa 6
  xji 0x4cfc 0x4d00 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt hlt)
  clear hw
  xa 3
  xmo 0x4d06 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xa 2
  xmo 0x4d0b (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x4d0c (.reg .add) ri_add
  have hslot2 : balancesBase + Sevm.dataWord sevm (Bytes.toB256 [4]) = balanceSlot k := by
    rw [hargv]; rfl
  rw [hslot2] at h
  xw 0x4d0d (.reg .sload) ri_sload
  rw [getStorVal_eq, hstor1, afterSload_getStor] at h
  xa 5
  xji 0x4d15 0x4d19 hw
  · xdead
  have hle : ((b.getStor sevm.currentTarget).get (balanceSlot k)).toNat ≤
      (Bytes.toB256 (out.take 32)).toNat := by
    have hne := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    exact B256.le_iff_toNat_le_toNat.mp (not_lt.mp hne)
  clear hw
  xa 9
  xmo 0x4d24 (.reg .mstore) (ri_mstore_imgAt (o := 0) rfl)
  xa 2
  obtain ⟨hrun, hL1⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  simp only [Linst.Run, Linst.run] at hrun
  rw [Devm.popToNat_eq_ok (devm := _) rfl] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨idx, dA⟩, hpop1, hrun⟩
  obtain ⟨rfl, rfl⟩ := Except.ok.inj hpop1
  dsimp only at hrun
  rw [Devm.popToNat_eq_ok (devm := _) rfl] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨sz, dB⟩, hpop2, hrun⟩
  obtain ⟨rfl, rfl⟩ := Except.ok.inj hpop2
  rcases Except.bind_eq_ok hrun with ⟨dC, hchg, hrun⟩
  dsimp only at hrun
  simp only [chargeGas_def] at hchg
  split at hchg
  · cases hchg
  · rename_i gas hsafe
    injection hchg with hdv
    subst hdv
    injection hrun with hpost
    have harg0 : Sevm.argWord sevm 0 = Sevm.dataWord sevm (Bytes.toB256 [4]) := by
      unfold Sevm.argWord
      rw [show (32 * (0 : B256) + 4 : B256) = Bytes.toB256 [4] by decide]
    have hout_post : post.output =
        ((Bytes.toB256 (out.take 32)) -
          (b.getStor sevm.currentTarget).get (balanceSlot k)).toBytes := by
      rw [← hpost, Devm.withOutput_output]
      show (M.read 0 32).1 = _
      rw [Mem.Reads.read hR 0 32]
      exact Region.slice (Region.write_self _ _ _) (by simp only [B256.length_toBytes])
    have hlogs_post : post.logs = b.logs ++ c.post.logs := by
      rw [← hpost, Devm.withOutput_logs, Devm.memRead_logs]
      show (afterSload sevm d1 (balanceSlot k)).logs = b.logs ++ c.post.logs
      rw [afterSload_logs, hlogs1, afterSload_logs, hclogs, List.append_nil]
    have hstor_post : ∀ x, (post.getStor sevm.currentTarget).get x =
        (b.getStor sevm.currentTarget).get x := by
      intro x
      rw [← hpost]
      show ((afterSload sevm d1 (balanceSlot k)).getStor _).get x = _
      rw [afterSload_getStor, hstor1, afterSload_getStor]
    rw [hL1] at hL
    refine ⟨hval, k, c, out, hL, ?_, htgt, hdata, hstat, hout, hlen32, hclogs, hstor_post,
      hlogs_post, hout_post, hle⟩
    rw [harg0]
    exact hk_def.symm

/-! ## The frame theorem -/

/-- **The `admin_balances` frame**: from the frame's start, past the dispatcher, the body ran:
no value; one static child (coin `k`'s `balanceOf(self)`, at least 32 bytes back); storage
kept; logs the child's; the difference returned. -/
theorem xa_adminBalances {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAdminBalances)
    (hcoin : ∀ i, i < 3 → ¬ sevm.benvStat.rules.isPrecomp
      (((b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i)).toAdr))
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    sevm.value = 0 ∧
    ∃ (k : Fin 3) (c : Exec.Frame) (out : Bytes),
      L = [c] ∧
      (Sevm.argWord sevm 0).toNat = k.val ∧
      c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr ∧
      c.sevm.data = balanceOfData sevm.currentTarget ∧
      c.sevm.isStatic = true ∧
      c.post.output = out ∧ 32 ≤ out.length ∧
      c.post.logs = [] ∧
      (∀ x, (post.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) ∧
      post.logs = b.logs ++ c.post.logs ∧
      post.output = ((Bytes.toB256 (out.take 32)) -
        (b.getStor sevm.currentTarget).get (balanceSlot k)).toBytes ∧
      ((b.getStor sevm.currentTarget).get (balanceSlot k)).toNat ≤
        (Bytes.toB256 (out.take 32)).toNat := by
  obtain ⟨G3, h⟩ := xa_dispatch (q := 0x4c93) hcode hlen hcd hsel h
  exact adminBal_body hcode hfork hcoin h

/-- The environment an `admin_balances` frame observed: coin `k`'s one `balanceOf(self)`
answer `w` (as the pre-call read; there is no second call, so no post-call read), nothing
else. (`balEnv`'s `balPost = some` would demand two ordered replies for one child, which no
single-`STATICCALL` frame can give; the transition reads `balPre` only.) -/
def adminBal_env (sevm : Sevm) (k : Fin 3) (w : Nat) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun j => if j = k then ⟨some w, none, false, false⟩ else ⟨none, none, false, false⟩,
    none, false, false⟩

/-- The model's `admin_balances(i)` under the frame's one answer. -/
theorem adminBal_step {sevm : Sevm} {s : State} (hv : sevm.value = 0) (k : Fin 3)
    (hk : arg sevm 0 = k.val) (w : Nat) (hle : s.balances.get k ≤ w) :
    step s (adminBal_env sevm k w) (.adminBalances (arg sevm 0)) =
      some (viewOut s (w - s.balances.get k)) := by
  have hv' : (adminBal_env sevm k w).value = 0 := by
    show sevm.value.toNat = 0
    rw [hv]; rfl
  have hidx : idx (arg sevm 0) = some k := by
    rw [hk, idx, dite_eq_left k.isLt]
  have hif : (if sevm.value.toNat = 0 then some (viewOut s (w - s.balances.get k))
      else none) = some (viewOut s (w - s.balances.get k)) := by
    rw [show sevm.value.toNat = 0 from hv']; rfl
  simp only [step, body, hif, ite_true, hidx, adminBalances, adminBal_env, ite_true,
    StableSwapNewton.chkSub, hle, bind, Option.bind]

/-- **Safety of `admin_balances`.** A successful frame of the pool's runtime on the
`admin_balances` selector, entered at a `Checkpoint` with empty stack and memory, under the
frame premises (no coin is a precompile), computed the model's step on the decoded call in
the environment `adminBal_env` it observed, with the raw effect Spec states. -/
theorem adminBalances_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAdminBalances)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      (((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨hval, k, c, out, hL, harg, htgt, hdata, hstat, hout, hlen32, hclogs, hstorF, hlogsF,
    houtF, hleW⟩ :=
    xa_adminBalances hcode hfork hlen hcd hsel (fun i hi => hcoin ⟨i, hi⟩) hx
  have hdec : decodeCall sevm = .adminBalances (arg sevm 0) :=
    decodeCall_at (k := 19) rfl hsel hlen
  have harg0 : arg sevm 0 = k.val := harg
  have hidx : idx (arg sevm 0) = some k := by
    rw [harg0, idx, dite_eq_left k.isLt]
  have hbal : s.balances.get k = ((pre.getStor sevm.currentTarget).get (balanceSlot k)).toNat :=
    (hck.abs.balances k).symm
  have hleM : s.balances.get k ≤ answerWord out := by
    rw [hbal]
    exact hleW
  have hstep := adminBal_step hval k harg0 (answerWord out) hleM
  have hchildren : children ⟨0, sevm, pre, .ok post, exc⟩ = [c] := hL
  refine ⟨adminBal_env sevm k (answerWord out),
    viewOut s (answerWord out - s.balances.get k), ?step, ?raw⟩
  case step =>
    rw [hdec]
    exact hstep
  case raw =>
    have hreply : ReplyAt ⟨0, sevm, pre, .ok post, exc⟩ 0
        ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr
        (balanceOfData sevm.currentTarget) (answerWord out) := by
      refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hchildren]; rfl
      · exact htgt
      · exact hdata
      · rw [hout]; exact hlen32
      · rw [hout]
    refine ⟨?env, ?stor, ?logs, ?output, ?calls⟩
    case env =>
      refine ⟨rfl, rfl, rfl, fun j => ?_, fun T h => (by cases h), fun h => (by cases h),
        fun h => (by cases h)⟩
      by_cases hj : j = k
      · subst j
        have hc : (adminBal_env sevm k (answerWord out)).coin k =
            ⟨some (answerWord out), none, false, false⟩ :=
          ite_eq_left rfl
        rw [hc]
        refine ⟨fun w' h => ?_, fun w' h => (by cases h), fun h => (by cases h),
          fun h => (by cases h)⟩
        have hw' : answerWord out = w' := Option.some_inj.mp h
        subst hw'
        exact Or.inr ⟨0, hreply⟩
      · have hc : (adminBal_env sevm k (answerWord out)).coin j =
            ⟨none, none, false, false⟩ := by
          show (if j = k then (⟨some (answerWord out), none, false, false⟩ : CoinObs)
            else ⟨none, none, false, false⟩) = _
          rw [ite_eq_right hj]
        rw [hc]
        exact ⟨fun w' h => (by cases h), fun w' h => (by cases h), fun h => (by cases h),
          fun h => (by cases h)⟩
    case stor =>
      show StorEffect (decodeCall sevm) (pre.getStor sevm.currentTarget)
        (post.getStor sevm.currentTarget)
        (viewOut s (answerWord out - s.balances.get k)).state
      rw [hdec]
      refine ⟨fun x _ => hstorF x, fun f hf => ?_⟩
      rw [show footprint (.adminBalances (arg sevm 0)) = [] from rfl] at hf
      cases hf
    case logs =>
      rw [hlogsF, hchildren]
      simp only [viewOut, List.flatMap_cons, List.flatMap_nil, List.map_nil, List.append_nil]
    case output =>
      have hsub : (Bytes.toB256 (out.take 32) -
          (pre.getStor sevm.currentTarget).get (balanceSlot k)).toNat =
          answerWord out - s.balances.get k := by
        rw [B256.toNat_sub_eq_of_le _ _
          (B256.le_iff_toNat_le_toNat.mpr (by simpa only [hbal, answerWord] using hleM)),
          hbal, answerWord]
      have hword : (Bytes.toB256 (out.take 32) -
          (pre.getStor sevm.currentTarget).get (balanceSlot k)) =
          Nat.toB256 (answerWord out - s.balances.get k) := by
        apply B256.toNat_inj
        rw [hsub, B256.toNat_toB256_of_lt (by
          have h256 : answerWord out < 2 ^ 256 := B256.toNat_lt _
          omega)]
      rw [houtF]
      simp only [retOut, word]
      exact congrArg B256.toBytes hword
    case calls =>
      intro hs
      have hcallsL : CallsOf ⟨0, sevm, pre, .ok post, exc⟩ = [] := by
        rw [CallsOf, hchildren]
        simp only [List.filterMap_cons, List.filterMap_nil, hstat, ↓reduceIte]
      have hcallsR : modelCalls ⟨0, sevm, pre, .ok post, exc⟩
          (viewOut s (answerWord out - s.balances.get k)).calls = [] := by
        simp only [modelCalls, viewOut, List.map_nil, List.filter_nil]
      rw [hcallsL, hcallsR]

end Blanc.Lift.Curve3Pool
