import Blanc.Lift.Curve3Pool.Safe
import Blanc.Lift.StableSwapNewton.Y

/-!
# Curve 3pool: the U4 `get_y_D` and `get_y` laws at the bytecode frames (goal §12, design §4)

The model laws `getYDChk_rootOrSucc` and `getYChk_rootOrSucc` (`StableSwapNewton/Y.lean`) say that
every successful checked `get_y_D` / `get_y` call returns the floor root `r` of its
floored-coefficient quadratic or `r + 1`, and `r + 1` only off `rootGap`.  Here they are linked to the
deployed bytecode: a successful frame refines the model with its raw effect *and* its internal
callee call returned a word `y` on the words the bytecode passed, at the frame's observed
environment, so the law holds of that word.

* `pool_getYD_rootOrSucc_cwo` — a `calc_withdraw_one_coin` frame's first `get_y_D` call
  (`cwo_raw_getYD_of`, through `xa_cw`);
* `pool_getYD_rootOrSucc_oneCoin` — a `remove_liquidity_one_coin` frame's first `get_y_D` call
  (`removeLiquidityOneCoin_raw_getYD_of`);
* `pool_getYD2_rootOrSucc_cwo` / `pool_getYD2_rootOrSucc_oneCoin` — the second `get_y_D` call of
  the same two frames (`cwo_raw_getYD2_of`, `removeLiquidityOneCoin_raw_getYD2_of`);
* `pool_getY_rootOrSucc_exchange` — an `exchange` frame's `get_y` call (`exchange_raw_getY`);
* `pool_getY_rootOrSucc_dy` / `pool_getY_rootOrSucc_dyu` — a `get_dy` / `get_dy_underlying`
  frame's `get_y` call (`dy_raw_getY`, `dyu_raw_getY`).

Per §12 (decision `curve3pool-u4-gety-amend-trigger-20261018`) both `get_y_D` and `get_y` take the
root-or-successor form; the exact floor holds under `rootGap` (`rootOrSucc`'s second disjunct
excludes it).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.Lift Blanc.StableSwapNewton

/-- **The root-or-successor law of `_calc_withdraw_one_coin`'s first `get_y_D` call**: the words
the bytecode passed (`amp`, `xp`, `D1`, from the model's checked prefix at time `t` and supply `T`)
and the word `y` it received, which is the floor root of the floored-coefficient quadratic or its
successor. -/
def CwFirstGetYDLaw (s : State) (t a : Nat) (i : Fin 3) (T : Nat) : Prop :=
  ∃ (A x0 x1 x2 D0 D1 y : B256),
    aChk s t = some A.toNat ∧
    xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
    getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get A.toNat 1 = some D0.toNat ∧
    ((chkMul a D0.toNat).bind fun m => (chkDiv m T).bind fun q => chkSub D0.toNat q) =
      some D1.toNat ∧
    getYDChk A.toNat i (V3.mk x0.toNat x1.toNat x2.toNat).get D1.toNat = some y.toNat ∧
    rootOrSucc
      (cOf ((V3.mk x0.toNat x1.toNat x2.toNat).get (others i).1)
        ((V3.mk x0.toNat x1.toNat x2.toNat).get (others i).2) D1.toNat (A.toNat * 3))
      (bOf ((V3.mk x0.toNat x1.toNat x2.toNat).get (others i).1)
        ((V3.mk x0.toNat x1.toNat x2.toNat).get (others i).2) D1.toNat (A.toNat * 3))
      D1.toNat y.toNat

theorem cwFirstGetYD_law {s : State} {t a : Nat} {i : Fin 3} {T : Nat}
    (h : CwFirstGetYD s t a i T) : CwFirstGetYDLaw s t a i T := by
  obtain ⟨A, x0, x1, x2, D0, D1, y, hA, hxp, hD0, hD1, hy⟩ := h
  exact ⟨A, x0, x1, x2, D0, D1, y, hA, hxp, hD0, hD1, hy, getYDChk_rootOrSucc hy⟩

/-- **The root-or-successor law of `_calc_withdraw_one_coin`'s second `get_y_D` call**: the words
the bytecode passed (`amp`, `xp_reduced = (r0, r1, r2)`, `D1`) and the word `y2` it received, which
is the floor root of the floored-coefficient quadratic on those words or its successor. -/
def CwSecondGetYDLaw (s : State) (t a : Nat) (i : Fin 3) (T : Nat) : Prop :=
  ∃ (A x0 x1 x2 D0 D1 r0 r1 r2 y2 : B256),
    aChk s t = some A.toNat ∧
    xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
    getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get A.toNat 1 = some D0.toNat ∧
    ((chkMul a D0.toNat).bind fun m => (chkDiv m T).bind fun q => chkSub D0.toNat q) =
      some D1.toNat ∧
    getYDChk A.toNat i (V3.mk r0.toNat r1.toNat r2.toNat).get D1.toNat = some y2.toNat ∧
    rootOrSucc
      (cOf ((V3.mk r0.toNat r1.toNat r2.toNat).get (others i).1)
        ((V3.mk r0.toNat r1.toNat r2.toNat).get (others i).2) D1.toNat (A.toNat * 3))
      (bOf ((V3.mk r0.toNat r1.toNat r2.toNat).get (others i).1)
        ((V3.mk r0.toNat r1.toNat r2.toNat).get (others i).2) D1.toNat (A.toNat * 3))
      D1.toNat y2.toNat

theorem cwSecondGetYD_law {s : State} {t a : Nat} {i : Fin 3} {T : Nat}
    (h : CwSecondGetYD s t a i T) : CwSecondGetYDLaw s t a i T := by
  obtain ⟨A, x0, x1, x2, D0, D1, r0, r1, r2, y2, hA, hxp, hD0, hD1, hy⟩ := h
  exact ⟨A, x0, x1, x2, D0, D1, r0, r1, r2, y2, hA, hxp, hD0, hD1, hy, getYDChk_rootOrSucc hy⟩

/-- **U4 `get_y_D` at the `calc_withdraw_one_coin` frame.**  A successful frame of the certified
runtime on the selector, entered fresh at a `Checkpoint` (its token not a precompile), refines the
model with its raw effect, and its first `get_y_D` call, at the observed environment's time and
supply, returned the floor root or its successor. -/
theorem pool_getYD_rootOrSucc_cwo {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCalcWithdrawOneCoin)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : arg sevm 1 < 3) (T : Nat), e.supply = some T ∧
        CwFirstGetYDLaw s e.time (arg sevm 0) ⟨arg sevm 1, hi⟩ T := by
  obtain ⟨e, o, hstep, hraw, hi, T, hT, hfirst⟩ :=
    cwo_raw_getYD_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck htok
  exact ⟨e, o, hstep, hraw, hi, T, hT, cwFirstGetYD_law hfirst⟩

/-- **U4 `get_y_D` at the `remove_liquidity_one_coin` frame.**  A successful frame on the
selector, entered fresh at a `Checkpoint` under the ENV bundle, refines the model with its raw
effect, and its first `get_y_D` call (inside `_calc_withdraw_one_coin`), at the observed
environment's time and supply, returned the floor root or its successor. -/
theorem pool_getYD_rootOrSucc_oneCoin {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (henv : PoolFrameEnv ⟨0, sevm, pre, .ok post, exc⟩) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : arg sevm 1 < 3) (T : Nat), e.supply = some T ∧
        CwFirstGetYDLaw s e.time (arg sevm 0) ⟨arg sevm 1, hi⟩ T := by
  obtain ⟨e, o, hstep, hraw, hi, T, hT, hfirst⟩ :=
    removeLiquidityOneCoin_raw_getYD_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas
      hck henv.htok henv.hcoin hpc henv.id henv.keep henv.hidk
  exact ⟨e, o, hstep, hraw, hi, T, hT, cwFirstGetYD_law hfirst⟩

/-- **U4 second `get_y_D` at the `calc_withdraw_one_coin` frame.**  A successful frame of the certified
runtime on the selector, entered fresh at a `Checkpoint` (its token not a precompile), refines the
model with its raw effect, and its first `get_y_D` call, at the observed environment's time and
supply, returned the floor root or its successor. -/
theorem pool_getYD2_rootOrSucc_cwo {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCalcWithdrawOneCoin)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : arg sevm 1 < 3) (T : Nat), e.supply = some T ∧
        CwSecondGetYDLaw s e.time (arg sevm 0) ⟨arg sevm 1, hi⟩ T := by
  obtain ⟨e, o, hstep, hraw, hi, T, hT, -, hsec⟩ :=
    cwo_raw_getYD2_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck htok
  exact ⟨e, o, hstep, hraw, hi, T, hT, cwSecondGetYD_law hsec⟩

/-- **U4 second `get_y_D` at the `remove_liquidity_one_coin` frame.**  A successful frame on the
selector, entered fresh at a `Checkpoint` under the ENV bundle, refines the model with its raw
effect, and its first `get_y_D` call (inside `_calc_withdraw_one_coin`), at the observed
environment's time and supply, returned the floor root or its successor. -/
theorem pool_getYD2_rootOrSucc_oneCoin {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (henv : PoolFrameEnv ⟨0, sevm, pre, .ok post, exc⟩) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : arg sevm 1 < 3) (T : Nat), e.supply = some T ∧
        CwSecondGetYDLaw s e.time (arg sevm 0) ⟨arg sevm 1, hi⟩ T := by
  obtain ⟨e, o, hstep, hraw, hi, T, hT, -, hsec⟩ :=
    removeLiquidityOneCoin_raw_getYD2_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas
      hck henv.htok henv.hcoin hpc henv.id henv.keep henv.hidk
  exact ⟨e, o, hstep, hraw, hi, T, hT, cwSecondGetYD_law hsec⟩

/-- **U4 `get_y` at the `exchange` frame.**  A successful frame on the selector, entered fresh at a
`Checkpoint` under the ENV bundle, refines the model with its raw effect, and its `get_y` call — on
the decoded coins `i`, `j`, the word `x` the bytecode passed and the stored `xp` at the model's
`amp` for the observed time — returned a word `y` that is the floor root of the floored-coefficient
quadratic at `D = get_D(xp, amp)` or its successor. -/
theorem pool_getY_rootOrSucc_exchange {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (henv : PoolFrameEnv ⟨0, sevm, pre, .ok post, exc⟩) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (i j : Fin 3) (dx md : Nat), decodeCall sevm = .exchange i.val j.val dx md ∧
      ∃ (amp : Nat) (x0 x1 x2 x y : B256), aChk s e.time = some amp ∧
        xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
        getYChk amp i j x.toNat (V3.mk x0.toNat x1.toNat x2.toNat).get = some y.toNat ∧
        rootOrSucc
          (cOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get i x.toNat (others j).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get i x.toNat (others j).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (bOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get i x.toNat (others j).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get i x.toNat (others j).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) y.toNat := by
  obtain ⟨e, o, hstep, hraw, i, j, dx, md, hdec, amp, x0, x1, x2, x, y, hA, hxp, hy⟩ :=
    exchange_raw_getY exc hcode hfork hlen hcd hsel hstack hmem hgas hck henv.hcoin hpc henv.id
      henv.keep henv.hidk
  exact ⟨e, o, hstep, hraw, i, j, dx, md, hdec, amp, x0, x1, x2, x, y, hA, hxp, hy,
    getYChk_rootOrSucc hy⟩

/-- **U4 `get_y` at the `get_dy` frame.** A successful `get_dy` frame, entered fresh at a `Checkpoint`, refines the model with its raw effect, and its `get_y` call, on the decoded coins, the word `dyX` the bytecode passed and the stored `xp` at the model's `amp` for the observed time, returned a word `y` that is the floor root of the floored-coefficient quadratic or its successor. -/
theorem pool_getY_rootOrSucc_dy {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetDy)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : (dyI sevm).toNat < 3) (hj : (dyJ sevm).toNat < 3) (amp : Nat)
        (x0 x1 x2 y : B256),
        aChk s e.time = some amp ∧ xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
        getYChk amp ⟨(dyI sevm).toNat, hi⟩ ⟨(dyJ sevm).toNat, hj⟩ (dyX sevm x0 x1 x2).toNat
          (V3.mk x0.toNat x1.toNat x2.toNat).get = some y.toNat ∧
        rootOrSucc
          (cOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (bOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) y.toNat := by
  obtain ⟨e, o, hstep, hraw, hi, hj, amp, x0, x1, x2, y, hA, hxp, hy⟩ :=
    dy_raw_getY checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck
  exact ⟨e, o, hstep, hraw, hi, hj, amp, x0, x1, x2, y, hA, hxp, hy, getYChk_rootOrSucc hy⟩

/-- **U4 `get_y` at the `get_dy_underlying` frame.** The `get_dy_underlying` analogue of `pool_getY_rootOrSucc_dy`, on the word `dyuX` the bytecode passed. -/
theorem pool_getY_rootOrSucc_dyu {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetDyUnderlying)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : (dyI sevm).toNat < 3) (hj : (dyJ sevm).toNat < 3) (amp : Nat)
        (x0 x1 x2 y : B256),
        aChk s e.time = some amp ∧ xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
        getYChk amp ⟨(dyI sevm).toNat, hi⟩ ⟨(dyJ sevm).toNat, hj⟩ (dyuX sevm x0 x1 x2).toNat
          (V3.mk x0.toNat x1.toNat x2.toNat).get = some y.toNat ∧
        rootOrSucc
          (cOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyuX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyuX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (bOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyuX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyuX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) y.toNat := by
  obtain ⟨e, o, hstep, hraw, hi, hj, amp, x0, x1, x2, y, hA, hxp, hy⟩ :=
    dyu_raw_getY checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck
  exact ⟨e, o, hstep, hraw, hi, hj, amp, x0, x1, x2, y, hA, hxp, hy, getYChk_rootOrSucc hy⟩

end Blanc.Lift.Curve3Pool
