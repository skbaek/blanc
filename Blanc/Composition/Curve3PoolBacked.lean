import Blanc.Composition.Curve3PoolBackedUsdc
import Blanc.Composition.Curve3PoolBackedWindow
import Blanc.Composition.Curve3PoolVirtualPrice

/-!
# The pool's books are covered

Per coin, the walk's two conclusions: at any point of history the books are at most what the coin's storage reads, and at
any step moving nothing out of a coin, what the coin answers covers the books at that step's entry.

* `pool_backed_holds`: `pool_backed`, at the end of any history;
* `Moment.backed`: the same right after any transaction;
* `Assumes.donateCovered`: `donate_admin_fees` reads coverage, so `virtual_price_bound_holds` follows.
-/

namespace Blanc.Composition.Curve3PoolBacked

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolPublic Blanc.Composition.Curve3PoolCoinKeep
open Blanc.StableSwapNewton (bind_some)
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun PoolEntries balanceOfData decodeCall step ReplyAt Checkpoint Env Out)

variable {d : Deployment}

/-- **USDC's books at a transaction boundary.** -/
theorem usdc_window (m : Moment d) (A : Assumes d m.through) (unlisted : UsdcUnlisted m.world pool) :
    recorded m.world 1 ≤ coinHeld m.world pool 1 := by
  have capabilities := BodyStageCapabilities.historical
  have certified := A.circle.usdcCertified
  have code : m.world.getCode usdc = Lift.Usdc.Proxy.code :=
    Usdc.usdc_code_at_cut (d.sincePool m.history) m.block m.cut capabilities A.circle.usdcCode certified
  have tail := (Usdc.usdc_viewChain_certified (MidHistoryTraceIn.tail m.block m.cut) capabilities code
    fun F member => certified F (by
      rw [m.settled_split]
      exact List.mem_append_right _ member)).1
  have r := m.coin_window A (usdcWalk A) tail
  rw [show usdcBook.V = Usdc.ledgerView from rfl, show usdcBook.T = usdc from rfl,
    show usdcBook.Rd = fun xs m => usdcRead xs (m (Usdc.balSlot pool)) from rfl] at r
  dsimp only at r
  rw [view_bal] at r
  exact r.trans (usdcRead_le_coinHeld _ fun _ _ => unfrozen_lt unlisted)

/-- A replay's invocation, at the checkpoint it enters, with what `RepliesCovered` says of it. -/
theorem replies_at {T : Adr} {k : Fin 3} : ∀ {st st' : Curve3Pool.State} {invs : List PoolInvocation},
    PoolRun st invs st' → PoolEntries st invs → RepliesCovered T pool k st invs → ∀ i ∈ invs,
      ∃ s o, Checkpoint (i.frame.pre.getStor i.frame.sevm.currentTarget) s ∧
        step s i.env (decodeCall i.frame.sevm) = some o ∧
        (pushed k o.calls = 0 → ∀ n w, ReplyAt (Exec.Frame.rootDeriv i.frame) n T (balanceOfData pool) w →
          s.balances.get k ≤ w)
  | _, _, [], _, _, _, _, m => absurd m List.not_mem_nil
  | st, _, i :: rest, run, entries, replies, j, m => by
    obtain ⟨o, hstep, -, tail⟩ := run
    obtain ⟨here, later⟩ := replies o hstep
    rcases List.mem_cons.mp m with rfl | m
    · exact ⟨st, o, entries.1, hstep, here⟩
    · exact replies_at tail (entries.2 o hstep) later j m

/-- `donate_admin_fees` names no call. -/
theorem donate_calls {s : Curve3Pool.State} {e : Env} {o : Out} (h : step s e .donateAdminFees = some o) : o.calls = [] := by
  have hb := Curve3Pool.pool_step_body h
  change Curve3Pool.donateAdminFees s e = some o at hb
  unfold Curve3Pool.donateAdminFees at hb
  obtain ⟨_, -, hb⟩ := bind_some hb
  obtain ⟨_, -, hb⟩ := bind_some hb
  cases Option.some.inj hb
  rfl

variable {future : BlockChain} {h : MainnetHistory d.minter.post future}

/-- **At a `donate_admin_fees` call, what coin `k` answers covers the books.** -/
theorem donate_covered (A : Assumes d h) {B : CoinBook} {k : Fin 3} {a b : StorWords}
    (W : CoinWalk B pool k (d.sincePool h).settledFrames (d.sincePool h).settledRoots a b Curve3Pool.Creation.coinsN
      Curve3Pool.Creation.tokenN) {T : Adr} (hT : B.T = T) {f : Exec.Frame} (member : f ∈ (d.sincePool h).settledFrames)
    (target : f.sevm.currentTarget = pool) (mutable : f.sevm.isStatic = false) (op : opOf f.sevm = .donateAdminFees)
    {n v : Nat} (reply : ReplyAt (Exec.Frame.rootDeriv f) n T (balanceOfData pool) v) : recorded f.pre.state k ≤ v := by
  subst hT
  obtain ⟨-, invs, auth, obs, entries, s, run, replies⟩ := A.coin_walk_whole W
  obtain ⟨i, hi, rfl⟩ := A.frame_invocation rfl rfl obs auth entries run member target mutable
  obtain ⟨st, o, ck, hstep, cover⟩ := replies_at run entries replies i hi
  have dec := opOf_decode i.frame.sevm
  rw [op] at dec
  cases dec with
  | donate hc =>
    rw [hc] at hstep
    have abs : Curve3Pool.Abstracts (i.frame.pre.state.getStor pool) st := by
      have := ck.abs
      rw [target] at this
      exact this
    rw [recorded_of_abstracts abs]
    exact cover (by rw [donate_calls hstep]; rfl) n v reply

end Blanc.Composition.Curve3PoolBacked

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolBacked

variable {d : Deployment}

/-- **The pool's books are covered right after any transaction of mainnet**, with USDC's flag on the pool clear there. -/
theorem Moment.backed (m : Moment d) (A : Assumes d m.through) (unlisted : UsdcUnlisted m.world pool) :
    PoolBacked m.world := fun k => by
  match k with
  | 0 => exact dai_window m A
  | 1 => exact usdc_window m A unlisted
  | 2 => exact usdt_window m A

/-- **`pool_backed`.** -/
theorem pool_backed_holds : pool_backed := fun _ _ _ A k => by
  match k with
  | 0 => exact dai_backed A
  | 1 => exact usdc_backed A
  | 2 => exact usdt_backed A

/-- **What the coins answer covers the books at each `donate_admin_fees` call.** -/
theorem Assumes.donateCovered {future : BlockChain} {h : MainnetHistory d.minter.post future} (A : Assumes d h) :
    ∀ f ∈ poolCalls (d.sinceMinter h), DonateCovered f := by
  intro f hf
  obtain ⟨memberM, target, mutable, -⟩ := A.frame_facts hf
  have member := sinceMinter_settled_sub f memberM
  unfold DonateCovered
  intro op k n v
  match k with
  | 0 =>
    intro reply
    exact donate_covered (T := dai) A (daiWalk A) rfl member target mutable op reply
  | 1 =>
    intro reply
    exact donate_covered (T := usdc) A (usdcWalk A) rfl member target mutable op reply
  | 2 =>
    intro reply
    exact donate_covered (T := usdt) A (usdtWalk A) rfl member target mutable op reply

/-- **`virtual_price_bound`.** -/
theorem virtual_price_bound_holds : virtual_price_bound :=
  virtual_price_bound_of_donateCovered fun _ _ _ A => A.donateCovered

end Blanc.Composition.Curve3PoolPublic
