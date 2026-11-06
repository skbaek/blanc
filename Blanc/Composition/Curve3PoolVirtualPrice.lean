import Blanc.Composition.Curve3PoolVirtualPriceFrames
import Blanc.Composition.Curve3PoolVirtualPriceModel
import Blanc.Composition.Curve3PoolPublic
import Blanc.Lift.CurveCoins.PremisesOfLogs

/-!
# `virtual_price_bound`

Each committed pool call since the minter assignment stays within its allowance:

* `opOf_decode`: the public entry names against the dispatcher;
* `pool_mid_entries`: `joint_mid_u3`'s invocations each entered at a checkpoint of their replayed state, and no call
  nests in another, so the committed calls are exactly those invocations (`frame_facts`);
* `within_of_frame`: `Within` at one call, arm by arm, the literal fee-loop balances included;
* `virtual_price_bound_of_donateCovered`: the headline, from one **marked hypothesis**, `DonateCovered`.

`DonateCovered` is what `donate_admin_fees`'s arm needs of backing: that call overwrites the books with what the coins
answer, so a coin answering less than the books would lower `D` arbitrarily. It says the answers cover the books at
each such call. It is not a premise of the headline: `pool_backed`'s internal form is to discharge it.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCoinKeep
open Blanc.Composition.Curve3PoolVirtualPrice
open Blanc.Composition.Curve3PoolSupply (SupplyObserved supplyAt joint_mid_u3)
open Blanc.StableSwapNewton

/-! ## The entries -/

/-- What the dispatcher runs for a frame the public statement names `op`. -/
inductive OpDecoded (e : Sevm) : PoolOp → Prop
  | removeLiquidity {a mins} : decodeCall e = .removeLiquidity a mins → OpDecoded e .removeLiquidity
  | donate : decodeCall e = .donateAdminFees → OpDecoded e .donateAdminFees
  | add {mm} : 4 ≤ e.data.length → Sevm.selector e = selAddLiquidity →
      decodeCall e = .addLiquidity (argV3 e 0) mm → OpDecoded e (.addLiquidity (argV3 e 0))
  | imbalance {am mb} : decodeCall e = .removeLiquidityImbalance am mb → OpDecoded e (.imbalance am)
  | exchange {i j dx md} : decodeCall e = .exchange i j dx md → OpDecoded e (.exchange i j)
  | oneCoin {a i mn} : decodeCall e = .removeLiquidityOneCoin a i mn → OpDecoded e (.oneCoin a i)
  | other : Call.quiet (decodeCall e) = true → OpDecoded e .other

/-- **`opOf` reads the dispatcher**: the words it names are the ones `decodeCall` gives the entry. -/
theorem opOf_decode (e : Sevm) : OpDecoded e (opOf e) := by
  by_cases hl : e.data.length < 4
  · have : opOf e = .other := by rw [opOf, ite_eq_left hl]
    rw [this]
    exact .other (by rw [decodeCall_short hl]; rfl)
  have hlen : 4 ≤ e.data.length := by omega
  by_cases h1 : Sevm.selector e = selRemoveLiquidity
  · have : opOf e = .removeLiquidity := by rw [opOf, ite_eq_right hl, ite_eq_left h1]
    rw [this]
    exact .removeLiquidity (decodeCall_at (k := 7) (by decide +kernel) h1 hlen)
  by_cases h2 : Sevm.selector e = selDonateAdminFees
  · have : opOf e = .donateAdminFees := by rw [opOf, ite_eq_right hl, ite_eq_right h1, ite_eq_left h2]
    rw [this]
    exact .donate (decodeCall_at (k := 21) (by decide +kernel) h2 hlen)
  by_cases h3 : Sevm.selector e = selAddLiquidity
  · have : opOf e = .addLiquidity (argV3 e 0) := by rw [opOf, ite_eq_right hl, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
    rw [this]
    exact .add hlen h3 (decodeCall_at (k := 3) (by decide +kernel) h3 hlen)
  by_cases h4 : Sevm.selector e = selRemoveLiquidityImbalance
  · have : opOf e = .imbalance (argV3 e 0) := by rw [opOf, ite_eq_right hl, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
    rw [this]
    exact .imbalance (decodeCall_at (k := 8) (by decide +kernel) h4 hlen)
  by_cases h5 : Sevm.selector e = selExchange
  · have : opOf e = .exchange (Curve3Pool.arg e 0) (Curve3Pool.arg e 1) := by
      rw [opOf, ite_eq_right hl, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_left h5]
    rw [this]
    exact .exchange (decodeCall_at (k := 6) (by decide +kernel) h5 hlen)
  by_cases h6 : Sevm.selector e = selRemoveLiquidityOneCoin
  · have : opOf e = .oneCoin (Curve3Pool.arg e 0) (Curve3Pool.arg e 1) := by
      rw [opOf, ite_eq_right hl, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5, ite_eq_left h6]
    rw [this]
    exact .oneCoin (decodeCall_at (k := 10) (by decide +kernel) h6 hlen)
  have : opOf e = .other := by
    rw [opOf, ite_eq_right hl, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5, ite_eq_right h6]
  rw [this]
  exact .other (decodeCall_quiet h3 h5 h1 h4 h6 h2)

/-! ## Invocations -/

/-- A replay of a concatenation passes through a state after its first part. -/
theorem PoolRun.prefix : ∀ {s t : Curve3Pool.State} {xs ys : List PoolInvocation},
    PoolRun s (xs ++ ys) t → ∃ m, PoolRun s xs m
  | s, _, [], _, _ => ⟨s, rfl⟩
  | _, _, _ :: _, _, h => by
    obtain ⟨o, hstep, hraw, rest⟩ := h
    obtain ⟨m, hm⟩ := PoolRun.prefix rest
    exact ⟨m, o, hstep, hraw, hm⟩

/-- **Entry checkpoints carry between two replays of the same frames**, whatever environments they recorded: each
frame's post storage abstracts one state. -/
theorem PoolEntries.transfer {A : List PoolInvocation} :
    ∀ {B : List PoolInvocation} {s t t' : Curve3Pool.State},
    A.map PoolInvocation.frame = B.map PoolInvocation.frame → PoolRun s A t → PoolEntries s A →
    PoolRun s B t' → PoolEntries s B := by
  induction A with
  | nil =>
    intro B s t t' hmap _ _ _
    cases B with
    | nil => trivial
    | cons _ _ => cases hmap
  | cons a A ih =>
    intro B s t t' hmap hA hE hB
    cases B with
    | nil => cases hmap
    | cons b B =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨e, hmap⟩ := hmap
      obtain ⟨oa, ha, ra, restA⟩ := hA
      obtain ⟨ob, hb, rb, restB⟩ := hB
      have ck : Checkpoint (b.frame.pre.getStor b.frame.sevm.currentTarget) s := e ▸ hE.1
      refine ⟨ck, fun o ho => ?_⟩
      obtain rfl := Option.some.inj (ho.symm.trans hb)
      have c1 := (rawEffect_refines (D := Exec.Frame.rootDeriv a.frame) hE.1 ha ra).1
      have c2 := (rawEffect_refines (D := Exec.Frame.rootDeriv b.frame) ck ho rb).1
      rw [e] at c1
      have same : oa.state = o.state := c1.abs.unique c2.abs
      have next := hE.2 oa ha
      rw [same] at next restA
      exact ih hmap restA next restB

/-- A frame with no non-static pool frame below is its own pool subtree. -/
theorem subtree_self {f : Exec.Frame} (target : f.sevm.currentTarget = pool) (hs : f.sevm.isStatic = false)
    (quiet : ∀ g ∈ Exec.descendantFrames f.run, g.sevm.isStatic = false → g.sevm.currentTarget ≠ pool) :
    poolSubtreeFrames pool f = [f] := by
  have self : poolSubtreeFrames pool f = f :: (Exec.descendantFrames f.run).flatMap (poolFrameObs pool) :=
    Blanc.Exec.Frame.subtreeAt_of_target target hs
  rw [self, List.flatMap_eq_nil_iff.mpr]
  intro g hg
  cases hgs : g.sevm.isStatic with
  | true => exact poolFrameObs_static hgs
  | false => exact poolFrameObs_foreign (quiet g hg hgs)

/-- What coin 2's storage says `a` holds. -/
theorem coinHeld_two (w : Jaune.State) (a : Adr) : coinHeld w a 2 = word w usdt (Usdt.balSlot a) := by
  rw [coinHeld, ite_eq_right fun hk => absurd hk.1 (by decide)]
  rfl

/-- The facts about one committed pool call. -/
structure CallFacts (f : Exec.Frame) (s : Curve3Pool.State) (e : Env) (o : Out) : Prop where
  ck : Checkpoint (f.pre.getStor f.sevm.currentTarget) s
  coins : s.coins = Curve3Pool.Creation.coinsN ∧ s.token = Curve3Pool.Creation.tokenN
  fee : s.adminFee ≤ feeDen
  step : Curve3Pool.step s e (decodeCall f.sevm) = some o
  raw : RawEffect (Exec.Frame.rootDeriv f) f.post e o
  observed : ∀ T, e.supply = some T → T = supply f.pre.state
  after : supplyAfter (supply f.pre.state) o.calls = supply f.post.state
  ledger : U3Ledger s e (decodeCall f.sevm) o (supply f.pre.state) (supply f.post.state)

section Assumes

variable {d : Deployment} {future : BlockChain} {h : MainnetHistory d.minter.post future}

/-- `FramesHold` since the minter assignment. -/
theorem Assumes.framesHold (A : Assumes d h) : FramesHold (d.sinceMinter h) dai usdc usdt c3 :=
  framesHold_of_coins A.coinsSince A.c3Code

/-- A settled pool frame since the minter assignment runs the pool's code. -/
theorem Assumes.ownCode (A : Assumes d h) {f : Exec.Frame} (member : f ∈ (d.sinceMinter h).settledFrames)
    (target : f.sevm.currentTarget = pool) :
    f.sevm.code = Curve3Pool.code ∧ f.pre.getCode f.sevm.currentTarget ≠ .empty := by
  obtain ⟨poolCode, -, -⟩ := Curve3PoolJointRoot.joint_root (Deployment.toJoint d A.facts)
  have poolNe : Curve3Pool.code.toList ≠ [] := fun e => by
    have := Curve3Pool.code_toList_length
    rw [e] at this
    cases this
  have own := (d.sinceMinter h).settled_ownCodeIn (F := HistFork) Curve3Pool.poolSem pool HistFork.stateGas_none poolNe
    (Curve3Pool.poolSem.not_delegation (show some Curve3Pool.code.toList = Curve3Pool.poolSem.image from rfl))
    (Curve3PoolSupply.pool_ownSpawnsIn pool) BodyStageCapabilities.historical poolCode Curve3Pool.pool_runtimeSafety rfl
  have ownF := own f member
  refine ⟨ownF.2.2.2.2 target, ?_⟩
  rw [target, ownF.1]
  exact fun e => poolNe (by rw [e, ByteArray.toList_eq_toList_data]; rfl)

/-- A settled pool frame at a checkpoint of the recorded parties has nothing non-static at the pool below it. -/
theorem Assumes.quiet (A : Assumes d h) {f : Exec.Frame} (member : f ∈ (d.sinceMinter h).settledFrames)
    (target : f.sevm.currentTarget = pool) (hs : f.sevm.isStatic = false) {s : Curve3Pool.State}
    (hck : Checkpoint (f.pre.getStor f.sevm.currentTarget) s)
    (hq : s.coins = Curve3Pool.Creation.coinsN ∧ s.token = Curve3Pool.Creation.tokenN) :
    ∀ g ∈ Exec.descendantFrames f.run, g.sevm.isStatic = false → g.sevm.currentTarget ≠ pool := by
  obtain ⟨hcode, hpc⟩ := A.ownCode member target
  obtain ⟨sevm, b, post, exc, cm, rfl, H⟩ :=
    pool_at A.midFacts A.framesHold member target hs hcode hpc hck hq
  intro g hg hgs
  have := H.no_nested g hg hgs
  rwa [show sevm.currentTarget = pool from target] at this

/-- A list of frames each its own subtree is its own observation. -/
theorem flatMap_subtree_self : ∀ {L : List PoolInvocation},
    (∀ i ∈ L, poolSubtreeFrames pool i.frame = [i.frame]) →
    L.flatMap (fun i => poolSubtreeFrames pool i.frame) = L.map PoolInvocation.frame
  | [], _ => rfl
  | i :: L, hL => by
    rw [List.flatMap_cons, hL i List.mem_cons_self, List.map_cons,
      flatMap_subtree_self fun j hj => hL j (List.mem_cons_of_mem _ hj)]
    rfl

/-- **The committed pool calls since the minter assignment are `joint_mid_u3`'s invocations, each at its checkpoint.** -/
theorem Assumes.frame_facts (A : Assumes d h) {f : Exec.Frame} (hf : f ∈ poolCalls (d.sinceMinter h)) :
    f ∈ (d.sinceMinter h).settledFrames ∧ f.sevm.currentTarget = pool ∧ f.sevm.isStatic = false ∧
    ∃ s e o, CallFacts f s e o := by
  obtain ⟨member, target⟩ := mem_flatMap_poolFrameObs hf
  have nonstatic : f.sevm.isStatic = false := by
    obtain ⟨g, -, hg⟩ := List.mem_flatMap.mp hf
    unfold poolFrameObs at hg
    split at hg
    · rename_i hc
      rw [List.mem_singleton] at hg
      rw [hg]
      exact hc.2
    · exact absurd hg List.not_mem_nil
  refine ⟨member, target, nonstatic, ?_⟩
  obtain ⟨invs₀, ps, cs, -, run₀, -, joint, B, obsB, authB, ⟨sB, runB, -⟩, per⟩ :=
    joint_mid_u3 (Deployment.toJoint d A.facts) (d.sinceMinter h) A.fresh A.env
  obtain ⟨poolCode, -, -⟩ := Curve3PoolJointRoot.joint_root (Deployment.toJoint d A.facts)
  have hps := run₀.coins_token
  have hpq : ps.coins = Curve3Pool.Creation.coinsN ∧ ps.token = Curve3Pool.Creation.tokenN := hps
  have envAt : PoolMidEnv (d.sinceC3Block h) (d.sinceMinter h) pool ps.coins ps.token := by
    rw [hpq.1, hpq.2]
    exact A.env
  obtain ⟨-, C, obsC, authC, entriesC, sC, runC, -, -, -, -⟩ :=
    pool_mid_history (d.sinceMinter h) poolCode joint.poolCk envAt
  have inCommitted : ∀ {L : List PoolInvocation},
      L.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFramesMid pool (d.sinceMinter h) →
      (∀ i ∈ L, i.Authentic pool) → ∀ i ∈ L, i.frame ∈ committedPoolFramesMid pool (d.sinceMinter h) := by
    intro L obs auth i hi
    rw [← obs]
    obtain ⟨-, -, at', nst, -⟩ := auth i hi
    refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
    have self : poolSubtreeFrames pool i.frame =
        i.frame :: (Exec.descendantFrames i.frame.run).flatMap (poolFrameObs pool) :=
      Blanc.Exec.Frame.subtreeAt_of_target at' nst
    rw [self]
    exact List.mem_cons_self
  have quietC : ∀ i ∈ C, poolSubtreeFrames pool i.frame = [i.frame] := by
    intro i hi
    obtain ⟨-, -, at', nst, -⟩ := authC i hi
    obtain ⟨pre, post, split⟩ := List.append_of_mem hi
    obtain ⟨m, hm⟩ := PoolRun.prefix (split ▸ runC)
    have ck := PoolEntries.split (split ▸ entriesC) hm
    have hco := hm.coins_token
    exact subtree_self at' nst (A.quiet (mem_flatMap_poolFrameObs (inCommitted obsC authC i hi)).1 at' nst ck
      ⟨hco.1.trans hpq.1, hco.2.trans hpq.2⟩)
  have mapC : C.map PoolInvocation.frame = committedPoolFramesMid pool (d.sinceMinter h) := by
    rw [← flatMap_subtree_self quietC]
    exact obsC
  have quietB : ∀ i ∈ B, poolSubtreeFrames pool i.frame = [i.frame] := by
    intro i hi
    obtain ⟨-, -, at', nst, -⟩ := authB i hi
    have inC := inCommitted obsB authB i hi
    rw [← mapC] at inC
    obtain ⟨a, ha, ea⟩ := List.mem_map.mp inC
    rw [← ea]
    exact quietC a ha
  have mapB : B.map PoolInvocation.frame = committedPoolFramesMid pool (d.sinceMinter h) := by
    rw [← flatMap_subtree_self quietB]
    exact obsB
  have entriesB : PoolEntries ps B := PoolEntries.transfer (mapC.trans mapB.symm) runC entriesC runB
  have hf' : f ∈ B.map PoolInvocation.frame := by
    rw [mapB]
    exact hf
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf'
  obtain ⟨pre, post, split⟩ := List.append_of_mem hi
  obtain ⟨m, hm⟩ := PoolRun.prefix (split ▸ runB)
  obtain ⟨-, fee, o, hstep, hraw, obs, after, ledger⟩ := per pre i post m split hm
  have hco := hm.coins_token
  exact ⟨m, i.env, o,
    { ck := PoolEntries.split (split ▸ entriesB) hm
      coins := ⟨hco.1.trans hpq.1, hco.2.trans hpq.2⟩
      fee := fee
      step := hstep
      raw := hraw
      observed := fun T hT => (obs T hT).1
      after := after
      ledger := ledger }⟩

/-- USDT's two replies across `add_liquidity`, at a committed call. -/
theorem Assumes.add_replies (A : Assumes d h) {f : Exec.Frame} (member : f ∈ (d.sinceMinter h).settledFrames)
    (target : f.sevm.currentTarget = pool) (hs : f.sevm.isStatic = false) {s : Curve3Pool.State} {e : Env}
    (hck : Checkpoint (f.pre.getStor f.sevm.currentTarget) s)
    (hq : s.coins = Curve3Pool.Creation.coinsN ∧ s.token = Curve3Pool.Creation.tokenN)
    (henv : EnvOf (Exec.Frame.rootDeriv f) e) (hlen : 4 ≤ f.sevm.data.length)
    (hsel : Sevm.selector f.sevm = selAddLiquidity) (hpos : 0 < (argV3 f.sevm 0).get 2)
    {w w' : Nat} (hw : (e.coin 2).balPre = some w) (hw' : (e.coin 2).balPost = some w') :
    w = ((f.pre.getStor usdt).get (Usdt.balSlot pool)).toNat ∧
      w' = ((f.post.getStor usdt).get (Usdt.balSlot pool)).toNat := by
  obtain ⟨hcode, hpc⟩ := A.ownCode member target
  have kids : ∀ c ∈ Exec.childFrames f.run, c ∈ (d.sinceMinter h).settledFrames := fun _ hc =>
    settledFrames_children (d.sinceMinter h) member hc
  obtain ⟨sevm, b, post, exc, cm, rfl, H⟩ :=
    pool_at A.midFacts A.framesHold member target hs hcode hpc hck hq
  refine H.add_replies cm target hlen hsel (fun c hc => CurveCoins.settled_wf _ (kids c hc)) ?_ henv hpos hw hw'
  intro c hc ht hcs sel
  have inPool := sinceMinter_settled_sub c (kids c hc)
  have hF : c ∈ coinFrames usdt (fun _ => True) (d.sincePool h).settledFrames :=
    mem_coinFrames.mpr ⟨inPool, ht, hcs, trivial⟩
  exact CurveCoins.Usdt.frame_flag_keep hF A.hashes.coinKeys.usdt (H.usdt_good hc ht) ht
    (A.tether.notDeprecated c hF) (by rcases sel with s | s | s <;> rw [s] <;> decide)

end Assumes

/-! ## The arms -/

theorem v3Of_get (g : Fin 3 → Nat) (k : Fin 3) : (v3Of g).get k = g k := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

theorem coinAt_eq (k : Fin 3) : coinAt k = adrOf (Curve3Pool.Creation.coinsN.get k) := by
  match k with
  | 0 => exact coin0_eq.symm
  | 1 => exact coin1_eq.symm
  | 2 => exact coin2_eq.symm

/-- `feeGap` at the literal fee loop. -/
theorem feeGap_eq {w : Jaune.State} {s : Curve3Pool.State} {amp D D1 fee D2 : Nat} {new fees stored mid : V3}
    (hs : Abstracts (w.getStor pool) s) (hD : invariant w amp = some D) (hD1 : getDMem new amp = some D1)
    (hfee : feeAdj s = some fee) (hfl : feeLoop fee s.adminFee D D1 s.balances new = some (fees, stored, mid))
    (hD2 : getDMem mid amp = some D2) :
    feeGap w amp new = overshoot (xpOf mid) amp D2 := by
  have e1 : word w pool feeSlot = s.fee := hs.fee
  have e2 : word w pool adminFeeSlot = s.adminFee := hs.adminFee
  have e3 : books w = s.balances := books_of_abstracts hs
  have r : feeRun w amp new = some (stored, mid) := by
    have hf : ((chkMul s.fee 3).bind fun a => chkDiv a 8) = some fee := hfee
    unfold feeRun
    rw [hD, e1, e2, e3]
    simp only [Option.bind_eq_bind, Option.bind_some, hD1]
    cases hm : chkMul s.fee 3 with
    | none =>
      rw [hm] at hf
      cases hf
    | some x =>
      rw [hm] at hf
      simp only [Option.bind_some] at hf ⊢
      rw [hf]
      simp only [Option.bind_some, hfl]
  simp only [feeGap, afterFees, r, Option.map_some, Option.bind_some, hD2, Option.getD_some]

/-- **The marked hypothesis**: at each `donate_admin_fees` call, what the coins answer covers the books. Not a
premise of `virtual_price_bound`: `pool_backed`'s internal form is to discharge it. -/
def DonateCovered (f : Exec.Frame) : Prop :=
  opOf f.sevm = .donateAdminFees → ∀ k n v,
    ReplyAt (Exec.Frame.rootDeriv f) n (coinAt k) (balanceOfData pool) v → recorded f.pre.state k ≤ v

section Arms

variable {d : Deployment} {future : BlockChain} {h : MainnetHistory d.minter.post future}

/-- **One committed pool call stays within its allowance.** -/
theorem Assumes.within (A : Assumes d h) {f : Exec.Frame} (hf : f ∈ poolCalls (d.sinceMinter h))
    (cover : DonateCovered f) {amp D D' : Nat}
    (hamp : ampAt f.pre.state f.sevm.benvStat.time.toNat = some amp) (hT : 0 < supply f.pre.state)
    (hD : invariant f.pre.state amp = some D) (hD' : invariant f.post.state amp = some D') :
    Within f.pre.state f.post.state (opOf f.sevm) amp D D' := by
  obtain ⟨member, target, nonstatic, s, e, o, F⟩ := A.frame_facts hf
  have hck := F.ck
  have hs : Abstracts (f.pre.state.getStor pool) s := by
    have := F.ck.abs
    rw [target] at this
    exact this
  have hs' : Abstracts (f.post.state.getStor pool) o.state := by
    have := (rawEffect_refines (D := Exec.Frame.rootDeriv f) F.ck F.step F.raw).1.abs
    change Abstracts (f.post.getStor f.sevm.currentTarget) _ at this
    rw [target] at this
    exact this
  have hA : aChk s e.time = some amp := by
    rw [F.raw.env.time, ← ampAt_of_abstracts hs]
    exact hamp
  have hD0 : getDMem s.balances amp = some D := by rw [← invariant_of_abstracts hs]; exact hD
  have hD1 : getDMem o.state.balances amp = some D' := by rw [← invariant_of_abstracts hs']; exact hD'
  have hb := pool_step_body F.step
  have dec := opOf_decode f.sevm
  have cov := cover
  unfold DonateCovered at cov
  generalize opOf f.sevm = op at dec cov ⊢
  cases dec with
  | removeLiquidity hc =>
    have l := F.ledger
    rw [hc] at l
    exact within_removeLiquidity l hs hT hD hD1
  | exchange hc =>
    rename_i i j dx md
    have l := F.ledger
    rw [hc] at l
    obtain ⟨i', j', ei, ej, -⟩ := l.2.2.2.2.1 i j dx md rfl
    have hi : i < 3 := by
      unfold Curve3Pool.idx at ei
      split at ei
      · assumption
      · cases ei
    have hj : j < 3 := by
      unfold Curve3Pool.idx at ej
      split at ej
      · assumption
      · cases ej
    exact within_exchange hi hj l hs hs' hA F.fee hD hD'
  | oneCoin hc =>
    rename_i a i mn
    have l := F.ledger
    rw [hc] at l
    obtain ⟨i', ei, -⟩ := l.2.2.2.2.2 a i mn rfl
    have hi : i < 3 := by
      unfold Curve3Pool.idx at ei
      split at ei
      · assumption
      · cases ei
    exact within_oneCoin hi l hs hs' hA F.fee hD hD'
  | donate hc =>
    have l := F.ledger
    rw [hc] at l
    have hcoin : ∀ k v, (e.coin k).balPre = some v → s.balances.get k ≤ v := by
      intro k v hv
      have hnp := Curve3PoolJointRoot.parties_not_precompile
        ((d.sinceMinter h).rootEntryIn _ ((d.sinceMinter h).mem_rawFrames_of_mem_settledFrames f member)).2
      have hcoinAdr : coinAdr (Exec.Frame.rootDeriv f) k = coinAt k := by
        have := coinAdr_eq (D := Exec.Frame.rootDeriv f) F.ck.abs k
        rw [this, F.coins.1, coinAt_eq]
      rcases (F.raw.env.coin k).balPre v hv with hf' | ⟨n, hn⟩
      · exfalso
        rw [hcoinAdr] at hf'
        have np := hnp.1 k
        have : ¬ f.sevm.benvStat.rules.isPrecomp (coinAt k) := by
          rw [coinAt_eq]
          exact np
        simp only [framed, Exec.Frame.rootDeriv, this, decide_false, Bool.not_false, Bool.true_or, reduceCtorEq] at hf'
      · rw [hcoinAdr, show (Exec.Frame.rootDeriv f).sevm.currentTarget = pool from target] at hn
        have := cov rfl k n v hn
        rwa [recorded_of_abstracts hs k] at this
    obtain ⟨-, hTT, -, hle⟩ := l.2.1 rfl hcoin amp D D' hD1
    change D * supply f.post.state ≤ (D' + overshoot (scaled f.pre.state) amp D) * supply f.pre.state
    rw [hTT]
    refine Nat.mul_le_mul_right _ ?_
    simpa only [overshoot, scaled, books_of_abstracts hs] using hle
  | add hlen hsel hc =>
    rename_i mm
    rw [hc] at hb
    have hbody : addLiquidity s e (argV3 f.sevm 0) mm = some o := hb
    obtain ⟨T, hT'⟩ := addLiquidity_supply hbody
    have eT := F.observed T hT'
    subst eT
    obtain ⟨new, D1, fee, fees, stored, mid, D2, hnew, hnD1, hfee, hfl, hD2, hle⟩ :=
      addLiquidity_literal hbody hA hT' hT F.fee hD0 hD1
    have newEq : new = v3Of fun k => recorded f.pre.state k +
        creditedIn f.pre.state f.post.state (argV3 f.sevm 0) k := by
      refine V3.ext_get fun k => ?_
      rw [v3Of_get]
      obtain ⟨v1, v2⟩ := pullAdd_value (Nat.pos_iff_ne_zero.mp hT) (ofFnM_some hnew k)
      rw [recorded_of_abstracts hs k]
      by_cases hk : k = 2 ∧ (argV3 f.sevm 0).get k > 0
      · obtain ⟨rfl, hpos⟩ := hk
        obtain ⟨w, w', hw, hw', hv⟩ := v2 rfl hpos
        obtain ⟨r0, r1⟩ := A.add_replies member target nonstatic F.ck F.coins F.raw.env hlen hsel hpos hw hw'
        rw [hv]
        simp only [creditedIn, hpos, and_self, ↓reduceIte]
        rw [coinHeld_two, coinHeld_two, r0, r1]
        rfl
      · rw [v1 hk]
        simp only [creditedIn, gt_iff_lt] at hk ⊢
        rw [ite_eq_right hk]
    subst newEq
    have gap := feeGap_eq hs hD hnD1 hfee hfl hD2
    rw [F.after] at hle
    change D * supply f.post.state ≤ (D' + feeGap f.pre.state amp _) * supply f.pre.state
    rw [gap]
    exact hle
  | imbalance hc =>
    rename_i am mb
    rw [hc] at hb
    have hbody : removeLiquidityImbalance s e am mb = some o := hb
    obtain ⟨T, hT'⟩ := removeLiquidityImbalance_supply hbody
    have eT := F.observed T hT'
    subst eT
    obtain ⟨new, D1, fee, fees, stored, mid, D2, hnew, hnD1, hfee, hfl, hD2, hle⟩ :=
      removeLiquidityImbalance_literal hbody hA hT' F.fee hD0 hD1
    have newEq : new = v3Of fun k => recorded f.pre.state k - am.get k := by
      refine V3.ext_get fun k => ?_
      rw [v3Of_get, recorded_of_abstracts hs k]
      exact (chkSub_some (ofFnM_some hnew k)).1
    subst newEq
    have gap := feeGap_eq hs hD hnD1 hfee hfl hD2
    rw [F.after] at hle
    change D * supply f.post.state ≤ (D' + feeGap f.pre.state amp _) * supply f.pre.state
    rw [gap]
    exact hle
  | other hq =>
    obtain ⟨hbal, hsup⟩ := step_quiet hq F.step (supply f.pre.state)
    rw [F.after] at hsup
    have same : D' = D := by
      rw [hbal] at hD1
      exact Option.some.inj (hD1.symm.trans hD0)
    change D * supply f.post.state ≤ (D' + 0) * supply f.pre.state
    rw [hsup, same]
    exact Nat.le_refl _

end Arms

/-- **The bound, from `Assumes`, with one marked hypothesis**: the coins' answers cover the books at each
`donate_admin_fees` call. -/
theorem virtualPriceBound_of_assumes {d : Deployment} {future : BlockChain}
    {h : MainnetHistory d.minter.post future} (A : Assumes d h)
    (cover : ∀ f ∈ poolCalls (d.sinceMinter h), DonateCovered f) :
    VirtualPriceBound (poolCalls (d.sinceMinter h)) :=
  fun f hf _ _ _ hamp hT hD hD' => A.within hf (cover f hf) hamp hT hD hD'

/-- **`virtual_price_bound`, conditional on `DonateCovered` alone.** -/
theorem virtual_price_bound_of_donateCovered
    (cover : ∀ (d : Deployment) {future : BlockChain} (h : MainnetHistory d.minter.post future),
      Assumes d h → ∀ f ∈ poolCalls (d.sinceMinter h), DonateCovered f) :
    virtual_price_bound :=
  fun d _ h A => virtualPriceBound_of_assumes A (cover d h A)

end Blanc.Composition.Curve3PoolPublic
