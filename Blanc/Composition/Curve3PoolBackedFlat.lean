import Blanc.Composition.Curve3PoolBackedEnv
import Blanc.Lift.CurveCoins.BalanceAnswers
import Blanc.Composition.Curve3PoolPublicBridge
import Blanc.Lift.CurveCoins.PremisesOfLogs

/-!
# The walk over a coin whose whole storage chains and whose reading never changes

DAI and USDT: `flatBook` reads one entry the same way throughout. `flat_walk` builds `CoinWalk` from the coin's
`EntryLocal` and four facts about its frames.

* `Assumes.poolFrames`: every settled non-static pool frame is a `PoolAt`, one replay's invocation;
* `pool_ownCalls_history`: what the pool sends a coin, as a history fact.
-/

namespace Blanc.Composition.Curve3PoolBacked

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolPublic
open Blanc.Composition.Curve3PoolCoinKeep
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun PoolEntries poolFrameObs poolSubtreeFrames V3 adrOf answerWord
  balanceOfData transferSel transferFromSel)
open Blanc.Lift.CurveCoins (PoolCoinSel)

/-! ## The messages of the pool's calls -/

theorem word_length (n : Nat) : (Curve3Pool.word n).length = 32 := B256.length_toBytes _

theorem transfer_words {e : Sevm} {dst amt : Nat} (h : e.data = transferSel ++ Curve3Pool.word dst ++ Curve3Pool.word amt) :
    Blanc.Sevm.selector e = 0xa9059cbb ∧ Sevm.dataWord e 4 = Nat.toB256 dst ∧ Sevm.dataWord e 36 = Nat.toB256 amt := by
  refine ⟨selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by
      rw [h, List.append_assoc]; rfl), ?_, ?_⟩
  · exact Curve3PoolSupply.dataWord_eq_of_append (pre := transferSel) (rest := Curve3Pool.word amt) (by
      rw [h, List.append_assoc]; rfl) (by decide)
  · exact Curve3PoolSupply.dataWord_eq_of_append (pre := transferSel ++ Curve3Pool.word dst) (rest := []) (by
      rw [h, List.append_nil]; rfl) (by rw [List.length_append, word_length]; decide)

theorem transferFrom_words {e : Sevm} {src amt : Nat} {p : Adr}
    (h : e.data = transferFromSel ++ Curve3Pool.word src ++ p.toB256.toBytes ++ Curve3Pool.word amt) :
    Blanc.Sevm.selector e = 0x23b872dd ∧ Sevm.dataWord e 4 = Nat.toB256 src ∧ Sevm.dataWord e 36 = p.toB256 ∧
      Sevm.dataWord e 68 = Nat.toB256 amt := by
  refine ⟨selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by
      rw [h]; simp only [List.append_assoc]; rfl), ?_, ?_, ?_⟩
  · exact Curve3PoolSupply.dataWord_eq_of_append (pre := transferFromSel)
      (rest := p.toB256.toBytes ++ Curve3Pool.word amt) (by
      rw [h]; simp only [List.append_assoc]; rfl) (by decide)
  · exact Curve3PoolSupply.dataWord_eq_of_append (pre := transferFromSel ++ Curve3Pool.word src)
      (rest := Curve3Pool.word amt) (by
      rw [h]; simp only [List.append_assoc]) (by rw [List.length_append, word_length]; decide)
  · exact Curve3PoolSupply.dataWord_eq_of_append (pre := transferFromSel ++ Curve3Pool.word src ++ p.toB256.toBytes)
      (rest := []) (by
      rw [h, List.append_nil]; rfl) (by
      rw [List.length_append, List.length_append, word_length, B256.length_toBytes]; decide)

/-- A word's number is at most the number it was made from. -/
theorem toB256_toNat_le (n : Nat) : (Nat.toB256 n).toNat ≤ n := by
  rw [B256.toNat_toB256]
  exact Nat.mod_le _ _

theorem sel_ne : (0xa9059cbb : B256) ≠ 0x23b872dd := by decide

/-- `ownDebit` of a `transfer`. -/
theorem ownDebit_transfer {h : Adr} {e : Sevm} {dst amt : Nat}
    (hd : e.data = transferSel ++ Curve3Pool.word dst ++ Curve3Pool.word amt) : ownDebit h e ≤ amt := by
  obtain ⟨sel, -, w36⟩ := transfer_words hd
  unfold ownDebit
  split
  · exact Nat.zero_le _
  · split
    · rw [w36]
      exact toB256_toNat_le amt
    · split
      · rename_i hs
        exact absurd (sel.symm.trans hs.1) sel_ne
      · exact Nat.zero_le _

/-- `ownDebit` of a `transferFrom` from someone else. -/
theorem ownDebit_transferFrom {h : Adr} {e : Sevm} {src amt : Nat} {p : Adr}
    (hd : e.data = transferFromSel ++ Curve3Pool.word src ++ p.toB256.toBytes ++ Curve3Pool.word amt)
    (hsrc : adrOf src ≠ h) : ownDebit h e = 0 := by
  obtain ⟨sel, w4, -, -⟩ := transferFrom_words hd
  unfold ownDebit
  split
  · rfl
  · split
    · rename_i hs
      exact absurd (hs.1.symm.trans sel) sel_ne
    · split
      · rename_i hs
        exact absurd (by rw [← hs.2.1, w4]; rfl) hsrc
      · rfl

/-- `ownCredit` of the holder's `transferFrom` from someone else to itself. -/
theorem ownCredit_transferFrom {h : Adr} {e : Sevm} {src amt : Nat} (caller : e.caller = h)
    (hd : e.data = transferFromSel ++ Curve3Pool.word src ++ h.toB256.toBytes ++ Curve3Pool.word amt)
    (hsrc : adrOf src ≠ h) (fits : amt < 2 ^ 256) : ownCredit h e = amt := by
  obtain ⟨sel, w4, w36, w68⟩ := transferFrom_words hd
  unfold ownCredit
  rw [w4, w36, w68, toAdr_toB256, ite_eq_left ⟨caller, sel, hsrc, rfl⟩]
  exact B256.toNat_toB256_of_lt fits

/-! ## A pool frame's children -/

variable {B : CoinBook}

/-- **The position above a child of a pool frame is free of opaque frames**, if it is above the pool frame. -/
theorem noOpaque_child {Op : Exec.Frame → Prop} {pre L₁ : List Exec.Frame} {P c : Exec.Frame}
    (above : Exec.NoOpaqueAbove Op pre P) (notP : ¬ Op P) :
    Exec.NoOpaqueAbove Op (pre ++ P :: blocks L₁) c := by
  intro b A m n hsplit hdesc
  rcases List.split_append_cons hsplit with ⟨m', inPre, rfl⟩ | ⟨b', rfl, hrest⟩
  · refine above b A m' (blocks L₁ ++ c :: n) inPre ?_
    rw [hdesc]
    simp only [List.append_assoc, List.cons_append]
  · cases b' with
    | nil =>
      obtain ⟨rfl, -⟩ := List.cons.inj hrest
      exact notP
    | cons x b'' =>
      obtain ⟨-, inBlocks⟩ := List.cons.inj hrest
      obtain ⟨⟨r, e⟩, -⟩ := rootFrames_forest (roots := L₁) inBlocks
      have l₁ := congrArg List.length hdesc
      have l₂ := congrArg List.length e
      simp only [List.length_append, List.length_cons] at l₁ l₂
      omega

variable {sevm : Sevm} {b post : Devm} {exc : Exec 0 sevm b (.ok post)} {s : Curve3Pool.State}

/-- **A child's subtree holds no chain frame but the child**, when nothing observed lies below a frame at the coin. -/
theorem kid_sub (H : Curve3PoolPublic.PoolAt exc s) {c : Exec.Frame} (hc : c ∈ Exec.childFrames exc)
    (obs : c.sevm.isStatic = false → c.sevm.currentTarget = B.T → B.Obs c)
    (quiet : c.sevm.isStatic = false → c.sevm.currentTarget = B.T → B.cf (Exec.descendantFrames c.run) = []) :
    B.cf (Exec.committedFrames c.run) = if c.sevm.isStatic = false ∧ c.sevm.currentTarget = B.T then [c] else [] := by
  by_cases hit : c.sevm.isStatic = false ∧ c.sevm.currentTarget = B.T
  · rw [ite_eq_left hit, Exec.Frame.committedFrames_self, show c :: Exec.descendantFrames c.run =
      [c] ++ Exec.descendantFrames c.run from rfl, cf_append, quiet hit.1 hit.2, List.append_nil]
    unfold CoinBook.cf coinFrames coinObs
    rw [List.flatMap_cons, ite_eq_left ⟨hit.2, hit.1, obs hit.1 hit.2⟩, List.flatMap_nil, List.append_nil]
  · rw [ite_eq_right fun h => (hit h).elim]
    refine List.eq_nil_iff_forall_not_mem.mpr fun f hf => ?_
    obtain ⟨member, target, mutable, -⟩ := mem_coinFrames.mp hf
    have root : Exec.Frame.rootDeriv f ∈ Exec.rawFrameRoots c.run := by
      rw [Exec.Frame.committedFrames_self, List.mem_cons] at member
      rcases member with rfl | m
      · simp only [Exec.rawFrameRoots, List.mem_cons]
        exact .inl rfl
      · exact List.mem_cons_of_mem _ (Exec.mem_rawFrameDescendants_of_mem_descendantFrames c.run f m)
    have at' := H.roots_at hc _ root mutable
    cases hs : c.sevm.isStatic with
    | true =>
      have := Exec.committedFrames_isStatic c.run hs f member
      rw [mutable] at this
      cases this
    | false => exact hit ⟨hs, at'.symm.trans target⟩

/-! ## The replay over the history from the pool's creation -/

section Replay

variable {d : Deployment} {future : BlockChain} {h : MainnetHistory d.minter.post future}

/-- Every invocation of a replay is entered at a checkpoint of a state with the replay's coins and token. -/
theorem entries_checkpoint {coins : V3} {tok : Nat} : ∀ {st st' : Curve3Pool.State} {invs : List PoolInvocation},
    PoolRun st invs st' → PoolEntries st invs → st.coins = coins → st.token = tok →
    ∀ i ∈ invs, ∃ s : Curve3Pool.State, Curve3Pool.Checkpoint (i.frame.pre.getStor i.frame.sevm.currentTarget) s ∧
      s.coins = coins ∧ s.token = tok
  | _, _, [], _, _, _, _, _, m => absurd m List.not_mem_nil
  | st, _, i :: rest, run, entries, hc, ht, j, m => by
    obtain ⟨o, hstep, -, tail⟩ := run
    rcases List.mem_cons.mp m with rfl | m
    · exact ⟨st, entries.1, hc, ht⟩
    · obtain ⟨hc', ht'⟩ := (Curve3Pool.step_keeps hstep).coins_token
      exact entries_checkpoint tail (entries.2 o hstep) (hc'.trans hc) (ht'.trans ht) j m

/-- The replay of the pool from its creation, over `sincePool`. -/
theorem _root_.Blanc.Composition.Curve3PoolPublic.Assumes.replay (A : Assumes d h) :
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = Curve3Pool.committedPoolFramesMid pool (d.sincePool h) ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      PoolEntries (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat) invs ∧
      ∃ s, PoolRun (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat) invs s ∧
        Curve3Pool.Checkpoint (future.state.getStor pool) s := by
  obtain ⟨installed, initial⟩ := A.poolStart
  have env : Curve3Pool.PoolMidEnv (d.sinceC3Block h) (d.sincePool h) pool
      (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat).coins
      (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat).token :=
    { A.midFactsPool with
      callbacks := pool_keepAt_of_frames A.midFactsPool party_words' A.framesPool }
  obtain ⟨-, invs, obs, auth, entries, s, run, -, hc, -⟩ := Curve3Pool.pool_mid_history (d.sincePool h) installed initial env
  exact ⟨invs, obs, auth, entries, s, run, hc⟩

/-- The pool's own code stands at each of its settled frames. -/
theorem _root_.Blanc.Composition.Curve3PoolPublic.Assumes.poolOwn (A : Assumes d h) {f : Exec.Frame} (member : f ∈ (d.sincePool h).settledFrames)
    (target : f.sevm.currentTarget = pool) :
    f.sevm.code = Curve3Pool.code ∧ f.pre.getCode f.sevm.currentTarget ≠ .empty := by
  have capabilities := BodyStageCapabilities.historical
  have poolNe : Curve3Pool.code.toList ≠ [] := fun e => by
    have := Curve3Pool.code_toList_length
    rw [e] at this
    cases this
  have own := (d.sincePool h).settled_ownCodeIn (F := HistFork) Curve3Pool.poolSem pool HistFork.stateGas_none poolNe
    (Curve3Pool.poolSem.not_delegation (show some Curve3Pool.code.toList = Curve3Pool.poolSem.image from rfl))
    (Curve3PoolSupply.pool_ownSpawnsIn pool) capabilities A.poolStart.1 Curve3Pool.pool_runtimeSafety rfl f member
  refine ⟨own.2.2.2.2 target, ?_⟩
  rw [target, own.1]
  exact fun e => poolNe (by rw [e, ByteArray.toList_eq_toList_data]; rfl)

/-- A settled non-static pool frame entered at a checkpoint of the recorded parties is a `PoolAt`. -/
theorem _root_.Blanc.Composition.Curve3PoolPublic.Assumes.poolAt (A : Assumes d h) {f : Exec.Frame} (member : f ∈ (d.sincePool h).settledFrames)
    (target : f.sevm.currentTarget = pool) (mutable : f.sevm.isStatic = false) {s : Curve3Pool.State}
    (hck : Curve3Pool.Checkpoint (f.pre.getStor f.sevm.currentTarget) s)
    (hq : s.coins = Curve3Pool.Creation.coinsN ∧ s.token = Curve3Pool.Creation.tokenN) :
    ∃ (sevm : Sevm) (b post : Devm) (exc : Exec 0 sevm b (.ok post)) (cm : Execution.commits (.ok post) = true),
      f = ⟨0, sevm, b, .ok post, exc, cm⟩ ∧ PoolAt exc s :=
  pool_at A.midFactsPool A.framesPool member target mutable (A.poolOwn member target).1 (A.poolOwn member target).2 hck hq

/-- **Every settled non-static pool frame is entered at a checkpoint**: nothing nests, so each is an invocation. -/
theorem _root_.Blanc.Composition.Curve3PoolPublic.Assumes.poolFrames (A : Assumes d h) {f : Exec.Frame} (member : f ∈ (d.sincePool h).settledFrames)
    (target : f.sevm.currentTarget = pool) (mutable : f.sevm.isStatic = false) :
    ∃ s : Curve3Pool.State, Curve3Pool.Checkpoint (f.pre.getStor f.sevm.currentTarget) s ∧
      s.coins = Curve3Pool.Creation.coinsN ∧ s.token = Curve3Pool.Creation.tokenN := by
  obtain ⟨invs, obs, auth, entries, s, run, -⟩ := A.replay
  have inObs : f ∈ invs.flatMap (fun i => poolSubtreeFrames pool i.frame) := by
    rw [obs]
    refine List.mem_flatMap.mpr ⟨f, member, ?_⟩
    rw [poolFrameObs, ite_eq_left ⟨target, mutable⟩]
    exact List.mem_singleton.mpr rfl
  obtain ⟨i, hi, hf⟩ := List.mem_flatMap.mp inObs
  obtain ⟨st, ck, hc, ht⟩ := entries_checkpoint run entries rfl rfl i hi
  obtain ⟨hpc, -, atPool, mutableI, -⟩ := auth i hi
  have selfObs : poolSubtreeFrames pool i.frame =
      i.frame :: (Exec.descendantFrames i.frame.run).flatMap (poolFrameObs pool) :=
    Blanc.Exec.Frame.subtreeAt_of_target atPool mutableI
  have memberI : i.frame ∈ (d.sincePool h).settledFrames := by
    have : i.frame ∈ invs.flatMap (fun i => poolSubtreeFrames pool i.frame) := by
      refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
      rw [selfObs]
      exact List.mem_cons_self
    rw [obs] at this
    obtain ⟨g, hg, hobs⟩ := List.mem_flatMap.mp this
    rw [poolFrameObs] at hobs
    split at hobs
    · rw [List.mem_singleton] at hobs
      rw [hobs]
      exact hg
    · cases hobs
  obtain ⟨sevm, b, post, exc, cm, e, H⟩ := A.poolAt memberI atPool mutableI ck ⟨hc, ht⟩
  rw [selfObs, List.mem_cons] at hf
  rcases hf with rfl | hf
  · exact ⟨st, ck, hc, ht⟩
  · obtain ⟨g, hg, hobs⟩ := List.mem_flatMap.mp hf
    rw [poolFrameObs] at hobs
    split at hobs
    · rename_i hq
      rw [List.mem_singleton] at hobs
      subst hobs
      have hT : sevm.currentTarget = pool := by
        rw [e] at atPool
        exact atPool
      have hd : f ∈ Exec.descendantFrames exc := by
        have := hg
        rw [e] at this
        exact this
      exact absurd (hq.1.trans hT.symm) (H.no_nested f hd hq.2)
    · cases hobs

/-! ## The walk for a coin with one reading -/

/-- A settled frame's committed child, over `sincePool`. -/
theorem kid_settled {f c : Exec.Frame} (member : f ∈ (d.sincePool h).settledFrames) (hc : c ∈ Exec.childFrames f.run) :
    c ∈ (d.sincePool h).settledFrames :=
  settledFrames_children (d.sincePool h) member hc

/-- A coin whose whole storage chains and whose reading never changes. -/
def flatBook (T : Adr) (Good : Exec.Frame → Prop) (held : StorWords → Nat) (debit credit : Sevm → Nat) : CoinBook where
  T := T
  V := id
  Obs := fun _ => True
  Good := Good
  held := fun _ => held
  debit := debit
  credit := credit
  Rd := fun _ => held

theorem viewChain_id {T : Adr} {Good : Exec.Frame → Prop} : ∀ {a b : StorWords} {xs : List Exec.Frame},
    FrameChain T Good a xs b → ViewChain T id Good a xs b
  | _, _, [], h => h
  | _, _, _ :: _, h => ⟨h.1, h.2.1, viewChain_id h.2.2⟩

theorem ledger_flat {T : Adr} {Good : Exec.Frame → Prop} {held : StorWords → Nat} {debit credit : Sevm → Nat}
    {a b : StorWords} {frames : List Exec.Frame} {p : Adr}
    (L : EntryLocal T (fun _ => True) Good held debit credit a b frames)
    (third : ∀ F ∈ coinFrames T (fun _ => True) frames, F.sevm.caller ≠ p → debit F.sevm = 0) :
    Ledger (flatBook T Good held debit credit) p frames a b where
  loc :=
    { chain := viewChain_id L.chain
      at_ := fun split noOpaque => viewChain_id (L.at_ split noOpaque)
      law := L.law }
  seam := fun _ _ _ _ => Nat.le_refl _
  leave := fun _ _ _ _ _ => Nat.le_refl _
  third := third

/-- A pool frame's child at a coin runs the coin's bytes. -/
theorem _root_.Blanc.Composition.Curve3PoolPublic.PoolAt.child_good {sevm : Sevm} {b post : Devm}
    {exc : Exec 0 sevm b (.ok post)} {s : Curve3Pool.State} (H : PoolAt exc s) {T : Adr} {C : ByteArray}
    (hb : b.getCode T = C) (hne : C.toList ≠ []) (hnd : ¬ isValidDelegation C) {c : Exec.Frame}
    (hc : c ∈ Exec.childFrames exc) (ht : c.sevm.currentTarget = T) : CodeFrame T HistFork C c := by
  have hsg := H.fork.stateGas_none
  obtain ⟨pc0, stat, -, cpre, ccode⟩ := poolChild_facts H.code hsg exc c hc
  have hC : c.sevm.code = C := by
    rw [ccode T (by rw [hb]; exact hne) (by rw [hb]; exact hnd) ht, hb]
  exact ⟨pc0, hC, by rw [stat]; exact H.fork, by rw [cpre T (by rw [hb]; exact hne), hb]; exact hne⟩

/-- **`CoinWalk` for a coin with one reading.** -/
theorem flat_walk (A : Assumes d h) {k : Fin 3} {T : Adr} {Good : Exec.Frame → Prop} {held : StorWords → Nat}
    {debit credit : Sevm → Nat} {a b : StorWords}
    (L : EntryLocal T (fun _ => True) Good held debit credit a b (d.sincePool h).settledFrames)
    (hT : adrOf (Curve3Pool.Creation.coinsN.get k) = T)
    (hOther : ∀ j, j ≠ k → adrOf (Curve3Pool.Creation.coinsN.get j) ≠ T)
    (hTok : adrOf Curve3Pool.Creation.tokenN ≠ T) (hPool : T ≠ pool)
    (third : ∀ F ∈ coinFrames T (fun _ => True) (d.sincePool h).settledFrames, F.sevm.caller ≠ pool → debit F.sevm = 0)
    (below : ∀ G ∈ (d.sincePool h).settledFrames, G.sevm.currentTarget = T → G.sevm.isStatic = false →
      ∀ f ∈ Exec.descendantFrames G.run, f.sevm.isStatic = true)
    (push : ∀ (e : Sevm) dst amt, e.data = transferSel ++ Curve3Pool.word dst ++ Curve3Pool.word amt → debit e ≤ amt)
    (pullOut : ∀ (e : Sevm) src amt, e.data = transferFromSel ++ Curve3Pool.word src ++ pool.toB256.toBytes ++ Curve3Pool.word amt →
      adrOf src ≠ pool → debit e = 0)
    (pullIn : k ≠ Curve3Pool.feeIndex → ∀ (e : Sevm) src amt, e.caller = pool →
      e.data = transferFromSel ++ Curve3Pool.word src ++ pool.toB256.toBytes ++ Curve3Pool.word amt →
      adrOf src ≠ pool → amt < 2 ^ 256 → credit e = amt)
    (answer : ∀ {sevm : Sevm} {pb post : Devm} {exc : Exec 0 sevm pb (.ok post)} {s : Curve3Pool.State}, PoolAt exc s →
      ∀ c ∈ Exec.childFrames exc, c ∈ (d.sincePool h).settledFrames → c.sevm.currentTarget = T →
      c.sevm.data = balanceOfData pool → ∀ before : List Exec.Frame, (∀ F ∈ before, F ∈ (d.sincePool h).settledFrames) →
      FrameChain T Good a (coinFrames T (fun _ => True) before) (wordsAt T c.pre.state) →
      answerWord c.post.output = held (wordsAt T c.pre.state)) :
    CoinWalk (flatBook T Good held debit credit) pool k (d.sincePool h).settledFrames (d.sincePool h).settledRoots a b
      Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN where
  ledger := ledger_flat L third
  forest := (d.sincePool h).settledFrames_eq
  roots := by
    have capabilities := BodyStageCapabilities.historical
    exact (d.sincePool h).settledRoots_caller_ne_of_stateInv
      (Curve3Pool.poolSpec_preservesAdmittedH pool (Curve3Pool.poolEntryAtH Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN))
      capabilities (Curve3Pool.pool_mid_trace_admitted A.midFactsPool) ((d.sincePool h).rewardCreditsFunded capabilities)
      (c := Curve3Pool.poolSpec) ⟨A.poolStart.1, trivial, trivial⟩ Curve3Pool.pool_runtimeSafety rfl (by decide)
  targetNe := hPool
  coinAt := hT
  coinOther := hOther
  tokNe := hTok
  parties := fun f member t => A.midFactsPool.parties _ ((d.sincePool h).mem_rawFrames_of_mem_settledFrames f member) t
  delegate := by
    intro F hF G hG child mutableG te caller
    obtain ⟨-, target, mutableF, -⟩ := mem_coinFrames.mp hF
    have := below G hG (te.trans target) mutableG F (Exec.mem_descendantFrames_of_mem_childFrames G.run F child)
    rw [mutableF] at this
    cases this
  kids := by
    intro f member target mutable st ck hc ht
    obtain ⟨sevm, pb, post, exc, cm, rfl, H⟩ := A.poolAt member target mutable ck ⟨hc, ht⟩
    refine ⟨fun c hc' => kid_sub H hc' (fun _ _ => trivial) fun _ _ => ?_, fun c _ _ dst amt hd => push _ dst amt hd,
      fun c _ _ src amt hd hs => pullOut _ src amt hd hs, fun f' c hc' tc src amt hd hs fits => ?_⟩
    · refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
      obtain ⟨inDesc, tx, mx, -⟩ := mem_coinFrames.mp hx
      rename_i hsc htc
      have cmem := kid_settled member hc'
      have := below c cmem htc hsc x inDesc
      rw [mx] at this
      cases this
    · refine pullIn f' _ src amt ?_ hd hs fits
      obtain ⟨rel, -⟩ := child_spawned exc hc'
      rcases rel with ce | te
      · exact ce.trans target
      · exact absurd (tc.symm.trans (te.trans target)) hPool
  reply := by
    intro pre rest L₁ L₂ P c split kidsEq at' mutable tc hd hlen
    have Pmem : P ∈ (d.sincePool h).settledFrames := by
      rw [split]
      exact List.mem_append_right _ List.mem_cons_self
    have cKid : c ∈ Exec.childFrames P.run := by
      rw [kidsEq]
      exact List.mem_append_right _ List.mem_cons_self
    have cmem := kid_settled Pmem cKid
    have splitC : (d.sincePool h).settledFrames =
        (pre ++ P :: blocks L₁) ++ c :: (Exec.descendantFrames c.run ++ blocks L₂ ++ rest) := by
      rw [split, blocks_append]
      simp only [blocks, List.flatMap_cons, Exec.Frame.committedFrames_self, List.append_assoc, List.cons_append]
    have above : Exec.NoOpaqueAbove (fun G => G.sevm.currentTarget = T ∧ G.sevm.isStatic = false) pre P := by
      intro b' G m n hp hde op
      have Gmem : G ∈ (d.sincePool h).settledFrames := by
        rw [split, hp]
        exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
      have inDesc : P ∈ Exec.descendantFrames G.run := by
        rw [hde]
        exact List.mem_append_right _ List.mem_cons_self
      have := below G Gmem op.1 op.2 P inDesc
      rw [mutable] at this
      cases this
    have noOp := noOpaque_child (L₁ := L₁) (c := c) above fun op => hPool (op.1.symm.trans at')
    have chain := L.at_ splitC noOp
    have sub : ∀ F ∈ pre ++ P :: blocks L₁, F ∈ (d.sincePool h).settledFrames := fun F hF => by
      rw [splitC]
      exact List.mem_append_left _ hF
    have chain₀ := chain
    have cfP : coinFrames T (fun _ => True) (pre ++ P :: blocks L₁) =
        coinFrames T (fun _ => True) pre ++ coinFrames T (fun _ => True) (blocks L₁) := by
      rw [show pre ++ P :: blocks L₁ = pre ++ ([P] ++ blocks L₁) from rfl, coinFrames_append, coinFrames_append]
      congr 1
      have : coinFrames T (fun _ => True) [P] = [] := by
        refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
        obtain ⟨m, tx, -, -⟩ := mem_coinFrames.mp hx
        rw [List.mem_singleton] at m
        subst m
        exact hPool (tx.symm.trans at')
      rw [this, List.nil_append]
    rw [cfP] at chain
    obtain ⟨st, ck, hc, ht⟩ := A.poolFrames Pmem at' mutable
    obtain ⟨sevm, pb, post, exc, cm, e, H⟩ := A.poolAt Pmem at' mutable ck ⟨hc, ht⟩
    subst e
    exact ⟨wordsAt T c.pre.state, viewChain_id chain, answer H c cKid cmem tc hd _ sub chain₀⟩

/-! ## What the pool sends a coin -/

/-- **`ownCalls`, of the history.** A non-static frame at a coin called by the pool is on the pool's coin selectors. -/
theorem pool_ownCalls_history (A : Assumes d h) {T : Adr} (hTok : T ≠ c3) {F : Exec.Frame}
    (member : F ∈ (d.sincePool h).settledFrames) (target : F.sevm.currentTarget = T) (mutable : F.sevm.isStatic = false)
    (caller : F.sevm.caller = pool)
    (below : ∀ G ∈ (d.sincePool h).settledFrames, F ∈ Exec.childFrames G.run → G.sevm.isStatic = false →
      G.sevm.currentTarget = F.sevm.currentTarget → False) :
    PoolCoinSel (Blanc.Sevm.selector F.sevm) := by
  obtain ⟨b₀, a₀, split⟩ := List.append_of_mem member
  have forest := (d.sincePool h).settledFrames_eq
  have rootsNe : ∀ R ∈ (d.sincePool h).settledRoots, R.sevm.caller ≠ pool := by
    have capabilities := BodyStageCapabilities.historical
    exact (d.sincePool h).settledRoots_caller_ne_of_stateInv
      (Curve3Pool.poolSpec_preservesAdmittedH pool (Curve3Pool.poolEntryAtH Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN))
      capabilities (Curve3Pool.pool_mid_trace_admitted A.midFactsPool) ((d.sincePool h).rewardCreditsFunded capabilities)
      (c := Curve3Pool.poolSpec) ⟨A.poolStart.1, trivial, trivial⟩ Curve3Pool.pool_runtimeSafety rfl (by decide)
  rcases (rootFrames_forest (forest.symm.trans split)).2 with root | ⟨b₁, G, b₂, hb, child, ⟨relation, static⟩, -⟩
  · exact absurd caller (rootsNe F root)
  · have Gmem : G ∈ (d.sincePool h).settledFrames := by
      rw [split, hb]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    cases mutableG : G.sevm.isStatic
    · rcases relation with ce | te
      · have at' : G.sevm.currentTarget = pool := ce.symm.trans caller
        obtain ⟨st, ck, hc, ht⟩ := A.poolFrames Gmem at' mutableG
        obtain ⟨sevm, pb, post, exc, cm, e, H⟩ := A.poolAt Gmem at' mutableG ck ⟨hc, ht⟩
        subst e
        rcases H.children with hall | hall
        · rcases hall F child with tk | ⟨-, sel⟩
          · exact absurd (target.symm.trans (tk.trans H.parties.token)) hTok
          · exact sel
        · rw [hall F child] at mutable
          cases mutable
      · exact (below G Gmem child mutableG te.symm).elim
    · rw [static mutableG] at mutable
      cases mutable

/-- **The walk, over the whole history from the pool's creation.** At the end the books are at most what the position
reads, and across each step moving nothing out, the coin's answers cover the books at the frame's entry. -/
theorem _root_.Blanc.Composition.Curve3PoolPublic.Assumes.coin_walk_whole (A : Assumes d h) {B : CoinBook} {k : Fin 3}
    {a b : StorWords}
    (W : CoinWalk B pool k (d.sincePool h).settledFrames (d.sincePool h).settledRoots a b Curve3Pool.Creation.coinsN
      Curve3Pool.Creation.tokenN) :
    recorded future.state k ≤ B.Rd (B.cf (d.sincePool h).settledFrames) b ∧
      ∃ invs : List PoolInvocation, (∀ i ∈ invs, i.Authentic pool) ∧
        invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = Curve3Pool.committedPoolFramesMid pool (d.sincePool h) ∧
        ∃ s, PoolRun (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat) invs s ∧
        RepliesCovered B.T pool k (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat) invs := by
  obtain ⟨invs, obs, auth, entries, s, run, hc⟩ := A.replay
  have zero : (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat).balances.get k = 0 := by
    match k with
    | 0 | 1 | 2 => rfl
  have start : B.Covered a [] ((Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat).balances.get k) :=
    ⟨a, rfl, by rw [zero]; exact Nat.zero_le _⟩
  obtain ⟨⟨m, hm, hr⟩, replies⟩ := coin_walk W invs (pre := []) (fs := (d.sincePool h).settledFrames) (post := []) run
    entries auth obs (by simp only [List.nil_append, List.append_nil]) (TargetClosed.nil pool)
    (by
      rw [List.nil_append]
      exact Curve3PoolSupply.targetClosed_of_forest W.forest) rfl rfl start
  rw [List.nil_append] at hm hr
  obtain rfl := chain_det hm W.ledger.loc.chain
  refine ⟨?_, invs, auth, obs, s, run, replies⟩
  rw [recorded_of_abstracts hc.abs]
  exact hr

end Replay

end Blanc.Composition.Curve3PoolBacked
