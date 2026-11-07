import Blanc.Composition.Curve3PoolBackedUsdt
import Blanc.Composition.UsdcTokenCore
import Blanc.Lift.Usdc.EntryPositional
import Blanc.Composition.Curve3PoolUsdcEntryApart
import Blanc.Lift.Usdc.V2Answer
import Blanc.Lift.Usdc.V2_1Answer

/-!
# The pool's books of USDC are covered

USDC reads one word two ways: FiatTokenV2_2 its low 255 bits, the earlier versions the whole word. A position reads the whole
word until a chain frame before it has run V2_2, and the bits after. Entering the first such frame the reading can only rise,
by `UsdcMovesOnce.firstRead`; by `UsdcMovesOnce.onward` a frame running an earlier version has no such frame before it, so it
reads as its position does. A reader's answer is its position's reading the same way. At the end, `UsdcMovesOnce.atTip` covers
USDC naming V2_2's address before any chain frame has run it.
-/

namespace Blanc.Composition.Curve3PoolBacked

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolPublic Blanc.Composition.Curve3PoolCoinKeep
open Blanc.Lift.Curve3Pool (answerWord balanceOfData transferSel transferFromSel adrOf)
open Blanc.Lift.CurveCoins (PoolCoinSel)

variable {d : Deployment} {future : BlockChain} {h : MainnetHistory d.minter.post future}

open Classical in
/-- What a position after chain frames `xs` reads of word `w`: the bits once one of them has run V2_2, the whole word before. -/
noncomputable def usdcRead (xs : List Exec.Frame) (w : B256) : Nat :=
  if ∃ G ∈ xs, Usdc.V22At usdc G then Usdc.balanceBits w else w.toNat

theorem usdcRead_seen {xs : List Exec.Frame} {G : Exec.Frame} (w : B256) (mem : G ∈ xs) (v22 : Usdc.V22At usdc G) :
    usdcRead xs w = Usdc.balanceBits w :=
  ite_eq_left ⟨G, mem, v22⟩

theorem usdcRead_unseen {xs : List Exec.Frame} (w : B256) (none : ∀ G ∈ xs, ¬ Usdc.V22At usdc G) :
    usdcRead xs w = w.toNat :=
  ite_eq_right fun ⟨G, mem, v22⟩ => none G mem v22

/-- USDC's entry for the pool, as a book, read by position. -/
noncomputable def usdcBook : CoinBook where
  T := usdc
  V := Usdc.ledgerView
  Obs := Usdc.ChainObs usdc
  Good := Usdc.EntryGood usdc
  held := Usdc.heldAt usdc pool
  debit := ownDebit pool
  credit := ownCredit pool
  Rd := fun xs m => usdcRead xs (m (Usdc.balSlot pool))

theorem pool_bal_ne_impl : Usdc.balSlot pool ≠ Usdc.implSlot := Usdc.entryApart_pool.impl
theorem pool_bal_ne_admin : Usdc.balSlot pool ≠ Usdc.adminSlot := Usdc.entryApart_pool.admin

theorem view_bal (w : StorWords) : Usdc.ledgerView w (Usdc.balSlot pool) = w (Usdc.balSlot pool) :=
  Usdc.ledgerView_bal pool_bal_ne_impl pool_bal_ne_admin

/-! ## What USDC answers -/

/-- **A committed `balanceOf` frame of the proxy answers the entry it names, as its version reads it.** -/
theorem usdc_balanceOf_answer {F : Exec.Frame} (pc : F.pc = 0) (code : F.sevm.code = Usdc.Proxy.code)
    (fork : HistFork F.sevm.benvStat.fork) (has : (F.pre.getCode F.sevm.currentTarget).toList ≠ [])
    (notAdmin : F.sevm.caller ≠ Usdc.adminOf F.pre.state F.sevm.currentTarget)
    (certified : Usdc.UsdcCertified F.pre F.sevm.currentTarget) (size : F.sevm.data.length < 2 ^ 256)
    (sel : Blanc.Sevm.selector F.sevm = 0x70a08231) :
    (Usdc.V22At F.sevm.currentTarget F → F.post.output =
      (lo255 &&& (F.pre.state.getStor F.sevm.currentTarget).get (Usdc.balSlot (Sevm.dataWord F.sevm 4).toAdr)).toBytes) ∧
    (¬ Usdc.V22At F.sevm.currentTarget F → F.post.output =
      ((F.pre.state.getStor F.sevm.currentTarget).get (Usdc.balSlot (Sevm.dataWord F.sevm 4).toAdr)).toBytes) := by
  obtain ⟨fpc, sevm, pre, out, run, committed⟩ := F
  dsimp only at pc code fork has notAdmin certified size sel ⊢
  subst pc
  cases out with
  | error e => cases committed
  | ok post =>
  have hsg := fork.stateGas_none
  have version : CurveCoins.UsdcVersion (pre.getCode (pre.getStorVal sevm.currentTarget Usdc.implSlot).toAdr) := certified.1
  obtain ⟨G, E⟩ := Usdc.proxy_entry_child run code hsg fork.bal_none has notAdmin version.not_delegation
    (certified.2.2 _) size
  have gfork : HistFork G.sevm.benvStat.fork := by rw [E.stat]; exact fork
  have gsel : Blanc.Sevm.selector G.sevm = 0x70a08231 := by
    simp only [Blanc.Sevm.selector, Sevm.dataWord, E.data] at sel ⊢
    exact sel
  have gword : Sevm.dataWord G.sevm 4 = Sevm.dataWord sevm 4 := by
    simp only [Sevm.dataWord, E.data]
  have gval : ∀ k, G.pre.getStorVal G.sevm.currentTarget k = (pre.state.getStor sevm.currentTarget).get k := fun k => by
    rw [E.target]
    exact congrArg (fun s => Stor.get s k) E.preStor
  have out' : post.output = G.post.output := E.output
  have st : G.pre = St G.pre [] Mem.empty G.pre.gasLeft := by
    rw [← E.fresh.1, ← E.fresh.2]
    exact St.self' _
  constructor
  · intro v22
    have gcode : G.sevm.code = Usdc.Impl.code := E.code.trans v22
    have r := run_of_frame Usdc.Impl.cert_check rfl E.pc gcode gfork.stateGas_none
    rw [E.fresh.1, E.fresh.2] at r
    have o := UsdcToken.frame_balanceOf_output gfork gsel r
    rw [gword, gval] at o
    change _ = (lo255 &&& _).toBytes
    exact out'.trans o
  · intro notV22
    rcases version with c | c | c
    · have gcode := E.code.trans c
      have r := run_of_frame Usdc.ImplV2.cert_check rfl E.pc gcode gfork.stateGas_none
      have o := Usdc.ImplV2.frame_balanceOf_output gfork E.wf gsel r
      rw [gword, gval] at o
      exact out'.trans o
    · have gcode := E.code.trans c
      have r := run_of_frame Usdc.ImplV2_1.cert_check rfl E.pc gcode gfork.stateGas_none
      have o := Usdc.ImplV2_1.frame_balanceOf_output gfork E.wf gsel r
      rw [gword, gval] at o
      exact out'.trans o
    · exact (notV22 c).elim

/-! ## The walk -/

theorem usdc_ne_pool : usdc ≠ pool := by decide

theorem pool_ne_lib : Curve3Pool.code ≠ Usdc.Lib.code := fun e => absurd (congrArg ByteArray.size e) (by decide +kernel)

theorem pool_not_version : ¬ CurveCoins.UsdcVersion Curve3Pool.code := by
  rintro (e | e | e) <;> exact absurd (congrArg ByteArray.size e) (by decide +kernel)

/-- A child of a settled frame at USDC running the proxy was called by USDC itself. -/
theorem usdc_kid_caller (A : Assumes d h) {G F : Exec.Frame} (member : G ∈ (d.sincePool h).settledFrames)
    (parent : G.sevm.currentTarget = usdc) (child : F ∈ Exec.childFrames G.run) (code : F.sevm.code = Usdc.Proxy.code) :
    F.sevm.caller = usdc :=
  Usdc.settled_child_caller (d.sincePool h) BodyStageCapabilities.historical A.circle.usdcCode A.circle.usdcCertified member
    parent child code

/-- **USDC's locality over the history from the pool's creation**, from `Assumes` alone. -/
theorem usdc_local (A : Assumes d h) :
    EntryLocalAt usdc Usdc.ledgerView (Usdc.ChainObs usdc) (Usdc.EntryGood usdc) (Usdc.heldAt usdc pool) (ownDebit pool)
      (ownCredit pool) (Usdc.ledgerView (wordsAt usdc d.poolCut.afterBenv.state))
      (Usdc.ledgerView (wordsAt usdc future.state)) (d.sincePool h).settledFrames := by
  have capabilities := BodyStageCapabilities.historical
  refine Usdc.usdc_entryLocalAt (d.sincePool h) capabilities A.circle.usdcCode A.circle.usdcCertified Usdc.entryApart_pool
    A.hashes.coinKeys.usdc (NoKeyHolder.usdcAuthority (d.sincePool h) capabilities A.keys A.circle.usdcCode
      A.circle.usdcCertified fun F hF caller => ?_)
  obtain ⟨member, target, mutable, obs⟩ := mem_coinFrames.mp hF
  refine pool_ownCalls_history A (T := usdc) (by decide) member target mutable caller fun G hG child mg te => ?_
  have := usdc_kid_caller A hG (te.trans target) child obs.1.1
  rw [caller] at this
  exact usdc_ne_pool this.symm

/-- A chain frame at a position of the frames' chain lies at a split of the frames, with that position before it. -/
theorem coinFrames_split {T : Adr} {Obs : Exec.Frame → Prop} {F : Exec.Frame} : ∀ {fs xs ys : List Exec.Frame},
    coinFrames T Obs fs = xs ++ F :: ys → ∃ before after, fs = before ++ F :: after ∧ coinFrames T Obs before = xs
  | [], xs, _, e => by cases xs <;> simp only [coinFrames, List.flatMap_nil, List.nil_append, List.cons_append, reduceCtorEq] at e
  | g :: fs, xs, ys, e => by
    rw [show g :: fs = [g] ++ fs from rfl, coinFrames_append] at e
    by_cases h : coinFrames T Obs [g] = []
    · rw [h, List.nil_append] at e
      obtain ⟨before, after, rfl, c⟩ := coinFrames_split e
      refine ⟨g :: before, after, rfl, ?_⟩
      rw [show g :: before = [g] ++ before from rfl, coinFrames_append, h, c, List.nil_append]
    · have single : coinFrames T Obs [g] = [g] := by
        simp only [coinFrames, List.flatMap_cons, List.flatMap_nil, List.append_nil, coinObs] at h ⊢
        split at h
        · rw [ite_eq_left ‹_›]
        · exact (h rfl).elim
      rw [single] at e
      cases xs with
      | nil =>
        obtain ⟨rfl, -⟩ := List.cons.inj e
        exact ⟨[], fs, rfl, rfl⟩
      | cons x xs =>
        obtain ⟨rfl, tail⟩ := List.cons.inj e
        obtain ⟨before, after, rfl, c⟩ := coinFrames_split (xs := xs) tail
        refine ⟨g :: before, after, rfl, ?_⟩
        rw [show g :: before = [g] ++ before from rfl, coinFrames_append, single, c]
        rfl

/-- **Before a frame running an earlier version, no chain frame has run V2_2**, by `onward`. -/
theorem none_before (A : Assumes d h) {before after : List Exec.Frame} {c : Exec.Frame}
    (split : (d.sincePool h).settledFrames = before ++ c :: after) (target : c.sevm.currentTarget = usdc)
    (obs : Usdc.ChainObs usdc c) (notV22 : ¬ Usdc.V22At usdc c) :
    ∀ G ∈ coinFrames usdc (Usdc.ChainObs usdc) before, ¬ Usdc.V22At usdc G := by
  intro G hG v22
  obtain ⟨inBefore, targetG, -, obsG⟩ := mem_coinFrames.mp hG
  obtain ⟨b₁, b₂, rfl⟩ := List.append_of_mem inBefore
  have whole : (d.sincePool h).settledFrames = b₁ ++ G :: (b₂ ++ c :: after) := by
    rw [split]
    simp only [List.append_assoc, List.cons_append]
  exact notV22 (A.circle.movesOnce.onward b₁ G _ whole targetG obsG v22 c
    (List.mem_append_right _ List.mem_cons_self) target obs)

/-- **What a reader answers is its position's reading**: the whole word under an earlier version, by `onward`, and the bits
under V2_2, by `firstRead` if nothing before it has run V2_2. -/
theorem reply_read (A : Assumes d h) {before after : List Exec.Frame} {c : Exec.Frame} {v : Nat}
    (split : (d.sincePool h).settledFrames = before ++ c :: after) (target : c.sevm.currentTarget = usdc)
    (obs : Usdc.ChainObs usdc c)
    (bits : Usdc.V22At usdc c → v = Usdc.balanceBits (wordsAt usdc c.pre.state (Usdc.balSlot pool)))
    (whole : ¬ Usdc.V22At usdc c → v = (wordsAt usdc c.pre.state (Usdc.balSlot pool)).toNat) :
    v = usdcRead (coinFrames usdc (Usdc.ChainObs usdc) before) (wordsAt usdc c.pre.state (Usdc.balSlot pool)) := by
  by_cases v22 : Usdc.V22At usdc c
  · rw [bits v22]
    by_cases seen : ∃ G ∈ coinFrames usdc (Usdc.ChainObs usdc) before, Usdc.V22At usdc G
    · obtain ⟨G, gm, gv⟩ := seen
      rw [usdcRead_seen _ gm gv]
    · have none : ∀ G ∈ coinFrames usdc (Usdc.ChainObs usdc) before, ¬ Usdc.V22At usdc G := fun G gm gv => seen ⟨G, gm, gv⟩
      rw [usdcRead_unseen _ none]
      exact Usdc.bits_eq_of_lt (A.circle.movesOnce.firstRead before c after split target obs v22 none)
  · rw [whole v22, usdcRead_unseen _ (none_before A split target obs v22)]

/-- How a frame reads the pool's entry does not see the view. -/
theorem heldAt_view (F : Exec.Frame) (w : StorWords) :
    Usdc.heldAt usdc pool F (Usdc.ledgerView w) = Usdc.heldAt usdc pool F w := by
  unfold Usdc.heldAt
  rw [view_bal]

/-- USDC's ledger against the pool's books. -/
theorem usdc_ledger (A : Assumes d h) :
    Ledger usdcBook pool (d.sincePool h).settledFrames (Usdc.ledgerView (wordsAt usdc d.poolCut.afterBenv.state))
      (Usdc.ledgerView (wordsAt usdc future.state)) where
  loc := usdc_local A
  seam := fun xs F ys split => by
    obtain ⟨before, after, whole, position⟩ := coinFrames_split (T := usdc) (Obs := Usdc.ChainObs usdc) split
    have mem : F ∈ coinFrames usdc (Usdc.ChainObs usdc) (d.sincePool h).settledFrames := by
      change F ∈ usdcBook.cf _
      rw [split]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨-, target, -, obs⟩ := mem_coinFrames.mp mem
    rw [show usdcBook.V = Usdc.ledgerView from rfl, show usdcBook.T = usdc from rfl,
      show usdcBook.held = Usdc.heldAt usdc pool from rfl, show usdcBook.Rd = fun xs m => usdcRead xs (m (Usdc.balSlot pool)) from rfl]
    dsimp only
    rw [view_bal, heldAt_view]
    unfold Usdc.heldAt
    by_cases seen : ∃ G ∈ xs, Usdc.V22At usdc G
    · obtain ⟨G, gm, gv⟩ := seen
      rw [usdcRead_seen _ gm gv]
      split
      · exact Nat.le_refl _
      · exact Usdc.bits_le_word _
    · have none : ∀ G ∈ xs, ¬ Usdc.V22At usdc G := fun G gm gv => seen ⟨G, gm, gv⟩
      rw [usdcRead_unseen _ none]
      split
      · rename_i v22
        exact Nat.le_of_eq (Usdc.bits_eq_of_lt (A.circle.movesOnce.firstRead before F after whole target obs v22
          (by rw [position]; exact none))).symm
      · exact Nat.le_refl _
  leave := fun xs F ys split => by
    obtain ⟨before, after, whole, position⟩ := coinFrames_split (T := usdc) (Obs := Usdc.ChainObs usdc) split
    have mem : F ∈ coinFrames usdc (Usdc.ChainObs usdc) (d.sincePool h).settledFrames := by
      change F ∈ usdcBook.cf _
      rw [split]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨-, target, -, obs⟩ := mem_coinFrames.mp mem
    rw [show usdcBook.V = Usdc.ledgerView from rfl, show usdcBook.T = usdc from rfl,
      show usdcBook.held = Usdc.heldAt usdc pool from rfl, show usdcBook.Rd = fun xs m => usdcRead xs (m (Usdc.balSlot pool)) from rfl]
    dsimp only
    rw [view_bal, heldAt_view]
    unfold Usdc.heldAt
    split
    · rename_i v22
      rw [usdcRead_seen _ (List.mem_append_right _ List.mem_cons_self) v22]
    · rename_i notV22
      have none := none_before A whole target obs notV22
      rw [position] at none
      rw [usdcRead_unseen]
      intro G gm
      rcases List.mem_append.mp gm with gm | gm
      · exact none G gm
      · rw [List.mem_singleton.mp gm]
        exact notV22
  third := fun _ _ ne => ite_eq_left ne

variable {sevm : Sevm} {pb post : Devm} {exc : Exec 0 sevm pb (.ok post)} {s : Curve3Pool.State}

/-- A pool frame's child at USDC on the pool's selectors is a reader of USDC's ledger, running the proxy. -/
theorem usdc_child_obs (H : PoolAt exc s) {c : Exec.Frame} (hc : c ∈ Exec.childFrames exc)
    (target : c.sevm.currentTarget = usdc) (sel : PoolCoinSel (Blanc.Sevm.selector c.sevm)) :
    CodeFrame usdc HistFork Usdc.Proxy.code c ∧ Usdc.ChainObs usdc c := by
  have good := H.child_good H.world.usdcCode Usdc.proxy_toList_ne_nil Usdc.proxy_not_delegation hc target
  have notAdmin := Curve3PoolCoinKeep.usdc_child_notAdmin c good.1 good.2.1 good.2.2.1.stateGas_none good.2.2.1.bal_none sel
  rw [target] at notAdmin
  refine ⟨good, ⟨good.2.1, notAdmin⟩, ?_⟩
  rcases sel with e | e | e <;> rw [e] <;> decide

/-- What the pool sends USDC is on the pool's selectors. -/
theorem usdc_child_sel (H : PoolAt exc s) {c : Exec.Frame} (hc : c ∈ Exec.childFrames exc)
    (mutable : c.sevm.isStatic = false) (target : c.sevm.currentTarget = usdc) :
    PoolCoinSel (Blanc.Sevm.selector c.sevm) := by
  rcases H.children with hall | hall
  · rcases hall c hc with tk | ⟨-, sel⟩
    · exact absurd (target.symm.trans (tk.trans H.parties.token)) (by decide)
    · exact sel
  · rw [hall c hc] at mutable
    cases mutable

/-- Nothing below a link of the chain is a link. -/
theorem usdc_kid_quiet (A : Assumes d h) {c : Exec.Frame} (member : c ∈ (d.sincePool h).settledFrames)
    (good : CodeFrame usdc HistFork Usdc.Proxy.code c) (target : c.sevm.currentTarget = usdc)
    (obs : Usdc.ChainObs usdc c) : coinFrames usdc (Usdc.ChainObs usdc) (Exec.descendantFrames c.run) = [] := by
  have certified := A.circle.usdcCertified c member target good.2.1 obs.1.2
  have size := Usdc.settled_data_bound (d.sincePool h) BodyStageCapabilities.historical c member
  obtain ⟨pc0, code, fork, -⟩ := good
  obtain ⟨cobs, notRescue⟩ := obs
  have quiet : (Exec.descendantFrames c.run).flatMap (coinObs usdc (Usdc.EntryObs usdc)) = [] := by
    obtain ⟨fpc, csevm, pre, out, run, committed⟩ := c
    dsimp only at pc0 code fork target cobs notRescue certified size ⊢
    subst pc0
    cases out with
    | error e => cases committed
    | ok post => exact Usdc.entryQuiet run code fork target cobs.2 notRescue certified size
  refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
  obtain ⟨inDesc, tx, mx, ox⟩ := mem_coinFrames.mp hx
  have nil := List.flatMap_eq_nil_iff.mp quiet x inDesc
  rw [coinObs, ite_eq_left ⟨tx, mx, ox.1⟩] at nil
  cases nil

/-- **USDC's `CoinWalk`.** -/
theorem usdcWalk (A : Assumes d h) :
    CoinWalk usdcBook pool 1 (d.sincePool h).settledFrames (d.sincePool h).settledRoots
      (Usdc.ledgerView (wordsAt usdc d.poolCut.afterBenv.state)) (Usdc.ledgerView (wordsAt usdc future.state))
      Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN where
  ledger := usdc_ledger A
  forest := (d.sincePool h).settledFrames_eq
  roots := A.rootsNe
  targetNe := usdc_ne_pool
  coinAt := coin1_eq
  coinOther := fun j hj => by
    match j, hj with
    | 0, _ => decide +kernel
    | 2, _ => decide +kernel
    | 1, hj => exact absurd rfl hj
  tokNe := by decide +kernel
  parties := fun f member t => A.midFactsPool.parties _ ((d.sincePool h).mem_rawFrames_of_mem_settledFrames f member) t
  delegate := fun F hF G hG child _ te caller => by
    obtain ⟨-, target, -, obs⟩ := mem_coinFrames.mp hF
    have := usdc_kid_caller A hG (te.trans target) child obs.1.1
    rw [caller] at this
    exact usdc_ne_pool this.symm
  kids := by
    intro f member target mutable st ck hc ht
    obtain ⟨sevm, pb, post, exc, cm, rfl, H⟩ := A.poolAt member target mutable ck ⟨hc, ht⟩
    refine ⟨fun c hc' => kid_sub H hc' (fun ms tc => (usdc_child_obs H hc' tc (usdc_child_sel H hc' ms tc)).2) fun ms tc => ?_,
      fun c _ _ dst amt hd => ownDebit_transfer hd, fun c _ _ src amt hd hs => ownDebit_transferFrom hd hs,
      fun _ c hc' tc src amt hd hs fits => ?_⟩
    · obtain ⟨good, obs⟩ := usdc_child_obs H hc' tc (usdc_child_sel H hc' ms tc)
      exact usdc_kid_quiet A (kid_settled member hc') good tc obs
    · refine ownCredit_transferFrom ?_ hd hs fits
      obtain ⟨rel, -⟩ := child_spawned exc hc'
      rcases rel with ce | te
      · exact ce.trans target
      · exact absurd (tc.symm.trans (te.trans target)) usdc_ne_pool
  reply := by
    intro pre rest L₁ L₂ P c split kidsEq at' mutable tc hd hlen
    replace tc : c.sevm.currentTarget = usdc := tc
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
    have capabilities := BodyStageCapabilities.historical
    have subPre : ∀ F ∈ pre, F ∈ (d.sincePool h).settledFrames := fun F hF => by
      rw [split]
      exact List.mem_append_left _ hF
    have poolCode := (A.poolOwn Pmem at').1
    have above : Exec.NoOpaqueAbove (Usdc.LinkFrame usdc) pre P :=
      Usdc.noLink_above (d.sincePool h) capabilities A.circle.usdcCode A.circle.usdcCertified subPre mutable
        (by rw [poolCode]; exact pool_ne_lib) (by rw [poolCode]; exact pool_not_version)
    have noOp := noOpaque_child (L₁ := L₁) (c := c) above fun op => usdc_ne_pool (op.1.symm.trans at')
    have chain := Usdc.usdc_viewAt_links (d.sincePool h) capabilities A.circle.usdcCode A.circle.usdcCertified splitC noOp
    have cfP : coinFrames usdc (Usdc.ChainObs usdc) (pre ++ P :: blocks L₁) =
        coinFrames usdc (Usdc.ChainObs usdc) pre ++ coinFrames usdc (Usdc.ChainObs usdc) (blocks L₁) := by
      rw [show pre ++ P :: blocks L₁ = pre ++ ([P] ++ blocks L₁) from rfl, coinFrames_append, coinFrames_append]
      congr 1
      have : coinFrames usdc (Usdc.ChainObs usdc) [P] = [] := by
        refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
        obtain ⟨m, tx, -, -⟩ := mem_coinFrames.mp hx
        rw [List.mem_singleton] at m
        subst m
        exact usdc_ne_pool (tx.symm.trans at')
      rw [this, List.nil_append]
    rw [cfP] at chain
    obtain ⟨st, ck, hc, ht⟩ := A.poolFrames Pmem at' mutable
    obtain ⟨sevm, pb, post, exc, cm, e, H⟩ := A.poolAt Pmem at' mutable ck ⟨hc, ht⟩
    subst e
    have sel : Blanc.Sevm.selector c.sevm = 0x70a08231 :=
      selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
    have word4 : Sevm.dataWord c.sevm 4 = pool.toB256 :=
      Curve3PoolSupply.dataWord_eq_of_append (pre := Curve3Pool.balanceOfSel) (rest := [])
        (by rw [hd, List.append_nil]; rfl) (by decide)
    obtain ⟨good, obs⟩ := usdc_child_obs H cKid tc (.inr (.inr sel))
    obtain ⟨pc0, code, fork, has⟩ := good
    have notAdmin := obs.1.2
    have certified := A.circle.usdcCertified c cmem tc code notAdmin
    have size := Usdc.settled_data_bound (d.sincePool h) capabilities c cmem
    rw [← tc] at notAdmin certified has
    obtain ⟨atV22, atWords⟩ := usdc_balanceOf_answer pc0 code fork has notAdmin certified size sel
    rw [word4, toAdr_toB256, tc] at atV22 atWords
    refine ⟨Usdc.ledgerView (wordsAt usdc c.pre.state), chain, ?_⟩
    change answerWord c.post.output = usdcRead (coinFrames usdc (Usdc.ChainObs usdc) pre ++
      coinFrames usdc (Usdc.ChainObs usdc) (blocks L₁)) (Usdc.ledgerView (wordsAt usdc c.pre.state) (Usdc.balSlot pool))
    rw [view_bal, ← cfP]
    refine reply_read A splitC tc obs (fun v22 => ?_) fun v22 => ?_
    · rw [answerWord, atV22 v22, List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes,
        Usdc.lo255_and_toNat]
      rfl
    · rw [answerWord, atWords v22, List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes]
      rfl

/-- **A position's reading is at most what USDC's storage says the pool holds**, given the word below the flag wherever USDC
names V2_2's address before a chain frame has run it. -/
theorem usdcRead_le_coinHeld (w : State) {xs : List Exec.Frame}
    (below : UsdcPacked w → (∀ G ∈ xs, ¬ Usdc.V22At usdc G) → ((w.getStor usdc).get (Usdc.balSlot pool)).toNat < 2 ^ 255) :
    usdcRead xs ((w.getStor usdc).get (Usdc.balSlot pool)) ≤ coinHeld w pool 1 := by
  unfold coinHeld
  by_cases seen : ∃ G ∈ xs, Usdc.V22At usdc G
  · obtain ⟨G, gm, gv⟩ := seen
    rw [usdcRead_seen _ gm gv]
    split
    · exact Nat.le_refl _
    · exact Usdc.bits_le_word _
  · have none : ∀ G ∈ xs, ¬ Usdc.V22At usdc G := fun G gm gv => seen ⟨G, gm, gv⟩
    rw [usdcRead_unseen _ none]
    split
    · rename_i c
      exact Nat.le_of_eq (Usdc.bits_eq_of_lt (below c.2 none)).symm
    · exact Nat.le_refl _

/-- **The pool's books of USDC are at most what USDC's storage says it holds.** -/
theorem usdc_backed (A : Assumes d h) : recorded future.state 1 ≤ coinHeld future.state pool 1 := by
  have r := (A.coin_walk_whole (usdcWalk A)).1
  change _ ≤ usdcRead (coinFrames usdc (Usdc.ChainObs usdc) (d.sincePool h).settledFrames)
    (Usdc.ledgerView (wordsAt usdc future.state) (Usdc.balSlot pool)) at r
  rw [view_bal] at r
  exact r.trans (usdcRead_le_coinHeld _ A.circle.movesOnce.atTip)

end Blanc.Composition.Curve3PoolBacked
