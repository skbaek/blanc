import Blanc.Composition.Curve3PoolVirtualPriceCell
import Blanc.Composition.Curve3PoolVirtualPriceDeploy
import Blanc.Composition.Curve3PoolSupplyFrames
import Blanc.Lift.CurveCoins.ApprovalLogsUsdt

/-!
# What the bound reads of a pool frame

A committed non-static frame at the pool, entered at a checkpoint of the recorded coins and token:

* `PoolAt`: its parties are their bytes, the facts its walks take (`pool_at`);
* `PoolAt.no_nested`: nothing below it is another non-static frame at the pool;
* `PoolAt.keeps_foreign`: a child elsewhere keeps every cell of an address with code;
* `PoolAt.add_replies`: on `add_liquidity` with USDT in the amounts, the two replies the model credits are the
  pool's USDT entry at the frame's entry and at its end.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool
open Blanc.Lift.CurveCoins
open Blanc.Composition.Curve3PoolCoinKeep
open Blanc.Composition.Curve3PoolVirtualPrice
open Blanc.Composition.Curve3PoolSupply (descendantFrames_eq_children)

/-- What a frame's walks take, at the recorded parties. -/
structure PoolAt {sevm : Sevm} {b post : Devm} (exc : Exec 0 sevm b (.ok post)) (s : Curve3Pool.State) : Prop where
  code : sevm.code = Curve3Pool.code
  fork : HistFork sevm.benvStat.fork
  cd : sevm.data.length < 2 ^ 256
  stack : b.stack = []
  mem : b.memory = Mem.empty
  gas : b.gasMeasure < 2 ^ 256
  static : sevm.isStatic = false
  pc : b.getCode sevm.currentTarget ≠ .empty
  ck : Checkpoint (b.getStor sevm.currentTarget) s
  id : IdReadyH sevm b
  tok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr
  coin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr
  world : PoolWorld exc dai usdc usdt c3
  parties : PartiesAt (b.getStor sevm.currentTarget) sevm.currentTarget dai usdc usdt c3
  coinIs : ∀ k : Fin 3, ((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr =
    adrOf (Curve3Pool.Creation.coinsN.get k)

section At

variable {cfg : ChainConfig} {start : Benv} {future checkpoint : BlockChain}
  {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
  {trace : MidHistoryTraceIn HistFork cfg start future}

/-- **A settled non-static pool frame, entered at a checkpoint of the recorded parties, is a `PoolAt`.** -/
theorem pool_at (facts : PoolMidFacts full trace pool Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN)
    (frames : FramesHold trace dai usdc usdt c3) {f : Exec.Frame} (member : f ∈ trace.settledFrames)
    (target : f.sevm.currentTarget = pool) (hstatic : f.sevm.isStatic = false)
    (hcode : f.sevm.code = Curve3Pool.code) (hpc : f.pre.getCode f.sevm.currentTarget ≠ .empty)
    {s : Curve3Pool.State} (hck : Checkpoint (f.pre.getStor f.sevm.currentTarget) s)
    (hq : s.coins = Curve3Pool.Creation.coinsN ∧ s.token = Curve3Pool.Creation.tokenN) :
    ∃ (sevm : Sevm) (b post : Devm) (exc : Exec 0 sevm b (.ok post))
      (cm : Execution.commits (.ok post) = true), f = ⟨0, sevm, b, .ok post, exc, cm⟩ ∧ PoolAt exc s := by
  have raw : Exec.Frame.rootDeriv f ∈ trace.rawFrames := trace.mem_rawFrames_of_mem_settledFrames f member
  obtain ⟨⟨hstack, hmem⟩, hcd, hgas, hid, hcs, htk, -⟩ := facts.entry raw target
  obtain ⟨hpc0, hfork⟩ := trace.rootEntryIn _ raw
  obtain ⟨cdai, cusdc, cusdt, ctok⟩ := frames.code f member
  have kids : ∀ c ∈ Exec.childFrames f.run, c ∈ trace.settledFrames := fun _ hc =>
    settledFrames_children trace member hc
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
  dsimp only at hpc0 hfork target hcode hpc hstatic hck hstack hmem hcd hgas hid hcs htk cdai cusdc cusdt ctok kids
  subst hpc0
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have habs : Abstracts (entryStor ⟨0, sevm, pre, .ok post, run⟩) s := hck.abs
    have hcw : ∀ k : Fin 3, ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr =
        adrOf (Curve3Pool.Creation.coinsN.get k) := by
      intro k
      have := coinAdr_eq habs k
      rw [hq.1] at this
      exact this
    have htw : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = adrOf Curve3Pool.Creation.tokenN := by
      have := tokenAdr_eq habs
      rw [hq.2] at this
      exact this
    have words := party_words'
    refine ⟨sevm, pre, post, run, committed, rfl, ?_⟩
    exact
      { code := hcode
        fork := hfork
        cd := hcd
        stack := hstack
        mem := hmem
        gas := hgas
        static := hstatic
        pc := hpc
        ck := hck
        id := hid
        tok := by rw [htw]; exact htk
        coin := fun k => by rw [hcw k]; exact hcs k
        world :=
          { daiCode := cdai
            usdcCode := cusdc
            usdtCode := cusdt
            tokCode := ctok
            usdcImpl := fun c hc ht hs => frames.usdcImpl c (kids c hc) ht hs
            usdtLive := fun c hc ht hs => frames.usdtLive c (kids c hc) ht hs }
        parties :=
          { coin := fun k => by rw [hcw k]; exact words.coin k
            token := by rw [htw]; exact words.token
            coinNe := fun k => by rw [hcw k, target]; exact words.coinNe k
            tokNe := by rw [target]; exact words.tokNe
            apart := fun k => by rw [hcw k]; exact words.apart k }
        coinIs := hcw }

end At

/-! ## Nothing nests -/

section Nested

/-- A frame whose raw roots are static or apart from `P` commits no non-static frame at `P`. -/
theorem committed_apart {P : Adr} (c : Exec.Frame)
    (roots : ∀ r ∈ Exec.rawFrameRoots c.run, r.sevm.isStatic = false → r.sevm.currentTarget ≠ P) :
    ∀ f ∈ Exec.committedFrames c.run, f.sevm.isStatic = false → f.sevm.currentTarget ≠ P := by
  intro f hf
  rw [Exec.Frame.committedFrames_run c, List.mem_cons] at hf
  rcases hf with rfl | hf
  · exact roots (Exec.Frame.rootDeriv f) (by
      simp only [Exec.rawFrameRoots, List.mem_cons]
      exact .inl rfl)
  · exact roots (Exec.Frame.rootDeriv f) (List.mem_cons_of_mem _
      (Exec.mem_rawFrameDescendants_of_mem_descendantFrames c.run f hf))

/-- A frame entered from a chain node of certified code that executes only `STATICCALL` is static and enters
only static frames. `ForeignKeep`'s private `staticOnly_child`. -/
theorem staticOnly_child' {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    {root : Exec.Deriv} (pc0 : root.pc = 0) (installed : root.sevm.code = code)
    (rootSg : root.sevm.benvStat.rules.stateGas = none)
    {nodePc nextPc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out raw : Execution} {frame : Jaune.Frame}
    {rsm : Resume} {cevm : Evm} {run : Exec nodePc nodeSevm nodePre out}
    (chain : Exec.Deriv.ParentPrefix root ⟨nodePc, nodeSevm, nodePre, out, run⟩)
    (step : Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc)
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw) :
    ∀ D ∈ Exec.rawFrameRoots child, D.sevm.isStatic = true ∧ D.sevm.codeAddress ≠ none := by
  have sevmEq : nodeSevm = root.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have sg : nodeSevm.benvStat.rules.stateGas = none := by rw [sevmEq]; exact rootSg
  obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
  have onlyStatic : x = .staticcall :=
    parentPrefix_exec_staticcall_of_cert_noStateGas checked only pc0 installed rootSg chain instruction
  subst x
  have fst := Xinst.step_staticcall_spawn_isStatic spawn
  have stc : cevm.sta.isStatic = true := (Frame.enter_run_isStatic enter).trans fst
  obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv enter
  have cca : cevm.sta.codeAddress ≠ none := by
    rw [hcev]; exact Xinst.step_spawn_codeAddress_of_static_noStateGas sg spawn fst
  exact Exec.static_rawFrameRoots_noStateGas child (Evm.step_spawn_child_fork_noStateGas step enter sg) stc cca

/-- **Every frame a USDC proxy frame on the pool's selectors enters runs at USDC.** -/
theorem usdc_roots (c : Exec.Frame) (hpc : c.pc = 0) (hcode : c.sevm.code = Usdc.Proxy.code)
    (hsg : c.sevm.benvStat.rules.stateGas = none) (bal : c.sevm.benvStat.rules.bal = none)
    (hsize : c.sevm.data.length < 2 ^ 256)
    (hI : UsdcImplAt c.pre c.sevm.currentTarget)
    (sel : PoolCoinSel (Blanc.Sevm.selector c.sevm)) :
    ∀ r ∈ Exec.rawFrameRoots c.run, r.sevm.currentTarget = c.sevm.currentTarget := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at hpc hcode hsg bal hsize hI sel
  subst hpc
  intro r hr
  simp only [Exec.rawFrameRoots, List.mem_cons] at hr
  rcases hr with rfl | hr
  · rfl
  refine Exec.rawFrameDescendants_of_chain (Q := fun D => D.sevm.currentTarget = _) (root := ⟨0, sevm, pre, out, run⟩) ?_ run (.refl _) r hr
  intro nodePc nextPc nodeSevm nodePre nodeOut raw frame rsm cevm nrun chain step enter child D hD
  obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
  have env : nodeSevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  subst env
  obtain ⟨f, K, ⟨rfl, delegated⟩ | ⟨rfl, -, hw⟩⟩ := Usdc.Proxy.proxy_nodeH run hcode hsg bal chain hat
  swap
  · rw [Usdc.dispatchWord_eq_selector] at hw
    rcases sel with s | s | s <;> rw [s] at hw <;> exact absurd hw (by decide)
  obtain ⟨-, b', gas, S, M, G, tail, hstate, -, input⟩ := delegated
  change nodePre = _ at input
  subst input
  have hslotCode : (St b' (gas :: pre.getStorVal nodeSevm.currentTarget Usdc.implSlot :: 0 ::
      nodeSevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (nodeSevm.data.sliceD 0 nodeSevm.data.length.toB256.toNat 0)) G).getCode
        (pre.getStorVal nodeSevm.currentTarget Usdc.implSlot).toAdr =
      pre.getCode (pre.getStorVal nodeSevm.currentTarget Usdc.implSlot).toAdr := by
    rw [St_getCode]
    simp only [Devm.getCode, Devm.getAcct, hstate]
  have hcC := Xinst.step_delegatecall_spawn_code hx rfl (by rw [hslotCode]; exact hI.not_delegation)
  obtain ⟨target, -, -, -, data⟩ := Xinst.step_delegatecall_spawn_St_noStateGas hsg hx
  obtain ⟨benv, -, childEq⟩ := Frame.enter_run_inv enter
  subst childEq
  have hdata : frame.inner.data = nodeSevm.data := by
    rw [data]
    have read : ((M.write 0 (nodeSevm.data.sliceD 0 nodeSevm.data.length.toB256.toNat 0)).read 0
        nodeSevm.data.length.toB256.toNat).1 =
        nodeSevm.data.sliceD 0 nodeSevm.data.length.toB256.toNat 0 := by
      by_cases empty : nodeSevm.data.sliceD 0 nodeSevm.data.length.toB256.toNat 0 = []
      · have length := congrArg List.length empty
        simp only [List.length_sliceD, List.length_nil] at length
        rw [empty, length]
        rfl
      · simpa only [List.length_sliceD] using Mem.read_write_zero M empty
    rw [show (0 : B256).toNat = 0 from rfl, read, B256.toNat_toB256_of_lt hsize]
    exact Bytes.sliceD_zero_length rfl
  have hnil := Exec.rawFrameDescendants_eq_nil_of_noExec child (usdcVersion_noExec
    (C := frame.inner.code) (by rw [hcC, hslotCode]; exact hI) child rfl
    (by rw [Frame.enter_run_benvStat enter, Xinst.step_spawn_benvStat hx]; exact hsg)
    (by
      have e : (initEvm (frame.inner.withBenv benv)).sta.data = nodeSevm.data := hdata
      simpa only [Blanc.Sevm.selector, Sevm.dataWord, e] using sel))
  simp only [Exec.rawFrameRoots, hnil, List.mem_singleton] at hD
  subst hD
  exact target

variable {sevm : Sevm} {b post : Devm} {exc : Exec 0 sevm b (.ok post)} {s : Curve3Pool.State}

/-- Who a `PoolAt` frame's children are. -/
theorem PoolAt.children (H : PoolAt exc s) :
    (∀ c ∈ Exec.childFrames exc, PoolChildSel (b.getStor sevm.currentTarget) c) ∨
      ∀ c ∈ Exec.childFrames exc, c.sevm.isStatic = true :=
  pool_children_of_world H.code H.fork H.cd H.stack H.mem H.gas H.static H.pc H.ck H.id H.tok H.coin H.world
    H.parties

/-- A child's roots from certified code with no frame below it. -/
private theorem roots_of_noExec {c : Exec.Frame} (hpc : c.pc = 0) (P : Adr) (hne : c.sevm.currentTarget ≠ P)
    (h : ∀ {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out),
      c.sevm = sevm → c.pre = pre → ChainNoExec run) :
    ∀ r ∈ Exec.rawFrameRoots c.run, r.sevm.isStatic = false → r.sevm.currentTarget ≠ P := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at hpc hne h
  subst hpc
  intro r hr _
  simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants_eq_nil_of_noExec run (h run rfl rfl),
    List.mem_singleton] at hr
  rw [hr]
  exact hne

/-- **No non-static frame at the pool below a `PoolAt` frame.** -/
theorem PoolAt.no_nested (H : PoolAt exc s) :
    ∀ f ∈ Exec.descendantFrames exc, f.sevm.isStatic = false → f.sevm.currentTarget ≠ sevm.currentTarget := by
  intro f hf
  rw [descendantFrames_eq_children] at hf
  obtain ⟨c, hc, hf⟩ := List.mem_flatMap.mp hf
  have hsg := H.fork.stateGas_none
  obtain ⟨pc0, stat, hsize, -, ccode⟩ := poolChild_facts H.code hsg exc c hc
  have hsgC : c.sevm.benvStat.rules.stateGas = none := by rw [stat]; exact hsg
  have hbalC : c.sevm.benvStat.rules.bal = none := by rw [stat]; exact H.fork.bal_none
  refine committed_apart c ?_ f hf
  cases hs : c.sevm.isStatic with
  | true =>
    intro r hr hrs
    obtain ⟨cpc, csevm, cpre, cout, crun, ccommitted⟩ := c
    have := Exec.static_rawFrameRoots_noStateGas crun hsgC hs (poolChild_codeAddress hsg _ hc hs) r hr
    rw [this.1] at hrs
    cases hrs
  | false =>
    rcases H.children with hall | hall
    · rcases hall c hc with ht | ⟨⟨i, hi, ht⟩, sel⟩
      · have htok : c.sevm.currentTarget = c3 := ht.trans H.parties.token
        have hcC : c.sevm.code = Curve3Crv.code := by
          rw [ccode c3 (by rw [H.world.tokCode]; exact c3crv_code_ne)
            (by rw [H.world.tokCode]; exact c3crv_not_delegation) htok, H.world.tokCode]
        obtain ⟨cpc, csevm, cpre, cout, crun, ccommitted⟩ := c
        dsimp only at pc0 hsgC htok hcC
        subst pc0
        have hd : ∀ D ∈ Exec.rawFrameDescendants crun, D.sevm.isStatic = true ∧ D.sevm.codeAddress ≠ none :=
          Exec.rawFrameDescendants_of_chain (root := ⟨0, csevm, cpre, cout, crun⟩)
            (fun chain step enter child =>
              staticOnly_child' Curve3Crv.cert_check Curve3Crv.cert_onlyStaticcall rfl hcC hsgC chain step enter child)
            crun (.refl _)
        intro r hr hrs
        simp only [Exec.rawFrameRoots, List.mem_cons] at hr
        rcases hr with rfl | hr
        · rw [htok]
          exact H.parties.tokNe.1
        · rw [(hd r hr).1] at hrs
          cases hrs
      · have ht' : c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot ⟨i, hi⟩)).toAdr := ht
        have hP : c.sevm.currentTarget ≠ sevm.currentTarget := by
          rw [ht']
          exact (H.parties.coinNe ⟨i, hi⟩).1
        have codeAt : ∀ {t : Adr} {C : ByteArray}, c.sevm.currentTarget = t → b.getCode t = C →
            C.toList ≠ [] → ¬ isValidDelegation C → c.sevm.code = C := by
          intro t C e hb hn hd
          rw [ccode t (by rw [hb]; exact hn) (by rw [hb]; exact hd) e, hb]
        rcases H.parties.coin ⟨i, hi⟩ with e | e | e
        · have hC := codeAt (ht'.trans e) H.world.daiCode (by decide +kernel) (by decide +kernel)
          exact roots_of_noExec pc0 _ hP fun run se _ =>
            dai_noExec run (se ▸ hC) (se ▸ hsgC) (se ▸ sel)
        · have hC := codeAt (ht'.trans e) H.world.usdcCode (by decide +kernel) (by decide +kernel)
          have hI : UsdcImplAt c.pre c.sevm.currentTarget := by
            rw [ht'.trans e]
            exact H.world.usdcImpl c hc (ht'.trans e) hs
          intro r hr _
          rw [usdc_roots c pc0 hC hsgC hbalC hsize hI sel r hr]
          exact hP
        · have hC := codeAt (ht'.trans e) H.world.usdtCode (by decide +kernel) (by decide +kernel)
          have hdep : Usdt.flag20 ((Devm.getStor c.pre c.sevm.currentTarget).get 10) = 0 := by
            rw [ht'.trans e]
            exact H.world.usdtLive c hc (ht'.trans e) hs
          exact roots_of_noExec pc0 _ hP fun run se pe =>
            usdt_noExec run (se ▸ hC) (se ▸ hsgC) (se ▸ hbalC)
              (by subst se; subst pe; exact hdep) (se ▸ sel)
    · rw [hall c hc] at hs
      cases hs

end Nested

/-! ## USDT's replies across `add_liquidity` -/

section Replies

variable {sevm : Sevm} {b post : Devm} {exc : Exec 0 sevm b (.ok post)} {s : Curve3Pool.State}

/-- **A child elsewhere keeps every cell of an address with code.** -/
theorem PoolAt.keeps_foreign (H : PoolAt exc s) {a : Adr} (ha : (b.getCode a).toList ≠ []) (key : B256) :
    ∀ c ∈ Exec.childFrames exc, c.sevm.currentTarget ≠ a → KeepsCell a key c := by
  intro c hc hne
  have hsg := H.fork.stateGas_none
  obtain ⟨-, stat, -, cpre, -⟩ := poolChild_facts H.code hsg exc c hc
  have hsgC : c.sevm.benvStat.rules.stateGas = none := by rw [stat]; exact hsg
  cases hs : c.sevm.isStatic with
  | true =>
    exact (frameKeeps_of_static c hsgC hs (poolChild_codeAddress hsg c hc hs) a).1
      (by rw [cpre a ha]; exact ha) key
  | false =>
    rcases H.children with hall | hall
    · rcases hall c hc with ht | ⟨⟨i, hi, ht⟩, sel⟩
      · have htok := ht.trans H.parties.token
        exact (H.world.tok_keeps H.code H.fork c hc htok a (fun e => hne (htok.trans e))).1 ha key
      · have ht' : c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot ⟨i, hi⟩)).toAdr := ht
        exact (H.world.coin_keeps H.parties H.code H.fork ⟨i, hi⟩ c hc ht' sel a
          (fun e => hne (ht'.trans e))).1 ha key
    · rw [hall c hc] at hs
      cases hs

/-- Two marked positions, in order, in a list marked only at `c0` and `c1`, are those two. -/
theorem marked_pair {α : Type} {P : α → Prop} {A : List α} {c0 c c1 cm x y : α} {n m : Nat}
    (hA : ∀ z ∈ A, ¬ P z) (hc : ¬ P c) (hcm : ¬ P cm)
    (hn : (A ++ [c0, c, c1, cm])[n]? = some x) (hm : (A ++ [c0, c, c1, cm])[m]? = some y)
    (px : P x) (py : P y) (lt : n < m) : x = c0 ∧ y = c1 := by
  have pos : ∀ {k : Nat} {z : α}, (A ++ [c0, c, c1, cm])[k]? = some z → P z →
      (k = A.length ∧ z = c0) ∨ (k = A.length + 2 ∧ z = c1) := by
    intro k z hk pz
    by_cases hlt : k < A.length
    · rw [List.getElem?_append_left hlt] at hk
      exact absurd pz (hA z (List.mem_of_getElem? hk))
    · rw [List.getElem?_append_right (by omega)] at hk
      obtain ⟨i, rfl⟩ : ∃ i, k = A.length + i := ⟨k - A.length, by omega⟩
      rw [Nat.add_sub_cancel_left] at hk
      match i, hk with
      | 0, hk =>
        exact .inl ⟨rfl, (Option.some.inj hk).symm⟩
      | 1, hk =>
        cases Option.some.inj hk
        exact absurd pz hc
      | 2, hk =>
        exact .inr ⟨rfl, (Option.some.inj hk).symm⟩
      | 3, hk =>
        cases Option.some.inj hk
        exact absurd pz hcm
      | i + 4, hk =>
        simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hk
  rcases pos hn px with ⟨e1, r1⟩ | ⟨e1, r1⟩ <;> rcases pos hm py with ⟨e2, r2⟩ | ⟨e2, r2⟩
  · omega
  · exact ⟨r1, r2⟩
  · omega
  · omega

theorem transferFrom_ne_balanceOf {a b c : Bytes} {x : Adr} :
    transferFromSel ++ a ++ b ++ c ≠ balanceOfData x := fun h =>
  absurd (List.cons.inj h).1 (by decide)

/-- A child at USDT runs USDT's code. -/
theorem PoolAt.usdt_good (H : PoolAt exc s) {c : Exec.Frame} (hc : c ∈ Exec.childFrames exc)
    (ht : c.sevm.currentTarget = usdt) : CodeFrame usdt HistFork Lift.Usdt.code c := by
  have hsg := H.fork.stateGas_none
  obtain ⟨pc0, stat, -, cpre, ccode⟩ := poolChild_facts H.code hsg exc c hc
  have hne : Lift.Usdt.code.toList ≠ [] := by decide +kernel
  have hC : c.sevm.code = Lift.Usdt.code := by
    rw [ccode usdt (by rw [H.world.usdtCode]; exact hne)
      (by rw [H.world.usdtCode]; decide +kernel) ht, H.world.usdtCode]
  exact ⟨pc0, hC, by rw [stat]; exact H.fork, by
      rw [cpre usdt (by rw [H.world.usdtCode]; exact hne), H.world.usdtCode]
      exact hne⟩

/-- **USDT's `balanceOf` child answers the entry it names.** -/
theorem PoolAt.usdt_answer (H : PoolAt exc s) {c : Exec.Frame} (hc : c ∈ Exec.childFrames exc)
    (wf : Mem.Wf c.pre.memory) (ht : c.sevm.currentTarget = usdt) {a : Adr}
    (hd : c.sevm.data = balanceOfData a) (live : Usdt.flag20 ((Devm.getStor c.pre usdt).get 10) = 0) :
    answerWord c.post.output = ((c.pre.getStor usdt).get (Usdt.balSlot a)).toNat := by
  have good := H.usdt_good hc ht
  have sel : Sevm.selector c.sevm = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
  have word4 : Sevm.dataWord c.sevm 4 = a.toB256 :=
    Curve3PoolSupply.dataWord_eq_of_append (pre := balanceOfSel) (rest := [])
      (by rw [hd, List.append_nil]; rfl) (by decide)
  have out := CurveCoins.Usdt.frame_balanceOf_answer good ht live wf sel
  rw [word4, toAdr_toB256] at out
  rw [answerWord, out, List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes]
  rfl

/-- **On `add_liquidity` with USDT in the amounts, the replies the model credits are the pool's USDT entry at the
frame's entry and at its end.** USDT's only state-changing child there sits between the two. -/
theorem PoolAt.add_replies (H : PoolAt exc s) (cm' : Execution.commits (.ok post) = true)
    (at' : sevm.currentTarget = pool)
    (hlen : 4 ≤ sevm.data.length) (hsel : Sevm.selector sevm = selAddLiquidity)
    (wf : ∀ c ∈ Exec.childFrames exc, Mem.Wf c.pre.memory)
    (flagKeep : ∀ c ∈ Exec.childFrames exc, c.sevm.currentTarget = usdt → c.sevm.isStatic = false →
      PoolCoinSel (Sevm.selector c.sevm) →
      (c.post.getStor usdt).get 10 = (c.pre.getStor usdt).get 10)
    {e : Env} (henv : EnvOf ⟨0, sevm, b, .ok post, exc⟩ e) (hpos : 0 < (argV3 sevm 0).get 2)
    {w w' : Nat} (hw : (e.coin 2).balPre = some w) (hw' : (e.coin 2).balPost = some w') :
    w = ((b.getStor usdt).get (Usdt.balSlot pool)).toNat ∧
      w' = ((post.getStor usdt).get (Usdt.balSlot pool)).toNat := by
  have hpne : (b.getCode sevm.currentTarget).toList ≠ [] := ByteArray.toList_ne_nil_of_ne_empty H.pc
  have hK := keepSel_of_world H.world H.parties H.code H.fork hpne
  have hx : XAt sevm post 0 (St b [] Mem.empty b.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self H.stack H.mem) (XAt.of_exec exc H.gas)
  have hcoinN : ∀ i, i < 3 → ¬ sevm.benvStat.rules.isPrecomp
      (Curve3Pool.coinAt (b.getStor sevm.currentTarget) i).toAdr := fun i hi => H.coin ⟨i, hi⟩
  obtain ⟨-, -, -, -, A, cT, L0, L1, L2, L', D0, D1, cr0, cr1, cr2, b', M, img, G', -, hL, hTt,
    -, -, -, -, -, -, hk0, hk1, hk2, -, -, -, -, -, -, hst', -, -, hcd', -, hR, hW, hA, hm, w900,
    h⟩ := xa_al_frontC checkedM H.code H.fork hlen H.cd hsel H.ck.abs H.tok hcoinN H.pc H.id hK hx
  have htokB : ∀ k : Nat, k < 3 → balancesBase + Nat.toB256 k ≠ tokenSlot := fun k hk => by
    rcases three_cases hk with rfl | rfl | rfl <;> decide
  obtain ⟨-, -, -, -, -, -, -, -, cm, rfl, -, -, -, -, hmt, -⟩ :=
    xa_al_backC checkedM H.code H.fork hR hW hA hm w900 hst'
      (by rw [Stor.get_set_ne _ lock_ne_token]; exact H.tok) htokB
      (by rw [hcd']; exact H.pc)
      (fun c hc ht => (hK.tok c (by rw [hL]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hc))
        (by rw [ht, Stor.get_set_ne _ lock_ne_token])).1) h
  have coinT : ∀ {i : Nat} (hi : i < 3) {c : Exec.Frame},
      c.sevm.currentTarget = (Curve3Pool.coinAt (alLocked (b.getStor sevm.currentTarget)) i).toAdr →
      c.sevm.currentTarget = adrOf (Curve3Pool.Creation.coinsN.get ⟨i, hi⟩) := fun {i} hi {c} ht => by
    rw [ht, Curve3Pool.coinAt, Stor.get_set_ne _ (coin_ne_lock hi)]
    exact H.coinIs ⟨i, hi⟩
  have amtNe : alAmt sevm 2 ≠ 0 := by
    intro zero
    have e2 : (argV3 sevm 0).get 2 = (alAmt sevm 2).toNat := by
      change (Sevm.dataWord sevm (32 * (0 + 2) + 4)).toNat = _
      rw [alAmt, show (32 * (0 + 2) + 4 : B256) = Bytes.toB256 [0x20] * Nat.toB256 2 + Bytes.toB256 [4] by decide]
    rw [e2, zero] at hpos
    exact absurd hpos (by decide)
  rcases hk2 with ⟨h0, -, -⟩ | ⟨-, hne, -⟩ | ⟨-, -, c0, c, c1, rfl, h0, hp, h1, -, -⟩
  · exact absurd h0 amtNe
  · exact absurd rfl hne
  have t0 : c0.sevm.currentTarget = usdt := (coinT (i := 2) (by decide) h0.target).trans coin2_eq
  have tc : c.sevm.currentTarget = usdt := (coinT (i := 2) (by decide) hp.target).trans coin2_eq
  have t1 : c1.sevm.currentTarget = usdt := (coinT (i := 2) (by decide) h1.target).trans coin2_eq
  have tcm : cm.sevm.currentTarget = c3 := by
    rw [hmt, Stor.get_set_ne _ lock_ne_token]
    exact H.parties.token
  have tcT : cT.sevm.currentTarget = c3 := by
    rw [hTt]
    exact H.parties.token
  have split : Exec.childFrames exc = (cT :: (L0 ++ L1)) ++ [c0, c, c1, cm] := by
    rw [hL]
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  have memA : ∀ z ∈ cT :: (L0 ++ L1), z ∈ Exec.childFrames exc := fun z hz => by
    rw [split]
    exact List.mem_append_left _ hz
  have mem0 : c0 ∈ Exec.childFrames exc := by rw [split]; simp only [List.mem_append, List.mem_cons, true_or, or_true]
  have memc : c ∈ Exec.childFrames exc := by rw [split]; simp only [List.mem_append, List.mem_cons, true_or, or_true]
  have mem1 : c1 ∈ Exec.childFrames exc := by rw [split]; simp only [List.mem_append, List.mem_cons, true_or, or_true]
  have memm : cm ∈ Exec.childFrames exc := by rw [split]; simp only [List.mem_append, List.mem_cons, true_or, or_true]
  have apartA : ∀ z ∈ cT :: (L0 ++ L1), z.sevm.currentTarget ≠ usdt := by
    intro z hz
    simp only [List.mem_cons, List.mem_append] at hz
    rcases hz with rfl | hz | hz
    · rw [tcT]
      decide
    · rw [(coinT (i := 0) (by decide) (hk0.target z hz)).trans coin0_eq]
      decide
    · rw [(coinT (i := 1) (by decide) (hk1.target z hz)).trans coin1_eq]
      decide
  have hne : sevm.currentTarget ≠ usdt := by rw [at']; decide
  have hsg := H.fork.stateGas_none
  have usdtNe : (b.getCode usdt).toList ≠ [] := by rw [H.world.usdtCode]; decide +kernel
  have keepsA : ∀ key, ∀ z ∈ cT :: (L0 ++ L1), KeepsCell usdt key z := fun key z hz =>
    H.keeps_foreign usdtNe key z (memA z hz) (apartA z hz)
  have staticKeep : ∀ key, ∀ z ∈ Exec.childFrames exc, z.sevm.isStatic = true → KeepsCell usdt key z := by
    intro key z hz hs
    obtain ⟨-, stat, -, cpre, -⟩ := poolChild_facts H.code hsg exc z hz
    exact (frameKeeps_of_static z (by rw [stat]; exact hsg) hs (poolChild_codeAddress hsg z hz hs) usdt).1
      (by rw [cpre usdt usdtNe]; exact usdtNe) key
  have upto := fun key => cell_upto (a := usdt) key exc cm' hsg hne usdtNe
  have keep0 : ∀ key, KeepsCell usdt key c0 := fun key => staticKeep key c0 mem0 h0.static
  have keep1 : ∀ key, KeepsCell usdt key c1 := fun key => staticKeep key c1 mem1 h1.static
  -- the flag
  have flag0 : ∀ z, (z = c0 → True) → (Devm.getStor c0.pre usdt).get 10 = (Devm.getStor b usdt).get 10 :=
    fun _ _ => ((upto 10) (cT :: (L0 ++ L1)) [c0, c, c1, cm] split (keepsA 10)).1 c0 _ rfl
  have cStatic : c.sevm.isStatic = false := hp.static.trans H.static
  have flagc : (Devm.getStor c.pre usdt).get 10 = (Devm.getStor b usdt).get 10 :=
    ((upto 10) ((cT :: (L0 ++ L1)) ++ [c0]) [c, c1, cm]
      (by rw [split]; simp only [List.append_assoc, List.singleton_append])
      (by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact keepsA 10 z hz
        · rw [List.mem_singleton] at hz
          subst hz
          exact keep0 10)).1 c _ rfl
  have liveC := H.world.usdtLive c memc tc cStatic
  have flagB : Usdt.flag20 ((Devm.getStor b usdt).get 10) = 0 := by rw [← flagc]; exact liveC
  have live0 : Usdt.flag20 ((Devm.getStor c0.pre usdt).get 10) = 0 := by rw [flag0 c0 (fun _ => trivial)]; exact flagB
  have selc : PoolCoinSel (Sevm.selector c.sevm) := poolCoinSel_transferFromData hp.data
  have xsKeep : ∀ key, KeepsCell usdt key c → ∀ z ∈ (cT :: (L0 ++ L1)) ++ [c0, c], KeepsCell usdt key z := by
    intro key kc z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact keepsA key z hz
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact keep0 key
      · exact kc
  have flag1 : (Devm.getStor c1.pre usdt).get 10 = (Devm.getStor b usdt).get 10 :=
    ((upto 10) ((cT :: (L0 ++ L1)) ++ [c0, c]) [c1, cm]
      (by rw [split]; simp only [List.append_assoc, List.cons_append, List.nil_append])
      (xsKeep 10 (flagKeep c memc tc cStatic selc))).1 c1 _ rfl
  have live1 : Usdt.flag20 ((Devm.getStor c1.pre usdt).get 10) = 0 := by rw [flag1]; exact flagB
  -- the replies
  have hdata0 : c0.sevm.data = balanceOfData pool := by rw [h0.data, at']
  have hdata1 : c1.sevm.data = balanceOfData pool := by rw [h1.data, at']
  have ans0 := H.usdt_answer mem0 (wf c0 mem0) t0 hdata0 live0
  have ans1 := H.usdt_answer mem1 (wf c1 mem1) t1 hdata1 live1
  have cellPre : ((c0.pre.getStor usdt).get (Usdt.balSlot pool)) = (b.getStor usdt).get (Usdt.balSlot pool) :=
    ((upto (Usdt.balSlot pool)) (cT :: (L0 ++ L1)) [c0, c, c1, cm] split (keepsA _)).1 c0 _ rfl
  have cellPost : (post.getStor usdt).get (Usdt.balSlot pool) = (c1.pre.getStor usdt).get (Usdt.balSlot pool) := by
    refine (cell_after (a := usdt) (Usdt.balSlot pool) exc cm' hsg hne usdtNe ((cT :: (L0 ++ L1)) ++ [c0, c]) c1 [cm]
      (by rw [split]; simp only [List.append_assoc, List.cons_append, List.nil_append]) ?_).trans
      (keep1 _)
    intro z hz
    rw [List.mem_singleton] at hz
    rw [hz]
    exact H.keeps_foreign usdtNe _ cm memm (by rw [tcm]; decide)
  have hcoinAdr : coinAdr ⟨0, sevm, b, .ok post, exc⟩ 2 = usdt := (H.coinIs 2).trans coin2_eq
  have framedT : framed ⟨0, sevm, b, .ok post, exc⟩ usdt = true := by
    have hnp : ¬ sevm.benvStat.rules.isPrecomp usdt := by
      have := H.coin 2
      rwa [H.coinIs 2, coin2_eq] at this
    simp only [framed, hnp, decide_false, Bool.not_false, Bool.true_or]
  rcases (henv.coin 2).balPost w' hw' with hf | ⟨w0, n, m, hw0, lt, ⟨x, hx1, hxt, hxd, -, hxa⟩, ⟨y, hy1, hyt, hyd, -, hya⟩⟩
  · rw [hcoinAdr, framedT] at hf
    cases hf
  have e0 : w0 = w := Option.some.inj (hw0.symm.trans hw)
  subst e0
  obtain ⟨rfl, rfl⟩ := marked_pair (P := fun z : Exec.Frame => z.sevm.currentTarget = usdt ∧
      z.sevm.data = balanceOfData pool) (A := cT :: (L0 ++ L1)) (c0 := c0) (c := c) (c1 := c1) (cm := cm)
    (fun z hz hP => apartA z hz hP.1)
    (fun hP => by
      have := hP.2
      rw [hp.data] at this
      exact transferFrom_ne_balanceOf this)
    (fun hP => by rw [tcm] at hP; exact absurd hP.1 (by decide))
    (by rw [← split]; exact hx1) (by rw [← split]; exact hy1)
    ⟨by rw [hxt, hcoinAdr], by rw [hxd, at']⟩ ⟨by rw [hyt, hcoinAdr], by rw [hyd, at']⟩ lt
  refine ⟨?_, ?_⟩
  · rw [← hxa, ans0, cellPre]
  · rw [← hya, ans1, cellPost]

end Replies

end Blanc.Composition.Curve3PoolPublic
