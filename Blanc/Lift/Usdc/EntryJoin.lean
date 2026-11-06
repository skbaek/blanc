import Blanc.Lift.Usdc.EntryLawV22
import Blanc.Lift.Usdc.EntryChainSettled
import Blanc.Lift.Usdc.InitializerKeeps

/-!
# USDC's entry locality: the chain, the laws and the initializers joined

`UsdcKeysFreshInit`: the one hash premise at USDC. `UsdcKeysFresh` over further listed keys: the initializers'
literal slots, the string windows, and the rows `initializeV2_1` and `initializeV2_2` compute from their calldata.
`RowsApart` and `MigrationsApart` follow from it, so neither is a premise any more.

`usdc_initializerKeeps`, `usdc_initializerRowsKeep`: the two fields, over the chain's frames.

`usdc_entryLocalAt`: `EntryLocalAt` with the observation `ChainObs T`, from certification at the settled frames, the
authority of the holder and the keys.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- The literal slots the initializers' certified stores name. -/
def lowKeys : List CoinKey := (List.range 256).map fun n => .raw (Nat.toB256 n)

/-- A string's payload window. A list for the statement: a reader checks it as the interval from `keccak s`, never
by enumerating it. -/
def windowKeys (s : B256) : List CoinKey :=
  (List.range (2 ^ 155)).map fun j => .raw (s.toBytes.keccak + Nat.toB256 j)

/-- The rows an initializer frame computes from its calldata: `initializeV2_1`'s recipient, and each account
`initializeV2_2` migrates, in the old blacklist and in the balances. -/
def frameInitKeys (sevm : Sevm) : List CoinKey :=
  (if Blanc.Sevm.selector sevm = 0x2fc81e09 then [.map 9 (Sevm.dataWord sevm 4).toAdr.toB256] else []) ++
    (if Blanc.Sevm.selector sevm = 0x430239b4 then
      (List.range (min (InitReachV2_2.arrLen sevm).toNat (2 ^ 32))).flatMap fun j =>
        [.map 3 (InitReachV2_2.acctAt sevm (InitReachV2_2.arrPtr sevm) j),
          .map 9 (InitReachV2_2.acctAt sevm (InitReachV2_2.arrPtr sevm) j &&& InitReachV2_2.addrMask)]
    else [])

/-- The keys beside the holder's and the sites'. -/
def usdcExtra (T : Adr) (frames : List Exec.Frame) : List CoinKey :=
  [.raw implSlot, .raw adminSlot] ++ ([.map 3 T.toB256, .map 9 T.toB256] ++ (lowKeys ++ (windowKeys 4 ++
    (windowKeys 5 ++ (windowKeys 7 ++ frames.flatMap fun F => frameInitKeys F.sevm)))))

/-- **Hash freshness at USDC, the initializers' keys included** (HASH-T). -/
def UsdcKeysFreshInit (T h : Adr) (frames : List Exec.Frame) : Prop :=
  CoinKeysFreshWith (usdcExtra T frames) usdcSites 9 10 h frames

section Keys

variable {T h : Adr} {frames : List Exec.Frame}

theorem UsdcKeysFreshInit.base (keys : UsdcKeysFreshInit T h frames) : UsdcKeysFresh h frames := by
  refine freshKeys_mono (fun k hk => ?_) keys
  rcases List.mem_append.mp hk with here | rest
  · exact List.mem_append_left _ (List.mem_append_left _ here)
  · exact List.mem_append_right _ rest

/-- Each group of the extra keys lies in the fresh list. -/
theorem extra_mem {k : CoinKey} (m : k ∈ usdcExtra T frames) :
    k ∈ coinKeysWith (usdcExtra T frames) usdcSites 9 10 h frames :=
  List.mem_append_left _ m

theorem window_mem {s : B256} {j : Nat} (hj : j < 2 ^ 155) :
    CoinKey.raw (s.toBytes.keccak + Nat.toB256 j) ∈ windowKeys s :=
  List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem recipient_mem {sevm : Sevm} (sel : Blanc.Sevm.selector sevm = 0x2fc81e09) :
    CoinKey.map 9 (Sevm.dataWord sevm 4).toAdr.toB256 ∈ frameInitKeys sevm := by
  unfold frameInitKeys
  rw [ite_eq_left sel]
  exact List.mem_append_left _ List.mem_cons_self

theorem migration_mem {sevm : Sevm} (sel : Blanc.Sevm.selector sevm = 0x430239b4) {j : Nat}
    (hj : j < min (InitReachV2_2.arrLen sevm).toNat (2 ^ 32)) :
    CoinKey.map 3 (InitReachV2_2.acctAt sevm (InitReachV2_2.arrPtr sevm) j) ∈ frameInitKeys sevm ∧
      CoinKey.map 9 (InitReachV2_2.acctAt sevm (InitReachV2_2.arrPtr sevm) j &&& InitReachV2_2.addrMask) ∈
        frameInitKeys sevm := by
  unfold frameInitKeys
  rw [ite_eq_left sel]
  constructor
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_cons_self⟩)
  · exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_cons_of_mem _ List.mem_cons_self⟩)

/-- Down the right spine of `usdcExtra` to the frames' keys. -/
theorem frame_extra_mem {F : Exec.Frame} (hF : F ∈ frames) {k : CoinKey} (m : k ∈ frameInitKeys F.sevm) :
    k ∈ usdcExtra T frames :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨F, hF, m⟩))))))

/-- **A tracked row is apart from an initializer's keys.** -/
theorem UsdcKeysFreshInit.rowApart (keys : UsdcKeysFreshInit T h frames) {F G : Exec.Frame} (hF : F ∈ frames)
    (hG : G ∈ frames) : RowApart T F.sevm (allowSlot h G.sevm.caller) := by
  have mr : CoinKey.row 10 h.toB256 G.sevm.caller.toB256 ∈
      coinKeysWith (usdcExtra T frames) usdcSites 9 10 h frames := frame_row_mem hG
  have raw : ∀ {x : B256}, CoinKey.raw x ∈ usdcExtra T frames → allowSlot h G.sevm.caller ≠ x :=
    fun m e => raw_ne_row keys (extra_mem m) mr e.symm
  have map : ∀ {b a : B256}, CoinKey.map b a ∈ usdcExtra T frames → allowSlot h G.sevm.caller ≠ mapSlot a b :=
    fun m e => map_ne_row keys (extra_mem m) mr e.symm
  have window4 : StrWindow 4 (allowSlot h G.sevm.caller) := fun j hj => raw
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (window_mem hj)))))
  have window5 : StrWindow 5 (allowSlot h G.sevm.caller) := fun j hj => raw
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (window_mem hj))))))
  have window7 : StrWindow 7 (allowSlot h G.sevm.caller) := fun j hj => raw
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ (window_mem hj)))))))
  refine ⟨?_, window4, window5, window7, raw (List.mem_append_left _ List.mem_cons_self),
    raw (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    map (List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self)),
    map (List.mem_append_right _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))),
    fun sel => map (frame_extra_mem hF (recipient_mem sel)),
    fun sel j hj => ⟨map (frame_extra_mem hF (migration_mem sel hj).1),
      map (frame_extra_mem hF (migration_mem sel hj).2)⟩⟩
  refine Nat.le_of_not_lt fun small => ?_
  have bound : (allowSlot h G.sevm.caller).toNat < 2 ^ 256 := by omega
  refine raw (x := Nat.toB256 (allowSlot h G.sevm.caller).toNat)
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
      (List.mem_map.mpr ⟨_, List.mem_range.mpr small, rfl⟩))))
    (B256.toNat_inj _ _ ?_)
  rw [B256.toNat_toB256_of_lt bound]

/-- The holder's entry is apart from each account `initializeV2_2` migrates into the old blacklist. -/
theorem UsdcKeysFreshInit.migrationApart (keys : UsdcKeysFreshInit T h frames) {F : Exec.Frame} (hF : F ∈ frames)
    (sel : Blanc.Sevm.selector F.sevm = 0x430239b4) : MigrationApart (balSlot h) F.sevm := fun j hj e => by
  have same := keys.2 _ (held_mem (extra := usdcExtra T frames) (sites := usdcSites) (allowBase := 10)
    (frames := frames) (balBase := 9) (h := h)) _ (extra_mem (frame_extra_mem hF (migration_mem sel hj).1)) e
  injection same with base
  exact absurd base (by decide)

end Keys

section Trace

variable {T h : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
  (trace : MidHistoryTraceIn HistFork cfg start future)
  (capabilities : BodyStageCapabilities HistFork)

/-- The chain's frames of a history. -/
noncomputable abbrev usdcFrames (T : Adr) (settled : List Exec.Frame) : List Exec.Frame := coinFrames T (ChainObs T) settled

theorem init_ne_rescue {σ : B256} (sel : σ ∈ usdcInitializers) : σ ≠ rescueSelector := by
  rintro rfl
  exact absurd sel (by decide)

theorem init_frame_mem {settled : List Exec.Frame} {F : Exec.Frame} (member : F ∈ settled)
    (target : F.sevm.currentTarget = T) (nonstatic : F.sevm.isStatic = false) (obs : EntryObs T F)
    (sel : Blanc.Sevm.selector F.sevm ∈ usdcInitializers) : F ∈ usdcFrames T settled :=
  mem_coinFrames.mpr ⟨member, target, nonstatic, obs, init_ne_rescue sel⟩

include capabilities in
/-- **`T` has code at the entry of every settled frame**, the chain's fact for frames off it as well. -/
theorem usdc_settled_hasCode (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T trace.settledFrames) :
    ∀ F ∈ trace.settledFrames, (F.pre.getCode T).toList ≠ [] := by
  intro F member
  rw [trace.settledFrames_eq] at member
  obtain ⟨R, here, frame⟩ := List.mem_flatMap.mp member
  have ready := Blanc.Lift.MidHistoryTraceIn.rootsReady trace capabilities (sem := entrySem) (C := Proxy.code) rfl
    installed proxy_toList_ne_nil proxy_not_delegation
    (usdc_outputNotDeleted trace capabilities installed certified).1 R here
  have proxy : R.pre.getCode T = Proxy.code := bytes_eq_of_image ready.2.1.1
  have retained := (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run (Exec.Frame.rootDeriv F)).mpr
    ⟨F, frame, .refl _⟩
  have code := Exec.rawNodes_getCode R.run proxy proxy_toList_ne_nil _
    ((Exec.retainedNodes_sublist_rawNodes R.run).subset retained)
  change F.pre.getCode T = Proxy.code at code
  rw [code]
  exact proxy_toList_ne_nil

include capabilities in
/-- **`InitializerKeeps` from certification and the keys.** -/
theorem usdc_initializerKeeps (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T trace.settledFrames) (a : EntryApart T (balSlot h))
    (keys : UsdcKeysFreshInit T h (usdcFrames T trace.settledFrames)) :
    InitializerKeeps T h trace.settledFrames :=
  initializerKeeps trace capabilities a
    (fun F member _ _ => usdc_settled_hasCode trace capabilities installed certified F member)
    (fun F member target obs => (certified F member target obs.1 obs.2).1)
    fun F member target nonstatic obs sel => keys.migrationApart
      (init_frame_mem member target nonstatic obs (by rw [sel]; decide)) sel

include capabilities in
/-- **`InitializerRowsKeep` from certification and the keys.** U3i's theorem at `Tracked := CallerOf frames`, against
U3l's definition. -/
theorem usdc_initializerRowsKeep (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T trace.settledFrames)
    (keys : UsdcKeysFreshInit T h (usdcFrames T trace.settledFrames)) :
    InitializerRowsKeep T h (usdcFrames T trace.settledFrames) trace.settledFrames :=
  initializerRowsKeep trace capabilities
    (fun F member _ _ => usdc_settled_hasCode trace capabilities installed certified F member)
    (fun F member target obs => (certified F member target obs.1 obs.2).1)
    fun F member target nonstatic obs sel g tracked => by
      obtain ⟨G, hG, rfl⟩ := tracked
      exact keys.rowApart (init_frame_mem member target nonstatic obs sel) hG

/-- An initializer has no `ownCredit`. -/
theorem init_credit_zero {e : Sevm} (sel : Blanc.Sevm.selector e ∈ usdcInitializers) : ownCredit h e = 0 :=
  ite_eq_right fun c => by
    have : (0x23b872dd : B256) ∈ usdcInitializers := c.2.1 ▸ sel
    exact absurd this (by decide)

include capabilities in
/-- **USDC's entry locality**: over a mid history from the proxy, certified at its settled frames, with the holder's
authority and the keys. The chain's frames are the entry frames off `rescueERC20`. Each frame's law is its version's,
or an initializer's fields, and the rows run along the chain. -/
theorem usdc_entryLocalAt (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T trace.settledFrames) (a : EntryApart T (balSlot h))
    (keys : UsdcKeysFreshInit T h (usdcFrames T trace.settledFrames))
    (authority : PoolAuthorityEmpty SignedAs allowSlot CurveCoins.PoolCoinSel h
      (ledgerView (wordsAt T start.state)) (usdcFrames T trace.settledFrames)) :
    EntryLocalAt T ledgerView (ChainObs T) (EntryGood T) (heldAt T h) (ownDebit h) (ownCredit h)
      (ledgerView (wordsAt T start.state)) (ledgerView (wordsAt T future.state)) trace.settledFrames := by
  have viewChain := usdc_viewChain_certified trace capabilities installed certified
  have keepInit := usdc_initializerKeeps trace capabilities installed certified a keys
  have keepRows := usdc_initializerRowsKeep trace capabilities installed certified keys
  have law : ∀ F ∈ usdcFrames T trace.settledFrames, EntryGood T F →
      RowsView h (usdcFrames T trace.settledFrames) (ledgerView (wordsAt T F.pre.state)) →
      RowsView h (usdcFrames T trace.settledFrames) (ledgerView (wordsAt T F.post.state)) ∧
        heldAt T h F (ledgerView (wordsAt T F.pre.state)) + ownCredit h F.sevm ≤
          heldAt T h F (ledgerView (wordsAt T F.post.state)) + ownDebit h F.sevm := by
    intro F hF good rows
    obtain ⟨member, target, nonstatic, obs, notRescue⟩ := mem_coinFrames.mp hF
    obtain ⟨pc, code, fork, hasCode⟩ := good
    by_cases init : Blanc.Sevm.selector F.sevm ∈ usdcInitializers
    · refine ⟨keepRows F member target nonstatic obs init rows, ?_⟩
      have := keepInit F member target nonstatic obs init
      rw [init_credit_zero init]
      omega
    exact usdc_entry_law keys.base hF pc code fork target hasCode obs.2 (certified F member target code obs.2)
      (settled_data_bound trace capabilities F member) notRescue init (authority.ownCalls F hF)
      (authority.noSignature F hF) rows
  refine ⟨viewChain.1, viewChain.2, fun F hF => ?_⟩
  have rows := viewChain.1.inv_all (I := RowsView h (usdcFrames T trace.settledFrames))
    (fun G hG good r => (law G hG good r).1) authority.rowsAtCut F hF
  exact (law F hF (viewChain.1.good F hF) rows).2

end Trace

end Blanc.Lift.Usdc
