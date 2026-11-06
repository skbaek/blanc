import Blanc.Lift.Usdc.EntryChain
import Blanc.Lift.Usdc.InitRowsHistory
import Blanc.Lift.Usdc.V21InitializerReach
import Blanc.Lift.Usdc.V22InitializerReach

/-!
# USDC's initializers keep a holder's entry

`initializerKeeps` discharges `InitializerKeeps` over a mid history. No flag of the contract is read:
an initializer's stores are classified by the prefix walks, whatever the frame's outcome and whatever
`initialized` and `_initializedVersion` hold, and a holder's entry lies apart from all of them.

* `StrApart`, `EntryApart`: closed arithmetic on the entry's word. A string's payload stays within
  `2 ^ 251` words of its hash whatever its stored header says, so an entry outside those intervals
  misses every payload and clearing store. `entryApart_pool` computes this for the pool's entry;
* `init_write_ne`: `initialize` and `initializeV2`, all three versions;
* `init2_write_ne`: `initializeV2_1` and `initializeV2_2`, given `recipient` and `migration`;
* `init_children`: below a proxy frame on these selectors runs one level of implementation frames;
* `frame_init_keep`: the committed frame keeps the entry's word.

Two calldata facts stay as premises, `RecipientsApart` and `MigrationsApart`: the recipient's credit and
the listed account's blacklist bit are the stores that do land on a holder named in the calldata. Each
is a reader's check against the upgrade's calldata; the walks that would give their value bounds (a
credit never falls, the bits survive `_blacklist`) are not written.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- **A word apart from a string's whole interval**: the string at `s` occupies words from `keccak s`,
and no header's length reaches past `2 ^ 251` words. -/
def StrApart (s k : B256) : Prop :=
  s.toBytes.keccak.toNat + 2 ^ 251 < 2 ^ 256 ∧
    (k.toNat < s.toBytes.keccak.toNat ∨ s.toBytes.keccak.toNat + 2 ^ 251 ≤ k.toNat)

theorem StrApart.not_payload {s k : B256} (h : StrApart s k) {j : Nat} (hj : j < 2 ^ 251) :
    k ≠ s.toBytes.keccak + j.toB256 := by
  intro e
  have small : j < 2 ^ 256 := by omega
  have := congrArg B256.toNat e
  simp only [B256.toNat_add, B256.toNat_toB256_of_lt small, Nat.lo] at this
  obtain ⟨room, far⟩ := h
  omega

theorem StrApart.not_clear {s k : B256} (h : StrApart s k) {n : Nat} (hn : n < 2 ^ 251) :
    ¬ StrStore.ClearRange s n k := by
  rintro ⟨old, i, hi, lo, hi'⟩
  have small : i < 2 ^ 256 := by omega
  unfold StrStore.oldEnd at hi'
  generalize (Bytes.toB256 [31] + (Bytes.toB256 [1, 0] * ((Bytes.toB256 [1] &&& old) =? 0) -
      Bytes.toB256 [1] &&& old) / Bytes.toB256 [2]) = w at hi'
  have div : (w / Bytes.toB256 [32]).toNat < 2 ^ 251 := by
    rw [B256.toNat_div (by decide), show (Bytes.toB256 [32]).toNat = 32 from rfl]
    have := B256.toNat_lt w
    omega
  simp only [B256.toNat_add, B256.toNat_toB256_of_lt small, Nat.lo] at lo hi'
  obtain ⟨room, far⟩ := h
  omega

/-- **What an entry `k` of a holder lies apart from at USDC `T`**: closed facts of two words. -/
structure EntryApart (T : Adr) (k : B256) : Prop where
  /-- Above every literal slot. -/
  low : 256 ≤ k.toNat
  name : StrApart 4 k
  symbol : StrApart 5 k
  currency : StrApart 7 k
  /-- The proxy's two slots. -/
  impl : k ≠ implSlot
  admin : k ≠ adminSlot
  /-- `T`'s own rows in the old blacklist and in the balances. -/
  self3 : k ≠ mapSlot T.toB256 3
  self9 : k ≠ mapSlot T.toB256 9

theorem payload_bound {L : Nat} (h : L ≤ 2 ^ 160) : (L + 31) / 32 < 2 ^ 251 := by omega

theorem not_low {T : Adr} {k x : B256} (a : EntryApart T k) (hx : x.toNat < 256) : k ≠ x := by
  rintro rfl
  have := a.low
  omega

/-- A store of `initialize`'s range misses the entry. -/
theorem InitRange.key_ne {T : Adr} {k : B256} (a : EntryApart T k) {L1 L2 L3 : Nat}
    (h1 : L1 ≤ 2 ^ 160) (h2 : L2 ≤ 2 ^ 160) (h3 : L3 ≤ 2 ^ 160) {C : Conf}
    (range : Init06.InitRange L1 L2 L3 C) {key v : B256} {S : List B256}
    (stack : C.d.stack = key :: v :: S) : key ≠ k := by
  rintro rfl
  rcases range _ _ _ stack with keys | ⟨-, c | c | c⟩
  · unfold Init06.KeysInit at keys
    rcases keys with fixed | ⟨j, hj, e⟩ | ⟨j, hj, e⟩ | ⟨j, hj, e⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
      rcases fixed with e | e | e | e | e | e | e | e <;> exact not_low a (by decide) e
    · exact a.name.not_payload (hj.trans (payload_bound h1)) e
    · exact a.symbol.not_payload (hj.trans (payload_bound h2)) e
    · exact a.currency.not_payload (hj.trans (payload_bound h3)) e
  · exact a.name.not_clear (payload_bound h1) c
  · exact a.symbol.not_clear (payload_bound h2) c
  · exact a.currency.not_clear (payload_bound h3) c

/-- A store of `initializeV2`'s range misses the entry. -/
theorem InitRangeV2.key_ne {T : Adr} {k : B256} (a : EntryApart T k) {sevm : Sevm} {C : Conf}
    (range : InitRangeV2 sevm C) {key v : B256} {S : List B256}
    (stack : C.d.stack = key :: v :: S) : key ≠ k := by
  have bound : min (CdStrWrap.cdLen sevm) (2 ^ 32) ≤ 2 ^ 160 :=
    (Nat.min_le_right _ _).trans (by decide)
  rintro rfl
  rcases range _ _ _ stack with keys | ⟨-, c⟩
  · rcases keys with e | e | e | ⟨j, hj, e⟩
    · exact not_low a (by decide) e
    · exact not_low a (by decide) e
    · exact not_low a (by decide) e
    · exact a.name.not_payload (hj.trans (payload_bound bound)) e
  · exact a.name.not_clear (payload_bound bound) c

/-- The caps of `InitRange06`. -/
theorem cap160 (n : Nat) : min n (2 ^ 160) ≤ 2 ^ 160 := Nat.min_le_right _ _

/-- **A store under `initialize` or `initializeV2` misses the entry**, at a node below a frame of any
outcome running a certified version from pc `0`. No flag is read. -/
theorem init_write_ne {T : Adr} {k : B256} (a : EntryApart T k) {G N : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (fresh : Exec.FreshEntry G.sevm G.devm)
    (gas : G.devm.gasMeasure < 2 ^ 256) (version : CurveCoins.UsdcVersion G.sevm.code)
    (sel : Blanc.Sevm.selector G.sevm = 0x3357162b ∨ Blanc.Sevm.selector G.sevm = 0xd608ea64)
    (chain : Exec.Deriv.ParentPrefix G N) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? N = some w) : w.key ≠ k := by
  obtain ⟨hat, rest, hstack⟩ := successfulSstore?_decoded found
  obtain ⟨stack, memory⟩ := fresh
  have erase : ∀ {s d n d'}, StepIn G s d n d' → Ninst.Run s d n d' := fun h => StepIn.toRun h
  have eraseP : ∀ {s d n d'}, FreePtr.PotStep (StepIn G) s d n d' → Ninst.Run s d n d' :=
    fun h => StepIn.toRun h.1
  have use06 : ∀ {C : Conf}, Init06.InitRange06 G.sevm C → C.d = N.devm → w.key ≠ k := fun r e =>
    InitRange.key_ne a (cap160 _) (cap160 _) (cap160 _) r (e ▸ hstack)
  have useV2 : ∀ {C : Conf}, InitRangeV2 G.sevm C → C.d = N.devm → w.key ≠ k := fun r e =>
    InitRangeV2.key_ne a r (e ▸ hstack)
  have word := selWord_eq_selector G.sevm
  rcases version with code | code | code
  · obtain ⟨C, run, hT, e⟩ := Reach.sstoreNode_pot ImplV2.cert_check hpc code hsg stack memory
      gas chain hat
    rcases sel with hs | hs
    · exact use06 (Init06.init_reach_V2_range erase (word.trans hs) run hT) e
    · exact useV2 (InitReachV2.initV2_reach_range eraseP (word.trans hs) run hT) e
  · obtain ⟨C, run, hT, e⟩ := Reach.sstoreNode_pot ImplV2_1.cert_check hpc code hsg stack memory
      gas chain hat
    rcases sel with hs | hs
    · exact use06 (Init06.init_reach_V2_1_range erase (word.trans hs) run hT) e
    · exact useV2 (InitReachV2_1.initV2_reach_range eraseP (word.trans hs) run hT) e
  · obtain ⟨C, run, hT, e⟩ := Reach.sstoreNode_pot Impl.cert_check hpc code hsg stack memory
      gas chain hat
    rcases sel with hs | hs
    · exact use06 (Init06.init_reach_V2_2_range erase (word.trans hs) run hT) e
    · exact useV2 (InitReachV2_2.initV2_reach_range eraseP (word.trans hs) run hT) e

/-! ## `initializeV2_1` and `initializeV2_2` -/

/-- Every site of FiatTokenV2 stands under one of these selectors: no `initializeV2_1`,
no `initializeV2_2`. -/
def v2SiteSels : List B256 := [861345323, 4076725131, 1061922874, 1431022396, 2220280665, 3590908516,
  2906177314, 2854281700, 1086394137, 1117154408, 716570693, 1510251120, 2953339029, 3258388623,
  3780513747, 3824031246, 599290589, 3573918927, 445207142, 4193856484, 2835717307, 814919637,
  1313134934, 961581905, 157198259, 2757214935]

/-- Every site of FiatTokenV2_1 stands under one of these selectors: no `initializeV2_2`. -/
def v2_1SiteSels : List B256 := [861345323, 4076725131, 1061922874, 1431022396, 2220280665, 801644041,
  3590908516, 2906177314, 2854281700, 1086394137, 1117154408, 716570693, 1510251120, 3824031246,
  4015374022, 599290589, 3573918927, 445207142, 4193856484, 2835717307, 814919637, 1313134934,
  961581905, 157198259, 2757214935]

theorem v2_sites : (WriteSite.wsRoot ImplV2Ws.implWsAnn).all (WriteSite.hasSel selV2T v2SiteSels) = true := by
  decide +kernel

theorem v2_1_sites :
    (WriteSite.wsRoot ImplV2_1Ws.implWsAnn).all (WriteSite.hasSel selV2T v2_1SiteSels) = true := by
  decide +kernel

/-- The selector a site's guard reads. -/
theorem selV2T_root (sevm : Sevm) :
    selV2T.eval (WriteSite.Env.root sevm) = Blanc.Sevm.selector sevm :=
  (selV2T_root_selWord sevm).trans (selWord_eq_selector sevm)

/-- **What the migration names**: the rows `initializeV2_2` writes for its account list. A collision
of `keccak(account ‖ 3)` is of the hash class; `account = holder` at base `9` is what the migration's
calldata is read for. -/
def MigrationApart (k : B256) (sevm : Sevm) : Prop :=
  ∀ j < min (InitReachV2_2.arrLen sevm).toNat (2 ^ 32),
    k ≠ mapSlot (InitReachV2_2.acctAt sevm (InitReachV2_2.arrPtr sevm) j) 3 ∧
      k ≠ mapSlot (InitReachV2_2.acctAt sevm (InitReachV2_2.arrPtr sevm) j &&& InitReachV2_2.addrMask) 9

theorem self_mask (T : Adr) : T.toB256 &&& InitReachV2_2.addrMask = T.toB256 := by
  rw [B256.and_comm]
  exact ff20_and_adr T

/-- A store of `initializeV2_2`'s range misses the entry. -/
theorem InitRange22.key_ne {T : Adr} {k : B256} (a : EntryApart T k) {sevm : Sevm}
    (target : sevm.currentTarget = T) (apart : MigrationApart k sevm) {C : Conf}
    (range : InitReachV2_2.InitRange22 sevm C) {key v : B256} {S : List B256}
    (stack : C.d.stack = key :: v :: S) : key ≠ k := by
  have bound : min (InitReachV2_2.strLen sevm) (2 ^ 32) ≤ 2 ^ 160 :=
    (Nat.min_le_right _ _).trans (by decide)
  rintro rfl
  rcases range _ _ _ stack with keys | ⟨-, c⟩
  · rcases keys with e | ⟨j, hj, e⟩ | ⟨j, hj, e | e⟩ | e | e | e
    · exact not_low a (by decide) e
    · exact a.symbol.not_payload (hj.trans (payload_bound bound)) e
    · exact (apart j hj).1 e
    · exact (apart j hj).2 e
    · rw [target, self_mask] at e
      exact a.self9 e
    · rw [target] at e
      exact a.self3 e
    · exact not_low a (by decide) e
  · exact a.symbol.not_clear (payload_bound bound) c

/-- **A store under `initializeV2_1` or `initializeV2_2` misses the entry**, given the recipient and
the migration's accounts are apart from it. -/
theorem init2_write_ne {T : Adr} {k : B256} (a : EntryApart T k) {G N : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (fresh : Exec.FreshEntry G.sevm G.devm)
    (gas : G.devm.gasMeasure < 2 ^ 256) (version : CurveCoins.UsdcVersion G.sevm.code)
    (target : G.sevm.currentTarget = T)
    (sel : Blanc.Sevm.selector G.sevm = 0x2fc81e09 ∨ Blanc.Sevm.selector G.sevm = 0x430239b4)
    (recipient : Blanc.Sevm.selector G.sevm = 0x2fc81e09 →
      k ≠ mapSlot (Sevm.dataWord G.sevm 4).toAdr.toB256 9)
    (migration : Blanc.Sevm.selector G.sevm = 0x430239b4 → MigrationApart k G.sevm)
    (chain : Exec.Deriv.ParentPrefix G N) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? N = some w) : w.key ≠ k := by
  have r18 : w.key = 18 → w.key ≠ k := fun e c => not_low a (x := 18) (by decide) (c.symm.trans e)
  have self9 : w.key = mapSlot G.sevm.currentTarget.toB256 9 → w.key ≠ k := fun e c =>
    a.self9 (by rw [← target]; exact c.symm.trans e)
  have self3 : w.key = mapSlot G.sevm.currentTarget.toB256 3 → w.key ≠ k := fun e c =>
    a.self3 (by rw [← target]; exact c.symm.trans e)
  rcases version with code | code | code
  · obtain ⟨site, inRoot, -, guards, -⟩ := WriteSite.successfulSstore_site ImplV2.cert_check
      implV2_wsCert hpc code hsg chain found
    have mem := WriteSite.hasSel_sound (List.all_eq_true.mp v2_sites site inRoot) rfl guards
    rw [selV2T_root] at mem
    rcases sel with hs | hs <;> rw [hs] at mem <;> exact absurd mem (by decide)
  · rcases sel with hs | hs
    · rcases V21InitializerReach.successfulSstore_all_source hpc code hsg chain hs found with
        e | ⟨-, -, e, -⟩ | ⟨-, e, -⟩ | ⟨-, e, -⟩
      · exact r18 e
      · exact self9 e
      · exact fun c => recipient hs (c.symm.trans e)
      · exact self3 e
    · obtain ⟨site, inRoot, -, guards, -⟩ := WriteSite.successfulSstore_site ImplV2_1.cert_check
        implV2_1_wsCert hpc code hsg chain found
      have mem := WriteSite.hasSel_sound (List.all_eq_true.mp v2_1_sites site inRoot) rfl guards
      rw [selV2T_root, hs] at mem
      exact absurd mem (by decide)
  · rcases sel with hs | hs
    · rcases V22InitializerReach.successfulSstore_source hpc code hsg chain hs found with
        e | ⟨-, e, -⟩ | ⟨-, e, -⟩ | ⟨-, e, -⟩
      · exact r18 e
      · exact self9 e
      · exact fun c => recipient hs (c.symm.trans e)
      · exact self9 e
    · obtain ⟨hat, rest, hstack⟩ := successfulSstore?_decoded found
      obtain ⟨stack, memory⟩ := fresh
      have eraseP : ∀ {s d n d'}, FreePtr.PotStep (StepIn G) s d n d' → Ninst.Run s d n d' :=
        fun h => StepIn.toRun h.1
      obtain ⟨C, run, hT, e⟩ := Reach.sstoreNode_pot Impl.cert_check hpc code hsg stack memory
        gas chain hat
      exact InitRange22.key_ne a target (migration hs)
        (InitReachV2_2.initV2_2_reach_range eraseP ((selWord_eq_selector _).trans hs) run hT)
        (e ▸ hstack)

/-! ## No frame below an initializer -/

/-- The four initializers' selectors. -/
theorem mem_inits {σ : B256} : σ ∈ usdcInitializers ↔
    σ = 0x3357162b ∨ σ = 0xd608ea64 ∨ σ = 0x2fc81e09 ∨ σ = 0x430239b4 := by
  simp only [usdcInitializers, List.mem_cons, List.not_mem_nil, or_false]

/-- A version's initializer enters no frame. -/
theorem init_noExec {C : ByteArray} (hC : CurveCoins.UsdcVersion C) {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec 0 sevm pre out) (hcode : sevm.code = C)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : Blanc.Sevm.selector sevm ∈ usdcInitializers) : CurveCoins.ChainNoExec run := by
  rw [mem_inits] at sel
  rcases hC with rfl | rfl | rfl
  · refine noExec_of_reach ImplV2.cert_check rfl rfl run hcode hsg fun T h t => ?_
    change Reach _ _ _ ⟨_, ImplV2.t_0000_c0, []⟩ T at h
    repeat rstepN h t
    rbranchE h t CurveCoins.v2Free_execFree
    repeat rstepN h t
    rbranchE h t CurveCoins.v2Free_execFree
    iterate 4 rstepN h t
    rw [shr_selector_word] at h
    rcases sel with s | s | s | s <;> rw [s] at h <;> repeat rdispE h t CurveCoins.v2Free_execFree
  · refine noExec_of_reach ImplV2_1.cert_check rfl rfl run hcode hsg fun T h t => ?_
    change Reach _ _ _ ⟨_, ImplV2_1.t_0000_c0, []⟩ T at h
    repeat rstepN h t
    rbranchE h t CurveCoins.v2_1Free_execFree
    repeat rstepN h t
    rbranchE h t CurveCoins.v2_1Free_execFree
    iterate 4 rstepN h t
    rw [shr_selector_word] at h
    rcases sel with s | s | s | s <;> rw [s] at h <;> repeat rdispE h t CurveCoins.v2_1Free_execFree
  · refine noExec_of_reach Impl.cert_check rfl rfl run hcode hsg fun T h t => ?_
    change Reach _ _ _ ⟨_, Impl.t_0000_c0, []⟩ T at h
    repeat rstepN h t
    rbranchE h t CurveCoins.v22Free_execFree
    repeat rstepN h t
    rbranchE h t CurveCoins.v22Free_execFree
    iterate 4 rstepN h t
    rw [shr_selector_word] at h
    rcases sel with s | s | s | s <;> rw [s] at h <;> repeat rdispE h t CurveCoins.v22Free_execFree

/-- What a raw frame below a proxy frame on an initializer is. -/
structure InitChild (T : Adr) (data : Bytes) (D : Exec.Deriv) : Prop where
  pc : D.pc = 0
  version : CurveCoins.UsdcVersion D.sevm.code
  target : D.sevm.currentTarget = T
  sameData : D.sevm.data = data
  stateGas : D.sevm.benvStat.rules.stateGas = none

/-- **Below a proxy frame on an initializer there are only frames of the implementation**, none of them
with a frame below it. Whoever the caller is: an admin caller reaches an external instruction only on
`upgradeToAndCall`. -/
theorem init_children {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Proxy.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) (hsize : sevm.data.length < 2 ^ 256)
    (hI : CurveCoins.UsdcImplAt pre sevm.currentTarget)
    (sel : Blanc.Sevm.selector sevm ∈ usdcInitializers) :
    ∀ D ∈ Exec.rawFrameDescendants run, InitChild sevm.currentTarget sevm.data D := by
  refine Exec.rawFrameDescendants_of_chain (root := ⟨0, sevm, pre, out, run⟩) ?_ run (.refl _)
  intro nodePc nextPc nodeSevm nodePre nodeOut raw frame rsm cevm nrun chain step enter child D hD
  obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
  have env : nodeSevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  subst env
  obtain ⟨f, K, ⟨rfl, delegated⟩ | ⟨rfl, -, hw⟩⟩ := Proxy.proxy_nodeH run hcode hsg bal chain hat
  swap
  · rw [dispatchWord_eq_selector] at hw
    rw [hw] at sel
    exact absurd sel (by decide)
  obtain ⟨-, b', gas, S, M, G, tail, hstate, -, input⟩ := delegated
  change nodePre = _ at input
  subst input
  have hslotCode : (St b' (gas :: pre.getStorVal nodeSevm.currentTarget implSlot :: 0 ::
      nodeSevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (nodeSevm.data.sliceD 0 nodeSevm.data.length.toB256.toNat 0)) G).getCode
        (pre.getStorVal nodeSevm.currentTarget implSlot).toAdr =
      pre.getCode (pre.getStorVal nodeSevm.currentTarget implSlot).toAdr := by
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
  have childSg : (initEvm (frame.inner.withBenv benv)).sta.benvStat.rules.stateGas = none := by
    rw [Frame.enter_run_benvStat enter, Xinst.step_spawn_benvStat hx]
    exact hsg
  have hnil := Exec.rawFrameDescendants_eq_nil_of_noExec child (init_noExec
    (C := frame.inner.code) (by rw [hcC, hslotCode]; exact hI) child rfl childSg
    (by
      have e : (initEvm (frame.inner.withBenv benv)).sta.data = nodeSevm.data := hdata
      simpa only [Blanc.Sevm.selector, Sevm.dataWord, e] using sel))
  simp only [Exec.rawFrameRoots, hnil, List.mem_singleton] at hD
  subst hD
  exact ⟨rfl, by show CurveCoins.UsdcVersion frame.inner.code; rw [hcC, hslotCode]; exact hI, target, hdata, childSg⟩

/-- Selector and migration read only the calldata. -/
theorem MigrationApart.of_data {k : B256} {s s' : Sevm} (e : s'.data = s.data)
    (h : MigrationApart k s) : MigrationApart k s' := by
  simpa only [MigrationApart, InitReachV2_2.arrLen, InitReachV2_2.arrPtr, InitReachV2_2.acctAt,
    Sevm.dataWord, e] using h

/-- **A committed proxy frame on an initializer keeps the entry**, word for word. -/
theorem frame_init_keep {T : Adr} {k : B256} (a : EntryApart T k) (F : Exec.Frame) (hpc : F.pc = 0)
    (hcode : F.sevm.code = Proxy.code) (hsg : F.sevm.benvStat.rules.stateGas = none)
    (bal : F.sevm.benvStat.rules.bal = none) (hsize : F.sevm.data.length < 2 ^ 256)
    (gas : F.pre.gasMeasure < 2 ^ 256) (target : F.sevm.currentTarget = T)
    (hne : (F.pre.getCode T).toList ≠ []) (hI : CurveCoins.UsdcImplAt F.pre T)
    (sel : Blanc.Sevm.selector F.sevm ∈ usdcInitializers)
    (recipient : Blanc.Sevm.selector F.sevm = 0x2fc81e09 →
      k ≠ mapSlot (Sevm.dataWord F.sevm 4).toAdr.toB256 9)
    (migration : Blanc.Sevm.selector F.sevm = 0x430239b4 → MigrationApart k F.sevm) :
    (F.post.getStor T).get k = (F.pre.getStor T).get k := by
  refine frame_cellInv F hsg hne k (Inv := fun v => v = (F.pre.getStor T).get k) rfl ?_
  intro m member w found _ key _
  exfalso
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := F
  dsimp only at hpc hcode hsg bal hsize gas target hne hI sel recipient migration member
  subst hpc
  subst target
  obtain ⟨r, hr, chain⟩ := (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run m).mp member
  have rootCase := hr
  simp only [Exec.rawFrameRoots, List.mem_cons] at hr
  rcases hr with rfl | hr
  · obtain ⟨hat, rest, stack⟩ := successfulSstore?_decoded found
    rcases Proxy.proxy_sstoreNodeH run hcode hsg bal chain hat with ⟨rest', hs⟩ | ⟨rest', hs, -, -⟩
    · rw [stack] at hs
      exact a.admin (key.symm.trans (List.cons.inj hs).1)
    · rw [stack] at hs
      exact a.impl (key.symm.trans (List.cons.inj hs).1)
  · obtain ⟨cp, version, tgt, data, sg⟩ := init_children run hcode hsg bal hsize hI sel r hr
    have fresh : Exec.FreshEntry r.sevm r.devm :=
      Exec.rawFrameDescendants_entered enteredCondition_fresh run r hr
    have rgas : r.devm.gasMeasure < 2 ^ 256 :=
      (Exec.rawFrameRoots_gasMeasure_le run r rootCase).trans_lt gas
    have same : Blanc.Sevm.selector r.sevm = Blanc.Sevm.selector sevm := by
      simp only [Blanc.Sevm.selector, Sevm.dataWord, data]
    have word : Sevm.dataWord r.sevm 4 = Sevm.dataWord sevm 4 := by
      simp only [Sevm.dataWord, data]
    rcases mem_inits.mp sel with s | s | s | s
    · exact init_write_ne a cp sg fresh rgas version (.inl (same.trans s)) chain found key
    · exact init_write_ne a cp sg fresh rgas version (.inr (same.trans s)) chain found key
    · exact init2_write_ne a cp sg fresh rgas version tgt (.inl (same.trans s))
        (fun _ => by rw [word]; exact recipient s)
        (fun hs => absurd (s.symm.trans (same.symm.trans hs)) (by decide)) chain found key
    · exact init2_write_ne a cp sg fresh rgas version tgt (.inr (same.trans s))
        (fun hs => absurd (s.symm.trans (same.symm.trans hs)) (by decide))
        (fun _ => (migration s).of_data data) chain found key

/-! ## The field -/

/-- `initializeV2_1` names no recipient at the holder's entry (a calldata fact per frame). -/
def RecipientsApart (T h : Adr) (settled : List Exec.Frame) : Prop :=
  ∀ F ∈ settled, F.sevm.currentTarget = T → F.sevm.isStatic = false → EntryObs T F →
    Blanc.Sevm.selector F.sevm = 0x2fc81e09 → balSlot h ≠ mapSlot (Sevm.dataWord F.sevm 4).toAdr.toB256 9

/-- `initializeV2_2`'s account list is apart from the holder's entry (a calldata fact per frame). -/
def MigrationsApart (T h : Adr) (settled : List Exec.Frame) : Prop :=
  ∀ F ∈ settled, F.sevm.currentTarget = T → F.sevm.isStatic = false → EntryObs T F →
    Blanc.Sevm.selector F.sevm = 0x430239b4 → MigrationApart (balSlot h) F.sevm

/-- **`InitializerKeeps`, over a mid history.** No flag of USDC is read. `hasCode` and `certified` are
what the chain's frames carry; `certified` is the proxy admin's power. -/
theorem initializerKeeps {cfg : ChainConfig} {start : Benv} {future : BlockChain} {T h : Adr}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (capabilities : BodyStageCapabilities HistFork) (a : EntryApart T (balSlot h))
    (hasCode : ∀ F ∈ trace.settledFrames, F.sevm.currentTarget = T → EntryObs T F →
      (F.pre.getCode T).toList ≠ [])
    (certified : ∀ F ∈ trace.settledFrames, F.sevm.currentTarget = T → EntryObs T F →
      CurveCoins.UsdcImplAt F.pre T)
    (recipients : RecipientsApart T h trace.settledFrames)
    (migrations : MigrationsApart T h trace.settledFrames) :
    InitializerKeeps T h trace.settledFrames := by
  intro F member target nonstatic obs sel
  have raw := trace.mem_rawFrames_of_mem_settledFrames F member
  obtain ⟨pc, fork⟩ := trace.rootEntryIn _ raw
  obtain ⟨_, _, block, inBlock⟩ := trace.rawFrames_mem_block _ raw
  have gas : F.pre.gasMeasure < 2 ^ 256 := by
    have := block.gas_bound capabilities _ inBlock
    change F.pre.gasMeasure < _ at this
    omega
  have keep := frame_init_keep a F pc obs.1 fork.stateGas_none fork.bal_none
    (trace.calldata_bound capabilities (fun _ hf => hf.dataNonZero_ge) _ raw) gas target
    (hasCode F member target obs) (certified F member target obs) sel
    (recipients F member target nonstatic obs) (migrations F member target nonstatic obs)
  have words : ∀ w : State, ledgerView (wordsAt T w) (balSlot h) = (w.getStor T).get (balSlot h) :=
    fun w => ledgerView_bal a.impl a.admin
  unfold heldAt
  simp only [words]
  have keep' : (F.post.state.getStor T).get (balSlot h) = (F.pre.state.getStor T).get (balSlot h) := keep
  rw [keep']

/-! ## The pool's entry -/

/-- The pool's address. Curve's `poolAddress`, kept as a literal so as not to import the pool. -/
def curvePoolWord : Adr := 0xbebc44782c7db0a1a60cb6fe97d0b483032ff1c7

/-- **The pool's USDC entry is apart from the initializers' keys.** Computed from the two addresses:
a reader can recompute each hash. No hash assumption enters. -/
theorem entryApart_pool : EntryApart usdcProxy (balSlot curvePoolWord) where
  low := by decide +kernel
  name := by unfold StrApart; decide +kernel
  symbol := by unfold StrApart; decide +kernel
  currency := by unfold StrApart; decide +kernel
  impl := by decide +kernel
  admin := by decide +kernel
  self3 := by decide +kernel
  self9 := by decide +kernel

end Blanc.Lift.Usdc
