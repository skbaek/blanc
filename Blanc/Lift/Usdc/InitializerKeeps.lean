import Blanc.Lift.Usdc.EntryChain
import Blanc.Lift.Usdc.InitRowsHistory
import Blanc.Lift.Usdc.V21InitializerReach
import Blanc.Lift.Usdc.V22InitializerReach

/-!
# USDC's initializers keep a holder's entry

`initializerKeeps` discharges `InitializerKeeps` over a mid history. No flag of the contract is read:
an initializer's stores are classified by the prefix walks, whatever the frame's outcome and whatever
`initialized` and `_initializedVersion` hold.

* `StrApart`, `EntryApart`: closed arithmetic on the entry's word. A string's payload stays within
  `2 ^ 251` words of its hash whatever its stored header says, so an entry outside those intervals
  misses every payload and clearing store. `entryApart_pool` (`InitializerKeepsPool`) computes this
  for the pool's entry;
* `init_write_ne`: `initialize` and `initializeV2`, all three versions, miss the entry;
* `init2_word`, `init2_bits`: `initializeV2_1` and `initializeV2_2` do land on a holder named in the
  calldata, and the entry's reading does not fall: a recipient's credit, and a listed account's balance
  bits under the blacklist flag;
* `init_children`: below a proxy frame on these selectors runs one level of implementation frames;
* `frame_init_keep`, `frame_init_mono`: the committed frame keeps the entry's word on the first two
  selectors, and doesn't lower its reading on the last two.

One premise is left, `MigrationsApart`, of the hash class: `initializeV2_2` writes `0` at each listed
account's `keccak(a ‖ 3)`, so a collision with the entry there would lower it.
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

/-- **The migration's old-blacklist rows miss the entry**: `initializeV2_2` writes `0` at `keccak(a ‖ 3)`
for each listed account `a`. A statement of the hash class: no value bound removes it. -/
def MigrationApart (k : B256) (sevm : Sevm) : Prop :=
  ∀ j < min (InitReachV2_2.arrLen sevm).toNat (2 ^ 32),
    k ≠ mapSlot (InitReachV2_2.acctAt sevm (InitReachV2_2.arrPtr sevm) j) 3

/-- **Under V2_1's code a store on these selectors doesn't lower the entry's word.** V2 has no such
selector, nor V2_1 `initializeV2_2`. -/
theorem init2_word {T : Adr} {k : B256} (a : EntryApart T k) {G N : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (version : CurveCoins.UsdcVersion G.sevm.code)
    (notV22 : G.sevm.code ≠ Impl.code) (target : G.sevm.currentTarget = T)
    (sel : Blanc.Sevm.selector G.sevm = 0x2fc81e09 ∨ Blanc.Sevm.selector G.sevm = 0x430239b4)
    (chain : Exec.Deriv.ParentPrefix G N) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? N = some w) (key : w.key = k) :
    (N.devm.getStorVal T k).toNat ≤ w.value.toNat := by
  rcases version with code | code | code
  · exfalso
    obtain ⟨site, inRoot, -, guards, -⟩ := WriteSite.successfulSstore_site ImplV2.cert_check
      implV2_wsCert hpc code hsg chain found
    have mem := WriteSite.hasSel_sound (List.all_eq_true.mp v2_sites site inRoot) rfl guards
    rw [selV2T_root] at mem
    rcases sel with hs | hs <;> rw [hs] at mem <;> exact absurd mem (by decide)
  · rcases sel with hs | hs
    · have same := Exec.Deriv.ParentPrefix.sevm_eq chain
      rcases V21InitializerReach.successfulSstore_all_source hpc code hsg chain hs found with
        e | ⟨-, -, e, -⟩ | ⟨-, bound, e, -⟩ | ⟨-, e, -⟩
      · exact absurd (key.symm.trans e) (not_low a (by decide))
      · exact absurd (key.symm.trans e) (by rw [target]; exact a.self9)
      · rw [same, target, key] at bound
        exact bound
      · exact absurd (key.symm.trans e) (by rw [target]; exact a.self3)
    · exfalso
      obtain ⟨site, inRoot, -, guards, -⟩ := WriteSite.successfulSstore_site ImplV2_1.cert_check
        implV2_1_wsCert hpc code hsg chain found
      have mem := WriteSite.hasSel_sound (List.all_eq_true.mp v2_1_sites site inRoot) rfl guards
      rw [selV2T_root, hs] at mem
      exact absurd mem (by decide)
  · exact absurd code notV22

/-- **Under V2_2's code a store on these selectors doesn't lower the entry's balance bits**, given the
migration's old-blacklist rows miss the entry. -/
theorem init2_bits {T : Adr} {k : B256} (a : EntryApart T k) {G N : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (empty : G.devm.stack = [])
    (code : G.sevm.code = Impl.code) (target : G.sevm.currentTarget = T)
    (sel : Blanc.Sevm.selector G.sevm = 0x2fc81e09 ∨ Blanc.Sevm.selector G.sevm = 0x430239b4)
    (migration : Blanc.Sevm.selector G.sevm = 0x430239b4 → MigrationApart k G.sevm)
    (chain : Exec.Deriv.ParentPrefix G N) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? N = some w) (key : w.key = k) :
    balanceBits (N.devm.getStorVal T k) ≤ balanceBits w.value := by
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rcases sel with hs | hs
  · rcases V22InitializerReach.successfulSstore_credit hpc code hsg chain hs found with
      e | ⟨-, e, -⟩ | ⟨-, bound, e, -⟩ | ⟨-, e, -⟩
    · exact absurd (key.symm.trans e) (not_low a (by decide))
    · exact absurd (key.symm.trans e) (by rw [target]; exact a.self9)
    · rw [same, target, key] at bound
      exact bound
    · exact absurd (key.symm.trans e) (by rw [target]; exact a.self9)
  · obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
    obtain ⟨κ, reach, ok⟩ :=
      observed_reach_of_parentPrefix_noStateGas Impl.cert_check hpc code hsg chain
    obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
    have atStore : AtSstore (κ.conf N.devm) := ⟨g, tree⟩
    change ObservedReach (StepIn G) (Cursor.RawEdgeAt Impl.code Impl.cert G N)
      Impl.cert.prog G.sevm ⟨G.devm, Impl.t_0000_c0, []⟩ (κ.conf N.devm) at reach
    rw [St.self empty rfl] at reach
    have bound : min (InitReachV2_2.strLen G.sevm) (2 ^ 32) ≤ 2 ^ 160 :=
      (Nat.min_le_right _ _).trans (by decide)
    rcases InitReachV2_2.initV2_2_bits (fun h => StepIn.toRun h)
        ((selWord_eq_selector _).trans hs) hsg reach atStore with
      ⟨key', v, S, stack', alt⟩ | other
    · have e := (List.cons.inj ((show N.devm.stack = _ from stack').symm.trans stack)).1
      rw [e, key] at alt
      exfalso
      rcases alt with fixed | ⟨j, hj, payload⟩ | ⟨-, clear⟩
      · exact not_low a (x := 5) (by decide) fixed
      · exact a.symbol.not_payload (hj.trans (payload_bound bound)) payload
      · exact a.symbol.not_clear (payload_bound bound) clear
    · rcases other w.key w.value rest stack with e | ⟨j, hj, e⟩ | e | kept
      · exact absurd (key.symm.trans e) (not_low a (by decide))
      · exact absurd (key.symm.trans e) (migration hs j hj)
      · exact absurd (key.symm.trans e) (by rw [target]; exact a.self3)
      · change balanceBits w.value = balanceBits (N.devm.getStorVal _ w.key) at kept
        rw [target, key] at kept
        exact kept.ge

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
structure InitChild (T : Adr) (data : Bytes) (impl : ByteArray) (D : Exec.Deriv) : Prop where
  pc : D.pc = 0
  version : CurveCoins.UsdcVersion D.sevm.code
  code : D.sevm.code = impl
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
    ∀ D ∈ Exec.rawFrameDescendants run, InitChild sevm.currentTarget sevm.data
      (pre.getCode (pre.getStorVal sevm.currentTarget implSlot).toAdr) D := by
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
  exact ⟨rfl, by show CurveCoins.UsdcVersion frame.inner.code; rw [hcC, hslotCode]; exact hI,
    by show frame.inner.code = _; rw [hcC, hslotCode], target, hdata, childSg⟩

/-- Selector and migration read only the calldata. -/
theorem MigrationApart.of_data {k : B256} {s s' : Sevm} (e : s'.data = s.data)
    (h : MigrationApart k s) : MigrationApart k s' := by
  simpa only [MigrationApart, InitReachV2_2.arrLen, InitReachV2_2.arrPtr, InitReachV2_2.acctAt,
    Sevm.dataWord, e] using h

/-- **What a committed proxy frame on an initializer does to the entry**: the proxy's own stores miss it,
so only the stores of the implementation frames below it count. -/
theorem frame_init_cell {T : Adr} {k : B256} {Inv : B256 → Prop} (a : EntryApart T k) (F : Exec.Frame)
    (hpc : F.pc = 0) (hcode : F.sevm.code = Proxy.code) (hsg : F.sevm.benvStat.rules.stateGas = none)
    (bal : F.sevm.benvStat.rules.bal = none) (hsize : F.sevm.data.length < 2 ^ 256)
    (gas : F.pre.gasMeasure < 2 ^ 256) (target : F.sevm.currentTarget = T)
    (hne : (F.pre.getCode T).toList ≠ []) (hI : CurveCoins.UsdcImplAt F.pre T)
    (sel : Blanc.Sevm.selector F.sevm ∈ usdcInitializers)
    (init : Inv ((F.pre.getStor T).get k))
    (child : ∀ G N : Exec.Deriv, InitChild T F.sevm.data (F.pre.getCode (F.pre.getStorVal T implSlot).toAdr) G →
      Exec.FreshEntry G.sevm G.devm → G.devm.gasMeasure < 2 ^ 256 → Exec.Deriv.ParentPrefix G N →
      ∀ w : Exec.StorageWrite, Exec.Deriv.successfulSstore? N = some w → w.key = k →
        Inv ((N.devm.getStor T).get k) → Inv w.value) :
    Inv ((F.post.getStor T).get k) := by
  refine frame_cellInv F hsg hne k init ?_
  intro m member w found _ key held
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := F
  dsimp only at hpc hcode hsg bal hsize gas target hne hI sel init child member
  subst hpc
  subst target
  obtain ⟨r, hr, chain⟩ := (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run m).mp member
  have rootCase := hr
  simp only [Exec.rawFrameRoots, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exfalso
    obtain ⟨hat, rest, stack⟩ := successfulSstore?_decoded found
    rcases Proxy.proxy_sstoreNodeH run hcode hsg bal chain hat with ⟨rest', hs⟩ | ⟨rest', hs, -, -⟩
    · rw [stack] at hs
      exact a.admin (key.symm.trans (List.cons.inj hs).1)
    · rw [stack] at hs
      exact a.impl (key.symm.trans (List.cons.inj hs).1)
  · exact child r m (init_children run hcode hsg bal hsize hI sel r hr)
      (Exec.rawFrameDescendants_entered enteredCondition_fresh run r hr)
      ((Exec.rawFrameRoots_gasMeasure_le run r rootCase).trans_lt gas) chain w found key held

/-- **On `initialize` and `initializeV2` a committed proxy frame keeps the entry**, word for word. -/
theorem frame_init_keep {T : Adr} {k : B256} (a : EntryApart T k) (F : Exec.Frame) (hpc : F.pc = 0)
    (hcode : F.sevm.code = Proxy.code) (hsg : F.sevm.benvStat.rules.stateGas = none)
    (bal : F.sevm.benvStat.rules.bal = none) (hsize : F.sevm.data.length < 2 ^ 256)
    (gas : F.pre.gasMeasure < 2 ^ 256) (target : F.sevm.currentTarget = T)
    (hne : (F.pre.getCode T).toList ≠ []) (hI : CurveCoins.UsdcImplAt F.pre T)
    (sel : Blanc.Sevm.selector F.sevm = 0x3357162b ∨ Blanc.Sevm.selector F.sevm = 0xd608ea64) :
    (F.post.getStor T).get k = (F.pre.getStor T).get k := by
  have member : Blanc.Sevm.selector F.sevm ∈ usdcInitializers :=
    mem_inits.mpr (sel.elim .inl (.inr ∘ .inl))
  refine frame_init_cell (Inv := fun v => v = (F.pre.getStor T).get k) a F hpc hcode hsg bal hsize gas
    target hne hI member rfl ?_
  intro G N child fresh rgas chain w found key _
  have same : Blanc.Sevm.selector G.sevm = Blanc.Sevm.selector F.sevm := by
    simp only [Blanc.Sevm.selector, Sevm.dataWord, child.sameData]
  exact absurd key (init_write_ne a child.pc child.stateGas fresh rgas child.version
    (same ▸ sel) chain found)

/-- **On `initializeV2_1` and `initializeV2_2` a committed proxy frame doesn't lower the entry's
reading**, by the code the implementation word finds: its bits under V2_2, its word before. -/
theorem frame_init_mono {T : Adr} {k : B256} (a : EntryApart T k) (F : Exec.Frame) (hpc : F.pc = 0)
    (hcode : F.sevm.code = Proxy.code) (hsg : F.sevm.benvStat.rules.stateGas = none)
    (bal : F.sevm.benvStat.rules.bal = none) (hsize : F.sevm.data.length < 2 ^ 256)
    (gas : F.pre.gasMeasure < 2 ^ 256) (target : F.sevm.currentTarget = T)
    (hne : (F.pre.getCode T).toList ≠ []) (hI : CurveCoins.UsdcImplAt F.pre T)
    (sel : Blanc.Sevm.selector F.sevm = 0x2fc81e09 ∨ Blanc.Sevm.selector F.sevm = 0x430239b4)
    (migration : Blanc.Sevm.selector F.sevm = 0x430239b4 → MigrationApart k F.sevm) :
    (F.pre.getCode (F.pre.getStorVal T implSlot).toAdr = Impl.code →
      balanceBits ((F.pre.getStor T).get k) ≤ balanceBits ((F.post.getStor T).get k)) ∧
    (F.pre.getCode (F.pre.getStorVal T implSlot).toAdr ≠ Impl.code →
      ((F.pre.getStor T).get k).toNat ≤ ((F.post.getStor T).get k).toNat) := by
  have member : Blanc.Sevm.selector F.sevm ∈ usdcInitializers :=
    mem_inits.mpr (sel.elim (.inr ∘ .inr ∘ .inl) (.inr ∘ .inr ∘ .inr))
  have same : ∀ G : Exec.Deriv, G.sevm.data = F.sevm.data →
      Blanc.Sevm.selector G.sevm = Blanc.Sevm.selector F.sevm := fun G e => by
    simp only [Blanc.Sevm.selector, Sevm.dataWord, e]
  constructor
  · intro isV22
    refine frame_init_cell (Inv := fun v => balanceBits ((F.pre.getStor T).get k) ≤ balanceBits v) a F
      hpc hcode hsg bal hsize gas target hne hI member le_rfl ?_
    intro G N child fresh _ chain w found key held
    exact held.trans (init2_bits a child.pc child.stateGas fresh.1 (child.code.trans isV22) child.target
      (same G child.sameData ▸ sel)
      (fun hs => (migration ((same G child.sameData).symm.trans hs)).of_data child.sameData) chain found key)
  · intro notV22
    refine frame_init_cell (Inv := fun v => ((F.pre.getStor T).get k).toNat ≤ v.toNat) a F
      hpc hcode hsg bal hsize gas target hne hI member le_rfl ?_
    intro G N child _ _ chain w found key held
    exact held.trans (init2_word a child.pc child.stateGas child.version
      (fun e => notV22 (child.code.symm.trans e)) child.target (same G child.sameData ▸ sel) chain found key)

/-! ## The field -/

/-- `initializeV2_2`'s old-blacklist rows are apart from the holder's entry, per frame: of the hash class,
as `CoinKeysFresh` is. -/
def MigrationsApart (T h : Adr) (settled : List Exec.Frame) : Prop :=
  ∀ F ∈ settled, F.sevm.currentTarget = T → F.sevm.isStatic = false → EntryObs T F →
    Blanc.Sevm.selector F.sevm = 0x430239b4 → MigrationApart (balSlot h) F.sevm

/-- **`InitializerKeeps`, over a mid history.** No flag of USDC is read. `hasCode` and `certified` are
what the chain's frames carry; `certified` is the proxy admin's power; `migrations` is a hash-class fact
over the migration's account list. -/
theorem initializerKeeps {cfg : ChainConfig} {start : Benv} {future : BlockChain} {T h : Adr}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (capabilities : BodyStageCapabilities HistFork) (a : EntryApart T (balSlot h))
    (hasCode : ∀ F ∈ trace.settledFrames, F.sevm.currentTarget = T → EntryObs T F →
      (F.pre.getCode T).toList ≠ [])
    (certified : ∀ F ∈ trace.settledFrames, F.sevm.currentTarget = T → EntryObs T F →
      CurveCoins.UsdcImplAt F.pre T)
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
  have hsize := trace.calldata_bound capabilities (fun _ hf => hf.dataNonZero_ge) _ raw
  have code := hasCode F member target obs
  have impl := certified F member target obs
  have words : ∀ w : State, ledgerView (wordsAt T w) (balSlot h) = (w.getStor T).get (balSlot h) :=
    fun w => ledgerView_bal a.impl a.admin
  unfold heldAt
  simp only [words]
  rcases mem_inits.mp sel with s | s | s | s
  · have keep := frame_init_keep a F pc obs.1 fork.stateGas_none fork.bal_none hsize gas target code impl
      (.inl s)
    have keep' : (F.post.state.getStor T).get (balSlot h) = (F.pre.state.getStor T).get (balSlot h) := keep
    rw [keep']
  · have keep := frame_init_keep a F pc obs.1 fork.stateGas_none fork.bal_none hsize gas target code impl
      (.inr s)
    have keep' : (F.post.state.getStor T).get (balSlot h) = (F.pre.state.getStor T).get (balSlot h) := keep
    rw [keep']
  all_goals
    obtain ⟨bits, word⟩ := frame_init_mono a F pc obs.1 fork.stateGas_none fork.bal_none hsize gas target
      code impl (by first | exact .inl s | exact .inr s) (migrations F member target nonstatic obs)
    by_cases hv : V22At T F
    · rw [if_pos hv, if_pos hv]
      exact bits hv
    · rw [if_neg hv, if_neg hv]
      exact word hv

end Blanc.Lift.Usdc
