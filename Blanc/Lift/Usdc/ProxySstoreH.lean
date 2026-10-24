import Blanc.Lift.Usdc.ProxyReachH
import Blanc.Lift.ReachWalkSstore
import Blanc.Lift.CursorTreeNinst

/-!
# Every `SSTORE` a proxy frame reaches, on historical forks

The `SSTORE` twin of `proxy_reachH` (`ProxyReachH.lean`), with the kit of
`Blanc/Lift/ReachWalkSstore.lean`. A prefix reach of the proxy certificate from
entry `0` to an `SSTORE` stops either in `_setAdmin` (entry 17), writing the admin
slot, or in `_setImplementation` (entry 25), writing the implementation slot with
the word `upgradeArg` (calldata word 4 masked to an address), and then only under
the `upgradeTo` or `upgradeToAndCall` selector for a caller equal to the admin word
of the frame's entry state (`ProxySstoreConf`). The other wrappers, the getters, the
fallback and `upgradeToAndCall`'s tail after `_upgradeTo` hold no `SSTORE`
(`SstoreFreeSet`, decided).

`proxy_sstoreNodeH` is the node form at a raw `SSTORE` of a pc-0 proxy frame without
state gas: its key is the admin slot, or the implementation slot with value
`upgradeArg` under the admin-checked upgrade selectors.
-/

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- `upgradeTo(address)`. -/
def upgradeToWord : B256 := Bytes.toB256 [0x36, 0x59, 0xcf, 0xe6]

/-- `upgradeToAndCall(address,bytes)`. -/
def upgradeToAndCallWord : B256 := Bytes.toB256 [0x4f, 0x1e, 0xf2, 0x86]

/-- The upgrade argument both upgrade selectors decode: calldata word 4 masked to an address. -/
def upgradeArg (sevm : Sevm) : B256 :=
  Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& Sevm.dataWord sevm (Bytes.toB256 [0x04])

/-- What a proxy frame's `SSTORE` writes, read at the target configuration: the admin slot, or
the implementation slot with `upgradeArg` below it, under an upgrade selector, for a caller
equal to the admin word of the frame's entry state `b`. -/
def ProxySstoreConf (sevm : Sevm) (b : Devm) (T : Conf) : Prop :=
  (∃ rest, T.d.stack = adminSlot :: rest) ∨
    ∃ rest, T.d.stack = implSlot :: upgradeArg sevm :: rest ∧
      (dispatchWord sevm = upgradeToWord ∨ dispatchWord sevm = upgradeToAndCallWord) ∧
      sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr

theorem getters_sstoreFree : SstoreFreeSet prog getterEntries = true := by decide

/-- Every entry but the dispatcher, the three wrappers that write (`upgradeTo`,
`upgradeToAndCall`, `changeAdmin`), their bodies, `_upgradeTo`, `_setAdmin` and
`_setImplementation` is `SSTORE`-free. -/
def freeEntries : List Nat :=
  [3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30,
    31, 32, 35, 37]

theorem free_sstoreFree : SstoreFreeSet prog freeEntries = true := by decide

theorem empty_sstoreFree : SstoreFreeSet prog [] = true := by decide

section Walk

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}

include hP

/-- `isContract(x)`: the flag `extcodesize(x) > 0`, after one account access. -/
theorem isContract_retH (bal : sevm.benvStat.rules.bal = none) {x r : B256} {D : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: r :: S) M G) t_084b_c32 (.returned D)) :
    ∃ c G', D = St (accountAccessH sevm b x.toAdr) (c :: S) M G' := by
  unfold t_084b_c32 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_extcodesizeH bal (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_gt (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, rfl⟩ := rpw_ret run
  exact ⟨_, _, rfl⟩

/-- `_setImplementation(x)` (entry 25) writes only the implementation slot, with `x`. -/
theorem setImpl_reachS (bal : sevm.benvStat.rules.bal = none) {x r : B256}
    (run : Reach P prog sevm ⟨St b (x :: r :: S) M G, t_0779_c25, []⟩ T) (hT : AtSstore T) :
    ∃ rest, T.d.stack = implSlot :: x :: rest := by
  unfold t_0779_c25 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rs_callOver free_sstoreFree (k := 32) rfl (by decide) run hT
  obtain ⟨c, _, rfl⟩ := isContract_retH hP bal callee
  unfold t_0784_c25 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree empty_sstoreFree run hT (by decide)
      (fun _ h => by cases h)).elim
  unfold t_081e_c25 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_mul (hP s)
  rw [implSlot_word] at run
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  rcases Reach.sstoreS run with rfl | ⟨_, -, run⟩
  · exact ⟨_, rfl⟩
  · exact (Reach.false_of_sstoreFree empty_sstoreFree run hT (by decide)
      (fun _ h => by cases h)).elim

/-- `_setAdmin` (entry 17) writes only the admin slot, from any entry state. -/
theorem setAdmin_reachS {d : Devm}
    (run : Reach P prog sevm ⟨d, t_0748_c17, []⟩ T) (hT : AtSstore T) :
    ∃ rest, T.d.stack = adminSlot :: rest := by
  rw [St.self' d] at run
  unfold t_0748_c17 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_mul (hP s)
  rw [adminSlot_word] at run
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, -, _, rfl⟩ := ri_dup_any (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  rcases Reach.sstoreS run with rfl | ⟨_, -, run⟩
  · exact ⟨_, rfl⟩
  · exact (Reach.false_of_sstoreFree empty_sstoreFree run hT (by decide)
      (fun _ h => by cases h)).elim

omit hP in
/-- A step past a node other than `SSTORE`, forgetting the state. -/
theorem Reach.skipS {d : Devm} {n : Ninst} {f : SFunc} {K : List SFunc}
    (run : Reach P prog sevm ⟨d, .next n f, K⟩ T) (hT : AtSstore T)
    (hn : n ≠ .reg .sstore := by intro h; cases h) :
    ∃ d', Reach P prog sevm ⟨d', f, K⟩ T := by
  obtain ⟨d', -, rest⟩ := Reach.nextS hn run hT
  exact ⟨d', rest⟩

set_option hygiene false in
/-- Skip the non-`SSTORE` nodes of a straight line. -/
local macro "skipsS" : tactic => `(tactic| repeat (obtain ⟨_, run⟩ := Reach.skipS run hT))

set_option hygiene false in
/-- Dismiss an `SSTORE`-free tree with no pending continuation. -/
local macro "freeS" : tactic => `(tactic| exact (Reach.false_of_sstoreFree free_sstoreFree run hT
  (by decide) (fun _ h => by cases h)).elim)

/-- `changeAdmin` (entry 36, wrapper of entry 4) writes only through `_setAdmin`. -/
theorem sel36_reachS {d : Devm}
    (run : Reach P prog sevm ⟨d, t_015f_c36, []⟩ T) (hT : AtSstore T) :
    ∃ rest, T.d.stack = adminSlot :: rest := by
  unfold t_015f_c36 at run
  obtain ⟨_, -, run⟩ := Reach.destS run hT
  skipsS
  rcases Reach.branchS run hT with ⟨_, _, -, run⟩ | ⟨_, _, _, -, -, run⟩
  · freeS
  unfold t_016b_c36 at run
  obtain ⟨_, -, run⟩ := Reach.destS run hT
  skipsS
  obtain ⟨_, _, _, hk, -, ⟨T', run, rfl⟩ | ⟨_, -, run⟩⟩ := Reach.callS run hT
  swap
  · freeS
  cases hk
  replace hT : AtSstore T' := AtSstore.below.mp hT
  show ∃ rest, T'.d.stack = _
  unfold t_0360_c4 at run
  obtain ⟨_, -, run⟩ := Reach.destS run hT
  skipsS
  obtain ⟨_, _, _, hk, -, ⟨T'', run, rfl⟩ | ⟨_, -, run⟩⟩ := Reach.callS run hT
  · cases hk
    exact (Reach.false_of_sstoreFree free_sstoreFree run (AtSstore.below.mp hT)
      (by decide) (fun _ h => by cases h)).elim
  cases hk
  unfold t_0368_c4 at run
  obtain ⟨_, -, run⟩ := Reach.destS run hT
  skipsS
  rcases Reach.branchS run hT with ⟨_, _, -, run⟩ | ⟨_, _, _, -, -, run⟩
  swap
  · freeS
  unfold t_039c_c4 at run
  skipsS
  rcases Reach.branchS run hT with ⟨_, _, -, run⟩ | ⟨_, _, _, -, -, run⟩
  · freeS
  unfold t_0466_c4 at run
  obtain ⟨_, -, run⟩ := Reach.destS run hT
  skipsS
  obtain ⟨_, _, _, hk, -, ⟨T'', run, rfl⟩ | ⟨_, -, run⟩⟩ := Reach.callS run hT
  · cases hk
    exact (Reach.false_of_sstoreFree free_sstoreFree run (AtSstore.below.mp hT)
      (by decide) (fun _ h => by cases h)).elim
  cases hk
  unfold t_048f_c4 at run
  obtain ⟨_, -, run⟩ := Reach.destS run hT
  skipsS
  obtain ⟨_, _, _, hk, -, ⟨T'', run, rfl⟩ | ⟨_, -, run⟩⟩ := Reach.callS run hT
  · cases hk
    dsimp only at run
    obtain ⟨rest, hs⟩ := setAdmin_reachS hP run (AtSstore.below.mp hT)
    exact ⟨rest, hs⟩
  · freeS

/-- `_upgradeTo(x)` (entry 9) writes only through `_setImplementation(x)`. -/
theorem upgrade_reachS (bal : sevm.benvStat.rules.bal = none) {x : B256}
    (run : Reach P prog sevm ⟨St b (x :: S) M G, t_06d9_c9, []⟩ T) (hT : AtSstore T) :
    ∃ rest, T.d.stack = implSlot :: x :: rest := by
  unfold t_06d9_c9 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, T', inner, rfl⟩ := rs_callInto empty_sstoreFree (k := 25) rfl (by decide)
    (fun _ h => by cases h) run hT
  dsimp only at inner
  obtain ⟨rest, hs⟩ := setImpl_reachS hP bal inner (AtSstore.below.mp hT)
  exact ⟨rest, hs⟩

/-- `upgradeTo` (entry 33, wrapper of entry 1): it writes only on its admin side, through
`_upgradeTo` of its decoded argument. -/
theorem sel33_reachS (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256}
    (run : Reach P prog sevm ⟨St b (x :: S) M G, t_0077_c33, []⟩ T) (hT : AtSstore T) :
    ∃ rest, T.d.stack = implSlot :: upgradeArg sevm :: rest ∧
      sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr := by
  unfold t_0077_c33 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_007f_c33 at run
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    exact (Reach.not_lastS run hT).elim
  unfold t_0083_c33 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_sub (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, T', inner, rfl⟩ := rs_callInto empty_sstoreFree (k := 1) rfl (by decide)
    (fun _ h => by cases h) run hT
  dsimp only at inner
  replace run := inner
  replace hT : AtSstore T' := AtSstore.below.mp hT
  show ∃ rest, T'.d.stack = _ ∧ _
  unfold t_0213_c1 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rs_callOver getters_sstoreFree (k := 8) rfl (by decide) run hT
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
  unfold t_021b_c1 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rs_branch run hT with ⟨hz, _, run⟩ | ⟨-, _, run⟩
  · have hadm : sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr :=
      (masked_eq_iff _ _).mp (eqCheck_ne_zero (iszero_eq_zero hz))
    unfold t_024f_c1 at run
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, T'', inner9, rfl⟩ := rs_callInto free_sstoreFree (k := 9) rfl (by decide)
      (fun _ h => by cases h) run hT
    dsimp only at inner9
    obtain ⟨rest, hs⟩ := upgrade_reachS hP bal inner9 (AtSstore.below.mp hT)
    exact ⟨rest, hs, hadm⟩
  · unfold t_025c_c1 at run
    obtain ⟨_, run⟩ := rs_dest run hT
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨g, _, hg, run⟩ := rs_jump run hT
    exact (Reach.false_of_sstoreFree free_sstoreFree run hT
      (SstoreFreeSet.lookup free_sstoreFree (by decide) hg) (fun _ h => by cases h)).elim

/-- `upgradeToAndCall` (entry 34, wrapper of entry 2): it writes only on its admin side,
through `_upgradeTo` of its decoded address argument, before its self-call. -/
theorem sel34_reachS (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256}
    (run : Reach P prog sevm ⟨St b (x :: S) M G, t_00ba_c34, []⟩ T) (hT : AtSstore T) :
    ∃ rest, T.d.stack = implSlot :: upgradeArg sevm :: rest ∧
      sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr := by
  unfold t_00ba_c34 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_sub (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 3) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 3) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, T', inner, rfl⟩ := rs_callInto empty_sstoreFree (k := 2) rfl (by decide)
    (fun _ h => by cases h) run hT
  dsimp only at inner
  replace run := inner
  replace hT : AtSstore T' := AtSstore.below.mp hT
  show ∃ rest, T'.d.stack = _ ∧ _
  unfold t_0268_c2 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rs_callOver getters_sstoreFree (k := 8) rfl (by decide) run hT
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
  unfold t_0270_c2 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rs_branch run hT with ⟨hz, _, run⟩ | ⟨-, _, run⟩
  · have hadm : sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr :=
      (masked_eq_iff _ _).mp (eqCheck_ne_zero (iszero_eq_zero hz))
    unfold t_02a4_c2 at run
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, T'', inner9, rfl⟩ := rs_callInto free_sstoreFree (k := 9) rfl (by decide)
      (fun _ h => by cases h) run hT
    dsimp only at inner9
    obtain ⟨rest, hs⟩ := upgrade_reachS hP bal inner9 (AtSstore.below.mp hT)
    exact ⟨rest, hs, hadm⟩
  · unfold t_02fa_c2 at run
    obtain ⟨_, run⟩ := rs_dest run hT
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨g, _, hg, run⟩ := rs_jump run hT
    exact (Reach.false_of_sstoreFree free_sstoreFree run hT
      (SstoreFreeSet.lookup free_sstoreFree (by decide) hg) (fun _ h => by cases h)).elim


/-- **Every `SSTORE` a proxy frame reaches.** -/
theorem proxy_sstoreH (bal : sevm.benvStat.rules.bal = none) {b : Devm}
    (run : Reach P prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtSstore T) :
    ProxySstoreConf sevm b T := by
  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_000d_c0 at run
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_div (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rs_branchTo run hT with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_0077_c33 := Option.some.inj (hg.symm.trans rfl)
      obtain ⟨rest, hs, hadm⟩ := sel33_reachS hP bal run hT
      exact .inr ⟨rest, hs, .inl (eqCheck_ne_zero h).symm, hadm⟩
    unfold t_0041_c0 at run
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rs_branchTo run hT with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_00ba_c34 := Option.some.inj (hg.symm.trans rfl)
      obtain ⟨rest, hs, hadm⟩ := sel34_reachS hP bal run hT
      exact .inr ⟨rest, hs, .inr (eqCheck_ne_zero h).symm, hadm⟩
    unfold t_004c_c0 at run
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rs_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_0108_c35 := Option.some.inj (hg.symm.trans rfl)
      exact (Reach.false_of_sstoreFree free_sstoreFree run hT (by decide)
        (fun _ h => by cases h)).elim
    unfold t_0057_c0 at run
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rs_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_015f_c36 := Option.some.inj (hg.symm.trans rfl)
      exact .inl (sel36_reachS hP run hT)
    unfold t_0062_c0 at run
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rs_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_01a2_c37 := Option.some.inj (hg.symm.trans rfl)
      exact (Reach.false_of_sstoreFree free_sstoreFree run hT (by decide)
        (fun _ h => by cases h)).elim
    unfold t_006d_c0 at run
    obtain ⟨_, run⟩ := rs_dest run hT
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨g, _, hg, run⟩ := rs_jump run hT
    exact (Reach.false_of_sstoreFree free_sstoreFree run hT
      (SstoreFreeSet.lookup free_sstoreFree (by decide) hg) (fun _ h => by cases h)).elim
  unfold t_006d_c0_1 at run
  obtain ⟨_, run⟩ := rs_dest run hT
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rs_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rs_jump run hT
  exact (Reach.false_of_sstoreFree free_sstoreFree run hT
      (SstoreFreeSet.lookup free_sstoreFree (by decide) hg) (fun _ h => by cases h)).elim


end Walk

/-- **The `SSTORE`s of a proxy frame on a historical fork.** At a node of a pc-0 proxy frame
without state gas decoding `SSTORE`, the key on the stack is the admin slot, or the
implementation slot with `upgradeArg` below it, under an upgrade selector, for a caller equal
to the admin word of the frame's entry state. -/
theorem proxy_sstoreNodeH {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    (hat : Ninst.At N.sevm.code N.pc (.reg .sstore)) :
    (∃ rest, N.devm.stack = adminSlot :: rest) ∨
      ∃ rest, N.devm.stack = implSlot :: upgradeArg sevm :: rest ∧
        (dispatchWord sevm = upgradeToWord ∨ dispatchWord sevm = upgradeToAndCallWord) ∧
        sevm.caller = (pre.getStorVal sevm.currentTarget adminSlot).toAdr := by
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix_noStateGas cert_check
    (R := ⟨0, sevm, pre, out, run⟩) rfl codeEq hsg chain
  obtain ⟨g, hf, -⟩ := ok.tree_of_sstore hat
  have hT : AtSstore (κ.conf N.devm) := ⟨g, hf⟩
  change Reach _ _ _ ⟨pre, t_0000_c0, []⟩ _ at reach
  rw [show (⟨pre, t_0000_c0, []⟩ : Conf) =
      ⟨St pre pre.stack pre.memory pre.gasLeft, t_0000_c0, []⟩ by rw [← St.self' pre]] at reach
  exact proxy_sstoreH (fun h => StepIn.toRun h) bal reach hT

end Blanc.Lift.Usdc.Proxy
