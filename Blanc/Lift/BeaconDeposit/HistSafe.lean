import Blanc.Lift.BeaconDeposit.HistSafeGuards
import Blanc.Lift.BeaconDeposit.HistSafeCount
import Blanc.Lift.BeaconDeposit.HistSafeInsert
import Blanc.Lift.BeaconDeposit.HistSafePubkeyRoot
import Blanc.Lift.BeaconDeposit.HistSafeNode
import Blanc.Lift.BeaconDeposit.HistSafeSignatureRoot
import Blanc.Lift.BeaconDeposit.CommittedExec

/-!
# The deployed runtime refines the model over a historical frame (B1, safety)

The historical counterpart of `Safe.lean`: the same per-frame refinement with `CoveredFork`
replaced by the two rule facts every historical fork carries (`rules.stateGas = none`,
`rules.bal = none`, from `HistFork.stateGas_none`/`HistFork.bal_none`) and `ShaReady` by
`ShaReadyH`.  The conclusion of `deposit_frame_refinesH` is `deposit_frame_refines`'s verbatim.
The route: `lift_sound_noStateGas`; the dispatcher; the views by `SFunc.Run.world_of_quietH`;
the decoder and the body's historical segments (`safe_guardsH` … `safe_countBumpH`); the
insertion loop over `LoopBaseH` with `safe_insertDeadH`/`safe_insertLiveH`.  Frame tails:
`frame_solInvH`, `successful_deposit_not_staticH`, `frameAccepted_eq_nil_of_staticH`.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## The views -/

theorem view_worldH {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none) {k : Nat} {g : SFunc}
    {d : Devm} {o : Outcome} (hk : k ∈ viewSet) (hg : prog[k]? = some g)
    (run : SFunc.Run prog sevm d g o) :
    Devm.getStor (Outcome.devm o) = Devm.getStor d ∧ (Outcome.devm o).logs = d.logs := by
  have h := (List.all_eq_true.mp viewSet_quiet) k hk
  rw [hg] at h
  simp only [Bool.and_eq_true] at h
  exact SFunc.Run.world_of_quietH viewSet_quiet hsg h.1 h.2 run

/-! ## The insertion loop -/

/-- **The insertion loop, inverted**: every successful run from the loop head at height `0`
stores at a height `h` whose size bit is set and below which every bit is clear, and returns. -/
theorem safe_insert_loopH {sevm : Sevm} {b₀ : Devm} {x : Nat} {node0 : B256}
    {br : Nat → B256} {stor1 : Stor}
    {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ y₅ y₆ y₇ d : B256} {rest : List B256}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none)
    (hsha : ShaReadyH sevm b₀) (hrest : rest.length ≤ 4) (hx : x < 2 ^ 256)
    (hstor1 : Devm.getStor b₀ sevm.currentTarget = stor1)
    (hbr : ∀ h < 32, stor1.get (solBranchSlot h) = br h)
    {M : Mem} {G : Nat} {o : Outcome}
    (hM : BodyMem M (1024 + 96 * 0) (Nat.toB256 (928 + 96 * 0)) [])
    (run : SFunc.Run prog sevm (St b₀ (Nat.toB256 0 :: Nat.toB256 (x / 2 ^ 0) ::
      insertNode Bytes.sha256 br 0 node0 ::
      x₁ :: x₂ :: x₃ :: x₄ :: y₁ :: y₂ :: y₃ :: y₄ :: y₅ :: y₆ :: y₇ :: d :: rest) M G)
      t_0f6e_c23 o) :
    ∃ h bf Mf Gf, o = .returned (St bf rest Mf Gf) ∧ h < 32 ∧ (∀ j < h, (x / 2 ^ j) % 2 = 0) ∧
      (x / 2 ^ h) % 2 = 1 ∧
      BaseRel (afterSstoreH sevm b₀ (solBranchSlot h) (insertNode Bytes.sha256 br h node0)) bf := by
  let T : List B256 := [x₁, x₂, x₃, x₄, y₁, y₂, y₃, y₄, y₅, y₆, y₇, d] ++ rest
  let I : Devm → Prop := fun devm => ∃ h bh Mh Gh,
    devm = St bh (Nat.toB256 h :: Nat.toB256 (x / 2 ^ h) :: insertNode Bytes.sha256 br h node0 :: T)
      Mh Gh ∧ h ≤ 32 ∧ (∀ j < h, (x / 2 ^ j) % 2 = 0) ∧
      LoopBaseH b₀ bh ∧
      BodyMem Mh (1024 + 96 * h) (Nat.toB256 (928 + 96 * h)) []
  let Q : Outcome → Prop := fun o => ∃ h bf Mf Gf, o = .returned (St bf rest Mf Gf) ∧ h < 32 ∧
    (∀ j < h, (x / 2 ^ j) % 2 = 0) ∧ (x / 2 ^ h) % 2 = 1 ∧
    BaseRel (afterSstoreH sevm b₀ (solBranchSlot h) (insertNode Bytes.sha256 br h node0)) bf
  have hL0 : LoopBaseH b₀ b₀ := LoopBaseH.refl b₀
  refine SFunc.RunP.loop (P := Ninst.Run) (k := 23) (g := t_0f6e_c23) rfl I Q ?_ _ o
    ⟨0, b₀, M, G, rfl, by omega, fun j hj => absurd hj (Nat.not_lt_zero _), hL0, hM⟩ run
  intro devm ⟨h, bh, Mh, Gh, hdevm, hh, hdead, hL, hMh⟩ r hrun
  subst hdevm
  have hxh : x / 2 ^ h < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have hszv : (Nat.toB256 (x / 2 ^ h)).toNat = x / 2 ^ h := B256.toNat_toB256_of_lt hxh
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ h) with hbit | hbit
  · obtain ⟨hh32, b', M', G', hK, hM', rfl⟩ := safe_insertDeadH (hsha.of_eq hL.code hL.addrs) hh
      (by rw [hszv]; exact hbit) (by simp only [T, List.cons_append, List.nil_append, List.length_cons, Nat.reduceLeDiff]; omega) hMh hrun
    refine ⟨h + 1, b', M', G', ?_, by omega, ?_, hL.step hK, ?_⟩
    · have hsz : Nat.toB256 (x / 2 ^ h) / 2 = Nat.toB256 (x / 2 ^ (h + 1)) := by
        rw [toB256_div_two hxh, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      have hnd : BeaconDeposit.hashPair Bytes.sha256
          (bh.getStorVal sevm.currentTarget (solBranchSlot h))
          (insertNode Bytes.sha256 br h node0) = insertNode Bytes.sha256 br (h + 1) node0 := by
        show _ = BeaconDeposit.hashPair Bytes.sha256 (br h) _
        congr 1
        show (Devm.getStor bh sevm.currentTarget).get _ = _
        rw [hL.stor, hstor1, hbr h hh32]
      rw [hsz, hnd]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hdead j hj
      · exact hbit
    · rw [show 1024 + 96 * (h + 1) = 1120 + 96 * h by omega,
        show 928 + 96 * (h + 1) = 1024 + 96 * h by omega]
      exact hM'
  · obtain ⟨hh32, b', G', hK, rfl⟩ := safe_insertLiveH hsg hbal (hh := hh)
      (by rw [hszv]; exact hbit) hrun
    refine ⟨h, b', Mh, G', rfl, hh32, hdead, hbit, ?_⟩
    refine ⟨fun a => ?_, fun a => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hK.stor, getStor_afterSstoreH, getStor_afterSstoreH, hL.stor, hL.stor]
    · rw [hK.code, afterSstoreH_getCode, afterSstoreH_getCode, hL.code]
    · rw [hK.addrs, afterSstoreH_accessedAddresses, afterSstoreH_accessedAddresses, hL.addrs]
    · rw [hK.logs, afterSstoreH_logs, afterSstoreH_logs, hL.logs]
    · rw [hK.output, afterSstoreH_output, afterSstoreH_output, hL.output]
    · rw [hK.error, afterSstoreH_error, afterSstoreH_error, hL.error]

/-! ## The `deposit` route -/

/-- The `deposit` wrapper's successful runs, from the dispatcher's hand-off. -/
theorem deposit_routeH {sevm : Sevm} {pre post : Devm} {history : List B256} {G1 : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none) (hcd : sevm.data.length < 2 ^ 256)
    (hsha : ShaReadyH sevm pre)
    (hinv : SolInv (Devm.getStor pre sevm.currentTarget) history)
    (run : SFunc.Run prog sevm (St pre [Sevm.selector sevm] mem0 G1) t_00a4_c32 (.halted post)) :
    DepositDecodable sevm ∧ ∃ s' ev,
        BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor pre sevm.currentTarget))
          (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm)
          sevm.value.toNat = .ok (s', ev) ∧
        solAcc (Devm.getStor post sevm.currentTarget) = s' ∧
        SolInv (Devm.getStor post sevm.currentTarget)
          (history ++ [BeaconDeposit.depositDataNode Bytes.sha256 (argBytes sevm 0)
            (argBytes sevm 1) (argBytes sevm 2) ev.amount]) ∧
        (∃ h v, h < 32 ∧ Devm.getStor post sevm.currentTarget =
          ((Devm.getStor pre sevm.currentTarget).set solCountSlot (1 + bodyCount sevm pre)).set
            (solBranchSlot h) v) ∧
        (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
        post.logs = pre.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] := by
  obtain ⟨hdec, G2, d, runB, hpostStor, hpostLogs⟩ := safe_decoder hcd run
  refine ⟨hdec, ?_⟩
  set sel := Sevm.selector sevm
  set b0 := St pre [sel] mem0 G1 with hb0
  set tgt := sevm.currentTarget with htgt
  set stor := Devm.getStor pre tgt with hstor
  set w := bodyCount sevm pre with hw
  have hw0 : b0.getStorVal tgt solCountSlot = w := rfl
  set pP := argPtr sevm 0
  set wP := argPtr sevm 1
  set sP := argPtr sevm 2
  set rt := argRoot sevm
  -- segment B1
  obtain ⟨hL0, hL1, hL2, hv1, hv2, hv3, b1, M1, G3, hK1, hM1, run1⟩ :=
    safe_guardsH (b := b0) (sel := sel) (rt := rt) (sP := sP) (wP := wP) (pP := pP)
      (pkL := argLen sevm 0) (wcL := argLen sevm 1) (sgL := argLen sevm 2) hcd hbal runB
  set a := gweiAmount sevm
  set v := sevm.value.toNat
  have hamt : a.toNat = v / 10 ^ 9 := by
    rw [show a = gweiAmount sevm from rfl, gweiAmount, B256.toNat_div (by decide)]; rfl
  -- segment B2
  obtain ⟨b2, M2, G4, hK2, hM2, run2⟩ := safe_event (sevm := sevm) (b := b1) (a := a) (c := w)
    hM1 run1
  -- segment B3
  have hc1 : ∀ x, b1.getCode x = pre.getCode x := fun x => by
    rw [hK1.code, afterSloadH_getCode]; rfl
  have ha1 : b1.accessedAddresses = pre.accessedAddresses := by
    rw [hK1.addrs, afterSloadH_accessedAddresses]; rfl
  set ev := bodyEvent sevm pP wP sP a w
  have hlen : (BeaconDeposit.abiDepositEvent ev).length = 576 := by
    simp only [BeaconDeposit.abiDepositEvent, List.append_assoc, abiBytesTail, bodyEvent,
      BeaconDeposit.le64, Nat.toUInt8_eq, List.length_sliceD, ceil32, Nat.reduceMod, Nat.reduceAdd,
      Nat.succ_eq_add_one, Nat.reduceSub, List.reduceReplicate, Nat.mod_self, tsub_self,
      List.replicate_zero, List.append_nil, List.cons_append, List.nil_append, List.length_cons,
      List.length_nil, zero_add, List.length_append, B256.length_toBytes, ev]
  obtain ⟨b3, M3, G5, hK3, hM3, run3⟩ := safe_pubkeyRootH (sevm := sevm) (b := b2) (a := a)
    (hsha.of_eq (fun x => by rw [hK2.code, hc1]) (by rw [hK2.addrs, ha1])) hlen hM2 run2
  have hc3 : ∀ x, b3.getCode x = pre.getCode x := fun x => by
    rw [hK3.code]; show b2.getCode x = _; rw [hK2.code, hc1]
  have ha3 : b3.accessedAddresses = pre.accessedAddresses := by
    rw [hK3.addrs]; show b2.accessedAddresses = _; rw [hK2.addrs, ha1]
  -- segment B4
  have hsP : sP.toNat + 96 < 2 ^ 256 := by
    have := argPtr_toNat hdec.2.2.2
    have := hdec.2.2.2.1
    show (argPtr sevm 2).toNat + 96 < _
    omega
  set pkR := BeaconDeposit.pubkeyRoot Bytes.sha256 (sevm.data.sliceD pP.toNat 48 0)
  obtain ⟨b4, M4, G6, hK4, hM4, run4⟩ := safe_signatureRootH (sevm := sevm) (b := b3) (a := a)
    (pkR := pkR) (hsha.of_eq hc3 ha3) hsP hM3 run3
  -- segment B5
  set sR := BeaconDeposit.signatureRoot Bytes.sha256 (sevm.data.sliceD sP.toNat 96 0)
  obtain ⟨b5, M5, G7, hK5, hM5, run5⟩ := safe_dataNodeH (sevm := sevm) (b := b4) (a := a)
    (pkR := pkR) (sR := sR)
    (hsha.of_eq (fun x => by rw [hK4.code, hc3]) (by rw [hK4.addrs, ha3])) hM4 run4
  -- segment B6
  have hstor5 : ∀ x, Devm.getStor b5 x = Devm.getStor pre x := fun x => by
    rw [hK5.stor, hK4.stor, hK3.stor]
    show Devm.getStor b2 x = _
    rw [hK2.stor, hK1.stor, afterSloadH_getStor]; rfl
  have hw5 : b5.getStorVal sevm.currentTarget solCountSlot = w := by
    show (Devm.getStor b5 _).get _ = _
    rw [hstor5]; rfl
  obtain ⟨hroot, hcap, b6, M6, G8, hK6, hM6, run6⟩ := safe_countBumpH (sevm := sevm) (b := b5)
    (a := a) (pkR := pkR) (sR := sR) hsg hbal hM5 run5
  rw [hw5] at hcap hK6 run6
  -- the insertion loop
  set x := w.toNat + 1 with hx
  have hx32 : x < 2 ^ 32 := by omega
  set br := (solAcc stor).branch
  set stor1 := stor.set solCountSlot (1 + w)
  have hb6stor : Devm.getStor b6 sevm.currentTarget = stor1 := by
    rw [hK6.stor, afterSstoreH_getStor_self, hstor5]
  have hbr : ∀ h < 32, stor1.get (solBranchSlot h) = br h := fun h hh => by
    rw [Stor.get_set_ne _ (Ne.symm (solBranchSlot_ne_count hh))]
    simp only [solAcc, hh, ↓reduceIte, stor, br]
  have hc6 : ∀ y, b6.getCode y = pre.getCode y := fun y => by
    rw [hK6.code, afterSstoreH_getCode, hK5.code, hK4.code, hc3]
  have ha6 : b6.accessedAddresses = pre.accessedAddresses := by
    rw [hK6.addrs, afterSstoreH_accessedAddresses, hK5.addrs, hK4.addrs, ha3]
  have e1 : (1 + w) = Nat.toB256 (x / 2 ^ 0) := by
    rw [Nat.pow_zero, Nat.div_one]
    apply B256.toNat_inj
    rw [B256.toNat_toB256_of_lt (by omega), B256.toNat_add, show (1 : B256).toNat = 1 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  rw [t_0f6e_c20_eq, hroot, e1] at run6
  obtain ⟨h, bf, Mf, Gf, hd, hh, hdead, hlive, hW⟩ := safe_insert_loopH (b₀ := b6) (x := x)
    (node0 := rt) (br := br) (stor1 := stor1) (rest := [sel]) hsg hbal (hsha.of_eq hc6 ha6) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.one_le_ofNat])
    (by omega) hb6stor hbr (M := M6) (G := G8) hM6 run6
  cases hd
  have hn : h = insertDepth 32 x := insertDepth_unique (by omega) hx32 hdead hlive
  -- the model
  set nd := insertNode Bytes.sha256 br h rt
  have hlen0 : (argBytes sevm 0).length = 48 := by
    rw [argBytes, List.length_sliceD, hL0]; rfl
  have hlen1 : (argBytes sevm 1).length = 32 := by
    rw [argBytes, List.length_sliceD, hL1]; rfl
  have hlen2 : (argBytes sevm 2).length = 96 := by
    rw [argBytes, List.length_sliceD, hL2]; rfl
  have hpkB : argBytes sevm 0 = sevm.data.sliceD pP.toNat 48 0 := (argBytes_eq hlen0).1
  have hwcB : argBytes sevm 1 = sevm.data.sliceD wP.toNat 32 0 := (argBytes_eq hlen1).1
  have hsgB : argBytes sevm 2 = sevm.data.sliceD sP.toNat 96 0 := (argBytes_eq hlen2).1
  have hnode : BeaconDeposit.depositDataNode Bytes.sha256 (argBytes sevm 0) (argBytes sevm 1)
      (argBytes sevm 2) (BeaconDeposit.le64 (v / BeaconDeposit.oneGwei)) = rt := by
    rw [← hroot, hpkB, hwcB, hsgB, show BeaconDeposit.oneGwei = 10 ^ 9 from rfl, ← hamt]; rfl
  have hwalk := walk_insertNode Bytes.sha256 br rt 32 0 x (by omega) hx32
  rw [Nat.zero_add, show insertNode Bytes.sha256 br 0 rt = rt from rfl, ← hn] at hwalk
  have hOk := deposit_ok_of (H := Bytes.sha256) (s := solAcc stor) hlen0 hlen1 hlen2 hv1 hv2 hv3
    hnode (show (solAcc stor).count < 2 ^ 32 - 1 from hcap) hwalk
  refine ⟨_, _, hOk, ?_⟩
  -- the storage
  have hpostT : Devm.getStor post tgt = stor1.set (solBranchSlot h) nd := by
    rw [hpostStor]; show Devm.getStor bf _ = _
    rw [hW.stor, afterSstoreH_getStor_self, hb6stor]
  have hacc : solAcc (Devm.getStor post tgt) =
      ⟨BeaconDeposit.setSlot br h nd, (solAcc stor).count + 1⟩ := by
    rw [hpostT]
    refine acc_mk_eq ?_ ?_
    · funext j
      by_cases hj : j < 32
      · rw [ite_eq_left hj]
        unfold BeaconDeposit.setSlot
        by_cases hjh : j = h
        · subst hjh; rw [ite_eq_left rfl, Stor.get_set_self]
        · rw [ite_eq_right hjh, Stor.get_set_ne _ (fun e => hjh (solBranchSlot_inj hj hh e.symm)),
            hbr j hj]
      · rw [ite_eq_right hj]
        unfold BeaconDeposit.setSlot
        rw [ite_eq_right (by omega)]
        simp only [solAcc, hj, ↓reduceIte, br]
    · rw [Stor.get_set_ne _ (solBranchSlot_ne_count hh), Stor.get_set_self]
      have := congrArg B256.toNat e1
      rw [Nat.pow_zero, Nat.div_one, B256.toNat_toB256_of_lt (by omega)] at this
      exact this
  refine ⟨hacc, ⟨fun h' hh' => ?_, ?_⟩, ⟨h, nd, hh, hpostT⟩, fun y hy => ?_, ?_⟩
  · -- the zero-hash table
    obtain ⟨n1, n2⟩ := solZeroHashSlot_ne hh' hh
    rw [hpostT, Stor.get_set_ne _ (Ne.symm n1), Stor.get_set_ne _ (Ne.symm n2)]
    exact hinv.1 h' hh'
  · rw [hacc]
    exact BeaconDeposit.deposit_inv Bytes.sha256 _ _ _ _ _ _ _ _ _ hinv.2 hOk
  · rw [hpostStor]; show Devm.getStor bf _ = _
    rw [hW.stor, getStor_afterSstoreH, ite_eq_right hy, hK6.stor, getStor_afterSstoreH,
      ite_eq_right hy, hstor5]
  · rw [hpostLogs]; show bf.logs = _
    rw [hW.logs, afterSstoreH_logs, hK6.logs, afterSstoreH_logs, hK5.logs, hK4.logs,
      hK3.logs]
    show b2.logs ++ _ = _
    rw [hK2.logs, hK1.logs, afterSloadH_logs]
    have hev : ev = ⟨argBytes sevm 0, argBytes sevm 1,
        BeaconDeposit.le64 (v / BeaconDeposit.oneGwei), argBytes sevm 2,
        BeaconDeposit.le64 (solAcc stor).count⟩ := by
      rw [hpkB, hwcB, hsgB]
      show bodyEvent sevm pP wP sP a w = _
      unfold bodyEvent
      rw [hamt]
      rfl
    rw [hev]
    rfl


/-! ## The frame -/

/-- **The deployed runtime refines the model (B3, safety).**  For every successful frame
execution of the deployed bytes from a frame start (empty stack and memory), over rules without
state gas or access list (every historical fork),
with the precompile premises and the storage abstraction `SolInv` for a history:

* if the selector is `deposit`'s, the calldata is `DepositDecodable`, the model deposit on the
  arguments the deployed decoder reads returns `.ok (s', ev)`, the contract's new storage
  abstracts to `s'` and satisfies `SolInv` for the history extended by the model's node, it
  differs from the old one exactly at the count slot and one branch slot, every other account's
  storage is unchanged, and exactly the model's `DepositEvent` log is appended;
* otherwise every storage map and the log list are unchanged. -/
theorem deposit_frame_refinesH {sevm : Sevm} {pre post : Devm} {history : List B256}
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsha : ShaReadyH sevm pre)
    (hinv : SolInv (Devm.getStor pre sevm.currentTarget) history)
    (exc : Exec 0 sevm pre (.ok post)) :
    (Sevm.selector sevm = BeaconDeposit.depositSelector →
      DepositDecodable sevm ∧ ∃ s' ev,
        BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor pre sevm.currentTarget))
          (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm)
          sevm.value.toNat = .ok (s', ev) ∧
        solAcc (Devm.getStor post sevm.currentTarget) = s' ∧
        SolInv (Devm.getStor post sevm.currentTarget)
          (history ++ [BeaconDeposit.depositDataNode Bytes.sha256 (argBytes sevm 0)
            (argBytes sevm 1) (argBytes sevm 2) ev.amount]) ∧
        (∃ h v, h < 32 ∧ Devm.getStor post sevm.currentTarget =
          ((Devm.getStor pre sevm.currentTarget).set solCountSlot (1 + bodyCount sevm pre)).set
            (solBranchSlot h) v) ∧
        (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
        post.logs = pre.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev]) ∧
    (Sevm.selector sevm ≠ BeaconDeposit.depositSelector →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs) := by
  obtain ⟨f, hf, run⟩ := lift_sound_noStateGas cert_check hcode hsg exc
  have hf0 : prog[0]? = some t_0000_c0 := rfl
  rw [hf0] at hf
  cases hf
  rw [St.self hstack hmem] at run
  obtain ⟨k, G1, g, hk, hk32, hg, run⟩ := safe_dispatch run
  have hworld : ∀ x, Devm.getStor (St pre [Sevm.selector sevm] mem0 G1) x = Devm.getStor pre x :=
    fun _ => rfl
  by_cases hsel : Sevm.selector sevm = BeaconDeposit.depositSelector
  · refine ⟨fun _ => ?_, fun h => absurd hsel h⟩
    have hk' : k = 32 := hk32.mpr hsel
    subst hk'
    have hg32 : g = t_00a4_c32 := by
      have : prog[32]? = some t_00a4_c32 := rfl
      rw [this] at hg; exact (Option.some.inj hg).symm
    subst hg32
    exact deposit_routeH hsg hbal hcd hsha hinv run
  · refine ⟨fun h => absurd h hsel, fun _ => ?_⟩
    have hkv : k ∈ viewSet := by
      have : k ≠ 32 := fun h => hsel (hk32.mp h)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      simp only [viewSet, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hw := view_worldH hsg hkv hg run
    exact ⟨fun x => (congrFun hw.1 x).trans (hworld x), hw.2⟩


/-! ## Frame tails -/

/-- One historical frame extends the storage abstraction by its accepted nodes. -/
theorem frame_solInvH {sevm : Sevm} {pre post : Devm} {history : List B256}
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsha : ShaReadyH sevm pre)
    (hinv : SolInv (Devm.getStor pre sevm.currentTarget) history)
    (exc : Exec 0 sevm pre (.ok post)) :
    SolInv (Devm.getStor post sevm.currentTarget) (history ++ frameAccepted sevm) := by
  have hr := deposit_frame_refinesH hcode hsg hbal hcd hstack hmem hsha hinv exc
  unfold frameAccepted
  by_cases hsel : Sevm.selector sevm = BeaconDeposit.depositSelector
  · rw [ite_eq_left hsel]
    obtain ⟨-, s', ev, hOk, hacc, hinv', -⟩ := hr.1 hsel
    refine ⟨hinv'.1, ?_⟩
    show BeaconDeposit.Inv Bytes.sha256 _ _
    rw [hacc]
    exact BeaconDeposit.deposit_inv Bytes.sha256 _ _ _ _ _ _ _ _ _ hinv.2 hOk
  · rw [ite_eq_right hsel, List.append_nil, (hr.2 hsel).1]
    exact hinv

/-- The event segment's mandatory `LOG1` forces a non-static frame on any successful run. -/
theorem event_suffix_nonstaticH {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.Run prog sevm pre t_071c_c4 out) : sevm.isStatic = false := by
  cases static : sevm.isStatic with
  | false => rfl
  | true =>
    unfold t_071c_c4 at run
    cases run with
    | dest burn run =>
      iterate 22 (cases run; rename_i _ step run)
      cases run with
      | next step run =>
        obtain ⟨pc, logRun⟩ := of_run_reg step
        exact (Rinst.log_not_ok_of_static static logRun).elim

/-- A successful deployed deposit cannot run in a static historical frame. -/
theorem successful_deposit_not_staticH {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (run : Exec 0 sevm pre (.ok post)) : sevm.isStatic = false := by
  obtain ⟨f, hf, lifted⟩ := lift_sound_noStateGas cert_check hcode hsg run
  have hf0 : prog[0]? = some t_0000_c0 := rfl
  rw [hf0] at hf
  cases hf
  rw [St.self hstack hmem] at lifted
  obtain ⟨k, G1, g, _, hk32, hg, lifted⟩ := safe_dispatch lifted
  have hk : k = 32 := hk32.mpr hsel
  subst k
  have hg32 : g = t_00a4_c32 := by
    have heq : prog[32]? = some t_00a4_c32 := rfl
    rw [heq] at hg
    exact (Option.some.inj hg).symm
  subst g
  obtain ⟨_, G2, d, body, _, _⟩ := safe_decoder hcd lifted
  obtain ⟨_, _, _, _, _, _, b1, M1, G3, _, memory, body⟩ := safe_guardsH hcd hbal body
  obtain ⟨b2, M2, G4, _, _, body⟩ := safe_event memory body
  exact event_suffix_nonstaticH body

/-- Static historical executions of the deployed deposit selector accept nothing. -/
theorem frameAccepted_eq_nil_of_staticH {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm pre (.ok post)) : frameAccepted sevm = [] := by
  unfold frameAccepted
  split
  next selected =>
    have impossible := successful_deposit_not_staticH hcode hsg hbal hcd hstack hmem selected run
    rw [static] at impossible
    cases impossible
  next => rfl

end Blanc.Lift.BeaconDeposit
