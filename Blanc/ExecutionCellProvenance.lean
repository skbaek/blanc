import Blanc.LockExclusion
import Blanc.ExecutionOccurrence
import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionAccountingPositional
import Blanc.ExecutionNoDelSafeHistory

/-!
# Storage-cell provenance over the raw node chronology

Contract-neutral provenance for one persistent storage cell `(wa, k)` along
`Exec.rawNodes`: `CellProv wa k init nodes v` says the cell holds `v` after
the listed nodes either because it still holds its entry value `init`, or
because some listed node executed a successful `SSTORE` of `v` to `(wa, k)`.

`CellProv.mono_left`, `CellProv.mono_right` and `CellProv.trans` assemble
provenance across concatenated chronologies; `CellProv.of_replayCell` turns
chronological replay of a retained write list into provenance.  The per-step
facts are state-gas-absence twins of the covered-fork storage lemmas
(`Evm.step_cont_getStor_get`, `Evm.step_spawn_enter_getStor`), proved in a
different shape with `Xinst.step_done_getStor_noStateGas` /
`Xinst.step_shapeNoStateGas` in place of coverage.  `successfulSstore?_sound_raw`
is the raw-chronology soundness of the SSTORE recognizer.  The level-zero
results are `Exec.rawNodes_getCode` and
`Exec.rawNodes_cellProv_noStateGas`, by induction on the run.

Reused (not copied): `Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix`,
`Exec.retainedNodes_sublist_rawNodes`, `Exec.rawFrameRoots_codePreserve`,
`ParentPrefix.codePreserve`, `Evm.step_spawn_child`,
`Evm.step_spawn_child_fork_noStateGas`,
`Evm.step_spawn_child_world_noStateGas`,
`Evm.step_spawn_rollback_getStor_noStateGas`,
`Evm.step_doneOk_getStor_eq`, `Xinst.step_done_getStor_noStateGas`,
`Xinst.storageReplay_some_of_body_noStateGas`,
`Exec.storageReplay_committedPost_noStateGas`,
`Exec.NinstOccurrence.toSuccessfulSstore`, `List.split_append_cons`.
-/

namespace Blanc

open Jaune

-- Compatibility names, as in `Blanc/ExecutionOccurrence.lean`: `Blanc.Exec.Deriv`
-- is the `Jaune.*` declaration itself, so Blanc-local extensions such as
-- `Exec.Deriv.successfulSstore?` resolve here.
namespace Exec
export Jaune.Exec (Deriv)
end Exec

namespace Exec.Deriv
export Jaune.Exec.Deriv (ParentStep ParentPrefix)
end Exec.Deriv

/-- Storage-cell provenance: after `nodes`, the cell `(wa, k)` holds `v`
because it kept its entry value `init`, or because a listed node ran a
successful `SSTORE` of `v` to `(wa, k)`. -/
def CellProv (wa : Adr) (k init : B256) (nodes : List Exec.Deriv)
    (v : B256) : Prop :=
  v = init ∨ ∃ b₁ b₂ : List Exec.Deriv, ∃ (m : Exec.Deriv)
    (w : Exec.StorageWrite),
    nodes = b₁ ++ m :: b₂ ∧ Exec.Deriv.successfulSstore? m = some w ∧
      w.owner = wa ∧ w.key = k ∧ w.value = v

/-- Provenance witnessed in the left part persists across a right extension. -/
theorem CellProv.mono_left {wa : Adr} {k init : B256}
    {L : List Exec.Deriv} {v : B256} (h : CellProv wa k init L v)
    (L' : List Exec.Deriv) : CellProv wa k init (L ++ L') v := by
  rcases h with rfl | ⟨b₁, b₂, m, w, hs, hss, ho, hk, hv⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨b₁, b₂ ++ L', m, w,
      by rw [hs, List.append_assoc, List.cons_append], hss, ho, hk, hv⟩

/-- Provenance witnessed in the right part lifts across a left extension. -/
theorem CellProv.mono_right {wa : Adr} {k init : B256}
    {L' : List Exec.Deriv} {v : B256} (h : CellProv wa k init L' v)
    (L : List Exec.Deriv) : CellProv wa k init (L ++ L') v := by
  rcases h with rfl | ⟨b₁, b₂, m, w, hs, hss, ho, hk, hv⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨L ++ b₁, b₂, m, w, by rw [hs, ← List.append_assoc],
      hss, ho, hk, hv⟩

/-- Provenance chains across concatenated chronologies through the middle value. -/
theorem CellProv.trans {wa : Adr} {k init mid : B256}
    {L L' : List Exec.Deriv} {v : B256}
    (h1 : CellProv wa k init L mid) (h2 : CellProv wa k mid L' v) :
    CellProv wa k init (L ++ L') v := by
  rcases h2 with rfl | ⟨b₁, b₂, m, w, hs, hss, ho, hk, hv⟩
  · exact h1.mono_left L'
  · exact Or.inr ⟨L ++ b₁, b₂, m, w, by rw [hs, ← List.append_assoc],
      hss, ho, hk, hv⟩

/-- Folding replay over a match-free write list leaves the cell unchanged. -/
private theorem foldl_replay_eq_of_nomatch {wa : Adr} {k : B256} :
    ∀ (writes : List Exec.StorageWrite) (init : B256),
    (∀ w ∈ writes, w.matches wa k ≠ true) →
    writes.foldl
        (fun cell w => if w.matches wa k then w.value else cell) init =
      init := by
  intro writes
  induction writes with
  | nil => intro init _; rfl
  | cons w ws ih =>
      intro init h
      simp only [List.foldl_cons, h w (List.mem_cons_self ..)]
      exact ih init (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A write list with a match has a last matching write, with no match after it. -/
private theorem exists_last_match' {wa : Adr} {k : B256}
    {writes : List Exec.StorageWrite}
    (hex : ∃ w ∈ writes, w.matches wa k = true) :
    ∃ pre ev suf, writes = pre ++ ev :: suf ∧ ev.matches wa k = true ∧
      ∀ later ∈ suf, later.matches wa k ≠ true := by
  induction writes with
  | nil =>
      rcases hex with ⟨_, hmem, _⟩
      exact (List.not_mem_nil hmem).elim
  | cons w ws ih =>
      by_cases hmatch : w.matches wa k = true
      · by_cases hlater : ∃ x ∈ ws, x.matches wa k = true
        · rcases ih hlater with ⟨pre, ev, suf, hs, hm, hl⟩
          exact ⟨w :: pre, ev, suf, by rw [hs, List.cons_append], hm, hl⟩
        · exact ⟨[], w, ws, rfl, hmatch,
            fun later hl hc => hlater ⟨later, hl, hc⟩⟩
      · rcases hex with ⟨_, hmem, hm⟩
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact (hmatch hm).elim
        · rcases ih ⟨_, hmem, hm⟩ with ⟨pre, ev, suf, hs, hm', hl⟩
          exact ⟨w :: pre, ev, suf, by rw [hs, List.cons_append], hm', hl⟩

/-- A replayCell value is the initial value or some matching write's value:
chronological replay of a retained write list is cell provenance. -/
theorem CellProv.of_replayCell {wa : Adr} {k init : B256}
    {nodes : List Exec.Deriv} {v : B256}
    {writes : List Exec.StorageWrite}
    (hreplay : Exec.StorageWrite.replayCell wa k init writes = v)
    (mem : ∀ w ∈ writes, ∃ m ∈ nodes,
      Exec.Deriv.successfulSstore? m = some w) :
    CellProv wa k init nodes v := by
  by_cases hex : ∃ w ∈ writes, w.matches wa k = true
  · rcases exists_last_match' hex with
      ⟨pre, ev, suf, hsplit, hmatch, hlast⟩
    have hval : v = ev.value := by
      rw [← hreplay, hsplit]
      unfold Exec.StorageWrite.replayCell
      rw [List.foldl_append]
      simp only [List.foldl_cons, hmatch, ite_true]
      exact foldl_replay_eq_of_nomatch suf ev.value hlast
    have hmem : ev ∈ writes := by
      rw [hsplit]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    rcases mem ev hmem with ⟨m, hmn, hss⟩
    rcases List.append_of_mem hmn with ⟨b₁, b₂, hsplitm⟩
    have hoe := Exec.StorageWrite.matches_eq_true.mp hmatch
    exact Or.inr ⟨b₁, b₂, m, ev, hsplitm, hss, hoe.1, hoe.2,
      hval.symm⟩
  · have hnone : ∀ w ∈ writes, w.matches wa k ≠ true := by
      intro w hw hc
      exact hex ⟨w, hw, hc⟩
    have hinit : v = init := by
      rw [← hreplay]
      unfold Exec.StorageWrite.replayCell
      exact foldl_replay_eq_of_nomatch writes init hnone
    exact Or.inl hinit

/-! ## State-gas-absence twins of the per-step storage facts -/

/-- The executable-instruction arm under state-gas absence: the instruction
runs the actual completed execution without state gas, so the post storage
is the executed storage.  Takes the `Ninst.step` equation (as in the
original's `nstep`) rather than a run proof. -/
private theorem Ninst.exec_getStor_get_noStateGas {pc pc' : Nat} {sevm : Sevm}
    {pre post : Devm} {executable : Xinst}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (nstep : Ninst.step ⟨pc, sevm, pre⟩ (.exec executable) = .cont pc' post)
    {owner : Adr} {key : B256} :
    (Devm.getStor post owner).get key = (Devm.getStor pre owner).get key := by
  simp only [Ninst.step_exec, XStep.toStep] at nstep
  cases actual : Xinst.step sevm pre executable with
  | spawn frame resume => rw [actual] at nstep; cases nstep
  | done out =>
      rw [actual] at nstep
      cases out with
      | error error => cases nstep
      | ok actualPost =>
          cases nstep
          exact congrArg (fun storage => storage.get key)
            (Xinst.step_done_getStor_noStateGas hsg actual owner)

/-- State-gas-absence twin of `Evm.step_cont_getStor_get`: a successful
non-matching driver step preserves the observed cell.  The executable arm
is factored through the helper above, which runs the `Xinst.step_done`
analysis under `Xinst.step_done_getStor_noStateGas` instead of coverage. -/
theorem Evm.step_cont_getStor_get_noStateGas {pc pc' : Nat} {sevm : Sevm}
    {pre post : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    {owner : Adr} {key : B256}
    (notStore : sevm.currentTarget = owner →
      Ninst.At sevm.code pc (.reg .sstore) → pre.stack.head? ≠ some key) :
    (Devm.getStor post owner).get key = (Devm.getStor pre owner).get key := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      unfold Evm.step at step
      rw [decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | last last =>
          rw [Evm.step_last decoded] at step
          cases step
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
          | error error =>
              rw [jumpEq] at step
              cases step
          | ok pair =>
              rcases pair with ⟨actualPc, actualPost⟩
              rw [jumpEq] at step
              cases step
              have frame := Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ jumpInst
              rw [jumpEq] at frame
              rw [← frame.getStor owner]
      | next instruction =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction =
              .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          cases instruction with
          | exec executable =>
              exact Ninst.exec_getStor_get_noStateGas hsg nstep
          | reg regular =>
              have run : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
                ((Step.run_ofExecution (xl := (.none : Xlot))).mp nrun).2.symm
              by_cases store : regular = .sstore
              · subst regular
                by_cases own : sevm.currentTarget = owner
                · subst owner
                  have sstoreRun : Ninst.Run sevm pre Ninst.sstore post :=
                    ⟨.none, trivial, pc, nrun⟩
                  rcases of_run_sstore sstoreRun with ⟨written, value, popped⟩
                  rcases pref_of_split popped with ⟨rest, stackEq⟩
                  rw [sstore_getStor_set sstoreRun ⟨rest, stackEq⟩]
                  apply Stor.get_set_ne
                  intro same
                  apply notStore rfl decoded
                  simp only [Split, List.cons_append, List.nil_append] at stackEq
                  rw [stackEq, same]
                  rfl
                · rw [sstore_preserves_getStor_ne run own]
              · rw [← congrFun (Rinst.preserves_stor store run) owner]
          | push bytes bound =>
              exact congrArg (fun storage => storage.get key) ((Ninst.push_instructionFrame_effectRec
                (hxs := bound) (xl := .none) trivial nrun).getStor owner).symm
          | dupn imm =>
              exact congrArg (fun storage => storage.get key) ((Ninst.dupn_instructionFrame_effectRec
                (xl := .none) trivial nrun).getStor owner).symm
          | swapn imm =>
              exact congrArg (fun storage => storage.get key) ((Ninst.swapn_instructionFrame_effectRec
                (xl := .none) trivial nrun).getStor owner).symm
          | exchange imm =>
              exact congrArg (fun storage => storage.get key) ((Ninst.exchange_instructionFrame_effectRec
                (xl := .none) trivial nrun).getStor owner).symm

/-- State-gas-absence twin of `Evm.step_spawn_enter_getStor`: the entered
child opens on the spawning world's storage at every code-bearing owner.
Corollary of `Evm.step_spawn_child_world_noStateGas` (shared library first);
the code-nonempty premise is the `toList` form used by the L0 induction. -/
theorem Evm.step_spawn_enter_getStor_noStateGas {pc pc' : Nat} {sevm : Sevm}
    {pre : Devm} {frame : Frame} {resume : Resume} {child : Evm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run child)
    {owner : Adr} (hcode : (pre.getCode owner).toList ≠ []) :
    Devm.getStor child.dyna owner = Devm.getStor pre owner := by
  have hne : pre.getCode owner ≠ .empty := by
    intro hempty
    apply hcode
    rw [hempty, ByteArray.toList_empty]
  have hstor := (Evm.step_spawn_child_world_noStateGas hsg step enter hne).1
  simpa only [Devm.getStor, Devm.getAcct, State.getStor] using hstor

/-! ## Small storage twins for the upper levels -/

/-- Erasing a different account keeps the observed storage. -/
private theorem destroyAccount_getStor_ne {w : State} {x a : Adr}
    (hne : x ≠ a) :
    (destroyAccount w x).getStor a = w.getStor a := by
  unfold destroyAccount State.getStor
  exact congrArg Acct.stor (State.get_erase_ne (a := x) (b := a) (Ne.symm hne))

/-- Storage twin of `sweepTouchedAccounts_getCode_of_nonempty`: removing
touched empty accounts keeps the storage of a code-bearing owner. -/
theorem sweepTouchedAccounts_getStor_of_nonempty (rules : ForkRules)
    (addresses : List Adr) {state : State} {a : Adr}
    (h : (state.getCode a).toList ≠ []) :
    (sweepTouchedAccounts rules addresses state).getStor a =
      state.getStor a := by
  unfold sweepTouchedAccounts
  split
  · induction addresses generalizing state with
    | nil => rfl
    | cons x xs ih =>
      rw [List.foldl_cons]
      split
      · rename_i hempty
        have hne : x ≠ a := by
          rintro rfl
          apply h
          have hsize : (state.getCode x).size = 0 := hempty.2.1
          rw [ByteArray.size_eq_length_toList] at hsize
          exact List.eq_nil_of_length_eq_zero hsize
        have hcode := ExecutionTrace.destroyAccount_getCode_ne (w := state) hne
        have hstor := destroyAccount_getStor_ne (w := state) hne
        rw [ih (by rw [hcode]; exact h), hstor]
      · exact ih h
  · rfl

/-- One balance credit keeps a protected owner's storage: the normalization
arm of `getStor_addBal` needs the credited account to empty, which a
protected account never does. -/
private theorem addBal_getStor_of_protected {s : State} {b : Adr} {v : B256}
    {a : Adr} (hp : State.Protected s a) :
    (s.addBal b v).getStor a = s.getStor a := by
  rw [getStor_addBal]
  split_ifs with hcond
  · obtain ⟨heq, hE⟩ := hcond
    exfalso
    subst heq
    rcases hp with hn | hc
    · exact hn hE.2.1
    · exact hc hE.1
  · rfl

/-- One balance credit keeps a code-bearing owner's storage. -/
private theorem addBal_getStor_of_codenonempty {s : State} {b : Adr}
    {v : B256} {a : Adr} (h : (s.getCode a).toList ≠ []) :
    (s.addBal b v).getStor a = s.getStor a :=
  addBal_getStor_of_protected (State.Protected.of_code_ne_nil h)

/-- Storage twin of `payRewards_getCode`: block rewards only credit balances,
so a protected owner's storage is unchanged. -/
theorem payRewards_getStor (pow : PowRules) (number : Nat) (coinbase : Adr)
    (ommers : List Header) (st : State) {a : Adr}
    (h : (st.getCode a).toList ≠ []) :
    (payRewards pow number coinbase ommers st).getStor a = st.getStor a := by
  unfold payRewards
  suffices hfold : ∀ (os : List Header) (s : State),
      (s.getCode a).toList ≠ [] →
      (os.foldl (fun acc ommer => acc.addBal ommer.coinbase
        ((8 + ommer.number - number) * pow.blockReward / 8).toB256) s).getStor a =
        s.getStor a by
    refine (hfold ommers _ ?_).trans (addBal_getStor_of_codenonempty h)
    rw [State.addBal_getCode]
    exact h
  intro os s hs
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
      rw [List.foldl_cons]
      exact (ih _ (by rw [State.addBal_getCode]; exact hs)).trans
        (addBal_getStor_of_codenonempty hs)

/-- Storage twin of `messageCallExecutionMessage_getCode`: resolving a call
message's code address touches no storage. -/
theorem ExecutionTrace.messageCallExecutionMessage_getStor (msg : Msg) (a : Adr) :
    (ExecutionTrace.messageCallExecutionMessage msg).benv.state.getStor a =
      msg.benv.state.getStor a := by
  unfold ExecutionTrace.messageCallExecutionMessage Msg.resolveCodeDelegation
  split
  · rfl
  · rfl

/-! ## Raw-chronology soundness of the SSTORE recognizer -/

/-- A node whose recognizer fires is the node of a successful-SSTORE
occurrence.  Restructured from `successfulSstore?_sound`: the occurrence is
built directly at the raw member node (no retained detour), and only the
storage-write equation is concluded (no `Retained` tail). -/
theorem Exec.Deriv.successfulSstore?_sound_raw {G m : Exec.Deriv}
    {w : Exec.StorageWrite}
    (hmem : m ∈ Exec.rawNodes G.exc)
    (found : Exec.Deriv.successfulSstore? m = some w) :
    ∃ write : Exec.SuccessfulSstoreOccurrence G,
      write.storageWrite = w := by
  rcases m with ⟨pc, sevm, pre, out, run⟩
  cases run with
  | halt hstep =>
      simp only [successfulSstore?, reduceCtorEq] at found
  | doneErr hstep henter hresume =>
      simp only [successfulSstore?, reduceCtorEq] at found
  | doneOk hstep henter hresume next =>
      simp only [successfulSstore?, reduceCtorEq] at found
  | runErr hstep henter child hresume =>
      simp only [successfulSstore?, reduceCtorEq] at found
  | runOk hstep henter child hresume next =>
      simp only [successfulSstore?, reduceCtorEq] at found
  | cont hstep next =>
      cases hget : Evm.getInst ⟨pc, sevm, pre⟩ with
      | none =>
          simp only [successfulSstore?, hget, reduceCtorEq] at found
      | some instruction =>
          cases instruction with
          | jump jumpInst =>
              simp only [successfulSstore?, hget, reduceCtorEq] at found
          | last lastInst =>
              simp only [successfulSstore?, hget, reduceCtorEq] at found
          | next instruction =>
              cases instruction with
              | exec executable =>
                  simp only [successfulSstore?, hget, reduceCtorEq] at found
              | push arg next =>
                  simp only [successfulSstore?, hget, reduceCtorEq] at found
              | dupn n =>
                  simp only [successfulSstore?, hget, reduceCtorEq] at found
              | swapn n =>
                  simp only [successfulSstore?, hget, reduceCtorEq] at found
              | exchange =>
                  simp only [successfulSstore?, hget, reduceCtorEq] at found
              | reg regular =>
                  cases regular <;>
                    simp only [successfulSstore?, hget, reduceCtorEq] at found
                  cases hstack : pre.stack with
                  | nil =>
                      simp only [hstack, reduceCtorEq] at found
                  | cons key rest =>
                      cases rest with
                      | nil =>
                          simp only [hstack, reduceCtorEq] at found
                      | cons value tail =>
                          simp only [hstack, Option.some.injEq] at found
                          subst w
                          let occurrence : Exec.NinstOccurrence G :=
                            { node := ⟨pc, sevm, pre, out, .cont hstep next⟩,
                              instruction := .reg .sstore,
                              slot := .none,
                              stepResult := .ok _,
                              reached := hmem,
                              decoded := hget,
                              filled := trivial,
                              stepRun := by
                                unfold Ninst.StepRun
                                rw [← Evm.step_next hget, hstep]
                                exact ⟨rfl, rfl⟩ }
                          rcases occurrence.toSuccessfulSstore rfl rfl with
                            ⟨write, hwrite⟩
                          refine ⟨write, ?_⟩
                          have known : [key, value] <<+ pre.stack := by
                            rw [hstack]
                            exact ⟨tail, rfl⟩
                          have popped := write.popped
                          rw [hwrite] at popped
                          rcases of_cons_cons_pref_of_cons_cons_pref known
                            (pref_of_split popped) with ⟨hkey, hvalue, _⟩
                          have keyEq : write.key = key := by
                            simpa only
                              [Exec.SuccessfulSstoreOccurrence.storageWrite]
                              using hkey.symm
                          have valueEq : write.value = value := by
                            simpa only
                              [Exec.SuccessfulSstoreOccurrence.storageWrite]
                              using hvalue.symm
                          ext
                          · unfold Exec.SuccessfulSstoreOccurrence.storageWrite
                            rw [hwrite]
                          · unfold Exec.SuccessfulSstoreOccurrence.storageWrite
                            rw [hwrite]
                          · simp only [Exec.SuccessfulSstoreOccurrence.storageWrite,
                              hwrite]
                            exact keyEq
                          · simp only [Exec.SuccessfulSstoreOccurrence.storageWrite,
                              hwrite]
                            exact valueEq

/-! ## Level zero: one run -/

/-- Every raw node of a run sees its entry code at a code-bearing owner:
membership is a same-frame-or-descendant position under some raw frame root
(`Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix`), roots keep entry code
(`Exec.rawFrameRoots_codePreserve`), prefixes keep code
(`ParentPrefix.codePreserve`). -/
theorem Exec.rawNodes_getCode {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out)
    {wa : Adr} {C : ByteArray} (hC : pre.getCode wa = C)
    (hCne : C.toList ≠ []) (n : Exec.Deriv)
    (hn : n ∈ Exec.rawNodes run) : n.devm.getCode wa = C := by
  obtain ⟨R, hR, hp⟩ :=
    (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run n).mp hn
  have hRcode : R.devm.getCode wa = C :=
    (Exec.rawFrameRoots_codePreserve run wa (by rw [hC]; exact hCne) R hR).trans
      hC
  have hRne : (R.devm.getCode wa).toList ≠ [] := by
    rw [hRcode]
    exact hCne
  exact (Blanc.Exec.Deriv.ParentPrefix.codePreserve hp wa hRne).trans hRcode

/-- Field equations of a fired recognizer at a known continuation node:
stack shape, written key and value, owner, and the decode equation. -/
private theorem sstore_fields_of_found {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} {run : Exec pc sevm pre out}
    {w : Exec.StorageWrite}
    (hwss : Exec.Deriv.successfulSstore?
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) = some w) :
    ∃ key value rest, pre.stack = key :: value :: rest ∧ w.key = key ∧
      w.value = value ∧ w.owner = sevm.currentTarget ∧
      Evm.getInst ⟨pc, sevm, pre⟩ = some (.next (.reg .sstore)) := by
  cases run with
  | halt hstep =>
      simp only [Exec.Deriv.successfulSstore?, reduceCtorEq] at hwss
  | doneErr hstep henter hresume =>
      simp only [Exec.Deriv.successfulSstore?, reduceCtorEq] at hwss
  | doneOk hstep henter hresume next =>
      simp only [Exec.Deriv.successfulSstore?, reduceCtorEq] at hwss
  | runErr hstep henter child hresume =>
      simp only [Exec.Deriv.successfulSstore?, reduceCtorEq] at hwss
  | runOk hstep henter child hresume next =>
      simp only [Exec.Deriv.successfulSstore?, reduceCtorEq] at hwss
  | cont hstep next =>
      cases hget : Evm.getInst ⟨pc, sevm, pre⟩ with
      | none =>
          simp only [Exec.Deriv.successfulSstore?, hget, reduceCtorEq] at hwss
      | some instruction =>
          cases instruction with
          | jump jumpInst =>
              simp only [Exec.Deriv.successfulSstore?, hget, reduceCtorEq] at hwss
          | last lastInst =>
              simp only [Exec.Deriv.successfulSstore?, hget, reduceCtorEq] at hwss
          | next instruction =>
              cases instruction with
              | exec executable =>
                  simp only [Exec.Deriv.successfulSstore?, hget,
                    reduceCtorEq] at hwss
              | push arg next =>
                  simp only [Exec.Deriv.successfulSstore?, hget,
                    reduceCtorEq] at hwss
              | dupn n =>
                  simp only [Exec.Deriv.successfulSstore?, hget,
                    reduceCtorEq] at hwss
              | swapn n =>
                  simp only [Exec.Deriv.successfulSstore?, hget,
                    reduceCtorEq] at hwss
              | exchange =>
                  simp only [Exec.Deriv.successfulSstore?, hget,
                    reduceCtorEq] at hwss
              | reg regular =>
                  cases regular <;>
                    simp only [Exec.Deriv.successfulSstore?, hget,
                      reduceCtorEq] at hwss
                  cases hstack : pre.stack with
                  | nil =>
                      simp only [hstack, reduceCtorEq] at hwss
                  | cons key rest =>
                      cases rest with
                      | nil =>
                          simp only [hstack, reduceCtorEq] at hwss
                      | cons value tail =>
                          simp only [hstack, Option.some.injEq] at hwss
                          exact ⟨key, value, tail, rfl, by rw [← hwss],
                            by rw [← hwss], by rw [← hwss], rfl⟩

/-- Every raw node of a run inherits cell provenance from entry: the
induction is on the run, generalizing the code image (resumed frames need
their own), the fork absence, and the positional split.  Continuation nodes
split on whether they fire a matching `SSTORE` (event plus transitivity, or
the no-state-gas continuation twin plus monotonicity); entered children
open on the spawning storage (the no-state-gas enter twin) with code from
`Evm.step_spawn_child`; resumes use rollback, done-completion, or replay of
the settlement-retained writes (`CellProv.of_replayCell`). -/
theorem Exec.rawNodes_cellProv_noStateGas {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out) (k : B256)
    (hsg : sevm.benvStat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : pre.getCode wa = C)
    (hCne : C.toList ≠ [])
    {before : List Exec.Deriv} {n : Exec.Deriv} {after : List Exec.Deriv}
    (split : Exec.rawNodes run = before ++ n :: after) :
    CellProv wa k ((Devm.getStor pre wa).get k) before
      ((Devm.getStor n.devm wa).get k) := by
  induction run generalizing C hCne before n after with
  | @halt pc sevm pre out hstep =>
      simp only [Exec.rawNodes] at split
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          exact Or.inl rfl
      | cons b bs =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨-, hcon⟩ := split
          have hlen := congrArg List.length hcon
          simp only [List.length_nil, List.length_append,
            List.length_cons] at hlen
          omega
  | @doneErr pc sevm pre f rsm pc' r e hstep henter hresume =>
      simp only [Exec.rawNodes] at split
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          exact Or.inl rfl
      | cons b bs =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨-, hcon⟩ := split
          have hlen := congrArg List.length hcon
          simp only [List.length_nil, List.length_append,
            List.length_cons] at hlen
          omega
  | @cont pc sevm pre pc' post out hstep next ihNext =>
      simp only [Exec.rawNodes] at split
      have hprene : (pre.getCode wa).toList ≠ [] := by
        rw [hC]
        exact hCne
      have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve
        (.cont hstep next) wa hprene
      have hCne_next : (post.getCode wa).toList ≠ [] := by
        rw [codeEq]
        exact hprene
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          exact Or.inl rfl
      | cons r rest =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, hnext⟩ := split
          by_cases hmatch : ∃ w,
              Exec.Deriv.successfulSstore?
                (⟨pc, sevm, pre, out, .cont hstep next⟩ : Exec.Deriv) =
                some w ∧ w.owner = wa ∧ w.key = k
          · rcases hmatch with ⟨w, hwss, hown, hkey⟩
            rcases sstore_fields_of_found hwss with
              ⟨skey, svalue, srest, hstack, hkey', hvalue', howner, hget⟩
            have htgt : sevm.currentTarget = wa :=
              howner.symm.trans hown
            have nstep : Ninst.step ⟨pc, sevm, pre⟩ (.reg .sstore) =
                .cont pc' post := by
              rw [← Evm.step_next hget]
              exact hstep
            have nrun : Ninst.StepRun pc sevm pre (.reg .sstore) .none
                (.ok post) := by
              unfold Ninst.StepRun
              rw [nstep]
              exact ⟨rfl, rfl⟩
            have sstoreRun : Ninst.Run sevm pre Ninst.sstore post :=
              ⟨.none, trivial, pc, nrun⟩
            rcases of_run_sstore sstoreRun with ⟨written, value, popped⟩
            rcases pref_of_split popped with ⟨prest, stackEq⟩
            have known : [skey, svalue] <<+ pre.stack := by
              rw [hstack]
              exact ⟨srest, rfl⟩
            rcases of_cons_cons_pref_of_cons_cons_pref known
              (pref_of_split popped) with ⟨hkeq, hveq, _⟩
            have hpost : (Devm.getStor post wa).get k =
                w.value := by
              rw [← htgt, sstore_getStor_set sstoreRun ⟨prest, stackEq⟩,
                ← hkeq, ← hkey', hkey, ← hveq, ← hvalue',
                Stor.get_set_self]
            have hev : CellProv wa k
                ((Devm.getStor pre wa).get k)
                [⟨pc, sevm, pre, out, .cont hstep next⟩]
                ((Devm.getStor post wa).get k) :=
              Or.inr ⟨[], [],
                ⟨pc, sevm, pre, out, .cont hstep next⟩, w, rfl, hwss, hown,
                hkey, hpost.symm⟩
            have htail := ihNext hsg rfl hCne_next hnext
            exact hev.trans htail
          · have hcell : (Devm.getStor post wa).get k =
                (Devm.getStor pre wa).get k := by
              apply Evm.step_cont_getStor_get_noStateGas hsg hstep
              intro htgt hat hhead
              apply hmatch
              have nstep : Ninst.step ⟨pc, sevm, pre⟩ (.reg .sstore) =
                  .cont pc' post := by
                rw [← Evm.step_next hat]
                exact hstep
              have nrun : Ninst.StepRun pc sevm pre (.reg .sstore) .none
                  (.ok post) := by
                unfold Ninst.StepRun
                rw [nstep]
                exact ⟨rfl, rfl⟩
              have sstoreRun : Ninst.Run sevm pre Ninst.sstore post :=
                ⟨.none, trivial, pc, nrun⟩
              rcases of_run_sstore sstoreRun with
                ⟨written, value, popped⟩
              rcases pref_of_split popped with ⟨prest, stackEq⟩
              simp only [Split, List.cons_append,
                List.nil_append] at stackEq
              have hwritten : written = k := by
                rw [stackEq] at hhead
                simp only [List.head?_cons,
                  Option.some.injEq] at hhead
                exact hhead
              have hget : Evm.getInst ⟨pc, sevm, pre⟩ =
                  some (.next (.reg .sstore)) := hat
              have hwit : Exec.Deriv.successfulSstore?
                  (⟨pc, sevm, pre, out, .cont hstep next⟩ : Exec.Deriv) =
                  some ⟨⟨pc, sevm, pre, out, Exec.cont hstep next⟩,
                    sevm.currentTarget, written, value⟩ := by
                simp only [Exec.Deriv.successfulSstore?, hget, stackEq]
              exact ⟨_, hwit, htgt, hwritten⟩
            have htail := ihNext hsg rfl hCne_next hnext
            rw [hcell] at htail
            exact htail.mono_right
              [⟨pc, sevm, pre, out, .cont hstep next⟩]
  | @doneOk pc sevm pre f rsm pc' r post out hstep henter hresume next
      ihNext =>
      simp only [Exec.rawNodes] at split
      have hprene : (pre.getCode wa).toList ≠ [] := by
        rw [hC]
        exact hCne
      have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve
        (.doneOk hstep henter hresume next) wa hprene
      have hCne_next : (post.getCode wa).toList ≠ [] := by
        rw [codeEq]
        exact hprene
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          exact Or.inl rfl
      | cons r rest =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, hnext⟩ := split
          have hcell : (Devm.getStor post wa).get k =
              (Devm.getStor pre wa).get k :=
            congrArg (Stor.get · k) (Evm.step_doneOk_getStor_eq hstep henter
              hresume wa (State.Protected.of_code_ne_nil hprene))
          have htail := ihNext hsg rfl hCne_next hnext
          rw [hcell] at htail
          exact htail.mono_right
            [⟨pc, sevm, pre, out, .doneOk hstep henter hresume next⟩]
  | @runErr pc sevm pre f rsm pc' cev raw e hstep henter child hresume
      ihChild =>
      simp only [Exec.rawNodes] at split
      have hprene : (pre.getCode wa).toList ≠ [] := by
        rw [hC]
        exact hCne
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          exact Or.inl rfl
      | cons r rest =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, hchild⟩ := split
          have hsg_c := Evm.step_spawn_child_fork_noStateGas hstep henter hsg
          have hchildCode : cev.dyna.getCode wa = pre.getCode wa :=
            (Evm.step_spawn_child hstep henter).2.1 wa
          have hC_c : cev.dyna.getCode wa = C := hchildCode.trans hC
          have hchild := ihChild hsg_c hC_c hCne hchild
          have henterStor : (Devm.getStor cev.dyna wa).get k =
              (Devm.getStor pre wa).get k :=
            congrArg (Stor.get · k)
              (Evm.step_spawn_enter_getStor_noStateGas hsg hstep henter
                hprene)
          rw [henterStor] at hchild
          exact hchild.mono_right
            [⟨pc, sevm, pre, Except.error e,
              .runErr hstep henter child hresume⟩]
  | @runOk pc sevm pre frame resume pc' childEvm raw post out hstep henter
      child hresume next ihChild ihNext =>
      simp only [Exec.rawNodes] at split
      have hprene : (pre.getCode wa).toList ≠ [] := by
        rw [hC]
        exact hCne
      have hsg_c := Evm.step_spawn_child_fork_noStateGas hstep henter hsg
      have hchildCode : childEvm.dyna.getCode wa = pre.getCode wa :=
        (Evm.step_spawn_child hstep henter).2.1 wa
      have hC_c : childEvm.dyna.getCode wa = C := hchildCode.trans hC
      have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve
        (.runOk hstep henter child hresume next) wa hprene
      have hCne_next : (post.getCode wa).toList ≠ [] := by
        rw [codeEq]
        exact hprene
      have henterStor : (Devm.getStor childEvm.dyna wa).get k =
          (Devm.getStor pre wa).get k :=
        congrArg (Stor.get · k)
          (Evm.step_spawn_enter_getStor_noStateGas hsg hstep henter hprene)
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          exact Or.inl rfl
      | cons r rest =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, hX⟩ := split
          rcases List.split_append_cons hX with
            ⟨m, hchildSplit, -⟩ | ⟨q, hrest, hnextSplit⟩
          · have hchild := ihChild hsg_c hC_c hCne hchildSplit
            rw [henterStor] at hchild
            exact hchild.mono_right
              [⟨pc, sevm, pre, out,
                .runOk hstep henter child hresume next⟩]
          · rw [hrest]
            have htail := ihNext hsg rfl hCne_next hnextSplit
            have spawnPost : CellProv wa k ((Devm.getStor pre wa).get k)
                ([⟨pc, sevm, pre, out,
                  .runOk hstep henter child hresume next⟩] ++
                  Exec.rawNodes child)
                ((Devm.getStor post wa).get k) := by
              by_cases hsettles : Frame.settlementCommits frame raw = true
              · obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv hstep
                have hreplay :=
                  Xinst.storageReplay_some_of_body_noStateGas spawn
                    (RunFrame.of_run henter) hresume
                    (fun committed =>
                      Exec.storageReplay_committedPost_noStateGas child
                        committed hsg_c) hsg
                simp only [hsettles, ↓reduceIte] at hreplay
                have hcell : (Devm.getStor post wa).get k =
                    Exec.StorageWrite.replayCell wa k
                      ((Devm.getStor pre wa).get k)
                      (Exec.retainedStorageWrites child) :=
                  hreplay.2 wa hprene k
                exact CellProv.of_replayCell hcell.symm fun w hw => by
                  simp only [Exec.retainedStorageWrites,
                    List.mem_filterMap] at hw
                  obtain ⟨mm, hmem, hss⟩ := hw
                  exact ⟨mm, List.mem_append.mpr (Or.inr
                    ((Exec.retainedNodes_sublist_rawNodes child).subset
                      hmem)), hss⟩
              · have hrob : (Devm.getStor post wa).get k =
                    (Devm.getStor pre wa).get k :=
                  congrArg (fun g => (g wa).get k)
                    (Evm.step_spawn_rollback_getStor_noStateGas hsg hstep
                      henter hresume hsettles)
                rw [← hrob]
                exact Or.inl rfl
            exact spawnPost.trans htail

end Blanc
