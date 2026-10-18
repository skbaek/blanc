import Blanc.Lift.Usdc.HistorySlotsCore
import Blanc.ExecutionAccountingPositional

/-!
# The proxy's slot invariant at the three code kinds (U6b2)

The frame handlers of the slot induction (`HistorySlotsCore.lean`) for the frames that run at the
proxy: library frames (`libFrame`), implementation frames (`implFrame`) and proxy frames
(`proxyFrame`, the target handler of `lift_core_sem`).  `usdc_slotsOk` assembles them with the
foreign handlers.

The implementation's end and its spawning nodes keep the invariant by the family laws: the whole
frame laws (`ImplStepLaw`, with the signed family's law a hypothesis), the initializers' revert at a
good ledger, and `rescueERC20`'s model law (`RescueLaw`).  `RescueLaw` says nothing about a successful
`rescueERC20` frame that decodes no external instruction; `RescueQuietEnd` states that case (such a
frame keeps the proxy's storage); it is proved in `HistorySlotsRescue.lean` and taken as a
hypothesis here.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.Token

/-- **The no-call case of `rescueERC20`**: a successful non-static `rescueERC20` frame whose chain
decodes no external instruction keeps the proxy's storage.  (`RescueLaw` covers frames that reach
their `CALL`.) -/
def RescueQuietEnd : Prop :=
  ∀ {P : Adr} {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post)),
    sevm.code = Impl.code → sevm.currentTarget = P → CoveredFork sevm.benvStat.fork →
    sevm.isStatic = false → Blanc.Sevm.selector sevm = rescueSelector →
    State.Protected pre.state P →
    (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) →
    post.state.getStor P = pre.state.getStor P

/-! ## Small facts -/

/-- The library runtime decodes `SSTORE` nowhere (`0x55` does not occur in it). -/
theorem lib_stor_free {pc : Nat} (hat : Ninst.At Lib.code pc (.reg .sstore)) : False :=
  (show (0x55 : UInt8) ∉ Lib.code.data.toList by decide +kernel)
    (ByteArray.sstore_mem_of_getInst hat)

/-- A decoded `rescueERC20` has its selector. -/
theorem decodeCall_rescue {e : Sevm} {t d : Adr} {v : Nat}
    (h : decodeCall e = some (.rescueERC20 t d v)) : Blanc.Sevm.selector e = rescueSelector := by
  obtain ⟨r, hr, hsel, hread, -⟩ := decodeCall_some h
  rw [← hsel]
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | decide | cases hread

/-- A committed book step keeps the ledger good. -/
theorem book_good {P : Adr} {l l' : Ledger} {e : Sevm} (h : (usdcBookS P).step l e = some l')
    (good : l.Good) : l'.Good := by
  rcases usdcBookS_step h with ⟨-, rfl⟩ | ⟨c, -, hs⟩
  · exact good
  · exact Ledger.step_good good hs

/-- The external instructions of an implementation frame: `CALL`, or `DELEGATECALL` to the library. -/
theorem impl_node {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) {f : Frame} {rsm : Resume}
    (spawn : Xinst.step N.sevm N.devm x = .spawn f rsm) :
    x = .call ∨ (x = .delegatecall ∧ ∃ g rest, N.devm.stack = g :: usdcLib.toB256 :: rest) := by
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix certL_check
    (F := ⟨0, sevm, pre, out, run⟩) rfl codeEq fork chain
  have frames := Cursor.framesSat_of_reachable certL_framesSat certL_framesSat_head reach
  have hP := ok.framesSat_exec frames hat
  have kind := ok.execsSatisfy (Cursor.execsSatisfy_of_reachable impl_kinds reach) hat
  cases x with
  | call => exact .inl rfl
  | delegatecall =>
      simp only [implP, beq_iff_eq] at hP
      have hw := ok.stack_const hP
      obtain ⟨g, a, rest, hs⟩ := Xinst.step_delegatecall_spawn_stack spawn
      rw [hs] at hw
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hw
      subst hw
      exact .inr ⟨rfl, g, rest, hs⟩
  | _ => simp only [implKinds, reduceCtorEq, beq_iff_eq, Bool.or_eq_true, or_self] at kind

/-- The whole-frame keeping of a successful implementation frame: the ledger good, the proxy's
slots kept and the support kept at its end and at every external node. -/
def ImplKeeps (P : Adr) (U : Key → Prop) {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) : Prop :=
  ((ledger U (post.state.getStor P)).Good ∧
      (post.state.getStor P).get implSlot = (pre.state.getStor P).get implSlot ∧
      (post.state.getStor P).get adminSlot = (pre.state.getStor P).get adminSlot ∧
      SlotFootprint.Support Key.slot fixedSlots U (post.state.getStor P)) ∧
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        (ledger U (N.devm.state.getStor P)).Good ∧
        (N.devm.state.getStor P).get implSlot = (pre.state.getStor P).get implSlot ∧
        (N.devm.state.getStor P).get adminSlot = (pre.state.getStor P).get adminSlot ∧
        SlotFootprint.Support Key.slot fixedSlots U (N.devm.state.getStor P)

/-- **The family laws at a good ledger.**  A successful non-static implementation frame keeps the
proxy's slots and the ledger good, at its end and at every external node; or it is `rescueERC20`. -/
theorem impl_laws {P : Adr} {U : Key → Prop} (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U) (signed : ImplStepLaw famSigned)
    {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Impl.code) (target : sevm.currentTarget = P)
    (codeAddr : sevm.codeAddress = some usdcImpl) (fork : CoveredFork sevm.benvStat.fork)
    (nonstatic : sevm.isStatic = false) (keys : ∀ k ∈ frameKeys sevm, U k)
    (lib : some (pre.state.getCode usdcLib).toList = libSem.image)
    (notAdmin : sevm.caller ≠ adminOf pre.state P) (good : (ledger U (pre.state.getStor P)).Good)
    (sup : SlotFootprint.Support Key.slot fixedSlots U (pre.state.getStor P)) :
    ImplKeeps P U run ∨ Blanc.Sevm.selector sevm = rescueSelector := by
  obtain ⟨c, dec⟩ := impl_decodes run codeEq fork
  have whole : ∀ fam, ImplStepLaw fam → fam c →
      ImplKeeps P U run ∨ Blanc.Sevm.selector sevm = rescueSelector := fun fam law hc => by
    obtain ⟨step, hi, ha, hs, nodes⟩ :=
      law run codeEq target codeAddr fork nonstatic inj apart keys lib notAdmin c dec hc
    exact Or.inl ⟨⟨book_good step good, hi, ha, hs sup⟩, fun N chain x hat =>
      let ⟨_, g, i, a, ns⟩ := nodes N chain x hat
      ⟨g good, i, a, ns sup⟩⟩
  rcases call_family_cases c with h | h | h | h | h | h | ⟨t, d, v, rfl⟩
  · exact whole _ implStepLaw_famTransfer h
  · exact whole _ signed h
  · exact whole _ implStepLaw_famAdmin h
  · exact whole _ impl_view_law (by cases c <;> first | rfl | exact h.elim)
  · exact (impl_initRevert run codeEq target codeAddr fork nonstatic inj apart keys lib notAdmin
      good c dec h).elim
  · exact (impl_initV2Revert run codeEq target codeAddr fork nonstatic inj apart keys lib notAdmin
      good c dec (by cases c <;> first | exact .inl rfl | exact .inr ⟨_, rfl⟩ | exact h.elim)).elim
  · exact .inr (decodeCall_rescue dec)

/-- The entry facts of a child spawned at a node of a frame's chain. -/
theorem node_child {P : Adr} {root N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix root N)
    (fork : CoveredFork root.sevm.benvStat.fork) (codes : Codes P root.devm) {f : Frame}
    {rsm : Resume} {pc' : Nat} {cevm : Evm}
    (step : Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc') (enter : f.enter = .run cevm) :
    N.sevm = root.sevm ∧ CoveredFork N.sevm.benvStat.fork ∧ cevm.pc = 0 ∧
      CoveredFork cevm.sta.benvStat.fork ∧ cevm.sta.depth < root.sevm.depth ∧ Codes P N.devm ∧
      Codes P cevm.dyna ∧ cevm.dyna.state.getStor P = N.devm.state.getStor P := by
  have sevmEq : N.sevm = root.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have nfork : CoveredFork N.sevm.benvStat.fork := by rw [sevmEq]; exact fork
  obtain ⟨pcZero, cfork, cdepth, ccode, cstor⟩ := Evm.step_spawn_entry nfork step enter
  have ncodes : Codes P N.devm :=
    codes_keep (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 codes
  exact ⟨sevmEq, nfork, pcZero, cfork, sevmEq ▸ cdepth, ncodes,
    codes_keep (fun a _ => ccode a) ncodes, cstor P (proxy_protected ncodes.1)⟩

section Frames

variable {P : Adr} {U : Key → Prop} {a₀ : Adr}

/-- A child at a node of a frame at the proxy that a `CALL`/`STATICCALL` spawned: located by the
proxy's code, it carries its conclusion by the deeper hypothesis. -/
theorem entry_slots {k : Nat} (deeper : Deeper P U a₀ k) {root N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix root N) (fork : CoveredFork root.sevm.benvStat.fork)
    (codes : Codes P root.devm) (target : root.sevm.currentTarget = P)
    (depth : root.sevm.depth ≤ k) {x : Xinst} (kind : x = .call ∨ x = .staticcall) {f : Frame}
    {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution}
    (step : Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc')
    (spawn : Xinst.step N.sevm N.devm x = .spawn f rsm) (enter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw) (h : raw.commits = true)
    (admitted : Exec.FrameAdmitted P (slotEntry U) root.exc)
    (desc : ∀ g ∈ Exec.Frame.ofRun child h :: Exec.descendantFrames child,
      g ∈ Exec.descendantFrames root.exc)
    (avail : ∀ g ∈ Exec.descendantFrames root.exc, Avail P a₀ g)
    (nodeInv : SlotInv U a₀ (N.devm.state.getStor P)) :
    FrameQ P U a₀ (Exec.Frame.ofRun child h) ∧
      ∀ g ∈ Exec.descendantFrames child, FrameQ P U a₀ g := by
  obtain ⟨sevmEq, -, pcZero, cfork, cdepth, ncodes, ccodes, cstor⟩ :=
    node_child chain fork codes step enter
  have mem := desc _ List.mem_cons_self
  have kindAt : cevm.sta.currentTarget = P →
      cevm.sta.codeAddress = some P ∧ cevm.sta.code = Proxy.code := fun t =>
    let ⟨ca, cd⟩ := entry_child kind spawn enter ncodes.1 t
    ⟨ca, cd (by rw [sevmEq]; exact target)⟩
  obtain ⟨-, q, d⟩ := child_slots (fun at_ => deeper _ _ _ _ child (Nat.lt_of_lt_of_le cdepth depth) at_)
    child h pcZero cfork ccodes.1 kindAt (Exec.FrameAdmitted.of_mem_descendantFrames admitted mem)
    (avail _ mem) (fun g hg => avail g (desc g (List.mem_cons_of_mem _ hg)))
    (by rw [cstor]; exact nodeInv)
  exact ⟨q, d⟩

/-- **A library frame at the proxy.**  Its chain keeps the proxy's storage and spawns only static
entries. -/
theorem libFrame {k : Nat} (deeper : Deeper P U a₀ k) {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (depth : sevm.depth ≤ k) (codeEq : sevm.code = Lib.code)
    (target : sevm.currentTarget = P) (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted P (slotEntry U) run) (codes : Codes P pre)
    (avail : ∀ f ∈ Exec.descendantFrames run, Avail P a₀ f)
    (inv : SlotInv U a₀ (pre.state.getStor P)) :
    SlotInv U a₀ (post.state.getStor P) ∧ ∀ f ∈ Exec.descendantFrames run, FrameQ P U a₀ f := by
  let root : Exec.Deriv := ⟨0, sevm, pre, .ok post, run⟩
  have onlyStatic : ∀ {node : Exec.Deriv} {x : Xinst}, Exec.Deriv.ParentPrefix root node →
      Ninst.At node.sevm.code node.pc (.exec x) → x = .staticcall := fun chain hat =>
    parentPrefix_exec_staticcall_of_cert Lib.cert_check lib_staticOnly (root := root) rfl codeEq
      fork chain hat
  refine ⟨?_, Exec.descendantFrames_of_spawns (root := root) ?_ run (.refl _) (fun _ h => h)
    (fun _ h => h)⟩
  · have keep := (lib_children run codeEq fork).2 post rfl
    rw [target] at keep
    rw [keep]; exact inv
  · intro N f rsm pc' cevm raw child h chain step enter _ desc
    obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
    have hx : x = .staticcall := onlyStatic chain hat
    have keep := Exec.Deriv.ParentPrefix.getStor_of_quiet chain fork
      (fun _ hat' => lib_stor_free (by rw [← codeEq]; exact hat')) onlyStatic
    have nodeInv : SlotInv U a₀ (N.devm.state.getStor P) := by
      rw [show N.devm.state.getStor P = pre.state.getStor P from congrFun keep P]; exact inv
    exact entry_slots deeper chain fork codes target depth (.inr hx) step (hx ▸ spawn) enter child
      h admitted desc avail nodeInv

/-- **An implementation frame's children**, given the invariant at every committed child's entry:
library frames (`libFrame`) and entries. -/
theorem impl_children_slots {k : Nat} (deeper : Deeper P U a₀ k) {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (depth : sevm.depth ≤ k) (codeEq : sevm.code = Impl.code)
    (target : sevm.currentTarget = P) (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted P (slotEntry U) run) (codes : Codes P pre)
    (avail : ∀ f ∈ Exec.descendantFrames run, Avail P a₀ f)
    (entryInv : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution}
        (child : Exec cevm.pc cevm.sta cevm.dyna raw) (h : raw.commits = true),
        Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc' → f.enter = .run cevm →
        Exec.Frame.ofRun child h ∈ Exec.childFrames run →
        SlotInv U a₀ (cevm.dyna.state.getStor P) ∧ SlotInv U a₀ (N.devm.state.getStor P)) :
    ∀ f ∈ Exec.descendantFrames run, FrameQ P U a₀ f := by
  refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, .ok post, run⟩) ?_ run (.refl _)
    (fun _ h => h) (fun _ h => h)
  intro N f rsm pc' cevm raw child h chain step enter member desc
  obtain ⟨cinv, ninv⟩ := entryInv N chain child h step enter member
  obtain ⟨sevmEq, nfork, pcZero, cfork, cdepth, ncodes, ccodes, -⟩ :=
    node_child chain fork codes step enter
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  rcases impl_node run codeEq fork chain hat spawn with rfl | ⟨rfl, g, rest, stack⟩
  · exact entry_slots deeper chain fork codes target depth (.inl rfl) step spawn enter child h
      admitted desc avail ninv
  · have adr : usdcLib.toB256.toAdr = usdcLib := toAdr_toB256 _
    obtain ⟨hT, hA, -, -, -, hK, -⟩ := Xinst.step_delegatecall_spawn_exact nfork spawn stack
      (by rw [adr, ncodes.2.2]; exact lib_undelegated)
    rw [adr] at hA hK
    have ctarget : cevm.sta.currentTarget = P := by
      rw [Frame.enter_run_currentTarget enter, hT, sevmEq]; exact target
    have ccode : cevm.sta.code = Lib.code := by
      rw [Frame.enter_run_code enter, hK]; exact ncodes.2.2
    have cca : cevm.sta.codeAddress = some usdcLib := by
      rw [Frame.enter_run_codeAddress enter]; exact hA
    have mem := desc _ List.mem_cons_self
    have cadmitted := Exec.FrameAdmitted.of_mem_descendantFrames admitted mem
    cases raw with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at h
    | ok cpost =>
      obtain ⟨cevmPc, csevm, cdyna⟩ := cevm
      dsimp only at pcZero
      subst pcZero
      obtain ⟨lpost, ldesc⟩ := libFrame deeper child (Nat.le_of_lt (Nat.lt_of_lt_of_le cdepth depth))
        ccode ctarget cfork cadmitted ccodes
        (fun g hg => avail g (desc g (List.mem_cons_of_mem _ hg))) cinv
      exact ⟨⟨cinv, lpost, fun _ => .inr (.inr ⟨cca, ccode⟩)⟩, ldesc⟩

/-- **An implementation frame at the proxy.**  A static one keeps the proxy's storage; a non-static
one keeps the invariant by its family's law, at its end and at every spawning node. -/
theorem implFrame (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U) (signed : ImplStepLaw famSigned)
    (rescueEnd : RescueQuietEnd) {k : Nat} (deeper : Deeper P U a₀ k) {sevm : Sevm}
    {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true) (depth : sevm.depth ≤ k)
    (codeEq : sevm.code = Impl.code) (target : sevm.currentTarget = P)
    (codeAddr : sevm.codeAddress = some usdcImpl) (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted P (slotEntry U) run) (codes : Codes P pre)
    (notAdmin : sevm.caller ≠ adminOf pre.state P)
    (avail : ∀ f ∈ Exec.descendantFrames run, Avail P a₀ f)
    (inv : SlotInv U a₀ (pre.state.getStor P)) :
    SlotInv U a₀ (post.state.getStor P) ∧ ∀ f ∈ Exec.descendantFrames run, FrameQ P U a₀ f := by
  have keys : ∀ k ∈ frameKeys sevm, U k := (admitted.root target).1
  have lib : some (pre.state.getCode usdcLib).toList = libSem.image := by
    rw [show pre.state.getCode usdcLib = Lib.code from codes.2.2]; rfl
  have codeNe : (pre.getCode P).toList ≠ [] := by rw [codes.1]; exact proxy_nonempty
  have entryOfNode : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm},
        Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc' → f.enter = .run cevm →
        cevm.dyna.state.getStor P = N.devm.state.getStor P := by
    intro N chain f rsm pc' cevm step enter
    exact (node_child chain fork codes step enter).2.2.2.2.2.2.2
  cases hs : sevm.isStatic
  · rcases impl_laws inj apart signed run codeEq target codeAddr fork hs keys lib notAdmin
      inv.2.2.1 inv.2.2.2 with ⟨⟨pg, pi, pa, ps⟩, nodes⟩ | hsel
    · have nodeInv : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
          ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → SlotInv U a₀ (N.devm.state.getStor P) :=
        fun N chain x hat =>
          let ⟨g, i, a, ns⟩ := nodes N chain x hat
          ⟨i.trans inv.1, by rw [a]; exact inv.2.1, g, ns⟩
      refine ⟨⟨pi.trans inv.1, by rw [pa]; exact inv.2.1, pg, ps⟩, ?_⟩
      refine impl_children_slots deeper run depth codeEq target fork admitted codes avail ?_
      intro N chain f rsm pc' cevm raw child h step enter _
      obtain ⟨x, hat, -, -⟩ := Evm.step_spawn_inv step
      have ni := nodeInv N chain x hat
      exact ⟨by rw [entryOfNode N chain step enter]; exact ni, ni⟩
    · obtain ⟨-, nodes⟩ := rescueLaw run codeEq target codeAddr fork hs keys hsel
      have desc : ∀ f ∈ Exec.descendantFrames run, FrameQ P U a₀ f := by
        refine impl_children_slots deeper run depth codeEq target fork admitted codes avail ?_
        intro N chain f rsm pc' cevm raw child h step enter _
        obtain ⟨x, hat, -, -⟩ := Evm.step_spawn_inv step
        have nstor := (nodes N chain x hat).2.1
        exact ⟨by rw [entryOfNode N chain step enter, nstor]; exact inv, by rw [nstor]; exact inv⟩
      refine ⟨?_, desc⟩
      rcases Exec.Deriv.exists_firstExec_or_none run with none | ⟨Vn, hV⟩
      · rw [rescueEnd run codeEq target fork hs hsel (proxy_protected codes.1) none]; exact inv
      have hpV := hV.parentPrefix
      have dEq := hV.descendantFrames_eq
      obtain ⟨x, hx⟩ := hV.exec_at
      have hexn := Exec.Deriv.ParentPrefix.exn_eq hpV
      obtain ⟨-, nstor, after⟩ := nodes _ hpV x hx
      obtain ⟨vpc, vsevm, vd, vout, vrun⟩ := Vn
      dsimp only at hexn hx dEq nstor after hpV
      subst hexn
      have vfork : CoveredFork vsevm.benvStat.fork := by
        have e := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hpV
        dsimp only at e
        rw [e]; exact fork
      have vprot : State.Protected vd.state P :=
        proxy_protected (codes_keep (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode hpV).2 codes).1
      cases vrun with
      | halt step =>
          rw [Evm.step_next hx] at step
          exact (Ninst.step_ne_halt_ok step).elim
      | cont step next =>
          rename_i pc' post'
          have nstep : Ninst.step ⟨vpc, vsevm, vd⟩ (.exec x) = .cont pc' post' := by
            rw [← Evm.step_next hx]; exact step
          have nrun : Ninst.StepRun vpc vsevm vd (.exec x) .none (.ok post') := by
            unfold Ninst.StepRun; rw [nstep]; exact ⟨rfl, rfl⟩
          have hstor : post'.state.getStor P = vd.state.getStor P :=
            Ninst.none_getStor_eq_of_ne_sstore nrun (by intro h; cases h) P vprot
          rw [(after _ (.cont step next)).1]
          change SlotInv U a₀ (post'.state.getStor P)
          rw [hstor, nstor]; exact inv
      | doneOk step enter resume next =>
          rename_i settled pc' post'
          have hstor : post'.state.getStor P = vd.state.getStor P :=
            Evm.step_doneOk_getStor_eq step enter resume P vprot
          rw [(after _ (.doneOk step enter resume next)).1]
          change SlotInv U a₀ (post'.state.getStor P)
          rw [hstor, nstor]; exact inv
      | runOk step enter child resume next =>
          rename_i frame rsm pc' cevm raw inter
          rw [(after _ (.runOk step enter child resume next)).1]
          change SlotInv U a₀ (inter.state.getStor P)
          obtain ⟨seamA, seamB⟩ := Exec.spawn_seam vfork step enter child resume
          by_cases settles : Frame.settlementCommits frame raw = true
          · have hcommit := Frame.raw_commits_of_settlementCommits settles
            have mem : Exec.Frame.ofRun child hcommit ∈ Exec.descendantFrames run := by
              rw [dEq, Exec.descendantFrames_runOk_of_settlementCommits step enter child resume next
                settles]
              exact List.mem_cons_self
            exact SlotInv.congr (seamA hcommit settles P) (desc _ mem).2.1
          · refine SlotInv.congr (seamB settles P) ?_
            change SlotInv U a₀ (vd.state.getStor P)
            rw [nstor]; exact inv
  · have keep := Exec.getStor_committedPost_eq_of_static run hs committed fork
      (Or.inl (by rw [target]; exact proxy_protected codes.1))
    refine ⟨?_, ?_⟩
    · rw [show post.state.getStor P = pre.state.getStor P from congrFun keep P]; exact inv
    refine impl_children_slots deeper run depth codeEq target fork admitted codes avail ?_
    intro N chain f rsm pc' cevm raw child h step enter member
    have mem := Exec.mem_descendantFrames_of_mem_childFrames run _ member
    have e : cevm.dyna.state.getStor P = pre.state.getStor P :=
      Blanc.Exec.descendantFrames_getStor_of_static run hs committed fork codeNe _ mem
    exact ⟨by rw [e]; exact inv, by rw [← entryOfNode N chain step enter, e]; exact inv⟩

/-- **A proxy frame** (the target handler).  An admin caller holds a getter by F2: no child, the
storage unchanged; any other caller forwards to the implementation, entered with the frame's
storage, and ends with the implementation's state. -/
theorem proxyFrame (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U) (signed : ImplStepLaw famSigned)
    (rescueEnd : RescueQuietEnd) {sevm : Sevm} {pre post : Devm}
    (codeEq : sevm.code = Proxy.code) (target : sevm.currentTarget = P)
    (deeper : Deeper P U a₀ sevm.depth) : SlotsOk P U a₀ 0 sevm pre (.ok post) := by
  intro run _ fork _ admitted here avail inv
  obtain ⟨-, codes, gov⟩ := here target
  by_cases admin : sevm.caller = adminOf pre.state P
  · have admin' : sevm.caller = adminOf pre.state sevm.currentTarget := by rw [target]; exact admin
    have hsel := gov (admin.trans inv.2.1)
    have noExec : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) := fun N chain x hat =>
      hsel (by rw [(proxy_admin_exec run codeEq fork admin' N chain x hat).2.1]; decide)
    rw [Exec.descendantFrames_eq_nil_of_noExec run noExec]
    refine ⟨fun p hp => ?_, fun f hf => (List.not_mem_nil hf).elim⟩
    cases hp
    have keep := ((proxy_admin_rule run codeEq fork admin').2.2 hsel).2 post rfl
    rw [target] at keep
    rw [keep]; exact inv
  · have notAdmin' : sevm.caller ≠ adminOf pre.state sevm.currentTarget := by
      rw [target]; exact admin
    have slot : (pre.state.getStor sevm.currentTarget).get implSlot = usdcImpl.toB256 := by
      rw [target]; exact inv.1
    obtain ⟨-, kids, fin⟩ := proxy_forwards run codeEq fork slot notAdmin'
      (by rw [show pre.state.getCode usdcImpl = Impl.code from codes.2.1]; exact impl_undelegated)
      (impl_not_precompile fork) (admitted.root target).2
    have nodeState : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → N.devm.state = pre.state := by
      intro N chain x hat
      obtain ⟨g, K, ⟨-, hd⟩ | ⟨-, hs, -⟩⟩ := proxy_node run codeEq fork chain hat
      · obtain ⟨-, b', w, S, M, G, rest, hstate, -, hdev⟩ := hd
        change N.devm = _ at hdev
        rw [hdev]; exact hstate
      · exact (notAdmin' (by rw [adminOf_eq]; exact hs.1)).elim
    have desc : ∀ f ∈ Exec.descendantFrames run, FrameQ P U a₀ f := by
      refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, .ok post, run⟩) ?_ run
        (.refl _) (fun _ h => h) (fun _ h => h)
      intro N f rsm pc' cevm raw child h chain step enter member descm
      obtain ⟨hT, hA, hC, -, -, -, hK⟩ := kids _ member
      obtain ⟨-, -, pcZero, cfork, cdepth, -, ccodes, cstor⟩ :=
        node_child chain fork codes step enter
      obtain ⟨x, hat, -, -⟩ := Evm.step_spawn_inv step
      have nstate := nodeState N chain x hat
      have cstor' : cevm.dyna.state.getStor P = pre.state.getStor P := by rw [cstor, nstate]
      have cinv : SlotInv U a₀ (cevm.dyna.state.getStor P) := by rw [cstor']; exact inv
      have mem := descm _ List.mem_cons_self
      have ccode : cevm.sta.code = Impl.code := hK.trans codes.2.1
      cases raw with
      | error e => simp only [Execution.commits, Bool.false_eq_true] at h
      | ok cpost =>
        obtain ⟨cevmPc, csevm, cdyna⟩ := cevm
        dsimp only at pcZero
        subst pcZero
        have cnot : csevm.caller ≠ adminOf cdyna.state P := by
          change csevm.caller = sevm.caller at hC
          unfold adminOf
          rw [cstor', hC]; exact admin
        obtain ⟨ipost, idesc⟩ := implFrame inj apart signed rescueEnd deeper child h
          (Nat.le_of_lt cdepth) ccode (hT.trans target) hA cfork
          (Exec.FrameAdmitted.of_mem_descendantFrames admitted mem) ccodes cnot
          (fun g hg => avail g (descm g (List.mem_cons_of_mem _ hg))) cinv
        exact ⟨⟨cinv, ipost, fun _ => .inr (.inl ⟨hA, ccode⟩)⟩, idesc⟩
    refine ⟨fun p hp => ?_, desc⟩
    cases hp
    obtain ⟨c, mem, -, hstate⟩ := fin post rfl
    rw [hstate]
    exact (desc c (Exec.mem_descendantFrames_of_mem_childFrames run c mem)).2.1

/-- **The slot induction**, at every derivation located by the proxy's code. -/
theorem usdc_slotsOk (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U) (signed : ImplStepLaw famSigned)
    (rescueEnd : RescueQuietEnd) :
    Exec.Fa (Exec.WknSem P proxySem (fun pc s d e _ => SlotsOk P U a₀ pc s d e)) :=
  lift_core_sem (fun pc s d e => SlotsOk P U a₀ pc s d e)
    (fun s d p => SlotsOk P U a₀ 0 s d (.ok p)) (fun h => h) P proxySem
    (fun hrun target deeper => proxyFrame inj apart signed rescueEnd hrun target deeper)
    (fun _ => SlotsOk.error) (fun _ _ => SlotsOk.error) (fun _ _ _ => SlotsOk.error)
    (fun _ _ _ _ _ => SlotsOk.error)
    (fun hat step next targetNe ih => SlotsOk.nextNone hat step next targetNe ih)
    (fun hat step child next targetNe ihChild ihNext =>
      SlotsOk.nextSome hat step child next targetNe ihChild ihNext)
    (fun _ _ _ => SlotsOk.error)
    (fun hat step next targetNe ih => SlotsOk.jump hat step next targetNe ih)
    (fun hat step _ => SlotsOk.last hat step)

end Frames

end Blanc.Lift.Usdc
