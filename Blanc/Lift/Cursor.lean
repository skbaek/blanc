import Blanc.Lift.Sound
import Jaune.ExecChronology

/-!
# The certificate cursor: the prefix form of the lift

`lift_sound` (`Blanc/Lift/Sound.lean`) relates only *successful* executions to
the certificate's synthetic program.  This module relates every node reached
along a frame's same-frame chain (`Exec.Deriv.ParentPrefix`) — whatever the
frame's eventual outcome: success, revert, exceptional halt — to a checked
node of the certificate.

A `Cursor` names a point of the synthetic program: the tree still to run, its
pc, its abstract frame, the current function's return arity, and the stack of
pending `callNext` continuations (`Cont`).  `CursorOK code c n κ` says the
concrete node `n` sits at `κ`: same pc, the tree checks there
(`checkNode … = true`), and the concrete operand stack decomposes into one
segment per pending function, each matched by its abstract frame
(`FrameMatches`) — `node_sound`'s recursion invariant made explicit.

* `cursor_start`: a checked certificate places every frame entered at pc `0`
  at entry `0`;
* `cursor_step`: every same-frame edge out of a cursor-placed node is one
  synthetic step (`SStep`) to a cursor-placed node — including a `CALL`'s
  edge over its child frame, whatever the child's outcome;
* `cursor_of_parentPrefix`: hence every node of the frame's same-frame chain is
  cursor-placed, reached from entry `0` by synthetic steps.

No statement here has a success premise.  `CoveredFork` enters only through
the transfer soundness of the instruction steps (`ninstTransfer_run`).
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-- A pending `callNext` continuation: the tree `f` at the return tag `tag`,
the caller's frame `a` below the callee's arguments, the caller's return arity
`m`, and the callee's return arity `rets`.  A `live` continuation is checked;
a dead one (`live = false`) belongs to a callee whose frame carries no return
address, which therefore never returns. -/
structure Cont : Type where
  f : SFunc
  tag : B256
  a : List AVal
  m : Nat
  rets : Nat
  live : Bool

/-- A point of the synthetic program: the tree still to run at `pc` with frame
`a`, the current function's return arity `m`, and the pending continuations
`K`, innermost first. -/
structure Cursor : Type where
  f : SFunc
  pc : Nat
  a : List AVal
  m : Nat
  K : List Cont

/-- The return address the current function's frame reads `.ret` as. -/
def Cont.tagOf : List Cont → B256
  | [] => 0
  | k :: _ => k.tag

/-- A frame that mentions its return address has a live pending continuation
expecting exactly its return arity. -/
def RetOK (a : List AVal) (m : Nat) (K : List Cont) : Prop :=
  AVal.ret ∈ a → ∃ k K', K = k :: K' ∧ k.live = true ∧ k.rets = m

/-- The operand stack below the current function: one segment per pending
continuation, matched by the caller's remaining frame, each live continuation
checked at its return tag. -/
inductive ContsOK (code : ByteArray) (es : List Entry) : List Cont → List B256 → Prop
  | nil (base : List B256) : ContsOK code es [] base
  | cons {k : Cont} {K : List Cont} {S rest : List B256} :
      FrameMatches (Cont.tagOf K) k.a S →
      RetOK k.a k.m K →
      (k.live = true →
        checkNode code es k.m k.tag.toNat (List.replicate k.rets .unk ++ k.a) k.f = true) →
      ContsOK code es K rest →
      ContsOK code es (k :: K) (S ++ rest)

/-- The concrete node `n` sits at the checked cursor `κ`. -/
structure CursorOK (code : ByteArray) (c : Cert) (n : Exec.Deriv) (κ : Cursor) : Prop where
  code_eq : n.sevm.code = code
  pc_eq : n.pc = κ.pc
  check : checkNode code c.entries κ.m κ.pc κ.a κ.f = true
  retOK : RetOK κ.a κ.m κ.K
  stack : ∃ S rest, n.devm.stack = S ++ rest ∧
    FrameMatches (Cont.tagOf κ.K) κ.a S ∧ ContsOK code c.entries κ.K rest

/-- One node of the synthetic program, following `checkNode`'s bookkeeping. -/
inductive SStep (c : Cert) : Cursor → Cursor → Prop
  | next {n : Ninst} {f : SFunc} {pc : Nat} {a a' : List AVal} {m : Nat} {K : List Cont} :
      absNinst n a = some a' →
      SStep c ⟨.next n f, pc, a, m, K⟩ ⟨f, pc + n.size, a', m, K⟩
  | dest {f : SFunc} {pc : Nat} {a : List AVal} {m : Nat} {K : List Cont} :
      SStep c ⟨.dest f, pc, a, m, K⟩ ⟨f, pc + 1, a, m, K⟩
  | zero {f g : SFunc} {pc : Nat} {t : B256} {v : AVal} {a : List AVal} {m : Nat}
      {K : List Cont} :
      SStep c ⟨.branch f g, pc, .const t :: v :: a, m, K⟩ ⟨f, pc + 1, a, m, K⟩
  | succ {f g : SFunc} {pc : Nat} {t : B256} {v : AVal} {a : List AVal} {m : Nat}
      {K : List Cont} :
      SStep c ⟨.branch f g, pc, .const t :: v :: a, m, K⟩ ⟨g, t.toNat, a, m, K⟩
  | toZero {f : SFunc} {k pc : Nat} {t : B256} {v : AVal} {a : List AVal} {m : Nat}
      {K : List Cont} :
      SStep c ⟨.branchTo f k, pc, .const t :: v :: a, m, K⟩ ⟨f, pc + 1, a, m, K⟩
  | toSucc {f g : SFunc} {k pc : Nat} {t : B256} {v : AVal} {a : List AVal} {m : Nat}
      {K : List Cont} {e : Entry} :
      c.entries[k]? = some e → c.prog[k]? = some g →
      SStep c ⟨.branchTo f k, pc, .const t :: v :: a, m, K⟩ ⟨g, e.pc, e.frame, e.rets, K⟩
  | jump {g : SFunc} {k pc : Nat} {t : B256} {a : List AVal} {m : Nat} {K : List Cont}
      {e : Entry} :
      c.entries[k]? = some e → c.prog[k]? = some g →
      SStep c ⟨.jump k, pc, .const t :: a, m, K⟩ ⟨g, e.pc, e.frame, e.rets, K⟩
  | call {f g : SFunc} {k pc : Nat} {t : B256} {a : List AVal} {m : Nat} {K : List Cont}
      {e : Entry} (κc : Cont) :
      c.entries[k]? = some e → c.prog[k]? = some g →
      κc.f = f → κc.a = a.drop e.frame.length → κc.m = m → κc.rets = e.rets →
      SStep c ⟨.callNext k f, pc, .const t :: a, m, K⟩ ⟨g, e.pc, e.frame, e.rets, κc :: K⟩
  | ret {pc : Nat} {a : List AVal} {m : Nat} {k : Cont} {K : List Cont} :
      SStep c ⟨.ret, pc, .ret :: a, m, k :: K⟩
        ⟨k.f, k.tag.toNat, List.replicate k.rets .unk ++ k.a, k.m, K⟩
  | pcAt {f : SFunc} {p : Nat} {a : List AVal} {m : Nat} {K : List Cont} :
      SStep c ⟨.pcAt p f, p, a, m, K⟩ ⟨f, p + 1, .const (Nat.toB256 p) :: a, m, K⟩

/-! ### One same-frame edge, by instruction kind -/

namespace Cursor

theorem parentStep_sevm {n' n : Exec.Deriv} (edge : Exec.Deriv.ParentStep n' n) :
    n'.sevm = n.sevm := by
  cases edge <;> rfl

/-- A same-frame edge out of a jump instruction is a continued `Jinst.Run`. -/
theorem parentStep_jinst {n' n : Exec.Deriv} {j : Jinst}
    (edge : Exec.Deriv.ParentStep n' n) (hat : Jinst.At n.sevm.code n.pc j) :
    Jinst.Run ⟨n.pc, n.sevm, n.devm⟩ j (.ok ⟨n'.pc, n'.devm⟩) := by
  cases edge with
  | cont hstep next => exact Step.ofJump_cont ((Evm.step_jump hat).symm.trans hstep)
  | doneOk hstep _ _ _ => exact ((Step.ofJump_ne_spawn ((Evm.step_jump hat).symm.trans hstep))).elim
  | runOk hstep _ _ _ _ =>
    exact ((Step.ofJump_ne_spawn ((Evm.step_jump hat).symm.trans hstep))).elim

/-- A same-frame edge out of a non-jump instruction is one `Ninst.Run` to the
next pc, over the child frame (of any outcome) if the instruction spawned one. -/
theorem parentStep_ninst {n' n : Exec.Deriv} {i : Ninst}
    (edge : Exec.Deriv.ParentStep n' n) (hat : Ninst.At n.sevm.code n.pc i) :
    n'.pc = n.pc + i.size ∧ Ninst.Run n.sevm n.devm i n'.devm := by
  rcases n with ⟨pc, sevm, pre, out, run⟩
  dsimp only at hat ⊢
  cases edge with
  | cont hstep next =>
    have hs := (Evm.step_next hat).symm.trans hstep
    refine ⟨Ninst.step_cont_pc hs, .none, trivial, pc, ?_⟩
    simp only [Ninst.StepRun, hs, Step.Run]
    exact ⟨trivial, trivial⟩
  | doneOk hstep henter hresume next =>
    have hs := (Evm.step_next hat).symm.trans hstep
    refine ⟨Ninst.step_spawn_pc hs, .none, trivial, pc, ?_⟩
    simp only [Ninst.StepRun, hs, Step.Run]
    exact ⟨_, RunFrame.of_done henter, hresume.symm⟩
  | runOk hstep henter child hresume next =>
    have hs := (Evm.step_next hat).symm.trans hstep
    refine ⟨Ninst.step_spawn_pc hs, .some ⟨_, _⟩, ⟨child⟩, pc, ?_⟩
    simp only [Ninst.StepRun, hs, Step.Run]
    exact ⟨_, RunFrame.of_run henter, hresume.symm⟩

/-- A same-frame edge out of a `PC` is the `PC` step at the node's own pc. -/
theorem parentStep_pc {n' n : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep n' n) (hat : Ninst.At n.sevm.code n.pc (.reg .pc)) :
    n'.pc = n.pc + 1 ∧ Ninst.StepRun n.pc n.sevm n.devm (.reg .pc) .none (.ok n'.devm) := by
  rcases n with ⟨pc, sevm, pre, out, run⟩
  dsimp only at hat ⊢
  have hstep0 := Evm.step_next (devm := pre) hat
  rw [Ninst.step_reg] at hstep0
  cases edge with
  | cont hstep next =>
    have hs := hstep0.symm.trans hstep
    cases hr : Rinst.run ⟨pc, sevm, pre⟩ .pc <;> simp [hr, Step.ofExecution] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨rfl, ?_⟩
    simp only [Ninst.StepRun, Ninst.step_reg, hr, Step.ofExecution, Step.Run]
    exact ⟨trivial, trivial⟩
  | doneOk hstep _ _ _ =>
    have hs := hstep0.symm.trans hstep
    cases hr : Rinst.run ⟨pc, sevm, pre⟩ .pc <;> simp [hr, Step.ofExecution] at hs
  | runOk hstep _ _ _ _ =>
    have hs := hstep0.symm.trans hstep
    cases hr : Rinst.run ⟨pc, sevm, pre⟩ .pc <;> simp [hr, Step.ofExecution] at hs

theorem parentStep_false_of_linst {n' n : Exec.Deriv} {l : Linst}
    (edge : Exec.Deriv.ParentStep n' n) (hat : Linst.At n.sevm.code n.pc l) : False := by
  cases edge with
  | cont hstep _ => cases (Evm.step_last hat).symm.trans hstep
  | doneOk hstep _ _ _ => cases (Evm.step_last hat).symm.trans hstep
  | runOk hstep _ _ _ _ => cases (Evm.step_last hat).symm.trans hstep

theorem parentStep_false_of_none {n' n : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep n' n) (hnone : n.sevm.code.getInst n.pc = none) : False := by
  cases edge with
  | cont hstep _ => cases (Evm.step_invOp hnone).symm.trans hstep
  | doneOk hstep _ _ _ => cases (Evm.step_invOp hnone).symm.trans hstep
  | runOk hstep _ _ _ _ => cases (Evm.step_invOp hnone).symm.trans hstep

/-! ### Frame bookkeeping for one step -/

theorem ret_mem_of_absNinst {n : Ninst} {a a' : List AVal}
    (h : absNinst n a = some a') (hm : AVal.ret ∈ a') : AVal.ret ∈ a := by
  by_cases hpush : ∃ (bs : Bytes) (fits : bs.length ≤ 32), n = .push bs fits
  · obtain ⟨bs, fits, rfl⟩ := hpush
    simp only [absNinst, Option.some.injEq] at h
    subst h
    simpa using hm
  · have hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), n ≠ .push bs fits :=
      fun bs fits he => hpush ⟨bs, fits, he⟩
    obtain ⟨_, out, a0, _, hread, hfold⟩ := absNinst_nonpush_spec hn h
    exact ret_mem_of_readBack hread (ret_mem_of_foldTop (hfold ▸ hm))

/-- The abstract effect of a checked non-jump instruction is sound for one
instruction run, whatever the frame's eventual outcome: the words the
instruction leaves above the untouched `rest` match the transferred frame. -/
theorem absNinst_run_stack {sevm : Sevm} {devm devm' : Devm} {n : Ninst}
    {a a' : List AVal} {ρ : B256} {S rest : List B256}
    (hfork : CoveredFork sevm.benvStat.fork) (habs : absNinst n a = some a')
    (hstack : devm.stack = S ++ rest) (hframe : FrameMatches ρ a S)
    (run : Ninst.Run sevm devm n devm') :
    ∃ S', devm'.stack = S' ++ rest ∧ FrameMatches ρ a' S' := by
  by_cases hpush : ∃ (bs : Bytes) (fits : bs.length ≤ 32), n = .push bs fits
  · obtain ⟨bs, fits, rfl⟩ := hpush
    simp only [absNinst, Option.some.injEq] at habs
    subst habs
    exact ⟨Bytes.toB256 bs :: S, by rw [push_run_stack run, hstack]; rfl,
      List.Forall₂.cons rfl hframe⟩
  · have hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), n ≠ .push bs fits :=
      fun bs fits he => hpush ⟨bs, fits, he⟩
    obtain ⟨hlen, out, a0, htrans, hread, hfold⟩ := absNinst_nonpush_spec hn habs
    have hinput :
        Matches ((indexPattern a.length).map (label a ρ) ++ rest.map some)
          devm.stack := by
      rw [hstack]
      apply matches_append
      · rw [indexPattern_map_label hlen]
        exact frameMatches_matches hframe
      · exact matches_some_map rest
    have hout := ninstTransfer_run hfork hinput
      (ninstTransfer_append (rest.map some) (ninstTransfer_map (label a ρ) rfl htrans)) run
    rw [mapM_readBack_label hread] at hout
    obtain ⟨S', below, hsp, hfirst, hbelow⟩ := matches_split hout
    rw [matches_some_map_eq hbelow] at hsp
    refine ⟨S', hsp, ?_⟩
    rw [hfold]
    exact frameMatches_foldTop hframe hstack run hsp (matches_to_frame hfirst)

theorem pop_one_frame {ρ : B256} {av : AVal} {a : List AVal} {S rest : List B256}
    {x : B256} {d d' : Devm} (hstack : d.stack = S ++ rest)
    (hframe : FrameMatches ρ (av :: a) S) (pop : Devm.PopBurn [x] d d') :
    AVal.Matches ρ av x ∧ ∃ S1, d'.stack = S1 ++ rest ∧ FrameMatches ρ a S1 := by
  cases hframe with
  | @cons _ s0 _ S1 h0 htail =>
    have hp := popBurn_one_stack pop
    rw [hstack] at hp
    simp only [List.cons_append, List.cons.injEq] at hp
    obtain ⟨rfl, hs⟩ := hp
    exact ⟨h0, S1, hs.symm, htail⟩

theorem pop_two_frame {ρ : B256} {av bv : AVal} {a : List AVal} {S rest : List B256}
    {x y : B256} {d d' : Devm} (hstack : d.stack = S ++ rest)
    (hframe : FrameMatches ρ (av :: bv :: a) S) (pop : Devm.PopBurn [x, y] d d') :
    AVal.Matches ρ av x ∧ ∃ S1, d'.stack = S1 ++ rest ∧ FrameMatches ρ a S1 := by
  cases hframe with
  | @cons _ s0 _ S0 h0 htail =>
    cases htail with
    | @cons _ s1 _ S1 h1 htail =>
      have hp := popBurn_two_stack pop
      rw [hstack] at hp
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, rfl, hs⟩ := hp
      exact ⟨h0, S1, hs.symm, htail⟩

theorem pop_two_second {ρ : B256} {av bv : AVal} {a : List AVal} {S rest : List B256}
    {x y : B256} {d d' : Devm} (hstack : d.stack = S ++ rest)
    (hframe : FrameMatches ρ (av :: bv :: a) S) (pop : Devm.PopBurn [x, y] d d') :
    AVal.Matches ρ bv y := by
  cases hframe with
  | @cons _ s0 _ S0 h0 htail =>
    cases htail with
    | @cons _ s1 _ S1 h1 htail =>
      have hp := popBurn_two_stack pop
      rw [hstack] at hp
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, rfl, _⟩ := hp
      exact h1

end Cursor

/-! ### The cursor theorems -/

/-- The cursor at entry `0`: the frame's start. -/
def Cursor.start : Cert → Cursor
  | (e, f) :: _ => ⟨f, 0, [], e.rets, []⟩
  | [] => ⟨.undefined, 0, [], 0, []⟩

/-- A frame entered at pc `0` of certified bytes sits at entry `0`, whatever
its initial operand stack (the whole stack is the untouched base). -/
theorem cursor_start {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {F : Exec.Deriv} (hpc : F.pc = 0) (hcode : F.sevm.code = code) :
    CursorOK code c F (Cursor.start c) := by
  cases c with
  | nil => simp [Cert.check] at hc
  | cons p c =>
    rcases p with ⟨e, f⟩
    have hc0 : Cert.check code ((e, f) :: c) = true := hc
    simp [Cert.check] at hc
    have hepc : e.pc = 0 := by simpa using hc.1.1
    have hef : e.frame = [] := by simpa using hc.1.2
    have hf : checkNode code (Cert.entries ((e, f) :: c)) e.rets e.pc e.frame f = true :=
      cert_check_at hc0 0 e f (by simp [Cert.entries]) (by simp [Cert.prog])
    refine ⟨hcode, hpc, ?_, ?_, [], F.devm.stack, rfl, List.Forall₂.nil, .nil _⟩
    · simpa [Cursor.start, hepc, hef] using hf
    · intro hm; simp [Cursor.start] at hm

/-- **One same-frame edge is one synthetic step.**  If `n` sits at the
checked cursor `κ`, its same-frame continuation `n'` — after a plain step, an
immediately completed spawn, or a child frame of any outcome — sits at a
cursor `κ'` one synthetic step after `κ`. -/
theorem cursor_step {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {n n' : Exec.Deriv} {κ : Cursor} (ok : CursorOK code c n κ)
    (edge : Exec.Deriv.ParentStep n' n) (hfork : CoveredFork n.sevm.benvStat.fork) :
    ∃ κ', SStep c κ κ' ∧ CursorOK code c n' κ' := by
  obtain ⟨hcode, hpc, hcheck, hret, S, rest, hstack, hframe, hK⟩ := ok
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hpc hcheck hret hframe hK
  have hcode' : n'.sevm.code = code := by rw [Cursor.parentStep_sevm edge]; exact hcode
  cases f with
  | next i f =>
    simp only [checkNode, Bool.and_eq_true] at hcheck
    obtain ⟨⟨hbytes, _⟩, hrest⟩ := hcheck
    cases habs : absNinst i a with
    | none => simp [habs] at hrest
    | some a' =>
      simp only [habs] at hrest
      have hat : Ninst.At n.sevm.code n.pc i := by
        rw [hcode, hpc]
        exact Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil i) hbytes)
      obtain ⟨hpc', run⟩ := Cursor.parentStep_ninst edge hat
      obtain ⟨S', hst', hfr'⟩ := Cursor.absNinst_run_stack hfork habs hstack hframe run
      exact ⟨_, .next habs, hcode', by simp [hpc', hpc], hrest,
        fun hm => hret (Cursor.ret_mem_of_absNinst habs hm), S', rest, hst', hfr', hK⟩
  | dest f =>
    have h' : byteAt code pc = some (Jinst.toUInt8 .jumpdest) ∧
        checkNode code c.entries m (pc + 1) a f = true := by
      simpa [checkNode] using hcheck
    have hat : Jinst.At n.sevm.code n.pc .jumpdest := by
      rw [hcode, hpc]; exact byteAt_jinst_at h'.1
    obtain ⟨hpc', burn⟩ := of_jumpdest_run (Cursor.parentStep_jinst edge hat)
    refine ⟨_, .dest, hcode', by simp [hpc', hpc], h'.2, hret, S, rest, ?_, hframe, hK⟩
    rw [← burn.stack, hstack]
  | branch f g =>
    match a, hcheck, hret, hframe with
    | .const t :: v :: a', hcheck, hret, hframe =>
      have h' : (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
            (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true)) ∧
          (v.jumps? = some false ∨ checkNode code c.entries m t.toNat a' g = true) := by
        simpa [checkNode] using hcheck
      have hat : Jinst.At n.sevm.code n.pc .jumpi := by
        rw [hcode, hpc]; exact byteAt_jinst_at h'.1.1
      have hret' : RetOK a' m K := fun hm =>
        hret (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
      rcases of_jumpi_run (Cursor.parentStep_jinst edge hat) with
        ⟨x, hpc', pop⟩ | ⟨x, y, hpc', pop, _, hy⟩
      · obtain ⟨_, S1, hst, hfr⟩ := Cursor.pop_two_frame hstack hframe pop
        exact ⟨_, .zero, hcode', by simp [hpc', hpc],
          live_fall (Cursor.pop_two_second hstack hframe pop) h'.1.2, hret', S1, rest, hst, hfr, hK⟩
      · have hv := Cursor.pop_two_second hstack hframe pop
        obtain ⟨hx, S1, hst, hfr⟩ := Cursor.pop_two_frame hstack hframe pop
        have hx : x = t := hx
        subst hx
        exact ⟨_, .succ, hcode', hpc', live_taken hy hv h'.2, hret', S1, rest, hst, hfr, hK⟩
    | [], hcheck, _, _ => simp [checkNode] at hcheck
    | [.const _], hcheck, _, _ => simp [checkNode] at hcheck
    | .ret :: _, hcheck, _, _ => simp [checkNode] at hcheck
    | .unk :: _, hcheck, _, _ => simp [checkNode] at hcheck
  | branchTo f k =>
    match a, hcheck, hret, hframe with
    | .const t :: v :: a', hcheck, hret, hframe =>
      cases hk : c.entries[k]? with
      | none => simp [checkNode, hk] at hcheck
      | some e =>
        have h' : (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
              e.pc = t.toNat) ∧ e.rets = m) ∧
              gotoCompat a' e.frame = true) ∧
              (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true) := by
          simpa [checkNode, hk] using hcheck
        have hat : Jinst.At n.sevm.code n.pc .jumpi := by
          rw [hcode, hpc]; exact byteAt_jinst_at h'.1.1.1.1
        have hret' : RetOK a' m K := fun hm =>
          hret (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
        rcases of_jumpi_run (Cursor.parentStep_jinst edge hat) with
          ⟨x, hpc', pop⟩ | ⟨x, y, hpc', pop, _, _⟩
        · obtain ⟨_, S1, hst, hfr⟩ := Cursor.pop_two_frame hstack hframe pop
          exact ⟨_, .toZero, hcode', by simp [hpc', hpc],
            live_fall (Cursor.pop_two_second hstack hframe pop) h'.2, hret', S1, rest, hst, hfr, hK⟩
        · obtain ⟨hx, S1, hst, hfr⟩ := Cursor.pop_two_frame hstack hframe pop
          have hx : x = t := hx
          subst hx
          obtain ⟨g, hg⟩ := cert_prog_of_entry c k e hk
          refine ⟨_, .toSucc hk hg, hcode', by simp [hpc', h'.1.1.1.2], ?_, ?_, S1, rest, hst,
            frameMatches_gotoCompat h'.1.2 hfr, hK⟩
          · exact cert_check_at hc k e g hk hg
          · intro hm
            rw [h'.1.1.2]
            exact hret' (ret_mem_of_gotoCompat h'.1.2 hm)
    | [], hcheck, _, _ => simp [checkNode] at hcheck
    | [.const _], hcheck, _, _ => simp [checkNode] at hcheck
    | .ret :: _, hcheck, _, _ => simp [checkNode] at hcheck
    | .unk :: _, hcheck, _, _ => simp [checkNode] at hcheck
  | jump k =>
    match a, hcheck, hret, hframe with
    | .const t :: a', hcheck, hret, hframe =>
      cases hk : c.entries[k]? with
      | none => simp [checkNode, hk] at hcheck
      | some e =>
        have h' : (((byteAt code pc = some (Jinst.toUInt8 .jump) ∧
              e.pc = t.toNat) ∧ e.rets = m) ∧
              gotoCompat a' e.frame = true) := by
          simpa [checkNode, hk] using hcheck
        have hat : Jinst.At n.sevm.code n.pc .jump := by
          rw [hcode, hpc]; exact byteAt_jinst_at h'.1.1.1
        obtain ⟨x, hpc', pop, _⟩ := of_jump_run (Cursor.parentStep_jinst edge hat)
        obtain ⟨hx, S1, hst, hfr⟩ := Cursor.pop_one_frame hstack hframe pop
        have hx : x = t := hx
        subst hx
        obtain ⟨g, hg⟩ := cert_prog_of_entry c k e hk
        refine ⟨_, .jump hk hg, hcode', by simp [hpc', h'.1.1.2], ?_, ?_, S1, rest, hst,
          frameMatches_gotoCompat h'.2 hfr, hK⟩
        · exact cert_check_at hc k e g hk hg
        · intro hm
          rw [h'.1.2]
          exact hret (List.mem_cons_of_mem _ (ret_mem_of_gotoCompat h'.2 hm))
    | [], hcheck, _, _ => simp [checkNode] at hcheck
    | .ret :: _, hcheck, _, _ => simp [checkNode] at hcheck
    | .unk :: _, hcheck, _, _ => simp [checkNode] at hcheck
  | callNext k f =>
    match a, f, hcheck, hret, hframe with
    | .const t :: a', .dest f0, hcheck, hret, hframe =>
      cases hk : c.entries[k]? with
      | none => simp [checkNode, hk] at hcheck
      | some e =>
        simp only [checkNode, hk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
        obtain ⟨⟨⟨hbyte, hepc⟩, hlen⟩, hmatch⟩ := hcheck
        have hat : Jinst.At n.sevm.code n.pc .jump := by
          rw [hcode, hpc]; exact byteAt_jinst_at hbyte
        obtain ⟨x, hpc', pop, _⟩ := of_jump_run (Cursor.parentStep_jinst edge hat)
        obtain ⟨hx, S0, hst, hfr⟩ := Cursor.pop_one_frame hstack hframe pop
        have hx : x = t := hx
        subst hx
        obtain ⟨g, hg⟩ := cert_prog_of_entry c k e hk
        have hentry := cert_check_at hc k e g hk hg
        have hretDrop : RetOK (a'.drop e.frame.length) m K := fun hm =>
          hret (List.mem_cons_of_mem _ (List.mem_of_mem_drop hm))
        cases hi : e.frame.findIdx? (· == .ret) with
        | none =>
          simp only [hi] at hmatch
          obtain ⟨sf, sr, hS0, hsf, hsr⟩ := frameMatches_callCompat hmatch hfr
          let κc : Cont := ⟨.dest f0, 0, a'.drop e.frame.length, m, e.rets, false⟩
          refine ⟨_, .call κc hk hg rfl rfl rfl rfl, hcode', by simp [hpc', hepc], hentry,
            ?_, sf, sr ++ rest, by rw [hst, hS0, List.append_assoc], hsf,
            .cons hsr hretDrop (fun h => by cases h) hK⟩
          intro hm
          exact (ret_not_mem_of_findIdx_none hi _ hm rfl).elim
        | some i =>
          simp only [hi] at hmatch
          cases har : a'[i]? with
          | none => simp [har] at hmatch
          | some av =>
            cases av with
            | ret => simp [har] at hmatch
            | unk => simp [har] at hmatch
            | const r =>
              simp only [har, Bool.and_eq_true] at hmatch
              obtain ⟨hcall, hcont⟩ := hmatch
              obtain ⟨sf, sr, hS0, hsf, hsr⟩ := frameMatches_callCompat hcall hfr
              let κc : Cont := ⟨.dest f0, r, a'.drop e.frame.length, m, e.rets, true⟩
              refine ⟨_, .call κc hk hg rfl rfl rfl rfl, hcode', by simp [hpc', hepc], hentry,
                fun _ => ⟨κc, K, rfl, rfl, rfl⟩, sf, sr ++ rest,
                by rw [hst, hS0, List.append_assoc], hsf,
                .cons hsr hretDrop (fun _ => by
                  show checkNode code c.entries m r.toNat
                    (List.replicate e.rets .unk ++ a'.drop e.frame.length) (.dest f0) = true
                  simpa [checkNode] using hcont) hK⟩
    | [], _, hcheck, _, _ => simp [checkNode] at hcheck
    | .ret :: _, _, hcheck, _, _ => simp [checkNode] at hcheck
    | .unk :: _, _, hcheck, _, _ => simp [checkNode] at hcheck
    | .const _ :: _, .next _ _, hcheck, _, _ => simp [checkNode] at hcheck
    | .const _ :: _, .branch _ _, hcheck, _, _ => simp [checkNode] at hcheck
    | .const _ :: _, .branchTo _ _, hcheck, _, _ => simp [checkNode] at hcheck
    | .const _ :: _, .last _, hcheck, _, _ => simp [checkNode] at hcheck
    | .const _ :: _, .jump _, hcheck, _, _ => simp [checkNode] at hcheck
    | .const _ :: _, .callNext _ _, hcheck, _, _ => simp [checkNode] at hcheck
    | .const _ :: _, .ret, hcheck, _, _ => simp [checkNode] at hcheck
    | .const _ :: _, .pcAt _ _, hcheck, _, _ => simp [checkNode] at hcheck
    | .const _ :: _, .undefined, hcheck, _, _ => simp [checkNode] at hcheck
  | ret =>
    match a, hcheck, hret, hframe with
    | .ret :: a', hcheck, hret, hframe =>
      have h' : byteAt code pc = some (Jinst.toUInt8 .jump) ∧ a'.length = m := by
        simpa [checkNode] using hcheck
      obtain ⟨k, K', rfl, hlive, hrets⟩ := hret List.mem_cons_self
      cases hK with
      | @cons _ _ S1 rest1 hS1 hretk hchk hK' =>
        have hat : Jinst.At n.sevm.code n.pc .jump := by
          rw [hcode, hpc]; exact byteAt_jinst_at h'.1
        obtain ⟨x, hpc', pop, _⟩ := of_jump_run (Cursor.parentStep_jinst edge hat)
        obtain ⟨hx, S', hst, hfr⟩ := Cursor.pop_one_frame hstack hframe pop
        have hx : x = k.tag := hx
        subst hx
        have hlenS : S'.length = k.rets := by
          rw [← List.Forall₂.length_eq hfr, h'.2, hrets]
        refine ⟨_, .ret, hcode', hpc', hchk hlive, ?_, S' ++ S1, rest1,
          by rw [hst, List.append_assoc], ?_, hK'⟩
        · intro hm
          rcases List.mem_append.mp hm with hm | hm
          · simp [List.mem_replicate] at hm
          · exact hretk hm
        · rw [← hlenS]
          exact List.rel_append (frameMatches_unk_length S') hS1
    | [], hcheck, _, _ => simp [checkNode] at hcheck
    | .const _ :: _, hcheck, _, _ => simp [checkNode] at hcheck
    | .unk :: _, hcheck, _, _ => simp [checkNode] at hcheck
  | last l =>
    have hbyte : byteAt code pc = some l.toUInt8 := by simpa [checkNode] using hcheck
    have hat : Linst.At n.sevm.code n.pc l := by
      rw [hcode, hpc]; exact byteAt_linst_at hbyte
    exact (Cursor.parentStep_false_of_linst edge hat).elim
  | pcAt p f =>
    have h' : (bytesAt code pc (Ninst.toBytes (Ninst.reg .pc)) = true ∧ p = pc) ∧
        checkNode code c.entries m (pc + 1) (.const (Nat.toB256 pc) :: a) f = true := by
      simpa [checkNode] using hcheck
    obtain ⟨⟨hbytes, rfl⟩, hrest⟩ := h'
    have hat : Ninst.At n.sevm.code n.pc (.reg .pc) := by
      rw [hcode, hpc]
      exact Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil _) hbytes)
    obtain ⟨hpc', hrun⟩ := Cursor.parentStep_pc edge hat
    rw [hpc] at hrun
    refine ⟨_, .pcAt, hcode', by simp [hpc', hpc], hrest,
      fun hm => hret (by simpa using hm), Nat.toB256 p :: S, rest, ?_,
      List.Forall₂.cons rfl hframe, hK⟩
    rw [pc_stepRun_stack hrun, hstack]
    rfl
  | undefined =>
    have hnone : n.sevm.code.getInst n.pc = none := by
      rw [hcode, hpc]; simpa [checkNode, Option.isNone_iff_eq_none] using hcheck
    exact (Cursor.parentStep_false_of_none edge hnone).elim

/-- **The prefix form of the lift.**  Every node reached along the
same-frame chain of a frame entered at pc `0` of certified bytes — whatever
that frame's eventual outcome — sits at a checked cursor reached from entry
`0` by synthetic steps. -/
theorem cursor_of_parentPrefix {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {F n : Exec.Deriv} (hpc : F.pc = 0) (hcode : F.sevm.code = code)
    (hfork : CoveredFork F.sevm.benvStat.fork) (hp : Exec.Deriv.ParentPrefix F n) :
    ∃ κ, Relation.ReflTransGen (SStep c) (Cursor.start c) κ ∧ CursorOK code c n κ := by
  suffices h : ∀ {F n : Exec.Deriv}, Exec.Deriv.ParentPrefix F n →
      ∀ κ₀, CursorOK code c F κ₀ → CoveredFork F.sevm.benvStat.fork →
      ∃ κ, Relation.ReflTransGen (SStep c) κ₀ κ ∧ CursorOK code c n κ from
    h hp _ (cursor_start hc hpc hcode) hfork
  intro F n hp
  induction hp with
  | refl root => exact fun κ₀ ok _ => ⟨κ₀, .refl, ok⟩
  | step head _ ih =>
    intro κ₀ ok hfork
    obtain ⟨κ₁, hstep, ok₁⟩ := cursor_step hc ok head hfork
    obtain ⟨κ, hreach, ok'⟩ := ih κ₁ ok₁ (by rw [Cursor.parentStep_sevm head]; exact hfork)
    exact ⟨κ, .head hstep hreach, ok'⟩

/-- A cursor-placed node decodes only the frame-spawning instructions the
checker admits: `CALL` and `STATICCALL` (never `DELEGATECALL`, `CALLCODE`,
`CREATE` or `CREATE2`). -/
theorem CursorOK.exec_call_or_staticcall {code : ByteArray} {c : Cert} {n : Exec.Deriv}
    {κ : Cursor} (ok : CursorOK code c n κ) {x : Xinst}
    (hat : Ninst.At n.sevm.code n.pc (.exec x)) : x = .call ∨ x = .staticcall := by
  obtain ⟨hcode, hpc, hcheck, -, -⟩ := ok
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hpc hcheck
  rw [hcode, hpc] at hat
  have hjump : ∀ j : Jinst, byteAt code pc = some j.toUInt8 → False := fun j hb => by
    have hj := byteAt_jinst_at hb
    unfold Jinst.At at hj
    unfold Ninst.At at hat
    rw [hat] at hj
    cases hj
  cases f with
  | next i g =>
    simp only [checkNode, Bool.and_eq_true] at hcheck
    obtain ⟨⟨hbytes, _⟩, hrest⟩ := hcheck
    have hi := Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil i) hbytes)
    unfold Ninst.At at hi hat
    rw [hat] at hi
    cases hi
    cases habs : absNinst (.exec x) a with
    | none => simp [habs] at hrest
    | some a' =>
      obtain ⟨_, out, _, htrans, _⟩ := absNinst_nonpush_spec (fun _ _ h => by cases h) habs
      cases x <;> simp [ninstTransfer] at htrans ⊢
  | last l =>
    have hl := byteAt_linst_at (show byteAt code pc = some l.toUInt8 by
      simpa [checkNode] using hcheck)
    unfold Linst.At at hl
    unfold Ninst.At at hat
    rw [hat] at hl
    cases hl
  | undefined =>
    have hnone : code.getInst pc = none := by
      simpa [checkNode, Option.isNone_iff_eq_none] using hcheck
    unfold Ninst.At at hat
    rw [hat] at hnone
    cases hnone
  | dest g => exact (hjump _ (by simp [checkNode] at hcheck; exact hcheck.1)).elim
  | branch g h =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp at hcheck; exact hcheck.1.1)).elim
    · cases hcheck
  | branchTo g k =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp at hcheck; exact hcheck.1.1.1.1)).elim
    · cases hcheck
  | jump k =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp at hcheck; exact hcheck.1.1.1)).elim
    · cases hcheck
  | callNext k g =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp at hcheck; exact hcheck.1.1.1)).elim
    · cases hcheck
  | ret =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp at hcheck; exact hcheck.1)).elim
    · cases hcheck
  | pcAt p g =>
    simp only [checkNode, Bool.and_eq_true] at hcheck
    have hi := Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil (.reg .pc)) hcheck.1.1)
    unfold Ninst.At at hi hat
    rw [hat] at hi
    cases hi

end Blanc.Lift
