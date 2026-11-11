import Blanc.Lift.ExactWalkCut
import Blanc.ForwardSha256
import Blanc.ForwardStorageAccess
import Jaune.WordFacts
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.ExactWalk
import Blanc.Lift.ExactWalkOps
import Blanc.CommonProofs.Walk
import Blanc.Lift.Loop
import Blanc.CompiledWalkInversion
import Blanc.Lift.InvWalk
import Blanc.Lift.CopyLoop
import Blanc.Lift.Silent
import Blanc.Lift.WalkInvKit
import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.StaticCallStorage
import Blanc.CompiledFixedInvariance
import Blanc.Lift.Quiet
import Blanc.Lift.Check
import Blanc.Lift.MemMap
import Blanc.LadderSem
import Blanc.ExecutionFrames
import Blanc.Lift.Sound
import Blanc.Lift.Reach
import Blanc.Lift.ObservedReach
import Jaune.ExecChronology
import Blanc.Lift.Cursor
import Blanc.Lift.CallRestriction
import Blanc.ExecutionDirectCode
import Blanc.ExecutionNoninterference
import Blanc.ExecutionAdmissionSem
import Blanc.ExecutionTraceFrames
import Blanc.Lift.StaticOnlyFrames
import Blanc.Lift.HistAccessWalk
import Blanc.Lift.HistStaticCall
import Blanc.Lift.HistAccessWalkFacts
import Blanc.Lift.Exact
import Blanc.Lift.SolcStorageReturn
import Blanc.Lift.WalkSteps
import Blanc.DeploymentMessage
import Blanc.DeploymentTouch
import Blanc.Lift.Deploy
import Blanc.TransactionForwardSupport

/-!
# Walk-kit lemmas over lifted programs

Exact-walk, inverse-walk, quiet-function, soundness, cursor and static-call facts for lifted
programs, together with the historical (`…H`) access facts.  Each section names the module whose
vocabulary it extends.  Nothing here mentions a contract.
-/

/-! ## From `Blanc/Lift/ExactWalkCutOps.lean` -/

namespace Blanc.Lift

open Jaune

/-! ## Word arithmetic on small pointers -/

/-! ## What the SHA-256 precompile call leaves -/

theorem BaseRel.trans {b b' b'' : Devm} (h1 : BaseRel b b') (h2 : BaseRel b' b'') :
    BaseRel b b'' :=
  ⟨fun a => (h2.stor a).trans (h1.stor a), fun a => (h2.code a).trans (h1.code a),
    h2.addrs.trans h1.addrs, h2.logs.trans h1.logs, h2.output.trans h1.output,
    h2.error.trans h1.error⟩

/-! ## Exact-run steps -/

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f g : SFunc} {o : Outcome}
  {S : List B256} {M : Mem} {G : Nat}

end Steps

/-! ## Exact cut-run steps -/

section CutSteps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f g : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

/-- An internal call that returns, inside a cut run (the callee runs uncut). -/
theorem rxc_callRet {d : B256} {j : Nat} {D : Devm} (hj : fs[j]? = some g)
    (hcall : SFunc.RunExact fs sevm (St b S M G) g (.returned D))
    (k : SFunc.RunExactCut fs sevm C D f r) :
    SFunc.RunExactCut fs sevm C (St b (d :: S) M (G + 8)) (.callNext j f) r :=
  .callRet d hj popBurnBy_St1 hcall k

end CutSteps

end Blanc.Lift

/-! ## From `Blanc/Lift/ExactWalkOps.lean` -/

namespace Blanc.Lift

open Jaune

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f g : SFunc} {o : Outcome}
  {S : List B256} {M : Mem} {G : Nat}

/-- `EXP` with its exponent's byte charge named. -/
theorem rx_exp' {x y : B256} {c : Nat} (hc : gExp + gExpbyte * y.bytecount = c)
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (B256.bexp x y :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + c)) (.next (.reg .exp) f) o := by
  subst hc
  refine .next ?_ k
  have h := Ninst.runCompiled_reg (sevm := sevm) (r := .exp) (by rintro ⟨⟩)
    (Rinst.runCore_exp_eq_ok (devm := St b (x :: y :: S) M (G + (gExp + gExpbyte * y.bytecount)))
      rfl (by simp only [St.gasLeft, le_add_iff_nonneg_left, zero_le]) hroom)
  simpa only [St, Devm.memory_setMach, Devm.setMach_gasLeft, add_tsub_cancel_right,
    Devm.stateGas_setMach, Devm.setMach_setMach] using h

end Steps

end Blanc.Lift

/-! ## From `Blanc/Lift/InvWalk.lean` -/

namespace Blanc.Lift

open Jaune

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

end Steps

/-! ## Control nodes of cut runs -/

section Control

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f g : SFunc} {r : Seg}

theorem ric_jumpCut {k : Nat} {dd : B256} (hk : k ∈ C)
    (run : SFunc.RunCut fs sevm C (St b (dd :: S) M G) (.jump k) r) :
    ∃ G', r = .at k (St b S M G') := by
  cases run with
  | jumpCut d0 _ h =>
      exact ⟨_, congrArg _ (St.of_pop1 h).2⟩
  | jump _ hkC _ _ _ => exact absurd hk hkC

theorem ric_undefined {devm : Devm} (run : SFunc.RunCut fs sevm C devm .undefined r) : False := by
  cases run

end Control

/-! ## World-touching steps (frozen) -/

section World

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

-- SEGMENT: riSstore
end World

end Blanc.Lift

/-! ## From `Blanc/Lift/InvWalkOps.lean` -/

namespace Blanc.Lift

open Jaune

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-! ## Binary operations -/

/-- `BYTE`, inverted. -/
theorem ri_byte {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .byte) d) :
    ∃ G', d = St b ((List.getD y.toBytes x.toNat 0).toB256 :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := fun x y => (List.getD y.toBytes x.toNat 0).toB256) (Devm.diffBurn_of_applyBinary run)

/-! ## Unary operations -/

/-! ## Environment pushes -/

/-! ## Memory operations -/

/-! ## Naming a successor's top word -/

end Steps

/-! ## The solc word-copy loop, inverted -/

section CopyLoop

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {exit T : SFunc}

end CopyLoop

/-! ## Comparison flags -/

end Blanc.Lift

/-! ## From `Blanc/Lift/InvWalkWorld.lean` -/

namespace Blanc.Lift

open Jaune

/-! ## Trees with no successful run -/

/-! ## Trees that cannot halt -/

/-- A run of an entry in a `NoHaltSet` cannot halt. -/
theorem SFunc.RunP.not_halted_entry {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {S : List Nat} (hS : NoHaltSet fs S = true)
    {k : Nat} (hkS : k ∈ S) {g : SFunc} (hk : fs[k]? = some g)
    {sevm : Sevm} {devm : Devm} {D : Devm} {o : Outcome}
    (run : SFunc.RunP P fs sevm devm g o) (ho : o = .halted D) : False := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.noHalt = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  have ht := closed hkS hk
  exact SFunc.RunP.not_halted hS ht.1 ht.2 run ho

/-! ## Gotos and calls of cut runs -/

section Control

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f g : SFunc} {r : Seg}

end Control

/-! ## Uncut runs

The segment statements are over `SFunc.Run`; `SFunc.Run.cut` moves one to the cut form with
nothing cut, where every `ric_*` lemma applies with `C = []`, and `SFunc.RunCut.uncut` moves
back. -/

/-! ## World steps -/

section World

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- `LOG1`, inverted: the successor's base carries the entry `rx_log1` appends, over the bytes
the window reads; memory is the window read's image. -/
theorem ri_log1 {i sz t : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: sz :: t :: S) M G) (.reg (.log 1)) d) :
    ∃ G', d = St (b.addLog ⟨sevm.currentTarget, [t], (M.read i.toNat sz.toNat).1⟩) S
      (M.read i.toNat sz.toNat).2 G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rw [show (St b (i :: sz :: t :: S) M G).popToNat = .ok (i.toNat, St b (sz :: t :: S) M G)
    from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (sz :: t :: S) M G).popToNat = .ok (sz.toNat, St b (t :: S) M G)
    from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (t :: S) M G).popN ((1 : Fin 5) : Nat) = .ok ([t], St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨_, -, h3⟩
  cases h3
  have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
  refine ⟨s1.gasLeft, ?_⟩
  rw [e1]
  rfl

end World

end Blanc.Lift

/-! ## From `Blanc/Lift/Quiet.lean` -/

namespace Jaune

end Jaune

namespace Blanc.Lift

open Jaune
open scoped LogOutputHinv

/-! ## Log-list equality through an instruction

`Devm.LogsEq` is the relation "same log list".  The walk below keeps the
instruction's entry machine `d` fixed and carries, for the machine reached so far,
the equation `x.logs = d.logs`; each primitive (all `liftMach`-family or meta-only
updates other than `addLog`) extends that equation, so one combinator set proves
`Execution.Rel Devm.LogsEq` for every non-`LOG` regular instruction. -/

namespace LogsWalk

end LogsWalk

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
/-! ## Log-list shape of a recursive instruction

`Xinst.ShapeCovered` (`CommonProofs.lean`) keeps only the instruction frame of the machine
handed to the generic call or create, which does not fix the log list.  `Xinst.ShapeLogs`
is the same covered-fork decomposition with the log list in place of the frame. -/

namespace ShapeLogs

end ShapeLogs

/-! ## Static execution keeps the log list -/

/-- A synthetic tree whose instructions are quiet and whose terminals are not
`SELFDESTRUCT`. -/
def SFunc.quiet : SFunc → Bool
  | .branch f g => f.quiet && g.quiet
  | .branchTo f _ => f.quiet
  | .last l => l != .selfdestruct
  | .next n f => n.quiet && f.quiet
  | .dest f => f.quiet
  | .jump _ => true
  | .callNext _ f => f.quiet
  | .ret => true
  | .pcAt _ f => f.quiet
  | .undefined => true

/-- `S` is closed under the entries referenced by its members, and all of them are quiet. -/
def QuietSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.quiet && g.refs.all (· ∈ S)
    | none => false

theorem PopBurn.world {ws : List B256} {a b : Devm} (h : Devm.PopBurn ws a b) :
    Devm.getStor b = Devm.getStor a ∧ b.logs = a.logs :=
  ⟨funext fun x => Devm.PopBurn.getStor h x, h.logs.symm⟩

theorem Burn.world {a b : Devm} (h : Devm.Burn a b) :
    Devm.getStor b = Devm.getStor a ∧ b.logs = a.logs := by
  refine ⟨funext fun x => ?_, h.logs.symm⟩
  exact getStor_eq_of_state_eq h.state.symm x

end Blanc.Lift

/-! ## From `Blanc/Lift/Sound.lean` -/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-! ### Decided `JUMPI`s -/

/-! ### Folded instructions -/

/-! ### Where a lifted step's child derivation sits -/

/-! ### `PC` nodes -/

/-! ### Checked entries, with or without memory tracking -/

theorem lift_sound {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (exc : Exec 0 sevm pre (.ok post)) :
    SProg.Run c.prog sevm pre post :=
  lift_sound_noStateGas hc hcode hfork.rules_stateGas_none exc

end Blanc.Lift

/-! ## From `Blanc/Lift/Cursor.lean` -/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-! ### One same-frame edge, by instruction kind -/

namespace Cursor

/-! ### Frame bookkeeping for one step -/

end Cursor

/-! ### The cursor theorems -/

theorem cursor_of_parentPrefix {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {F n : Exec.Deriv} (hpc : F.pc = 0) (hcode : F.sevm.code = code)
    (hfork : ShanghaiOnwards F.sevm.benvStat.fork) (hp : Exec.Deriv.ParentPrefix F n) :
    ∃ κ, Relation.ReflTransGen (SStep c) (Cursor.start c) κ ∧ CursorOK code c n κ :=
  cursor_of_parentPrefix_noStateGas hc hpc hcode hfork.rules_stateGas_none hp

end Blanc.Lift

/-! ## From `Blanc/Lift/StaticOnlyFrames.lean` -/

namespace Blanc.Lift

open Jaune

/-- The external-instruction restriction: only `STATICCALL`. -/
def Xinst.isStaticcall : Xinst → Bool
  | .staticcall => true
  | _ => false

/-- A checked certificate whose functions execute only `STATICCALL` permits only
`STATICCALL` at every actual same-frame location, including internal jumps and
returns, of a frame entered at pc `0` of the certified bytes. -/
theorem parentPrefix_exec_staticcall_of_cert {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    {root node : Exec.Deriv} (pc : root.pc = 0) (installed : root.sevm.code = code)
    (fork : ShanghaiOnwards root.sevm.benvStat.fork)
    (chain : Exec.Deriv.ParentPrefix root node)
    {x : Xinst} (instruction : Ninst.At node.sevm.code node.pc (.exec x)) :
    x = .staticcall := by
  obtain ⟨cursor, reachable, ok⟩ := cursor_of_parentPrefix checked pc installed fork chain
  have allowed := ok.execsSatisfy
    (cursor.execsSatisfy_of_reachable only reachable) instruction
  cases x <;> simp_all only [Xinst.isStaticcall, Bool.false_eq_true]

end Blanc.Lift

namespace Blanc

open Jaune

end Blanc

/-! ## From `Blanc/Lift/HistAccessWalkFacts.lean` -/

namespace Blanc.Lift

open Jaune

/-! ## `afterSloadH` projections -/

theorem afterSloadH_accessedAddresses (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).accessedAddresses = base.accessedAddresses := by
  unfold afterSloadH
  split
  · exact afterSload_accessedAddresses sevm base key
  · rfl

/-! ## `afterSstoreH` projections -/

theorem afterSstoreH_getCode (sevm : Sevm) (base : Devm) (key value : B256) (address : Adr) :
    (afterSstoreH sevm base key value).getCode address = base.getCode address := by
  unfold afterSstoreH storageAccessH
  split
  · by_cases h : sevm.currentTarget = address
    · subst h
      show ((((base.withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
      rw [State.setStorVal_get_self]
      rfl
    · show ((((base.withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
      rw [State.setStorVal_get_ne _ h]
      rfl
  · by_cases hw : (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys
    · simp only [hw, ite_true]
      by_cases h : sevm.currentTarget = address
      · subst h
        show ((((base.withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
        rw [State.setStorVal_get_self]
        rfl
      · show ((((base.withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
        rw [State.setStorVal_get_ne _ h]
        rfl
    · simp only [hw, ite_false]
      by_cases h : sevm.currentTarget = address
      · subst h
        show (((((addAccessedStorageKey base _ _).withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
        rw [State.setStorVal_get_self]
        rfl
      · show (((((addAccessedStorageKey base _ _).withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
        rw [State.setStorVal_get_ne _ h]
        rfl

/-! ## The quiet frame theorem without state gas -/

/-- **The quiet frame theorem** over `Ninst.world_of_quietH`: a run of a quiet
tree whose gotos and calls stay in a `QuietSet` keeps every storage map and the
log list, from `rules.stateGas = none` alone. -/
theorem SFunc.Run.world_of_quietH {fs : List SFunc} {S : List Nat}
    (hS : QuietSet fs S = true) {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (hf : f.quiet = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.Run fs sevm devm f o) :
    Devm.getStor (Outcome.devm o) = Devm.getStor devm ∧ (Outcome.devm o).logs = devm.logs := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.quiet = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  have tr : ∀ {a b c : Devm}, (Devm.getStor c = Devm.getStor b ∧ c.logs = b.logs) →
      (Devm.getStor b = Devm.getStor a ∧ b.logs = a.logs) →
      Devm.getStor c = Devm.getStor a ∧ c.logs = a.logs :=
    fun h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  induction run with
  | zero d pop run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact tr (ih hf.1 hrefs.1) (PopBurn.world pop)
  | succ d w hnz pop run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact tr (ih hf.2 hrefs.2) (PopBurn.world pop)
  | toZero d pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      exact tr (ih hf hrefs.2) (PopBurn.world pop)
  | toSucc d w hnz lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact tr (ih ht.1 ht.2) (PopBurn.world pop)
  | last hrun =>
      exact Linst.world_of_ok (by simpa only [ne_eq, quiet, bne_iff_ne] using hf) hrun
  | next hrun run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      exact tr (ih hf.2 hrefs) (Ninst.world_of_quietH hsg hf.1 hrun)
  | dest burn run ih =>
      exact tr (ih hf hrefs) (Burn.world burn)
  | jump d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact tr (ih ht.1 ht.2) (PopBurn.world pop)
  | ret d pop =>
      exact PopBurn.world pop
  | callHalt d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact tr (ih ht.1 ht.2) (PopBurn.world pop)
  | callRet d lookup pop run tail ihRun ihTail =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      simp only [SFunc.quiet] at hf
      exact tr (ihTail hf hrefs.2) (tr (ihRun ht.1 ht.2) (PopBurn.world pop))
  | pcAt hrun _ run ih =>
      simp only [SFunc.quiet] at hf
      simp only [SFunc.refs] at hrefs
      exact tr (ih hf hrefs) (Ninst.world_of_quietH hsg rfl hrun)

end Blanc.Lift

/-! ## From `Blanc/Lift/Deploy.lean` -/

namespace Blanc.Lift

open Jaune

/-! ## Constructor walk steps

`SSTORE`, `CALLVALUE` and `RETURN` in cut runs, and `RETURN` of an arbitrary state in exact runs,
with the halting state named over a variable state (`returnPost`) so that nothing reduces a
concrete memory image. -/

section Steps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

end Steps

/-- **Deploying lifted creation code, exactly.**  If the checked creation certificate's
constructor runs, gas-exactly, from the creation frame's start state to `raw` without error,
and `raw`'s output is admissible code (no `0xEF` prefix, affordable, within the size limit),
then `processCreateMessage msg` succeeds with exactly `liftCreatePost msg.currentTarget raw`. -/
theorem liftCreate_post {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true)
    (msg : Msg) (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hfork : CoveredFork msg.benv.stat.fork) {benv : Benv} {raw : Devm}
    (htransfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (hrun : SProg.RunExact c.prog (initSevm (createSeed msg benv))
      (initDevm (createSeed msg benv)) raw)
    (herror : raw.error = .none) (hprefix : raw.output.head? ≠ some 0xEF)
    (hgas : raw.output.length * gasCodeDeposit ≤ raw.gasLeft)
    (hmax : raw.output.length ≤ msg.benv.stat.rules.code.maxCodeSize) :
    processCreateMessage msg = .ok (liftCreatePost msg.currentTarget raw) := by
  have hstat : (initSevm (createSeed msg benv)).benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  obtain ⟨exc⟩ := lift_exact hc hj (sevm := initSevm (createSeed msg benv)) hcode
    (by rw [hstat]; exact hfork.shanghaiOnwards) hrun
  have hexec : exec (initEvm (createSeed msg benv)) = .ok raw :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩
  have hprocess : processMessage (processCreateMessage.msg msg) = .ok raw :=
    processMessage_ok_of_exec htransfer hcodeAddress hexec herror
      (hfork.cases (motive := fun f => f.ruleSet.settle.touchedSweep = false) rfl rfl rfl rfl)
  have hcharge := processCreateMessage.chargeCodeGas_legacy_eq_ok
    (rules := msg.benv.stat.rules) (d := raw) hfork.rules_stateGas_none hprefix hgas hmax
  exact processCreateMessage_ok_of_processMessage_and_charge msg hprocess herror hcharge

/-- **Deploying lifted creation code.**  If the checked creation certificate's constructor
runs, gas-exactly, from the creation frame's start state to `raw` without error, and `raw`'s
output is admissible code (no `0xEF` prefix, affordable, within the size limit), then
`processCreateMessage msg` succeeds, installs `raw.output` at `msg.currentTarget`, and keeps
the exact normalized storage there. -/
theorem liftCreate_ok {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true)
    (msg : Msg) (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hfork : CoveredFork msg.benv.stat.fork) {benv : Benv} {raw : Devm}
    (htransfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (hrun : SProg.RunExact c.prog (initSevm (createSeed msg benv))
      (initDevm (createSeed msg benv)) raw)
    (herror : raw.error = .none) (hprefix : raw.output.head? ≠ some 0xEF)
    (hgas : raw.output.length * gasCodeDeposit ≤ raw.gasLeft)
    (hmax : raw.output.length ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = raw.output ∧
      Devm.getStor post msg.currentTarget =
        ({ raw.state.get msg.currentTarget with code := ⟨⟨raw.output⟩⟩ } : Acct).clearIfEmpty.stor ∧
      post.error = .none := by
  refine ⟨_, liftCreate_post hc hj msg hcodeAddress hcode hfork htransfer hrun herror hprefix
    hgas hmax, ?_, ?_, ?_⟩
  · unfold Devm.getCode Devm.getAcct
    rw [(liftCreatePost_facts _ raw).2.2.1]
    simp only [Acct.clearIfEmpty_code, ByteArray.toList_eq_toList_data]
  · unfold Devm.getStor Devm.getAcct
    rw [(liftCreatePost_facts _ raw).2.2.1]
  · rw [(liftCreatePost_facts _ raw).1]
    exact herror

end Blanc.Lift
