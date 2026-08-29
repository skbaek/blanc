-- Tactics.lean : tactic machinery and the statically quoted lemmas it requires.

import Blanc.CommonCore
import Blanc.ProofRecipesGenerated

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

section

open Lean.Elab.Tactic
open Lean.Parser.Tactic
open Lean.Elab.Term
open Lean
open Qq

/-! ## Goal-time proof recipe lookup

`blanc_suggest` deliberately matches raw declaration names.  Several relations
it recognizes live downstream of this shared tactic module, so typed quotations
would create an import cycle.  The tactic only reads the target and local
context, filters the generated registry, and logs advice; it never assigns a
metavariable or replaces a goal. -/

def proofRecipeHeadName? : Lean.Expr → Option Lean.Name
  | .const name _ => some name
  | .app fn _ => proofRecipeHeadName? fn
  | .mdata _ expr => proofRecipeHeadName? expr
  | _ => none

def proofRecipeContainsName (needle : Lean.Name) : Lean.Expr → Bool
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false
  | .const name _ => name == needle
  | .app fn arg =>
      proofRecipeContainsName needle fn || proofRecipeContainsName needle arg
  | .lam _ type body _ | .forallE _ type body _ =>
      proofRecipeContainsName needle type || proofRecipeContainsName needle body
  | .letE _ type value body _ =>
      proofRecipeContainsName needle type ||
        proofRecipeContainsName needle value ||
        proofRecipeContainsName needle body
  | .mdata _ expr | .proj _ _ expr => proofRecipeContainsName needle expr

def proofRecipeExprHasFVarOrMVar : Lean.Expr → Bool
  | .fvar _ | .mvar _ => true
  | .bvar _ | .sort _ | .const _ _ | .lit _ => false
  | .app fn arg =>
      proofRecipeExprHasFVarOrMVar fn || proofRecipeExprHasFVarOrMVar arg
  | .lam _ type body _ | .forallE _ type body _ =>
      proofRecipeExprHasFVarOrMVar type || proofRecipeExprHasFVarOrMVar body
  | .letE _ type value body _ =>
      proofRecipeExprHasFVarOrMVar type ||
        proofRecipeExprHasFVarOrMVar value ||
        proofRecipeExprHasFVarOrMVar body
  | .mdata _ expr | .proj _ _ expr => proofRecipeExprHasFVarOrMVar expr

def proofRecipeIsDevmWithUpdaterName : Lean.Name → Bool
  | .str pre suffix =>
      pre == `Jaune.Devm && suffix.startsWith "with"
  | _ => false

def proofRecipeContainsDevmUpdater : Lean.Expr → Bool
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false
  | .const name _ =>
      name == `Jaune.Devm.setMach ||
        name == `Jaune.Devm.setMeta ||
        name == `Jaune.Devm.setWorld ||
        proofRecipeIsDevmWithUpdaterName name
  | .app fn arg =>
      proofRecipeContainsDevmUpdater fn || proofRecipeContainsDevmUpdater arg
  | .lam _ type body _ | .forallE _ type body _ =>
      proofRecipeContainsDevmUpdater type || proofRecipeContainsDevmUpdater body
  | .letE _ type value body _ =>
      proofRecipeContainsDevmUpdater type ||
        proofRecipeContainsDevmUpdater value ||
        proofRecipeContainsDevmUpdater body
  | .mdata _ expr | .proj _ _ expr => proofRecipeContainsDevmUpdater expr

def proofRecipeEqLhs? : Lean.Expr → Option Lean.Expr
  | .app (.app (.app (.const name _) _) lhs) _ =>
      if name == `Eq then some lhs else none
  | .mdata _ expr => proofRecipeEqLhs? expr
  | _ => none

def proofRecipeIsDirectDevmProjectionName (name : Lean.Name) : Bool :=
  name == `Jaune.Devm.mach ||
    name == `Jaune.Devm.meta ||
    name == `Jaune.Devm.world ||
    name == `Jaune.Devm.stack ||
    name == `Jaune.Devm.memory ||
    name == `Jaune.Devm.gasLeft ||
    name == `Jaune.Devm.logs ||
    name == `Jaune.Devm.refundCounter ||
    name == `Jaune.Devm.output ||
    name == `Jaune.Devm.accountsToDelete ||
    name == `Jaune.Devm.returnData ||
    name == `Jaune.Devm.error ||
    name == `Jaune.Devm.accessedAddresses ||
    name == `Jaune.Devm.accessedStorageKeys ||
    name == `Jaune.Devm.createdAccounts ||
    name == `Jaune.Devm.state ||
    name == `Jaune.Devm.transientStorage

def proofRecipeDirectDevmProjectionSource? : Lean.Expr → Option Lean.Expr
  | .proj typeName _ source =>
      if typeName == `Jaune.Devm then some source else none
  | .app (.const name _) source =>
      if proofRecipeIsDirectDevmProjectionName name then some source else none
  | .mdata _ expr => proofRecipeDirectDevmProjectionSource? expr
  | _ => none

def proofRecipeIsDevmProjectionBridge (target : Lean.Expr) : Bool :=
  match proofRecipeEqLhs? target with
  | some lhs =>
      match proofRecipeDirectDevmProjectionSource? lhs with
      | some source => proofRecipeContainsDevmUpdater source
      | none => false
  | none => false

def proofRecipeContainsClosedCompileShapeByteSize : Lean.Expr → Bool
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => false
  | .app fn arg =>
      match fn, arg with
      | .const byteSizeName _, .app (.const compileShapeName _) func =>
          if byteSizeName == `Blanc.Func.CompileShape.byteSize &&
              compileShapeName == `Blanc.Func.compileShape then
            !proofRecipeExprHasFVarOrMVar func
          else
            proofRecipeContainsClosedCompileShapeByteSize fn ||
              proofRecipeContainsClosedCompileShapeByteSize arg
      | _, _ =>
          proofRecipeContainsClosedCompileShapeByteSize fn ||
            proofRecipeContainsClosedCompileShapeByteSize arg
  | .lam _ type body _ | .forallE _ type body _ =>
      proofRecipeContainsClosedCompileShapeByteSize type ||
        proofRecipeContainsClosedCompileShapeByteSize body
  | .letE _ type value body _ =>
      proofRecipeContainsClosedCompileShapeByteSize type ||
        proofRecipeContainsClosedCompileShapeByteSize value ||
        proofRecipeContainsClosedCompileShapeByteSize body
  | .mdata _ expr | .proj _ _ expr =>
      proofRecipeContainsClosedCompileShapeByteSize expr

def proofRecipeIsByteSizeComposition (target : Lean.Expr) : Bool :=
  let head := proofRecipeHeadName? target
  (head == some `Eq || head == some `Ne ||
    head == some `LE.le || head == some `LT.lt) &&
    proofRecipeContainsClosedCompileShapeByteSize target

def proofRecipeHasPremiseHead (needle : Lean.Name) : Lean.Expr → Bool
  | .forallE _ domain body _ =>
      proofRecipeHeadName? domain == some needle ||
        proofRecipeHasPremiseHead needle body
  | .letE _ _ _ body _ | .mdata _ body =>
      proofRecipeHasPremiseHead needle body
  | _ => false

def proofRecipeLocalTypeCount (needle : Lean.Name) : TacticM Nat := do
  let context ← Lean.MonadLCtx.getLCtx
  let mut count := 0
  for declaration in context do
    unless declaration.isImplementationDetail do
      let type ← Lean.instantiateMVars declaration.type
      if proofRecipeHeadName? type == some needle then
        count := count + 1
  return count

def proofRecipeBVarOccurrenceCount (needle : Nat) : Lean.Expr → Nat
  | .bvar index => if index == needle then 1 else 0
  | .app fn arg =>
      proofRecipeBVarOccurrenceCount needle fn +
        proofRecipeBVarOccurrenceCount needle arg
  | .lam _ type body _ | .forallE _ type body _ =>
      proofRecipeBVarOccurrenceCount needle type +
        proofRecipeBVarOccurrenceCount (needle + 1) body
  | .letE _ type value body _ =>
      proofRecipeBVarOccurrenceCount needle type +
        proofRecipeBVarOccurrenceCount needle value +
        proofRecipeBVarOccurrenceCount (needle + 1) body
  | .mdata _ expr | .proj _ _ expr =>
      proofRecipeBVarOccurrenceCount needle expr
  | _ => 0

def proofRecipeHasRepeatedClosedLetSubject : Lean.Expr → Bool
  | .app fn arg =>
      proofRecipeHasRepeatedClosedLetSubject fn ||
        proofRecipeHasRepeatedClosedLetSubject arg
  | .lam _ type body _ | .forallE _ type body _ =>
      proofRecipeHasRepeatedClosedLetSubject type ||
        proofRecipeHasRepeatedClosedLetSubject body
  | .letE _ type value body _ =>
      (!proofRecipeExprHasFVarOrMVar value &&
          proofRecipeBVarOccurrenceCount 0 body > 1) ||
        proofRecipeHasRepeatedClosedLetSubject type ||
        proofRecipeHasRepeatedClosedLetSubject value ||
        proofRecipeHasRepeatedClosedLetSubject body
  | .mdata _ expr | .proj _ _ expr =>
      proofRecipeHasRepeatedClosedLetSubject expr
  | _ => false

def proofRecipeTriggerMatches (target : Lean.Expr) (trigger : String) : TacticM Bool := do
  let head := proofRecipeHeadName? target
  match trigger with
  | "goal-head:Func.RunCompiled" => return head == some `Blanc.Func.RunCompiled
  | "goal-head:Func.RunCompiledTo" => return head == some `Blanc.Func.RunCompiledTo
  | "goal-head:Func.ExecTo" => return head == some `Blanc.Func.ExecTo
  | "goal-head:Func.ExecWitness" => return head == some `Blanc.Func.ExecWitness
  | "goal-head:Func.ExecSat" => return head == some `Blanc.Func.ExecSat
  | "goal-head:Prog.ExecSat" => return head == some `Blanc.Prog.ExecSat
  | "goal-head:Line.Inv" => return head == some `Blanc.Line.Inv
  | "goal-head:Ninst.Inv" => return head == some `Blanc.Ninst.Inv
  | "goal-head:Rinst.Inv" => return head == some `Blanc.Rinst.Inv
  | "goal-head:Func.Inv" => return head == some `Blanc.Func.Inv
  | "implication-premise:Line.Run" =>
      return proofRecipeHasPremiseHead `Blanc.Line.Run target
  | "implication-premise:Func.Run" =>
      return proofRecipeHasPremiseHead `Blanc.Func.Run target
  | "goal-shape:stack-prefix-line-run" =>
      return proofRecipeContainsName `Blanc.Pref target &&
        proofRecipeContainsName `Blanc.Line.Run target
  | "context-shape:intermediate-devm" =>
      return (← proofRecipeLocalTypeCount `Jaune.Devm) > 2
  | "goal-shape:devm-update-projection" =>
      return proofRecipeIsDevmProjectionBridge target
  | "goal-shape:successor-projection" =>
      return head == some `Eq &&
        proofRecipeContainsName `Jaune.Devm.setMach target &&
        !proofRecipeIsDevmProjectionBridge target
  | "goal-shape:compileshape-bytesize" =>
      return proofRecipeIsByteSizeComposition target
  | "goal-shape:selector-separation" =>
      return proofRecipeContainsName `Blanc.selector target
  | "goal-shape:fixed-byte-offset" =>
      return head == some `Blanc.Mem.Wf || head == some `Blanc.Mem.Reads
  | "goal-shape:frame-root-carrying" =>
      return proofRecipeContainsName `Blanc.rootedRunCompiledTo target ||
        proofRecipeContainsName `Blanc.ninstAllChildRoots target ||
        proofRecipeContainsName `Blanc.Exec.rawFrameRoots target ||
        proofRecipeContainsName `Blanc.Exec.rawFrameDescendants target
  | "goal-shape:message-execution-settlement" =>
      return proofRecipeContainsName `Jaune.processMessage target &&
        (proofRecipeContainsName `Jaune.exec target ||
          proofRecipeContainsName `Jaune.initEvm target)
  | "goal-shape:devm-common-update-law" =>
      return proofRecipeContainsName `Jaune.Devm.memWrite target ||
        proofRecipeContainsName `Jaune.addAccessedStorageKey target ||
        proofRecipeContainsName `Jaune.Devm.setStorVal target
  | "goal-shape:terminal-return-revert" =>
      return head == some `Blanc.Func.RunCompiledTo &&
        (proofRecipeContainsName `Jaune.Linst.ret target ||
          proofRecipeContainsName `Jaune.Linst.rev target)
  | "goal-shape:full-length-slice" =>
      return proofRecipeContainsName `Jaune.List.sliceD target
  | "goal-shape:runcompiled-family-compression" =>
      return head == some `Blanc.Func.RunCompiled ||
        head == some `Blanc.Func.RunCompiledTo
  | "goal-shape:shared-subject-kernel-decision" =>
      return proofRecipeHasRepeatedClosedLetSubject target
  | _ => return false

def proofRecipeMatches (target : Lean.Expr)
    (recipe : ProofRecipes.Recipe) : TacticM Bool := do
  for trigger in recipe.triggers do
    if ← proofRecipeTriggerMatches target trigger then
      return true
  return false

elab "blanc_suggest" : tactic =>
  withMainContext do
    let target ← Lean.instantiateMVars (← getMainTarget)
    let mut found := false
    for recipe in ProofRecipes.recipes do
      if ← proofRecipeMatches target recipe then
        found := true
        let symbols := String.intercalate ", " recipe.symbols
        Lean.logInfo m!"[proof-recipe:{recipe.id}] {recipe.preferredPath}\n\
          Registered symbols: {symbols}\n\
          Boundary: {recipe.boundary}"
    unless found do
      Lean.logInfo "blanc_suggest: no matching proof recipe\n\
        Declaration discovery: consult docs/COMMON_API.md before adding a \
        contract-local helper."

def String.toSyntax (s : String) : Lean.Syntax :=
  Lean.Syntax.ident Lean.SourceInfo.none s.toRawSubstring
    (Lean.Name.str Lean.Name.anonymous s) []

def Strings.intro (ss : List String) : Lean.Elab.Tactic.TacticM Unit := do
  let ids : Lean.TSyntaxArray [`ident, `Lean.Parser.Term.hole] :=
    ⟨ss.map (λ s => {raw := String.toSyntax s})⟩
  let fvars ← liftMetaTacticAux fun mvarId => do
    let (fvars, mvarId) ← mvarId.introN ids.size (ids.map getNameOfIdent').toList
    return (fvars, [mvarId])
  withMainContext do
    for stx in ids, fvar in fvars do
      Lean.Elab.Term.addLocalVarInfo stx (Lean.mkFVar fvar)

def matchingName (x : Lean.Expr) (d : Lean.LocalDecl) :
    Lean.Elab.Tactic.TacticM (Option Lean.Name) := do
  if (← Lean.Meta.isExprDefEq x d.toExpr) -- Check if type equals goal type.
  then return some d.userName -- If equal, success!
  else return none

def subscriptSuccAux : List Char → Option (List Char)
| [] => ['₁']
| '₀' :: cs => '₁' :: cs
| '₁' :: cs => '₂' :: cs
| '₂' :: cs => '₃' :: cs
| '₃' :: cs => '₄' :: cs
| '₄' :: cs => '₅' :: cs
| '₅' :: cs => '₆' :: cs
| '₆' :: cs => '₇' :: cs
| '₇' :: cs => '₈' :: cs
| '₈' :: cs => '₉' :: cs
| '₉' :: cs =>
  match subscriptSuccAux cs with
  | some cs' => '₀' :: cs'
  | none => none
| _ => none

def subscriptSucc (cs : List Char) : Option (List Char) :=
match subscriptSuccAux cs.reverse with
| none => none
| some cs' => some cs'.reverse

def findSubscript (x : Lean.Expr) : Lean.Elab.Tactic.TacticM String := do
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    let some nm ← ctx.findDeclM? (matchingName x) | failure
    match nm with
    | Lean.Name.str _ s =>
      match s.toList with
      | 's' :: cs =>
        match subscriptSucc cs with
        | none => failure
        | some cs' => pure (String.ofList cs')
      | _ => failure
    | _ => failure

lemma of_run_prepend {c e s r} :
   ∀ p q, Func.Run c e s (p +++ q) r →
   ∃ s', (Line.Run e s p s' ∧ Func.Run c e s' q r)
| [], _, h => ⟨s, cst, h⟩
| (_ :: p), q, (@Func.Run.next c e _ i _ _ _ h h') => by
  let ⟨s', hp, hq⟩ := of_run_prepend p q h'
  refine' ⟨s', Line.Run.cons h hp, hq⟩

lemma run_prepend_elim (φ : Prop) (l) {p} {c e} {s r}
    (h : ∀ s', Line.Run e s l s' → Func.Run c e s' p r → φ)
    (h' : Func.Run c e s (l +++ p) r) : φ := by
  rcases of_run_prepend _ _ h' with ⟨s', hs, hs'⟩; apply h s' hs hs'

lemma Line.of_run_cons {e s i l s''} (h : Line.Run e s (i :: l) s'') :
    ∃ s', Ninst.Run e s i s' ∧ Line.Run e s' l s'' := by
  cases h
  refine' ⟨_, asm, asm⟩

lemma of_run_append  {e s} (a) {b s''} (h : Line.Run e s (a ++ b) s'') :
    ∃ s', Line.Run e s a s' ∧ Line.Run e s' b s'' := by
  induction a generalizing s with
  | nil => refine' ⟨s, cst, h⟩
  | cons i a ih =>
    rcases Line.of_run_cons h with ⟨s0, hi, h_ab⟩
    rcases ih h_ab with ⟨s1, ha, hb⟩
    refine ⟨s1, Line.Run.cons hi ha, hb⟩

lemma run_append_elim (φ : Prop) (l) {l'} {e} {s s''}
    (h : ∀ s', Line.Run e s l s' → Line.Run e s' l' s'' → φ)
    (h' : Line.Run e s (l ++ l') s'') : φ := by
  rcases of_run_append _ h' with ⟨s', hs, hs'⟩; apply h s' hs hs'

elab "func_execute_with" e:term : tactic =>
  withMainContext do
    let x ← elabTermForApply e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Func.Run _ _ $s _ _ → $c) =>
      let ss ← findSubscript s
      Lean.Expr.apply (Lean.mkApp2 q(@run_prepend_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]

def Func.take : Nat → Q(Func) → TacticM Q(Line)
| 0, _ => pure q([] : Line)
| n + 1, p => do
  let p' : Q(Func) ← Lean.Meta.whnf p
  match p' with
  | ~q(Func.next $i $q) =>
    let x ← Func.take n q
    pure q($i :: $x)
  | _ => failure

elab "func_execute" e:num : tactic =>
  withMainContext do
    let n := Lean.TSyntax.getNat e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Func.Run _ _ $s $p _ → $c) =>
      let ss ← findSubscript s
      let x ← Func.take n p
      Lean.Expr.apply (Lean.mkApp2 q(@run_prepend_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]

/-- Public observation-preservation shape for a straight-line fragment.  It is
the successful-run projection of the canonical relational effect idiom. -/
def Line.Inv {ξ : Type} (f : Devm → ξ) (l : Line) : Prop :=
  ∀ {e s s'}, Line.Run e s l s' → f s = f s'

lemma Line.of_inv {ξ : Type} {e s s'} (r : Devm → ξ) {l : Line} :
  Line.Inv r l → Line.Run e s l s' → r s = r s' := λ h => h

/-- Successful-run observation invariant for one nonterminal instruction;
retained for the `line_inv`/`func_inv` API built over relational masters. -/
def Ninst.Inv {ξ : Type} (r : Devm → ξ) (i : Ninst) : Prop :=
  ∀ {e s s'}, Ninst.Run e s i s' → r s = r s'

lemma Line.nil_inv {ξ : Type} {f : Devm → ξ} : Line.Inv f [] := by
  intros e s s' h; cases h; rfl

lemma Line.cons_inv {ξ : Type} {f : Devm → ξ} {i l} :
    Ninst.Inv f i → Line.Inv f l → Line.Inv f (i :: l) := by
  intros h0 h1 e s s'' h2
  rcases Line.of_run_cons h2 with ⟨s', h3, h4⟩
  apply Eq.trans (h0 h3) (h1 h4)

class Ninst.Hinv {ξ : Type} (f : Devm → ξ) (i : Ninst) where (inv : Ninst.Inv f i)

def Ninst.invExpr (ξx fx : Lean.Expr) (ix : Q(Ninst)) : Lean.Elab.Tactic.TacticM Lean.Expr := do
  let x ← Lean.Meta.synthInstance <| Lean.mkApp3 q(@Ninst.Hinv) ξx fx ix
  pure <| Lean.mkApp4 q(@Ninst.Hinv.inv) ξx fx ix x

def instInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t ← Lean.Elab.Tactic.getMainTarget
  have t' : Q(Prop) := t
  match t' with
  | ~q(@Ninst.Inv $ξx $fx $ix) =>
    let x ← Ninst.invExpr ξx fx ix
    Lean.Elab.Tactic.closeMainGoal `tacName x
  | _ => dbg_trace "Not a Ninst.Inv goal"

def lineNilInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Expr.apply q(@Line.nil_inv)

def lineConsInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Expr.apply q(@Line.cons_inv)

partial def lineInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t : Q(Prop) ← Lean.Elab.Tactic.getMainTarget
  match t with
  | ~q(@Line.Inv $ξx $fx $lx) =>
    let lx' : Q(Line) ← Lean.Meta.whnf lx
    match lx' with
    | ~q([]) => lineNilInv
    | _ => lineConsInv; instInv; lineInv
  | _ => dbg_trace "Not a Line.Inv goal"

elab "line_inv" : tactic => lineInv

def Strings.toName : List String → Lean.Name
  | [] => `Blanc
  | s :: ss => Lean.Name.str (Strings.toName ss) s

def Strings.toExpr (l : List String) : Lean.Expr :=
  Lean.Expr.const (Strings.toName l.reverse) []

def String.toExpr (s : String) : Lean.Expr :=
  Strings.toExpr <| String.splitOn s "."

def String.apply (s : String): Lean.Elab.Tactic.TacticM Unit :=
  Lean.Expr.apply <| String.toExpr s

/-- Public program-level invariant consumed by solvency proofs; unlike
`Execution.Rel`, it records only successful `Func.Run` executions. -/
def Func.Inv {ξ : Type} (f : Devm → ξ) (g : Devm → ξ) (p : Func) : Prop :=
  ∀ {c sevm s r}, Func.Run c sevm s p r → f s = g r

/-- Successful terminal-instruction projection used to assemble `Func.Inv`;
outcome-aware preservation is stated canonically with `Execution.Rel`. -/
def Linst.Inv {ξ : Type} (f : Devm → ξ) (g : Devm → ξ) (o : Linst) : Prop :=
  ∀ {e s r}, Linst.Run e s o (.ok r) → f s = g r

class Linst.Hinv {ξ : Type} (f : Devm → ξ) (g : Devm → ξ) (o : Linst) where (inv : Linst.Inv f g o)

def Linst.invExpr (ξx fx gx : Lean.Expr) (ox : Q(Linst)) :
    Lean.Elab.Tactic.TacticM Lean.Expr := do
  let x ← Lean.Meta.synthInstance <| Lean.mkApp4 q(@Linst.Hinv) ξx fx gx ox
  pure <| Lean.mkApp5 q(@Linst.Hinv.inv) ξx fx gx ox x

def hopInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t ← Lean.Elab.Tactic.getMainTarget
  have t' : Q(Prop) := t
  match t' with
  | ~q(@Linst.Inv $ξx $fx $gx $ox) =>
    let x ← Linst.invExpr ξx fx gx ox
    Lean.Elab.Tactic.closeMainGoal `tacName x
  | _ => dbg_trace "Not a Linst.Inv goal"

lemma Devm.Burn.getBal {s s' : Devm} (h : Devm.Burn s s') (a : Adr) : s'.getBal a = s.getBal a := by
  simp [Devm.getBal, Devm.getAcct]; rw [h.state]

lemma Devm.PopBurn.getBal {xs} {s s' : Devm} (h : Devm.PopBurn xs s s') (a : Adr) : s'.getBal a = s.getBal a := by
  simp [Devm.getBal, Devm.getAcct]; rw [h.state]

lemma Func.of_inv {ξ : Type} {e s r} (f g) {p : Func} :
  @Func.Inv ξ f g p → Func.Run c e s p r → f s = g r := λ h => h

lemma last_inv {ξ} {f g o} (h : Linst.Inv f g o) :
    @Func.Inv ξ f g (Func.last o) := by
  intros c e s r h'; cases h'; rename_i hl
  apply h hl

lemma prepend_inv {ξ : Type} {f g} {l p} (hl : Line.Inv f l)
    (hp : Func.Inv f g p) : @Func.Inv ξ f g (l +++ p) := by
  intros c e s r h; rcases of_run_prepend _ _ h with ⟨s', hl', hp'⟩
  apply Eq.trans (hl hl') (hp hp')

lemma of_run_branch {c e s r} {p q : Func} (h : Func.Run c e s (Func.branch p q) r) :
    (∃ s', Devm.PopBurn [0] s s' ∧ Func.Run c e s' p r) ∨
    (∃ w s' s'', w ≠ 0 ∧ Devm.PopBurn [w] s s' ∧ Devm.Burn s' s'' ∧ Func.Run c e s'' q r) := by
  cases h with
  | zero h1 h2 => left; exact ⟨_, h1, h2⟩
  | succ h1 h2 h3 h4 => right; exact ⟨_, _, _, h1, h2, h3, h4⟩

class PopBurn.Inv {ξ} (f : Devm → ξ) : Prop where
  (inv : ∀ {xs s s'}, Devm.PopBurn xs s s' → f s = f s')

class Burn.Inv {ξ} (f : Devm → ξ) : Prop where
  (inv : ∀ {s s'}, Devm.Burn s s' → f s = f s')

instance : PopBurn.Inv Devm.getBal := ⟨by
  intros xs s s' h
  funext a
  exact (Devm.PopBurn.getBal h a).symm
⟩

instance : Burn.Inv Devm.getBal := ⟨by
  intros s s' h
  funext a
  exact (Devm.Burn.getBal h a).symm
⟩

lemma branch_inv {ξ : Type} {f : Devm → ξ} {g} {p q}
    [h_pop : PopBurn.Inv f] [h_burn : Burn.Inv f]
    (hp : Func.Inv f g p) (hq : Func.Inv f g q) :
    @Func.Inv ξ f g (Func.branch p q) := by
  intros c e s r h_run
  rcases of_run_branch h_run with ⟨s', h_pb, h_run⟩ | ⟨w, s', s'', h_ne, h_pb, h_b, h_run⟩
  · rw [h_pop.inv h_pb]
    exact hp h_run
  · rw [h_pop.inv h_pb]
    rw [h_burn.inv h_b]
    exact hq h_run

lemma next_inv {ξ : Type} {f : Devm → ξ} {g} {i p}
    (h : Ninst.Inv f i) (h' : Func.Inv f g p) : Func.Inv f g (i ::: p) := by
  intros c e s r h_run
  cases h_run; rename_i hi hp
  rw [h hi, h' hp]

/-- Walk a `Func` and assemble its `Func.Inv` out of `prepend_inv`,
`next_inv`, `branch_inv` and `last_inv`.

The `Func.call` arm is a refusal, not an omission, and the refusal is the whole
content of that case.  `Func.Inv` quantifies over the context list `c`, so
`Func.Run c sevm s (.call k) r` runs whatever `c[k]?` happens to be: at this
altitude the callee is arbitrary and no rule can discharge the goal.  A property
of a `Func` that tail-jumps has to be stated with the context fixed, or factored
through the entry it jumps to.

Every shape it cannot handle raises.  It used to log the shape and return, which
made it a tactic that reported success without applying a rule -- the enclosing
`by func_inv` then failed on the leftover goal, so the message was noise in
front of an unrelated-looking error rather than an answer. -/
partial def funcInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let t : Q(Prop) ← Lean.Elab.Tactic.getMainTarget
    match t with
    | ~q(@Func.Inv $ξx $fx $gx $px) =>
      match px with
      | ~q(_ +++ _) => Lean.Expr.apply q(@prepend_inv); lineInv; funcInv
      | _ =>
        let px' : Q(Func) ← Lean.Meta.whnf px
        match px' with
        | ~q(Func.next _ _) => Lean.Expr.apply q(@next_inv); instInv; funcInv
        | ~q(Func.last _) =>   Lean.Expr.apply q(@last_inv); hopInv
        | ~q(Func.branch _ _) => Lean.Expr.apply q(@branch_inv); funcInv; funcInv
        | ~q(Func.call $kx) => do
          let pp ← Lean.Meta.ppExpr kx
          Lean.throwError m!"func_inv: no rule for the tail jump `Func.call \
            {pp}`. `Func.Inv` quantifies over the context list, so the entry \
            this jumps to is arbitrary here; state the property with the \
            context fixed, or factor it through that entry."
        | _ => do
          let pp ← Lean.Meta.ppExpr px'
          Lean.throwError m!"func_inv: no rule for{Lean.indentD pp}"
    | _ =>
      Lean.throwError m!"func_inv: the goal is not a `Func.Inv`{Lean.indentExpr t}"

elab "func_inv" : tactic => funcInv

end

lemma apply_univ {ξ : Type} (φ : ξ → Prop) (x : ξ) (h : ∀ x, φ x) : φ x := h x

section

open Lean.Elab.Tactic
open Lean.Parser.Tactic
open Lean.Elab.Term
open Lean
open Qq

inductive Stack.Nth : Nat → B256 → Stack → Prop
  | head : ∀ x xs, Nth 0 x (x :: xs)
  | tail : ∀ m x y xs, Nth m x xs → Nth (m + 1) x (y :: xs)

syntax "show_nth" : tactic
macro_rules
  | `(tactic| show_nth) =>
    `(tactic| first | apply Stack.Nth.head | (apply Stack.Nth.tail ; show_nth))

def showNthAt : Nat → Lean.Elab.Tactic.TacticM Unit
  | 0 => Blanc.String.apply "Stack.Nth.head"
  | n +1 => do Blanc.String.apply "Stack.Nth.tail"; showNthAt n

def showSwapAt : Nat → Lean.Elab.Tactic.TacticM Unit
  | 0 => Blanc.String.apply "Stack.swapCore_zero"
  | n + 1 => do Blanc.String.apply "Stack.swapCore_succ"; showSwapAt n

def fail {ξ} (s : String) : Lean.Elab.Tactic.TacticM ξ := do
  dbg_trace s; failure

def getSwapAux (xx : Q(B256)) : Nat → Q(Stack) → Lean.Elab.Tactic.TacticM (Q(B256) × Q(Stack))
  | 0, ~q($yx :: $lx) => pure (yx, q($xx :: $lx))
  | n + 1, ~q($yx :: $lx) => do
    let (zx, lx') ← getSwapAux xx n lx
    pure (zx, q($yx :: $lx'))
  | _, _ =>fail "getSwapAux : cannot decompose list"

def getSwap (n : Nat) : Q(Stack) → Lean.Elab.Tactic.TacticM Q(Stack)
  | ~q($xx :: $lx) => do
    let (yx, lx') ← getSwapAux xx n lx
    pure q($yx :: $lx')
  | _ => fail "getSwap : cannot decompose list"

def getTake : Nat → Q(Stack) → Lean.Elab.Tactic.TacticM Q(Stack)
  | 0, _ => pure q([])
  | _ + 1, ~q([]) => fail "cannot take from empty list"
  | n + 1, ~q($xx :: $lx) => do
    let lx' ← getTake n lx
    pure q($xx :: $lx')
  | _, _ => fail "get take : cannot decompose list"

partial def linePrefix : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t : Q(Prop) ← Lean.Elab.Tactic.getMainTarget
  match t with
  | ~q(∀ s : Devm, ($px <<+ s.stack) → Line.Run _ s $lx _ → _) =>
    let lx' : Q(Line) ← Lean.Meta.whnf lx
    match lx' with
    | ~q([]) => Blanc.String.apply "Line.spx_unwrap"
    | ~q($ix :: _) =>
      match ix with
      | ~q(Ninst.dup $nx) =>
        let n ← unsafe Lean.Meta.evalExpr (Fin 16) q(Fin 16) nx
        Blanc.String.apply "Line.spx_dup"; showNthAt n.val
      | ~q(Ninst.log $nx) =>
        let n ← unsafe Lean.Meta.evalExpr (Fin 5) q(Fin 5) nx
        let x ← getTake (n.val + 2) px
        Lean.Expr.apply <| Lean.mkApp (Blanc.String.toExpr "Line.spx_log") x
        Lean.Elab.Tactic.evalRefl Lean.Syntax.missing
      | ~q(Ninst.swap $nx) =>
        let n ← unsafe Lean.Meta.evalExpr (Fin 16) q(Fin 16) nx
        let x ← getSwap n.val px
        Lean.Expr.apply <| Lean.mkApp (Blanc.String.toExpr "Line.spx_swap") x
        showSwapAt n.val
      | ~q(Ninst.pushB256 _) => Blanc.String.apply "Line.spx_pushB256"
      | ~q(Ninst.push _ _) => Blanc.String.apply "Line.spx_push"
      | ~q(Ninst.sub) => Blanc.String.apply "Line.spx_sub"
      | ~q(Ninst.add) => Blanc.String.apply "Line.spx_add"
      | ~q(Ninst.pop) => Blanc.String.apply "Line.spx_pop"
      | ~q(Ninst.sstore) => Blanc.String.apply "Line.spx_sstore"
      | ~q(Ninst.mstore) => Blanc.String.apply "Line.spx_mstore"
      | ~q(Ninst.lt) => Blanc.String.apply "Line.spx_lt"
      | ~q(Ninst.gt) => Blanc.String.apply "Line.spx_gt"
      | ~q(Ninst.eq) => Blanc.String.apply "Line.spx_eq"
      | ~q(Ninst.not) => Blanc.String.apply "Line.spx_not"
      | ~q(Ninst.and) => Blanc.String.apply "Line.spx_and"
      | ~q(Ninst.or) => Blanc.String.apply "Line.spx_or"
      | ~q(Ninst.shl) => Blanc.String.apply "Line.spx_shl"
      | ~q(Ninst.shr) => Blanc.String.apply "Line.spx_shr"
      | ~q(Ninst.iszero) => Blanc.String.apply "Line.spx_iszero"
      | ~q(Ninst.caller) => Blanc.String.apply "Line.spx_caller"
      | ~q(Ninst.callvalue) => Blanc.String.apply "Line.spx_callvalue"
      | ~q(Ninst.calldatacopy) => Blanc.String.apply "Line.spx_calldatacopy"
      | _ => dbg_trace "line_prefix : unimplemented inst"; failure
      linePrefix
  | _ =>
    dbg_trace "Not a pref goal : "
    dbg_trace t

elab "line_prefix" : tactic => linePrefix

def findDeclWithM (f : Lean.LocalDecl → TacticM Bool) : TacticM Lean.LocalDecl := do
  let g : Lean.LocalDecl → TacticM (Option Lean.LocalDecl) := fun d => do
    if (← f d) then pure (some d) else pure none
  let ctx ← Lean.MonadLCtx.getLCtx
  let (some d) ← ctx.findDeclM? g | failure
  pure d

def isLineRun (ld : Lean.LocalDecl) : TacticM Bool := do
  let px : Q(Prop) ← Lean.Meta.inferType ld.toExpr
  match px with
  | ~q(Line.Run _ $sx _ $sx') => pure true
  | _ => pure false

def Lean.FVarId.clear (i : Lean.FVarId) : Lean.Elab.Tactic.TacticM Unit :=
  withMainContext do
    let mvarId ← (← getMainGoal).clear i
    replaceMainGoal [mvarId]

def Lean.FVarId.revertOne (i : Lean.FVarId) : TacticM Unit := do
  let (_, mvarId) ← (← getMainGoal).revert #[i]
  replaceMainGoal [mvarId]

def clearIf (i i' : Lean.FVarId) (sx : Lean.Expr) (ld : Lean.LocalDecl) :
    Lean.Elab.Tactic.TacticM Unit := do
  let pre_t ← Lean.Meta.inferType ld.toExpr
  let t ← Lean.instantiateMVars pre_t
  if (¬ BEq.beq ld.fvarId i ∧ ¬ BEq.beq ld.fvarId i' ∧ Lean.Expr.occurs sx t)
  then Blanc.Lean.FVarId.clear ld.fvarId
  else pure ()

def isPref (x : Lean.Expr) (ld : Lean.LocalDecl) : TacticM Bool := do
  let px : Q(Prop) ← Lean.Meta.inferType ld.toExpr
  match px with
  | ~q(_ <<+ (Devm.stack $x')) => pure (← Lean.Meta.isDefEq x x')
  | _ => pure false

def initDescOfRun : Q(Prop) → TacticM Lean.Expr
  | ~q(Line.Run _ $sx _ _) => pure sx
  | _ => failure

def Expr.imp (x y : Lean.Expr) : Lean.Expr :=
  Lean.Expr.forallE Lean.Name.anonymous x y Lean.BinderInfo.default

def mkMotive : Q(Prop) → TacticM Lean.Expr
| ~q(($p <<+ (Devm.stack $s₀)) → (Line.Run $e $s₀ $l $s₁) → $φ) => do
  pure <|
    Lean.Expr.lam `s q(Devm)
      ( Blanc.Expr.imp
          (Lean.Expr.app q(λ s : Devm => $p <<+ s.stack) (Lean.Expr.bvar 0))
          (Blanc.Expr.imp
            (Lean.Expr.app q(λ s : Devm => Line.Run $e s $l $s₁) (Lean.Expr.bvar 1))
            φ) )
      Lean.BinderInfo.default
| _ => failure

elab "generalize_line_prefix" : tactic =>
  withMainContext do
    let rd ← findDeclWithM isLineRun
    let sx ← initDescOfRun (← Lean.Meta.inferType rd.toExpr)
    let pd ← findDeclWithM (isPref sx)
    let sd ← findDeclWithM (λ dd => Lean.Meta.isDefEq dd.toExpr sx)
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM (clearIf rd.fvarId pd.fvarId sx)
    Blanc.Lean.FVarId.revertOne rd.fvarId
    Blanc.Lean.FVarId.revertOne pd.fvarId
    let g : Q(Prop) ← getMainTarget
    let m ← mkMotive g
    Lean.Expr.apply <| Lean.mkApp2 q(@apply_univ Devm) m sd.toExpr
    linePrefix

def clearIfOcc (sx : Lean.Expr) (ld : Lean.LocalDecl) :
    Lean.Elab.Tactic.TacticM Unit := do
  let t' ← Lean.instantiateMVars (← Lean.Meta.inferType ld.toExpr)
  if Lean.Expr.occurs sx t' then Blanc.Lean.FVarId.clear ld.fvarId

syntax "clear_state" (ppSpace colGt term:max) : tactic
elab_rules : tactic
  | `(tactic| clear_state $hs) =>
    Lean.Elab.Tactic.withMainContext do
      let i ← getFVarId hs
      let d ← findDeclWithM (λ d => pure <| BEq.beq d.fvarId i)
      let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
      ctx.forM (clearIfOcc d.toExpr)
      Blanc.Lean.FVarId.clear d.fvarId

end

end Blanc
