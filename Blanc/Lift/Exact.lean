import Blanc.Lift.Sound

/-!
# The gas-exact converse for lifted bytecode

`SFunc.RunExact` is the executable, exact-gas sibling of `SFunc.Run`.  The
converse below turns such a run back into a Jaune execution.  The checked
frame is retained in the induction invariant so that a returned frame can
transport an arbitrary continuation back through the synthetic tree.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

inductive SFunc.RunExact (fs : List SFunc) (sevm : Sevm) :
    Devm → SFunc → Outcome → Prop
  | zero {devm devm' : Devm} {f g : SFunc} {o : Outcome} (d : B256) :
    Devm.PopBurnBy [d, 0] gHigh devm devm' →
    SFunc.RunExact fs sevm devm' f o →
    SFunc.RunExact fs sevm devm (.branch f g) o
  | succ {devm devm' : Devm} {f g : SFunc} {o : Outcome} (d w : B256) :
    w ≠ 0 →
    Devm.PopBurnBy [d, w] gHigh devm devm' →
    SFunc.RunExact fs sevm devm' g o →
    SFunc.RunExact fs sevm devm (.branch f g) o
  | toZero {devm devm' : Devm} {f : SFunc} {k : Nat} {o : Outcome} (d : B256) :
    Devm.PopBurnBy [d, 0] gHigh devm devm' →
    SFunc.RunExact fs sevm devm' f o →
    SFunc.RunExact fs sevm devm (.branchTo f k) o
  | toSucc {devm devm' : Devm} {f g : SFunc} {k : Nat} {o : Outcome} (d w : B256) :
    w ≠ 0 →
    fs[k]? = some g →
    Devm.PopBurnBy [d, w] gHigh devm devm' →
    SFunc.RunExact fs sevm devm' g o →
    SFunc.RunExact fs sevm devm (.branchTo f k) o
  | last {devm devm' : Devm} {l : Linst} :
    Linst.Run sevm devm l (.ok devm') →
    SFunc.RunExact fs sevm devm (.last l) (.halted devm')
  | next {devm devm' : Devm} {n : Ninst} {f : SFunc} {o : Outcome} :
    Ninst.RunCompiled sevm devm n devm' →
    SFunc.RunExact fs sevm devm' f o →
    SFunc.RunExact fs sevm devm (.next n f) o
  | dest {devm devm' : Devm} {f : SFunc} {o : Outcome} :
    Devm.BurnBy gJumpdest devm devm' →
    SFunc.RunExact fs sevm devm' f o →
    SFunc.RunExact fs sevm devm (.dest f) o
  | jump {devm devm' : Devm} {k : Nat} {f : SFunc} {o : Outcome} (d : B256) :
    fs[k]? = some f →
    Devm.PopBurnBy [d] gMid devm devm' →
    SFunc.RunExact fs sevm devm' f o →
    SFunc.RunExact fs sevm devm (.jump k) o
  | ret {devm devm' : Devm} (d : B256) :
    Devm.PopBurnBy [d] gMid devm devm' →
    SFunc.RunExact fs sevm devm .ret (.returned devm')
  | callHalt {devm devm' devm'' : Devm} {k : Nat} {f g : SFunc} (d : B256) :
    fs[k]? = some g →
    Devm.PopBurnBy [d] gMid devm devm' →
    SFunc.RunExact fs sevm devm' g (.halted devm'') →
    SFunc.RunExact fs sevm devm (.callNext k f) (.halted devm'')
  | callRet {devm devm' devm'' : Devm} {k : Nat} {f g : SFunc} {o : Outcome}
      (d : B256) :
    fs[k]? = some g →
    Devm.PopBurnBy [d] gMid devm devm' →
    SFunc.RunExact fs sevm devm' g (.returned devm'') →
    SFunc.RunExact fs sevm devm'' f o →
    SFunc.RunExact fs sevm devm (.callNext k f) o
  | pcAt {devm devm' : Devm} {p : Nat} {f : SFunc} {o : Outcome} :
    Ninst.StepRun p sevm devm (.reg .pc) .none (.ok devm') →
    SFunc.RunExact fs sevm devm' f o →
    SFunc.RunExact fs sevm devm (.pcAt p f) o

def SProg.RunExact (fs : List SFunc) (sevm : Sevm) (devm devm' : Devm) : Prop :=
  ∃ f, fs[0]? = some f ∧ SFunc.RunExact fs sevm devm f (.halted devm')

theorem SFunc.RunExact.toRun {fs : List SFunc} {sevm : Sevm} {devm : Devm}
    {f : SFunc} {o : Outcome} (h : SFunc.RunExact fs sevm devm f o) :
    SFunc.Run fs sevm devm f o := by
  refine SFunc.RunExact.rec
    (motive := fun devm f o _ => SFunc.Run fs sevm devm f o)
    (fun d hpop hrun ih => .zero d (Devm.PopBurn.of_popBurnBy hpop) ih)
    (fun d w hne hpop hrun ih =>
      .succ d w hne (Devm.PopBurn.of_popBurnBy hpop) ih)
    (fun d hpop hrun ih => .toZero d (Devm.PopBurn.of_popBurnBy hpop) ih)
    (fun d w hne hget hpop hrun ih =>
      .toSucc d w hne hget (Devm.PopBurn.of_popBurnBy hpop) ih)
    (fun hrun => .last hrun)
    (fun hrun hnext ih => .next (Ninst.Run.of_runCompiled hrun) ih)
    (fun hburn hrun ih => .dest (Devm.Burn.of_burnBy hburn) ih)
    (fun d hget hpop hrun ih =>
      .jump d hget (Devm.PopBurn.of_popBurnBy hpop) ih)
    (fun d hpop => .ret d (Devm.PopBurn.of_popBurnBy hpop))
    (fun d hget hpop hrun ih =>
      .callHalt d hget (Devm.PopBurn.of_popBurnBy hpop) ih)
    (fun d hget hpop hrun hcont ihrun ihcont =>
      .callRet d hget (Devm.PopBurn.of_popBurnBy hpop) ihrun ihcont)
    (fun {_ _ p _ _} hstep _ ih => .pcAt ⟨.none, trivial, p, hstep⟩ hstep ih)
    h

/-! ## The jumpability certificate -/

def jumpsOkNode (code : ByteArray) (es : List Entry) : SFunc → List AVal → Bool
  | .next n f, a =>
    match absNinst n a with
    | some a' => jumpsOkNode code es f a'
    | none => true
  | .last _, _ => true
  | .dest f, a => jumpsOkNode code es f a
  | .branch f g, a =>
    match a with
    | .const t :: v :: a' =>
      (v.jumps? == some true || jumpsOkNode code es f a') &&
        (v.jumps? == some false || (jumpdestOk code t.toNat && jumpsOkNode code es g a'))
    | _ => false
  | .branchTo f k, a =>
    match a, es[k]? with
    | .const _ :: v :: a', some e =>
      jumpdestOk code e.pc && (v.jumps? == some true || jumpsOkNode code es f a')
    | _, _ => false
  | .jump k, a =>
    match a, es[k]? with
    | .const _ :: _, some e => jumpdestOk code e.pc
    | _, _ => false
  | .callNext k f, a =>
    match a, f, es[k]? with
    | .const _ :: a', .dest d, some e =>
      jumpdestOk code e.pc &&
        match e.frame.findIdx? (· == .ret) with
        | some i =>
          match a'[i]? with
          | some (.const r) =>
            jumpdestOk code r.toNat &&
              jumpsOkNode code es d
                (List.replicate e.rets .unk ++ a'.drop e.frame.length)
          | _ => false
        | none => true
    | _, _, _ => false
  | .ret, _ => true
  | .pcAt p f, a => jumpsOkNode code es f (.const (Nat.toB256 p) :: a)
  | .undefined, _ => true

def Cert.jumpsOk (code : ByteArray) (c : Cert) : Bool :=
  c.all fun (e, f) => jumpsOkNode code c.entries f e.frame

/-- `jumpsOkNode` over the frames `checkNodeM` computes (tracking memory when
`b` is on). -/
def jumpsOkNodeM (code : ByteArray) (es : List Entry) (b : Bool) :
    SFunc → List AVal → MemMap → Bool
  | .next n f, a, μ =>
    match absNinst n a with
    | some a' => jumpsOkNodeM code es b f (if b then memFold (memTop n a μ) a' else a')
        (if b then absMem n a μ else [])
    | none => true
  | .last _, _, _ => true
  | .dest f, a, μ => jumpsOkNodeM code es b f a μ
  | .branch f g, a, μ =>
    match a with
    | .const t :: v :: a' =>
      (v.jumps? == some true || jumpsOkNodeM code es b f a' μ) &&
        (v.jumps? == some false || (jumpdestOk code t.toNat && jumpsOkNodeM code es b g a' μ))
    | _ => false
  | .branchTo f k, a, μ =>
    match a, es[k]? with
    | .const _ :: v :: a', some e =>
      jumpdestOk code e.pc && (v.jumps? == some true || jumpsOkNodeM code es b f a' μ)
    | _, _ => false
  | .jump k, a, _ =>
    match a, es[k]? with
    | .const _ :: _, some e => jumpdestOk code e.pc
    | _, _ => false
  | .callNext k f, a, _ =>
    match a, f, es[k]? with
    | .const _ :: a', .dest d, some e =>
      jumpdestOk code e.pc &&
        match e.frame.findIdx? (· == .ret) with
        | some i =>
          match a'[i]? with
          | some (.const r) =>
            jumpdestOk code r.toNat &&
              jumpsOkNodeM code es b d
                (List.replicate e.rets .unk ++ a'.drop e.frame.length) []
          | _ => false
        | none => true
    | _, _, _ => false
  | .ret, _, _ => true
  | .pcAt p f, a, μ => jumpsOkNodeM code es b f (.const (Nat.toB256 p) :: a) μ
  | .undefined, _, _ => true

theorem jumpsOkNode_eq_jumpsOkNodeM (code : ByteArray) (es : List Entry) (f : SFunc)
    (a : List AVal) : jumpsOkNode code es f a = jumpsOkNodeM code es false f a [] := by
  let Q : SFunc → Prop := fun f =>
    ∀ (a : List AVal), jumpsOkNode code es f a = jumpsOkNodeM code es false f a []
  let P : SFunc → Prop := fun f =>
    Q f ∧ match f with
    | .dest g => Q g
    | _ => True
  have hall : ∀ f : SFunc, P f := by
    intro f
    induction f with
    | next n f ih =>
      refine ⟨fun a => ?_, by simp [P]⟩
      cases h : absNinst n a <;> simp [Q, jumpsOkNode, jumpsOkNodeM, h, ih.1]
    | last l => exact ⟨fun a => rfl, by simp [P]⟩
    | dest f ih => exact ⟨fun a => by simp [Q, jumpsOkNode, jumpsOkNodeM, ih.1], ih.1⟩
    | branch f g ihf ihg =>
      refine ⟨fun a => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;>
        simp [Q, jumpsOkNode, jumpsOkNodeM, ihf.1, ihg.1]
    | branchTo f k ih =>
      refine ⟨fun a => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;> cases h : es[k]? <;>
        simp [Q, jumpsOkNode, jumpsOkNodeM, ih.1, h]
    | jump k =>
      refine ⟨fun a => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases h : es[k]? <;>
        simp [Q, jumpsOkNode, jumpsOkNodeM, h]
    | callNext k f ih =>
      refine ⟨fun a => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases f <;> cases h : es[k]? <;>
        simp [Q, jumpsOkNode, jumpsOkNodeM, ih.1, ih.2, h] <;> rfl
    | ret => exact ⟨fun a => rfl, by simp [P]⟩
    | pcAt p f ih => exact ⟨fun a => by simp [Q, jumpsOkNode, jumpsOkNodeM, ih.1], by simp [P]⟩
    | undefined => exact ⟨fun a => rfl, by simp [P]⟩
  exact (hall f).1 a

/-- `jumpsOkNodeM` at `.branch` with an unknown condition needs both sub-trees
(and the taken target to be a jump destination). -/
theorem jumpsOkNodeM_branch_unk {code : ByteArray} (es : List Entry) (b : Bool)
    (tgt : B256) (v : AVal) (a' : List AVal) (μ : MemMap) (f g : SFunc)
    (hv : v.jumps? = none) :
    jumpsOkNodeM code es b (.branch f g) (.const tgt :: v :: a') μ =
      (jumpsOkNodeM code es b f a' μ &&
        (jumpdestOk code tgt.toNat && jumpsOkNodeM code es b g a' μ)) := by
  simp [jumpsOkNodeM, hv]

/-- Every entry is jump-safe from its declared map. -/
def Cert.JumpsOkM (code : ByteArray) (c : Cert) (ms : List MemMap) (b : Bool) : Prop :=
  ∀ k e f, c.entries[k]? = some e → c.prog[k]? = some f →
    jumpsOkNodeM code c.entries b f e.frame (ms.getD k []) = true

/-- `Cert.jumpsOk` with memory maps. -/
def Cert.jumpsEntriesM (code : ByteArray) (es : List Entry) (ms : List MemMap) (b : Bool) :
    Nat → Cert → Bool
  | _, [] => true
  | k, (e, f) :: c =>
    jumpsOkNodeM code es b f e.frame (ms.getD k []) && Cert.jumpsEntriesM code es ms b (k + 1) c

def Cert.jumpsOkM (code : ByteArray) (c : Cert) (ms : List MemMap) (b : Bool) : Bool :=
  Cert.jumpsEntriesM code c.entries ms b 0 c

lemma cert_jumpsOk_at {code : ByteArray} {c : Cert}
    (hc : Cert.jumpsOk code c = true) (k : Nat) (e : Entry) (f : SFunc)
    (he : c.entries[k]? = some e) (hf : c.prog[k]? = some f) :
    jumpsOkNode code c.entries f e.frame = true := by
  have hmem := cert_pair_mem c k e f he hf
  have h := (List.all_eq_true.mp hc) (e, f) hmem
  exact h

theorem Cert.jumpsOkM_of_jumpsOk {code : ByteArray} {c : Cert}
    (hj : Cert.jumpsOk code c = true) : Cert.JumpsOkM code c [] false := by
  intro k e f he hf
  have h := cert_jumpsOk_at hj k e f he hf
  rw [jumpsOkNode_eq_jumpsOkNodeM] at h
  simpa using h

theorem Cert.jumpsEntriesM_at {code : ByteArray} {es : List Entry} {ms : List MemMap}
    {b : Bool} : ∀ (c : Cert) (k : Nat), Cert.jumpsEntriesM code es ms b k c = true →
      ∀ j e f, c.entries[j]? = some e → c.prog[j]? = some f →
        jumpsOkNodeM code es b f e.frame (ms.getD (k + j) []) = true
  | [], _, _, j, e, f, he, _ => by simp [Cert.entries] at he
  | (e0, f0) :: c, k, h, 0, e, f, he, hf => by
      simp only [Cert.entries, Cert.prog, List.map_cons, List.getElem?_cons_zero,
        Option.some.injEq] at he hf
      subst he hf
      simp only [Cert.jumpsEntriesM, Bool.and_eq_true] at h
      simpa using h.1
  | (e0, f0) :: c, k, h, j + 1, e, f, he, hf => by
      simp only [Cert.jumpsEntriesM, Bool.and_eq_true] at h
      have := Cert.jumpsEntriesM_at c (k + 1) h.2 j e f (by simpa [Cert.entries] using he)
        (by simpa [Cert.prog] using hf)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem Cert.jumpsOkM_of_jumpsOkM {code : ByteArray} {c : Cert} {ms : List MemMap}
    {b : Bool} (hj : Cert.jumpsOkM code c ms b = true) : Cert.JumpsOkM code c ms b := by
  intro k e f he hf
  simpa using Cert.jumpsEntriesM_at c 0 hj k e f he hf

private lemma popBurnBy_state {xs : List B256} {cost : Nat} {devm devm' : Devm}
    (h : Devm.PopBurnBy xs cost devm devm') :
    devm.setMach ⟨devm'.stack, devm.memory, devm.gasLeft - cost, devm.stateGas⟩ = devm' := by
  refine Devm.eq_of_proj rfl h.memory ?_ h.logs h.refundCounter h.output
    h.accountsToDelete h.returnData h.error h.accessedAddresses
    h.accessedStorageKeys h.state h.createdAccounts h.transientStorage h.stateGas
    h.accountReads h.storageReads
  have hg := h.gasLeft
  change devm.gasLeft - cost = devm'.gasLeft
  omega

private lemma popBurnBy_one_stack {x : B256} {s s' : Devm}
    (h : Devm.PopBurnBy [x] gMid s s') : s.stack = x :: s'.stack := by
  simpa [Stack.Pop, Split] using h.stack

private lemma popBurnBy_two_stack {x y : B256} {s s' : Devm}
    (h : Devm.PopBurnBy [x, y] gHigh s s') : s.stack = x :: y :: s'.stack := by
  simpa [Stack.Pop, Split] using h.stack

private lemma cond_matches {ρ : B256} {av av2 : AVal} {a' : List AVal}
    {S base : List B256} {devm devm' : Devm} {d w : B256}
    (hframe : FrameMatches ρ (av :: av2 :: a') S) (hstack : devm.stack = S ++ base)
    (hpop : Devm.PopBurnBy [d, w] gHigh devm devm') : AVal.Matches ρ av2 w := by
  have hs := popBurnBy_two_stack hpop
  rw [hstack] at hs
  cases hframe with
  | cons _ hrest =>
    cases hrest with
    | cons h1 _ =>
      simp only [List.cons_append, List.cons.injEq] at hs
      rw [← hs.2.1]
      exact h1

private def ExactResult (code : ByteArray) (c : Cert) (sevm : Sevm)
    (pc m : Nat) (a : List AVal) (μ : MemMap) (f : SFunc) (ρ : B256) (S base : List B256)
    (devm : Devm) : Outcome → Prop
  | .halted post => Nonempty (Exec pc sevm devm (.ok post))
  | .returned devm' =>
    RetIn a μ ∧ ∃ S', devm'.stack = S' ++ base ∧ S'.length = m ∧
      (∀ {r : Execution}, Nonempty (Exec ρ.toNat sevm devm' r) →
        Nonempty (Exec pc sevm devm r))

private lemma jumpable_of_jumpdestOk {code : ByteArray} {k : Nat}
    (h : jumpdestOk code k = true) : jumpable code k = true := by
  rw [jumpable_eq_jumpdestOk]
  exact h

private lemma jumpi_zero_cont {pc : Nat} {sevm : Sevm} {devm devm' : Devm}
    {d : B256} (h_at : Jinst.At sevm.code pc .jumpi)
    (h : Devm.PopBurnBy [d, 0] gHigh devm devm') :
    Evm.step ⟨pc, sevm, devm⟩ = .cont (pc + 1) devm' := by
  have hs := popBurnBy_two_stack h
  have hg : gHigh ≤ devm.gasLeft := by have := h.gasLeft; omega
  have hstep := Evm.jumpi_cont_zero h_at hs hg
  have heq := popBurnBy_state h
  simpa [heq] using hstep

private lemma jumpi_succ_cont {pc : Nat} {sevm : Sevm} {devm devm' : Devm}
    {d w : B256} (h_at : Jinst.At sevm.code pc .jumpi)
    (hne : w ≠ 0) (hjp : jumpable sevm.code d.toNat = true)
    (h : Devm.PopBurnBy [d, w] gHigh devm devm') :
    Evm.step ⟨pc, sevm, devm⟩ = .cont d.toNat devm' := by
  have hs := popBurnBy_two_stack h
  have hg : gHigh ≤ devm.gasLeft := by have := h.gasLeft; omega
  have hstep := Evm.jumpi_cont_jump h_at hs hne hg hjp
  have heq := popBurnBy_state h
  simpa [heq] using hstep

private lemma jump_cont_exact {pc : Nat} {sevm : Sevm} {devm devm' : Devm}
    {d : B256} (h_at : Jinst.At sevm.code pc .jump)
    (hjp : jumpable sevm.code d.toNat = true)
    (h : Devm.PopBurnBy [d] gMid devm devm') :
    Evm.step ⟨pc, sevm, devm⟩ = .cont d.toNat devm' := by
  have hs := popBurnBy_one_stack h
  have hg : gMid ≤ devm.gasLeft := by have := h.gasLeft; omega
  have hstep := Evm.jump_cont h_at hs hg hjp
  have heq := popBurnBy_state h
  simpa [heq] using hstep

private lemma dest_cont_exact {pc : Nat} {sevm : Sevm} {devm devm' : Devm}
    (h_at : Jinst.At sevm.code pc .jumpdest)
    (h : Devm.BurnBy gJumpdest devm devm') :
    Evm.step ⟨pc, sevm, devm⟩ = .cont (pc + 1) devm' := by
  exact Evm.jumpdest_cont h_at h

private def ExactClaim {fs : List SFunc} {sevm : Sevm}
    (code : ByteArray) (c : Cert) (ms : List MemMap) (b : Bool) (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunExact fs sevm devm f o) : Prop :=
  ∀ (pc m : Nat) (a : List AVal) (ρ : B256) (S base : List B256) (μ : MemMap),
    checkNodeM code c.entries ms b m pc a μ f = true →
    jumpsOkNodeM code c.entries b f a μ = true →
    devm.stack = S ++ base →
    FrameMatches ρ a S →
    MemMatches ρ μ devm.memory →
    (RetIn a μ → jumpdestOk code ρ.toNat = true) →
    ExactResult code c sevm pc m a μ f ρ S base devm o

theorem node_exactM {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool}
    (hc : Cert.CheckedM code c ms b)
    (hj : Cert.JumpsOkM code c ms b) {sevm : Sevm}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunExact c.prog sevm devm f o) :
    ExactClaim code c ms b hcode hfork run := by
  refine SFunc.RunExact.rec
    (fs := c.prog) (sevm := sevm)
    (motive := fun devm f o run => ExactClaim code c ms b hcode hfork run)
    (fun {devm devm' f g o} d hpop hrun ih => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      cases a with
      | nil => simp [checkNodeM] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp [checkNodeM] at hcheck
        | unk => simp [checkNodeM] at hcheck
        | const t =>
          cases a0 with
          | nil => simp [checkNodeM] at hcheck
          | cons av2 a' =>
            have hcheck0 :
                (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                  (av2.jumps? = some true ∨ checkNodeM code c.entries ms b m (pc + 1) a' μ f = true)) ∧
                (av2.jumps? = some false ∨ checkNodeM code c.entries ms b m t.toNat a' μ g = true) := by
              simpa [checkNodeM] using hcheck
            have hjump0 :
                (av2.jumps? = some true ∨ jumpsOkNodeM code c.entries b f a' μ = true) ∧
                (av2.jumps? = some false ∨
                  (jumpdestOk code t.toNat = true ∧ jumpsOkNodeM code c.entries b g a' μ = true)) := by
              simpa [jumpsOkNodeM] using hjump
            have hv := cond_matches hframe hstack hpop
            have hcheck' :
                (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                  checkNodeM code c.entries ms b m (pc + 1) a' μ f = true) ∧ True :=
              ⟨⟨hcheck0.1.1, live_fall hv hcheck0.1.2⟩, trivial⟩
            have hjump' : True ∧ jumpsOkNodeM code c.entries b f a' μ = true ∧ True :=
              ⟨trivial, live_fall hv hjump0.1, trivial⟩
            have h_at : Jinst.At sevm.code pc .jumpi := by
              apply byteAt_jinst_at
              rw [hcode]
              exact hcheck'.1.1
            cases S with
            | nil => cases hframe
            | cons s0 S0 =>
              cases S0 with
              | nil => have := List.Forall₂.length_eq hframe; simp at this
              | cons s1 S1 =>
                cases hframe with
                | cons h0 hrest =>
                  cases hrest with
                  | cons h1 htail =>
                    have hs0 : s0 = t := h0
                    cases o with
                    | halted post =>
                      have hrec := ih (pc + 1) m a' ρ S1 base μ
                        hcheck'.1.2 hjump'.2.1 (by
                          have hs := popBurnBy_two_stack hpop
                          rw [hstack] at hs
                          have htail' : s1 :: (S1 ++ base) = 0 :: devm'.stack :=
                            (List.cons.inj hs).2
                          exact (List.cons.inj htail').2.symm) htail (hmem.of_memory_eq hpop.memory) (by
                            intro h
                            exact hρ (RetIn.of_frame (fun h => List.mem_cons_of_mem _
                              (List.mem_cons_of_mem _ h)) h))
                      rcases hrec with ⟨exc⟩
                      exact ⟨Exec.cont (jumpi_zero_cont h_at hpop) exc⟩
                    | returned devm'' =>
                      have hs := popBurnBy_two_stack hpop
                      rw [hstack] at hs
                      have htail' : s1 :: (S1 ++ base) = 0 :: devm'.stack := by
                        exact (List.cons.inj hs).2
                      have hinter : devm'.stack = S1 ++ base :=
                        (List.cons.inj htail').2.symm
                      have hrec := ih (pc + 1) m a' ρ S1 base μ
                        hcheck'.1.2 hjump'.2.1 hinter htail (hmem.of_memory_eq hpop.memory) (by
                          intro h
                          exact hρ (RetIn.of_frame (fun h => List.mem_cons_of_mem _
                            (List.mem_cons_of_mem _ h)) h))
                      rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
                      refine ⟨RetIn.of_frame (fun h => List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _ h)) hret, S', hst, hlen, ?_⟩
                      intro r hr
                      rcases hcont hr with ⟨exc⟩
                      exact ⟨Exec.cont (jumpi_zero_cont h_at hpop) exc⟩)
    (fun {devm devm' f g o} d w hne hpop hrun ih => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      cases a with
      | nil => simp [checkNodeM] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp [checkNodeM] at hcheck
        | unk => simp [checkNodeM] at hcheck
        | const t =>
          cases a0 with
          | nil => simp [checkNodeM] at hcheck
          | cons av2 a' =>
            have hcheck0 :
                (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                  (av2.jumps? = some true ∨ checkNodeM code c.entries ms b m (pc + 1) a' μ f = true)) ∧
                (av2.jumps? = some false ∨ checkNodeM code c.entries ms b m t.toNat a' μ g = true) := by
              simpa [checkNodeM] using hcheck
            have hjump0 :
                (av2.jumps? = some true ∨ jumpsOkNodeM code c.entries b f a' μ = true) ∧
                (av2.jumps? = some false ∨
                  (jumpdestOk code t.toNat = true ∧ jumpsOkNodeM code c.entries b g a' μ = true)) := by
              simpa [jumpsOkNodeM] using hjump
            have hv := cond_matches hframe hstack hpop
            have hcheck' :
                (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧ True) ∧
                checkNodeM code c.entries ms b m t.toNat a' μ g = true :=
              ⟨⟨hcheck0.1.1, trivial⟩, live_taken hne hv hcheck0.2⟩
            have hjump' :
                jumpdestOk code t.toNat = true ∧ True ∧
                jumpsOkNodeM code c.entries b g a' μ = true :=
              ⟨(live_taken hne hv hjump0.2).1, trivial, (live_taken hne hv hjump0.2).2⟩
            have h_at : Jinst.At sevm.code pc .jumpi := by
              apply byteAt_jinst_at
              rw [hcode]
              exact hcheck'.1.1
            have hjp := jumpable_of_jumpdestOk hjump'.1
            cases S with
            | nil => cases hframe
            | cons s0 S0 =>
              cases S0 with
              | nil => have := List.Forall₂.length_eq hframe; simp at this
              | cons s1 S1 =>
                cases hframe with
                | cons h0 hrest =>
                  cases hrest with
                  | cons h1 htail =>
                    have hs0 : s0 = t := h0
                    have hs := popBurnBy_two_stack hpop
                    rw [hstack] at hs
                    have hd : s0 = d := (List.cons.inj hs).1
                    have hdt : d = t := hd.symm.trans hs0
                    have hjp' : jumpable sevm.code t.toNat = true := by
                      rw [hcode]
                      exact hjp
                    cases o with
                    | halted post =>
                      have hrec := ih (t.toNat) m a' ρ S1 base μ
                        hcheck'.2 hjump'.2.2 (by
                          exact (List.cons.inj (List.cons.inj hs).2).2.symm) htail
                          (hmem.of_memory_eq hpop.memory)
                          (by
                            intro h
                            exact hρ (RetIn.of_frame (fun h => List.mem_cons_of_mem _
                              (List.mem_cons_of_mem _ h)) h))
                      rcases hrec with ⟨exc⟩
                      subst d
                      subst s0
                      exact ⟨Exec.cont (jumpi_succ_cont h_at hne hjp' hpop) exc⟩
                    | returned devm'' =>
                      have hinter : devm'.stack = S1 ++ base := by
                        exact (List.cons.inj (List.cons.inj hs).2).2.symm
                      have hrec := ih (t.toNat) m a' ρ S1 base μ
                        hcheck'.2 hjump'.2.2 hinter htail (hmem.of_memory_eq hpop.memory) (by
                          intro h
                          exact hρ (RetIn.of_frame (fun h => List.mem_cons_of_mem _
                            (List.mem_cons_of_mem _ h)) h))
                      rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
                      refine ⟨RetIn.of_frame (fun h => List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _ h)) hret, S', hst, hlen, ?_⟩
                      intro r hr
                      rcases hcont hr with ⟨exc⟩
                      subst d
                      subst s0
                      exact ⟨Exec.cont (jumpi_succ_cont h_at hne hjp' hpop) exc⟩)
    (fun {devm devm' f k o} d hpop hrun ih => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      cases a with
      | nil => simp [checkNodeM] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp [checkNodeM] at hcheck
        | unk => simp [checkNodeM] at hcheck
        | const t =>
          cases a0 with
          | nil => simp [checkNodeM] at hcheck
          | cons av2 a' =>
            cases hk : c.entries[k]? with
            | none => simp [checkNodeM, hk] at hcheck
            | some e =>
              have hcheck0 :
                  ((((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                    e.pc = t.toNat) ∧ e.rets = m) ∧
                    gotoCompat a' e.frame = true) ∧ memCompat μ (ms[k]?.getD []) = true) ∧
                    (av2.jumps? = some true ∨
                      checkNodeM code c.entries ms b m (pc + 1) a' μ f = true) := by
                simpa [checkNodeM, hk] using hcheck
              have hmc : memCompat μ (ms.getD k []) = true := by simpa using hcheck0.1.2
              replace hcheck0 := And.intro hcheck0.1.1 hcheck0.2
              have hv := cond_matches hframe hstack hpop
              have hcheck' :
                  (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                    e.pc = t.toNat) ∧ e.rets = m) ∧
                    gotoCompat a' e.frame = true) ∧
                    checkNodeM code c.entries ms b m (pc + 1) a' μ f = true :=
                ⟨hcheck0.1, live_fall hv hcheck0.2⟩
              have hjump0 :
                  jumpdestOk code e.pc = true ∧
                    (av2.jumps? = some true ∨ jumpsOkNodeM code c.entries b f a' μ = true) := by
                simpa [jumpsOkNodeM, hk, Bool.and_eq_true] using hjump
              have hjump' :
                  jumpdestOk code e.pc = true ∧
                    jumpsOkNodeM code c.entries b f a' μ = true :=
                ⟨hjump0.1, live_fall hv hjump0.2⟩
              have h_at : Jinst.At sevm.code pc .jumpi := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck'.1.1.1.1
              cases S with
              | nil => cases hframe
              | cons s0 S0 =>
                cases S0 with
                | nil => have := List.Forall₂.length_eq hframe; simp at this
                | cons s1 S1 =>
                  cases hframe with
                  | cons h0 hrest =>
                    cases hrest with
                    | cons h1 htail =>
                      have hs := popBurnBy_two_stack hpop
                      rw [hstack] at hs
                      have htail' : s1 :: (S1 ++ base) = 0 :: devm'.stack :=
                        (List.cons.inj hs).2
                      have hinter : devm'.stack = S1 ++ base :=
                        (List.cons.inj htail').2.symm
                      have hjp : jumpable sevm.code e.pc = true := by
                        rw [hcode]
                        exact jumpable_of_jumpdestOk hjump'.1
                      cases o with
                      | halted post =>
                        have hrec := ih (pc + 1) m a' ρ S1 base μ
                          hcheck'.2 hjump'.2 hinter htail (hmem.of_memory_eq hpop.memory) (by
                            intro h
                            exact hρ (RetIn.of_frame (fun h => List.mem_cons_of_mem _
                              (List.mem_cons_of_mem _ h)) h))
                        rcases hrec with ⟨exc⟩
                        exact ⟨Exec.cont (jumpi_zero_cont h_at hpop) exc⟩
                      | returned devm'' =>
                        have hrec := ih (pc + 1) m a' ρ S1 base μ
                          hcheck'.2 hjump'.2 hinter htail (hmem.of_memory_eq hpop.memory) (by
                            intro h
                            exact hρ (RetIn.of_frame (fun h => List.mem_cons_of_mem _
                              (List.mem_cons_of_mem _ h)) h))
                        rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
                        refine ⟨RetIn.of_frame (fun h => List.mem_cons_of_mem _
                            (List.mem_cons_of_mem _ h)) hret, S', hst, hlen, ?_⟩
                        intro r hr
                        rcases hcont hr with ⟨exc⟩
                        exact ⟨Exec.cont (jumpi_zero_cont h_at hpop) exc⟩)
    (fun {devm devm' f g k o} d w hne hget hpop hrun ih => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      cases a with
      | nil => simp [checkNodeM] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp [checkNodeM] at hcheck
        | unk => simp [checkNodeM] at hcheck
        | const t =>
          cases a0 with
          | nil => simp [checkNodeM] at hcheck
          | cons av2 a' =>
            cases hk : c.entries[k]? with
            | none => simp [checkNodeM, hk] at hcheck
            | some e =>
              have hcheck0 :
                  ((((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                    e.pc = t.toNat) ∧ e.rets = m) ∧
                    gotoCompat a' e.frame = true) ∧ memCompat μ (ms[k]?.getD []) = true) ∧
                    (av2.jumps? = some true ∨
                      checkNodeM code c.entries ms b m (pc + 1) a' μ f = true) := by
                simpa [checkNodeM, hk] using hcheck
              have hmc : memCompat μ (ms.getD k []) = true := by simpa using hcheck0.1.2
              have hcheck' := And.intro hcheck0.1.1 hcheck0.2
              rcases cert_prog_of_entry c k e hk with ⟨g', hg'⟩
              have hgg : g = g' := Option.some.inj (hget.symm.trans hg')
              subst g'
              have hentry := hc k e g hk hg'
              have hjump' :
                  jumpdestOk code e.pc = true ∧
                    (av2.jumps? = some true ∨ jumpsOkNodeM code c.entries b f a' μ = true) := by
                simpa [jumpsOkNodeM, hk, Bool.and_eq_true] using hjump
              have h_at : Jinst.At sevm.code pc .jumpi := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck'.1.1.1.1
              have hje : jumpdestOk code t.toNat = true := by
                simpa [hcheck'.1.1.1.2] using hjump'.1
              have hjp : jumpable sevm.code t.toNat = true := by
                rw [hcode]
                exact jumpable_of_jumpdestOk hje
              cases S with
              | nil => cases hframe
              | cons s0 S0 =>
                cases S0 with
                | nil => have := List.Forall₂.length_eq hframe; simp at this
                | cons s1 S1 =>
                  cases hframe with
                  | cons h0 hrest =>
                    cases hrest with
                    | cons h1 htail =>
                      have hs0 : s0 = t := h0
                      have hs := popBurnBy_two_stack hpop
                      rw [hstack] at hs
                      have hd : s0 = d := (List.cons.inj hs).1
                      have hdt : d = t := hd.symm.trans hs0
                      have hinter : devm'.stack = S1 ++ base :=
                        (List.cons.inj (List.cons.inj hs).2).2.symm
                      have hframe' : FrameMatches ρ e.frame S1 :=
                        frameMatches_gotoCompat hcheck'.1.2 htail
                      have hentry' :
                          checkNodeM code c.entries ms b e.rets t.toNat e.frame (ms.getD k []) g = true := by
                        simpa [hcheck'.1.1.1.2] using hentry
                      have hjg : jumpsOkNodeM code c.entries b g e.frame (ms.getD k []) = true :=
                        hj k e g hk hget
                      cases o with
                      | halted post =>
                        have hrec := ih t.toNat e.rets e.frame ρ S1 base (ms.getD k [])
                          hentry' hjg hinter hframe'
                          ((hmem.of_memory_eq hpop.memory).of_memCompat hmc) (by
                            intro h
                            exact hρ ((h.imp (ret_mem_of_gotoCompat hcheck'.1.2)
                              (mem_snd_of_memCompat hmc)).imp_left
                              (fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))
                        rcases hrec with ⟨exc⟩
                        subst d
                        subst s0
                        exact ⟨Exec.cont (jumpi_succ_cont h_at hne hjp hpop) exc⟩
                      | returned devm'' =>
                        have hrec := ih t.toNat e.rets e.frame ρ S1 base (ms.getD k [])
                          hentry' hjg hinter hframe'
                          ((hmem.of_memory_eq hpop.memory).of_memCompat hmc) (by
                            intro h
                            exact hρ ((h.imp (ret_mem_of_gotoCompat hcheck'.1.2)
                              (mem_snd_of_memCompat hmc)).imp_left
                              (fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))
                        rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
                        have hret' : RetIn a' μ :=
                          hret.imp (ret_mem_of_gotoCompat hcheck'.1.2) (mem_snd_of_memCompat hmc)
                        have hlen' : S'.length = m := by
                          simpa [hcheck'.1.1.2] using hlen
                        refine ⟨RetIn.of_frame (fun h => List.mem_cons_of_mem _
                            (List.mem_cons_of_mem _ h)) hret', S', hst, hlen', ?_⟩
                        intro r hr
                        rcases hcont hr with ⟨exc⟩
                        subst d
                        subst s0
                        exact ⟨Exec.cont (jumpi_succ_cont h_at hne hjp hpop) exc⟩)
    (fun {devm devm' l} hrun => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      have hbyte : byteAt code pc = some l.toUInt8 := by
        simpa [checkNodeM] using hcheck
      have h_at : Linst.At sevm.code pc l := by
        apply byteAt_linst_at
        rw [hcode]
        exact hbyte
      refine ⟨Exec.halt ?_⟩
      rw [Evm.step_last h_at]
      exact congrArg Step.halt hrun)
    (fun {devm devm' n f o} hrun hnext ih => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      rcases hrun with ⟨xl, hfilled, hsteps⟩
      have hrunN : Ninst.Run sevm devm n devm' := ⟨xl, hfilled, 0, hsteps 0⟩
      have next_nonpush (n0 : Ninst) (a1 a0 : List AVal) (out : Pattern)
          (hlen : a.length ≤ 1024)
          (htrans : ninstTransfer n0 (indexPattern a.length) = some out)
          (hread : out.mapM (readBack a) = some a1)
          (hfold : a0 = foldTop (foldConst n0 a) a1)
          (hchild : checkNodeM code c.entries ms b m (pc + n0.size)
            (if b then memFold (memTop n0 a μ) a0 else a0) (if b then absMem n0 a μ else []) f
              = true)
          (hjump0 : jumpsOkNodeM code c.entries b f
            (if b then memFold (memTop n0 a μ) a0 else a0) (if b then absMem n0 a μ else [])
              = true)
          (hstep0 : Ninst.StepRun pc sevm devm n0 xl (.ok devm'))
          (h_at : Ninst.At sevm.code pc n0) :
          ExactResult code c sevm pc m a μ (SFunc.next n0 f) ρ S base devm o := by
        have hinput :
            Matches
                ((indexPattern a.length).map (label a ρ) ++ base.map some)
                devm.stack := by
          rw [hstack]
          apply matches_append
          · rw [indexPattern_map_label hlen]
            exact frameMatches_matches hframe
          · exact matches_some_map base
        have hmap := ninstTransfer_map (label a ρ) rfl htrans
        have happ := ninstTransfer_append (base.map some) hmap
        have hout := ninstTransfer_run hfork hinput happ
          ⟨xl, hfilled, pc, hstep0⟩
        rw [mapM_readBack_label hread] at hout
        rcases matches_split hout with ⟨S', below, hsp, hfirst, hbelow⟩
        have hbelow' : below = base := matches_some_map_eq hbelow
        have hinter : devm'.stack = S' ++ base := by
          simpa [hbelow'] using hsp
        have hframe0 : FrameMatches ρ a0 S' := by
          rw [hfold]
          exact frameMatches_foldTop hframe hstack ⟨xl, hfilled, pc, hstep0⟩ hinter
            (matches_to_frame hfirst)
        obtain ⟨hframe', hmem'⟩ :=
          step_mem_sound b hframe hstack hmem ⟨xl, hfilled, pc, hstep0⟩ hinter hframe0
        have hret0 : ∀ {a2 : List AVal}, RetIn (if b then memFold (memTop n0 a μ) a2 else a2)
            (if b then absMem n0 a μ else []) → (AVal.ret ∈ a2 → AVal.ret ∈ a) → RetIn a μ := by
          intro a2 h ha2
          rcases RetIn.of_step b h with h | h | h
          · exact .inl (ha2 h)
          · exact .inl h
          · exact .inr h
        have hret1 : AVal.ret ∈ a0 → AVal.ret ∈ a := fun h =>
          ret_mem_of_readBack hread (ret_mem_of_foldTop (hfold ▸ h))
        have hrec := ih (pc + n0.size) m _ ρ S' base _
          hchild hjump0 hinter hframe' hmem' (fun h => hρ (hret0 h hret1))
        cases o with
        | halted post =>
          rcases hrec with ⟨exc⟩
          exact Ninst.exec_of_stepRun h_at hfilled hstep0 ⟨exc⟩
        | returned devm'' =>
          rcases hrec with ⟨hret, Sret, hst, hlenret, hcont⟩
          refine ⟨hret0 hret hret1, Sret, hst, hlenret, ?_⟩
          intro r hr
          rcases hcont hr with ⟨exc⟩
          exact Ninst.exec_of_stepRun h_at hfilled hstep0 ⟨exc⟩
      cases n with
      | push bs fits =>
        have hchk := hcheck
        simp only [checkNodeM, absNinst, Bool.and_eq_true] at hchk
        have h_at : Ninst.At sevm.code pc (.push bs fits) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.push bs fits))
          rw [hcode]
          exact hchk.1.1
        have hstack' : devm'.stack = Bytes.toB256 bs :: (S ++ base) := by
          rw [push_run_stack hrunN, hstack]
        have hframe0 :
            FrameMatches ρ (.const (Bytes.toB256 bs) :: a)
              (Bytes.toB256 bs :: S) := List.Forall₂.cons rfl hframe
        obtain ⟨hframe', hmem'⟩ := step_mem_sound b hframe hstack hmem hrunN
          (by rw [hstack']; rfl) hframe0
        have hjump' := hjump
        simp only [jumpsOkNodeM, absNinst] at hjump'
        have hret0 : RetIn (if b then memFold (memTop (.push bs fits) a μ)
            (.const (Bytes.toB256 bs) :: a) else .const (Bytes.toB256 bs) :: a)
            (if b then absMem (.push bs fits) a μ else []) → RetIn a μ := by
          intro h
          rcases RetIn.of_step b h with h | h | h
          · exact .inl (by simpa using h)
          · exact .inl h
          · exact .inr h
        have hrec := ih (pc + (Ninst.push bs fits).size) m
          _ ρ (Bytes.toB256 bs :: S) base _
          hchk.2 hjump' hstack' hframe' hmem' (fun h => hρ (hret0 h))
        cases o with
        | halted post =>
          rcases hrec with ⟨exc⟩
          exact Ninst.exec_of_stepRun h_at hfilled (hsteps pc) ⟨exc⟩
        | returned devm'' =>
          rcases hrec with ⟨hret, Sret, hst, hlenret, hcont⟩
          refine ⟨hret0 hret, Sret, hst, hlenret, ?_⟩
          intro r hr
          rcases hcont hr with ⟨exc⟩
          exact Ninst.exec_of_stepRun h_at hfilled (hsteps pc) ⟨exc⟩
      | reg r =>
        have hchk := hcheck
        simp only [checkNodeM, Bool.and_eq_true] at hchk
        have h_at : Ninst.At sevm.code pc (Ninst.reg r) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.reg r))
          rw [hcode]
          exact hchk.1.1
        cases ha : absNinst (Ninst.reg r) a with
        | none => simp [ha] at hchk
        | some a0 =>
          have hchild := hchk.2
          simp only [ha] at hchild
          rcases absNinst_nonpush_spec (by
            intro bs fits h
            cases h) ha with ⟨hlen, out, a1, htrans, hread, hfold⟩
          have hjump' := hjump
          simp only [jumpsOkNodeM, ha] at hjump'
          exact next_nonpush (Ninst.reg r) a1 a0 out hlen htrans hread hfold hchild hjump'
            (hsteps pc) h_at
      | exec x =>
        have hchk := hcheck
        simp only [checkNodeM, Bool.and_eq_true] at hchk
        have h_at : Ninst.At sevm.code pc (Ninst.exec x) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.exec x))
          rw [hcode]
          exact hchk.1.1
        cases ha : absNinst (Ninst.exec x) a with
        | none => simp [ha] at hchk
        | some a0 =>
          have hchild := hchk.2
          simp only [ha] at hchild
          rcases absNinst_nonpush_spec (by
            intro bs fits h
            cases h) ha with ⟨hlen, out, a1, htrans, hread, hfold⟩
          have hjump' := hjump
          simp only [jumpsOkNodeM, ha] at hjump'
          exact next_nonpush (Ninst.exec x) a1 a0 out hlen htrans hread hfold hchild hjump'
            (hsteps pc) h_at
      | dupn i =>
        have hchk := hcheck
        simp only [checkNodeM, Bool.and_eq_true] at hchk
        have h_at : Ninst.At sevm.code pc (Ninst.dupn i) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.dupn i))
          rw [hcode]
          exact hchk.1.1
        cases ha : absNinst (Ninst.dupn i) a with
        | none => simp [ha] at hchk
        | some a0 =>
          have hchild := hchk.2
          simp only [ha] at hchild
          rcases absNinst_nonpush_spec (by
            intro bs fits h
            cases h) ha with ⟨hlen, out, a1, htrans, hread, hfold⟩
          have hjump' := hjump
          simp only [jumpsOkNodeM, ha] at hjump'
          exact next_nonpush (Ninst.dupn i) a1 a0 out hlen htrans hread hfold hchild hjump'
            (hsteps pc) h_at
      | swapn i =>
        have hchk := hcheck
        simp only [checkNodeM, Bool.and_eq_true] at hchk
        have h_at : Ninst.At sevm.code pc (Ninst.swapn i) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.swapn i))
          rw [hcode]
          exact hchk.1.1
        cases ha : absNinst (Ninst.swapn i) a with
        | none => simp [ha] at hchk
        | some a0 =>
          have hchild := hchk.2
          simp only [ha] at hchild
          rcases absNinst_nonpush_spec (by
            intro bs fits h
            cases h) ha with ⟨hlen, out, a1, htrans, hread, hfold⟩
          have hjump' := hjump
          simp only [jumpsOkNodeM, ha] at hjump'
          exact next_nonpush (Ninst.swapn i) a1 a0 out hlen htrans hread hfold hchild hjump'
            (hsteps pc) h_at
      | exchange i =>
        have hchk := hcheck
        simp only [checkNodeM, Bool.and_eq_true] at hchk
        have h_at : Ninst.At sevm.code pc (Ninst.exchange i) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.exchange i))
          rw [hcode]
          exact hchk.1.1
        cases ha : absNinst (Ninst.exchange i) a with
        | none => simp [ha] at hchk
        | some a0 =>
          have hchild := hchk.2
          simp only [ha] at hchild
          rcases absNinst_nonpush_spec (by
            intro bs fits h
            cases h) ha with ⟨hlen, out, a1, htrans, hread, hfold⟩
          have hjump' := hjump
          simp only [jumpsOkNodeM, ha] at hjump'
          exact next_nonpush (Ninst.exchange i) a1 a0 out hlen htrans hread hfold hchild hjump'
            (hsteps pc) h_at)
    (fun {devm devm' f o} hburn hrun ih => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      have hcheck' :
          byteAt code pc = some (Jinst.toUInt8 .jumpdest) ∧
            checkNodeM code c.entries ms b m (pc + 1) a μ f = true := by
        simpa [checkNodeM] using hcheck
      have h_at : Jinst.At sevm.code pc .jumpdest := by
        apply byteAt_jinst_at
        rw [hcode]
        exact hcheck'.1
      have hstack' : devm'.stack = S ++ base := by
        rw [← hburn.stack, hstack]
      have hrec := ih (pc + 1) m a ρ S base μ
        hcheck'.2 (by simpa [jumpsOkNodeM] using hjump) hstack' hframe
        (hmem.of_memory_eq hburn.memory) hρ
      cases o with
      | halted post =>
        rcases hrec with ⟨exc⟩
        exact ⟨Exec.cont (dest_cont_exact h_at hburn) exc⟩
      | returned devm'' =>
        rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
        refine ⟨hret, S', hst, hlen, ?_⟩
        intro r hr
        rcases hcont hr with ⟨exc⟩
        exact ⟨Exec.cont (dest_cont_exact h_at hburn) exc⟩)
    (fun {devm devm' k f o} d hget hpop hrun ih => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      cases a with
      | nil => simp [checkNodeM] at hcheck
      | cons av a' =>
        cases av with
        | ret => simp [checkNodeM] at hcheck
        | unk => simp [checkNodeM] at hcheck
        | const t =>
          cases hk : c.entries[k]? with
          | none => simp [checkNodeM, hk] at hcheck
          | some e =>
            have hcheck0 :
                ((((byteAt code pc = some (Jinst.toUInt8 .jump) ∧
                  e.pc = t.toNat) ∧ e.rets = m) ∧
                  gotoCompat a' e.frame = true) ∧ memCompat μ (ms[k]?.getD []) = true) := by
              simpa [checkNodeM, hk] using hcheck
            have hcheck' := hcheck0.1
            have hmc : memCompat μ (ms.getD k []) = true := by simpa using hcheck0.2
            rcases cert_prog_of_entry c k e hk with ⟨g, hg⟩
            have hfg : f = g := Option.some.inj (hget.symm.trans hg)
            subst g
            have hentry := hc k e f hk hg
            have hjump' : jumpdestOk code e.pc = true := by
              simpa [jumpsOkNodeM, hk] using hjump
            have hjg : jumpsOkNodeM code c.entries b f e.frame (ms.getD k []) = true :=
              hj k e f hk hg
            have h_at : Jinst.At sevm.code pc .jump := by
              apply byteAt_jinst_at
              rw [hcode]
              exact hcheck'.1.1.1
            have hje : jumpdestOk code t.toNat = true := by
              simpa [hcheck'.1.1.2] using hjump'
            have hjp : jumpable sevm.code t.toNat = true := by
              rw [hcode]
              exact jumpable_of_jumpdestOk hje
            cases S with
            | nil => cases hframe
            | cons s0 S1 =>
              cases hframe with
              | cons h0 htail =>
                have hs0 : s0 = t := h0
                have hs := popBurnBy_one_stack hpop
                rw [hstack] at hs
                have hd : s0 = d := (List.cons.inj hs).1
                have hdt : d = t := hd.symm.trans hs0
                have hinter : devm'.stack = S1 ++ base :=
                  (List.cons.inj hs).2.symm
                have hframe' : FrameMatches ρ e.frame S1 :=
                  frameMatches_gotoCompat hcheck'.2 htail
                have hentry' :
                    checkNodeM code c.entries ms b e.rets t.toNat e.frame (ms.getD k []) f = true := by
                  simpa [hcheck'.1.1.2] using hentry
                cases o with
                | halted post =>
                  have hrec := ih t.toNat e.rets e.frame ρ S1 base (ms.getD k [])
                    hentry' hjg hinter hframe'
                    ((hmem.of_memory_eq hpop.memory).of_memCompat hmc) (by
                      intro h
                      exact hρ ((h.imp (ret_mem_of_gotoCompat hcheck'.2)
                        (mem_snd_of_memCompat hmc)).imp_left (List.mem_cons_of_mem _)))
                  rcases hrec with ⟨exc⟩
                  subst d
                  subst s0
                  exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exc⟩
                | returned devm'' =>
                  have hrec := ih t.toNat e.rets e.frame ρ S1 base (ms.getD k [])
                    hentry' hjg hinter hframe'
                    ((hmem.of_memory_eq hpop.memory).of_memCompat hmc) (by
                      intro h
                      exact hρ ((h.imp (ret_mem_of_gotoCompat hcheck'.2)
                        (mem_snd_of_memCompat hmc)).imp_left (List.mem_cons_of_mem _)))
                  rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
                  have hret' : RetIn a' μ :=
                    hret.imp (ret_mem_of_gotoCompat hcheck'.2) (mem_snd_of_memCompat hmc)
                  have hlen' : S'.length = m := by
                    simpa [hcheck'.1.2] using hlen
                  refine ⟨RetIn.of_frame (List.mem_cons_of_mem _) hret', S', hst, hlen', ?_⟩
                  intro r hr
                  rcases hcont hr with ⟨exc⟩
                  subst d
                  subst s0
                  exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exc⟩)
    (fun {devm devm'} d hpop => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      cases a with
      | nil => simp [checkNodeM] at hcheck
      | cons av a' =>
        cases av with
        | const c => simp [checkNodeM] at hcheck
        | unk => simp [checkNodeM] at hcheck
        | ret =>
          have hcheck' : byteAt code pc = some (Jinst.toUInt8 .jump) ∧
              a'.length = m := by
            simpa [checkNodeM] using hcheck
          have h_at : Jinst.At sevm.code pc .jump := by
            apply byteAt_jinst_at
            rw [hcode]
            exact hcheck'.1
          cases S with
          | nil => cases hframe
          | cons t S1 =>
            cases hframe with
            | cons hhead htail =>
              have ht : t = ρ := hhead
              have hs := popBurnBy_one_stack hpop
              rw [hstack] at hs
              have htx : t = d := by
                simpa using congrArg List.head? hs
              have hd : d = ρ := htx.symm.trans ht
              have hinter : devm'.stack = S1 ++ base := by
                simpa [hd] using (congrArg List.tail? hs).symm
              have hlen : S1.length = m :=
                (List.Forall₂.length_eq htail).symm.trans hcheck'.2
              have hjp : jumpable sevm.code ρ.toNat = true := by
                rw [hcode]
                exact jumpable_of_jumpdestOk (hρ (by simp [RetIn]))
              have hpop' : Devm.PopBurnBy [ρ] gMid devm devm' := by
                simpa [hd] using hpop
              refine ⟨by simp [RetIn], S1, hinter, hlen, ?_⟩
              intro r hr
              rcases hr with ⟨exc⟩
              exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop') exc⟩)
    (fun {devm devm' devm'' k f g} d hget hpop hrun ih => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      cases a with
      | nil => simp [checkNodeM] at hcheck
      | cons av a' =>
        cases av with
        | ret => simp [checkNodeM] at hcheck
        | unk => simp [checkNodeM] at hcheck
        | const t =>
          cases f with
          | dest dcont =>
            cases hk : c.entries[k]? with
            | none => simp [checkNodeM, hk] at hcheck
            | some e =>
              simp [checkNodeM, hk] at hcheck
              simp [jumpsOkNodeM, hk] at hjump
              have hentry := hc k e g hk hget
              have hjentry := hj k e g hk hget
              have hempty : ms[k]?.getD [] = [] := hcheck.1.2
              have hmemc : MemMatches 0 (ms.getD k []) devm'.memory := by
                simp only [List.getD_eq_getElem?_getD, hempty]; exact memMatches_nil _ _
              have h_at : Jinst.At sevm.code pc .jump := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck.1.1.1.1
              cases S with
              | nil => cases hframe
              | cons s0 S1 =>
                cases hframe with
                | cons h0 htail =>
                  have hs0 : s0 = t := h0
                  have hs := popBurnBy_one_stack hpop
                  rw [hstack] at hs
                  have hd : s0 = d := (List.cons.inj hs).1
                  have hdt : d = t := hd.symm.trans hs0
                  have hinter : devm'.stack = S1 ++ base :=
                    (List.cons.inj hs).2.symm
                  have hje : jumpdestOk code t.toNat = true := by
                    simpa [hcheck.1.1.1.2] using hjump.1
                  have hjp : jumpable sevm.code t.toNat = true := by
                    rw [hcode]
                    exact jumpable_of_jumpdestOk hje
                  have hentry' :
                      checkNodeM code c.entries ms b e.rets t.toNat e.frame (ms.getD k []) g = true := by
                    simpa [hcheck.1.1.1.2] using hentry
                  cases hidx : e.frame.findIdx? (· == .ret) with
                  | none =>
                    have hcall : callCompat 0 a' e.frame = true := by
                      simpa [hidx] using hcheck.2
                    rcases frameMatches_callCompat hcall htail with
                      ⟨Sf, Sr, hsplit, hframee, hframer⟩
                    have hstacke : devm'.stack = Sf ++ (Sr ++ base) := by
                      rw [hinter, hsplit]
                      simp [List.append_assoc]
                    have hrec := ih t.toNat e.rets e.frame 0 Sf (Sr ++ base) (ms.getD k [])
                      hentry' hjentry hstacke hframee hmemc (by
                        intro hret
                        rcases hret with hret | hret
                        · exact (ret_not_mem_of_findIdx_none hidx AVal.ret hret rfl).elim
                        · simp [List.getD_eq_getElem?_getD, hempty] at hret)
                    rcases hrec with ⟨exc⟩
                    subst d
                    subst s0
                    exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exc⟩
                  | some i =>
                    cases haidx : a'[i]? with
                    | none => simp [hidx, haidx] at hcheck
                    | some av =>
                      cases av with
                      | ret => simp [hidx, haidx] at hcheck
                      | unk => simp [hidx, haidx] at hcheck
                      | const r =>
                        have hcall : callCompat r a' e.frame = true ∧
                            byteAt code r.toNat = some (Jinst.toUInt8 .jumpdest) ∧
                            checkNodeM code c.entries ms b m (r.toNat + 1)
                              (List.replicate e.rets .unk ++
                                a'.drop e.frame.length) [] dcont = true := by
                          simpa [hidx, haidx, Bool.and_eq_true] using hcheck.2
                        rcases frameMatches_callCompat hcall.1 htail with
                          ⟨Sf, Sr, hsplit, hframee, hframer⟩
                        have hstacke : devm'.stack = Sf ++ (Sr ++ base) := by
                          rw [hinter, hsplit]
                          simp [List.append_assoc]
                        have hframee' : FrameMatches r e.frame Sf := hframee
                        have hjr : jumpdestOk code r.toNat = true := by
                          have hh : jumpdestOk code e.pc = true ∧
                              jumpdestOk code r.toNat = true ∧
                                jumpsOkNodeM code c.entries b dcont
                                  (List.replicate e.rets .unk ++
                                    a'.drop e.frame.length) [] = true := by
                            simpa [jumpsOkNodeM, hk, hidx, haidx,
                              Bool.and_eq_true] using hjump
                          exact hh.2.1
                        have hrec := ih t.toNat e.rets e.frame r Sf (Sr ++ base) (ms.getD k [])
                          hentry' hjentry hstacke hframee'
                          (by simp only [List.getD_eq_getElem?_getD, hempty]
                              exact memMatches_nil _ _) (by
                            intro _
                            exact hjr)
                        rcases hrec with ⟨exc⟩
                        subst d
                        subst s0
                        exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exc⟩
          | branch _ _ => simp [checkNodeM] at hcheck
          | branchTo _ _ => simp [checkNodeM] at hcheck
          | last _ => simp [checkNodeM] at hcheck
          | next _ _ => simp [checkNodeM] at hcheck
          | jump _ => simp [checkNodeM] at hcheck
          | callNext _ _ => simp [checkNodeM] at hcheck
          | ret => simp [checkNodeM] at hcheck
          | pcAt _ _ => simp [checkNodeM] at hcheck
          | undefined => simp [checkNodeM] at hcheck)
    (fun {devm devm' devm'' k f g o} d hget hpop hrun hcont ihrun ihcont => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      cases a with
      | nil => simp [checkNodeM] at hcheck
      | cons av a' =>
        cases av with
        | ret => simp [checkNodeM] at hcheck
        | unk => simp [checkNodeM] at hcheck
        | const t =>
          cases f with
          | dest dcont =>
            cases hk : c.entries[k]? with
            | none => simp [checkNodeM, hk] at hcheck
            | some e =>
              simp [checkNodeM, hk] at hcheck
              simp [jumpsOkNodeM, hk] at hjump
              have hentry := hc k e g hk hget
              have hjentry := hj k e g hk hget
              have hempty : ms[k]?.getD [] = [] := hcheck.1.2
              have hmemc : MemMatches 0 (ms.getD k []) devm'.memory := by
                simp only [List.getD_eq_getElem?_getD, hempty]; exact memMatches_nil _ _
              have h_at : Jinst.At sevm.code pc .jump := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck.1.1.1.1
              cases S with
              | nil => cases hframe
              | cons s0 S1 =>
                cases hframe with
                | cons h0 htail =>
                  have hs0 : s0 = t := h0
                  have hs := popBurnBy_one_stack hpop
                  rw [hstack] at hs
                  have hd : s0 = d := (List.cons.inj hs).1
                  have hdt : d = t := hd.symm.trans hs0
                  have hinter : devm'.stack = S1 ++ base :=
                    (List.cons.inj hs).2.symm
                  have hje : jumpdestOk code t.toNat = true := by
                    simpa [hcheck.1.1.1.2] using hjump.1
                  have hjp : jumpable sevm.code t.toNat = true := by
                    rw [hcode]
                    exact jumpable_of_jumpdestOk hje
                  have hentry' :
                      checkNodeM code c.entries ms b e.rets t.toNat e.frame (ms.getD k []) g = true := by
                    simpa [hcheck.1.1.1.2] using hentry
                  cases hidx : e.frame.findIdx? (· == .ret) with
                  | none =>
                    have hcall : callCompat 0 a' e.frame = true := by
                      simpa [hidx] using hcheck.2
                    have hret_no : ∀ x, x ∈ e.frame → x ≠ AVal.ret :=
                      ret_not_mem_of_findIdx_none hidx
                    rcases frameMatches_callCompat hcall htail with
                      ⟨Sf, Sr, hsplit, hframee, hframer⟩
                    have hstacke : devm'.stack = Sf ++ (Sr ++ base) := by
                      rw [hinter, hsplit]
                      simp [List.append_assoc]
                    have hretno : ¬ RetIn e.frame (ms.getD k []) := by
                      intro hret
                      rcases hret with hret | hret
                      · exact hret_no AVal.ret hret rfl
                      · simp [List.getD_eq_getElem?_getD, hempty] at hret
                    have hrec := ihrun t.toNat e.rets e.frame 0 Sf (Sr ++ base) (ms.getD k [])
                      hentry' hjentry hstacke hframee hmemc (fun h => (hretno h).elim)
                    rcases hrec with ⟨hret, Sret, hst, hlen, hchildcont⟩
                    exact (hretno hret).elim
                  | some i =>
                    cases haidx : a'[i]? with
                    | none => simp [hidx, haidx] at hcheck
                    | some av =>
                      cases av with
                      | ret => simp [hidx, haidx] at hcheck
                      | unk => simp [hidx, haidx] at hcheck
                      | const r =>
                        have hcall : callCompat r a' e.frame = true ∧
                            byteAt code r.toNat = some (Jinst.toUInt8 .jumpdest) ∧
                            checkNodeM code c.entries ms b m (r.toNat + 1)
                              (List.replicate e.rets .unk ++
                                a'.drop e.frame.length) [] dcont = true := by
                          simpa [hidx, haidx, Bool.and_eq_true] using hcheck.2
                        rcases frameMatches_callCompat hcall.1 htail with
                          ⟨Sf, Sr, hsplit, hframee, hframer⟩
                        have hstacke : devm'.stack = Sf ++ (Sr ++ base) := by
                          rw [hinter, hsplit]
                          simp [List.append_assoc]
                        have hjr : jumpdestOk code r.toNat = true := by
                          have hh : jumpdestOk code e.pc = true ∧
                              jumpdestOk code r.toNat = true ∧
                                jumpsOkNodeM code c.entries b dcont
                                  (List.replicate e.rets .unk ++
                                    a'.drop e.frame.length) [] = true := by
                            simpa [jumpsOkNodeM, hk, hidx, haidx,
                              Bool.and_eq_true] using hjump
                          exact hh.2.1
                        have hrec := ihrun t.toNat e.rets e.frame r Sf (Sr ++ base) (ms.getD k [])
                          hentry' hjentry hstacke hframee
                          (by simp only [List.getD_eq_getElem?_getD, hempty]
                              exact memMatches_nil _ _) (by
                            intro _
                            exact hjr)
                        rcases hrec with ⟨hret, Sret, hst, hlen, hchildcont⟩
                        have hunk : FrameMatches ρ
                            (List.replicate e.rets .unk) Sret := by
                          rw [← hlen]
                          exact frameMatches_unk_length Sret
                        let framec :=
                          List.replicate e.rets .unk ++ a'.drop e.frame.length
                        have hframec : FrameMatches ρ framec (Sret ++ Sr) := by
                          apply matches_to_frame
                          rw [List.map_append]
                          apply matches_append
                          · exact frameMatches_matches hunk
                          · exact frameMatches_matches hframer
                        have hst' : devm''.stack = (Sret ++ Sr) ++ base := by
                          simpa [framec, List.append_assoc] using hst
                        have hretc : RetIn framec [] → AVal.ret ∈ a' := by
                          intro h
                          rcases h with h | h
                          · rcases List.mem_append.mp h with h | h
                            · simp at h
                            · exact List.mem_of_mem_drop h
                          · simp at h
                        have hρc : RetIn framec [] →
                            jumpdestOk code ρ.toNat = true := by
                          intro h
                          exact hρ (.inl (List.mem_cons_of_mem _ (hretc h)))
                        have hcheckc :
                            checkNodeM code c.entries ms b m r.toNat framec []
                              (.dest dcont) = true := by
                          simp [framec, checkNodeM, hcall.2.1, hcall.2.2]
                        have hjumpc : jumpsOkNodeM code c.entries b
                            (.dest dcont) framec [] = true := by
                          have hh : jumpdestOk code e.pc = true ∧
                              jumpdestOk code r.toNat = true ∧
                                jumpsOkNodeM code c.entries b dcont framec [] = true := by
                            simpa [framec, jumpsOkNodeM, hk, hidx, haidx,
                              Bool.and_eq_true] using hjump
                          exact hh.2.2
                        cases o with
                        | halted post =>
                          have hrec2 := ihcont r.toNat m framec ρ
                            (Sret ++ Sr) base [] hcheckc hjumpc hst' hframec
                            (memMatches_nil _ _) hρc
                          rcases hrec2 with ⟨exc2⟩
                          rcases hchildcont ⟨exc2⟩ with ⟨exct⟩
                          subst d
                          subst s0
                          exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exct⟩
                        | returned devmfinal =>
                          have hrec2 := ihcont r.toNat m framec ρ
                            (Sret ++ Sr) base [] hcheckc hjumpc hst' hframec
                            (memMatches_nil _ _) hρc
                          rcases hrec2 with
                            ⟨hret2, S2, hst2, hlen2, hcont2⟩
                          have hret_a' : AVal.ret ∈ a' := hretc hret2
                          refine ⟨.inl (List.mem_cons_of_mem _ hret_a'), S2, hst2,
                            hlen2, ?_⟩
                          intro r2 hr2
                          rcases hcont2 hr2 with ⟨exc2⟩
                          rcases hchildcont ⟨exc2⟩ with ⟨exct⟩
                          subst d
                          subst s0
                          exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exct⟩
          | branch _ _ => simp [checkNodeM] at hcheck
          | branchTo _ _ => simp [checkNodeM] at hcheck
          | last _ => simp [checkNodeM] at hcheck
          | next _ _ => simp [checkNodeM] at hcheck
          | jump _ => simp [checkNodeM] at hcheck
          | callNext _ _ => simp [checkNodeM] at hcheck
          | ret => simp [checkNodeM] at hcheck
          | pcAt _ _ => simp [checkNodeM] at hcheck
          | undefined => simp [checkNodeM] at hcheck)
    (fun {devm devm' p f o} hstepPc _ ih => by
      intro pc m a ρ S base μ hcheck hjump hstack hframe hmem hρ
      have hcheck' :
          (bytesAt code pc (Ninst.toBytes (Ninst.reg .pc)) = true ∧ p = pc) ∧
            checkNodeM code c.entries ms b m (pc + 1) (.const (Nat.toB256 pc) :: a) μ f = true := by
        simpa [checkNodeM] using hcheck
      obtain ⟨⟨hbytes, rfl⟩, hchild⟩ := hcheck'
      have h_at : Ninst.At sevm.code p (Ninst.reg .pc) := by
        apply Ninst.at_of_slice
        apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.reg .pc))
        rw [hcode]
        exact hbytes
      have hstack' : devm'.stack = Nat.toB256 p :: (S ++ base) := by
        rw [pc_stepRun_stack hstepPc, hstack]
      have hframe' :
          FrameMatches ρ (.const (Nat.toB256 p) :: a) (Nat.toB256 p :: S) :=
        List.Forall₂.cons rfl hframe
      have hrec := ih (p + 1) m (.const (Nat.toB256 p) :: a) ρ (Nat.toB256 p :: S) base μ
        hchild (by simpa [jumpsOkNodeM] using hjump) hstack' hframe'
        (hmem.of_memory_eq (pc_stepRun_memory hstepPc).symm) (by
          intro h
          exact hρ (RetIn.of_frame (fun h => by simpa using h) h))
      cases o with
      | halted post =>
        rcases hrec with ⟨exc⟩
        exact Ninst.exec_of_stepRun (xl := .none) h_at trivial hstepPc ⟨exc⟩
      | returned devm'' =>
        rcases hrec with ⟨hret, Sret, hst, hlenret, hcont⟩
        refine ⟨RetIn.of_frame (fun h => by simpa using h) hret, Sret, hst, hlenret, ?_⟩
        intro r hr
        rcases hcont hr with ⟨exc⟩
        exact Ninst.exec_of_stepRun (xl := .none) h_at trivial hstepPc ⟨exc⟩)
    run

/-- The gas-exact converse from checked, jump-safe entries whose entry `0`
starts the frame. -/
theorem lift_exactM_core {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool}
    (hc : Cert.CheckedM code c ms b) (hj : Cert.JumpsOkM code c ms b)
    (hstart : ∃ e f c', c = (e, f) :: c' ∧ e.pc = 0 ∧ e.frame = [] ∧ ms.getD 0 [] = [])
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hrun : SProg.RunExact c.prog sevm pre post) :
    Nonempty (Exec 0 sevm pre (.ok post)) := by
  obtain ⟨e, f, cs, rfl, hepc, hef, hm0⟩ := hstart
  rcases hrun with ⟨f0, hf0, hrf⟩
  have hf0' : f0 = f := by simpa [Cert.prog] using hf0.symm
  subst f0
  have hf := hc 0 e f (by simp [Cert.entries]) (by simp [Cert.prog])
  have hentry := hj 0 e f (by simp [Cert.entries]) (by simp [Cert.prog])
  rw [hm0, hepc, hef] at hf
  rw [hm0, hef] at hentry
  exact node_exactM hc hj hcode hfork hrf 0 e.rets [] 0 [] pre.stack [] hf hentry rfl
    (by simp [FrameMatches]) (memMatches_nil _ _) (fun h => absurd h retIn_nil_nil)

/-- The top-level gas-exact converse. -/
theorem lift_exact {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hrun : SProg.RunExact c.prog sevm pre post) :
    Nonempty (Exec 0 sevm pre (.ok post)) := by
  apply lift_exactM_core (Cert.checkedM_of_check hc) (Cert.jumpsOkM_of_jumpsOk hj) _
    hcode hfork hrun
  cases c with
  | nil => simp [Cert.check] at hc
  | cons p cs =>
    rcases p with ⟨e, f⟩
    simp [Cert.check] at hc
    exact ⟨e, f, cs, rfl, by simpa using hc.1.1, by simpa using hc.1.2, by simp⟩

/-- **The gas-exact converse, with a constant memory map.** -/
theorem lift_exactM {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool}
    (hc : Cert.checkM code c ms b = true) (hj : Cert.jumpsOkM code c ms b = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hrun : SProg.RunExact c.prog sevm pre post) :
    Nonempty (Exec 0 sevm pre (.ok post)) := by
  apply lift_exactM_core (Cert.checkedM_of_checkM hc) (Cert.jumpsOkM_of_jumpsOkM hj) _
    hcode hfork hrun
  cases c with
  | nil => simp [Cert.checkM] at hc
  | cons p cs =>
    rcases p with ⟨e, f⟩
    simp only [Cert.checkM, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hc
    exact ⟨e, f, cs, rfl, hc.1.1.1, hc.1.1.2, hc.1.2⟩

end Blanc.Lift
