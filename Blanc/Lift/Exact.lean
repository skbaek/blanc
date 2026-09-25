import Blanc.Lift.Sound
import Blanc.Lift.Jumpdest
import Blanc.Lift.Weth9.Cert

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
    h

theorem SProg.Run.of_runExact {fs : List SFunc} {sevm : Sevm} {devm devm' : Devm}
    (h : SProg.RunExact fs sevm devm devm') : SProg.Run fs sevm devm devm' := by
  rcases h with ⟨f, hf, hr⟩
  exact ⟨f, hf, SFunc.RunExact.toRun hr⟩

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
    | .const t :: _ :: a' =>
      jumpdestOk code t.toNat && jumpsOkNode code es f a' &&
        jumpsOkNode code es g a'
    | _ => false
  | .branchTo f k, a =>
    match a, es[k]? with
    | .const _ :: _ :: a', some e =>
      jumpdestOk code e.pc && jumpsOkNode code es f a'
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
  | .undefined, _ => true

def Cert.jumpsOk (code : ByteArray) (c : Cert) : Bool :=
  c.all fun (e, f) => jumpsOkNode code c.entries f e.frame

lemma cert_jumpsOk_at {code : ByteArray} {c : Cert}
    (hc : Cert.jumpsOk code c = true) (k : Nat) (e : Entry) (f : SFunc)
    (he : c.entries[k]? = some e) (hf : c.prog[k]? = some f) :
    jumpsOkNode code c.entries f e.frame = true := by
  have hmem := cert_pair_mem c k e f he hf
  have h := (List.all_eq_true.mp hc) (e, f) hmem
  exact h

private lemma burnBy_state {cost : Nat} {devm devm' : Devm}
    (h : Devm.BurnBy cost devm devm') :
    devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - cost, devm.stateGas⟩ = devm' := by
  refine Devm.eq_of_proj h.stack h.memory ?_ h.logs h.refundCounter h.output
    h.accountsToDelete h.returnData h.error h.accessedAddresses
    h.accessedStorageKeys h.state h.createdAccounts h.transientStorage h.stateGas
    h.accountReads h.storageReads
  have hg := h.gasLeft
  change devm.gasLeft - cost = devm'.gasLeft
  omega

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

private def ExactResult (code : ByteArray) (c : Cert) (sevm : Sevm)
    (pc m : Nat) (a : List AVal) (f : SFunc) (ρ : B256) (S base : List B256)
    (devm : Devm) : Outcome → Prop
  | .halted post => Nonempty (Exec pc sevm devm (.ok post))
  | .returned devm' =>
    AVal.ret ∈ a ∧ ∃ S', devm'.stack = S' ++ base ∧ S'.length = m ∧
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
    (code : ByteArray) (c : Cert) (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunExact fs sevm devm f o) : Prop :=
  ∀ (pc m : Nat) (a : List AVal) (ρ : B256) (S base : List B256),
    checkNode code c.entries m pc a f = true →
    jumpsOkNode code c.entries f a = true →
    devm.stack = S ++ base →
    FrameMatches ρ a S →
    ExactResult code c sevm pc m a f ρ S base devm o

theorem node_exact {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    (hj : Cert.jumpsOk code c = true) {sevm : Sevm}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunExact c.prog sevm devm f o) :
    ExactClaim code c hcode hfork run := by
  refine SFunc.RunExact.rec
    (fs := c.prog) (sevm := sevm)
    (motive := fun devm f o run => ExactClaim code c hcode hfork run)
    (fun {devm devm' f g o} d hpop hrun ih => by
      intro pc m a ρ S base hcheck hjump hstack hframe
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | const t =>
          cases a0 with
          | nil => simp [checkNode] at hcheck
          | cons av2 a' =>
            have hcheck' :
                (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                  checkNode code c.entries m (pc + 1) a' f = true) ∧
                checkNode code c.entries m t.toNat a' g = true := by
              simpa [checkNode] using hcheck
            have hjump' :
                jumpdestOk code t.toNat = true ∧
                jumpsOkNode code c.entries f a' = true ∧
                jumpsOkNode code c.entries g a' = true := by
              have hh :
                  ((jumpdestOk code t.toNat &&
                    jumpsOkNode code c.entries f a') &&
                    jumpsOkNode code c.entries g a') = true := by
                simpa [jumpsOkNode] using hjump
              have hh' := Eq.mp
                (Bool.and_eq_true_eq_eq_true_and_eq_true
                  (jumpdestOk code t.toNat && jumpsOkNode code c.entries f a')
                  (jumpsOkNode code c.entries g a')) hh
              have hleft := Eq.mp
                (Bool.and_eq_true_eq_eq_true_and_eq_true
                  (jumpdestOk code t.toNat)
                  (jumpsOkNode code c.entries f a')) hh'.1
              exact ⟨hleft.1, hleft.2, hh'.2⟩
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
                      have hrec := ih (pc + 1) m a' ρ S1 base
                        hcheck'.1.2 hjump'.2.1 (by
                          have hs := popBurnBy_two_stack hpop
                          rw [hstack] at hs
                          have htail' : s1 :: (S1 ++ base) = 0 :: devm'.stack :=
                            (List.cons.inj hs).2
                          exact (List.cons.inj htail').2.symm) htail
                      rcases hrec with ⟨exc⟩
                      exact ⟨Exec.cont (jumpi_zero_cont h_at hpop) exc⟩
                    | returned devm'' =>
                      have hs := popBurnBy_two_stack hpop
                      rw [hstack] at hs
                      have htail' : s1 :: (S1 ++ base) = 0 :: devm'.stack := by
                        exact (List.cons.inj hs).2
                      have hinter : devm'.stack = S1 ++ base :=
                        (List.cons.inj htail').2.symm
                      have hrec := ih (pc + 1) m a' ρ S1 base
                        hcheck'.1.2 hjump'.2.1 hinter htail
                      rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
                      refine ⟨List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _ hret), S', hst, hlen, ?_⟩
                      intro r hr
                      rcases hcont hr with ⟨exc⟩
                      exact ⟨Exec.cont (jumpi_zero_cont h_at hpop) exc⟩)
    (fun {devm devm' f g o} d w hne hpop hrun ih => by
      intro pc m a ρ S base hcheck hjump hstack hframe
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | const t =>
          cases a0 with
          | nil => simp [checkNode] at hcheck
          | cons av2 a' =>
            have hcheck' :
                (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                  checkNode code c.entries m (pc + 1) a' f = true) ∧
                checkNode code c.entries m t.toNat a' g = true := by
              simpa [checkNode] using hcheck
            have hjump' :
                jumpdestOk code t.toNat = true ∧
                jumpsOkNode code c.entries f a' = true ∧
                jumpsOkNode code c.entries g a' = true := by
              have hh :
                  ((jumpdestOk code t.toNat &&
                    jumpsOkNode code c.entries f a') &&
                    jumpsOkNode code c.entries g a') = true := by
                simpa [jumpsOkNode] using hjump
              have hh' := Eq.mp
                (Bool.and_eq_true_eq_eq_true_and_eq_true
                  (jumpdestOk code t.toNat && jumpsOkNode code c.entries f a')
                  (jumpsOkNode code c.entries g a')) hh
              have hleft := Eq.mp
                (Bool.and_eq_true_eq_eq_true_and_eq_true
                  (jumpdestOk code t.toNat)
                  (jumpsOkNode code c.entries f a')) hh'.1
              exact ⟨hleft.1, hleft.2, hh'.2⟩
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
                      have hrec := ih (t.toNat) m a' ρ S1 base
                        hcheck'.2 hjump'.2.2 (by
                          exact (List.cons.inj (List.cons.inj hs).2).2.symm) htail
                      rcases hrec with ⟨exc⟩
                      subst d
                      subst s0
                      exact ⟨Exec.cont (jumpi_succ_cont h_at hne hjp' hpop) exc⟩
                    | returned devm'' =>
                      have hinter : devm'.stack = S1 ++ base := by
                        exact (List.cons.inj (List.cons.inj hs).2).2.symm
                      have hrec := ih (t.toNat) m a' ρ S1 base
                        hcheck'.2 hjump'.2.2 hinter htail
                      rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
                      refine ⟨List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _ hret), S', hst, hlen, ?_⟩
                      intro r hr
                      rcases hcont hr with ⟨exc⟩
                      subst d
                      subst s0
                      exact ⟨Exec.cont (jumpi_succ_cont h_at hne hjp' hpop) exc⟩)
    (fun {devm devm' f k o} d hpop hrun ih => by
      intro pc m a ρ S base hcheck hjump hstack hframe
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | const t =>
          cases a0 with
          | nil => simp [checkNode] at hcheck
          | cons av2 a' =>
            cases hk : c.entries[k]? with
            | none => simp [checkNode, hk] at hcheck
            | some e =>
              have hcheck' :
                  (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                    e.pc = t.toNat) ∧ e.rets = m) ∧
                    gotoCompat a' e.frame = true) ∧
                    checkNode code c.entries m (pc + 1) a' f = true := by
                simpa [checkNode, hk] using hcheck
              have hjump' :
                  jumpdestOk code e.pc = true ∧
                    jumpsOkNode code c.entries f a' = true := by
                simpa [jumpsOkNode, hk, Bool.and_eq_true] using hjump
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
                        have hrec := ih (pc + 1) m a' ρ S1 base
                          hcheck'.2 hjump'.2 hinter htail
                        rcases hrec with ⟨exc⟩
                        exact ⟨Exec.cont (jumpi_zero_cont h_at hpop) exc⟩
                      | returned devm'' =>
                        have hrec := ih (pc + 1) m a' ρ S1 base
                          hcheck'.2 hjump'.2 hinter htail
                        rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
                        refine ⟨List.mem_cons_of_mem _
                            (List.mem_cons_of_mem _ hret), S', hst, hlen, ?_⟩
                        intro r hr
                        rcases hcont hr with ⟨exc⟩
                        exact ⟨Exec.cont (jumpi_zero_cont h_at hpop) exc⟩)
    (fun {devm devm' f g k o} d w hne hget hpop hrun ih => by
      intro pc m a ρ S base hcheck hjump hstack hframe
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | const t =>
          cases a0 with
          | nil => simp [checkNode] at hcheck
          | cons av2 a' =>
            cases hk : c.entries[k]? with
            | none => simp [checkNode, hk] at hcheck
            | some e =>
              have hcheck' :
                  (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                    e.pc = t.toNat) ∧ e.rets = m) ∧
                    gotoCompat a' e.frame = true) ∧
                    checkNode code c.entries m (pc + 1) a' f = true := by
                simpa [checkNode, hk] using hcheck
              rcases cert_prog_of_entry c k e hk with ⟨g', hg'⟩
              have hgg : g = g' := Option.some.inj (hget.symm.trans hg')
              subst g'
              have hentry := cert_check_at hc k e g hk hg'
              have hjump' :
                  jumpdestOk code e.pc = true ∧
                    jumpsOkNode code c.entries f a' = true := by
                simpa [jumpsOkNode, hk, Bool.and_eq_true] using hjump
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
                          checkNode code c.entries e.rets t.toNat e.frame g = true := by
                        simpa [hcheck'.1.1.1.2] using hentry
                      have hjg : jumpsOkNode code c.entries g e.frame = true :=
                        cert_jumpsOk_at hj k e g hk hget
                      cases o with
                      | halted post =>
                        have hrec := ih t.toNat e.rets e.frame ρ S1 base
                          hentry' hjg hinter hframe'
                        rcases hrec with ⟨exc⟩
                        subst d
                        subst s0
                        exact ⟨Exec.cont (jumpi_succ_cont h_at hne hjp hpop) exc⟩
                      | returned devm'' =>
                        have hrec := ih t.toNat e.rets e.frame ρ S1 base
                          hentry' hjg hinter hframe'
                        rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
                        have hret' : AVal.ret ∈ a' :=
                          ret_mem_of_gotoCompat hcheck'.1.2 hret
                        have hlen' : S'.length = m := by
                          simpa [hcheck'.1.1.2] using hlen
                        refine ⟨List.mem_cons_of_mem _
                            (List.mem_cons_of_mem _ hret'), S', hst, hlen', ?_⟩
                        intro r hr
                        rcases hcont hr with ⟨exc⟩
                        subst d
                        subst s0
                        exact ⟨Exec.cont (jumpi_succ_cont h_at hne hjp hpop) exc⟩)
    (fun {devm devm' l} hrun => by
      intro pc m a ρ S base hcheck hjump hstack hframe
      have hbyte : byteAt code pc = some l.toUInt8 := by
        simpa [checkNode] using hcheck
      have h_at : Linst.At sevm.code pc l := by
        apply byteAt_linst_at
        rw [hcode]
        exact hbyte
      refine ⟨Exec.halt ?_⟩
      rw [Evm.step_last h_at]
      exact congrArg Step.halt hrun)
    (fun {devm devm' n f o} hrun hnext ih => by
      intro pc m a ρ S base hcheck hjump hstack hframe
      rcases hrun with ⟨xl, hfilled, hsteps⟩
      have hrunN : Ninst.Run sevm devm n devm' := ⟨xl, hfilled, 0, hsteps 0⟩
      have next_nonpush (n0 : Ninst) (a0 : List AVal) (out : Pattern)
          (hlen : a.length ≤ 1024)
          (htrans : ninstTransfer n0 (indexPattern a.length) = some out)
          (hread : out.mapM (readBack a) = some a0)
          (hchild : checkNode code c.entries m (pc + n0.size) a0 f = true)
          (hjump0 : jumpsOkNode code c.entries f a0 = true)
          (hstep0 : Ninst.StepRun pc sevm devm n0 xl (.ok devm'))
          (h_at : Ninst.At sevm.code pc n0) :
          ExactResult code c sevm pc m a (SFunc.next n0 f) ρ S base devm o := by
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
        have hframe' : FrameMatches ρ a0 S' := matches_to_frame hfirst
        have hrec := ih (pc + n0.size) m a0 ρ S' base
          hchild hjump0 hinter hframe'
        cases o with
        | halted post =>
          rcases hrec with ⟨exc⟩
          exact Ninst.exec_of_stepRun h_at hfilled hstep0 ⟨exc⟩
        | returned devm'' =>
          rcases hrec with ⟨hret, Sret, hst, hlenret, hcont⟩
          have hret' : AVal.ret ∈ a := ret_mem_of_readBack hread hret
          refine ⟨hret', Sret, hst, hlenret, ?_⟩
          intro r hr
          rcases hcont hr with ⟨exc⟩
          exact Ninst.exec_of_stepRun h_at hfilled hstep0 ⟨exc⟩
      cases n with
      | push bs fits =>
        have hcheck' :
            (bytesAt code pc (Ninst.toBytes (Ninst.push bs fits)) = true ∧
              Ninst.pcFree (Ninst.push bs fits) = true) ∧
            checkNode code c.entries m (pc + (Ninst.push bs fits).size)
              (.const (Bytes.toB256 bs) :: a) f = true := by
          simpa [checkNode, absNinst] using hcheck
        have h_at : Ninst.At sevm.code pc (.push bs fits) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.push bs fits))
          rw [hcode]
          exact hcheck'.1.1
        have hstack' : devm'.stack = Bytes.toB256 bs :: (S ++ base) := by
          rw [push_run_stack hrunN, hstack]
        have hframe' :
            FrameMatches ρ (.const (Bytes.toB256 bs) :: a)
              (Bytes.toB256 bs :: S) := List.Forall₂.cons rfl hframe
        have hrec := ih (pc + (Ninst.push bs fits).size) m
          (.const (Bytes.toB256 bs) :: a) ρ (Bytes.toB256 bs :: S) base
          hcheck'.2 (by simpa [jumpsOkNode, absNinst] using hjump) hstack' hframe'
        cases o with
        | halted post =>
          rcases hrec with ⟨exc⟩
          exact Ninst.exec_of_stepRun h_at hfilled (hsteps pc) ⟨exc⟩
        | returned devm'' =>
          rcases hrec with ⟨hret, Sret, hst, hlenret, hcont⟩
          refine ⟨by simpa using hret, Sret, hst, hlenret, ?_⟩
          intro r hr
          rcases hcont hr with ⟨exc⟩
          exact Ninst.exec_of_stepRun h_at hfilled (hsteps pc) ⟨exc⟩
      | reg r =>
        simp only [checkNode, Bool.and_eq_true] at hcheck
        have h_at : Ninst.At sevm.code pc (Ninst.reg r) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.reg r))
          rw [hcode]
          exact hcheck.1.1
        cases ha : absNinst (Ninst.reg r) a with
        | none => simp [ha] at hcheck
        | some a0 =>
          have hchild : checkNode code c.entries m (pc + (Ninst.reg r).size) a0 f = true := by
            simpa [ha] using hcheck.2
          rcases absNinst_nonpush_spec (by
            intro bs fits h
            cases h) ha with ⟨hlen, out, htrans, hread⟩
          have hjump' : jumpsOkNode code c.entries f a0 = true := by
            simpa [jumpsOkNode, ha] using hjump
          exact next_nonpush (Ninst.reg r) a0 out hlen htrans hread hchild hjump'
            (hsteps pc) h_at
      | exec x =>
        simp only [checkNode, Bool.and_eq_true] at hcheck
        have h_at : Ninst.At sevm.code pc (Ninst.exec x) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.exec x))
          rw [hcode]
          exact hcheck.1.1
        cases ha : absNinst (Ninst.exec x) a with
        | none => simp [ha] at hcheck
        | some a0 =>
          have hchild : checkNode code c.entries m (pc + (Ninst.exec x).size) a0 f = true := by
            simpa [ha] using hcheck.2
          rcases absNinst_nonpush_spec (by
            intro bs fits h
            cases h) ha with ⟨hlen, out, htrans, hread⟩
          have hjump' : jumpsOkNode code c.entries f a0 = true := by
            simpa [jumpsOkNode, ha] using hjump
          exact next_nonpush (Ninst.exec x) a0 out hlen htrans hread hchild hjump'
            (hsteps pc) h_at
      | dupn i =>
        simp only [checkNode, Bool.and_eq_true] at hcheck
        have h_at : Ninst.At sevm.code pc (Ninst.dupn i) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.dupn i))
          rw [hcode]
          exact hcheck.1.1
        cases ha : absNinst (Ninst.dupn i) a with
        | none => simp [ha] at hcheck
        | some a0 =>
          have hchild : checkNode code c.entries m (pc + (Ninst.dupn i).size) a0 f = true := by
            simpa [ha] using hcheck.2
          rcases absNinst_nonpush_spec (by
            intro bs fits h
            cases h) ha with ⟨hlen, out, htrans, hread⟩
          have hjump' : jumpsOkNode code c.entries f a0 = true := by
            simpa [jumpsOkNode, ha] using hjump
          exact next_nonpush (Ninst.dupn i) a0 out hlen htrans hread hchild hjump'
            (hsteps pc) h_at
      | swapn i =>
        simp only [checkNode, Bool.and_eq_true] at hcheck
        have h_at : Ninst.At sevm.code pc (Ninst.swapn i) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.swapn i))
          rw [hcode]
          exact hcheck.1.1
        cases ha : absNinst (Ninst.swapn i) a with
        | none => simp [ha] at hcheck
        | some a0 =>
          have hchild : checkNode code c.entries m (pc + (Ninst.swapn i).size) a0 f = true := by
            simpa [ha] using hcheck.2
          rcases absNinst_nonpush_spec (by
            intro bs fits h
            cases h) ha with ⟨hlen, out, htrans, hread⟩
          have hjump' : jumpsOkNode code c.entries f a0 = true := by
            simpa [jumpsOkNode, ha] using hjump
          exact next_nonpush (Ninst.swapn i) a0 out hlen htrans hread hchild hjump'
            (hsteps pc) h_at
      | exchange i =>
        simp only [checkNode, Bool.and_eq_true] at hcheck
        have h_at : Ninst.At sevm.code pc (Ninst.exchange i) := by
          apply Ninst.at_of_slice
          apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.exchange i))
          rw [hcode]
          exact hcheck.1.1
        cases ha : absNinst (Ninst.exchange i) a with
        | none => simp [ha] at hcheck
        | some a0 =>
          have hchild : checkNode code c.entries m (pc + (Ninst.exchange i).size) a0 f = true := by
            simpa [ha] using hcheck.2
          rcases absNinst_nonpush_spec (by
            intro bs fits h
            cases h) ha with ⟨hlen, out, htrans, hread⟩
          have hjump' : jumpsOkNode code c.entries f a0 = true := by
            simpa [jumpsOkNode, ha] using hjump
          exact next_nonpush (Ninst.exchange i) a0 out hlen htrans hread hchild hjump'
            (hsteps pc) h_at)
    (fun {devm devm' f o} hburn hrun ih => by
      intro pc m a ρ S base hcheck hjump hstack hframe
      have hcheck' :
          byteAt code pc = some (Jinst.toUInt8 .jumpdest) ∧
            checkNode code c.entries m (pc + 1) a f = true := by
        simpa [checkNode] using hcheck
      have h_at : Jinst.At sevm.code pc .jumpdest := by
        apply byteAt_jinst_at
        rw [hcode]
        exact hcheck'.1
      have hstack' : devm'.stack = S ++ base := by
        rw [← hburn.stack, hstack]
      have hrec := ih (pc + 1) m a ρ S base
        hcheck'.2 (by simpa [jumpsOkNode] using hjump) hstack' hframe
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
      intro pc m a ρ S base hcheck hjump hstack hframe
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a' =>
        cases av with
        | ret => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | const t =>
          cases hk : c.entries[k]? with
          | none => simp [checkNode, hk] at hcheck
          | some e =>
            have hcheck' :
                (((byteAt code pc = some (Jinst.toUInt8 .jump) ∧
                  e.pc = t.toNat) ∧ e.rets = m) ∧
                  gotoCompat a' e.frame = true) := by
              simpa [checkNode, hk] using hcheck
            rcases cert_prog_of_entry c k e hk with ⟨g, hg⟩
            have hfg : f = g := Option.some.inj (hget.symm.trans hg)
            subst g
            have hentry := cert_check_at hc k e f hk hg
            have hjump' : jumpdestOk code e.pc = true := by
              simpa [jumpsOkNode, hk] using hjump
            have hjg : jumpsOkNode code c.entries f e.frame = true :=
              cert_jumpsOk_at hj k e f hk hg
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
                    checkNode code c.entries e.rets t.toNat e.frame f = true := by
                  simpa [hcheck'.1.1.2] using hentry
                cases o with
                | halted post =>
                  have hrec := ih t.toNat e.rets e.frame ρ S1 base
                    hentry' hjg hinter hframe'
                  rcases hrec with ⟨exc⟩
                  subst d
                  subst s0
                  exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exc⟩
                | returned devm'' =>
                  have hrec := ih t.toNat e.rets e.frame ρ S1 base
                    hentry' hjg hinter hframe'
                  rcases hrec with ⟨hret, S', hst, hlen, hcont⟩
                  have hret' : AVal.ret ∈ a' :=
                    ret_mem_of_gotoCompat hcheck'.2 hret
                  have hlen' : S'.length = m := by
                    simpa [hcheck'.1.2] using hlen
                  refine ⟨List.mem_cons_of_mem _ hret', S', hst, hlen', ?_⟩
                  intro r hr
                  rcases hcont hr with ⟨exc⟩
                  subst d
                  subst s0
                  exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exc⟩)
    (fun {devm devm'} d hpop => by
      intro pc m a ρ S base hcheck hjump hstack hframe
      sorry)
    (fun {devm devm' devm'' k f g} d hget hpop hrun ih => by
      intro pc m a ρ S base hcheck hjump hstack hframe
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a' =>
        cases av with
        | ret => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | const t =>
          cases f with
          | dest dcont =>
            cases hk : c.entries[k]? with
            | none => simp [checkNode, hk] at hcheck
            | some e =>
              simp [checkNode, hk] at hcheck
              simp [jumpsOkNode, hk] at hjump
              have hentry := cert_check_at hc k e g hk hget
              have hjentry := cert_jumpsOk_at hj k e g hk hget
              have h_at : Jinst.At sevm.code pc .jump := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck.1.1.1
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
                    simpa [hcheck.1.1.2] using hjump.1
                  have hjp : jumpable sevm.code t.toNat = true := by
                    rw [hcode]
                    exact jumpable_of_jumpdestOk hje
                  have hentry' :
                      checkNode code c.entries e.rets t.toNat e.frame g = true := by
                    simpa [hcheck.1.1.2] using hentry
                  cases hidx : e.frame.findIdx? (· == .ret) with
                  | none =>
                    have hcall : callCompat 0 a' e.frame = true := by
                      simpa [hidx] using hcheck.2
                    rcases frameMatches_callCompat hcall htail with
                      ⟨Sf, Sr, hsplit, hframee, hframer⟩
                    have hstacke : devm'.stack = Sf ++ (Sr ++ base) := by
                      rw [hinter, hsplit]
                      simp [List.append_assoc]
                    have hrec := ih t.toNat e.rets e.frame 0 Sf (Sr ++ base)
                      hentry' hjentry hstacke hframee
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
                            checkNode code c.entries m (r.toNat + 1)
                              (List.replicate e.rets .unk ++
                                a'.drop e.frame.length) dcont = true := by
                          simpa [hidx, haidx, Bool.and_eq_true] using hcheck.2
                        rcases frameMatches_callCompat hcall.1 htail with
                          ⟨Sf, Sr, hsplit, hframee, hframer⟩
                        have hstacke : devm'.stack = Sf ++ (Sr ++ base) := by
                          rw [hinter, hsplit]
                          simp [List.append_assoc]
                        have hframee' : FrameMatches r e.frame Sf := hframee
                        have hrec := ih t.toNat e.rets e.frame r Sf (Sr ++ base)
                          hentry' hjentry hstacke hframee'
                        rcases hrec with ⟨exc⟩
                        subst d
                        subst s0
                        exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exc⟩
          | branch _ _ => simp [checkNode] at hcheck
          | branchTo _ _ => simp [checkNode] at hcheck
          | last _ => simp [checkNode] at hcheck
          | next _ _ => simp [checkNode] at hcheck
          | jump _ => simp [checkNode] at hcheck
          | callNext _ _ => simp [checkNode] at hcheck
          | ret => simp [checkNode] at hcheck
          | undefined => simp [checkNode] at hcheck)
    (fun {devm devm' devm'' k f g o} d hget hpop hrun hcont ihrun ihcont => by
      intro pc m a ρ S base hcheck hjump hstack hframe
      cases a with
      | nil => simp [checkNode] at hcheck
      | cons av a' =>
        cases av with
        | ret => simp [checkNode] at hcheck
        | unk => simp [checkNode] at hcheck
        | const t =>
          cases f with
          | dest dcont =>
            cases hk : c.entries[k]? with
            | none => simp [checkNode, hk] at hcheck
            | some e =>
              simp [checkNode, hk] at hcheck
              simp [jumpsOkNode, hk] at hjump
              have hentry := cert_check_at hc k e g hk hget
              have hjentry := cert_jumpsOk_at hj k e g hk hget
              have h_at : Jinst.At sevm.code pc .jump := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck.1.1.1
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
                    simpa [hcheck.1.1.2] using hjump.1
                  have hjp : jumpable sevm.code t.toNat = true := by
                    rw [hcode]
                    exact jumpable_of_jumpdestOk hje
                  have hentry' :
                      checkNode code c.entries e.rets t.toNat e.frame g = true := by
                    simpa [hcheck.1.1.2] using hentry
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
                    have hrec := ihrun t.toNat e.rets e.frame 0 Sf (Sr ++ base)
                      hentry' hjentry hstacke hframee
                    rcases hrec with ⟨hret, Sret, hst, hlen, hchildcont⟩
                    exact (hret_no AVal.ret hret rfl).elim
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
                            checkNode code c.entries m (r.toNat + 1)
                              (List.replicate e.rets .unk ++
                                a'.drop e.frame.length) dcont = true := by
                          simpa [hidx, haidx, Bool.and_eq_true] using hcheck.2
                        rcases frameMatches_callCompat hcall.1 htail with
                          ⟨Sf, Sr, hsplit, hframee, hframer⟩
                        have hstacke : devm'.stack = Sf ++ (Sr ++ base) := by
                          rw [hinter, hsplit]
                          simp [List.append_assoc]
                        have hrec := ihrun t.toNat e.rets e.frame r Sf (Sr ++ base)
                          hentry' hjentry hstacke hframee
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
                        have hcheckc :
                            checkNode code c.entries m r.toNat framec
                              (.dest dcont) = true := by
                          simp [framec, checkNode, hcall.2.1, hcall.2.2]
                        have hjumpc : jumpsOkNode code c.entries
                            (.dest dcont) framec = true := by
                          have hh : jumpdestOk code e.pc = true ∧
                              jumpdestOk code r.toNat = true ∧
                                jumpsOkNode code c.entries dcont framec = true := by
                            simpa [framec, jumpsOkNode, hk, hidx, haidx,
                              Bool.and_eq_true] using hjump
                          exact hh.2.2
                        cases o with
                        | halted post =>
                          have hrec2 := ihcont r.toNat m framec ρ
                            (Sret ++ Sr) base hcheckc hjumpc hst' hframec
                          rcases hrec2 with ⟨exc2⟩
                          rcases hchildcont ⟨exc2⟩ with ⟨exct⟩
                          subst d
                          subst s0
                          exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exct⟩
                        | returned devmfinal =>
                          have hrec2 := ihcont r.toNat m framec ρ
                            (Sret ++ Sr) base hcheckc hjumpc hst' hframec
                          rcases hrec2 with
                            ⟨hret2, S2, hst2, hlen2, hcont2⟩
                          have hret_a' : AVal.ret ∈ a' := by
                            have hh : AVal.ret ∈
                                List.replicate e.rets .unk ++
                                  a'.drop e.frame.length := by
                              simpa [framec] using hret2
                            rcases List.mem_append.mp hh with h | h
                            · simp at h
                            · exact List.mem_of_mem_drop h
                          refine ⟨List.mem_cons_of_mem _ hret_a', S2, hst2,
                            hlen2, ?_⟩
                          intro r2 hr2
                          rcases hcont2 hr2 with ⟨exc2⟩
                          rcases hchildcont ⟨exc2⟩ with ⟨exct⟩
                          subst d
                          subst s0
                          exact ⟨Exec.cont (jump_cont_exact h_at hjp hpop) exct⟩
          | branch _ _ => simp [checkNode] at hcheck
          | branchTo _ _ => simp [checkNode] at hcheck
          | last _ => simp [checkNode] at hcheck
          | next _ _ => simp [checkNode] at hcheck
          | jump _ => simp [checkNode] at hcheck
          | callNext _ _ => simp [checkNode] at hcheck
          | ret => simp [checkNode] at hcheck
          | undefined => simp [checkNode] at hcheck)
    run

/-- The top-level gas-exact converse. -/
theorem lift_exact {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hrun : SProg.RunExact c.prog sevm pre post) :
    Nonempty (Exec 0 sevm pre (.ok post)) := by
  cases c with
  | nil => simp [Cert.check] at hc
  | cons p cs =>
    rcases p with ⟨e, f⟩
    have hc' := hc
    simp only [Cert.check, Bool.and_eq_true] at hc'
    have hepc : e.pc = 0 := by simpa using hc'.1.1
    have hef : e.frame = [] := by simpa using hc'.1.2
    have hf : checkNode code (Cert.entries ((e, f) :: cs)) e.rets e.pc e.frame f = true := by
      apply List.all_eq_true.mp hc'.2 (e, f)
      simp [Cert.entries]
    rcases hrun with ⟨f0, hf0, hrf⟩
    have hf0' : f0 = f := by simpa [Cert.prog] using hf0.symm
    subst f0
    have hentry := cert_jumpsOk_at hj 0 e f (by simp [Cert.entries])
      (by simp [Cert.prog])
    have hnode : jumpsOkNode code (Cert.entries ((e, f) :: cs)) f [] = true := by
      simpa [hepc, hef] using hentry
    have hres := node_exact hc hj hcode hfork hrf
      0 e.rets [] 0 [] pre.stack
      (by simpa [hepc, hef] using hf) hnode rfl (by simp [FrameMatches])
    exact hres

namespace Weth9

set_option maxRecDepth 100000 in
theorem jumps_ok : Cert.jumpsOk code cert = true := by
  decide +kernel

end Weth9

end Blanc.Lift
