-- Exact functional observations for WETH10's read-only public surface boundary.

import Blanc.Weth10Permit

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Dynamic byte-string returns -/

/-- A successful dynamic ABI result is stated at the machine output field. -/
def ReturnsBytes (bs : Bytes) (d : Devm) : Prop :=
  Devm.output d = bs

lemma slice_three_words (img : Bytes) (a b c : B256) :
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt img 0 a.toBytes)
        32 b.toBytes)
      64 c.toBytes).sliceD 0 96 0 =
        a.toBytes ++ b.toBytes ++ c.toBytes := by
  have ha : a.toBytes.length = 32 := B256.length_toBytes a
  have hb : b.toBytes.length = 32 := B256.length_toBytes b
  have hc : c.toBytes.length = 32 := B256.length_toBytes c
  have e1 : Bytes.writeAt img 0 a.toBytes =
      a.toBytes ++ img.drop 32 := by
    rw [Bytes.writeAt, ha, show List.takeD 0 img 0 = [] from rfl,
      List.nil_append, Nat.zero_add]
  have e2 : Bytes.writeAt (a.toBytes ++ img.drop 32) 32 b.toBytes =
      a.toBytes ++ (b.toBytes ++ (img.drop 32).drop 32) := by
    rw [Bytes.writeAt, hb, List.takeD_eq_take _ (by simp [ha]),
      List.take_left' ha,
      show 32 + 32 = a.toBytes.length + 32 from by rw [ha],
      List.drop_append, List.append_assoc]
    simp [ha]
  have e3 : Bytes.writeAt
      (a.toBytes ++ (b.toBytes ++ (img.drop 32).drop 32))
      64 c.toBytes =
      a.toBytes ++ (b.toBytes ++
        (c.toBytes ++ ((img.drop 32).drop 32).drop 32)) := by
    rw [show a.toBytes ++ (b.toBytes ++ (img.drop 32).drop 32) =
        (a.toBytes ++ b.toBytes) ++ (img.drop 32).drop 32 by
          rw [List.append_assoc],
      Bytes.writeAt, hc,
      List.takeD_eq_take _ (by simp [ha, hb]; omega),
      List.take_left' (by simp [ha, hb]),
      show 64 + 32 = (a.toBytes ++ b.toBytes).length + 32 by
        simp [ha, hb],
      List.drop_append, List.append_assoc]
    simp [ha, hb, List.append_assoc]
  rw [e1, e2, e3]
  unfold List.sliceD
  rw [List.drop_zero,
    List.takeD_eq_take _ (by simp [ha, hb, hc]; omega)]
  rw [show a.toBytes ++ (b.toBytes ++
      (c.toBytes ++ List.drop 32 (List.drop 32 (List.drop 32 img)))) =
      (a.toBytes ++ b.toBytes ++ c.toBytes) ++
        List.drop 32 (List.drop 32 (List.drop 32 img)) by
          simp [List.append_assoc],
    List.take_left' (by simp [ha, hb, hc])]

/-- Store three known stack words into consecutive memory words and return the
complete 96-byte ABI window. The prior memory image is arbitrary because all
returned bytes are overwritten. -/
lemma of_storeReturnWords3 {fs : List Func} {sevm : Sevm} {s r : Devm}
    {a b c : B256} {img : Bytes} {xs}
    (hp : a :: b :: c :: xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (h : Func.Run fs sevm s
      (mstoreAt 0 +++ mstoreAt 1 +++ mstoreAt 2 +++
        returnMemoryRange 0 96) r) :
    ReturnsBytes (a.toBytes ++ b.toBytes ++ c.toBytes) r ∧
      Devm.getCode s = Devm.getCode r := by
  rcases of_run_prepend (mstoreAt 0) _ h with ⟨s1, h1, run1⟩
  rcases of_run_mstoreAt_val h1 hp with ⟨hp1, hm1⟩
  have hwf1 : Mem.Wf s1.memory := by
    rw [hm1]
    exact h_wf.write _ _
  have hrd1 : Mem.Reads s1.memory (Bytes.writeAt img 0 a.toBytes) := by
    rw [hm1]
    exact Mem.Reads.write h_wf h_reads 0 _
  rcases of_run_prepend (mstoreAt 1) _ run1 with ⟨s2, h2, run2⟩
  rcases of_run_mstoreAt_val h2 hp1 with ⟨hp2, hm2⟩
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2]
    exact hwf1.write _ _
  have hrd2 : Mem.Reads s2.memory
      (Bytes.writeAt (Bytes.writeAt img 0 a.toBytes) 32 b.toBytes) := by
    rw [hm2]
    exact Mem.Reads.write hwf1 hrd1 32 _
  rcases of_run_prepend (mstoreAt 2) _ run2 with ⟨s3, h3, run3⟩
  rcases of_run_mstoreAt_val h3 hp2 with ⟨hp3, hm3⟩
  have hwf3 : Mem.Wf s3.memory := by
    rw [hm3]
    exact hwf2.write _ _
  have hrd3 : Mem.Reads s3.memory
      (Bytes.writeAt
        (Bytes.writeAt (Bytes.writeAt img 0 a.toBytes) 32 b.toBytes)
        64 c.toBytes) := by
    rw [hm3]
    exact Mem.Reads.write hwf2 hrd2 64 _
  rcases of_run_prepend (pushList [96, 0]) _ run3 with ⟨s4, h4, run4⟩
  rcases Line.of_run_cons h4 with ⟨u1, q1, h4'⟩
  rcases Line.of_run_cons h4' with ⟨u2, q2, hnil⟩
  cases hnil
  have hu1 : (96 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp3
  have hu2 : (0 : B256) :: (96 : B256) :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 q2) hu1
  have hm4 : s3.memory = s4.memory :=
    Line.of_inv Devm.memory (by line_inv) h4
  have hgc : Devm.getCode s = Devm.getCode s4 :=
    (((Line.of_inv Devm.getCode (by line_inv) h1).trans
      (Line.of_inv Devm.getCode (by line_inv) h2)).trans
      (Line.of_inv Devm.getCode (by line_inv) h3)).trans
      (Line.of_inv Devm.getCode (by line_inv) h4)
  refine ⟨?_, hgc.trans (of_run_return_val hu2 run4).2⟩
  show Devm.output r = _
  rw [(of_run_return_val hu2 run4).1,
    show (0 : B256).toNat = 0 from rfl,
    show (96 : B256).toNat = 96 from rfl,
    Mem.Reads.read (hm4 ▸ hrd3) 0 96,
    slice_three_words]

def shortStringOutput (w shift len : B256) : Bytes :=
  (32 : B256).toBytes ++ len.toBytes ++ (w <<< shift.toNat).toBytes

/-- The runtime's compact ABI string emitter: place a short UTF-8 payload in
the high bytes of the data word, preceded by the dynamic offset and length. -/
lemma of_shortStringReturn {fs : List Func} {sevm : Sevm} {s r : Devm}
    {w shift len : B256} {img : Bytes} {xs}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s
      (pushB256 w ::: pushB256 shift ::: shl :::
        pushList [len, 32] +++
        mstoreAt 0 +++ mstoreAt 1 +++ mstoreAt 2 +++
        returnMemoryRange 0 96) r) :
    ReturnsBytes (shortStringOutput w shift len) r ∧
      Devm.getCode s = Devm.getCode r := by
  rcases of_run_next run with ⟨s1, q1, run1⟩
  have hp1 : w :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases of_run_next run1 with ⟨s2, q2, run2⟩
  have hp2 : shift :: w :: xs <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp1
  rcases of_run_next run2 with ⟨s3, q3, run3⟩
  have hp3 : (w <<< shift.toNat) :: xs <<+ s3.stack :=
    prefix_of_shl q3 hp2
  rcases of_run_prepend (pushList [len, 32]) _ run3 with
    ⟨s4, q4, run4⟩
  rcases Line.of_run_cons q4 with ⟨u1, p1, q4'⟩
  rcases Line.of_run_cons q4' with ⟨u2, p2, hnil⟩
  cases hnil
  have hp4 : len :: (w <<< shift.toNat) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 p1) hp3
  have hp5 : (32 : B256) :: len :: (w <<< shift.toNat) :: xs <<+
      s4.stack :=
    prefix_of_push (of_run_pushB256 p2) hp4
  have hm : s.memory = s4.memory :=
    (((Ninst.Hinv.inv (f := Devm.memory) q1).trans
      (Ninst.Hinv.inv (f := Devm.memory) q2)).trans
      (Ninst.Hinv.inv (f := Devm.memory) q3)).trans
      (Line.of_inv Devm.memory (by line_inv) q4)
  have hgc : Devm.getCode s = Devm.getCode s4 :=
    (((Ninst.Hinv.inv (f := Devm.getCode) q1).trans
      (Ninst.Hinv.inv (f := Devm.getCode) q2)).trans
      (Ninst.Hinv.inv (f := Devm.getCode) q3)).trans
      (Line.of_inv Devm.getCode (by line_inv) q4)
  obtain ⟨hout, hgc'⟩ :=
    of_storeReturnWords3 hp5 (hm ▸ h_wf) (hm ▸ h_reads) run4
  exact ⟨by simpa only [shortStringOutput] using hout,
    hgc.trans hgc'⟩

def nameOutput : Bytes :=
  shortStringOutput
    (Blanc.String.toBytes "Wrapped Ether v10").toB256 120 17

def symbolOutput : Bytes :=
  shortStringOutput (Blanc.String.toBytes "WETH10").toB256 208 6

theorem name_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s name r) :
    ReturnsBytes nameOutput r ∧ Devm.getCode s = Devm.getCode r := by
  simpa only [name, nameOutput] using
    (of_shortStringReturn hp h_wf h_reads run)

theorem symbol_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s symbol r) :
    ReturnsBytes symbolOutput r ∧ Devm.getCode s = Devm.getCode r := by
  simpa only [symbol, symbolOutput] using
    (of_shortStringReturn hp h_wf h_reads run)

/-! ## Constant word getters -/

theorem callbackSuccess_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s callbackSuccess r) :
    ReturnsWord CALLBACK_SUCCESS r ∧
      Devm.getCode s = Devm.getCode r := by
  simpa only [callbackSuccess] using
    (of_returnWord hp h_wf h_reads run)

theorem permitTypehash_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s permitTypehash r) :
    ReturnsWord PERMIT_TYPEHASH r ∧
      Devm.getCode s = Devm.getCode r := by
  simpa only [permitTypehash] using
    (of_returnWord hp h_wf h_reads run)

theorem decimals_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s decimals r) :
    ReturnsWord 0x12 r ∧
      Devm.getCode s = Devm.getCode r := by
  simpa only [decimals, Blanc.decimals, returnWord] using
    (of_returnWord (w := (0x12 : B256)) hp h_wf h_reads
      (by simpa only [decimals, Blanc.decimals, returnWord] using run))

/-- The deployment-chain getter returns the parameter embedded in this exact
member of the compiled runtime family. -/
theorem deploymentChainId_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {dp : DeployParams} {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s (deploymentChainId dp) r) :
    ReturnsWord dp.deploymentChainId r ∧
      Devm.getCode s = Devm.getCode r := by
  simp only [deploymentChainId, returnDeployWord] at run
  rcases of_run_next run with ⟨s1, hpush, run1⟩
  unfold pushDeployWord at hpush
  have hp1 : dp.deploymentChainId :: xs <<+ s1.stack := by
    rw [← B256.toB256_toBytes dp.deploymentChainId]
    exact prefix_of_push (of_run_push hpush) hp
  have hm : s.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hpush
  obtain ⟨hout, hcode⟩ :=
    of_storeReturnWord hp1 (hm ▸ h_wf) (hm ▸ h_reads) run1
  exact ⟨hout,
    (Ninst.Hinv.inv (f := Devm.getCode) hpush).trans hcode⟩

private lemma read_prefix_of_chainid {e : Sevm} {s s' : Devm}
    {xs : Stack}
    (hp : xs <<+ s.stack) (h : Ninst.Run e s chainid s') :
    e.benvStat.chainId.toB256 :: xs <<+ s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact prefix_of_push (Devm.pushBurn_of_pushItem run) hp

private lemma read_memory_eq_of_chainid {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s chainid s') : s.memory = s'.memory := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).memory

private lemma read_code_eq_of_chainid {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s chainid s') : s.getCode = s'.getCode := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  funext a
  exact getCode_eq_of_state_eq (Devm.pushBurn_of_pushItem run).state a

private lemma read_prefix_of_pushDeployWord {e : Sevm} {s s' : Devm}
    {w : B256} {xs : Stack} (hp : xs <<+ s.stack)
    (h : Ninst.Run e s (pushDeployWord w) s') :
    w :: xs <<+ s'.stack := by
  unfold pushDeployWord at h
  rw [← B256.toB256_toBytes w]
  exact prefix_of_push (of_run_push h) hp

/-- `DOMAIN_SEPARATOR()` returns the cached deployment separator on the
deployment chain and the exact recomputed EIP-712 image on every other chain.
The statement identifies the common logical word rather than merely exposing
the branch taken by the runtime. -/
theorem domainSeparator_output {fs : List Func} {sevm : Sevm}
    {s r : Devm} {dp : DeployParams} {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s (domainSeparator dp) r) :
    ReturnsWord
        (permitDomainSeparator dp sevm.benvStat.chainId.toB256
          sevm.currentTarget) r ∧
      Devm.getCode s = Devm.getCode r := by
  unfold domainSeparator at run
  rcases of_run_next run with ⟨s1, q1, run⟩
  have hp1 : sevm.benvStat.chainId.toB256 :: xs <<+ s1.stack :=
    read_prefix_of_chainid hp q1
  rcases of_run_next run with ⟨s2, q2, run⟩
  have hp2 : sevm.benvStat.chainId.toB256 ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s2.stack :=
    prefix_of_dup_val q2 (by show_nth) hp1
  rcases of_run_next run with ⟨s3, q3, run⟩
  have hp3 : dp.deploymentChainId ::
      sevm.benvStat.chainId.toB256 ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s3.stack :=
    read_prefix_of_pushDeployWord hp2 q3
  rcases of_run_next run with ⟨s4, q4, run⟩
  have hm4 : s.memory = s4.memory := by
    calc
      s.memory = s1.memory := read_memory_eq_of_chainid q1
      _ = s2.memory := Ninst.Hinv.inv (f := Devm.memory) q2
      _ = s3.memory := by
        unfold pushDeployWord at q3
        exact Ninst.Hinv.inv (f := Devm.memory) q3
      _ = s4.memory := Ninst.Hinv.inv (f := Devm.memory) q4
  have hcode4 : s.getCode = s4.getCode := by
    calc
      s.getCode = s1.getCode := read_code_eq_of_chainid q1
      _ = s2.getCode := Ninst.Hinv.inv (f := Devm.getCode) q2
      _ = s3.getCode := by
        unfold pushDeployWord at q3
        exact Ninst.Hinv.inv (f := Devm.getCode) q3
      _ = s4.getCode := Ninst.Hinv.inv (f := Devm.getCode) q4
  by_cases hchain :
      sevm.benvStat.chainId.toB256 = dp.deploymentChainId
  · have hp4 : (1 : B256) ::
        sevm.benvStat.chainId.toB256 :: xs <<+ s4.stack := by
      have heq := prefix_of_eq q4 hp3
      simpa [hchain, B256.eqCheck] using heq
    rcases of_run_branch run with
        ⟨sp, hpop, hfork⟩ |
        ⟨w, sp, sb, hnz, hpop, hburn, hcached⟩
    · exact absurd (popBurn_pref hpop hp4).1 B256.zero_ne_one
    · rcases popBurn_pref hpop hp4 with ⟨-, hp5⟩
      have hp6 : sevm.benvStat.chainId.toB256 :: xs <<+ sb.stack := by
        rw [← hburn.stack]
        exact hp5
      rcases of_run_next hcached with ⟨s5, q5, hret⟩
      have hp7 : xs <<+ s5.stack := prefix_of_pop (of_run_pop q5) hp6
      have hm5 : s.memory = s5.memory := by
        calc
          s.memory = s4.memory := hm4
          _ = sp.memory := hpop.memory
          _ = sb.memory := hburn.memory
          _ = s5.memory := Ninst.Hinv.inv (f := Devm.memory) q5
      rcases of_returnDeployWord hp7 (hm5 ▸ h_wf) (hm5 ▸ h_reads)
          hret with ⟨hout, hcode5⟩
      have hpopCode : s4.getCode = sp.getCode := by
        funext a
        exact getCode_eq_of_state_eq hpop.state a
      have hburnCode : sp.getCode = sb.getCode := by
        funext a
        exact getCode_eq_of_state_eq hburn.state a
      refine ⟨?_, hcode4.trans (hpopCode.trans
        (hburnCode.trans ((Ninst.Hinv.inv (f := Devm.getCode) q5).trans
          hcode5)))⟩
      simpa [permitDomainSeparator, hchain] using hout
  · have hrev :
        dp.deploymentChainId ≠ sevm.benvStat.chainId.toB256 :=
      fun h => hchain h.symm
    have hp4 : (0 : B256) ::
        sevm.benvStat.chainId.toB256 :: xs <<+ s4.stack := by
      have heq := prefix_of_eq q4 hp3
      simpa [B256.eqCheck, hrev] using heq
    rcases of_run_branch run with
        ⟨sp, hpop, hfork⟩ |
        ⟨w, sp, sb, hnz, hpop, hburn, hcached⟩
    · rcases popBurn_pref hpop hp4 with ⟨-, hp5⟩
      have hmsp : s.memory = sp.memory := hm4.trans hpop.memory
      rcases of_run_prepend calculateDomainSeparator _ hfork with
        ⟨s5, hdomain, htail⟩
      rcases of_calculateDomainSeparator hp5 (hmsp ▸ h_wf)
          (hmsp ▸ h_reads) hdomain with
        ⟨hp6, hwf6, hreads6, hcode5, -, -⟩
      rcases of_storeReturnWord hp6 hwf6 hreads6 htail with
        ⟨hout, hcodeTail⟩
      have hpopCode : s4.getCode = sp.getCode := by
        funext a
        exact getCode_eq_of_state_eq hpop.state a
      refine ⟨?_, hcode4.trans (hpopCode.trans
        (hcode5.symm.trans hcodeTail))⟩
      simpa [permitDomainSeparator, hchain] using hout
    · have hw0 : w = 0 := (popBurn_pref hpop hp4).1
      exact (hnz hw0).elim

/-! ## Storage word getters -/

/-- Exact runtime allowance key for the two canonical ABI words beginning at
calldata byte four.  The finite-collision qualification belongs to comparing
different calls; one call's computed key is exact. -/
def allowanceCallKey (e : Sevm) : B256 :=
  allowanceTagWord |||
    (allowancePayloadMask &&& Bytes.keccak (e.data.sliceD 4 64 0))

lemma of_run_allowanceArgCopy {e : Sevm} {s s' : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s (argCopy 0 0 2) s') :
    xs <<+ s'.stack ∧
      s'.memory = s.memory.write 0 (e.data.sliceD 4 64 0) := by
  simp only [argCopy, cdc] at run
  rcases Line.of_run_cons run with ⟨u1, q1, run1⟩
  have hp1 : (64 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons run1 with ⟨u2, q2, run2⟩
  have hp2 : (4 : B256) :: 64 :: xs <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons run2 with ⟨u3, q3, run3⟩
  have hp3 : (0 : B256) :: 4 :: 64 :: xs <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons run3 with ⟨u4, q4, hnil⟩
  cases hnil
  rcases prefix_of_calldatacopy_val q4 hp3 with ⟨hp4, hm4⟩
  refine ⟨hp4, ?_⟩
  rw [hm4,
    ← (Ninst.Hinv.inv (f := Devm.memory) q3),
    ← (Ninst.Hinv.inv (f := Devm.memory) q2),
    ← (Ninst.Hinv.inv (f := Devm.memory) q1)]
  rfl

theorem balanceOf_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s balanceOfEndpoint r) :
    ReturnsWord
        (Devm.getStorVal s sevm.currentTarget (Sevm.argWord sevm 0)) r ∧
      Devm.getCode s = Devm.getCode r := by
  simp only [balanceOfEndpoint, Blanc.balanceOf] at run
  rcases of_run_prepend (arg 0) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord sevm 0 :: xs <<+ s1.stack :=
    prefix_of_arg hp harg
  rcases of_run_next run1 with ⟨s2, hsload, run2⟩
  rcases prefix_of_sload hsload hp1 with ⟨bal, hp2, hbal⟩
  have hm1 : s.memory = s1.memory :=
    Line.of_inv Devm.memory (by line_inv) harg
  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) harg
  have hm2 : s1.memory = s2.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsload
  have hwf2 : Mem.Wf s2.memory := by
    rw [← hm2, ← hm1]
    exact h_wf
  have hrd2 : Mem.Reads s2.memory img := by
    rw [← hm2, ← hm1]
    exact h_reads
  have hgc1 : Devm.getCode s = Devm.getCode s2 :=
    (Line.of_inv Devm.getCode (by line_inv) harg).trans
      (Ninst.Hinv.inv (f := Devm.getCode) hsload)
  obtain ⟨hout, hgc2⟩ :=
    of_storeReturnWord hp2 hwf2 hrd2 run2
  rw [hbal] at hout
  change ReturnsWord
    ((Devm.getStor s1 sevm.currentTarget).get (Sevm.argWord sevm 0)) r at hout
  rw [← hs1] at hout
  exact ⟨hout, hgc1.trans hgc2⟩

theorem allowance_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s allowance r) :
    ReturnsWord
        (Devm.getStorVal s sevm.currentTarget (allowanceCallKey sevm)) r ∧
      Devm.getCode s = Devm.getCode r := by
  simp only [allowance] at run
  rcases of_run_prepend (argCopy 0 0 2) _ run with
    ⟨s1, hcopy, run1⟩
  rcases of_run_allowanceArgCopy hp hcopy with ⟨hp1, hm1⟩
  let payload : Bytes := sevm.data.sliceD 4 64 0
  have hwf1 : Mem.Wf s1.memory := by
    rw [hm1]
    exact h_wf.write _ _
  have hrd1 : Mem.Reads s1.memory (Bytes.writeAt img 0 payload) := by
    rw [hm1]
    exact Mem.Reads.write h_wf h_reads 0 _
  rcases of_run_prepend allowanceKeyFromMemory _ run1 with
    ⟨s2, hkey, run2⟩
  unfold allowanceKeyFromMemory pushList at hkey
  simp only [List.map] at hkey
  rcases Line.of_run_cons hkey with ⟨u1, q1, k1⟩
  have hk1 : (64 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp1
  rcases Line.of_run_cons k1 with ⟨u2, q2, k2⟩
  have hk2 : (0 : B256) :: 64 :: xs <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hk1
  rcases Line.of_run_cons k2 with ⟨u3, q3, k3⟩
  rcases prefix_of_keccak256_val q3 hk2 with ⟨hk3, hmK⟩
  have hhash : Bytes.keccak (u2.memory.read 0 64).1 =
      Bytes.keccak payload := by
    rw [Mem.Reads.read (by
      rw [← (Line.of_inv Devm.memory (by line_inv)
        (Line.Run.cons q1 (Line.Run.cons q2 Line.Run.nil)))]
      exact hrd1) 0 64]
    have hlen : payload.length = 64 :=
      by simp [payload, List.sliceD]
    rw [← hlen, Bytes.sliceD_writeAt]
  have hk3' : Bytes.keccak payload :: xs <<+ u3.stack := by
    rw [← hhash]
    exact hk3
  rcases Line.of_run_cons k3 with ⟨u4, q4, k4⟩
  have hk4 : allowancePayloadMask :: Bytes.keccak payload :: xs <<+
      u4.stack := prefix_of_push (of_run_pushB256 q4) hk3'
  rcases Line.of_run_cons k4 with ⟨u5, q5, k5⟩
  have hk5 : (allowancePayloadMask &&& Bytes.keccak payload) :: xs <<+
      u5.stack := prefix_of_and q5 hk4
  rcases Line.of_run_cons k5 with ⟨u6, q6, k6⟩
  have hk6 : allowanceTagWord ::
      (allowancePayloadMask &&& Bytes.keccak payload) :: xs <<+ u6.stack :=
    prefix_of_push (of_run_pushB256 q6) hk5
  rcases Line.of_run_cons k6 with ⟨u7, q7, hnil⟩
  cases hnil
  have hp2 : allowanceCallKey sevm :: xs <<+ s2.stack := by
    simpa only [allowanceCallKey, payload] using
      (prefix_of_or q7 hk6)
  rcases of_run_next run2 with ⟨s3, hsload, run3⟩
  rcases prefix_of_sload hsload hp2 with ⟨value, hp3, hvalue⟩
  have hm2 : s2.memory = s1.memory.extend 0 64 := by
    rw [← (Ninst.Hinv.inv (f := Devm.memory) q7),
      ← (Ninst.Hinv.inv (f := Devm.memory) q6),
      ← (Ninst.Hinv.inv (f := Devm.memory) q5),
      ← (Ninst.Hinv.inv (f := Devm.memory) q4), hmK]
    rw [← (Ninst.Hinv.inv (f := Devm.memory) q2),
      ← (Ninst.Hinv.inv (f := Devm.memory) q1)]
    rfl
  have hm3 : s2.memory = s3.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsload
  have hwf3 : Mem.Wf s3.memory := by
    rw [← hm3, hm2]
    exact hwf1.extend 0 64
  have hrd3 : Mem.Reads s3.memory (Bytes.writeAt img 0 payload) := by
    rw [← hm3, hm2]
    exact hrd1.extend 0 64
  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) hcopy
  have hs2 : Devm.getStor s1 = Devm.getStor s2 :=
    Line.of_inv Devm.getStor (by line_inv) hkey
  have hgc : Devm.getCode s = Devm.getCode s3 :=
    ((Line.of_inv Devm.getCode (by line_inv) hcopy).trans
      (Line.of_inv Devm.getCode
        (by line_inv) hkey)).trans
      (Ninst.Hinv.inv (f := Devm.getCode) hsload)
  obtain ⟨hout, hgc2⟩ :=
    of_storeReturnWord hp3 hwf3 hrd3 run3
  rw [hvalue] at hout
  change ReturnsWord
    ((Devm.getStor s2 sevm.currentTarget).get
      (allowanceCallKey sevm)) r at hout
  rw [← hs2, ← hs1] at hout
  exact ⟨hout, hgc.trans hgc2⟩

theorem nonces_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s nonces r) :
    ReturnsWord
        (Devm.getStorVal s sevm.currentTarget
          (nonceTagWord ||| Sevm.argWord sevm 0)) r ∧
      Devm.getCode s = Devm.getCode r := by
  simp only [nonces] at run
  rcases of_run_prepend (arg 0) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord sevm 0 :: xs <<+ s1.stack :=
    prefix_of_arg hp harg
  rcases of_run_prepend tagNonceKey _ run1 with ⟨s2, htag, run2⟩
  have hp2 : (nonceTagWord ||| Sevm.argWord sevm 0) :: xs <<+
      s2.stack := by
    unfold tagNonceKey at htag
    rcases Line.of_run_cons htag with ⟨u, hpush, htag'⟩
    rcases Line.of_run_cons htag' with ⟨v, hor, hnil⟩
    cases hnil
    exact prefix_of_or hor
      (prefix_of_push (of_run_pushB256 hpush) hp1)
  rcases of_run_next run2 with ⟨s3, hsload, run3⟩
  rcases prefix_of_sload hsload hp2 with ⟨value, hp3, hvalue⟩
  have hm1 : s.memory = s1.memory :=
    Line.of_inv Devm.memory (by line_inv) harg
  have hm2 : s1.memory = s2.memory :=
    Line.of_inv Devm.memory (by unfold tagNonceKey; line_inv) htag
  have hm3 : s2.memory = s3.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsload
  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) harg
  have hs2 : Devm.getStor s1 = Devm.getStor s2 :=
    Line.of_inv Devm.getStor (by unfold tagNonceKey; line_inv) htag
  have hgc : Devm.getCode s = Devm.getCode s3 :=
    ((Line.of_inv Devm.getCode (by line_inv) harg).trans
      (Line.of_inv Devm.getCode (by unfold tagNonceKey; line_inv) htag)).trans
      (Ninst.Hinv.inv (f := Devm.getCode) hsload)
  obtain ⟨hout, hgc2⟩ :=
    of_storeReturnWord hp3
      (by rw [← hm3, ← hm2, ← hm1]; exact h_wf)
      (by rw [← hm3, ← hm2, ← hm1]; exact h_reads) run3
  rw [hvalue] at hout
  change ReturnsWord
    ((Devm.getStor s2 sevm.currentTarget).get
      (nonceTagWord ||| Sevm.argWord sevm 0)) r at hout
  rw [← hs2, ← hs1] at hout
  exact ⟨hout, hgc.trans hgc2⟩

theorem flashMinted_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s flashMinted r) :
    ReturnsWord
        (Devm.getStorVal s sevm.currentTarget flashMintedSlot) r ∧
      Devm.getCode s = Devm.getCode r := by
  simp only [flashMinted] at run
  rcases of_run_prepend pushFlashMintedSlot _ run with
    ⟨s1, hslot, run1⟩
  have hp1 : flashMintedSlot :: xs <<+ s1.stack := by
    unfold pushFlashMintedSlot at hslot
    unfold flashMintedSlot
    generalize_line_prefix
  rcases of_run_next run1 with ⟨s2, hsload, run2⟩
  rcases prefix_of_sload hsload hp1 with ⟨value, hp2, hvalue⟩
  have hm1 : s.memory = s1.memory :=
    Line.of_inv Devm.memory (by
      unfold pushFlashMintedSlot
      line_inv) hslot
  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by
      unfold pushFlashMintedSlot
      line_inv) hslot
  have hm2 : s1.memory = s2.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsload
  have hwf2 : Mem.Wf s2.memory := by
    rw [← hm2, ← hm1]
    exact h_wf
  have hrd2 : Mem.Reads s2.memory img := by
    rw [← hm2, ← hm1]
    exact h_reads
  have hgc1 : Devm.getCode s = Devm.getCode s2 :=
    (Line.of_inv Devm.getCode (by
      unfold pushFlashMintedSlot
      line_inv) hslot).trans
      (Ninst.Hinv.inv (f := Devm.getCode) hsload)
  obtain ⟨hout, hgc2⟩ :=
    of_storeReturnWord hp2 hwf2 hrd2 run2
  rw [hvalue] at hout
  change ReturnsWord
    ((Devm.getStor s1 sevm.currentTarget).get flashMintedSlot) r at hout
  rw [← hs1] at hout
  exact ⟨hout, hgc1.trans hgc2⟩

theorem totalSupply_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s totalSupply r) :
    ReturnsWord
        (Devm.getStorVal s sevm.currentTarget flashMintedSlot +
          s.getBal sevm.currentTarget) r ∧
      Devm.getCode s = Devm.getCode r := by
  simp only [totalSupply] at run
  rcases of_run_next run with ⟨s1, hself, run1⟩
  have hp1 : s.getBal sevm.currentTarget :: xs <<+ s1.stack :=
    prefix_of_push (of_run_selfbalance hself) hp
  rcases of_run_prepend pushFlashMintedSlot _ run1 with
    ⟨s2, hslot, run2⟩
  have hp2 : flashMintedSlot :: s.getBal sevm.currentTarget :: xs <<+
      s2.stack := by
    unfold pushFlashMintedSlot at hslot
    unfold flashMintedSlot
    generalize_line_prefix
  rcases of_run_next run2 with ⟨s3, hsload, run3⟩
  rcases prefix_of_sload hsload hp2 with ⟨flash, hp3, hflash⟩
  rcases of_run_next run3 with ⟨s4, hadd, run4⟩
  have hp4 : (flash + s.getBal sevm.currentTarget) :: xs <<+ s4.stack :=
    prefix_of_add hadd hp3
  have hm1 : s.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hself
  have hm2 : s1.memory = s2.memory :=
    Line.of_inv Devm.memory (by
      unfold pushFlashMintedSlot
      line_inv) hslot
  have hm3 : s2.memory = s3.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsload
  have hm4 : s3.memory = s4.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hadd
  have hwf4 : Mem.Wf s4.memory := by
    rw [← hm4, ← hm3, ← hm2, ← hm1]
    exact h_wf
  have hrd4 : Mem.Reads s4.memory img := by
    rw [← hm4, ← hm3, ← hm2, ← hm1]
    exact h_reads
  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Ninst.Hinv.inv (f := Devm.getStor) hself
  have hs2 : Devm.getStor s1 = Devm.getStor s2 :=
    Line.of_inv Devm.getStor (by
      unfold pushFlashMintedSlot
      line_inv) hslot
  have hgc : Devm.getCode s = Devm.getCode s4 :=
    ((Ninst.Hinv.inv (f := Devm.getCode) hself).trans
      (Line.of_inv Devm.getCode (by
        unfold pushFlashMintedSlot
        line_inv) hslot)).trans
      ((Ninst.Hinv.inv (f := Devm.getCode) hsload).trans
        (Ninst.Hinv.inv (f := Devm.getCode) hadd))
  obtain ⟨hout, hgc2⟩ :=
    of_storeReturnWord hp4 hwf4 hrd4 run4
  rw [hflash] at hout
  change ReturnsWord
    ((Devm.getStor s2 sevm.currentTarget).get flashMintedSlot +
      s.getBal sevm.currentTarget) r at hout
  rw [← hs2, ← hs1] at hout
  exact ⟨hout, hgc.trans hgc2⟩

/-- A successful `flashFee` body run proves its own token guard and returns
zero.  The amount word is deliberately absent from the result: the deployed
contract does not inspect it. -/
theorem flashFee_output
    {dp : DeployParams} {sevm : Sevm} {s r : Devm}
    {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s flashFee r) :
    Sevm.argWord sevm 0 = sevm.currentTarget.toB256 ∧
      ReturnsWord 0 r ∧
      Devm.getStor r = Devm.getStor s ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s := by
  simp only [flashFee] at run
  let guard : Line := arg 0 ++ [address, eq, iszero]
  rcases of_run_prepend guard _ run with ⟨s1, hguard, run1⟩
  have hp1 :
      ((sevm.currentTarget.toB256 =? Sevm.argWord sevm 0) =? 0) :: [] <<+
        s1.stack := by
    unfold guard at hguard
    rcases of_run_append (arg 0) hguard with ⟨u1, harg, hrest⟩
    have hpArg : Sevm.argWord sevm 0 :: [] <<+ u1.stack :=
      prefix_of_arg nil_pref harg
    rcases Line.of_run_cons hrest with ⟨u2, haddress, hrest⟩
    have hpAddress : sevm.currentTarget.toB256 ::
        Sevm.argWord sevm 0 :: [] <<+ u2.stack :=
      prefix_of_push (of_run_address haddress) hpArg
    rcases Line.of_run_cons hrest with ⟨u3, heq, hrest⟩
    have hpEq : (sevm.currentTarget.toB256 =? Sevm.argWord sevm 0) :: [] <<+
        u3.stack := prefix_of_eq heq hpAddress
    rcases Line.of_run_cons hrest with ⟨u4, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero hpEq
  rcases of_run_branch run1 with
      ⟨s2, hpop, hreturn⟩ |
      ⟨w, s2, s3, hnz, hpop, hburn, herror⟩
  · have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
    rw [hpopStack] at hp1
    have hflag :
        ((sevm.currentTarget.toB256 =? Sevm.argWord sevm 0) =? 0) = 0 :=
      pref_head_unique hp1 (pref_append [0] s2.stack)
    have htoken :
        Sevm.argWord sevm 0 = sevm.currentTarget.toB256 := by
      by_contra hne
      have hne' :
          sevm.currentTarget.toB256 ≠ Sevm.argWord sevm 0 := by
        exact fun h => hne h.symm
      simp [B256.eqCheck, hne'] at hflag
      exact B256.zero_ne_one hflag.symm
    have hm : s.memory = s2.memory :=
      (Line.of_inv Devm.memory (by
        unfold guard
        line_inv) hguard).trans hpop.memory
    have hwf2 : Mem.Wf s2.memory := by
      rw [← hm]
      exact h_wf
    have hrd2 : Mem.Reads s2.memory img := by
      rw [← hm]
      exact h_reads
    obtain ⟨hout, hcode2⟩ :=
      of_returnWord (w := (0 : B256)) nil_pref hwf2 hrd2 hreturn
    have hstor1 : Devm.getStor s = Devm.getStor s2 :=
      (Line.of_inv Devm.getStor (by
        unfold guard
        line_inv) hguard).trans
        (funext fun a => (Devm.PopBurn.getStor hpop a).symm)
    have hstor2 : Devm.getStor s2 = Devm.getStor r :=
      Func.of_inv Devm.getStor Devm.getStor (by
        unfold returnWord
        func_inv) hreturn
    have hbal1 : Devm.getBal s = Devm.getBal s2 :=
      (Line.of_inv Devm.getBal (by
        unfold guard
        line_inv) hguard).trans
        (PopBurn.Inv.inv hpop)
    have hbal2 : Devm.getBal s2 = Devm.getBal r :=
      Func.of_inv Devm.getBal Devm.getBal (by
        unfold returnWord
        func_inv) hreturn
    have hcode1 : Devm.getCode s = Devm.getCode s2 :=
      (Line.of_inv Devm.getCode (by
        unfold guard
        line_inv) hguard).trans
        (funext fun a => getCode_eq_of_state_eq hpop.state a)
    exact ⟨htoken, hout, (hstor1.trans hstor2).symm,
      (hbal1.trans hbal2).symm, (hcode1.trans hcode2).symm⟩
  · rcases of_run_call herror with ⟨f, sc, hget, hcallBurn, hrev⟩
    have hf : f = flashTokenError := by
      have hlookup :
          ((weth10 dp).main :: weth10Aux)[flashTokenErrorSlot]? =
            some flashTokenError := by
        simp [weth10, weth10Aux, flashTokenErrorSlot]
      rw [hlookup] at hget
      exact Option.some.inj hget.symm
    subst f
    exact absurd hrev Func.not_run_revertWith

/-- The self-token branch of `maxFlashLoan` returns the unchecked remaining
capacity from the exact entry `flashMinted` word. -/
theorem maxFlashLoanSelf_output
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs : Stack}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s
      (pushFlashMintedSlot +++ sload :::
        pushB256 (Nat.toB256 maxFlashMinted) ::: sub :::
        mstoreAt 0 +++ returnMemoryRange 0 32) r) :
    ReturnsWord
      (Nat.toB256 maxFlashMinted -
        Devm.getStorVal s sevm.currentTarget flashMintedSlot) r ∧
      Devm.getCode s = Devm.getCode r := by
  rcases of_run_prepend pushFlashMintedSlot _ run with
    ⟨s1, hslot, run1⟩
  have hp1 : flashMintedSlot :: xs <<+ s1.stack := by
    unfold pushFlashMintedSlot at hslot
    unfold flashMintedSlot
    generalize_line_prefix
  rcases of_run_next run1 with ⟨s2, hsload, run2⟩
  rcases prefix_of_sload hsload hp1 with ⟨flash, hp2, hflash⟩
  rcases of_run_next run2 with ⟨s3, hmax, run3⟩
  have hp3 : Nat.toB256 maxFlashMinted :: flash :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 hmax) hp2
  rcases of_run_next run3 with ⟨s4, hsub, run4⟩
  have hp4 : (Nat.toB256 maxFlashMinted - flash) :: xs <<+ s4.stack :=
    prefix_of_sub hsub hp3
  have hm1 : s.memory = s1.memory :=
    Line.of_inv Devm.memory (by
      unfold pushFlashMintedSlot
      line_inv) hslot
  have hm2 : s1.memory = s2.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsload
  have hm3 : s2.memory = s3.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hmax
  have hm4 : s3.memory = s4.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsub
  have hwf4 : Mem.Wf s4.memory := by
    rw [← hm4, ← hm3, ← hm2, ← hm1]
    exact h_wf
  have hrd4 : Mem.Reads s4.memory img := by
    rw [← hm4, ← hm3, ← hm2, ← hm1]
    exact h_reads
  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by
      unfold pushFlashMintedSlot
      line_inv) hslot
  have hgc : Devm.getCode s = Devm.getCode s4 :=
    ((Line.of_inv Devm.getCode (by
        unfold pushFlashMintedSlot
        line_inv) hslot).trans
      (Ninst.Hinv.inv (f := Devm.getCode) hsload)).trans
      ((Ninst.Hinv.inv (f := Devm.getCode) hmax).trans
        (Ninst.Hinv.inv (f := Devm.getCode) hsub))
  obtain ⟨hout, hgc2⟩ :=
    of_storeReturnWord hp4 hwf4 hrd4 run4
  rw [hflash] at hout
  change ReturnsWord
    (Nat.toB256 maxFlashMinted -
      (Devm.getStor s1 sevm.currentTarget).get flashMintedSlot) r at hout
  rw [← hs1] at hout
  exact ⟨hout, hgc.trans hgc2⟩

/-- Exact successful body behavior of `maxFlashLoan`, including both the
self-token capacity branch and the non-self zero branch. -/
theorem maxFlashLoan_output
    {dp : DeployParams} {sevm : Sevm} {s r : Devm}
    {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s maxFlashLoan r) :
    ReturnsWord
      (if Sevm.argWord sevm 0 = sevm.currentTarget.toB256 then
        Nat.toB256 maxFlashMinted -
          Devm.getStorVal s sevm.currentTarget flashMintedSlot
       else 0) r ∧
      Devm.getStor r = Devm.getStor s ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s := by
  have hstor : Devm.getStor s = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold maxFlashLoan
      func_inv) run
  have hbal : Devm.getBal s = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by
      unfold maxFlashLoan
      func_inv) run
  simp only [maxFlashLoan] at run
  let guard : Line := arg 0 ++ [address, eq]
  rcases of_run_prepend guard _ run with ⟨s1, hguard, run1⟩
  have hp1 :
      (sevm.currentTarget.toB256 =? Sevm.argWord sevm 0) :: [] <<+
        s1.stack := by
    unfold guard at hguard
    rcases of_run_append (arg 0) hguard with ⟨u1, harg, hrest⟩
    have hpArg : Sevm.argWord sevm 0 :: [] <<+ u1.stack :=
      prefix_of_arg nil_pref harg
    rcases Line.of_run_cons hrest with ⟨u2, haddress, hrest⟩
    have hpAddress : sevm.currentTarget.toB256 ::
        Sevm.argWord sevm 0 :: [] <<+ u2.stack :=
      prefix_of_push (of_run_address haddress) hpArg
    rcases Line.of_run_cons hrest with ⟨u3, heq, hnil⟩
    cases hnil
    exact prefix_of_eq heq hpAddress
  rcases of_run_branch run1 with
      ⟨s2, hpop, hzero⟩ |
      ⟨w, s2, s3, hnz, hpop, hburn, hself⟩
  · have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
    rw [hpopStack] at hp1
    have hflag :
        (sevm.currentTarget.toB256 =? Sevm.argWord sevm 0) = 0 :=
      pref_head_unique hp1 (pref_append [0] s2.stack)
    have hne : Sevm.argWord sevm 0 ≠ sevm.currentTarget.toB256 := by
      intro heq
      rw [heq] at hflag
      simp [B256.eqCheck] at hflag
      exact B256.zero_ne_one hflag.symm
    have hm : s.memory = s2.memory :=
      (Line.of_inv Devm.memory (by
        unfold guard
        line_inv) hguard).trans hpop.memory
    have hwf2 : Mem.Wf s2.memory := by
      rw [← hm]
      exact h_wf
    have hrd2 : Mem.Reads s2.memory img := by
      rw [← hm]
      exact h_reads
    obtain ⟨hout, hcode2⟩ :=
      of_returnWord (w := (0 : B256)) nil_pref hwf2 hrd2 hzero
    have hcode1 : Devm.getCode s = Devm.getCode s2 :=
      (Line.of_inv Devm.getCode (by
        unfold guard
        line_inv) hguard).trans
        (funext fun a => getCode_eq_of_state_eq hpop.state a)
    rw [if_neg hne]
    exact ⟨hout, hstor.symm, hbal.symm, (hcode1.trans hcode2).symm⟩
  · have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
    rw [hpopStack] at hp1
    have hflag :
        (sevm.currentTarget.toB256 =? Sevm.argWord sevm 0) = w :=
      pref_head_unique hp1 (pref_append [w] s2.stack)
    have heq : Sevm.argWord sevm 0 = sevm.currentTarget.toB256 := by
      by_contra hne
      have hne' :
          sevm.currentTarget.toB256 ≠ Sevm.argWord sevm 0 := by
        exact fun h => hne h.symm
      rw [B256.eqCheck, if_neg hne'] at hflag
      exact hnz hflag.symm
    have hm : s.memory = s3.memory :=
      (Line.of_inv Devm.memory (by
        unfold guard
        line_inv) hguard).trans
        (hpop.memory.trans hburn.memory)
    have hwf3 : Mem.Wf s3.memory := by
      rw [← hm]
      exact h_wf
    have hrd3 : Mem.Reads s3.memory img := by
      rw [← hm]
      exact h_reads
    obtain ⟨hout, hcode2⟩ :=
      maxFlashLoanSelf_output nil_pref hwf3 hrd3 hself
    have hs : Devm.getStor s = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by
        unfold guard
        line_inv) hguard).trans
        ((funext fun a => (Devm.PopBurn.getStor hpop a).symm).trans
          (funext fun a => getStor_eq_of_state_eq hburn.state a))
    change ReturnsWord
      (Nat.toB256 maxFlashMinted -
        (Devm.getStor s3 sevm.currentTarget).get flashMintedSlot) r at hout
    rw [← congrFun hs sevm.currentTarget] at hout
    have hcode1 : Devm.getCode s = Devm.getCode s3 :=
      (Line.of_inv Devm.getCode (by
        unfold guard
        line_inv) hguard).trans
        ((funext fun a => getCode_eq_of_state_eq hpop.state a).trans
          (funext fun a => getCode_eq_of_state_eq hburn.state a))
    rw [if_pos heq]
    exact ⟨hout, hstor.symm, hbal.symm, (hcode1.trans hcode2).symm⟩

/-! ## Compiled public-selector observations -/

/-- The common public contract of successful read-only selectors: recognized
nonpayable ingress, exact output, and no persistent world mutation. -/
def PublicReadResult (P : Devm → Prop)
    (sevm : Sevm) (pre post : Devm) : Prop :=
  sevm.value = 0 ∧ P post ∧
    Devm.getStor post = Devm.getStor pre ∧
    Devm.getBal post = Devm.getBal pre ∧
    Devm.getCode post = Devm.getCode pre

/-- Lift a storage-word body observation while rewriting its entry slot from
the post-dispatch body state back to the public pre-state. -/
lemma of_exec_storageWordObservation
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    {sig key : B256} {body : Func} {img : Bytes}
    (h_stor : Func.Inv Devm.getStor Devm.getStor body)
    (h_bal : Func.Inv Devm.getBal Devm.getBal body)
    (observe : ∀ {s r : Devm} {img : Bytes},
      Mem.Wf s.memory →
      Mem.Reads s.memory img →
      Func.Run ((weth10 dp).main :: weth10Aux) sevm s body r →
      ReturnsWord (Devm.getStorVal s sevm.currentTarget key) r ∧
        Devm.getCode s = Devm.getCode r)
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = sig)
    (h_nonempty : sevm.data.length.toB256 ≠ 0)
    (h_mem : (sig, nonpayable body) ∈ weth10Funcs dp) :
    PublicReadResult
      (ReturnsWord (Devm.getStorVal pre sevm.currentTarget key))
      sevm pre post := by
  rcases exec_enters_weth10Nonpayable exc h_code h_sel h_nonempty h_mem with
    ⟨mid, hvalue, hstor0, hbal0, hcode0, hmemory, run⟩
  have hwf : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hrd : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  rcases observe hwf hrd run with ⟨hobs, hcode⟩
  change ReturnsWord ((Devm.getStor mid sevm.currentTarget).get key) post
    at hobs
  rw [hstor0] at hobs
  have hstor : Devm.getStor mid = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor h_stor run
  have hbal : Devm.getBal mid = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal h_bal run
  exact ⟨hvalue, hobs, hstor.symm.trans hstor0,
    hbal.symm.trans hbal0, hcode.symm.trans hcode0⟩

theorem name_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "name" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult (ReturnsBytes nameOutput) sevm pre post := by
  unfold PublicReadResult
  exact of_exec_nonpayableObservation
    (by func_inv) (by func_inv)
    (fun hwf hrd run => name_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem symbol_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "symbol" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult (ReturnsBytes symbolOutput) sevm pre post := by
  unfold PublicReadResult
  exact of_exec_nonpayableObservation
    (by func_inv) (by func_inv)
    (fun hwf hrd run => symbol_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem callbackSuccess_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "CALLBACK_SUCCESS" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult (ReturnsWord CALLBACK_SUCCESS) sevm pre post := by
  unfold PublicReadResult
  exact of_exec_nonpayableObservation
    (by func_inv) (by func_inv)
    (fun hwf hrd run => callbackSuccess_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem permitTypehash_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "PERMIT_TYPEHASH" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult (ReturnsWord PERMIT_TYPEHASH) sevm pre post := by
  unfold PublicReadResult
  exact of_exec_nonpayableObservation
    (by func_inv) (by func_inv)
    (fun hwf hrd run => permitTypehash_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem decimals_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "decimals" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult (ReturnsWord 0x12) sevm pre post := by
  unfold PublicReadResult
  exact of_exec_nonpayableObservation
    (by func_inv) (by func_inv)
    (fun hwf hrd run => decimals_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem deploymentChainId_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "deploymentChainId" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult (ReturnsWord dp.deploymentChainId) sevm pre post := by
  unfold PublicReadResult
  exact of_exec_nonpayableObservation
    (by unfold deploymentChainId returnDeployWord pushDeployWord; func_inv)
    (by unfold deploymentChainId returnDeployWord pushDeployWord; func_inv)
    (fun hwf hrd run => deploymentChainId_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem domainSeparator_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "DOMAIN_SEPARATOR" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult
      (ReturnsWord
        (permitDomainSeparator dp sevm.benvStat.chainId.toB256
          sevm.currentTarget))
      sevm pre post := by
  unfold PublicReadResult
  exact of_exec_nonpayableObservation
    (by
      unfold domainSeparator calculateDomainSeparator returnDeployWord
        pushDeployWord
      func_inv)
    (by
      unfold domainSeparator calculateDomainSeparator returnDeployWord
        pushDeployWord
      func_inv)
    (fun hwf hrd run =>
      domainSeparator_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem balanceOf_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "balanceOf" [.address])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult
      (ReturnsWord (Devm.getStorVal pre sevm.currentTarget
        (Sevm.argWord sevm 0))) sevm pre post := by
  exact of_exec_storageWordObservation
    (by func_inv) (by func_inv)
    (fun hwf hrd run => balanceOf_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem allowance_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "allowance" [.address, .address])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult
      (ReturnsWord (Devm.getStorVal pre sevm.currentTarget
        (allowanceCallKey sevm))) sevm pre post := by
  exact of_exec_storageWordObservation
    (by func_inv) (by func_inv)
    (fun hwf hrd run => allowance_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem nonces_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "nonces" [.address])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult
      (ReturnsWord (Devm.getStorVal pre sevm.currentTarget
        (nonceTagWord ||| Sevm.argWord sevm 0))) sevm pre post := by
  exact of_exec_storageWordObservation
    (by func_inv) (by func_inv)
    (fun hwf hrd run => nonces_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem flashMinted_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "flashMinted" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult
      (ReturnsWord (Devm.getStorVal pre sevm.currentTarget flashMintedSlot))
      sevm pre post := by
  exact of_exec_storageWordObservation
    (by func_inv) (by func_inv)
    (fun hwf hrd run => flashMinted_output nil_pref hwf hrd run)
    h_wf h_reads exc h_code h_sel h_nonempty
    (by simp [weth10Funcs])

theorem totalSupply_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "totalSupply" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult
      (ReturnsWord
        (Devm.getStorVal pre sevm.currentTarget flashMintedSlot +
          pre.getBal sevm.currentTarget)) sevm pre post := by
  rcases exec_enters_weth10Nonpayable (body := totalSupply)
      exc h_code h_sel h_nonempty
      (by simp [weth10Funcs]) with
    ⟨mid, hvalue, hstor0, hbal0, hcode0, hmemory, run⟩
  have hwf : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hrd : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  rcases totalSupply_output nil_pref hwf hrd run with ⟨hobs, hcode⟩
  change ReturnsWord
    ((Devm.getStor mid sevm.currentTarget).get flashMintedSlot +
      mid.getBal sevm.currentTarget) post at hobs
  rw [hstor0, hbal0] at hobs
  have hstor : Devm.getStor mid = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) run
  have hbal : Devm.getBal mid = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) run
  exact ⟨hvalue, hobs, hstor.symm.trans hstor0,
    hbal.symm.trans hbal0, hcode.symm.trans hcode0⟩

theorem maxFlashLoan_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "maxFlashLoan" [.address])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult
      (ReturnsWord
        (if Sevm.argWord sevm 0 = sevm.currentTarget.toB256 then
          Nat.toB256 maxFlashMinted -
            Devm.getStorVal pre sevm.currentTarget flashMintedSlot
         else 0))
      sevm pre post := by
  rcases exec_enters_weth10Nonpayable (body := maxFlashLoan)
      exc h_code h_sel h_nonempty (by simp [weth10Funcs]) with
    ⟨mid, hvalue, hstor0, hbal0, hcode0, hmemory, run⟩
  have hwf : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hrd : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  rcases maxFlashLoan_output hwf hrd run with
    ⟨hout, hstor, hbal, hcode⟩
  change ReturnsWord
    (if Sevm.argWord sevm 0 = sevm.currentTarget.toB256 then
      Nat.toB256 maxFlashMinted -
        (Devm.getStor mid sevm.currentTarget).get flashMintedSlot
     else 0) post at hout
  rw [hstor0] at hout
  exact ⟨hvalue, hout, hstor.trans hstor0,
    hbal.trans hbal0, hcode.trans hcode0⟩

theorem flashFee_exec_output
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm =
      selector "flashFee" [.address, .uint256])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    PublicReadResult
      (fun d =>
        Sevm.argWord sevm 0 = sevm.currentTarget.toB256 ∧
          ReturnsWord 0 d)
      sevm pre post := by
  rcases exec_enters_weth10Nonpayable (body := flashFee)
      exc h_code h_sel h_nonempty (by simp [weth10Funcs]) with
    ⟨mid, hvalue, hstor0, hbal0, hcode0, hmemory, run⟩
  have hwf : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hrd : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  rcases flashFee_output hwf hrd run with
    ⟨htoken, hout, hstor, hbal, hcode⟩
  exact ⟨hvalue, ⟨htoken, hout⟩,
    hstor.trans hstor0, hbal.trans hbal0, hcode.trans hcode0⟩

end Weth10

end Blanc
