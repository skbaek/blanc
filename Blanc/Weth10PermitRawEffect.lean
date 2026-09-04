-- Raw-word storage effect of WETH10's ERC-2612 `permit` endpoint, stated
-- without any canonical-calldata hypothesis.
--
-- `Blanc/Weth10Permit.lean` states permit's success effect over canonical
-- calldata, so its allowance write lands at the normalized `allowanceKey`.
-- The runtime hashes the two raw argument words it copies into memory words
-- 0 and 1, which agree with the normalized pair only on canonical calldata.
-- This module mirrors the same chain with every canonical-translation layer
-- removed, so the resulting storage image holds of short and dirty calldata
-- as well.

import Blanc.StaticPrecompileMessage
import Blanc.Weth10Permit
import Blanc.Weth10StateSound

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Raw calldata and memory images

Every reader below is total: `Sevm.argWord` zero-pads past the end of
calldata, and `CALLDATACOPY` zero-fills.  Nothing in this section assumes
that the incoming calldata is well formed. -/

private lemma takeD_add {ξ : Type} :
    ∀ (m n : Nat) (l : List ξ) (d : ξ),
      List.takeD (m + n) l d =
        List.takeD m l d ++ List.takeD n (l.drop m) d
  | 0, n, l, d => by simp
  | m + 1, n, l, d => by
      rw [show m + 1 + n = (m + n) + 1 from by omega,
        List.takeD_succ, List.takeD_succ, takeD_add m n l.tail d,
        List.drop_tail, show m + 1 = 1 + m from by omega,
        ← List.drop_drop]
      rfl

/-- The 64 calldata bytes `argCopy 0 0 2` copies into memory words 0 and 1
are exactly the two raw argument words the runtime then hashes. -/
lemma permitRawArgPair (e : Sevm) :
    e.data.sliceD 4 64 0 =
      (Sevm.argWord e 0).toBytes ++ (Sevm.argWord e 1).toBytes := by
  have h0 : Sevm.argWord e 0 =
      Bytes.toB256 (List.takeD 32 (e.data.drop 4) 0) := by
    unfold Sevm.argWord Sevm.dataWord List.sliceD
    rw [show ((32 * (0 : B256)) + 4).toNat = 4 from by decide]
  have h1 : Sevm.argWord e 1 =
      Bytes.toB256 (List.takeD 32 (e.data.drop 36) 0) := by
    unfold Sevm.argWord Sevm.dataWord List.sliceD
    rw [show ((32 * (1 : B256)) + 4).toNat = 36 from by decide]
  rw [h0, h1,
    Bytes.toBytes_toB256_of_length (List.takeD_length 32 (e.data.drop 4) 0),
    Bytes.toBytes_toB256_of_length (List.takeD_length 32 (e.data.drop 36) 0)]
  show List.takeD 64 (e.data.drop 4) 0 =
    List.takeD 32 (e.data.drop 4) 0 ++ List.takeD 32 (e.data.drop 36) 0
  rw [show (64 : Nat) = 32 + 32 from rfl, takeD_add,
    List.drop_drop, show 32 + 4 = 36 from rfl]

/-- Exact memory effect of `argCopy 0 0 2`, the owner/spender word-pair copy
shared by `approve`'s and `permit`'s allowance-key fragments. -/
lemma of_run_argCopy002 {e : Sevm} {s s' : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s (argCopy 0 0 2) s') :
    xs <<+ s'.stack ∧
      s'.memory = s.memory.write 0 (e.data.sliceD 4 64 0) := by
  simp only [argCopy, cdc] at run
  rcases Line.of_run_cons run with ⟨u1, q1, run1⟩
  have hp1 : (64 : B256) :: xs <<+ u1.stack := by
    have hword : (2 * 32 : B256) = 64 := by decide +kernel
    rw [hword] at q1
    exact prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons run1 with ⟨u2, q2, run2⟩
  have hp2 : (4 : B256) :: 64 :: xs <<+ u2.stack := by
    have hword : (0 * 32 + 4 : B256) = 4 := by decide +kernel
    rw [hword] at q2
    exact prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons run2 with ⟨u3, q3, run3⟩
  have hp3 : (0 : B256) :: 4 :: 64 :: xs <<+ u3.stack := by
    have hword : (0 * 32 : B256) = 0 := by decide +kernel
    rw [hword] at q3
    exact prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons run3 with ⟨u4, q4, hnil⟩
  cases hnil
  rcases prefix_of_calldatacopy_val q4 hp3 with ⟨hp4, hm4⟩
  refine ⟨hp4, ?_⟩
  rw [hm4,
    ← (Ninst.Hinv.inv (f := Devm.memory) q3),
    ← (Ninst.Hinv.inv (f := Devm.memory) q2),
    ← (Ninst.Hinv.inv (f := Devm.memory) q1)]
  rfl

/-- Value-carrying allowance-key computation from a known 64-byte window.
Unlike `Weth10StateFunctional`'s image version this needs no `Mem.Wf`
premise, because the caller supplies the window it just wrote. -/
lemma prefix_of_allowanceKeyFromMemory_val {e : Sevm} {xs : Stack}
    {s s' : Devm} {bs : Bytes}
    (hp : xs <<+ s.stack)
    (hread : (s.memory.read 0 64).1 = bs)
    (run : Line.Run e s allowanceKeyFromMemory s') :
    (allowanceTagWord ||| (allowancePayloadMask &&& Bytes.keccak bs)) ::
      xs <<+ s'.stack := by
  unfold allowanceKeyFromMemory pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨s1, hpush64, run1⟩
  have hb64 := of_run_pushB256 hpush64
  have hp1 : (64 : B256) :: xs <<+ s1.stack := prefix_of_push hb64 hp
  rcases Line.of_run_cons run1 with ⟨s2, hpush0, run2⟩
  have hb0 := of_run_pushB256 hpush0
  have hp2 : (0 : B256) :: 64 :: xs <<+ s2.stack := prefix_of_push hb0 hp1
  have hm2 : s.memory = s2.memory := hb64.memory.trans hb0.memory
  rcases Line.of_run_cons run2 with ⟨s3, hkeccak256, run3⟩
  rcases prefix_of_keccak256_val hkeccak256 hp2 with ⟨hp3, _⟩
  change (s2.memory.read 0 64).1.keccak :: xs <<+ s3.stack at hp3
  rw [← hm2, hread] at hp3
  rcases Line.of_run_cons run3 with ⟨s4, hpushMask, run4⟩
  have hp4 : allowancePayloadMask :: Bytes.keccak bs :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 hpushMask) hp3
  rcases Line.of_run_cons run4 with ⟨s5, hand, run5⟩
  have hp5 : (allowancePayloadMask &&& Bytes.keccak bs) :: xs <<+ s5.stack :=
    prefix_of_and hand hp4
  rcases Line.of_run_cons run5 with ⟨s6, hpushTag, run6⟩
  have hp6 : allowanceTagWord ::
      (allowancePayloadMask &&& Bytes.keccak bs) :: xs <<+ s6.stack :=
    prefix_of_push (of_run_pushB256 hpushTag) hp5
  rcases Line.of_run_cons run6 with ⟨s7, hor, hnil⟩
  cases hnil
  exact prefix_of_or hor hp6

/-! ## The raw approval tail -/

/-- The tagged key permit's approval tail actually stores at: the runtime
hashes the raw argument words copied into memory words 0 and 1, so a dirty
spender word is used verbatim rather than normalized. -/
def permitRuntimeAllowanceKey (e : Sevm) : B256 :=
  allowanceTagWord |||
    (allowancePayloadMask &&&
      Bytes.keccak ((Sevm.argWord e 0).toBytes ++ (Sevm.argWord e 1).toBytes))

/-- `approvePermit`'s unique storage write, stated over the raw argument
words.  No calldata hypothesis and no memory well-formedness premise. -/
theorem approvePermit_raw_storage
    {fs : List Func} {sevm : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Func.Run fs sevm s approvePermit r) :
    Devm.getStor r sevm.currentTarget =
      (Devm.getStor s sevm.currentTarget).set
        (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2) := by
  unfold approvePermit at run
  rcases of_run_prepend (argCopy 0 0 2) _ run with ⟨s1, hcopy, run⟩
  rcases of_run_argCopy002 hp hcopy with ⟨hp1, hm1⟩
  have hlen : (sevm.data.sliceD 4 64 0).length = 64 := by
    unfold List.sliceD
    exact List.takeD_length 64 _ 0
  have hne : sevm.data.sliceD 4 64 0 ≠ [] := by
    intro h
    rw [h] at hlen
    exact absurd hlen (by decide)
  have hread : (s1.memory.read 0 64).1 =
      (Sevm.argWord sevm 0).toBytes ++ (Sevm.argWord sevm 1).toBytes := by
    rw [hm1, ← permitRawArgPair sevm, ← hlen]
    exact Mem.read_write_zero s.memory hne
  rcases of_run_prepend allowanceKeyFromMemory _ run with ⟨s2, hkey, run⟩
  have hp2 : permitRuntimeAllowanceKey sevm :: xs <<+ s2.stack :=
    prefix_of_allowanceKeyFromMemory_val hp1 hread hkey
  rcases of_run_prepend (arg 2) _ run with ⟨s3, harg, run⟩
  have hp3 : Sevm.argWord sevm 2 :: permitRuntimeAllowanceKey sevm :: xs <<+
      s3.stack := prefix_of_arg hp2 harg
  rcases of_run_next run with ⟨s4, hswap, run⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      (Sevm.argWord sevm 2 :: permitRuntimeAllowanceKey sevm :: xs)
      (permitRuntimeAllowanceKey sevm :: Sevm.argWord sevm 2 :: xs) :=
    Stack.swapCore_zero
  have hp4 : permitRuntimeAllowanceKey sevm :: Sevm.argWord sevm 2 :: xs <<+
      s4.stack := Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp3
  rcases of_run_next run with ⟨s5, hstore, htail⟩
  have hset : Devm.getStor s5 sevm.currentTarget =
      (Devm.getStor s4 sevm.currentTarget).set
        (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2) :=
    sstore_getStor_set hstore hp4
  have hbefore : Devm.getStor s = Devm.getStor s4 := by
    rw [Line.of_inv Devm.getStor (by line_inv) hcopy,
      Line.of_inv Devm.getStor (by
        unfold allowanceKeyFromMemory pushList
        line_inv) hkey,
      Line.of_inv Devm.getStor (by line_inv) harg,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil)]
  have hafter : Devm.getStor s5 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) htail
  rw [← congrFun hafter sevm.currentTarget, hset,
    ← congrFun hbefore sevm.currentTarget]

/-! ## The raw signer guards

The canonical version of this walk translates the recovered word through
`argWord_zero_of_decodesPermit`.  Removing that step leaves the policy
itself, which is stated over the raw first argument word. -/

/-- Exact successful policy enforced after ECRECOVER together with its frame,
over raw calldata: zero and wrong-owner words cannot reach the approval tail,
and the two guards change no storage, memory, logs or output. -/
theorem of_permitSignerGuards_raw_frame (dp : DeployParams)
    {sevm : Sevm} {s r : Devm} {signer : B256} {xs : Stack}
    (hp : signer :: xs <<+ s.stack)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      permitSignerGuards r) :
    signer ≠ 0 ∧ signer = Sevm.argWord sevm 0 ∧
      ∃ t, xs <<+ t.stack ∧
        Devm.getStor t = Devm.getStor s ∧
        t.memory = s.memory ∧ t.logs = s.logs ∧ t.output = s.output ∧
        Func.Run ((weth10 dp).main :: weth10Aux) sevm t approvePermit r := by
  unfold permitSignerGuards at run
  rcases of_run_next run with ⟨s1, hdup, run⟩
  have hp1 : signer :: signer :: xs <<+ s1.stack :=
    prefix_of_dup_val hdup (by show_nth) hp
  rcases of_run_next run with ⟨s2, hzero, run⟩
  have hp2 : (signer =? 0) :: signer :: xs <<+ s2.stack :=
    prefix_of_iszero hzero hp1
  rcases of_run_branch run with
      ⟨s3, hpop1, run⟩ |
      ⟨w1, s3, s4, hnz1, hpop1, hburn1, hinvalid1⟩
  · have hflag1 : (0 : B256) = (signer =? 0) :=
      (popBurn_pref hpop1 hp2).1
    have hsigner : signer ≠ 0 := by
      intro hz
      subst signer
      simp [B256.eqCheck] at hflag1
      exact B256.zero_ne_one hflag1
    have hp3 : signer :: xs <<+ s3.stack := (popBurn_pref hpop1 hp2).2
    rcases of_run_prepend (arg 0) _ run with ⟨s4, harg0, run⟩
    have hp4 : Sevm.argWord sevm 0 :: signer :: xs <<+ s4.stack :=
      prefix_of_arg hp3 harg0
    rcases of_run_next run with ⟨s5, heq, run⟩
    have hp5 : (Sevm.argWord sevm 0 =? signer) :: xs <<+ s5.stack :=
      prefix_of_eq heq hp4
    rcases of_run_next run with ⟨s6, hzero2, run⟩
    have hp6 : ((Sevm.argWord sevm 0 =? signer) =? 0) :: xs <<+ s6.stack :=
      prefix_of_iszero hzero2 hp5
    rcases of_run_branch run with
        ⟨t, hpop2, happrove⟩ |
        ⟨w2, t0, t, hnz2, hpop2, hburn2, hinvalid2⟩
    · have hflag2 : (0 : B256) = ((Sevm.argWord sevm 0 =? signer) =? 0) :=
        (popBurn_pref hpop2 hp6).1
      have howner : signer = Sevm.argWord sevm 0 := by
        by_contra hne
        have hne' : Sevm.argWord sevm 0 ≠ signer := Ne.symm hne
        simp [B256.eqCheck, hne'] at hflag2
        exact B256.zero_ne_one hflag2
      have hstor : Devm.getStor t = Devm.getStor s := by
        symm
        calc
          Devm.getStor s = Devm.getStor s1 :=
            Ninst.Hinv.inv (f := Devm.getStor) hdup
          _ = Devm.getStor s2 := Ninst.Hinv.inv (f := Devm.getStor) hzero
          _ = Devm.getStor s3 := PopBurn.Inv.inv hpop1
          _ = Devm.getStor s4 :=
            Line.of_inv Devm.getStor (by line_inv) harg0
          _ = Devm.getStor s5 := Ninst.Hinv.inv (f := Devm.getStor) heq
          _ = Devm.getStor s6 := Ninst.Hinv.inv (f := Devm.getStor) hzero2
          _ = Devm.getStor t := PopBurn.Inv.inv hpop2
      have hmemory : t.memory = s.memory := by
        symm
        calc
          s.memory = s1.memory := Ninst.Hinv.inv (f := Devm.memory) hdup
          _ = s2.memory := Ninst.Hinv.inv (f := Devm.memory) hzero
          _ = s3.memory := hpop1.memory
          _ = s4.memory := Line.of_inv Devm.memory (by line_inv) harg0
          _ = s5.memory := Ninst.Hinv.inv (f := Devm.memory) heq
          _ = s6.memory := Ninst.Hinv.inv (f := Devm.memory) hzero2
          _ = t.memory := hpop2.memory
      have hlogs : t.logs = s.logs := by
        symm
        calc
          s.logs = s1.logs := Ninst.Hinv.inv (f := Devm.logs) hdup
          _ = s2.logs := Ninst.Hinv.inv (f := Devm.logs) hzero
          _ = s3.logs := hpop1.logs
          _ = s4.logs := Line.of_inv Devm.logs (by line_inv) harg0
          _ = s5.logs := Ninst.Hinv.inv (f := Devm.logs) heq
          _ = s6.logs := Ninst.Hinv.inv (f := Devm.logs) hzero2
          _ = t.logs := hpop2.logs
      have houtput : t.output = s.output := by
        symm
        calc
          s.output = s1.output := Ninst.Hinv.inv (f := Devm.output) hdup
          _ = s2.output := Ninst.Hinv.inv (f := Devm.output) hzero
          _ = s3.output := hpop1.output
          _ = s4.output := Line.of_inv Devm.output (by line_inv) harg0
          _ = s5.output := Ninst.Hinv.inv (f := Devm.output) heq
          _ = s6.output := Ninst.Hinv.inv (f := Devm.output) hzero2
          _ = t.output := hpop2.output
      exact ⟨hsigner, howner, t, (popBurn_pref hpop2 hp6).2,
        hstor, hmemory, hlogs, houtput, happrove⟩
    · rcases of_run_call hinvalid2 with ⟨f, u, hget, hcallBurn, hrev⟩
      have hf : f = invalidPermitError := by
        simpa [weth10Aux, invalidPermitErrorSlot] using hget.symm
      subst f
      exact absurd hrev Func.not_run_revertWith
  · rcases of_run_call hinvalid1 with ⟨f, u, hget, hcallBurn, hrev⟩
    have hf : f = invalidPermitError := by
      simpa [weth10Aux, invalidPermitErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revertWith

/-! ## The raw nonce prefix -/

private lemma raw_prefix_of_chainid {e : Sevm} {s s' : Devm} {xs : Stack}
    (hp : xs <<+ s.stack) (h : Ninst.Run e s chainid s') :
    e.benvStat.chainId.toB256 :: xs <<+ s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact prefix_of_push (Devm.pushBurn_of_pushItem run) hp

private lemma raw_memory_eq_of_chainid {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s chainid s') : s.memory = s'.memory := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).memory

/-- The tagged nonce key permit's prefix actually stores at: `addressArg 0`
normalizes the raw first argument word to its low 160 bits, and
`tagNonceKey` sets the nonce-region tag. -/
def permitRuntimeNonceKey (e : Sevm) : B256 :=
  nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord e 0)

/-- Exact raw effect of permit's nonce prefix: the pre-state nonce at the
tagged runtime key is stored at memory word 4 for the signed struct, and
`nonce + 1` is tentatively written back to that same key. -/
theorem of_permitNoncePrepare_raw {sevm : Sevm} {s t : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run sevm s permitNoncePrepare t) :
    let nonce :=
      Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm)
    sevm.benvStat.chainId.toB256 :: xs <<+ t.stack ∧
      Devm.getStor t sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set
          (permitRuntimeNonceKey sevm) (nonce + 1) ∧
      t.memory = s.memory.write 128 nonce.toBytes := by
  dsimp only
  unfold permitNoncePrepare at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : sevm.benvStat.chainId.toB256 :: xs <<+ s1.stack :=
    raw_prefix_of_chainid hp q1
  rcases of_run_append (addressArg 0) run with ⟨s2, h2, run⟩
  have hp2 : ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s2.stack :=
    prefix_of_addressArg hp1 h2
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  have hp3 : ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s3.stack :=
    prefix_of_dup_val q3 (by show_nth) hp2
  rcases of_run_append tagNonceKey run with ⟨s4, h4, run⟩
  have hp4 : permitRuntimeNonceKey sevm ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s4.stack := by
    unfold tagNonceKey at h4
    rcases Line.of_run_cons h4 with ⟨u41, q41, h4'⟩
    have hp41 : nonceTagWord ::
        ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
        ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
        sevm.benvStat.chainId.toB256 :: xs <<+ u41.stack :=
      prefix_of_push (of_run_pushB256 q41) hp3
    rcases Line.of_run_cons h4' with ⟨u42, q42, hnil⟩
    cases hnil
    exact prefix_of_or q42 hp41
  rcases Line.of_run_cons run with ⟨s5, q5, run⟩
  have hp5 : permitRuntimeNonceKey sevm :: permitRuntimeNonceKey sevm ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s5.stack :=
    prefix_of_dup_val q5 (by show_nth) hp4
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  rcases prefix_of_sload q6 hp5 with ⟨nonce, hp6, hnonce⟩
  have hstor5 : Devm.getStor s = Devm.getStor s5 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) q1
      _ = Devm.getStor s2 := Line.of_inv Devm.getStor (by line_inv) h2
      _ = Devm.getStor s3 := Ninst.Hinv.inv (f := Devm.getStor) q3
      _ = Devm.getStor s4 := Line.of_inv Devm.getStor (by
        unfold tagNonceKey
        line_inv) h4
      _ = Devm.getStor s5 := Ninst.Hinv.inv (f := Devm.getStor) q5
  have hnonce' : nonce =
      Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm) := by
    rw [hnonce]
    change (Devm.getStor s5 sevm.currentTarget).get (permitRuntimeNonceKey sevm) =
      (Devm.getStor s sevm.currentTarget).get (permitRuntimeNonceKey sevm)
    rw [← hstor5]
  rw [hnonce'] at hp6
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have hp7 :
      Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm) ::
      Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm) ::
      permitRuntimeNonceKey sevm ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s7.stack :=
    prefix_of_dup_val q7 (by show_nth) hp6
  rcases of_run_append (mstoreAt 4) run with ⟨s8, h8, run⟩
  rcases of_run_mstoreAt_val h8 hp7 with ⟨hp8, hm8⟩
  rw [show (((4 : B256) * 32).toNat) = 128 from rfl] at hm8
  rcases Line.of_run_cons run with ⟨s9, q9, run⟩
  have hp9 : (1 : B256) ::
      Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm) ::
      permitRuntimeNonceKey sevm ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s9.stack :=
    prefix_of_push (of_run_pushB256 q9) hp8
  rcases Line.of_run_cons run with ⟨s10, q10, run⟩
  have hp10 :
      (Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm) + 1) ::
      permitRuntimeNonceKey sevm ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s10.stack := by
    have h := prefix_of_add q10 hp9
    simpa only [B256.add_comm] using h
  rcases Line.of_run_cons run with ⟨s11, q11, run⟩
  have hp11 : permitRuntimeNonceKey sevm ::
      (Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm) + 1) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s11.stack := by
    have hswap : Stack.Swap (0 : Fin 16).val
        ((Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm) + 1) ::
          permitRuntimeNonceKey sevm ::
          ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
          sevm.benvStat.chainId.toB256 :: xs)
        (permitRuntimeNonceKey sevm ::
          (Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm) + 1) ::
          ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
          sevm.benvStat.chainId.toB256 :: xs) :=
      Stack.swapCore_zero
    exact Stack.prefix_of_swap hswap (of_run_swap q11) hp10
  rcases Line.of_run_cons run with ⟨s12, q12, run⟩
  have hset : Devm.getStor s12 sevm.currentTarget =
      (Devm.getStor s11 sevm.currentTarget).set (permitRuntimeNonceKey sevm)
        (Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm) + 1) :=
    sstore_getStor_set q12 hp11
  have hp12 : ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s12.stack :=
    prefix_of_sstore q12 hp11
  rcases Line.of_run_cons run with ⟨s13, q13, hnil⟩
  cases hnil
  rcases of_run_pop q13 with ⟨w13, hpop13⟩
  have hp13 : sevm.benvStat.chainId.toB256 :: xs <<+ t.stack :=
    (popBurn_pref hpop13 hp12).2
  have hstor11 : Devm.getStor s = Devm.getStor s11 := by
    calc
      Devm.getStor s = Devm.getStor s5 := hstor5
      _ = Devm.getStor s6 := Ninst.Hinv.inv (f := Devm.getStor) q6
      _ = Devm.getStor s7 := Ninst.Hinv.inv (f := Devm.getStor) q7
      _ = Devm.getStor s8 :=
        Line.of_inv Devm.getStor (by line_inv) h8
      _ = Devm.getStor s9 := Ninst.Hinv.inv (f := Devm.getStor) q9
      _ = Devm.getStor s10 := Ninst.Hinv.inv (f := Devm.getStor) q10
      _ = Devm.getStor s11 := Ninst.Hinv.inv (f := Devm.getStor) q11
  have hstor12 : Devm.getStor s12 = Devm.getStor t :=
    Ninst.Hinv.inv (f := Devm.getStor) q13
  have hm_to7 : s.memory = s7.memory := by
    calc
      s.memory = s1.memory := raw_memory_eq_of_chainid q1
      _ = s2.memory := Line.of_inv Devm.memory (by line_inv) h2
      _ = s3.memory := Ninst.Hinv.inv (f := Devm.memory) q3
      _ = s4.memory := Line.of_inv Devm.memory (by
        unfold tagNonceKey
        line_inv) h4
      _ = s5.memory := Ninst.Hinv.inv (f := Devm.memory) q5
      _ = s6.memory := Ninst.Hinv.inv (f := Devm.memory) q6
      _ = s7.memory := Ninst.Hinv.inv (f := Devm.memory) q7
  have hm8_to_t : s8.memory = t.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons q9
        (Line.Run.cons q10
          (Line.Run.cons q11
            (Line.Run.cons q12 (Line.Run.cons q13 Line.Run.nil)))))
  refine ⟨hp13, ?_, ?_⟩
  · rw [← congrFun hstor12 sevm.currentTarget, hset,
      ← congrFun hstor11 sevm.currentTarget]
  · rw [← hm8_to_t, hm8, ← hm_to7]

/-! ## The raw struct-hash prefix

Only the stack shape and memory well-formedness are needed here: the exact
hashed image is a canonical-translation fact, while the domain dispatch and
digest walks reused below are already raw. -/

/-- Exact memory effect of `argCopy 1 0 3`, the signed-argument copy embedded
in permit's struct-hash suffix. -/
lemma of_run_argCopy103 {e : Sevm} {s s' : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s (argCopy 1 0 3) s') :
    xs <<+ s'.stack ∧
      s'.memory = s.memory.write 32 (e.data.sliceD 4 96 0) := by
  simp only [argCopy, cdc] at run
  rcases Line.of_run_cons run with ⟨u1, q1, run1⟩
  have hp1 : (96 : B256) :: xs <<+ u1.stack := by
    have hword : (3 * 32 : B256) = 96 := by decide +kernel
    rw [hword] at q1
    exact prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons run1 with ⟨u2, q2, run2⟩
  have hp2 : (4 : B256) :: 96 :: xs <<+ u2.stack := by
    have hword : (0 * 32 + 4 : B256) = 4 := by decide +kernel
    rw [hword] at q2
    exact prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons run2 with ⟨u3, q3, run3⟩
  have hp3 : (32 : B256) :: 4 :: 96 :: xs <<+ u3.stack := by
    have hword : (1 * 32 : B256) = 32 := by decide +kernel
    rw [hword] at q3
    exact prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons run3 with ⟨u4, q4, hnil⟩
  cases hnil
  rcases prefix_of_calldatacopy_val q4 hp3 with ⟨hp4, hm4⟩
  refine ⟨hp4, ?_⟩
  rw [hm4,
    ← (Ninst.Hinv.inv (f := Devm.memory) q3),
    ← (Ninst.Hinv.inv (f := Devm.memory) q2),
    ← (Ninst.Hinv.inv (f := Devm.memory) q1)]
  rfl

/-- The struct-hash suffix leaves one word on the stack and preserves memory
well-formedness, on arbitrary calldata. -/
theorem of_permitStructPrepare_raw {sevm : Sevm} {s t : Devm} {xs : Stack}
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (run : Line.Run sevm s permitStructPrepare t) :
    (∃ structHash, structHash :: xs <<+ t.stack) ∧ Mem.Wf t.memory := by
  unfold permitStructPrepare pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hb1 := of_run_pushB256 q1
  have hp1 : PERMIT_TYPEHASH :: xs <<+ s1.stack := prefix_of_push hb1 hp
  have hwf1 : Mem.Wf s1.memory := hb1.memory ▸ hwf
  rcases of_run_append (mstoreAt 0) run with ⟨s2, h2, run⟩
  rcases of_run_mstoreAt_val h2 hp1 with ⟨hp2, hm2⟩
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2]
    exact hwf1.write _ _
  rcases of_run_append (argCopy 1 0 3) run with ⟨s3, h3, run⟩
  rcases of_run_argCopy103 hp2 h3 with ⟨hp3, hm3⟩
  have hwf3 : Mem.Wf s3.memory := by
    rw [hm3]
    exact hwf2.write _ _
  rcases of_run_append (arg 3) run with ⟨s4, h4, run⟩
  have hp4 : Sevm.argWord sevm 3 :: xs <<+ s4.stack := prefix_of_arg hp3 h4
  have hwf4 : Mem.Wf s4.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) h4]
    exact hwf3
  rcases of_run_append (mstoreAt 5) run with ⟨s5, h5, run⟩
  rcases of_run_mstoreAt_val h5 hp4 with ⟨hp5, hm5⟩
  have hwf5 : Mem.Wf s5.memory := by
    rw [hm5]
    exact hwf4.write _ _
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  have hb6 := of_run_pushB256 q6
  have hp6 : (192 : B256) :: xs <<+ s6.stack := prefix_of_push hb6 hp5
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have hb7 := of_run_pushB256 q7
  have hp7 : (0 : B256) :: 192 :: xs <<+ s7.stack := prefix_of_push hb7 hp6
  have hwf7 : Mem.Wf s7.memory := by
    rw [← hb7.memory, ← hb6.memory]
    exact hwf5
  rcases Line.of_run_cons run with ⟨s8, q8, hnil⟩
  cases hnil
  rcases prefix_of_keccak256_val q8 hp7 with ⟨hp8, hm8⟩
  refine ⟨⟨_, hp8⟩, ?_⟩
  rw [hm8]
  exact hwf7.extend _ _

/-- Every memory reads as its own materialised backing array, so a reader
image is available for free whenever one is needed only as a witness. -/
lemma mem_reads_self (μ : Mem) : Mem.Reads μ μ.data.toList := by
  intro i
  simp

/-! ## Reaching the recovery body -/

/-- Raw prefix from the selected `permit` body to `permitRecover`.  The
deadline guard, domain dispatch and both hash walks are already stated over
arbitrary calldata; only the nonce prefix had to be restated, because the
canonical version normalizes its key through `nonceKey`. -/
theorem of_permitToRecover_raw (dp : DeployParams)
    {sevm : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s (permit dp) r) :
    let nonce :=
      Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm)
    ∃ (t : Devm) (domain structHash : B256),
      domain :: structHash :: xs <<+ t.stack ∧
      Devm.getStor t sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set
          (permitRuntimeNonceKey sevm) (nonce + 1) ∧
      Devm.getCode t = Devm.getCode s ∧
      Mem.Wf t.memory ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm t permitRecover r := by
  dsimp only
  rcases of_permitDeadlineLive dp hp run with
    ⟨mid, hpMid, hstorMid, hcodeMid, hmemMid, _, _, hlive⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemMid]
    exact hwf
  have hnonceMid :
      Devm.getStorVal mid sevm.currentTarget (permitRuntimeNonceKey sevm) =
        Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm) := by
    change (Devm.getStor mid sevm.currentTarget).get _ =
      (Devm.getStor s sevm.currentTarget).get _
    rw [hstorMid]
  unfold permitAfterDeadline at hlive
  rcases of_run_prepend permitNoncePrepare _ hlive with
    ⟨s1, hnonceRun, hlive⟩
  rcases of_permitNoncePrepare_raw hpMid hnonceRun with
    ⟨hp1, hstor1, hm1⟩
  rw [hnonceMid] at hstor1 hm1
  rw [hstorMid] at hstor1
  have hwf1 : Mem.Wf s1.memory := by
    rw [hm1, hmemMid]
    exact hwf.write _ _
  rcases of_run_prepend permitStructPrepare _ hlive with
    ⟨s2, hstructRun, hdomainRun⟩
  rcases of_permitStructPrepare_raw hp1 hwf1 hstructRun with
    ⟨⟨structHash, hp2⟩, hwf2⟩
  have hstor2 : Devm.getStor s1 = Devm.getStor s2 :=
    Line.of_inv Devm.getStor (by
      unfold permitStructPrepare pushList
      line_inv) hstructRun
  have hcode1 : Devm.getCode s1 = Devm.getCode mid :=
    (Line.of_inv Devm.getCode (by
      unfold permitNoncePrepare addressArg normalizeAddress
        pushAddressMask tagNonceKey mstoreAt
      line_inv) hnonceRun).symm
  have hcode2 : Devm.getCode s2 = Devm.getCode s1 :=
    (Line.of_inv Devm.getCode (by
      unfold permitStructPrepare pushList
      line_inv) hstructRun).symm
  rcases of_permitDomainDispatch dp hp2 hwf2 (mem_reads_self s2.memory)
      hdomainRun with
    ⟨t, hp3, hstor3, hcode3, _, _, hwf3, _, hrecover⟩
  refine ⟨t, _, structHash, hp3, ?_, ?_, hwf3, hrecover⟩
  · rw [congrFun hstor3 sevm.currentTarget,
      ← congrFun hstor2 sevm.currentTarget, hstor1]
  · exact hcode3.trans (hcode2.trans (hcode1.trans hcodeMid))

/-! ## The raw ECRECOVER crossing -/

/-- Raw storage frame for permit's whole recovery line.  The recovered word
is left existential: the only thing the raw storage image needs from the
`STATICCALL` is that no account's storage moved. -/
theorem of_recoverPermitSigner_raw
    {sevm : Sevm} {s t : Devm} {digest : B256} {xs : Stack}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg : getDelegatedCodeAddress (s.getCode 1) = none)
    (hp : digest :: xs <<+ s.stack)
    (run : Line.Run sevm s recoverPermitSigner t) :
    (∃ signer : B256, signer :: xs <<+ t.stack) ∧
      Devm.getStor t = Devm.getStor s := by
  rw [recoverPermitSigner_eq_prepare] at run
  rcases of_run_append permitRecoverPrepare run with ⟨q, hprep, run⟩
  rcases permitRecoverPrepare_stack hp hprep with ⟨g, hpq⟩
  rcases permitRecoverPrepare_frame hprep with
    ⟨hstorPrep, _, _, hcodePrep⟩
  have hnodelegQ : getDelegatedCodeAddress (q.getCode 1) = none := by
    rw [← congrFun hcodePrep 1]
    exact hnodeleg
  rcases Line.of_run_cons run with ⟨u, qstat, htail⟩
  have hcross : (∃ w : B256, w :: xs <<+ u.stack) ∧
      Devm.getStor u = Devm.getStor q := by
    rcases of_run_staticcall_val_with_depth_cause hpq qstat with
        hfail | hsuccess
    · rcases hfail with ⟨hpU, hworld, _⟩
      refine ⟨⟨0, hpU⟩, ?_⟩
      funext a
      exact (getStor_eq_of_state_eq hworld.1 a).symm
    · rcases hsuccess with
        ⟨parent, child, xl, dpFlag, na, code, avail,
          _, hstack, hstate, _, _, _, hdel, _, hpm, _, _, hstateU, _, _,
          hstackU⟩
      have hpParent : xs <<+ parent.stack := by
        rw [hstack] at hpq
        exact cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
          (cons_pref_cons_inv (cons_pref_cons_inv
            (cons_pref_cons_inv hpq)))))
      obtain ⟨hna, hdpFalse⟩ : na = (1 : B256).toAdr ∧ dpFlag = false := by
        rcases hdel with ⟨_, hna, _, hdp⟩ | ⟨d, hsome, _, _, _⟩
        · exact ⟨hna, hdp⟩
        · change getDelegatedCodeAddress (q.getCode 1) = some d at hsome
          rw [hnodelegQ] at hsome
          cases hsome
      subst hna
      subst dpFlag
      have hchild := stor_of_processMessage_staticPrecomp
        (target := 1) hpre hpm
      refine ⟨⟨1, ?_⟩, ?_⟩
      · rw [hstackU]
        exact cons_pref_cons rfl hpParent
      · funext a
        calc
          Devm.getStor u a = Devm.getStor child a :=
            getStor_eq_of_state_eq hstateU a
          _ = Devm.getStor parent a := hchild a
          _ = Devm.getStor q a := getStor_eq_of_state_eq hstate a
  rcases hcross with ⟨⟨w, hpU⟩, hstorU⟩
  rcases Line.of_run_cons htail with ⟨u1, qpop, htail⟩
  rcases of_run_pop qpop with ⟨w1, hpop⟩
  have hp1 : xs <<+ u1.stack := (popBurn_pref hpop hpU).2
  rcases Line.of_run_cons htail with ⟨u2, qpush, htail⟩
  have hp2 : (128 : B256) :: xs <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 qpush) hp1
  rcases Line.of_run_cons htail with ⟨u3, qload, hnil⟩
  cases hnil
  rcases prefix_of_mload qload hp2 with ⟨signer, hp3⟩
  refine ⟨⟨signer, hp3⟩, ?_⟩
  calc
    Devm.getStor t = Devm.getStor u2 :=
      (Ninst.Hinv.inv (f := Devm.getStor) qload).symm
    _ = Devm.getStor u1 := (Ninst.Hinv.inv (f := Devm.getStor) qpush).symm
    _ = Devm.getStor u := (PopBurn.Inv.inv hpop).symm
    _ = Devm.getStor q := hstorU
    _ = Devm.getStor s := hstorPrep.symm

/-! ## The raw permit effect -/

/-- Byte-level shape of the tagged nonce key: `PUSH32 2^254; OR` applied to
the low-160-bit projection of the raw first argument word. -/
theorem permitRuntimeNonceKey_eq (e : Sevm) :
    permitRuntimeNonceKey e =
      nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord e 0) := rfl

/-- Byte-level shape of the tagged allowance key: the two raw argument words
copied into memory words 0 and 1, hashed, masked and tagged.  This is
definitionally `projectedAllowanceKey (Sevm.argWord e 0) (Sevm.argWord e 1)`,
which is the key the allowance attribution ledger projects. -/
theorem permitRuntimeAllowanceKey_eq (e : Sevm) :
    permitRuntimeAllowanceKey e =
      allowanceTagWord |||
        (allowancePayloadMask &&&
          Bytes.keccak
            ((Sevm.argWord e 0).toBytes ++ (Sevm.argWord e 1).toBytes)) := rfl

theorem permitRuntimeNonceKey_region (e : Sevm) :
    InRegion .nonce (permitRuntimeNonceKey e) := by
  have hvalid : ValidAdr ((~~~ addressMask) &&& Sevm.argWord e 0) :=
    normalizedAddress_valid _
  have howner : (((~~~ addressMask) &&& Sevm.argWord e 0).toAdr).toB256 =
      (~~~ addressMask) &&& Sevm.argWord e 0 := toB256_toAdr hvalid
  show InRegion .nonce (nonceTagWord ||| _)
  rw [← howner]
  simpa only [nonceTagWord, ← nonceKey_formula] using
    nonceKey_region (((~~~ addressMask) &&& Sevm.argWord e 0).toAdr)

theorem permitRuntimeAllowanceKey_region (e : Sevm) :
    InRegion .allowance (permitRuntimeAllowanceKey e) :=
  runtimeAllowanceKey_region _

/-- The tentative nonce write can never land on a tagged allowance key, so
the two writes below are independent whatever the raw argument words are. -/
theorem permitRuntimeNonceKey_ne_allowance (e : Sevm) {key : B256}
    (hkey : InRegion .allowance key) : permitRuntimeNonceKey e ≠ key := by
  intro h
  exact regions_disjoint (x := .nonce) (y := .allowance) (by decide) key
    (h ▸ permitRuntimeNonceKey_region e) hkey

/-- **Raw selected-body permit effect.**  A committed exact `permit` body
writes the tentative nonce increment at the tagged key of the *normalized*
first argument word, then the third argument word at the tagged hash of the
two *raw* argument words — in that order.  No calldata decoding hypothesis
occurs, so this also covers short and dirty calldata, where the runtime key
and the canonical `allowanceKey owner spender` differ. -/
theorem permit_selected_raw_effect (dp : DeployParams)
    {sevm : Sevm} {s r : Devm} {xs : Stack}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg : getDelegatedCodeAddress (s.getCode 1) = none)
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s (permit dp) r) :
    let nonce :=
      Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm)
    Devm.getStor r sevm.currentTarget =
      ((Devm.getStor s sevm.currentTarget).set
        (permitRuntimeNonceKey sevm) (nonce + 1)).set
          (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2) := by
  dsimp only
  rcases of_permitToRecover_raw dp hp hwf run with
    ⟨mid, domain, structHash, hpMid, hstorMid, hcodeMid, hwfMid, recoverRun⟩
  have hnodelegMid : getDelegatedCodeAddress (mid.getCode 1) = none := by
    rw [congrFun hcodeMid 1]
    exact hnodeleg
  rw [permitRecover_eq] at recoverRun
  rcases of_run_prepend permitDigest _ recoverRun with
    ⟨digestState, digestRun, recoverRun⟩
  rcases of_permitDigest hpMid hwfMid (mem_reads_self mid.memory) digestRun with
    ⟨hpDigest, _, _, hcodeDigest⟩
  have hnodelegDigest :
      getDelegatedCodeAddress (digestState.getCode 1) = none := by
    rw [congrFun hcodeDigest 1]
    exact hnodelegMid
  have hstorDigest : Devm.getStor mid = Devm.getStor digestState :=
    Line.of_inv Devm.getStor (by
      unfold permitDigest pushList
      line_inv) digestRun
  rcases of_run_prepend recoverPermitSigner _ recoverRun with
    ⟨signerState, signerRun, guardsRun⟩
  rcases of_recoverPermitSigner_raw hpre hnodelegDigest hpDigest signerRun with
    ⟨⟨signer, hpSigner⟩, hstorSigner⟩
  rcases of_permitSignerGuards_raw_frame dp hpSigner guardsRun with
    ⟨_, _, approveState, hpApprove, hstorGuards, _, _, _, approveRun⟩
  calc
    Devm.getStor r sevm.currentTarget =
        (Devm.getStor approveState sevm.currentTarget).set
          (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2) :=
      approvePermit_raw_storage hpApprove approveRun
    _ = (Devm.getStor signerState sevm.currentTarget).set
          (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2) := by
        rw [congrFun hstorGuards sevm.currentTarget]
    _ = (Devm.getStor digestState sevm.currentTarget).set
          (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2) := by
        rw [congrFun hstorSigner sevm.currentTarget]
    _ = (Devm.getStor mid sevm.currentTarget).set
          (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2) := by
        rw [congrFun hstorDigest.symm sevm.currentTarget]
    _ = ((Devm.getStor s sevm.currentTarget).set
          (permitRuntimeNonceKey sevm)
            (Devm.getStorVal s sevm.currentTarget
              (permitRuntimeNonceKey sevm) + 1)).set
          (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2) := by
        rw [hstorMid]

/-- **Raw compiled-selector permit effect.**  For a committed exact WETH10
`permit` frame the contract's own storage moves by exactly two writes, in
this order: the tentative nonce increment at the tagged key of the normalized
first argument word, then the raw third argument word at the tagged hash of
the two raw argument words.

The only hypotheses beyond frame authenticity are the two precompile-routing
premises the canonical chain already carries — address 1 resolves to the
ECRECOVER precompile and carries no EIP-7702 delegation designator — plus
memory well-formedness.  There is deliberately no `DecodesPermit` premise:
on short or dirty calldata the runtime key and the canonical
`allowanceKey owner spender` differ, and this theorem names the former. -/
theorem permit_exec_raw_effect (dp : DeployParams)
    {sevm : Sevm} {pre post : Devm}
    (hprecomp : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg : getDelegatedCodeAddress (pre.getCode 1) = none)
    (hwf : Mem.Wf pre.memory)
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : some sevm.code.toList = Prog.compile (weth10 dp))
    (hsel : Sevm.selector sevm = permitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    let nonce :=
      Devm.getStorVal pre sevm.currentTarget (permitRuntimeNonceKey sevm)
    sevm.value = 0 ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor pre sevm.currentTarget).set
          (permitRuntimeNonceKey sevm) (nonce + 1)).set
            (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2) := by
  dsimp only
  rcases exec_enters_weth10Nonpayable_logs exc hcode hsel hnonempty
      (permit_mem_weth10Funcs dp) with
    ⟨mid, hvalue, hstorEntry, _, hcodeEntry, hmemoryEntry, _, _, run⟩
  have hnodelegMid : getDelegatedCodeAddress (mid.getCode 1) = none := by
    rw [congrFun hcodeEntry 1]
    exact hnodeleg
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemoryEntry]
    exact hwf
  have heffect := permit_selected_raw_effect dp hprecomp hnodelegMid
    nil_pref hwfMid run
  dsimp only at heffect
  have hnonce :
      Devm.getStorVal mid sevm.currentTarget (permitRuntimeNonceKey sevm) =
        Devm.getStorVal pre sevm.currentTarget (permitRuntimeNonceKey sevm) := by
    change (Devm.getStor mid sevm.currentTarget).get _ =
      (Devm.getStor pre sevm.currentTarget).get _
    rw [hstorEntry]
  rw [hnonce] at heffect
  exact ⟨hvalue,
    by simpa only [congrFun hstorEntry sevm.currentTarget] using heffect⟩

/-! ## The allowance-region-restricted raw permit effect

The full-map chain above pays for its `STATICCALL` crossing with the two
precompile-routing premises, because only a synchronous precompile child is
known to leave *every* account's storage alone.  The allowance transport
needs far less: it reads the resulting image at allowance-region keys of the
frame's own account only.  The variants below therefore take the crossing as
an assumption *supplied by the caller* — this frame's `STATICCALL` leaves the
current target's allowance region where it found it — which a caller holding
its own recursion hypothesis can discharge for an interpreted child as well
as for a precompile one.  Every key image is unchanged: the two writes still
land at `permitRuntimeNonceKey` and `permitRuntimeAllowanceKey`. -/

/-- The caller-supplied `STATICCALL` crossing assumption: every `STATICCALL`
this frame executes from a state carrying the given code map, on permit's six
ECRECOVER operands, leaves the current target's allowance region unchanged.
The code map is an explicit parameter so that the assumption transports along
the childless prefixes the chain walks through. -/
def PermitStaticcallRegionSilent (sevm : Sevm) (code : Adr → ByteArray) : Prop :=
  ∀ {u v : Devm} {gasWord : B256} {tail : Stack},
    Devm.getCode u = code →
    gasWord :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
      (128 : B256) :: (32 : B256) :: tail <<+ u.stack →
    Ninst.Run sevm u Ninst.staticcall v →
    ∀ key, InRegion .allowance key →
      (Devm.getStor v sevm.currentTarget).get key =
        (Devm.getStor u sevm.currentTarget).get key

/-- Transport the crossing assumption along a code-map equality. -/
theorem PermitStaticcallRegionSilent.mono {sevm : Sevm}
    {code code' : Adr → ByteArray}
    (h : PermitStaticcallRegionSilent sevm code) (heq : code' = code) :
    PermitStaticcallRegionSilent sevm code' := by
  intro u v gasWord tail hcode hstack run
  exact h (hcode.trans heq) hstack run

/-- Allowance-region form of the raw recovery-line frame.  The crossing is
discharged from the caller's assumption, so no precompile-routing premise
occurs; the recovered word stays existential exactly as above. -/
theorem of_recoverPermitSigner_raw_region
    {sevm : Sevm} {s t : Devm} {digest : B256} {xs : Stack}
    (hsilent : PermitStaticcallRegionSilent sevm (Devm.getCode s))
    (hp : digest :: xs <<+ s.stack)
    (run : Line.Run sevm s recoverPermitSigner t) :
    (∃ signer : B256, signer :: xs <<+ t.stack) ∧
      ∀ key, InRegion .allowance key →
        (Devm.getStor t sevm.currentTarget).get key =
          (Devm.getStor s sevm.currentTarget).get key := by
  rw [recoverPermitSigner_eq_prepare] at run
  rcases of_run_append permitRecoverPrepare run with ⟨q, hprep, run⟩
  rcases permitRecoverPrepare_stack hp hprep with ⟨g, hpq⟩
  rcases permitRecoverPrepare_frame hprep with
    ⟨hstorPrep, _, _, hcodePrep⟩
  rcases Line.of_run_cons run with ⟨u, qstat, htail⟩
  have hstorU : ∀ key, InRegion .allowance key →
      (Devm.getStor u sevm.currentTarget).get key =
        (Devm.getStor q sevm.currentTarget).get key :=
    hsilent hcodePrep.symm hpq qstat
  have hpU : ∃ w : B256, w :: xs <<+ u.stack := by
    rcases of_run_staticcall_val_with_depth hpq qstat with hfail | hsuccess
    · exact ⟨0, hfail.1⟩
    · rcases hsuccess with
        ⟨parent, _child, _xl, _dpFlag, _na, _code, _avail,
          _, hstack, _, _, _, _, _, _, _, _, _, _, hstackU⟩
      refine ⟨1, ?_⟩
      rw [hstackU]
      rw [hstack] at hpq
      exact cons_pref_cons rfl (cons_pref_cons_inv (cons_pref_cons_inv
        (cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
          (cons_pref_cons_inv hpq))))))
  rcases hpU with ⟨w, hpU⟩
  rcases Line.of_run_cons htail with ⟨u1, qpop, htail⟩
  rcases of_run_pop qpop with ⟨w1, hpop⟩
  have hp1 : xs <<+ u1.stack := (popBurn_pref hpop hpU).2
  rcases Line.of_run_cons htail with ⟨u2, qpush, htail⟩
  have hp2 : (128 : B256) :: xs <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 qpush) hp1
  rcases Line.of_run_cons htail with ⟨u3, qload, hnil⟩
  cases hnil
  rcases prefix_of_mload qload hp2 with ⟨signer, hp3⟩
  refine ⟨⟨signer, hp3⟩, fun key hkey => ?_⟩
  have hsuffix : Devm.getStor t = Devm.getStor u :=
    calc
      Devm.getStor t = Devm.getStor u2 :=
        (Ninst.Hinv.inv (f := Devm.getStor) qload).symm
      _ = Devm.getStor u1 := (Ninst.Hinv.inv (f := Devm.getStor) qpush).symm
      _ = Devm.getStor u := (PopBurn.Inv.inv hpop).symm
  rw [congrFun hsuffix sevm.currentTarget, hstorU key hkey,
    congrFun hstorPrep.symm sevm.currentTarget]

/-- **Region-restricted raw selected-body permit effect.**  The allowance-key
image of `permit_selected_raw_effect`, with the `STATICCALL` crossing taken
from the caller instead of from the two precompile-routing premises.  The
nonce write is still the tentative increment at `permitRuntimeNonceKey`, and
the allowance write is still the raw third argument word at
`permitRuntimeAllowanceKey`. -/
theorem permit_selected_raw_effect_region (dp : DeployParams)
    {sevm : Sevm} {s r : Devm} {xs : Stack}
    (hsilent : PermitStaticcallRegionSilent sevm (Devm.getCode s))
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s (permit dp) r) :
    let nonce :=
      Devm.getStorVal s sevm.currentTarget (permitRuntimeNonceKey sevm)
    ∀ key, InRegion .allowance key →
      (Devm.getStor r sevm.currentTarget).get key =
        (((Devm.getStor s sevm.currentTarget).set
          (permitRuntimeNonceKey sevm) (nonce + 1)).set
            (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2)).get key := by
  dsimp only
  intro key hkey
  rcases of_permitToRecover_raw dp hp hwf run with
    ⟨mid, domain, structHash, hpMid, hstorMid, hcodeMid, hwfMid, recoverRun⟩
  rw [permitRecover_eq] at recoverRun
  rcases of_run_prepend permitDigest _ recoverRun with
    ⟨digestState, digestRun, recoverRun⟩
  rcases of_permitDigest hpMid hwfMid (mem_reads_self mid.memory) digestRun with
    ⟨hpDigest, _, _, hcodeDigest⟩
  have hstorDigest : Devm.getStor mid = Devm.getStor digestState :=
    Line.of_inv Devm.getStor (by
      unfold permitDigest pushList
      line_inv) digestRun
  rcases of_run_prepend recoverPermitSigner _ recoverRun with
    ⟨signerState, signerRun, guardsRun⟩
  rcases of_recoverPermitSigner_raw_region
      (hsilent.mono (hcodeDigest.trans hcodeMid)) hpDigest signerRun with
    ⟨⟨signer, hpSigner⟩, hstorSigner⟩
  rcases of_permitSignerGuards_raw_frame dp hpSigner guardsRun with
    ⟨_, _, approveState, hpApprove, hstorGuards, _, _, _, approveRun⟩
  calc
    (Devm.getStor r sevm.currentTarget).get key
        = ((Devm.getStor approveState sevm.currentTarget).set
            (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2)).get key := by
          rw [approvePermit_raw_storage hpApprove approveRun]
    _ = ((Devm.getStor signerState sevm.currentTarget).set
          (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2)).get key := by
        rw [congrFun hstorGuards sevm.currentTarget]
    _ = ((Devm.getStor digestState sevm.currentTarget).set
          (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2)).get key := by
        by_cases hcase : permitRuntimeAllowanceKey sevm = key
        · rw [← hcase, Stor.get_set_self, Stor.get_set_self]
        · rw [Stor.get_set_ne _ hcase, Stor.get_set_ne _ hcase,
            hstorSigner key hkey]
    _ = ((Devm.getStor mid sevm.currentTarget).set
          (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2)).get key := by
        rw [congrFun hstorDigest.symm sevm.currentTarget]
    _ = (((Devm.getStor s sevm.currentTarget).set
          (permitRuntimeNonceKey sevm)
            (Devm.getStorVal s sevm.currentTarget
              (permitRuntimeNonceKey sevm) + 1)).set
          (permitRuntimeAllowanceKey sevm) (Sevm.argWord sevm 2)).get key := by
        rw [hstorMid]

/-- **Region-restricted raw compiled-selector permit effect.**  A committed
exact WETH10 `permit` frame moves the contract's own allowance region by
exactly the write at `permitRuntimeAllowanceKey`, whatever its `STATICCALL`
child turns out to be: the crossing is the caller's assumption, and the
tentative nonce write lands in the nonce region, disjoint from every tagged
allowance key.  There is deliberately no `DecodesPermit` premise, exactly as
in the full-map form. -/
theorem permit_exec_raw_effect_region (dp : DeployParams)
    {sevm : Sevm} {pre post : Devm}
    (hsilent : PermitStaticcallRegionSilent sevm (Devm.getCode pre))
    (hwf : Mem.Wf pre.memory)
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : some sevm.code.toList = Prog.compile (weth10 dp))
    (hsel : Sevm.selector sevm = permitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    let nonce :=
      Devm.getStorVal pre sevm.currentTarget (permitRuntimeNonceKey sevm)
    sevm.value = 0 ∧
      ∀ key, InRegion .allowance key →
        (Devm.getStor post sevm.currentTarget).get key =
          (((Devm.getStor pre sevm.currentTarget).set
            (permitRuntimeNonceKey sevm) (nonce + 1)).set
              (permitRuntimeAllowanceKey sevm)
                (Sevm.argWord sevm 2)).get key := by
  dsimp only
  rcases exec_enters_weth10Nonpayable_logs exc hcode hsel hnonempty
      (permit_mem_weth10Funcs dp) with
    ⟨mid, hvalue, hstorEntry, _, hcodeEntry, hmemoryEntry, _, _, run⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemoryEntry]
    exact hwf
  have heffect := permit_selected_raw_effect_region dp (hsilent.mono hcodeEntry)
    nil_pref hwfMid run
  dsimp only at heffect
  have hnonce :
      Devm.getStorVal mid sevm.currentTarget (permitRuntimeNonceKey sevm) =
        Devm.getStorVal pre sevm.currentTarget (permitRuntimeNonceKey sevm) := by
    change (Devm.getStor mid sevm.currentTarget).get _ =
      (Devm.getStor pre sevm.currentTarget).get _
    rw [hstorEntry]
  rw [hnonce] at heffect
  refine ⟨hvalue, fun key hkey => ?_⟩
  simpa only [congrFun hstorEntry sevm.currentTarget] using heffect key hkey

end Weth10

end Blanc
