import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Fork
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Outer

/-!
V- as an admitted transaction under every covered fork: the outer transaction frame.

The tx-level dispatcher attacker `A'` (`Attacker2`), entered from the real transaction-shaped
message `msgC.withFork g` (`TxTopC`: `prepareMessage` under real EIP-2929 pre-warming, EOA `E` ->
`A'`, the same warmed addresses under every covered fork), runs its own certificate to its `CALL`
into the pool proxy `P`, spawns `P`'s frame, and -- **given** that child frame settles (the deep
reentrancy chain) with its observed gas, return data, success and world -- `A'` resumes, drops
the success flag and `STOP`s.  The whole outer frame is then an `Exec` of `A'`'s real bytes
(`lift_exact` over the registered `Attacker2` certificate), and Jaune's `processMessage`
returns that settled machine, whose world is the child's.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun Blanc.ForkUniform Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

attribute [local irreducible] callCfgC cp0C e0C

variable {g : Fork}

/-- **The outer transaction frame of the V- tx witness, given its child, under any covered
fork.**  `A'`'s frame -- entered from the real transaction-shaped message -- with `P`'s frame
supplied as the settled child `d1` of its `CALL` (`ChildOk` at `callCfgC`; its gas, return data
and success from the tx trace; its world shadows `ChildAgree`), is an `Exec` of `A'`'s real
bytes, Jaune's `processMessage` returns its settled machine, and that machine's storage is the
child's (`cs`) -- so any corruption the child leaves in `P`'s storage is the corruption of the
whole transaction message. -/
theorem txC_message_of_child_at (hg : CoveredFork g) (d1 : Devm)
    (ck : List (Adr × B256)) (ca : List Adr) (cs : StorShadow) (cc : AcctShadow)
    (hgas : d1.gasLeft = childGasC) (ho : d1.output = childOut) (he : d1.error = none)
    (hr : d1.refundCounter = refund0) (hd : d1.accountsToDelete = .emptyWithCapacity)
    (hok : ChildOk (e0C.withFork g).sta callCfgC d1) (ha : ChildAgree d1 ck ca cs cc) :
    ∃ post, Nonempty (Exec (e0C.withFork g).pc (e0C.withFork g).sta (e0C.withFork g).dyna
        (.ok post)) ∧
      processMessage (msgC.withFork g) = .ok post ∧ post.error = none ∧
      post.gasLeft = gas0outC ∧ post.output = [] ∧ post.refundCounter = refund0 ∧
      post.accountsToDelete = .emptyWithCapacity ∧
      (∀ a k, storOf post.state a k = lookupS cs a k) := by
  have hk := frame0txC_kernel d1 ck ca cs cc
  rw [childObsX_eq hgas ho he hr hd] at hk
  have hf0 : CoveredFork e0C.sta.benvStat.fork := by rw [e0C_block.1]; exact CoveredFork.prague
  unfold run0C at hk
  split at hk
  · rename_i c hc
    have hcg : callResume (e0C.withFork g).sta callCfgC d1 ck ca cs cc = some c :=
      (callResume_withFork hf0 hg _ _ _ _ _ _).trans hc
    have s : StepOk fs2 (e0C.withFork g).sta c0C c :=
      (wrun_cont (callCfgC_at hg)).trans (callResume_cont hcg hok ha)
    generalize hr' : wrun fs2 e0C.sta 2 c = r at hk
    have hrg : wrun fs2 (e0C.withFork g).sta 2 c = r :=
      (wrun_withFork hf0 hg e0C_block.2 fs2 2 c).trans hr'
    rcases r with c' | ⟨post | post, cl⟩ | _
    · simp [obs0C] at hk
    · simp only [obs0C, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at hk
      obtain ⟨hgas0, hout, ⟨herr, hrf⟩, hstor, hatd⟩ := hk
      obtain ⟨run, hagcl, hstate⟩ := wrun_done hrg (s.1 c0C_agree)
      have hrunexact : SProg.RunExact fs2 (e0C.withFork g).sta e0C.dyna post :=
        ⟨Attacker2.t_0000_c0, fs2_zero, s.2 _ c0C_agree run⟩
      have hexec : Nonempty (Exec 0 (e0C.withFork g).sta e0C.dyna (.ok post)) :=
        lift_exact Attacker2.cert_check Attacker2.cert_jumpsOk e0txC_code (hg : CoveredFork g)
          hrunexact
      have hexec' : Nonempty (Exec (e0C.withFork g).pc (e0C.withFork g).sta
          (e0C.withFork g).dyna (.ok post)) := by
        show Nonempty (Exec e0C.pc _ _ _)
        rw [e0txC_pc]; exact hexec
      have hpost_state : post.state = cl.devm.state := hstate post rfl
      have hstoreq : ∀ a k, storOf post.state a k = lookupS cs a k := by
        intro a k
        rw [hpost_state, hagcl.2.2.1 a k, hstor]
      have herr' : post.error = none := Option.isNone_iff_eq_none.mp herr
      refine ⟨post, hexec', ?_, herr', hgas0,
        List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hout, hrf, hatd, hstoreq⟩
      -- processMessage settlement
      have hsg0 : (f0C.withFork g).inner.benv.stat.rules.stateGas = none :=
        CoveredFork.rules_stateGas_none (s := (f0C.withFork g).inner.benv.stat) hg
      have hex := (exec_iff_exec_eq _ _ _ _).mp hexec'
      show runFrame (f0C.withFork g) = _
      unfold runFrame
      rw [f0C_enter_at hg]
      show (f0C.withFork g).settle (exec ⟨(e0C.withFork g).pc, (e0C.withFork g).sta,
        (e0C.withFork g).dyna⟩) = _
      rw [hex]
      exact frame_settle_ok rfl hsg0 herr'
    · simp [obs0C] at hk
    · simp [obs0C] at hk
  · simp [obs0C] at hk

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
