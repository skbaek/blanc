import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-!
V- as an admitted transaction (O10, best effort), the outer transaction frame.

The tx-level dispatcher attacker `A'` (`Attacker2`), entered from the real transaction-shaped
message `msg0tx` (`TxTop`: `prepareMessage` under real EIP-2929 pre-warming, EOA `E` -> `A'`),
runs its own certificate to its `CALL` into the pool proxy `P`
(`TxTop.callCfg`/`TxTop.cp0`), spawns `P`'s frame, and -- **given** that child frame settles
(the deep reentrancy chain, EELS frames 1-6 of the tx trace: `A' -> P -> impl remove -> A'
callback -> P -> impl add reentry`) with its observed gas, return data, success and world --
`A'` resumes, drops the success flag and `STOP`s.  The whole outer frame is then an `Exec` of
`A'`'s real bytes (`lift_exact` over the registered `Attacker2` certificate), and Jaune's
`processMessage msg0tx` returns that settled machine, whose world is the child's.

This is the transaction-entry analog of `Vulnerable.Top.frame0_of_child`: there the top
frame was the proxy `P` (raw bytes, `stepN`); here it is the lifted dispatcher `A'` (its
certificate, `wrun`), and the top-level settlement is Jaune's `processMessage`.  The child --
`P`'s frame at `A'`'s `CALL` -- is taken as a hypothesis (`ChildOk`/`ChildAgree` at
`TxTop.callCfg`), exactly as `Frame2.attacker_of_child` takes the proxy child; producing that
child is the remaining deep-chain regeneration (Plans `state/vminus-tx-v1.md`).

Kernel-only boundary facts (`kernel_forall_rfl`); do not open this file in the language server
alongside the deep chain.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-- `d` with its refund counter and its set of accounts to delete replaced by a literal and the
empty set: a settled child's other observed parts (its refund counter and that it deletes
nothing) as literals, so that a parent's run over it evaluates them. -/
def pinRA (r : Int) (d : Devm) : Devm :=
  ⟨d.mach, { d.meta with refundCounter := r, accountsToDelete := .emptyWithCapacity }, d.world⟩

theorem pinRA_eq {d : Devm} {r : Int} (hr : d.refundCounter = r)
    (ha : d.accountsToDelete = .emptyWithCapacity) : pinRA r d = d := by
  rcases d with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _, _⟩, _⟩
  simp only [Devm.refundCounter, Devm.accountsToDelete] at hr ha
  subst hr ha
  rfl

/-- A settled child with its gas, output, success, refund counter and (empty) accounts to delete
as literals. -/
def childObsX (g : Nat) (out : Bytes) (r : Int) (d : Devm) : Devm := pinRA r (childObs g out d)

theorem childObsX_eq {d : Devm} {g : Nat} {out : Bytes} {r : Int} (hg : d.gasLeft = g)
    (ho : d.output = out) (he : d.error = none) (hr : d.refundCounter = r)
    (ha : d.accountsToDelete = .emptyWithCapacity) : childObsX g out r d = d := by
  unfold childObsX
  rw [pinRA_eq (d := childObs g out d) hr ha]
  exact childObs_eq hg ho he

/-- The refund counters of the chain's frames, by evaluation of the interpreter over the real
chain (each frame's observation decides its own): frame 5 (the reentrant `add_liquidity`)
22,700, frames 4 (the proxy) and 3 (`A'`'s callback) inherit it, frame 2 (`remove_liquidity`)
adds its own lock release to make 42,600, which frames 1 and 0 inherit. -/
def refund5 : Int := 22700
def refund4 : Int := 22700
def refund3 : Int := 22700
def refund2 : Int := 42600

/-- The refund counter of `P`'s frame (and so of `A'`'s, whose own code refunds nothing):
42,600 (the remove-lock's release and the reentrant frames' refunds, by evaluation of the
interpreter over the real chain; the observations of every frame decide it). -/
def refund0 : Int := refund2

/-- Frame 1's (the proxy's) refund counter: its child's. -/
def refund1 : Int := refund2

/-- The EELS gas at `A'`'s `STOP` (tx trace, frame 0): 29,846,301. -/
def gas0out : Nat := 29846301

/-- `P`'s frame's return data as `A'`'s child sees it (tx trace, frame 1): the removed
amounts `[100, 100]`.  `A'`'s `CALL` uses `retLen = 0`, so this is never read; it is pinned
here only to match the trace. -/
def childOut : Bytes := word 100 ++ word 100

/-- The gas `A'`'s child frame (`P` running `remove_liquidity`) returns with (tx trace,
frame 1): 29,377,596. -/
def childGas : Nat := 29377596

/-- `A'`'s frame after its `CALL` to `P`, from a settled child `d1` and the child's shadows:
resume the `CALL` (dropping its output, `retLen = 0`), then `POP`; `STOP` (two nodes). -/
def run0 (d1 : Devm) (ck : List (Adr × B256)) (ca : List Adr)
    (cs : StorShadow) (cc : AcctShadow) : Res :=
  match callResume e0tx.sta callCfg d1 ck ca cs cc with
  | some c => wrun fs2 e0tx.sta 2 c
  | none => .stuck

/-- `A'`'s halt: gas, return data (empty), success, and the halting configuration's storage
shadow (which is the child's, since `POP`; `STOP` change no storage).  Reading `P`'s
`totalSupply` (slot 26) and the attacker's LP balance from that shadow is what carries the
corruption up from the child. -/
def obs0 : Res → Option (Nat × List Nat × Bool × StorShadow × AdrSet)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat,
      d.error.isNone && decide (d.refundCounter = refund0), cl.stor, d.accountsToDelete)
  | _ => none

/-- **`A'`'s outer frame halts, for any settled child** with the tx trace's gas and return
data (all its other parts free): `A'` drops the success flag and `STOP`s with its own gas and
empty output, no error, leaving the child's storage shadow `cs` untouched. -/
theorem frame0tx_kernel : ∀ (d1 : Devm) (ck : List (Adr × B256)) (ca : List Adr)
    (cs : StorShadow) (cc : AcctShadow),
    obs0 (run0 (childObsX childGas childOut refund0 d1) ck ca cs cc) =
      some (gas0out, [], true, cs, .emptyWithCapacity) := by
  kernel_forall_rfl

theorem fs2_zero : fs2[0]? = some Attacker2.t_0000_c0 := by kernel_rfl

theorem e0tx_code : e0tx.sta.code = Attacker2.code := by
  have h := e0tx_facts; simp only [Prod.mk.injEq] at h; exact h.2.1

theorem e0tx_pc : e0tx.pc = 0 := by
  have h := e0tx_facts; simp only [Prod.mk.injEq] at h; exact h.1

theorem e0tx_fork : CoveredFork e0tx.sta.benvStat.fork := by
  have h := e0tx_facts; simp only [Prod.mk.injEq] at h; rw [h.2.2.2]; exact CoveredFork.prague

/-- **The outer transaction frame of the V- tx witness, given its child.**

`A'`'s frame -- entered from the real transaction-shaped message `msg0tx` (`TxTop`) -- with
`P`'s frame supplied as the settled child `d1` of its `CALL` (`ChildOk` at `TxTop.callCfg`;
its gas, return data and success from the tx trace; its world shadows `ChildAgree`), is an
`Exec` of `A'`'s real bytes, Jaune's `processMessage msg0tx` returns its settled machine, and
that machine's storage is the child's (`cs`) -- so any corruption the child leaves in `P`'s
storage is the corruption of the whole transaction message. -/
theorem tx_message_of_child (d1 : Devm)
    (ck : List (Adr × B256)) (ca : List Adr) (cs : StorShadow) (cc : AcctShadow)
    (hg : d1.gasLeft = childGas) (ho : d1.output = childOut) (he : d1.error = none)
    (hr : d1.refundCounter = refund0) (hd : d1.accountsToDelete = .emptyWithCapacity)
    (hok : ChildOk e0tx.sta callCfg d1) (ha : ChildAgree d1 ck ca cs cc) :
    ∃ post, Nonempty (Exec e0tx.pc e0tx.sta e0tx.dyna (.ok post)) ∧
      processMessage msg0tx = .ok post ∧ post.error = none ∧
      post.gasLeft = gas0out ∧ post.output = [] ∧ post.refundCounter = refund0 ∧
      post.accountsToDelete = .emptyWithCapacity ∧
      (∀ a k, storOf post.state a k = lookupS cs a k) := by
  have hk := frame0tx_kernel d1 ck ca cs cc
  rw [childObsX_eq hg ho he hr hd] at hk
  unfold run0 at hk
  split at hk
  · rename_i c hc
    have s : StepOk fs2 e0tx.sta c0tx c :=
      (wrun_cont callCfg_eq).trans (callResume_cont hc hok ha)
    generalize hr : wrun fs2 e0tx.sta 2 c = r at hk
    rcases r with c' | ⟨post | post, cl⟩ | _
    · simp [obs0] at hk
    · simp only [obs0, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at hk
      obtain ⟨hgas, hout, ⟨herr, hrf⟩, hstor, hatd⟩ := hk
      obtain ⟨run, hagcl, hstate⟩ := wrun_done hr (s.1 c0tx_agree)
      have hrunexact : SProg.RunExact fs2 e0tx.sta e0tx.dyna post :=
        ⟨Attacker2.t_0000_c0, fs2_zero, s.2 _ c0tx_agree run⟩
      have hexec : Nonempty (Exec 0 e0tx.sta e0tx.dyna (.ok post)) :=
        lift_exact Attacker2.cert_check Attacker2.cert_jumpsOk e0tx_code e0tx_fork hrunexact
      have hexec' : Nonempty (Exec e0tx.pc e0tx.sta e0tx.dyna (.ok post)) := by
        rw [e0tx_pc]; exact hexec
      have hpost_state : post.state = cl.devm.state := hstate post rfl
      have hstoreq : ∀ a k, storOf post.state a k = lookupS cs a k := by
        intro a k
        rw [hpost_state, hagcl.2.2.1 a k, hstor]
      have herr' : post.error = none := Option.isNone_iff_eq_none.mp herr
      refine ⟨post, hexec', ?_, herr', hgas,
        List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hout, hrf, hatd, hstoreq⟩
      -- processMessage settlement
      have hsg0 : f0tx.inner.benv.stat.rules.stateGas = none := by
        show msg0tx.benv.stat.rules.stateGas = none
        exact (CoveredFork.prague).rules_stateGas_none
      have hex := (exec_iff_exec_eq _ _ _ _).mp hexec'
      show runFrame f0tx = _
      unfold runFrame
      rw [f0tx_enter]
      show f0tx.settle (exec ⟨e0tx.pc, e0tx.sta, e0tx.dyna⟩) = _
      rw [hex]
      exact frame_settle_ok rfl hsg0 herr'
    · simp [obs0] at hk
    · simp [obs0] at hk
  · simp [obs0] at hk

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
