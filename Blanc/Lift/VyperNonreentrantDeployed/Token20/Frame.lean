import Blanc.Lift.VyperNonreentrantDeployed.Token20.Run
import Blanc.Lift.ExactLeaf

/-!
# The synthetic token `T` as a node-walk child of a pool frame

The forms of `Run.lean` a pool witness consumes at a `CALL` or `STATICCALL` into `T`
(`spawn_resume_ok`, `Blanc/Lift/NodeWalkFrames.lean`).  Each `*_child` theorem takes the child's
start configuration `c` (pc 0, empty stack and memory) with its agreeing shadows (`PAgree c`, as
`call_node`/`staticcall_node` hand it over), the selector, and premises read from the shadows
only, and gives, under any covered fork:

* the shadows of the machine the child returns (`ChildAgree`): the accessed keys, and the
  storage shadow with exactly the token's writes prepended — nothing else moves;
* for every derivation node at `c`: the successful outcome, an explicit machine evaluated over
  the shadows (`*PostS`; no hash set is inspected), and no raw frame descendant (the code spawns
  nothing, `spawnFreeReach`).

Gas is exact: the frame's gas is `G + *GasS`, the post's gas left `G`.  Every executed instruction
is one of `PUSH*`, `DUP*`, `SWAP*`, `POP`, `CALLDATALOAD`, `SHR`, `EQ`, `LT`, `GT`, `ADD`, `SUB`,
`AND`, `CALLER`, `MSTORE`, `KECCAK256`, `SLOAD`, `SSTORE`, `JUMP`, `JUMPI`, `JUMPDEST`, `RETURN`:
all fork-neutral, and the theorems hold for every `CoveredFork` directly.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk

/-! ## The move, on the shadows -/

section MoveS

variable (sevm : Sevm) (keys : List (Adr × B256)) (stor : StorShadow) (src dst : Adr) (v : B256)

/-- `balanceOf[src]` on the storage shadow. -/
def mvFromS : B256 := lookupS stor sevm.currentTarget (balSlot src)
/-- The storage shadow after the debit. -/
def mvStor1 : StorShadow := ((sevm.currentTarget, balSlot src), mvFromS sevm stor src - v) :: stor
/-- `balanceOf[dst]` after the debit, on the shadow. -/
def mvToS : B256 := lookupS (mvStor1 sevm stor src v) sevm.currentTarget (balSlot dst)
/-- The storage shadow after the move: the debit, then the credit. -/
def mvStorS : StorShadow :=
  ((sevm.currentTarget, balSlot dst), v + mvToS sevm stor src dst v) :: mvStor1 sevm stor src v
/-- The key shadow after the move. -/
def mvKeysS : List (Adr × B256) :=
  (sevm.currentTarget, balSlot dst) :: (sevm.currentTarget, balSlot dst) ::
    (sevm.currentTarget, balSlot src) :: (sevm.currentTarget, balSlot src) :: keys
/-- The move's four storage charges, on the shadows. -/
def mvCostS : Nat :=
  sstoreCostS sevm ((sevm.currentTarget, balSlot dst) :: (sevm.currentTarget, balSlot src) ::
      (sevm.currentTarget, balSlot src) :: keys) (mvStor1 sevm stor src v) (balSlot dst)
      (v + mvToS sevm stor src dst v) +
    sloadCostS sevm.currentTarget ((sevm.currentTarget, balSlot src) ::
      (sevm.currentTarget, balSlot src) :: keys) (balSlot dst) +
    sstoreCostS sevm ((sevm.currentTarget, balSlot src) :: keys) stor (balSlot src)
      (mvFromS sevm stor src - v) +
    sloadCostS sevm.currentTarget keys (balSlot src)

/-- The move's base, on the shadows. -/
def mv4S (b : Devm) : Devm :=
  afterSstoreS sevm ((sevm.currentTarget, balSlot dst) :: (sevm.currentTarget, balSlot src) ::
      (sevm.currentTarget, balSlot src) :: keys) (mvStor1 sevm stor src v)
    (afterSloadS sevm.currentTarget ((sevm.currentTarget, balSlot src) ::
        (sevm.currentTarget, balSlot src) :: keys)
      (afterSstoreS sevm ((sevm.currentTarget, balSlot src) :: keys) stor
        (afterSloadS sevm.currentTarget keys b (balSlot src)) (balSlot src)
        (mvFromS sevm stor src - v)) (balSlot dst))
    (balSlot dst) (v + mvToS sevm stor src dst v)

end MoveS

/-- **The move, read from the shadows**: the values it compares, its charges and its base are
the shadow forms, and the shadows after it describe its base. -/
theorem mv_shadow {sevm : Sevm} {b : Devm} {keys : List (Adr × B256)} {adrs : List Adr}
    {stor : StorShadow} {acs : AcctShadow} (h : ChildAgree b keys adrs stor acs)
    (src dst : Adr) (v : B256) :
    mvFrom sevm b src = mvFromS sevm stor src ∧
      mvTo sevm b src dst v = mvToS sevm stor src dst v ∧
      mvCost sevm b src dst v = mvCostS sevm keys stor src dst v ∧
      mv4 sevm b src dst v = mv4S sevm keys stor src dst v b ∧
      ChildAgree (mv4 sevm b src dst v) (mvKeysS sevm keys src dst) adrs
        (mvStorS sevm stor src dst v) acs := by
  have e1 : mvFrom sevm b src = mvFromS sevm stor src := ChildAgree.getStorVal h _ _
  have h1 := ChildAgree.afterSload h (sevm := sevm) (balSlot src)
  have h2 := ChildAgree.afterSstore h1 (sevm := sevm) (balSlot src) (mvFrom sevm b src - v)
  have e2 : mvTo sevm b src dst v = mvToS sevm stor src dst v := by
    unfold mvTo mv2 mv1; rw [ChildAgree.getStorVal h2]; unfold mvToS mvStor1; rw [e1]
  have h3 := ChildAgree.afterSload h2 (sevm := sevm) (balSlot dst)
  have h4 := ChildAgree.afterSstore h3 (sevm := sevm) (balSlot dst) (v + mvTo sevm b src dst v)
  refine ⟨e1, e2, ?_, ?_, ?_⟩
  · unfold mvCost mvCostS mv3 mv2 mv1
    rw [sstoreCost_shadow h3, sloadCost_shadow h2, sstoreCost_shadow h1, sloadCost_shadow h, e2, e1]
    rfl
  · unfold mv4 mv3 mv2 mv1 mv4S
    rw [afterSstore_shadow h3, afterSload_shadow h2, afterSstore_shadow h1, afterSload_shadow h,
      e2, e1]
    rfl
  · have hs : (((sevm.currentTarget, balSlot dst), v + mvTo sevm b src dst v) ::
        ((sevm.currentTarget, balSlot src), mvFrom sevm b src - v) :: stor) =
        mvStorS sevm stor src dst v := by
      rw [e1, e2]; rfl
    exact hs ▸ h4

/-! ## `transfer` -/

/-- What `transfer` costs, on the shadows. -/
def transferGasS (sevm : Sevm) (keys : List (Adr × B256)) (stor : StorShadow) : Nat :=
  173 + mvCostS sevm keys stor sevm.caller (trTo sevm) (trVal sevm)

/-- The machine a successful `transfer` halts with, on the shadows. -/
def transferPostS (sevm : Sevm) (c : PCfg) (G : Nat) : Devm :=
  retPost (mv4S sevm c.keys c.stor sevm.caller (trTo sevm) (trVal sevm) c.devm)
    [trVal sevm, (trTo sevm).toB256, sevm.caller.toB256, Sevm.selector sevm]
    (okMem Mem.empty) G 1

/-- **`transfer(to, v)` from a pool frame.**  The caller's balance on the shadow covers `v`, and
the credit does not wrap.  The child returns the word `1` with `balanceOf[caller] -= v`, then
`balanceOf[to] += v` prepended to the storage shadow, and nothing else. -/
theorem transfer_child {sevm : Sevm} {c : PCfg} {G : Nat} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsel : Sevm.selector sevm = 0xa9059cbb) (hpc : c.pc = 0) (hstack : c.devm.stack = [])
    (hmem : c.devm.memory = Mem.empty) (hag : PAgree c)
    (hgas : c.devm.gasLeft = G + transferGasS sevm c.keys c.stor) (hsent : gCallStipend < G)
    (hle : trVal sevm ≤ mvFromS sevm c.stor sevm.caller)
    (hnof : trVal sevm ≤ trVal sevm + mvToS sevm c.stor sevm.caller (trTo sevm) (trVal sevm)) :
    ChildAgree (transferPostS sevm c G) (mvKeysS sevm c.keys sevm.caller (trTo sevm)) c.adrs
        (mvStorS sevm c.stor sevm.caller (trTo sevm) (trVal sevm)) c.acs ∧
      ∀ x, NodeAt sevm c x → x.exn = .ok (transferPostS sevm c G) ∧
        Exec.rawFrameDescendants x.exc = [] := by
  obtain ⟨e1, e2, e3, e4, hca⟩ :=
    mv_shadow (sevm := sevm) (childAgree_of_pagree hag) sevm.caller (trTo sevm) (trVal sevm)
  have hpost : transferPost sevm c.devm G = transferPostS sevm c G := by
    unfold transferPost transferBase transferPostS; rw [e4]
  have hrun := transfer_runExact (G := G) hfork hstatic hsel hstack hmem
    (by rw [hgas]; unfold transferGas transferGasS; rw [e3]) hsent (by rw [e1]; exact hle)
    (by rw [e2]; exact hnof)
  rw [hpost] at hrun
  refine ⟨?_, exact_leaf cert_check cert_jumpsOk spawnFreeReach hcode hfork hpc hrun⟩
  rw [← hpost]
  exact ChildAgree.ret hca _ _ _ _ _ _

/-! ## `transferFrom` -/

section TfS

variable (sevm : Sevm) (keys : List (Adr × B256)) (stor : StorShadow)

/-- The allowance slot `transferFrom` spends. -/
abbrev tfSlot : B256 := allowSlot (tfFrom sevm) sevm.caller
/-- `allowance[from][caller]` on the storage shadow. -/
def tfAllowS : B256 := lookupS stor sevm.currentTarget (tfSlot sevm)
/-- The key shadow after the allowance write. -/
def tfKeys2 : List (Adr × B256) :=
  (sevm.currentTarget, tfSlot sevm) :: (sevm.currentTarget, tfSlot sevm) :: keys
/-- The storage shadow after the allowance write. -/
def tfStor2 : StorShadow :=
  ((sevm.currentTarget, tfSlot sevm), tfAllowS sevm stor - tfVal sevm) :: stor
/-- The base after the allowance write, on the shadows. -/
def tf2S (b : Devm) : Devm :=
  afterSstoreS sevm ((sevm.currentTarget, tfSlot sevm) :: keys) stor
    (afterSloadS sevm.currentTarget keys b (tfSlot sevm)) (tfSlot sevm)
    (tfAllowS sevm stor - tfVal sevm)

/-- What `transferFrom` costs, on the shadows. -/
def transferFromGasS : Nat :=
  318 + mvCostS sevm (tfKeys2 sevm keys) (tfStor2 sevm stor) (tfFrom sevm) (tfTo sevm) (tfVal sevm) +
    sstoreCostS sevm ((sevm.currentTarget, tfSlot sevm) :: keys) stor (tfSlot sevm)
      (tfAllowS sevm stor - tfVal sevm) +
    sloadCostS sevm.currentTarget keys (tfSlot sevm)

end TfS

theorem tf_shadow {sevm : Sevm} {b : Devm} {keys : List (Adr × B256)} {adrs : List Adr}
    {stor : StorShadow} {acs : AcctShadow} (h : ChildAgree b keys adrs stor acs) :
    tfAllow sevm b = tfAllowS sevm stor ∧ tf2 sevm b = tf2S sevm keys stor b ∧
      sstoreCost sevm (tf1 sevm b) (tfSlot sevm) (tfAllow sevm b - tfVal sevm) +
          sloadCost sevm b (tfSlot sevm) =
        sstoreCostS sevm ((sevm.currentTarget, tfSlot sevm) :: keys) stor (tfSlot sevm)
          (tfAllowS sevm stor - tfVal sevm) + sloadCostS sevm.currentTarget keys (tfSlot sevm) ∧
      ChildAgree (tf2 sevm b) (tfKeys2 sevm keys) adrs (tfStor2 sevm stor) acs := by
  have e1 : tfAllow sevm b = tfAllowS sevm stor := ChildAgree.getStorVal h _ _
  have h1 := ChildAgree.afterSload h (sevm := sevm) (tfSlot sevm)
  have h2 := ChildAgree.afterSstore h1 (sevm := sevm) (tfSlot sevm) (tfAllow sevm b - tfVal sevm)
  refine ⟨e1, ?_, ?_, ?_⟩
  · unfold tf2 tf1 tf2S
    rw [afterSstore_shadow h1, afterSload_shadow h, e1]
  · unfold tf1
    rw [sstoreCost_shadow h1, sloadCost_shadow h, e1]
  · rw [show tfStor2 sevm stor = ((sevm.currentTarget, tfSlot sevm), tfAllow sevm b - tfVal sevm) ::
      stor by rw [e1]; rfl]
    exact h2

/-- The machine a successful `transferFrom` halts with, on the shadows. -/
def transferFromPostS (sevm : Sevm) (c : PCfg) (G : Nat) : Devm :=
  retPost (mv4S sevm (tfKeys2 sevm c.keys) (tfStor2 sevm c.stor) (tfFrom sevm) (tfTo sevm) (tfVal sevm)
      (tf2S sevm c.keys c.stor c.devm))
    [tfVal sevm, (tfTo sevm).toB256, (tfFrom sevm).toB256, Sevm.selector sevm]
    (okMem (scratch (tfFrom sevm).toB256 sevm.caller.toB256)) G 1

/-- **`transferFrom(from, to, v)` from a pool frame.**  The caller's allowance from `from` covers
`v`, `from`'s balance after the allowance write covers `v`, and the credit does not wrap.  The
child returns the word `1` with `allowance[from][caller] -= v`, `balanceOf[from] -= v`,
`balanceOf[to] += v` prepended to the storage shadow, and nothing else. -/
theorem transferFrom_child {sevm : Sevm} {c : PCfg} {G : Nat} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsel : Sevm.selector sevm = 0x23b872dd) (hpc : c.pc = 0) (hstack : c.devm.stack = [])
    (hmem : c.devm.memory = Mem.empty) (hag : PAgree c)
    (hgas : c.devm.gasLeft = G + transferFromGasS sevm c.keys c.stor) (hsent : gCallStipend < G)
    (hal : tfVal sevm ≤ tfAllowS sevm c.stor)
    (hle : tfVal sevm ≤ mvFromS sevm (tfStor2 sevm c.stor) (tfFrom sevm))
    (hnof : tfVal sevm ≤ tfVal sevm +
      mvToS sevm (tfStor2 sevm c.stor) (tfFrom sevm) (tfTo sevm) (tfVal sevm)) :
    ChildAgree (transferFromPostS sevm c G)
        (mvKeysS sevm (tfKeys2 sevm c.keys) (tfFrom sevm) (tfTo sevm)) c.adrs
        (mvStorS sevm (tfStor2 sevm c.stor) (tfFrom sevm) (tfTo sevm) (tfVal sevm)) c.acs ∧
      ∀ x, NodeAt sevm c x → x.exn = .ok (transferFromPostS sevm c G) ∧
        Exec.rawFrameDescendants x.exc = [] := by
  obtain ⟨a1, a2, a3, h2⟩ := tf_shadow (sevm := sevm) (childAgree_of_pagree hag)
  obtain ⟨e1, e2, e3, e4, hca⟩ := mv_shadow (sevm := sevm) h2 (tfFrom sevm) (tfTo sevm) (tfVal sevm)
  have hpost : transferFromPost sevm c.devm G = transferFromPostS sevm c G := by
    unfold transferFromPost transferFromBase transferFromPostS; rw [e4, a2]
  have hrun := transferFrom_runExact (G := G) hfork hstatic hsel hstack hmem
    (by rw [hgas]; unfold transferFromGas transferFromGasS; rw [e3]; simp only [tfSlot] at a3 ⊢; omega) hsent
    (by rw [a1]; exact hal) (by rw [e1]; exact hle) (by rw [e2]; exact hnof)
  rw [hpost] at hrun
  refine ⟨?_, exact_leaf cert_check cert_jumpsOk spawnFreeReach hcode hfork hpc hrun⟩
  rw [← hpost]
  exact ChildAgree.ret hca _ _ _ _ _ _

/-! ## `approve` -/

/-- The allowance slot `approve` writes. -/
abbrev apSlot (sevm : Sevm) : B256 := allowSlot sevm.caller (apSpender sevm)

/-- What `approve` costs, on the shadows. -/
def approveGasS (sevm : Sevm) (keys : List (Adr × B256)) (stor : StorShadow) : Nat :=
  203 + sstoreCostS sevm keys stor (apSlot sevm) (apVal sevm)

/-- The machine a successful `approve` halts with, on the shadows. -/
def approvePostS (sevm : Sevm) (c : PCfg) (G : Nat) : Devm :=
  retPost (afterSstoreS sevm c.keys c.stor c.devm (apSlot sevm) (apVal sevm)) [Sevm.selector sevm]
    (okMem (scratch sevm.caller.toB256 (apSpender sevm).toB256)) G 1

/-- **`approve(spender, v)` from a frame** (the token owner's root call in a setup).  The child
returns the word `1` with `allowance[caller][spender] := v` prepended to the storage shadow. -/
theorem approve_child {sevm : Sevm} {c : PCfg} {G : Nat} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsel : Sevm.selector sevm = 0x095ea7b3) (hpc : c.pc = 0) (hstack : c.devm.stack = [])
    (hmem : c.devm.memory = Mem.empty) (hag : PAgree c)
    (hgas : c.devm.gasLeft = G + approveGasS sevm c.keys c.stor) (hsent : gCallStipend < G) :
    ChildAgree (approvePostS sevm c G) ((sevm.currentTarget, apSlot sevm) :: c.keys) c.adrs
        (((sevm.currentTarget, apSlot sevm), apVal sevm) :: c.stor) c.acs ∧
      ∀ x, NodeAt sevm c x → x.exn = .ok (approvePostS sevm c G) ∧
        Exec.rawFrameDescendants x.exc = [] := by
  have h := childAgree_of_pagree hag
  have hpost : approvePost sevm c.devm G = approvePostS sevm c G := by
    unfold approvePost approveBase approvePostS; rw [afterSstore_shadow h]
  have hrun := approve_runExact (G := G) hfork hstatic hsel hstack hmem
    (by rw [hgas]; unfold approveGas approveGasS; rw [sstoreCost_shadow h]) hsent
  rw [hpost] at hrun
  refine ⟨?_, exact_leaf cert_check cert_jumpsOk spawnFreeReach hcode hfork hpc hrun⟩
  rw [← hpost]
  exact ChildAgree.ret (ChildAgree.afterSstore (sevm := sevm) h (apSlot sevm) (apVal sevm)) _ _ _ _ _ _

/-! ## `balanceOf` -/

/-- The balance slot `balanceOf` reads. -/
abbrev boSlot (sevm : Sevm) : B256 := balSlot (boHolder sevm)

/-- What `balanceOf` costs, on the shadows. -/
def balanceOfGasS (sevm : Sevm) (keys : List (Adr × B256)) : Nat :=
  106 + sloadCostS sevm.currentTarget keys (boSlot sevm)

/-- The machine a `balanceOf` halts with, on the shadows. -/
def balanceOfPostS (sevm : Sevm) (c : PCfg) (G : Nat) : Devm :=
  retPost (afterSloadS sevm.currentTarget c.keys c.devm (boSlot sevm)) [Sevm.selector sevm]
    (Mem.empty.write 0 (lookupS c.stor sevm.currentTarget (boSlot sevm)).toBytes) G
    (lookupS c.stor sevm.currentTarget (boSlot sevm))

/-- **`balanceOf(a)` from a pool frame** (a `STATICCALL` or a `CALL`): the child returns the
balance word the storage shadow holds, and writes nothing. -/
theorem balanceOf_child {sevm : Sevm} {c : PCfg} {G : Nat} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hsel : Sevm.selector sevm = 0x70a08231)
    (hpc : c.pc = 0) (hstack : c.devm.stack = []) (hmem : c.devm.memory = Mem.empty)
    (hag : PAgree c) (hgas : c.devm.gasLeft = G + balanceOfGasS sevm c.keys) :
    ChildAgree (balanceOfPostS sevm c G) ((sevm.currentTarget, boSlot sevm) :: c.keys) c.adrs
        c.stor c.acs ∧
      ∀ x, NodeAt sevm c x → x.exn = .ok (balanceOfPostS sevm c G) ∧
        Exec.rawFrameDescendants x.exc = [] := by
  have h := childAgree_of_pagree hag
  have hpost : balanceOfPost sevm c.devm G = balanceOfPostS sevm c G := by
    unfold balanceOfPost balanceOfPostS; rw [afterSload_shadow h, ChildAgree.getStorVal h]
  have hrun := balanceOf_runExact (G := G) hfork hsel hstack hmem
    (by rw [hgas]; unfold balanceOfGas balanceOfGasS; rw [sloadCost_shadow h])
  rw [hpost] at hrun
  refine ⟨?_, exact_leaf cert_check cert_jumpsOk spawnFreeReach hcode hfork hpc hrun⟩
  rw [← hpost]
  exact ChildAgree.ret (ChildAgree.afterSload (sevm := sevm) h (boSlot sevm)) _ _ _ _ _ _

end Blanc.Lift.VyperNonreentrantDeployed.Token20
