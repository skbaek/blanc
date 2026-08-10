import Blanc.Weth10AttributionChronology
import Blanc.Weth10HolderFlowExecAccounting

/-!
Allowance-region storage accounting for the compiled WETH10 runtime.

This module defines the carrier and recursion interface for the
last-committed-write transport of `weth10-redeem-future-v2`: the committed
storage content of every tagged allowance key after an execution equals the
last committed write recorded by the chronological attribution ledger, or
the entry value when no counted write touches that key.

The interface deliberately mirrors the balance development's
`Exec.CoreStorageSound` / `CompiledBodyStorageHandler` pair so the same
`lift_core` recursion discharges it: foreign frames and neutral steps are
covered by the existing full `getStor ca` equalities, and the sole
contract-specific obligation is the per-selector effect of an authentic
WETH10 frame.  The carrier is collision-insensitive: it speaks only of
projected keys, and the trace-local `NoAllowanceKeyCollision` hypothesis is
consumed later, when key chains are upgraded to raw pair chains.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## The ledger fold -/

theorem lastAllowanceWriteAt_append
    (xs ys : List CountedFrame) (key : B256) :
    lastAllowanceWriteAt (xs ++ ys) key =
      match lastAllowanceWriteAt xs key with
      | some value => some value
      | none => lastAllowanceWriteAt ys key := by
  induction xs with
  | nil => simp [lastAllowanceWriteAt]
  | cons frame rest ih =>
      cases hallow : frame.allowance with
      | none => simpa [lastAllowanceWriteAt, hallow] using ih
      | some event =>
          by_cases hkey : event.key = key
          · cases hwrite : event.visit.written? with
            | some value => simp [lastAllowanceWriteAt, hallow, hkey, hwrite]
            | none => simpa [lastAllowanceWriteAt, hallow, hkey, hwrite] using ih
          · simpa [lastAllowanceWriteAt, hallow, hkey] using ih

/-- The committed value at `key` after replaying a chronological ledger over
an entry storage: the last committed write in the ledger, or the entry value
when no counted write touches the key.  The ledger is chronological
(oldest first), so the walk runs over its reversal. -/
def applyAllowanceLedger (pre : Stor) (ledger : List CountedFrame)
    (key : B256) : B256 :=
  match lastAllowanceWriteAt ledger.reverse key with
  | some value => value
  | none => pre.get key

@[simp] theorem applyAllowanceLedger_nil (pre : Stor) (key : B256) :
    applyAllowanceLedger pre [] key = pre.get key := rfl

/-- Chronological composition: replaying `left ++ right` is replaying
`right` over the result of replaying `left`. -/
theorem applyAllowanceLedger_append
    (pre mid : Stor) (left right : List CountedFrame) (key : B256)
    (hmid : mid.get key = applyAllowanceLedger pre left key) :
    applyAllowanceLedger pre (left ++ right) key =
      applyAllowanceLedger mid right key := by
  unfold applyAllowanceLedger
  rw [List.reverse_append, lastAllowanceWriteAt_append]
  cases hright : lastAllowanceWriteAt right.reverse key with
  | some value => simp
  | none => simpa [applyAllowanceLedger] using hmid.symm

/-! ## The region carrier -/

/-- The allowance-region transport carrier: after the execution, every
tagged allowance key holds exactly the ledger's last committed write, or its
entry value.  `codeEq` keeps the installed-code witness available to later
siblings, exactly as in the balance carrier. -/
structure AllowanceRegionEffect (ca : Adr) (pre post : Devm)
    (ledger : List CountedFrame) : Prop where
  storage : ∀ key, InRegion .allowance key →
    (Devm.getStor post ca).get key =
      applyAllowanceLedger (Devm.getStor pre ca) ledger key
  codeEq : pre.getCode ca = post.getCode ca

theorem AllowanceRegionEffect.of_getStorCode_eq
    {ca : Adr} {pre post : Devm}
    (hstor : Devm.getStor pre ca = Devm.getStor post ca)
    (hcode : pre.getCode ca = post.getCode ca) :
    AllowanceRegionEffect ca pre post [] :=
  ⟨fun key _ => by rw [applyAllowanceLedger_nil, hstor], hcode⟩

theorem AllowanceRegionEffect.refl {ca : Adr} {pre : Devm} :
    AllowanceRegionEffect ca pre pre [] :=
  .of_getStorCode_eq rfl rfl

/-- Chronological composition of two transported segments. -/
theorem AllowanceRegionEffect.append
    {ca : Adr} {pre mid post : Devm}
    {left right : List CountedFrame}
    (hleft : AllowanceRegionEffect ca pre mid left)
    (hright : AllowanceRegionEffect ca mid post right) :
    AllowanceRegionEffect ca pre post (left ++ right) := by
  refine ⟨fun key hregion => ?_, hleft.codeEq.trans hright.codeEq⟩
  rw [hright.storage key hregion,
    applyAllowanceLedger_append (Devm.getStor pre ca) (Devm.getStor mid ca)
      left right key (hleft.storage key hregion)]

/-! ## The recursion interface -/

/-- Proof-indexed allowance transport consumed by the generic interpreter
recursion, mirroring `Exec.CoreStorageSound`: root freshness and direct code
ownership are demanded only when this exact execution is at the installed
contract. -/
def Exec.CoreAllowanceSound (dp : DeployParams) (ca : Adr)
    (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution) : Prop :=
  ∀ (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true),
    Prog.At (weth10 dp) ca pc sevm pre →
    (sevm.currentTarget = ca →
      Exec.Frame.IsRoot (Exec.Frame.ofRun run committed) ∧
        sevm.codeAddress = some ca) →
    AllowanceRegionEffect ca pre
      (Execution.committedPost out committed)
      (Exec.attributionStream dp ca run)

/-- The sole contract-specific allowance obligation left by the generic
interpreter recursion, mirroring `CompiledBodyStorageHandler`. -/
def CompiledBodyAllowanceHandler (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm},
    Prog.Run sevm pre (weth10 dp) post →
    sevm.currentTarget = ca →
    ForallDeeperAt sevm.depth ca (weth10 dp)
      (fun pc s d out _ => Exec.CoreAllowanceSound dp ca pc s d out) →
    ∀ (run : Exec 0 sevm pre (.ok post))
      (committed : Execution.commits (.ok post) = true),
      Prog.At (weth10 dp) ca 0 sevm pre →
      (sevm.currentTarget = ca →
        Exec.Frame.IsRoot (Exec.Frame.ofRun run committed) ∧
          sevm.codeAddress = some ca) →
      AllowanceRegionEffect ca pre post
        (Exec.attributionStream dp ca run)

/-- Frame-oriented form of the allowance obligation: the natural consumer of
selector chronology, exposing the authentic frame directly. -/
def CompiledFrameAllowanceHandler (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ (frame : Exec.Frame),
    frame.AuthenticContext dp ca →
    ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out) →
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run)

/-- Root/direct hypotheses reconstruct the authentic frame context, exactly
as in the balance development. -/
theorem CompiledFrameAllowanceHandler.compiledBodyAllowanceHandler
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledFrameAllowanceHandler dp ca) :
    CompiledBodyAllowanceHandler dp ca := by
  intro sevm pre post hrun htarget hdeeper run committed installed rootDirect
  let frame := Exec.Frame.ofRun run committed
  have hrootDirect := rootDirect htarget
  have context : frame.AuthenticContext dp ca := by
    refine ⟨hrootDirect.1, ?_, installed⟩
    refine ⟨rfl, htarget, hrootDirect.2, ?_⟩
    exact (installed.2 htarget).1
  exact handler frame context hdeeper

end Weth10

end Blanc

