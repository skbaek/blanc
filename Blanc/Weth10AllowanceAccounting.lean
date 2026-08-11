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

/-- Replaying a single counted frame: its allowance visit's written word at
a matching key, otherwise the entry value. -/
theorem applyAllowanceLedger_singleton (pre : Stor) (frame : CountedFrame)
    (key : B256) :
    applyAllowanceLedger pre [frame] key =
      match frame.allowance with
      | some event =>
          if event.key = key then
            match event.visit.written? with
            | some value => value
            | none => pre.get key
          else pre.get key
      | none => pre.get key := by
  unfold applyAllowanceLedger lastAllowanceWriteAt
  cases hallow : frame.allowance with
  | none => simp [lastAllowanceWriteAt, hallow]
  | some event =>
      by_cases hkey : event.key = key
      · cases hwrite : event.visit.written? with
        | some value => simp [hallow, hkey, hwrite]
        | none => simp [lastAllowanceWriteAt, hallow, hkey, hwrite]
      · simp [lastAllowanceWriteAt, hallow, hkey]

/-- A leading eventless record is transparent to the ledger replay. -/
theorem applyAllowanceLedger_cons_none
    {pre : Stor} {record : CountedFrame} {rest : List CountedFrame}
    {key : B256} (hnone : record.allowance = none) :
    applyAllowanceLedger pre (record :: rest) key =
      applyAllowanceLedger pre rest key := by
  have h := applyAllowanceLedger_append pre pre [record] rest key
    (by rw [applyAllowanceLedger_singleton, hnone])
  simpa using h

/-- The ledger replay reads its entry storage only at the replayed key. -/
theorem applyAllowanceLedger_congr
    {pre pre' : Stor} {ledger : List CountedFrame} {key : B256}
    (h : pre.get key = pre'.get key) :
    applyAllowanceLedger pre ledger key =
      applyAllowanceLedger pre' ledger key := by
  unfold applyAllowanceLedger
  cases lastAllowanceWriteAt ledger.reverse key with
  | none => exact h
  | some value => rfl

/-! ## Stream unfolding -/

theorem Exec.attributionStream_eq_frameContribution
    (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h : Execution.commits out = true) :
    Exec.attributionStream dp ca run =
      Exec.frameContribution dp ca (Exec.Frame.ofRun run h)
        (Exec.attributionInner dp ca run) := by
  unfold Exec.attributionStream
  rw [dif_pos h]

/-- A frame whose allowance activity precedes its spawns contributes its own
record ahead of its descendant stream. -/
theorem Exec.frameContribution_eq_cons
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (inner : List CountedFrame)
    (hexact : frame.exactInvocation dp ca)
    (hnotlast : ownRecordLast frame.sevm = false) :
    Exec.frameContribution dp ca frame inner =
      CountedFrame.ofFrame dp ca frame :: inner := by
  unfold Exec.frameContribution
  rw [if_pos hexact, if_neg (by simp [hnotlast])]

/-- A frame whose allowance activity follows its spawns — `flashLoan`'s
post-callback settlement, `permit`'s post-`STATICCALL` store — contributes
its own record behind its descendant stream. -/
theorem Exec.frameContribution_eq_append
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (inner : List CountedFrame)
    (hexact : frame.exactInvocation dp ca)
    (hlast : ownRecordLast frame.sevm = true) :
    Exec.frameContribution dp ca frame inner =
      inner ++ [CountedFrame.ofFrame dp ca frame] := by
  unfold Exec.frameContribution
  rw [if_pos hexact, if_pos hlast]

/-- Flash-specific form of `Exec.frameContribution_eq_append`. -/
theorem Exec.frameContribution_eq_append_of_flash
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (inner : List CountedFrame)
    (hexact : frame.exactInvocation dp ca)
    (hflash : isFlashInvocation frame.sevm = true) :
    Exec.frameContribution dp ca frame inner =
      inner ++ [CountedFrame.ofFrame dp ca frame] :=
  Exec.frameContribution_eq_append dp ca frame inner hexact
    (ownRecordLast_of_isFlashInvocation hflash)

/-- Permit-specific form of `Exec.frameContribution_eq_append`. -/
theorem Exec.frameContribution_eq_append_of_permit
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (inner : List CountedFrame)
    (hexact : frame.exactInvocation dp ca)
    (hpermit : isPermitInvocation frame.sevm = true) :
    Exec.frameContribution dp ca frame inner =
      inner ++ [CountedFrame.ofFrame dp ca frame] :=
  Exec.frameContribution_eq_append dp ca frame inner hexact
    (ownRecordLast_of_isPermitInvocation hpermit)

theorem Exec.frameContribution_eq_inner
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (inner : List CountedFrame)
    (hnotexact : ¬ frame.exactInvocation dp ca) :
    Exec.frameContribution dp ca frame inner = inner := by
  unfold Exec.frameContribution
  rw [if_neg hnotexact]

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

/-! ## The read-sound region carrier

`AllowanceRegionEffect` relates an entry state to a committed post state and
exposes no intermediate, so it can replay recorded *writes* but never ties a
recorded *read* to any state.  The strengthening below adds exactly that
missing clause, as an additive extension so every existing consumer keeps
working through `toAllowanceRegionEffect`. -/

/-- Whether a counted record's frame dispatched to `flashLoan` — the one
selector whose *read* is reconstructed from the committed post state rather
than observed at frame entry.  Its own record is also one of the two
`Exec.frameContribution` places after its subtree rather than before it, but
that is the placement predicate's business, not this one's. -/
def CountedFrame.IsFlash (record : CountedFrame) : Prop :=
  record.sel? = some flashLoanSelector

/-- A record whose recorded selector is not `flashLoan` is not a flash
record. -/
theorem CountedFrame.not_isFlash_of_sel
    {record : CountedFrame} {sel : B256}
    (hsel : record.sel? = some sel) (hne : sel ≠ flashLoanSelector) :
    ¬ record.IsFlash := by
  unfold CountedFrame.IsFlash
  rw [hsel]
  simpa using hne

/-- Every non-flash allowance event records exactly the word its own frame's
*entry* storage holds at the event's key.  This is a property of the
extractor, not of the runtime walk: `frameAllowanceEvent` computes the
approve, permit, spend and view sites from `pre`, and only the flash site
reconstructs its read from `post`. -/
theorem frameAllowanceEvent_read_eq_pre
    {e : Sevm} {pre post : Devm} {event : AllowanceEvent} {v : B256}
    (hnotflash : isFlashInvocation e = false)
    (hevent : frameAllowanceEvent e pre post = some event)
    (hread : event.visit.read? = some v) :
    v = (Devm.getStor pre e.currentTarget).get event.key := by
  unfold frameAllowanceEvent at hevent
  split at hevent
  · exact absurd hevent (by simp)
  · rename_i hne0
    split at hevent
    · cases hevent; exact absurd hread (by simp [AllowanceVisit.read?])
    · split at hevent
      · cases hevent; exact absurd hread (by simp [AllowanceVisit.read?])
      · split at hevent
        · split at hevent
          · exact absurd hevent (by simp)
          · cases hevent
            simp only [AllowanceEvent.key,
              ← callerAllowanceRuntimeKey_eq_projected]
            split at hread
            · rename_i hmax
              rw [hmax]
              exact (Option.some.inj hread).symm
            · exact (Option.some.inj hread).symm
        · split at hevent
          · rename_i hflash
            exact absurd hnotflash
              (by simp [isFlashInvocation, hne0, hflash])
          · split at hevent
            · cases hevent
              exact (Option.some.inj hread).symm
            · exact absurd hevent (by simp)

/-- Entry-read soundness for one ledger: every non-flash record's allowance
read observed exactly the word the ledger prefix strictly before that record
prescribes over the entry storage.

The non-flash restriction is forced rather than cosmetic.
`Exec.frameContribution` places a flash frame's own record *after* its
subtree, so for a flash record the prefix `earlier` is not "what ran before
that frame entered" and the clause below would be false.  Delegated debits
arise only from `transferFrom`/`withdrawFrom`, so the restriction costs
nothing where entry-read soundness is actually consumed (the dormant-holder
residual).

`permit`'s record is placed after its subtree for the same chronological
reason, but needs no exemption here: a `.permitStore` visit records no read
at all, so the clause is vacuous on it.  What the placement does buy is that
a read recorded *inside* a `permit`'s `STATICCALL` subtree now sees a prefix
that excludes the permit's own store — which is exactly the order in which
the runtime performs them. -/
def AllowanceEntryReadSound (pre : Stor) (ledger : List CountedFrame) : Prop :=
  ∀ earlier record later, ledger = earlier ++ record :: later →
    ¬ record.IsFlash →
    ∀ event, record.allowance = some event →
      ∀ v, event.visit.read? = some v →
        v = applyAllowanceLedger pre earlier event.key

theorem AllowanceEntryReadSound.nil (pre : Stor) :
    AllowanceEntryReadSound pre [] := by
  intro earlier record later hsplit
  exact absurd hsplit.symm (by simp)

/-- A one-record ledger is entry-read sound exactly when its own record's
read is the entry word at its key: the only admissible split has an empty
prefix. -/
theorem AllowanceEntryReadSound.singleton
    {pre : Stor} {own : CountedFrame}
    (h : ∀ event, own.allowance = some event →
      ∀ v, event.visit.read? = some v → v = pre.get event.key) :
    AllowanceEntryReadSound pre [own] := by
  intro earlier record later hsplit _ event hevent v hread
  cases earlier with
  | nil =>
      rw [List.nil_append] at hsplit
      obtain ⟨hrec, -⟩ := List.cons.injEq .. ▸ hsplit
      subst hrec
      exact h event hevent v hread
  | cons head tail => exact absurd hsplit (by simp)

/-- A one-record ledger whose record *is* the flash record is entry-read
sound for free: the clause exempts flash records, and the only admissible
split puts this record in the clause's position.  This is what lets a
`flashLoan` frame's own trailing segment compose, even though its recorded
read is reconstructed from the post state. -/
theorem AllowanceEntryReadSound.singleton_flash
    {pre : Stor} {own : CountedFrame} (hflash : own.IsFlash) :
    AllowanceEntryReadSound pre [own] := by
  intro earlier record later hsplit hnotflash
  cases earlier with
  | nil =>
      rw [List.nil_append] at hsplit
      obtain ⟨hrec, -⟩ := List.cons.injEq .. ▸ hsplit
      subst hrec
      exact absurd hflash hnotflash
  | cons head tail => exact absurd hsplit (by simp)

/-- The counted record of a non-flash frame is entry-read sound on its own:
its event, if any, reads the frame's entry storage. -/
theorem AllowanceEntryReadSound.ofFrame
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (htarget : frame.sevm.currentTarget = ca)
    (hnotflash : isFlashInvocation frame.sevm = false) :
    AllowanceEntryReadSound (Devm.getStor frame.pre ca)
      [CountedFrame.ofFrame dp ca frame] := by
  refine .singleton (fun event hevent v hread => ?_)
  rw [← htarget]
  exact frameAllowanceEvent_read_eq_pre hnotflash hevent hread

/-- Chronological composition of entry-read soundness.  The right segment's
prefixes are re-based from `mid` to `pre` by `applyAllowanceLedger_append`,
which applies because every event key is a projected allowance key and the
left segment transports the whole allowance region. -/
theorem AllowanceEntryReadSound.append
    {pre mid : Stor} {left right : List CountedFrame}
    (hstorage : ∀ key, InRegion .allowance key →
      mid.get key = applyAllowanceLedger pre left key)
    (hleft : AllowanceEntryReadSound pre left)
    (hright : AllowanceEntryReadSound mid right) :
    AllowanceEntryReadSound pre (left ++ right) := by
  intro earlier record later hsplit hnotflash event hevent v hread
  have hkey : InRegion .allowance event.key :=
    projectedAllowanceKey_region event.owner event.spender
  rcases List.append_eq_append_iff.1 hsplit with
    ⟨tail, hearlier, hrightSplit⟩ | ⟨tail, hleftSplit, hconsSplit⟩
  · subst hearlier
    rw [applyAllowanceLedger_append pre mid left tail event.key
      (hstorage event.key hkey)]
    exact hright tail record later hrightSplit hnotflash event hevent v hread
  · cases tail with
    | nil =>
        rw [List.append_nil] at hleftSplit
        subst hleftSplit
        exact (hright [] record later (by simpa using hconsSplit.symm)
          hnotflash event hevent v hread).trans (hstorage event.key hkey)
    | cons head rest =>
        rw [List.cons_append] at hconsSplit
        cases hconsSplit
        exact hleft earlier record rest hleftSplit hnotflash event hevent v
          hread

/-- The read-sound allowance-region carrier: the last-committed-write
transport of `AllowanceRegionEffect`, plus entry-read soundness of the same
ledger against the same entry state. -/
structure AllowanceRegionEffectSound (ca : Adr) (pre post : Devm)
    (ledger : List CountedFrame) : Prop extends
    AllowanceRegionEffect ca pre post ledger where
  entryRead : AllowanceEntryReadSound (Devm.getStor pre ca) ledger

theorem AllowanceRegionEffectSound.of_getStorCode_eq
    {ca : Adr} {pre post : Devm}
    (hstor : Devm.getStor pre ca = Devm.getStor post ca)
    (hcode : pre.getCode ca = post.getCode ca) :
    AllowanceRegionEffectSound ca pre post [] :=
  { AllowanceRegionEffect.of_getStorCode_eq hstor hcode with
    entryRead := .nil _ }

theorem AllowanceRegionEffectSound.refl {ca : Adr} {pre : Devm} :
    AllowanceRegionEffectSound ca pre pre [] :=
  .of_getStorCode_eq rfl rfl

/-- Chronological composition of two read-sound transported segments. -/
theorem AllowanceRegionEffectSound.append
    {ca : Adr} {pre mid post : Devm}
    {left right : List CountedFrame}
    (hleft : AllowanceRegionEffectSound ca pre mid left)
    (hright : AllowanceRegionEffectSound ca mid post right) :
    AllowanceRegionEffectSound ca pre post (left ++ right) :=
  { hleft.toAllowanceRegionEffect.append hright.toAllowanceRegionEffect with
    entryRead :=
      .append hleft.storage hleft.entryRead hright.entryRead }

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

