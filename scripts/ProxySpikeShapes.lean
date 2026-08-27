import Blanc.SourceAttainment
import Blanc.CycleWriteFree
import Blanc.ForwardCall

/-!
# Spike evidence: applied attribution, and the shapes a proxy programme needs

Branch-local evidence for goal `proxy-delegatecall-spike-v1`, row **P6** and the
applied-attribution half of row **P3**.  Deliberately outside `Blanc/`: it binds
no gate and states no baseline.

Three parts, and they are *different kinds of thing*:

* **Part A** is a proof.  Blanc's shared attribution surface is parametric in
  two addresses — a storage target and a code address — and the spike's question
  is whether it survives the two being *different*, which is exactly what
  `DELEGATECALL` makes them.  The answer is yes, with no new lemma, and the
  section closes it against a really executed delegatecall frame rather than a
  hypothetical one.
* **Part B** (`ProxyCorrespondence`) and **Part C** (`UpgradeEquivalent`) are
  *statements*.  They elaborate, their supporting definitions are `sorry`-free,
  and nothing here proves either of them.  What Part B does prove is that its
  premise set is simultaneously satisfiable — a correspondence whose hypotheses
  no message can meet would be a vacuous `Prop`, and that would be a finding
  rather than a deliverable.

Files under `scripts/` may not import one another, so every term this file
shares with `scripts/ProxySpikeExec.lean` and `scripts/ProxySpikeProxy.lean` is
restated rather than imported.  The restatements are character-for-character
copies; they are the same terms, which is what lets the results below be about
the programmes those files compiled rather than about programmes chosen to make
a theorem come out.

There is no `sorry`, no `native_decide`, no new axiom, and no
`set_option maxRecDepth`/`maxHeartbeats` anywhere below.
-/

namespace Blanc.ProxySpikeShapes

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Restated terms

### The pair, and the implementation programme

Copied character-for-character from `scripts/ProxySpikeExec.lean`
(`proxyAdr`, `implAdr`, `implSlot`, `implMain`, `implProg`, `implBytes`,
`implCode`, `implBodyGas`, `implEntryGas`).  Same terms; the copy exists only
because `scripts/` files cannot import one another. -/

/-- The proxy account: the storage owner under `DELEGATECALL`. -/
def proxyAdr : Adr := 0x00000000000000000000000000000000000a0001

/-- The implementation account: the code address under `DELEGATECALL`. -/
def implAdr : Adr := 0x00000000000000000000000000000000000b0002

/-- The implementation's own storage word. -/
def implSlot : B256 := 7

theorem proxyAdr_ne_implAdr : proxyAdr ≠ implAdr := by decide

def implMain : Func :=
  pushB256 1 ::: pushB256 implSlot ::: sstore :::
  pushB256 42 ::: mstoreAt 0 +++ pushB256 32 ::: pushB256 0 ::: Func.last .ret

def implProg : Prog := ⟨implMain, []⟩

def implBytes : Bytes := (Prog.compile implProg).getD []

def implCode : ByteArray := ByteArray.mk implBytes.toArray

theorem implProg_compiles : implProg.compiles = true := by decide

theorem implProg_compile : Prog.compile implProg = some implBytes :=
  Prog.compile_eq_some_getD_of_compiles _ implProg_compiles

/-- Not an EIP-7702 designator, so nothing below is accidentally testing 7702
resolution. -/
theorem implCode_notDelegation : getDelegatedCodeAddress implCode = none := by
  decide +kernel

def implBodyGas : Nat :=
  (gVerylow + gVerylow + (gasColdSload + gasStorageSet))
    + (gVerylow + gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

theorem implBodyGas_eq : implBodyGas = 22122 := by decide

def implEntryGas : Nat := implBodyGas + gJumpdest

/-! ### The forwarding proxy

Copied character-for-character from `scripts/ProxySpikeProxy.lean`
(`implementationSlotLit`, `proxyFallback`, `proxyProg`, `proxyBytes`,
`proxyCode`).  That file carries the one theorem tying the literal to the
derivation — `implementationSlotLit_derived`, a kernel decision on one fixed
input against `Blanc.String.keccak "eip1967.proxy.implementation" - 1` — and it
is not re-proved here; re-running a Keccak evaluation would buy this file
nothing the sibling has not already established about the same term. -/

def implementationSlotLit : B256 :=
  0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc

def proxyFallback : Func :=
  -- 1. copy the whole calldata to memory[0 .. cds)
  calldatasize ::: pushB256 0 ::: pushB256 0 ::: calldatacopy :::
  -- 2. the six DELEGATECALL operands, deepest pushed first
  pushB256 0 :::                                   -- retSize   = 0
  pushB256 0 :::                                   -- retOffset = 0
  calldatasize :::                                 -- argsSize
  pushB256 0 :::                                   -- argsOffset
  pushB256 implementationSlotLit ::: sload :::     -- implementation address
  gas :::                                          -- forward all remaining gas
  delcall :::
  -- 3. copy the child's returndata verbatim to memory[0 .. rds)
  retdatasize ::: dup 0 ::: pushB256 0 ::: pushB256 0 ::: retdatacopy :::
  -- stack is now [rds, success]; bring success to the top for the branch
  swap 0 :::
  Func.branch
    (pushB256 0 ::: Func.last .rev)     -- success = 0   -> revert verbatim
    (pushB256 0 ::: Func.last .ret)     -- success /= 0  -> return verbatim

def proxyProg : Prog := ⟨proxyFallback, []⟩

def proxyBytes : Bytes := (Prog.compile proxyProg).getD []

def proxyCode : ByteArray := ByteArray.mk proxyBytes.toArray

theorem proxyProg_compiles : proxyProg.compiles = true := by decide

theorem proxyProg_compile : Prog.compile proxyProg = some proxyBytes :=
  Prog.compile_eq_some_getD_of_compiles _ proxyProg_compiles


/-! # Part A — applied attribution across a role split

`Blanc/ExecutionOccurrence.lean:2324` states exact invocation identity in *two*
addresses:

```
def Exec.Deriv.exactInvocation
    (program : Prog) (storageTarget codeAddress : Adr) (root : Exec.Deriv) : Prop :=
  root.pc = 0 ∧ root.sevm.currentTarget = storageTarget ∧
    root.sevm.codeAddress = some codeAddress ∧
    some root.sevm.code.toList = program.compile
```

Every same-frame attribution theorem downstream carries those two addresses and
— this is the fact the whole spike turns on — neither of them is ever used to
close a goal.  `Exec.Deriv.SourceCursor.mainToward` consumes `hpc` and the
compiled-bytes conjunct and nothing else.  So the surface was already
delegatecall-ready; the section below applies it where the two addresses
*differ*, which is the case no existing consumer exercises. -/

/-! ## The applied theorem

Attribution for a frame whose storage owner is the **proxy** and whose executing
code lives at the **implementation** — two distinct addresses in the one
invocation predicate.  No new lemma: the proof is the shared theorem applied. -/

theorem slot_write_attributed_to_implementation
    {root target : Exec.Deriv}
    (invocation : root.exactInvocation implProg proxyAdr implAdr)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ site : Prog.SourceSite, site ∈ implProg.sourceSites ∧
      site.pc = target.pc ∧ site.instruction = .reg .sstore :=
  Exec.Deriv.sstore_sourceSite invocation sameFrame storeAt

/-- The `Exec.SuccessfulSstoreOccurrence` form, through
`Exec.Frame.successfulSstore_sourceSite` (`Blanc/ExecutionOccurrence.lean:3521`).
It applies with the roles split exactly as cleanly: that theorem's
`storageTarget` and `codeAddress` are inert in its proof too. -/
theorem successful_slot_write_attributed_to_implementation
    {frame : Exec.Frame}
    (invocation : frame.exactInvocation implProg proxyAdr implAdr)
    (write : Exec.SuccessfulSstoreOccurrence frame.rootDeriv)
    (sameFrame : Exec.Deriv.ParentPrefix frame.rootDeriv
      write.occurrence.node) :
    ∃ site : Prog.SourceSite, site ∈ implProg.sourceSites ∧
      site.pc = write.occurrence.node.pc ∧ site.instruction = .reg .sstore :=
  Exec.Frame.successfulSstore_sourceSite invocation write sameFrame

/-! ## The control that makes the application bite

An application to a *split* pair says something only if the surface would not
have been satisfied with the roles *fused*.  It would not: the code-address
conjunct pins one `Option Adr`, so a root cannot answer to two different code
addresses at once.  Stated generically, because the fact is about the predicate
and not about this pair. -/

theorem exactInvocation_roles_not_fusable
    {root : Exec.Deriv} {program : Prog} {storageTarget codeAddress : Adr}
    (invocation : root.exactInvocation program storageTarget codeAddress)
    (distinct : storageTarget ≠ codeAddress) :
    ¬ root.exactInvocation program storageTarget storageTarget := by
  rintro ⟨-, -, fused, -⟩
  exact distinct (Option.some.inj (fused.symm.trans invocation.2.2.1))

/-! ## Non-vacuity: a really executed delegatecall frame

A hypothetical application proves nothing if no frame can satisfy
`exactInvocation implProg proxyAdr implAdr` at all.  This section exhibits one,
and does not stop at the invocation predicate: it runs the implementation body,
routes the walk to its `SSTORE` through `Blanc/SourceAttainment.lean`'s forward
kit, and reaches the attribution conclusion at an actually reached node.  The
resulting theorem has no hypotheses. -/

/-- The message a `DELEGATECALL` builds.  Copied verbatim from
`Blanc.ProxySpike.delcallSpawnMsg` in `scripts/ProxySpikeSpawn.lean`, which is
where the edge itself is proved. -/
def delcallChildMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (codeAdr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) : Msg :=
  callMsg sevm p mcs sevm.value sevm.caller sevm.currentTarget codeAdr
    false false (p.memory.data.sliceD ii is 0) code dp

/-- The `Inhabited` frame, moved onto the proxy.  Copied from
`scripts/ProxySpikeExec.lean`. -/
def freshSevm : Sevm := { (default : Sevm) with currentTarget := proxyAdr }

/-- The concrete delegatecall child: storage owner `proxyAdr`, code address
`implAdr`, implementation bytes, entered with exactly the gas the body needs. -/
def implDelcallMsg (G : Nat) : Msg :=
  delcallChildMsg freshSevm default (G + implEntryGas) implAdr 0 0 implCode
    false

/-- The implementation body's forward walk.  `scripts/ProxySpikeExec.lean`'s
`implMain_runCompiledTo` with the storage, gas and framing conclusions dropped —
only the derivation is wanted here, because it is the derivation the route kit
consumes.  The walk itself is that file's, tactic for tactic. -/
theorem implMain_walk (fs : List Func) (sevm : Sevm) (base : Devm) (G : Nat)
    (h_static : sevm.isStatic = false)
    (h_cold : (⟨sevm.currentTarget, implSlot⟩ : Adr × B256)
      ∉ base.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm sevm.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal base sevm.currentTarget implSlot = 0) :
    ∃ post,
      Func.RunCompiledTo fs sevm (base.setMach ⟨[], Mem.empty, G + implBodyGas⟩)
        implMain (.ok post) := by
  apply Exists.intro
  rw [implBodyGas_eq]
  unfold implMain mstoreAt
  func_run [22100, 3]
  case h_cost =>
    rw [Devm.getStorVal_setMach, h_orig, h_cur]
    decide
  case h_ext =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_empty_word
  case a =>
    apply Func.runCompiledTo_ret_word (i := 0) (sz := 32) (s := [])
      (e := 0) (G := G) (out := (42 : B256).toBytes)
    · rfl
    · rw [show ((0 : B256)).toNat = 0 by decide,
        show ((32 : B256)).toNat = 32 by decide,
        show ((0 : B256) * 32).toNat = 0 by decide]
      exact Devm.extCost_word_word Mem.size_write_word
    · show G + 22122 - 22122 = G + 0
      omega
    · rw [show ((0 : B256)).toNat = 0 by decide,
        show ((32 : B256)).toNat = 32 by decide]
      exact Devm.memRead_word_fst
        (by rw [show ((0 : B256) * 32).toNat = 0 by decide]; rfl)

/-- **The applied attribution, with nothing left hypothetical.**  There is a
root derivation whose storage owner is the proxy and whose code address is the
implementation — two *distinct* addresses — which satisfies the shared exact
invocation surface, fails it when the two roles are fused, actually reaches an
`SSTORE`, and whose reached `SSTORE` is attributed to a source site of the
implementation's own programme.

The route is `Blanc/SourceAttainment.lean`'s: two `.next` crossings past the
body's two pushes, then the designation at the `SSTORE` head. -/
theorem delcall_frame_sstore_attributed (G : Nat) :
    ∃ (root node : Exec.Deriv) (site : Prog.SourceSite),
      root.pc = 0 ∧
      root.sevm = initSevm (implDelcallMsg G) ∧
      root.devm = initDevm (implDelcallMsg G) ∧
      root.sevm.currentTarget = proxyAdr ∧
      root.sevm.codeAddress = some implAdr ∧
      proxyAdr ≠ implAdr ∧
      root.exactInvocation implProg proxyAdr implAdr ∧
      ¬ root.exactInvocation implProg proxyAdr proxyAdr ∧
      Exec.Deriv.ParentPrefix root node ∧
      Ninst.At node.sevm.code node.pc (.reg .sstore) ∧
      site ∈ implProg.sourceSites ∧
      site.pc = node.pc ∧
      site.instruction = .reg .sstore := by
  have hstatic : (initSevm (implDelcallMsg G)).isStatic = false := rfl
  have hcold : (⟨(initSevm (implDelcallMsg G)).currentTarget, implSlot⟩
      : Adr × B256) ∉ (initDevm (implDelcallMsg G)).accessedStorageKeys := by
    show (⟨proxyAdr, implSlot⟩ : Adr × B256)
      ∉ (Std.HashSet.emptyWithCapacity : Std.HashSet (Adr × B256))
    simp
  have horig : getOrigStorVal (initSevm (implDelcallMsg G))
      (initSevm (implDelcallMsg G)).currentTarget implSlot = 0 := rfl
  have hcur : Devm.getStorVal (initDevm (implDelcallMsg G))
      (initSevm (implDelcallMsg G)).currentTarget implSlot = 0 := rfl
  have hcompile :
      some (initSevm (implDelcallMsg G)).code.toList = implProg.compile := by
    show some implCode.toList = _
    rw [implProg_compile]
    simp [implCode, ByteArray.toList_eq_toList_data]
  obtain ⟨post, walk⟩ :=
    implMain_walk (implProg.main :: implProg.aux)
      (initSevm (implDelcallMsg G)) (initDevm (implDelcallMsg G)) G
      hstatic hcold horig hcur
  have hburn : Devm.BurnBy gJumpdest (initDevm (implDelcallMsg G))
      ((initDevm (implDelcallMsg G)).setMach
        ⟨[], Mem.empty, G + implBodyGas⟩) :=
    Devm.burnBy_setMach_gas (by
      show (implDelcallMsg G).gas = G + implBodyGas + gJumpdest
      show G + implEntryGas = G + implBodyGas + gJumpdest
      simp only [implEntryGas]
      omega)
  have hroute : Func.RunCompiledTo.RouteTo ⟨0, []⟩ walk
      ⟨0, [.rest, .rest]⟩ (.reg .sstore) :=
    routeTo_next walk (fun _ _ tail₁ =>
      routeTo_next tail₁ (fun _ _ tail₂ => routeTo_head tail₂ _))
  obtain ⟨exc, occurrence, site, _, hmem, hpc, hinstr, hinstrTarget, hprefix⟩ :=
    Prog.exec_of_runCompiledTo_routeTo (p := implProg) hburn hroute hcompile
  have invocation :
      (⟨0, initSevm (implDelcallMsg G), initDevm (implDelcallMsg G), .ok post,
        exc⟩ : Exec.Deriv).exactInvocation implProg proxyAdr implAdr :=
    ⟨rfl, rfl, rfl, hcompile⟩
  have storeAt : Ninst.At occurrence.node.sevm.code occurrence.node.pc
      (.reg .sstore) := by
    rw [show (Ninst.reg .sstore) = occurrence.instruction from
      (hinstr.trans hinstrTarget).symm]
    exact occurrence.decoded
  exact ⟨_, occurrence.node, site, rfl, rfl, rfl, rfl, rfl,
    proxyAdr_ne_implAdr, invocation,
    exactInvocation_roles_not_fusable invocation proxyAdr_ne_implAdr,
    hprefix, storeAt, hmem, hpc.symm, hinstrTarget⟩

/-! ## Row P6(iii): slot-write authority

The shape the row asks for is: *if the proxy's own runtime contains no `SSTORE`
source site, then every write to an ERC-1967 slot at the proxy account is
attributable to a source site in the implementation's programme.*

Two of its three pieces close here.

* The proxy half is an existing certificate.  `Prog.entrySstoreFree`
  (`Blanc/CycleWriteFree.lean:151`) accepts `proxyFallback` with an empty
  component, and `Exec.Deriv.noSstore_of_exactMain_entrySstoreFree` (`:352`)
  turns that into the absence of any reached same-frame `SSTORE`.  Note that
  theorem *also* carries `{storageTarget codeAddress : Adr}` with both inert, so
  the proxy frame's own role fusion (`proxyAdr`/`proxyAdr`) costs nothing.
* The implementation half is `slot_write_attributed_to_implementation` above.

What does **not** close, and is left as a named hypothesis rather than silently
carried, is the *dichotomy*: that the raw frame root owning a given `SSTORE`
occurrence is either the proxy's frame or the implementation's.  That is a
deployment-and-frame-tree fact about a particular installed pair — which
accounts hold which code, and that no third frame writes the proxy's storage —
not an attribution fact, and Blanc has no theorem shaped to supply it.  It is
therefore the single premise `dichotomy` below, which is the minimal form of the
missing piece.

Two further things the statement deliberately does *not* say.  It does not
mention the ERC-1967 slot: `Exec.NinstOccurrence` names the instruction and the
node, and the *key* an `SSTORE` writes is a stack word, so pinning it to
`implementationSlotLit` is a separate obligation about the occurrence's stack.
And it does not say "at the proxy account": under `DELEGATECALL` that is exactly
`sevm.currentTarget`, which `exactInvocation`'s second conjunct already pins to
`proxyAdr` in *both* disjuncts — so the account is fixed by the premises rather
than claimed by the conclusion. -/

/-- The forwarding proxy carries no `SSTORE` anywhere in its own body, and calls
nothing.  This is the executable certificate, decided. -/
theorem proxyProg_entrySstoreFree :
    proxyProg.entrySstoreFree proxyProg.main [] = true := by decide

/-- **The certificate bites.**  The same scan *rejects* the implementation, which
does write storage — so accepting the proxy is a fact about the proxy and not a
scan that accepts everything. -/
theorem implProg_not_entrySstoreFree :
    implProg.entrySstoreFree implProg.main [] = false := by decide

/-- The proxy's own frame reaches no `SSTORE` at all. -/
theorem proxy_frame_reaches_no_sstore
    {root target : Exec.Deriv}
    (invocation : root.exactInvocation proxyProg proxyAdr proxyAdr)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) : False :=
  Exec.Deriv.noSstore_of_exactMain_entrySstoreFree invocation []
    proxyProg_entrySstoreFree sameFrame storeAt

/-- **P6(iii), with the missing piece minimised to one premise.**  Given the
frame dichotomy, every reached `SSTORE` of the system is attributed to a source
site of the *implementation's* programme — never the proxy's, which has none. -/
theorem slot_write_authority
    {globalRoot frameRoot : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence globalRoot)
    (isSstore : occurrence.instruction = .reg .sstore)
    (owned : Exec.Deriv.ParentPrefix frameRoot occurrence.node)
    (dichotomy :
      frameRoot.exactInvocation proxyProg proxyAdr proxyAdr ∨
        frameRoot.exactInvocation implProg proxyAdr implAdr) :
    ∃ site : Prog.SourceSite, site ∈ implProg.sourceSites ∧
      site.pc = occurrence.node.pc ∧ site.instruction = .reg .sstore := by
  have storeAt : Ninst.At occurrence.node.sevm.code occurrence.node.pc
      (.reg .sstore) := by
    rw [show (Ninst.reg .sstore) = occurrence.instruction from isSstore.symm]
    exact occurrence.decoded
  rcases dichotomy with proxyInvocation | implInvocation
  · exact (proxy_frame_reaches_no_sstore proxyInvocation owned storeAt).elim
  · exact slot_write_attributed_to_implementation implInvocation owned storeAt


/-! # Part B — row P6(i): pair correspondence

**Statement only.**  Nothing below proves `ProxyCorrespondence`; what is proved
is that its premise set is satisfiable, and that it transports an account-level
clause by instantiation.

## Altitude: per message

The correspondence is stated over a `Msg`, not over a frame or a frame tree.
The pinned-target thread's T3 bundle states its clauses as *what the account at
that address does under the exact inbound calls*, and an inbound call is a
message.  A per-frame statement cannot express that, because a frame is already
inside the response; and relating two frame *trees* — the proxied one has an
extra node — would force restatement rather than the instantiation the two
threads' declared convergence requires. -/

/-- What one settled `Devm` shows to the outside at a nominated account.

Storage and transient storage are compared **pointwise**, not as maps: `Stor`
and `Tra` are tree maps, so structural equality of two representations is a
stronger claim than agreement of the words they read back, and the stronger one
is not what an observer can see. -/
def ObservableAt (proxy : Adr) (a b : Devm) : Prop :=
  a.output = b.output ∧
    (∀ key : B256, a.getStorVal proxy key = b.getStorVal proxy key) ∧
    (∀ key : B256, a.getTransVal proxy key = b.getTransVal proxy key) ∧
    a.logs = b.logs

/-- Observational agreement of two message outcomes at the proxy account: the
same error status, the same `EvmError` when errored, the same output, the same
persistent and transient storage at the proxy, and the same logs.

**Two named deviations, and they are the honest part of the statement.**

* **Gas is excluded.**  A proxy costs a strictly positive forwarding overhead —
  the prologue, the `SLOAD`, the `DELEGATECALL`, the returndata copy — so gas
  equality between the proxied and the direct run is *false*.  Asserting it
  would not be a stronger claim; it would be a defect.
* **`accessedAddresses` is excluded.**  The proxy warms the implementation
  account and the direct run does not, so the two access sets differ by
  construction.  A caller who charges off the access set will see a difference;
  that difference is a deviation, not a violation.

Neither exclusion is a convenience: each names a place where the proxied and the
direct run genuinely differ, and a correspondence that quietly asserted equality
there would be unprovable rather than strong. -/
def ObservablyEqual (proxy : Adr)
    (a b : Except (EvmError × Devm) Devm) : Prop :=
  match a, b with
  | .ok da, .ok db => ObservableAt proxy da db
  | .error ⟨ea, da⟩, .error ⟨eb, db⟩ => ea = eb ∧ ObservableAt proxy da db
  | _, _ => False

/-- **The observable distinguishes outcomes.**  A success and a failure are never
observationally equal, whatever they leave behind. -/
theorem observablyEqual_ok_error (proxy : Adr) (error : EvmError) (a b : Devm) :
    ¬ ObservablyEqual proxy (.ok a) (.error (error, b)) :=
  fun h => h.elim

/-- **And it is not everywhere true.**  Two successes with different output are
not observationally equal, so `ObservablyEqual` is a real comparison rather than
a predicate that accepts any pair. -/
theorem observablyEqual_output_sensitive (proxy : Adr) :
    ¬ ObservablyEqual proxy (.ok default)
        (.ok ((default : Devm).withOutput [0])) := by
  rintro ⟨output, -, -, -⟩
  exact absurd output (by decide)

/-- **P6(i).**  Every inbound message to the proxy behaves observably like the
same message run directly against the implementation's programme, with the
storage owner still the proxy.

The counterfactual changes exactly two fields — `codeAddress` and `code` —
and leaves `currentTarget` at the proxy.  That *is* "the implementation's
programme executed with storage owner = proxy", stated in Jaune's own message
vocabulary without inventing a notion.

**The two numeric premises exist for reasons found in Jaune's source, and are
carried explicitly rather than silently.**

* `depthHeadroom`.  `callMsg` sets `depth := sevm.depth - 1`, so behind a proxy
  the implementation runs one frame deeper than it would directly.  An
  implementation that calls out near the depth limit can therefore succeed
  directly and fail proxied.  `depthHeadroom ≤ m.depth` is what excludes that
  boundary; it is a real restriction on the claim, not a formality.
* `overhead`.  The proxy burns its prologue *before* `calculateMsgCallGas`
  applies the 63/64 cap, so the implementation always runs with strictly less
  gas behind a proxy than in front of one.  `overhead ≤ m.gas` is about the
  frame *reaching* the `DELEGATECALL` at all; completing within the forwarded
  budget is a separate obligation this statement does not discharge, and a
  caller must not read `overhead` as a sufficient gas figure. -/
def ProxyCorrespondence (proxy impl : Adr) (proxyProg implProg : Prog)
    (slot : B256) (overhead depthHeadroom : Nat) : Prop :=
  ∀ (m : Msg),
    m.currentTarget = proxy → m.codeAddress = some proxy →
    some m.code.toList = Prog.compile proxyProg →
    Devm.getStorVal (initDevm m) proxy slot = impl.toB256 →
    some ((initDevm m).getCode impl).toList = Prog.compile implProg →
    getDelegatedCodeAddress ((initDevm m).getCode impl) = none →
    overhead ≤ m.gas → depthHeadroom ≤ m.depth →
    ObservablyEqual proxy
      (exec (initEvm m))
      (exec (initEvm { m with codeAddress := some impl,
                              code := (initDevm m).getCode impl }))

/-! ## Satisfiability

A `Prop` that elaborates can still be vacuous.  `ProxyCorrespondence` is a
universally quantified implication with eight premises, and if no message could
meet all eight at once it would be true for uninteresting reasons.  The witness
below is an explicit `Msg`: the ERC-1967 proxy installed at `proxyAdr` with its
implementation slot naming `implAdr`, the implementation's compiled bytes
installed at `implAdr`, and gas and depth chosen above whatever thresholds the
caller names.

This establishes that the correspondence's guard is inhabited.  It does not
prove the correspondence. -/

/-- The world the witness message enters: the proxy's implementation slot names
`implAdr`, and `implAdr` carries the implementation's compiled runtime. -/
def witnessState : State :=
  (State.setStorVal .empty proxyAdr implementationSlotLit
    implAdr.toB256).setCode implAdr implCode

/-- An inbound message to the installed proxy, with the caller's own gas and
depth thresholds met by construction. -/
def witnessMsg (gas depth : Nat) : Msg :=
  { (default : Msg) with
    benv := { (default : Benv) with state := witnessState }
    currentTarget := proxyAdr
    codeAddress := some proxyAdr
    code := proxyCode
    gas := gas
    depth := depth }

theorem witnessState_get_proxy_slot :
    Devm.getStorVal (initDevm (witnessMsg 0 0)) proxyAdr implementationSlotLit
      = implAdr.toB256 := by
  show ((witnessState.get proxyAdr).stor.get implementationSlotLit) = _
  rw [witnessState, State.setCode, State.get_set_ne _ (by decide),
    State.setStorVal, State.get_set_self, Stor.get_set_self]

theorem witnessState_get_impl_code :
    (initDevm (witnessMsg 0 0)).getCode implAdr = implCode := by
  show (witnessState.get implAdr).code = _
  rw [witnessState, State.setCode, State.get_set_self]

/-- **The premise set is simultaneously satisfiable.**  Every hypothesis of
`ProxyCorrespondence proxyAdr implAdr proxyProg implProg implementationSlotLit
overhead depthHeadroom` holds of one concrete message, for every pair of
thresholds. -/
theorem proxyCorrespondence_premises_satisfiable
    (overhead depthHeadroom : Nat) :
    ∃ m : Msg,
      m.currentTarget = proxyAdr ∧
      m.codeAddress = some proxyAdr ∧
      some m.code.toList = Prog.compile proxyProg ∧
      Devm.getStorVal (initDevm m) proxyAdr implementationSlotLit
        = implAdr.toB256 ∧
      some ((initDevm m).getCode implAdr).toList = Prog.compile implProg ∧
      getDelegatedCodeAddress ((initDevm m).getCode implAdr) = none ∧
      overhead ≤ m.gas ∧
      depthHeadroom ≤ m.depth := by
  refine ⟨witnessMsg overhead depthHeadroom, rfl, rfl, ?_, ?_, ?_, ?_,
    Nat.le_refl _, Nat.le_refl _⟩
  · show some proxyCode.toList = _
    rw [proxyProg_compile]
    simp [proxyCode, ByteArray.toList_eq_toList_data]
  · exact witnessState_get_proxy_slot
  · show some ((initDevm (witnessMsg 0 0)).getCode implAdr).toList = _
    rw [witnessState_get_impl_code, implProg_compile]
    simp [implCode, ByteArray.toList_eq_toList_data]
  · show getDelegatedCodeAddress ((initDevm (witnessMsg 0 0)).getCode implAdr)
      = none
    rw [witnessState_get_impl_code]
    exact implCode_notDelegation

/-! ## Transport

The point of stating the correspondence at message altitude is that an
account-level clause crosses it by *instantiation*.  A clause is a predicate on
a message and its outcome; it "respects" the observable when observationally
equal outcomes satisfy it alike.  Transport is then one `.mpr`. -/

/-- A clause is transportable exactly when it cannot distinguish observationally
equal outcomes. -/
def RespectsObservable (proxy : Adr)
    (P : Msg → Except (EvmError × Devm) Devm → Prop) : Prop :=
  ∀ (m : Msg) (a b : Except (EvmError × Devm) Devm),
    ObservablyEqual proxy a b → (P m a ↔ P m b)

/-- A representative account-level clause: the call succeeds and leaves the
proxy's storage word `key` holding `value`. -/
def SucceedsWithSlot (proxy : Adr) (key value : B256) :
    Msg → Except (EvmError × Devm) Devm → Prop :=
  fun _ result => ∃ post, result = .ok post ∧
    Devm.getStorVal post proxy key = value

theorem succeedsWithSlot_respectsObservable (proxy : Adr) (key value : B256) :
    RespectsObservable proxy (SucceedsWithSlot proxy key value) := by
  rintro m (⟨ea, da⟩ | da) (⟨eb, db⟩ | db) hobs
  · simp [SucceedsWithSlot]
  · exact hobs.elim
  · exact hobs.elim
  · constructor
    · rintro ⟨post, hpost, hval⟩
      obtain rfl : da = post := Except.ok.inj hpost
      exact ⟨db, rfl, (hobs.2.1 key).symm.trans hval⟩
    · rintro ⟨post, hpost, hval⟩
      obtain rfl : db = post := Except.ok.inj hpost
      exact ⟨da, rfl, (hobs.2.1 key).trans hval⟩

/-- **Transport is instantiation.**  A clause that respects the observable and
holds of the direct run holds of the proxied run, with no restatement of the
clause at proxy altitude. -/
theorem clause_transports_to_proxied_run
    {proxy impl : Adr} {proxyProgram implProgram : Prog} {slot : B256}
    {overhead depthHeadroom : Nat}
    (correspondence : ProxyCorrespondence proxy impl proxyProgram implProgram
      slot overhead depthHeadroom)
    (P : Msg → Except (EvmError × Devm) Devm → Prop)
    (respects : RespectsObservable proxy P)
    {m : Msg}
    (target : m.currentTarget = proxy)
    (codeAddress : m.codeAddress = some proxy)
    (installed : some m.code.toList = Prog.compile proxyProgram)
    (slotNames : Devm.getStorVal (initDevm m) proxy slot = impl.toB256)
    (implInstalled :
      some ((initDevm m).getCode impl).toList = Prog.compile implProgram)
    (notDelegation : getDelegatedCodeAddress ((initDevm m).getCode impl) = none)
    (gasRoom : overhead ≤ m.gas)
    (depthRoom : depthHeadroom ≤ m.depth)
    (direct : P m (exec (initEvm { m with codeAddress := some impl,
                                          code := (initDevm m).getCode impl }))) :
    P m (exec (initEvm m)) :=
  (respects m _ _ (correspondence m target codeAddress installed slotNames
    implInstalled notDelegation gasRoom depthRoom)).mpr direct


/-! # Part C — row P6(ii): upgrade equivalence

**Shape only.**  Nothing below is proved, and no satisfiability witness is
claimed for it.

The shape is over a `(v1, v2, migration)` triple: from a pre-state whose
ERC-1967 slot names `v1adr`, an upgrade message executed against the proxy
leaves the slot naming `v2adr`, and every subsequent inbound message's
observable outcome stands in a relation `R` to what that message's outcome would
have been under `v1`.

**`R` is a parameter, and choosing it is a product decision reserved to the
successor under user authority.**  Three choices are coherent, and they are not
interchangeable:

1. **Full observable equality on the pre-existing surface** — the upgrade is
   invisible to every caller of every selector `v1` served.  Strongest, and
   false for any upgrade that changes behaviour on purpose.
2. **Equality on a named storage projection plus a named selector set** — the
   upgrade preserves a stated slice of the state and a stated part of the
   interface, and is free elsewhere.  This is what a real migration usually
   claims.
3. **Preservation of a stated invariant only** — the upgrade may change every
   observable, provided a named property (solvency, an access-control
   predicate, a supply identity) survives it.

Which one a Blanc proxy claims determines what a migration may do, and that is a
statement about the product rather than about the semantics.  It is therefore
not settled here.

What the shape deliberately does *not* pin: whether the migration reaches the
proxy through the proxy's own forwarding code or through a separate admin path.
Both are expressible as "an upgrade message executed against the proxy", and
choosing between them is part of the same reserved decision. -/

def UpgradeEquivalent (proxy v1adr v2adr : Adr) (v1 v2 migration : Prog)
    (slot : B256) (R : Except (EvmError × Devm) Devm →
                      Except (EvmError × Devm) Devm → Prop) : Prop :=
  ∀ (upgrade : Msg) (upgraded : Devm),
    -- the pre-state: the slot names `v1adr`, and both versions are installed
    upgrade.currentTarget = proxy →
    Devm.getStorVal (initDevm upgrade) proxy slot = v1adr.toB256 →
    some ((initDevm upgrade).getCode v1adr).toList = Prog.compile v1 →
    some ((initDevm upgrade).getCode v2adr).toList = Prog.compile v2 →
    -- the upgrade message runs the migration programme against the proxy
    some upgrade.code.toList = Prog.compile migration →
    exec (initEvm upgrade) = .ok upgraded →
    -- (a) the slot now names `v2adr`
    Devm.getStorVal upgraded proxy slot = v2adr.toB256 ∧
    -- (b) every subsequent inbound message is `R`-related to its `v1` outcome
    ∀ later : Msg,
      later.currentTarget = proxy →
      later.benv.state = upgraded.state →
      R (exec (initEvm { later with codeAddress := some v2adr,
                                    code := upgraded.getCode v2adr }))
        (exec (initEvm { later with codeAddress := some v1adr,
                                    code := upgraded.getCode v1adr }))


/-! # Trust surface

Every theorem stated in this file, in order.  A subset of
`[propext, Classical.choice, Quot.sound]` is the pass; any `sorryAx`,
`Lean.ofReduceBool` or `Lean.ofReduceNat` is a failure. -/

#print axioms proxyAdr_ne_implAdr
#print axioms implProg_compiles
#print axioms implProg_compile
#print axioms implCode_notDelegation
#print axioms implBodyGas_eq
#print axioms proxyProg_compiles
#print axioms proxyProg_compile
#print axioms slot_write_attributed_to_implementation
#print axioms successful_slot_write_attributed_to_implementation
#print axioms exactInvocation_roles_not_fusable
#print axioms implMain_walk
#print axioms delcall_frame_sstore_attributed
#print axioms proxyProg_entrySstoreFree
#print axioms implProg_not_entrySstoreFree
#print axioms proxy_frame_reaches_no_sstore
#print axioms slot_write_authority
#print axioms observablyEqual_ok_error
#print axioms observablyEqual_output_sensitive
#print axioms witnessState_get_proxy_slot
#print axioms witnessState_get_impl_code
#print axioms proxyCorrespondence_premises_satisfiable
#print axioms succeedsWithSlot_respectsObservable
#print axioms clause_transports_to_proxied_run

end Blanc.ProxySpikeShapes
