# Porting policy

Blanc contracts often have a preexisting reference — WETH9, WETH10, a
Solidity original. The same questions recur in every such project and every
review of one: how closely must the Blanc artifact track the reference, and
which differences are defects? This document is the standing answer.
Principles 1–2 apply to all Blanc development; 3–5 apply whenever a
reference exists.

## 1. Byte-identity is a non-goal, permanently

Blanc does not, and will not, tune its output to reproduce bytecode built by
another toolchain. This is not a missing feature awaiting a roadmap slot; it
is out of scope by design. A compiler that chases another compiler's bytes
inherits every choice that compiler made — its dispatcher, its stack
discipline, its bugs — and can justify nothing beyond "same as before."
Reading deployed artifacts as *evidence* is a different matter and is
routine (see the disassembly provenance note in
[WETH_DEVIATIONS.md](WETH_DEVIATIONS.md)); what is excluded is making their
bytes the compilation target. Directly verifying a reference artifact is a
third thing again — worth doing, and a project someone should undertake, but
not one a Blanc port undertakes or claims (principle 5).

## 2. What Blanc optimizes instead

Blanc exists to produce better bytecode than the reference, not identical
bytecode. Better, concretely:

- **conformant** — behavior follows a high-level specification of what the
  contract is for, stated and proved in Lean;
- **verifiable** — the artifact stays within practical reach of interactive
  formal verification;
- **improved where improvement is measurable** — the language leaves the
  implementer broad low-level freedom, and that freedom is spent on
  objective wins where they exist: smaller code, cheaper execution.

When fidelity to a reference conflicts with any of these, fidelity loses,
and the conflict is recorded (principle 4).

## 3. What "contract X, implemented in Blanc" claims

A Blanc port of X does not claim identity with the deployed X down to the
last idiosyncrasy. The claim is counterfactual: **were X being written and
deployed today, the Blanc implementation would be a better way to build
it.** The claim is exactly the conjunction of three parts, and nothing more:

- it retains every functionality that matters — a claim made precise
  below as a standing wager, not as a completed enumeration;
- its deviations from the reference are all documented (principle 4), and
  each is one an informed deployer shipping X today could sign off on:
  unremarkable had it been the behavior from day one, or an accepted cost
  of a design that wins elsewhere — with the registry's stance column
  saying which;
- and some deviations are strict improvements: smaller code, cheaper
  calls, an operation refused rather than a balance silently overwritten.

### The functionality claim is a standing wager

A comprehensive specification capturing everything a contract is for is an
elusive goal. This project has not achieved one for its ports and, for
many contracts, never will — and a blanket "the specifications could be
written and proved if desired" would earn the fair retort "then why
weren't they." What is offered instead is falsifiable. Produce a
specification that

1. is **true of the deployed original**, and
2. **captures the contract's intent**: shown the specification and what it
   entails, the contract's authors and users would agree it states a
   *feature* — what the contract should do — not merely a behavior the
   contract is known to have,

and the wager is that the specification either holds of the Blanc
implementation, provably, or is already covered by a registry row that
priced the trade (principle 4). The burden is the project's, and it may
never be discharged with "that was never claimed."

The second branch carries a timestamp requirement: the row must predate the
challenge. A stance invented to answer one is silence caught late, which
principle 4 prohibits outright. What the wager demands is therefore that
the project know and publish its own trade-offs before anyone asks for
them.

A specification that holds of the Blanc port but resists proof is a
different failure, and there difficulty is no defense: verifiability is
itself a claim (principle 2), and a true property the artifact puts beyond
practical reach falsifies it.

Condition 2 asks for endorsement, not expectation, deliberately: an expert
who knows a contract's internals can fully expect a flaw or a pointless
idiosyncrasy while agreeing it is no feature, so familiarity with a
behavior earns it nothing here.

Condition 2 also does constructive duty, and it is the same test either
way. Asked in advance — would an informed author or user demand this of X?
— it is how a port decides what it owes before anyone challenges anything;
the answers that recur are collected below. Asked after the fact, it is how
a challenge is adjudicated. Nothing else adjudicates what a port owes: not
resemblance to the reference, and not a category a behavior appears to fall
into.

The deviation registries are the wager's priced-in exceptions, and a stance
(principle 4) answers the wager in one of two ways: by arguing that
condition 2 fails for the behavior — an informed author or user would not
count it a feature of the contract — or by conceding that it holds and
stating what the trade bought. The stance column says which. Disagreement
goes through the stance, never through silence: a failing intent-level
specification covered by no registry row is the wager lost. The "shown what
it entails" clause is load-bearing: "approve succeeds for every address
pair" is true of WETH9 and sounds like pure intent, but it quantifies over
the hash collisions where a flat keyspace must choose between refusing the
call and writing through a third party's balance slot — and an informed
user, shown that entailment, prefers the refusal recorded in
[WETH_DEVIATIONS.md](WETH_DEVIATIONS.md).

### Interface and accident

Some answers recur often enough to state once. They are not a second
criterion; each is the feature test already applied. The reference is
authoritative about what the contract is *for*; it is not authoritative
about how the job must be done.

The ABI surface, the event shapes indexers consume, and the semantics
ordinary callers depend on are demanded of any implementation of X:
interface. Code size, code hash, exact gas consumed, and storage layout are
demanded of nothing — no author or user asks X to hash to a particular value
or to keep balances in a particular slot: accidents. What the claim
deliberately does not include, then, is continuity with reliance on those
accidents. A caller bound to one — a code-hash pin, a storage proof against
WETH9's slot scheme — has bound itself to the artifact rather than the
contract, and no reimplementation can or should satisfy it. (Precedent: the
Blanc WETH's balance slots are deliberately not WETH9's;
[WETH_DEVIATIONS.md](WETH_DEVIATIONS.md) records the choice and declines any
storage-layout compatibility claim.)

The labels are presumptions, not verdicts: they settle the routine cases
without a fresh survey. Where one is contested, or where a behavior fits
neither — how malformed calldata is handled, what a callee may hand back —
the label is not the argument. Run the test for the contract at hand.
Whether a reference decoder's behavior on a truncated dynamic tail is
demanded of X is a question about X, and two contracts may answer it
differently.

## 4. Deviations are governed, not forbidden

A port may diverge from its reference, and should where divergence is an
improvement. The freedom is paid for in bookkeeping:

- Every known observable deviation is recorded in a per-contract registry —
  reference semantics, Blanc semantics, observable consequence, project
  stance, evidence. [WETH_DEVIATIONS.md](WETH_DEVIATIONS.md),
  [WETH10_DEVIATIONS.md](WETH10_DEVIATIONS.md) and
  [FMINT_DEVIATIONS.md](FMINT_DEVIATIONS.md) are the practice this policy
  canonizes.
- An observable difference not in the registry is a defect: either restore
  fidelity or record and defend the divergence. Silence is the one
  prohibited move. When it is unclear whether a difference is interface or
  accident, record it and argue it — default to declaring.
- The stance a row must sustain is principle 3's: an informed deployer
  shipping X today would accept the behavior — as unremarkable from day
  one, or as a stated cost of a design that wins elsewhere. Not every
  recorded deviation is an improvement, and the stance column says which
  are. A stance is thereby also the row's answer to principle 3's standing
  wager: a public argument that condition 2 fails for the behavior, or a
  public concession that it holds, with the compensating win named.
- Improvement claims are measured, not asserted: bytes are counted, gas is
  measured on named paths. A behavioral change is never filed under
  "optimization"; it enters the registry with its own defense.
- A gas increase on an externally callable path is a deviation like any
  other, recorded and defended. This is the feature test, not an exception
  to it: nobody demands that X cost exactly what it costs today, but
  cheapness on public paths is demanded, and contracts that forward fixed
  gas exist, so a costlier path can break real callers. Whether a *decrease*
  is equally observable is argued per contract — one that forwards its
  remaining gas to callbacks forwards more when its own path gets cheaper,
  while a stipend-limited send forwards the same either way.
- A registry row is not a verdict; it is where the argument stands to be
  examined.

## 5. Claims end where evidence ends

Two instruments produce a port's evidence, and they establish different
things. The Lean theorems are about Blanc: unless a theorem says otherwise,
it applies to the named Blanc program and, where a compiler witness is
provided, to that program's exact generated runtime, under the pinned Jaune
semantics and the theorem's own hypotheses. It proves nothing about the
reference deployment, which no Blanc port undertakes to verify (principle
1). Agreement with the reference comes from the fixtures instead, and
fixture agreement is specification-checked differential testing on chosen
inputs — not a proof, and not a liveness result.

A port's conformance claim is therefore exactly this: the properties proved
of the Blanc artifact, the behaviors differentially tested against the
reference, and the recorded deviations. State what was checked; stop there.
(Principle 3's wager is a commitment of burden, not a claim of completed
evidence; it creates obligations, never evidence.) Where the stakes warrant
it, the public boundary itself is frozen in a compatibility contract with
differential evidence
([WETH10_COMPATIBILITY.md](WETH10_COMPATIBILITY.md)).

WETH10's deployment root follows the same boundary. Its theorem establishes
the freshly generated Blanc runtime and `Weth10.Stable` after one strict,
collision-free singleton type-2 deployment through the configured Prague
transition, under its explicit valid-context, funding, gas, arithmetic, and
system-predeploy premises. It does not establish the deployed Solidity
artifact, construct or custody a signing key, guarantee propagation or block
inclusion, or cover arbitrary co-block, factory, CREATE2, endowment, or fork
shapes. The executable deployment fixture witnesses one concrete transaction
and receipt; it does not enlarge the theorem or the port-conformance claim.

Two registers are available for what a port has not established, and only
one of them is honest. Declaring a non-claim in advance — this boundary is
not covered, this property is not attempted — bounds the claim and asserts
nothing; the registries' exclusion sections are made of it. Asserting a
property the port has not proved is the other register, and it is never
available: it is what every unverified contract already offers, and
admitting it here would concede the thing that makes the work worth doing.
When a property resists proof, claim less rather than assert more.

Where such a property is nonetheless believed to hold and matters enough to
say so, it is recorded as a verification debt against principle 2, with
whatever informal argument supports it. The record discharges nothing. It is
not a stance and may never be cited as one: a deviation row settles a
question, while a debt only makes an absence public, and the sole way to end
one is to prove the property and delete the record. Debts are therefore
counted — a lengthening list of them is a fact about the project, where a
lengthening deviation registry is not.

## Precedent: WETH9

The Blanc WETH is several times smaller than the deployed WETH9 and cheaper
on the call paths measured, and where its simpler storage scheme introduces
a key-collision possibility WETH9's layout cannot express, it refuses the
operation rather than silently overwriting a balance (the fail-on-collision
row in [WETH_DEVIATIONS.md](WETH_DEVIATIONS.md)). Each of these is a
deviation from the letter of the reference, and each is a feature: no user
wants larger code, dearer calls, or silent writes through a collision.
Rejecting them for the sake of resemblance would have been an error. That
judgment — made once for WETH9 — is this policy.
