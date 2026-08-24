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

A Blanc port of X claims what a careful engineer means by saying a
contract was ported to another language — made exact, and nothing more
esoteric. The project began from a high-level understanding of what X is
for; implemented it in Blanc; and measured the result against the deployed
original. Throughout, the reference is read as the best available
*witness* of the contract's job — the artifact user expectations formed
around — never as its judge: authoritative evidence about what X is for,
not an authority on how the job must be done, and owed no deference in its
accidents or defects. The headline remains counterfactual: **were X being
written and deployed today, the Blanc implementation would be a better way
to build it.** That headline is carried by exactly three parts, and
nothing more:

- **Differential agreement on a stated corpus.** The port is tested
  against the reference under a published per-contract coverage criterion
  (WETH10's: 147 rows over all 27 selectors and the receive path, frozen
  in [WETH10_COMPATIBILITY.md](WETH10_COMPATIBILITY.md)). Fixture
  agreement is specification-checked differential testing on chosen
  inputs — not a proof, and not a liveness result (principle 5).
- **Proved specifications, each offered as intent.** Parts of that
  high-level understanding are stated as formal specifications and proved
  of the exact compiled bytes. Every specification and every differential
  expectation is individually offered as a statement of what X is for: an
  informed author or user, shown the item and what it entails, would
  recognize it as what the contract *should do*, not merely as a behavior
  the reference is known to have (the feature test, below). Contest any
  item and an answer is owed — that an item was written down is no
  defense of having written down the wrong thing.
- **Deviations declared and defended.** Known divergences from the
  reference are recorded in a per-contract registry (principle 4):
  non-exhaustive by nature, published when discovered rather than when
  challenged, kept to calibrate a reader's expectations. Each row carries
  one of three defenses — the difference is orthogonal to X's job; or it
  makes the port strictly better at that job; or it is the priced cost of
  a design that wins elsewhere — and some rows are strict improvements:
  smaller code, cheaper calls, an operation refused rather than a balance
  silently overwritten. The stance column says which defense a row rests
  on.

Deliberately not claimed: identity with the deployed X down to the last
idiosyncrasy; completeness of any list; and answerability for
specifications no one has written. No specification list is ever
finished, and the ideal X a contract's users carry — easy to point at in
its violations, impossible to write out in full — is not a satisfiable
specification: every implementation, the deployed original included, is a
trade-off against it. A port therefore answers for everything it wrote
down, and for anything it is shown (principle 4's discovered-difference
rule); it does not pre-accept burden for the unwritten. An earlier
version of this document did exactly that, and the policy note below
records why the undertaking was abandoned.

### The feature test

Whether a behavior is part of X's job is decided by one question, asked
throughout this document: would the contract's authors and users, shown
the behavior and what it entails, count it as what the contract *should
do* — a feature — rather than merely a behavior the contract is known to
have? Endorsement, not expectation, deliberately: an expert who knows a
contract's internals can fully expect a flaw or a pointless idiosyncrasy
while agreeing it is no feature, so familiarity with a behavior earns it
nothing here. The "shown what it entails" clause is load-bearing:
"approve succeeds for every address pair" sounds like pure intent, but
under a flat keyspace it entails writing through a third party's balance
slot on a hash collision, and Blanc's refusal instead is defended as a
priced design trade — the flat keyspace bought verifiability and size,
and fail-loud beat fail-silent — recorded in
[WETH_DEVIATIONS.md](WETH_DEVIATIONS.md), not as a claim that users
secretly wanted refusals.

The test is a heuristic for judgment, not a court. Asked in advance, it
selects what a port writes down: which specifications are worth stating
and proving, which differential expectations are worth asserting. Asked
about a recorded divergence, it shapes the row's defense. On the
contested frontier it decides nothing by itself — two informed people can
disagree about a marginal behavior, and this document no longer pretends
an instrument exists that settles such cases (see the policy note).

### Interface and accident

Some answers recur often enough to state once. They are not a second
criterion; each is the feature test already applied. The reference is
authoritative about what the contract is *for*; it is not authoritative
about how the job must be done.

The ABI surface, the event shapes indexers consume, and the semantics
ordinary callers depend on are demanded of any implementation of X:
interface — a port may not file their loss under "orthogonal." Code size,
code hash, exact gas consumed, and storage layout are demanded of nothing
— no author or user asks X to hash to a particular value or to keep
balances in a particular slot: accidents. What the claim deliberately
does not include, then, is continuity with reliance on those accidents. A
caller bound to one — a code-hash pin, a storage proof against WETH9's
slot scheme — has bound itself to the artifact rather than the contract,
and no reimplementation can or should satisfy it. (Precedent: the Blanc
WETH's balance slots are deliberately not WETH9's;
[WETH_DEVIATIONS.md](WETH_DEVIATIONS.md) records the choice and declines
any storage-layout compatibility claim.)

The labels are presumptions, not verdicts: they settle the routine cases
without a fresh survey. Where one is contested, or where a behavior fits
neither — how malformed calldata is handled, what a callee may hand back —
the label is not the argument. Run the feature test for the contract at
hand. Whether a reference decoder's behavior on a truncated dynamic tail
is demanded of X is a question about X, and two contracts may answer it
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
- An observable difference, once discovered, is dispositioned or it is a
  defect: either restore fidelity or record and defend the divergence.
  The registry is non-exhaustive as a matter of fact — no enumeration of
  another artifact's observable surface is ever known complete — but
  never as a matter of concealment: leaving a *known* difference
  unrecorded is the one prohibited move. Rows are published when a
  divergence becomes known, not when someone asks about it; a stance
  drafted only to answer a challenge is silence caught late. What the
  registry demands is that the project know and publish its own
  trade-offs before anyone asks for them. When it is unclear whether a
  difference is interface or accident, record it and argue it — default
  to declaring.
- The stance a row must sustain is principle 3's: an informed deployer
  shipping X today could sign off on the behavior. Each row names which
  of the three defenses it rests on — orthogonal to X's job, better at
  it, or a priced cost of a design that wins elsewhere — and not every
  recorded deviation is an improvement; the stance column says which are.
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
Where the stakes warrant it, the public boundary itself is frozen in a
compatibility contract with differential evidence
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

WETH10's committed holder-flow family has an equally exact Blanc-only
boundary. From a stable checkpoint, its proof-carrying Prague-only
`AccountedHistory` retains every applied block, the configured transition and
`applyBody` result, `BlockOutput`, ordinary transaction roots, and all four
system-message roots (beacon, history, withdrawal request, and consolidation
request). Its public fold discards failed or reverted effects at their actual
settlement boundary, including failed nested, outer, and top-level execution;
only committed effects enter the ledger. Every ordinary Prague-only reach from
the checkpoint admits such a history, and the history projects back to that
ordinary reach.

For natural-number checkpoint and later booked balances `B0` and `Bt`, that
family first proves that committed balance credits do not wrap, then proves
the gross equation
`B0 + ordinaryIn + selfTransfer + flashCredit = Bt + redeemed +
externalTransferredOut + selfTransfer + flashRepayment`. Exact same-receiver,
same-principal flash pairing and cancellation of the matched flash and
self-transfer terms then give
`B0 + ordinaryIn = Bt + redeemed + externalTransferredOut`, and therefore the
residual floor `B0 ≤ Bt + redeemed + externalTransferredOut` (together with
its truncated-subtraction and no-external-transfer forms). Here a debit is
only **runtime-authorized**: the ledger records the actual caller and the
direct, accepted allowance, or flash-settlement branch. It retains the raw
branch words separately from their normalized balance addresses, and exact
invocation evidence excludes `DELEGATECALL`/`CALLCODE` execution against
another storage owner and foreign lookalike slots or logs.

This holder-flow result assumes no `NoCollision` condition and says nothing
about holder consent or intent, allowance-value provenance, future
enabledness/liveness, or the successor's any-order claim. It does not verify
the deployed Solidity runtime. Concrete redemption fixtures are finite checks
of chosen histories; they neither construct a Lean `AccountedHistory` nor
widen the theorem's scope.

The Lido CircuitBreaker Registry-history family has an exact Blanc-only
boundary of the same kind. From a checkpoint at which the exact compiled
Blanc runtime is installed at an address and that address's storage admits a
`RegistryWitness`, every state reachable by the configured valid-chain
relation still has that exact runtime installed and still admits a
`RegistryWitness` — possibly a different one. The quantifier covers
arbitrary finite sequences of successful and reverting transactions and
arbitrary callee bytecode, including code that re-enters the same instance;
there is no target-honesty premise and no count or interval noninterference
premise. Its reader-facing corollaries deliver, at the reached state and at
the configured-chain and Prague rungs alike, the exact installed runtime, an
actual witness, membership and index equivalence at an arbitrary canonical
target, and global count conservation.

The history theorem itself takes that checkpoint as a hypothesis, and its
synthetic satisfiability exhibit remains a hand-built non-deployment. A
separate Blanc deployment-root family now discharges the hypothesis for one
exact official case: a valid base world, the frozen official constructor
arguments and full CREATE input, zero endowment, and a strict singleton type-2
Prague block whose configured transition succeeds. It derives the sender and
CREATE address, actual constructor/message/transaction/block execution,
successful receipt and three ordered constructor logs, empty requests, the
exact installed Blanc runtime and configuration slots, an empty Registry
witness, and a valid deployed context. Its root methods instantiate the
history theorem for every configured future reachable from that deployed
checkpoint.

The base and strict-envelope predicates carry valid context, sender recovery
and transaction checking, funding, gas/code-size, system-predeploy,
nonce/address, and block-shape obligations. The prepared context derives the
collision check after the system prefix, nonce increment, and fee debit. The
root theorem does not prove the named configured transition from no premises:
it takes the successful `stateTransitionUsing` equation and reconstructs the
body/poststate/receipt/root relationship from it.

This does not say that an arbitrary deployment establishes the checkpoint. It
does not cover arbitrary constructor parameters, co-blocks,
factory/proxy/clone/CREATE2 creation, nonzero endowment, arbitrary block shapes
or forks, signing-key or signature construction, transaction propagation or
historical mainnet inclusion, or the deployed Solidity bytecode. Because the invariant is
existential, nothing claims a transaction returns the entry list it began
with, and nothing produces a source-level history trace. The family states
nothing about count and expiry coherence at callback time, composes nothing
from the public `pause` entry through `setPauser`, and makes no liveness or
universal differential claim. Its reachability relation carries a bound of its own: a
block enters only when total wei plus that block's withdrawals stays below
`2 ^ 256`, so any history crossing that bound falls outside "every reachable
state" — a restriction the Registry invariant itself never consults. It does
not verify the deployed Solidity runtime; agreement with the pinned v1.0.0
reference rests on
[LIDO_CIRCUIT_BREAKER_COMPATIBILITY.md](LIDO_CIRCUIT_BREAKER_COMPATIBILITY.md)
and
[LIDO_CIRCUIT_BREAKER_DEVIATIONS.md](LIDO_CIRCUIT_BREAKER_DEVIATIONS.md).
The exact Blanc root is stated in
[LidoCircuitBreakerDeploymentRoot.lean](Blanc/LidoCircuitBreakerDeploymentRoot.lean).
A temporary pinned-EELS/Jaune replay checks one synthetic strict singleton
block as a separate finite channel. It is no Lean premise, and neither it nor
the finite differential manifest enlarges the Lean theorems or the
port-conformance claim.

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

## Policy change — 2026-08-19: the standing wager, retired

From this document's first version until 2026-08-19, principle 3 made its
functionality claim precise as a *standing wager*: produce a specification
that was (1) true of the deployed original and (2) a feature by the
feature test, and the project owed either a proof of it over the Blanc
port or a registry row predating the challenge; losing was public, the
burden was the project's, and "that was never claimed" was declared
unavailable. The aim was more ambitious than the claim that stands above —
a port answerable in advance for every feature-level truth of the deployed
original, enumerated or not.

The wager was retired, not narrowed, after concluding that the undertaking
fails in principle rather than in effort:

- **It promoted the reference to an index of obligations.** Condition 1
  made the deployed artifact the generator of the challenge set — the
  pool of properties the port could be held to. That contradicts the
  reference's actual standing (a witness of the contract's job, not its
  judge), and an instrument that only admits challenges true of the
  original can only ever ask the port to catch up to it — never to exceed
  it, which is the headline claim.
- **Its ground condition had no truth procedure.** "True of the deployed
  original" cannot be adjudicated against an artifact that has no
  specification — the very absence that motivates this project. For
  quantified properties the condition is undecidable in practice; the
  WETH registry itself records a collision branch "untestable by
  construction."
- **Its endorsement test could not adjudicate the contested cases.** The
  ideal X that users carry — easy to point at in its violations,
  impossible to write out in full — is not a satisfiable specification.
  Of a WETH it demands both that every well-formed allowance update
  succeed and that nothing ever write through a third party's balance
  slot; under Blanc's flat keyspace no implementation grants both, and
  the port chose refusal — a trade the reference's own layout makes
  differently, at prices of its own. Every implementation picks such
  poisons and pleads implementation reality for the ones it picked; no
  bright line separates a legitimate plea from a lame one; and an
  instrument whose loss condition turns on exactly that adjudication was
  never falsifiable in the way it advertised.

What replaces it is narrower and stated in principle 3: item-wise
answerability for everything the port wrote down, plus principle 4's
discovered-difference rule for anything it is shown. What survives
unchanged: the feature test as a selection heuristic, the registry
discipline with its publish-when-discovered norm, and principle 5's rule
that claims end where evidence ends — a rule the wager, a standing
commitment of burden with no evidence behind it, always sat uneasily
beside. Adjudications recorded while the wager stood (the 2026-08-09
value-rejection row in [WETH_DEVIATIONS.md](WETH_DEVIATIONS.md)) remain
valid records of their day and are marked where they cite it. The full
former text is in git history — this file as of commit `30f3f99`.

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
