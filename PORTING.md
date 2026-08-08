# Porting policy

Blanc contracts often have a preexisting reference — WETH9, WETH10, a
Solidity original. The same questions recur in every such project and every
review of one: how closely must the Blanc artifact track the reference, and
which differences are defects? This document is the standing answer.
Principles 1–2 apply to all Blanc development; 3–6 apply whenever a
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
bytes the compilation target.

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
and the conflict is recorded (principle 5).

## 3. What "contract X, implemented in Blanc" claims

A Blanc port of X does not claim identity with the deployed X down to the
last idiosyncrasy. The claim is counterfactual: **were X being written and
deployed today, the Blanc implementation would be a better way to build
it.** The claim is exactly the conjunction of three parts, and nothing more:

- it retains every functionality that matters — a claim made precise
  below as a standing wager, not as a completed enumeration;
- its deviations from the reference are all documented (principle 5), and
  each is one an informed deployer shipping X today could sign off on:
  unremarkable had it been the behavior from day one, or an accepted cost
  of a design that wins elsewhere — with the registry's stance column
  saying which;
- and some deviations are strict improvements: smaller code, cheaper
  calls, an operation refused rather than a balance silently overwritten.

What the claim deliberately does not include is continuity with reliance
on the deployed artifact's accidents — its code hash, its storage image,
its exact gas. Principle 4 draws that line.

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

and the wager is that the specification holds of the Blanc implementation,
provably. The burden of proof is the project's, and difficulty is no
defense: a specification meeting both conditions that fails on the Blanc
port is a defect of the port, and one that holds but resists proof
falsifies the verifiability claim (principle 2). Neither may be answered
with "that was never claimed."

Condition 2 asks for endorsement, not expectation, deliberately: an expert
who knows a contract's internals can fully expect a flaw or a pointless
idiosyncrasy while agreeing it is no feature, so familiarity with a
behavior earns it nothing here.

The deviation registries are the wager's priced-in exceptions. Each stance
(principle 5) is in substance an argument that condition 2 fails for that
behavior — that an informed author or user would not count it a feature of
the contract. Disagreement goes through the stance, never
through silence: a failing intent-level specification covered by no
registry row is the wager lost. The "shown what it entails" clause is
load-bearing: "approve succeeds for every address pair" is true of WETH9
and sounds like pure intent, but it quantifies over the hash collisions
where a flat keyspace must choose between refusing the call and writing
through a third party's balance slot — and an informed user, shown that
entailment, prefers the refusal recorded in
[WETH_DEVIATIONS.md](WETH_DEVIATIONS.md).

## 4. The standard a port must meet

Follow the spirit of the law, not the letter. The reference is authoritative
about what the contract is *for*; it is not authoritative about how the job
must be done. The bar is **drop-in usability**: if the Blanc bytecode
replaced the deployed original, every normal use would keep working, and an
informed user or integrator inspecting the result would conclude "that is
contract X, doing its job in a different way."

A use is *normal* when it relies on what X is, not on how the deployed
artifact happens to be built — when it would work against any faithful
implementation of X. The ABI surface, the event shapes indexers consume,
and the semantics ordinary callers depend on are owed by any
implementation: interface. Code size, code hash, exact gas consumed, and
storage layout are properties of one implementation: accidents. A caller
bound to an accident — a code-hash pin, a storage proof against WETH9's
slot scheme — has bound itself to the artifact rather than the contract,
and no reimplementation can or should satisfy it. (Precedent: the Blanc
WETH's balance slots are deliberately not WETH9's;
[WETH_DEVIATIONS.md](WETH_DEVIATIONS.md) records the choice and declines
any storage-layout compatibility claim.)

One commitment goes beyond what the counterfactual strictly owes: gas
*ceilings*. Contracts that forward fixed gas exist, so while making a
public path cheaper is always safe, making one costlier can break real
callers — a gas increase on an externally callable path is therefore
treated as a deviation to defend like any other.

## 5. Deviations are governed, not forbidden

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
  are. A stance is thereby also the row's answer to the standing wager: a
  public argument that its condition 2 fails for the behavior in question.
- Improvement claims are measured, not asserted: bytes are counted, gas is
  measured on named paths. A behavioral change is never filed under
  "optimization"; it enters the registry with its own defense.
- A registry row is not a verdict; it is where the argument stands to be
  examined.

## 6. Claims end where evidence ends

A port's conformance claim is exactly this: agreement with the reference on
the properties proved and the behaviors tested, plus the recorded
deviations. It is never a claim of bit-identity, gas-identity, or code-hash
identity, and fixture agreement is specification-checked differential
testing on chosen inputs, not a liveness proof. State what was checked;
stop there. (Principle 3's wager is a commitment of burden, not a claim of
completed evidence; it creates obligations, never evidence.) Where the stakes warrant it, the public boundary itself is
frozen in a compatibility contract with differential evidence
([WETH10_COMPATIBILITY.md](WETH10_COMPATIBILITY.md)).

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
