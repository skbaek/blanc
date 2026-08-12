# Security policy

## Read this first: Blanc emits bytecode, and a Blanc proof is not a deployment audit

Blanc compiles contracts to EVM runtime bytecode, and several of the contracts
in this repository are reimplementations of contracts that exist on mainnet.
Neither fact makes anything here safe to deploy.

A Blanc theorem is a statement about **Jaune's modeled semantics** — that a
program, compiled by Blanc's verified compiler, has a stated property when
executed by Jaune's EVM. It is not a statement about the Ethereum network, and
it is not an audit. In particular:

- **A port is not the original.** Where a Blanc contract reimplements a
  deployed one, it observably diverges from it. What a port does and does not
  claim is governed by [`PORTING.md`](PORTING.md), and every known divergence
  is registered in the `*_DEVIATIONS.md` files at this repository's root. Read
  the registry for the contract before comparing it to anything deployed.
- **The proofs inherit Jaune's trust base**, plus the pinned Jaune revision,
  the axiom audit, and the imported-source trust gate. See
  [`TRUSTED.md`](https://github.com/skbaek/jaune/blob/main/TRUSTED.md) and this
  repository's README under *Verification status*.
- **No contract here has been audited for deployment by anyone**, and no
  economic, governance, upgrade, or operational property is claimed beyond the
  theorems actually stated.

If you deploy bytecode produced by this repository, that is entirely your
decision and your risk.

## What to report

Report publicly, as an ordinary issue:

- **A proof that is weaker than the prose describing it** — in the README, in a
  module docstring, or on <https://skbaek.github.io/blanc/>. This is the report
  this project most wants to receive. Overstated claims are the failure mode
  the whole development is built to avoid, and an outside reader finding one is
  the strongest evidence the discipline is working.
- A divergence from a deployed original that is **not** in the relevant
  `*_DEVIATIONS.md` registry.
- A gate that passes when it should fail, or an axiom audit that admits a
  result it should reject.
- A compiler bug: a source program whose compiled bytecode does not behave as
  the source semantics say it should.

## What to report privately

Email **seulkeebaek@gmail.com** if you believe a defect here creates risk for
someone who has already deployed something derived from this repository. There
is no bug bounty. Expect an acknowledgement within about a week.

## Supported versions

Blanc is developed on `main` against a pinned Jaune revision and a pinned
toolchain. There are no long-lived release branches, and no version other than
`main` receives fixes.
