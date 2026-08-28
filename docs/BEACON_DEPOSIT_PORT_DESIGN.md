# Beacon deposit port — frozen implementation design

This note is the implementation-facing acceptance map for the compiled port.
The pinned source and the opening report's §B1.7 remain authoritative if this
note is wrong. It describes Blanc's own artifact, not the deployed artifact.

## Program and storage

The runtime has exactly four selector leaves, in ascending order, followed by
one shared empty-revert no-match auxiliary:

| Selector | Endpoint | Payability |
|---|---|---|
| `01ffc9a7` | `supportsInterface(bytes4)` | nonpayable |
| `22895118` | `deposit(bytes,bytes,bytes,bytes32)` | payable |
| `621fd130` | `get_deposit_count()` | nonpayable |
| `c5f2892f` | `get_deposit_root()` | nonpayable |

Blanc uses three compact disjoint storage regions for reachable indices:

```text
branch[h]     = 0x100 + h,  0 <= h < 32
deposit_count = 0x200
zero_hashes[h]= 0x300 + h,  0 <= h < 32
```

This is deliberately not Solidity's raw layout.  `accOfStor` is a total
projection from every concrete store: its branch function reads the first
region and its count is the `toNat` image of slot `0x200`.  It carries no
count bound, invariant, outside-region-zero premise, or constructor premise.
A separate `ZeroHashesCorrect` predicate fixes
`zero_hashes[h] = zeroHash Bytes.sha256 h` for `h < 32`; the model-root view
is a corollary of the more general concrete-storage view under that named
predicate.

## Dynamic ABI boundary

The decoder is a separate phase before every source-level guard. It first
requires the four-word head (`calldatasize >= 132`), then validates all three
dynamic tails. For each offset word it requires:

```text
offset < 2^32
36 + offset <= calldatasize
length := calldataload(4 + offset)
length < 2^32
36 + offset + ceil32(length) <= calldatasize
```

Offsets may be reordered or overlap; padding contents and trailing calldata
are ignored. These checks model the pinned solc decoder's 32-bit offset/length
boundary without defining decoding as “whatever this program reads.” Every
structural failure uses the shared empty-data reverter. Only after all three
tails are decodable does the body test, in source order, lengths 48/32/96,
the three value guards, reconstructed root, and count cap.

The statement layer distinguishes:

- a canonical encoder `abiDepositCall`, used by the flagship P2/P3 theorems;
- a machine-facing `DepositAbiDecodable`, matching the checks above;
- a proved implication from canonical encodings (under their explicit
  machine-width bound) to machine decodability;
- an undecodable-calldata empty-revert theorem.

The differential campaign owns the exact noncanonical comparison boundary;
any mismatch it discovers is a registry row, never an implicit exception.

## Event

`DepositEvent(bytes,bytes,bytes,bytes,bytes)` has topic
`649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5`.
The program stages five head offsets (`160,256,320,384,512`) and tails for
pubkey, withdrawal credentials, amount, signature, and old-count index. It
explicitly zeroes both partial-word padding regions and emits one `LOG1` over
memory `[0,576)`. The event is staged after the first six guards and before
root/cap validation. A later revert retains both the raw frame-local `LOG`
occurrence and the reverted `Devm` log field.  It is not a retained occurrence,
and the enclosing call/top-level output exposes no child log.  Proof statements
keep all three levels distinct instead of calling the raw trace log-free.

## SHA-256 sites

Every hash call uses `STATICCALL` to address `0x2`, with input size 64 and
output size 32. The program retains all twelve source-shaped sites:

- constructor zero-hash loop: one site;
- root fold: live and zero arms as two sites, plus the count mix-in;
- deposit reconstruction: seven sites;
- insertion walk: one site.

The proof boundary names the pinned fork's precompile selection and absence of
an EIP-7702 delegation designator at address `0x2`; it proves the 64-byte child
input and instantiates the result exactly as `Bytes.sha256 input`. These are
explicit environment facts, not a hash axiom. A failed call takes the shared
`Func.revReturnData` auxiliary and therefore bubbles the child returndata
byte-for-byte (with empty returndata as the ordinary empty-revert subcase).
A successful child response shorter than 32 bytes instead takes the shared
empty reverter; responses of at least 32 bytes use the first output word.
These two arms match the pinned solc wrapper.

The runtime memory ownership is fixed as follows. Words `0..17` hold the
complete event image through `LOG1` and may then be reused as hash input.
Words `18`, `19`, `20`, and `21` retain the old count, shifted insertion/root
size, current node, and numeric deposit amount. Words `22` and `23` are hash
intermediates. Deposit reconstruction consumes seven distinct call sites in
source order: pubkey root, the two signature halves, signature root, the
pubkey/withdrawal child, the amount/signature child, and the final data root.
The insertion loop owns an eighth deposit call site. The root fold writes each
digest directly to word `20`; its final mix-in uses words `0..1`.

The runtime auxiliary table is append-only at these coordinates:

```text
1  empty fallback / structural rejection
2  full-returndata bubble
3..10  eight Error(string) reason auxiliaries, in source order
11 root loop
12 root continuation
13 insertion loop
14 insertion continuation
```

The constructor has an independent compiled table: slot `1` empty-reverts,
slot `2` bubbles returndata, slot `3` is the zero-hash loop, and slot `4` its
continuation. Its loop writes the digest output directly to the retained node
word before storing `zero_hashes[h+1]`.

## Loop boundaries

The root fold is exactly 32 iterations and the constructor exactly 31. The
insertion loop has no compiled terminal `assert` arm: after the cap guard its
incremented count is nonzero below `2^32`, so a set bit is found within 32
shifts; `deposit_ne_assert_false` licenses this omission at the model bridge.
The loop realization (tail-recursive auxiliary slots or unroll) remains
pending the exclusive first-slice measurement recorded in
`BEACON_DEPOSIT_COST.md`.

Write statements distinguish raw from settled evidence. A reverting root has
no retained storage writes by settlement alone, which does not prove that a
guard preceded every store. Each of the eight deposit guard theorems therefore
also proves `NoRawSstore`: every raw instruction occurrence differs from
`SSTORE`. The success and constructor theorems compare the chronological
`(owner,key,value)` projection of retained writes, so no-op `SSTORE`s still
count and proof-node identity cannot obscure cardinality.

## Module boundary

The intended sibling family is:

```text
BeaconDepositCore       storage/ABI/event/error vocabulary
BeaconDeposit           executable runtime
BeaconDepositCode       compiler witness, selectors, sizes, inventories
BeaconDepositDeploy     constructor and creation artifact
BeaconDepositEncoding   canonical ABI/event and LE64 facts
BeaconDepositSha256     address-2 precompile crossing
BeaconDepositEffects    P2/P3/P4 compiled effects
BeaconDepositWrites     P5 complete SSTORE classification
BeaconDepositBridge     P6 storage abstraction and invariant transfer
```

Additional contract-local proof modules may split long walks, but no module in
this family imports another contract family. P7's deployment-root transition
and P8 history/open-frame results remain successor work.
