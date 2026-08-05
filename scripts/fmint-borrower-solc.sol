// SPDX-License-Identifier: MIT
//
// The one borrower in this suite that Blanc did not compile.
//
// Every other member of the zoo (`scripts/gen-fmint-borrowers.lean`) is a
// Blanc program compiled by Blanc's own compiler, so `onFlashLoan`'s five
// arguments are adjudicated by a decoder that shares its authorship with the
// encoder under test: a shared encoder/decoder defect would decode the wrong
// bytes back into exactly the expected values and every assertion would still
// pass. Nor does `Blanc.fmint_flashLoan_spec` close that circle -- it proves
// the callback's CALL window equals *Blanc's definition* of the canonical ABI
// encoding, so a definition that misstates the standard leaves the theorem
// true and the divergence unseen.
//
// `solc`'s ABI decoder is an independent implementation of that standard,
// which is the one thing no Lean theorem in this repository can be. Its
// prologue is doing real work here and it is the point of the file:
//
//   * it rejects calldata shorter than the five-word head;
//   * it rejects an `address` argument whose top 96 bits are not zero;
//   * it rejects a `bytes` argument whose offset or length runs past
//     calldatasize;
//   * it computes `keccak256("ERC3156FlashBorrower.onFlashLoan")` itself,
//     from the string, at compile time.
//
// The evidence this buys is narrow and stated as such: one borrower, on
// chosen inputs, differentially checked. It is not a proof and not liveness.
// See `scripts/fixtures/fmint/README.md`, "The Solidity-compiled borrower".
//
// Storage layout is load-bearing. The eight observation slots below MUST land
// at 0..7 to match `scripts/gen-fmint-borrowers.lean`'s `OBS_*` idiom (and
// `gen-fmint-fixtures.py`'s `OBS_*` mirror of it), so the fixture asserts the
// same eight facts about this borrower that it asserts about the Blanc ones.
// That is why every one of them is a full `uint256` rather than an `address`:
// three `address` fields would be packed into one slot by the compiler.
//
// No constructor and no `immutable`. The fixture installs
// `evm.deployedBytecode` directly into a genesis account, so nothing a
// constructor did would survive; the lender is read from `msg.sender`, the
// same way every Blanc borrower reads it (fmint always calls a borrower
// directly, so the caller inside the callback IS the token).
//
// Regenerate the committed artifact with
// `scripts/gen-fmint-borrower-solc.py`; never hand-transcribe its bytes.
pragma solidity 0.8.36;

interface IERC20 {
    function approve(address spender, uint256 value) external returns (bool);

    function balanceOf(address account) external view returns (uint256);

    function totalSupply() external view returns (uint256);
}

interface IERC3156FlashBorrower {
    function onFlashLoan(
        address initiator,
        address token,
        uint256 amount,
        uint256 fee,
        bytes calldata data
    ) external returns (bytes32);
}

contract SolcBorrower is IERC3156FlashBorrower {
    uint256 private obsSender; // slot 0 -- OBS_SENDER
    uint256 private obsInitiator; // slot 1 -- OBS_INITIATOR
    uint256 private obsToken; // slot 2 -- OBS_TOKEN
    uint256 private obsAmount; // slot 3 -- OBS_AMOUNT
    uint256 private obsFee; // slot 4 -- OBS_FEE
    uint256 private obsDataHash; // slot 5 -- OBS_DATAHASH
    uint256 private obsBalSelf; // slot 6 -- OBS_BAL_SELF
    uint256 private obsSupply; // slot 7 -- OBS_SUPPLY

    /// The compliant success path, in the same order the Blanc
    /// `compliantBorrower` runs it: record, then approve, then return the
    /// magic. `balanceOf(self)` and `totalSupply()` are read *during* the
    /// callback deliberately -- under fee = 0 a successful loan returns the
    /// token's storage to its pre-state, so a mid-callback read is the only
    /// durable evidence that the mint happened before the callback ran.
    function onFlashLoan(
        address initiator,
        address token,
        uint256 amount,
        uint256 fee,
        bytes calldata data
    ) external override returns (bytes32) {
        IERC20 lender = IERC20(msg.sender);
        obsSender = uint256(uint160(msg.sender));
        obsInitiator = uint256(uint160(initiator));
        obsToken = uint256(uint160(token));
        obsAmount = amount;
        obsFee = fee;
        obsDataHash = uint256(keccak256(data));
        obsBalSelf = lender.balanceOf(address(this));
        obsSupply = lender.totalSupply();
        require(lender.approve(msg.sender, amount + fee), "approve failed");
        return keccak256("ERC3156FlashBorrower.onFlashLoan");
    }
}
