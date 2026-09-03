#!/usr/bin/env python3
"""An independent exact-integer model of the PRORATA WETH vault.

Written from the frozen statement in `~/plans/reports/prorata-erc4626-port-sf.md`
§4 — the formulas, the capacity policy and the revert classes — and *not* from
the Lean development.  That independence is the point: this module exists to
disagree with the proofs if either side is wrong, so it must not be derived
from them.  Nothing here is ever reflected into a Lean proposition; it produces
evidence, not theorems.

Arithmetic is Python integers and floor division only.  There is no floating
point anywhere in this file, and every division is written as an explicit
floor or ceiling so a reader can check the rounding direction against the SF
table without knowing Python's operator conventions.
"""
from __future__ import annotations

from dataclasses import dataclass, field

U = 2 ** 256 - 1
"""The largest EVM word."""

O = 1000
"""The virtual-share offset, frozen at G1."""

MAX_SUPPLY = U - O
"""The root invariant maintains `S <= U - O`, so `D` is a nonzero word."""


class Revert(Exception):
    """A whole-call rollback.  `cls` names the frozen revert class."""

    def __init__(self, cls: str) -> None:
        super().__init__(cls)
        self.cls = cls


def floor_div(n: int, d: int) -> int:
    """Mathematical floor division, for nonnegative operands."""
    assert d > 0 and n >= 0
    return n // d


def ceil_div(n: int, d: int) -> int:
    """Mathematical ceiling division, for nonnegative operands."""
    assert d > 0 and n >= 0
    return -((-n) // d)


def denominator(supply: int) -> int:
    """`D = S + O`.  Nonzero because the root invariant caps `S` at `U - O`."""
    return supply + O


def numerator(assets: int) -> int:
    """`X = A + 1`, a mathematical integer in `[1, 2^256]`.

    The `A = U` case is why this is not a word: the model keeps it exact
    rather than wrapping, exactly as the SF requires of the implementation.
    """
    return assets + 1


def representable(value: int) -> int:
    """A conversion result that exceeds `U` cannot be returned."""
    if value > U:
        raise Revert("unrepresentable")
    return value


# --- the four exact conversions, in the SF's own order and rounding ---

def convert_to_shares(a: int, assets: int, supply: int) -> int:
    """`a * D / X`, rounded down."""
    return representable(floor_div(a * denominator(supply), numerator(assets)))


def preview_mint(s: int, assets: int, supply: int) -> int:
    """`ceil(s * X / D)`."""
    return representable(ceil_div(s * numerator(assets), denominator(supply)))


def convert_to_assets(s: int, assets: int, supply: int) -> int:
    """`s * X / D`, rounded down."""
    return representable(floor_div(s * numerator(assets), denominator(supply)))


def preview_withdraw(a: int, assets: int, supply: int) -> int:
    """`ceil(a * D / X)`."""
    return representable(ceil_div(a * denominator(supply), numerator(assets)))


preview_deposit = convert_to_shares
preview_redeem = convert_to_assets


# --- capacity policy ---

def share_room(supply: int) -> int:
    return MAX_SUPPLY - supply


def max_mint(receiver: int, assets: int, supply: int) -> int:
    """`0` for the zero receiver, else `min(shareRoom, floor(U * D / X))`.

    The second cap is the largest `s` whose `previewMint` is representable:
    `ceil(s*X/D) <= U` exactly when `s <= floor(U*D/X)`.
    """
    if receiver == 0:
        return 0
    return min(share_room(supply),
               floor_div(U * denominator(supply), numerator(assets)))


def max_deposit(receiver: int, assets: int, supply: int) -> int:
    """`0` for the zero receiver, else `min(U, ceil((shareRoom+1)*X/D) - 1)`.

    The largest word `a` with `floor(a*D/X) <= shareRoom`; a tight bound, not
    a loose one.
    """
    if receiver == 0:
        return 0
    return min(U, ceil_div((share_room(supply) + 1) * numerator(assets),
                           denominator(supply)) - 1)


def max_redeem(owner_balance: int) -> int:
    return owner_balance


def max_withdraw(owner_balance: int, assets: int, supply: int) -> int:
    return floor_div(owner_balance * numerator(assets), denominator(supply))


@dataclass
class Vault:
    """Vault share ledger plus the WETH row the vault owns.

    `weth` is the whole WETH balance map, because a deposit debits the caller's
    row and credits the vault's; a model that tracked only the vault's row
    could not tell a real transfer from a donation.
    """

    supply: int = 0
    balances: dict[int, int] = field(default_factory=dict)
    allowances: dict[tuple[int, int], int] = field(default_factory=dict)
    weth: dict[int, int] = field(default_factory=dict)
    weth_allowances: dict[tuple[int, int], int] = field(default_factory=dict)
    vault_address: int = 1
    logs: list = field(default_factory=list)

    # --- views ---

    def total_assets(self) -> int:
        return self.weth.get(self.vault_address, 0)

    def balance_of(self, who: int) -> int:
        return self.balances.get(who, 0)

    def allowance(self, owner: int, spender: int) -> int:
        return self.allowances.get((owner, spender), 0)

    # --- internal ledger moves, with the exact frozen checks ---

    def _credit(self, who: int, amount: int) -> None:
        after = self.balance_of(who) + amount
        if after > U:
            raise Revert("balance-overflow")
        self.balances[who] = after

    def _debit(self, who: int, amount: int) -> None:
        if self.balance_of(who) < amount:
            raise Revert("insufficient-balance")
        self.balances[who] = self.balance_of(who) - amount

    def _weth_move(self, src: int, dst: int, amount: int) -> None:
        if self.weth.get(src, 0) < amount:
            raise Revert("weth-insufficient-balance")
        self.weth[src] = self.weth.get(src, 0) - amount
        after = self.weth.get(dst, 0) + amount
        if after > U:
            raise Revert("weth-balance-overflow")
        self.weth[dst] = after

    def _spend_weth_allowance(self, owner: int, spender: int, amount: int) -> None:
        if owner == spender:
            return
        current = self.weth_allowances.get((owner, spender), 0)
        if current == U:
            return
        if current < amount:
            raise Revert("weth-insufficient-allowance")
        self.weth_allowances[(owner, spender)] = current - amount

    def _spend_share_allowance(self, owner: int, spender: int, amount: int) -> None:
        if owner == spender:
            return
        current = self.allowance(owner, spender)
        if current == U:
            return
        if current < amount:
            raise Revert("insufficient-allowance")
        self.allowances[(owner, spender)] = current - amount

    def _mint(self, receiver: int, shares: int) -> None:
        if shares > share_room(self.supply):
            raise Revert("supply-cap")
        self._credit(receiver, shares)
        self.supply += shares

    def _burn(self, owner: int, shares: int) -> None:
        self._debit(owner, shares)
        self.supply -= shares

    # --- the four flows ---

    def deposit(self, caller: int, a: int, receiver: int) -> int:
        if caller == 0:
            raise Revert("zero-caller")
        if receiver == 0:
            raise Revert("zero-receiver")
        assets, supply = self.total_assets(), self.supply
        shares = convert_to_shares(a, assets, supply)
        if shares > share_room(supply):
            raise Revert("supply-cap")
        self._spend_weth_allowance(caller, self.vault_address, a)
        self._weth_move(caller, self.vault_address, a)
        self._mint(receiver, shares)
        self.logs.append(("Transfer", 0, receiver, shares))
        self.logs.append(("Deposit", caller, receiver, a, shares))
        return shares

    def mint(self, caller: int, s: int, receiver: int) -> int:
        if caller == 0:
            raise Revert("zero-caller")
        if receiver == 0:
            raise Revert("zero-receiver")
        assets, supply = self.total_assets(), self.supply
        a = preview_mint(s, assets, supply)
        if s > share_room(supply):
            raise Revert("supply-cap")
        self._spend_weth_allowance(caller, self.vault_address, a)
        self._weth_move(caller, self.vault_address, a)
        self._mint(receiver, s)
        self.logs.append(("Transfer", 0, receiver, s))
        self.logs.append(("Deposit", caller, receiver, a, s))
        return a

    def withdraw(self, caller: int, a: int, receiver: int, owner: int) -> int:
        if caller == 0:
            raise Revert("zero-caller")
        if receiver == 0:
            raise Revert("zero-receiver")
        if owner == 0:
            raise Revert("zero-owner")
        assets, supply = self.total_assets(), self.supply
        shares = preview_withdraw(a, assets, supply)
        self._spend_share_allowance(owner, caller, shares)
        self._burn(owner, shares)
        self._weth_move(self.vault_address, receiver, a)
        self.logs.append(("Transfer", owner, 0, shares))
        self.logs.append(("Withdraw", caller, receiver, owner, a, shares))
        return shares

    def redeem(self, caller: int, s: int, receiver: int, owner: int) -> int:
        if caller == 0:
            raise Revert("zero-caller")
        if receiver == 0:
            raise Revert("zero-receiver")
        if owner == 0:
            raise Revert("zero-owner")
        assets, supply = self.total_assets(), self.supply
        a = convert_to_assets(s, assets, supply)
        self._spend_share_allowance(owner, caller, s)
        self._burn(owner, s)
        self._weth_move(self.vault_address, receiver, a)
        self.logs.append(("Transfer", owner, 0, s))
        self.logs.append(("Withdraw", caller, receiver, owner, a, s))
        return a

    # --- the share surface ---

    def transfer(self, caller: int, to: int, amount: int) -> bool:
        if caller == 0:
            raise Revert("zero-caller")
        if to == 0:
            raise Revert("zero-receiver")
        self._debit(caller, amount)
        self._credit(to, amount)
        self.logs.append(("Transfer", caller, to, amount))
        return True

    def transfer_from(self, caller: int, src: int, to: int, amount: int) -> bool:
        if caller == 0:
            raise Revert("zero-caller")
        if src == 0:
            raise Revert("zero-owner")
        if to == 0:
            raise Revert("zero-receiver")
        self._spend_share_allowance(src, caller, amount)
        self._debit(src, amount)
        self._credit(to, amount)
        self.logs.append(("Transfer", src, to, amount))
        return True

    def approve(self, caller: int, spender: int, amount: int) -> bool:
        if caller == 0:
            raise Revert("zero-caller")
        if spender == 0:
            raise Revert("zero-spender")
        self.allowances[(caller, spender)] = amount
        self.logs.append(("Approval", caller, spender, amount))
        return True

    def donate(self, giver: int, amount: int) -> None:
        """A third-party WETH transfer to the vault.  No share is minted."""
        self._weth_move(giver, self.vault_address, amount)

    # --- the ledger identity the Lean side proves ---

    def conserved(self) -> bool:
        return sum(self.balances.values()) == self.supply
