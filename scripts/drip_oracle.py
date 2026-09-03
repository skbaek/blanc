#!/usr/bin/env python3
"""Exact integer reference semantics for the DRIP accrual-index étude.

This module is deliberately independent of Lean, Jaune, EELS, and the Blanc
compiler.  Python integers model the mathematical values; explicit helpers
separately reproduce every 256-bit multiplication/addition guard in the
frozen runtime.  It is an executable falsifier and fixture oracle, never a
substitute for the compiled-program proofs.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


SCALE = 10**27
RATE = 1_000_000_001_547_125_957_863_212_448
HALF = SCALE // 2
MAX_ELAPSED = 2**32 - 1
MAX_CHI = 2**128 - 1
MAX_ASSET = 2**128 - 1
MAX_UNITS = 2**128 - 1
MAX_PIE = 2**128 - 1

WORD_MODULUS = 2**256
WORD_MAX = WORD_MODULUS - 1
ADDRESS_MAX = 2**160 - 1
CHI_SLOT = WORD_MAX
RHO_SLOT = WORD_MAX - 1
PIE_SLOT = WORD_MAX - 2


class Revert(Exception):
    """A frozen DRIP guard or outbound CALL failed."""

    def __init__(self, reason: str):
        super().__init__(reason)
        self.reason = reason


@dataclass(frozen=True)
class RoundedStep:
    kind: str
    left: int
    right: int
    product: int
    result: int


@dataclass(frozen=True)
class FreshIndex:
    stored: int
    timestamp: int
    elapsed: int
    factor: int
    value: int
    composition_residue: int
    steps: tuple[RoundedStep, ...]


def _require(condition: bool, reason: str) -> None:
    if not condition:
        raise Revert(reason)


def checked_product(left: int, right: int, reason: str) -> int:
    """Exact counterpart of the runtime's division-recovery guard."""

    _require(0 <= left <= WORD_MAX and 0 <= right <= WORD_MAX, reason)
    product = left * right
    _require(product < WORD_MODULUS, reason)
    if right != 0:
        _require(product // right == left, reason)
    return product


def checked_sum(left: int, right: int, reason: str) -> int:
    """Exact counterpart of the runtime's post-addition order guard."""

    _require(0 <= left <= WORD_MAX and 0 <= right <= WORD_MAX, reason)
    total = left + right
    _require(total < WORD_MODULUS and total >= left, reason)
    return total


def rounded_multiply(left: int, right: int) -> tuple[int, RoundedStep]:
    product = checked_product(left, right, "rpow-multiplication-overflow")
    biased = checked_sum(product, HALF, "rpow-addition-overflow")
    result = biased // SCALE
    return result, RoundedStep("multiply", left, right, product, result)


def rpow_checked(base: int, exponent: int) -> tuple[int, tuple[RoundedStep, ...]]:
    """Maker-shaped rpow: parity seed, then square before conditional multiply."""

    _require(0 <= base <= WORD_MAX, "rpow-base-out-of-word")
    _require(0 <= exponent <= WORD_MAX, "rpow-exponent-out-of-word")
    if base == 0:
        return (SCALE if exponent == 0 else 0), ()
    if exponent == 0:
        return SCALE, ()

    accumulator = base if exponent & 1 else SCALE
    power = base
    remaining = exponent // 2
    steps: list[RoundedStep] = []
    while remaining:
        squared, square_step = rounded_multiply(power, power)
        steps.append(RoundedStep(
            "square", square_step.left, square_step.right,
            square_step.product, square_step.result,
        ))
        power = squared
        if remaining & 1:
            accumulator, multiply_step = rounded_multiply(accumulator, power)
            steps.append(multiply_step)
        remaining //= 2
    return accumulator, tuple(steps)


def fresh_index(stored_chi: int, stored_rho: int, now: int) -> FreshIndex:
    _require(SCALE <= stored_chi <= MAX_CHI, "stored-chi-out-of-range")
    _require(0 <= stored_rho <= WORD_MAX, "stored-rho-out-of-word")
    _require(0 <= now <= WORD_MAX, "timestamp-out-of-word")
    _require(now >= stored_rho, "timestamp-regression")
    elapsed = now - stored_rho
    _require(elapsed <= MAX_ELAPSED, "elapsed-over-cap")

    factor, steps = rpow_checked(RATE, elapsed)
    product = checked_product(stored_chi, factor, "chi-factor-overflow")
    value = product // SCALE
    _require(value <= MAX_CHI, "fresh-chi-over-cap")
    return FreshIndex(
        stored=stored_chi,
        timestamp=now,
        elapsed=elapsed,
        factor=factor,
        value=value,
        composition_residue=product - value * SCALE,
        steps=steps,
    )


def units_for_assets(assets: int, chi: int) -> int:
    _require(0 <= assets <= MAX_ASSET, "asset-over-cap")
    _require(SCALE <= chi <= MAX_CHI, "conversion-chi-out-of-range")
    product = checked_product(assets, SCALE, "asset-scale-overflow")
    return product // chi


def assets_for_units(units: int, chi: int) -> int:
    _require(0 <= units <= MAX_UNITS, "units-over-cap")
    _require(SCALE <= chi <= MAX_CHI, "conversion-chi-out-of-range")
    product = checked_product(units, chi, "units-chi-overflow")
    return product // SCALE


def segment_index(initial_chi: int, parts: tuple[int, ...]) -> int:
    chi = initial_chi
    for elapsed in parts:
        factor, _ = rpow_checked(RATE, elapsed)
        product = checked_product(chi, factor, "chi-factor-overflow")
        chi = product // SCALE
        _require(chi <= MAX_CHI, "fresh-chi-over-cap")
    return chi


Recipient = Callable[["Drip", int], bool]


class Drip:
    """Stateful DRIP model at whole-message rollback granularity.

    ``join`` starts from the pre-message state and performs the EVM's incoming
    value credit internally.  If any later guard fails, that credit is rolled
    back with the frame.  ``exit`` settles its four storage writes before the
    callback; a rejected/failed child restores the complete outer snapshot,
    including successful nested calls made by the callback.
    """

    def __init__(self, deployed_at: int, *, balance: int = 0):
        _require(0 <= deployed_at <= WORD_MAX, "deployment-timestamp-out-of-word")
        _require(balance == 0, "nonpayable-constructor")
        self.chi = SCALE
        self.rho = deployed_at
        self.Pie = 0
        self.rows: dict[int, int] = {}
        self.balance = 0

    def _capture(self) -> tuple[int, int, int, int, dict[int, int]]:
        return self.chi, self.rho, self.Pie, self.balance, dict(self.rows)

    def _restore(self, saved: tuple[int, int, int, int, dict[int, int]]) -> None:
        self.chi, self.rho, self.Pie, self.balance, rows = saved
        self.rows = rows

    @staticmethod
    def _caller(caller: int) -> None:
        _require(0 <= caller <= ADDRESS_MAX, "caller-not-address-shaped")

    def row(self, caller: int) -> int:
        self._caller(caller)
        return self.rows.get(caller, 0)

    def snapshot(self) -> dict[str, object]:
        return {
            "chi": self.chi,
            "rho": self.rho,
            "Pie": self.Pie,
            "balance": self.balance,
            "rows": {
                f"0x{address:040x}": value
                for address, value in sorted(self.rows.items())
                if value != 0
            },
        }

    def _fresh(self, now: int) -> FreshIndex:
        return fresh_index(self.chi, self.rho, now)

    def external_credit(self, amount: int) -> None:
        _require(amount > 0, "external-credit-not-positive")
        self.balance += amount

    def receive(self, amount: int) -> None:
        _require(amount >= 0, "negative-receive")
        self.balance += amount

    def drip(self, now: int) -> int:
        saved = self._capture()
        try:
            fresh = self._fresh(now)
            self.chi = fresh.value
            self.rho = now
            return fresh.value
        except Exception:
            self._restore(saved)
            raise

    def convert_to_units(self, assets: int, now: int) -> int:
        _require(0 <= assets <= MAX_ASSET, "asset-over-cap")
        fresh = self._fresh(now)
        return units_for_assets(assets, fresh.value)

    def convert_to_assets(self, units: int, now: int) -> int:
        _require(0 <= units <= MAX_UNITS, "units-over-cap")
        fresh = self._fresh(now)
        return assets_for_units(units, fresh.value)

    def join(self, caller: int, assets: int, now: int) -> int:
        self._caller(caller)
        _require(assets >= 0, "negative-join")
        saved = self._capture()
        self.balance += assets
        try:
            _require(assets <= MAX_ASSET, "asset-over-cap")
            old_row = self.row(caller)
            _require(old_row <= MAX_UNITS, "caller-row-over-cap")
            _require(self.Pie <= MAX_PIE, "Pie-over-cap")
            fresh = self._fresh(now)
            units = units_for_assets(assets, fresh.value)
            new_row = old_row + units
            new_total = self.Pie + units
            _require(new_row <= MAX_UNITS, "caller-row-result-over-cap")
            _require(new_total <= MAX_PIE, "Pie-result-over-cap")

            self.chi = fresh.value
            self.rho = now
            self.rows[caller] = new_row
            self.Pie = new_total
            return units
        except Exception:
            self._restore(saved)
            raise

    def exit(
        self,
        caller: int,
        units: int,
        now: int,
        recipient: Recipient | None = None,
    ) -> int:
        self._caller(caller)
        _require(units >= 0, "negative-exit")
        saved = self._capture()
        try:
            _require(units <= MAX_UNITS, "units-over-cap")
            old_row = self.row(caller)
            _require(old_row <= MAX_UNITS, "caller-row-over-cap")
            _require(self.Pie <= MAX_PIE, "Pie-over-cap")
            _require(units <= old_row, "insufficient-caller-units")
            _require(units <= self.Pie, "insufficient-total-units")
            fresh = self._fresh(now)
            payout = assets_for_units(units, fresh.value)

            # Frozen checks-effects-interactions order.
            self.chi = fresh.value
            self.rho = now
            self.rows[caller] = old_row - units
            self.Pie -= units

            # CALL(GAS, CALLER, payout, 0, 0, 0, 0), including payout = 0.
            _require(payout <= self.balance, "outbound-call-failed")
            self.balance -= payout
            accepted = True if recipient is None else bool(recipient(self, payout))
            _require(accepted, "outbound-call-failed")
            return payout
        except Exception:
            self._restore(saved)
            raise


def operation_count(exponent: int) -> int:
    if exponent == 0:
        return 0
    half = exponent // 2
    return half.bit_length() + half.bit_count()


def join_residue(assets: int, units: int, chi: int) -> int:
    return assets * SCALE - units * chi


def exit_residue(units: int, assets: int, chi: int) -> int:
    return units * chi - assets * SCALE
