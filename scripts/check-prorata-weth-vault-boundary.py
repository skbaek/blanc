#!/usr/bin/env python3
"""Fail-closed G3 pins and optional Lean mutants for the vault/WETH boundary."""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BOUNDARY = ROOT / "Blanc/Composition/ProrataWethVaultBoundary.lean"
EFFECTS = ROOT / "Blanc/Composition/ProrataWethVaultEffects.lean"
STAGING = ROOT / "Blanc/Composition/ProrataWethVaultStaging.lean"
ROOT_MODULE = ROOT / "Blanc.lean"
LAYERING = ROOT / "scripts/check-layering.py"

SUMMARY = (
    "OK — PRORATA WETH vault boundary: 3 exact child forms; "
    "16 G3 headline axiom owners; whole-source call closure and no-alias pins green"
)

HEADLINES = [
    "DirectWethConfiguration.installed",
    "exactWethCallOccurrence_of_runCompiled",
    "exactWethStatcallOccurrence_of_runCompiled",
    "ExactWethChildSuccess.worldProgramRun",
    "ExactWethChildSuccess.programRun",
    "SuccessfulWethWorldProgramRun.balanceOf_effect",
    "SuccessfulWethProgramRun.balanceOf_effect",
    "SuccessfulWethProgramRun.transfer_effect",
    "SuccessfulWethProgramRun.transferFrom_effect",
    "vault_externalWethCallSites_complete",
    "readTotalAssets_exactEffect",
    "callWethTransferFrom_exactEffect",
    "callWethTransfer_exactEffect",
    "balanceOfStaging_rollback",
    "transferFromStaging_rollback",
    "transferStaging_rollback",
]

BANNED = re.compile(
    r"\b(?:sorry|admit|unsafe|native_decide|maxHeartbeats|maxRecDepth|axiom|alias|export)\b"
)


def compact(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def read(path: Path, errors: list[str]) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError as exc:
        errors.append(f"cannot read {path.relative_to(ROOT)}: {exc}")
        return ""


def require(text: str, snippet: str, owner: str, errors: list[str]) -> None:
    if compact(snippet) not in compact(text):
        errors.append(f"{owner}: missing exact pin: {compact(snippet)}")


def public_header(text: str, theorem: str) -> str | None:
    match = re.search(
        rf"\btheorem\s+{re.escape(theorem)}\b(.*?)\s*:=",
        text,
        re.S,
    )
    return None if match is None else compact(match.group(1))


def check_static(errors: list[str]) -> None:
    boundary = read(BOUNDARY, errors)
    effects = read(EFFECTS, errors)
    staging = read(STAGING, errors)
    root_module = read(ROOT_MODULE, errors)
    layering = read(LAYERING, errors)
    composition = "\n".join([boundary, effects, staging])

    if "import Blanc.Weth10" in composition:
        errors.append("composition: WETH10-family import is forbidden")
    if match := BANNED.search(composition):
        errors.append(f"composition: forbidden trust/debt token `{match.group(0)}`")

    pins = [
        (boundary, "def wethAccount : Adr := Blanc.ProrataWethVault.assetAddress.toAdr", "boundary"),
        (boundary, "code : (pre.getCode wethAccount).toList = Blanc.wethCode", "boundary"),
        (boundary, "MessageExecutesProgram msg xl Blanc.weth", "boundary"),
        (boundary, "post.state = child.state", "boundary"),
        (boundary, "post.returnData = child.output", "boundary"),
        (boundary, "post.logs = (if child.error.isSome then pre.logs else pre.logs ++ child.logs)", "boundary"),
        (boundary, "post.state = pre.state", "boundary"),
        (boundary, "selector \"approve\" [.address, .uint256] ∉ allowedWethSelectors", "boundary"),
        (boundary, "selector \"withdraw\" [.uint256] ∉ allowedWethSelectors", "boundary"),
        (effects, "Prog.RunCompiled childSevm childPre Blanc.weth rawPost", "effects"),
        (effects, "output = (1 : B256).toBytes", "effects"),
        (staging, "exactWethSourceClosure Blanc.ProrataWethVault.vault = true", "staging"),
        (staging, "transferFromCalldata sevm.caller sevm.currentTarget assets", "staging"),
        (staging, "transferCalldata receiver assets", "staging"),
        (staging, "callPost.returnData = (1 : B256).toBytes", "staging"),
    ]
    for text, snippet, owner in pins:
        require(text, snippet, owner, errors)

    for theorem in HEADLINES:
        if public_header(composition, theorem) is None:
            errors.append(f"composition: missing public theorem `{theorem}`")

    for theorem in [
        "readTotalAssets_exactEffect",
        "callWethTransferFrom_exactEffect",
        "callWethTransfer_exactEffect",
    ]:
        header = public_header(staging, theorem)
        if header is None:
            continue
        for forbidden in [
            "ExactWethChildOccurrence",
            "ExactWethChildSuccess",
            "SuccessfulWethProgramRun",
            "returndataBound",
        ]:
            if forbidden in header:
                errors.append(
                    f"staging: `{theorem}` accepts forbidden alias premise `{forbidden}`"
                )

    expected_modules = [
        "Composition.ProrataWethVaultBoundary",
        "Composition.ProrataWethVaultEffects",
        "Composition.ProrataWethVaultStaging",
    ]
    for module in expected_modules:
        require(layering, f'"{module}"', "layering", errors)
        require(root_module, f"import Blanc.{module}", "Blanc.lean", errors)


def replace_once(source: str, old: str, new: str, name: str) -> str:
    if source.count(old) != 1:
        raise ValueError(
            f"{name}: expected one mutation anchor, found {source.count(old)}"
        )
    return source.replace(old, new, 1)


def reject_lean(path: Path, diagnostics: tuple[str, ...], errors: list[str]) -> None:
    result = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    evidence = result.stdout + result.stderr
    normalized = compact(evidence)
    if result.returncode == 0:
        errors.append(f"mutant `{path.name}` unexpectedly compiled")
    elif not any(compact(diagnostic) in normalized for diagnostic in diagnostics):
        errors.append(
            f"mutant `{path.name}` failed outside its pinned diagnostic: {evidence[-1200:]}"
        )


def run_falsifiers(errors: list[str]) -> None:
    boundary = BOUNDARY.read_text(encoding="utf-8")
    effects = EFFECTS.read_text(encoding="utf-8")
    staging = STAGING.read_text(encoding="utf-8")

    with tempfile.TemporaryDirectory(prefix="prorata-weth-boundary-") as raw:
        temp = Path(raw)
        mutants: list[tuple[str, str, tuple[str, ...]]] = []

        mutants.append((
            "WrongTarget.lean",
            replace_once(
                boundary,
                "def wethAccount : Adr :=\n  Blanc.ProrataWethVault.assetAddress.toAdr",
                "def wethAccount : Adr :=\n  (0x1001 : B256).toAdr",
                "wrong target",
            ),
            ("wethAccount.toB256 = ProrataWethVault.assetAddress",),
        ))
        mutants.append((
            "WrongCode.lean",
            replace_once(
                boundary,
                "code : (pre.getCode wethAccount).toList = Blanc.wethCode",
                "code : (pre.getCode wethAccount).toList = "
                "Blanc.prorataWethVaultCode",
                "wrong code",
            ),
            (
                "has type (pre.getCode wethAccount).toList = "
                "prorataWethVaultCode but is expected to have type "
                "(pre.getCode wethAccount).toList = wethCode",
            ),
        ))
        mutants.append((
            "WrongRollbackPolarity.lean",
            replace_once(
                boundary,
                "(failureFlag : ∃ tail, post.stack = (0 : B256) :: tail) :\n"
                "    post.state = pre.state := by",
                "(failureFlag : ∃ tail, post.stack = (1 : B256) :: tail) :\n"
                "    post.state = pre.state := by",
                "rollback polarity",
            ),
            ("(if child.error.isSome = true then 0 else 1) = 0",),
        ))
        mutants.append((
            "WrongCalldata.lean",
            replace_once(
                effects,
                "(transferCalldata receiver assets) output initial final) :",
                "(balanceOfCalldata vault) output initial final) :",
                "wrong calldata",
            ),
            ("balanceOfCalldata vault",),
        ))
        mutants.append((
            "WrongOwnerRole.lean",
            replace_once(
                staging,
                "[caller] ++ mstoreAt 1 ++",
                "[address] ++ mstoreAt 1 ++",
                "wrong owner role",
            ),
            ("Tactic `rfl` failed", "Tactic `decide` failed"),
        ))
        mutants.append((
            "FalseAccepted.lean",
            replace_once(
                staging,
                "calldata\n        (1 : B256).toBytes false ∧",
                "calldata\n        (0 : B256).toBytes false ∧",
                "false return",
            ),
            ("callPost.returnData = B256.toBytes 1",),
        ))

        for filename, source, diagnostics in mutants:
            path = temp / filename
            path.write_text(source, encoding="utf-8")
            reject_lean(path, diagnostics, errors)

        hidden = temp / "HiddenApprove.lean"
        hidden.write_text(
            """import Blanc.Composition.ProrataWethVaultStaging

namespace Blanc.Composition.ProrataWethVault.Source

open Jaune
open Jaune.Ninst Ninst

private def hiddenApprove : Func :=
  pushB256 (selector \"approve\" [.address, .uint256]) :::
    Ninst.call ::: Func.stop

private def mutatedVault : Prog :=
  ⟨hiddenApprove, []⟩

example : exactWethSourceClosure mutatedVault = true := by
  have rejected : exactWethSourceClosure mutatedVault = false := by
    decide +kernel
  rw [rejected]

end Blanc.Composition.ProrataWethVault.Source
""",
            encoding="utf-8",
        )
        reject_lean(
            hidden,
            ("false = true",),
            errors,
        )


def main() -> int:
    if len(sys.argv) > 2 or (len(sys.argv) == 2 and sys.argv[1] != "--falsify"):
        print(
            "usage: scripts/check-prorata-weth-vault-boundary.py [--falsify]",
            file=sys.stderr,
        )
        return 2

    errors: list[str] = []
    check_static(errors)
    falsify = len(sys.argv) == 2
    if falsify and not errors:
        try:
            run_falsifiers(errors)
        except (OSError, ValueError) as exc:
            errors.append(f"falsifier setup failed: {exc}")

    if errors:
        for error in errors:
            print(f"REGRESSION — PRORATA WETH vault boundary: {error}", file=sys.stderr)
        return 1

    if falsify:
        print(f"{SUMMARY}; 7 diagnostic-pinned Lean mutants")
    else:
        print(SUMMARY)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
