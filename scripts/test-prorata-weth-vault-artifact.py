#!/usr/bin/env python3
"""Biting static controls for the frozen runtime and bounded proof pins."""
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "vault_artifact", ROOT / "scripts/check-prorata-weth-vault-artifact.py"
)
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
source = checker.CODE.read_text()
data = checker.DATA.read_text()


def errors_for(text, chunks=data):
    errors = []
    checker.check_runtime(text, chunks, errors)
    return errors


assert not errors_for(source), errors_for(source)
witness = checker.COMPILE_WITNESS
assert source.count(witness) == 1
mutants = {
    "deleted witness": source.replace(witness, ""),
    "corrupt body": source.replace(witness, witness.replace("  rfl", "  sorry")),
    "changed public statement": source.replace(witness, witness.replace(
        "Prog.compile ProrataWethVault.vault", "Prog.compile ProrataWethVault.vault.reverse")),
    "private witness": source.replace(witness, "private " + witness),
    "block-comment spoof": source.replace(witness, "/- " + witness + " -/"),
    "nested-comment spoof": source.replace(witness, "/- /- nested -/ " + witness + " -/"),
    "line-comment spoof": source.replace(witness, "\n".join("-- " + x for x in witness.splitlines())),
    "string spoof": source.replace(witness, 'def fake : String := "' + witness + '"'),
    "wrong join order": source.replace("  prorataWethVaultCodeChunk0 ++\n", "  prorataWethVaultCodeChunk1 ++\n", 1),
    "missing join boundary": source.replace("/-- Kernel-checked", "/-- Unbounded", 1),
}
for name, mutant in mutants.items():
    failures = errors_for(mutant)
    assert failures, name
    if name in list(mutants)[:8]:
        assert failures == ["runtime: missing exact public bounded compiler witness"], (name, failures)
    print(f"REJECTED — {name}: {failures[0]}")

owner_mutants = {
    "corrupt byte": (source, data.replace("0x5b", "0x5a", 1), "runtime: SHA-256"),
    "wrong data import": (source.replace("import Blanc.ProrataWethVaultCodeData", "import Blanc.OtherData"), data, "runtime: facade must import"),
    "commented data import": (source.replace("import Blanc.ProrataWethVaultCodeData", "-- import Blanc.ProrataWethVaultCodeData"), data, "runtime: facade must import"),
    "shadow chunk": (source.replace("namespace Blanc", "namespace Blanc\ndef prorataWethVaultCodeChunk0 : Bytes := [0x00]"), data, "runtime: facade shadows"),
    "wrong data dependency": (source, data.replace("import Blanc.ProrataWethVault", "import Blanc.OtherVault"), "runtime: data owner must import"),
    "private data chunk": (source, data.replace("def prorataWethVaultCodeChunk0", "private def prorataWethVaultCodeChunk0", 1), "runtime: data owner contains"),
    "data expression suffix": (source, data.replace("end GeneratedByteChunks", "  ++ [0x00]\nend GeneratedByteChunks"), "runtime: data owner contains"),
    "join expression suffix": (source.replace("    prorataWethVaultCodeChunk68", "    prorataWethVaultCodeChunk68 ++ []"), data, "runtime: literal join has unparsed"),
}
for name, (facade, chunks, diagnostic) in owner_mutants.items():
    failures = errors_for(facade, chunks)
    assert any(error.startswith(diagnostic) for error in failures), (name, failures)
    print(f"REJECTED — {name}: {diagnostic}")

# With only the new witness control disabled, byte-correct proof mutants pass
# the remaining runtime checks. Their rejection therefore lands at this pin.
check_witness = checker.check_compile_witness
checker.check_compile_witness = lambda text, errors: None
for name in list(mutants)[:8]:
    assert not errors_for(mutants[name]), name
checker.check_compile_witness = check_witness
assert not errors_for(source)
assert checker.CODE.read_text() == source and checker.DATA.read_text() == data
print(f"OK — vault artifact controls: {len(mutants) + len(owner_mutants)} mutants rejected; witness-only ablation and unchanged source restoration green")
