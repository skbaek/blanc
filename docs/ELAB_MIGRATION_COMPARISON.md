# Elaboration migration comparison

`scripts/compare-elab-migration.py` is a read-only receipt generator for the
Phase B Jaune migration. It compares the retained same-host shared baseline
against the separately published, clean normal-genesis record for the final
candidate. It does not replace `scripts/check-elab.sh`, initialize a baseline,
publish timing evidence, or modify `.lake` state.

Run the normal candidate timing command first. Its normal-genesis transcript is
separate evidence. Once that command has published a complete green shared
baseline, pass the two records by their exact origin, payload digest and
environment identities. The candidate must be clean, and the candidate SHA
must be its full `HEAD` identity.

```sh
python3 scripts/compare-elab-migration.py \
  --root "$PWD" \
  --candidate "$(git rev-parse HEAD)" \
  --reference-origin 0dabdfda6513c834074d803c1d7741ccd65cbe90 \
  --reference-digest d52d214f44f26e43ee16fbe22e29c618acf380ca44d5f302af71b289559dfac3 \
  --reference-environment 895224e8ce1829fc0045179d7b622561eefde4cbf69925979a9cba4b8222b38f \
  --candidate-origin "<published candidate origin>" \
  --candidate-digest "<published candidate payload digest>" \
  --candidate-environment "<published candidate environment>" \
  --old-jaune 423fbc1b8643a8849a510e355fd3f940b1764af2 \
  --new-jaune 6d0dcfff16691d4d612d22acab5696876d61f692 \
  --receipt /absolute/path/outside/the/worktree/elab-migration-receipt.json
```

The comparator gets the current runtime identity from `lake env lean --version`
and stable-host identity from the registered `scripts/gate-cache.py` provider.
There are no command-line overrides for either identity. It recomputes both
environment fingerprints from immutable Git objects, checks the exact Lean
toolchain/version relationship, and requires the source protocol files to be
byte-identical. The two Lake files may differ only by the declared Jaune Git
revision in both the Lakefile and manifest; any other dependency or
configuration change is refused.

Each selected baseline must have a valid store schema and payload digest, a
unique complete `OK` row for every immutable Lean source blob, and an origin
that is ancestrally ordered before the candidate. A candidate record whose
published origin is not `HEAD` is accepted only when it is exactly the existing
baseline-origin normalization and the normalized origin has identical Lean
corpus blobs and `GLOBAL_INPUTS` bytes. The receipt preserves both identities.

A common row is a regression only when its candidate time is strictly greater
than both thresholds read from the immutable, byte-matched `check-elab.sh`
protocol (currently `2 × old` and `old + 1.0s`). Candidate-only rows are
reported as `FIRST_MEASUREMENT_UNREFERENCED`: their normal full genesis value
is valid evidence, but it has no old row and is never presented as a
no-regression result. Removed rows are reported separately.

Exit code `0` means every common row stayed within the existing threshold;
`1` means valid inputs with one or more regressions; and `2` means the
comparison was refused before a receipt was written. The receipt states the
limits of shared records: they prove clean/full/green publication and exact
stored identities, but do not distinguish genesis from rebase or supply a rich
cache/runtime transcript.

The lightweight registration command for the eventual gate catalogue is:

```sh
python3 scripts/test-elab-migration-comparison.py
```

It builds disposable synthetic Git stores, provides only fixture-local host and
`lake env lean --version` stand-ins, and exercises positive, boundary,
regression, identity, schema and malformed-input paths. It neither elaborates
Lean nor accesses the real shared timing store. The comparator suppresses
bytecode writes only while loading the registered host provider, so callers do
not need to set `PYTHONDONTWRITEBYTECODE` to keep a candidate clean.
