#!/usr/bin/env python3
"""Pure authenticated synthetic-carrier controls. EELS invocations: zero."""
import copy
import contextlib
import io
import importlib.util
import json
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import drip_cost_measurements as cost

spec = importlib.util.spec_from_file_location(
    "legacy_cost_controls", Path(__file__).with_name("test-drip-cost-measurements.py"))
legacy = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = legacy
spec.loader.exec_module(legacy)
api = legacy.api


class SupplementalControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runtime, cls.creation = api.artifacts()
        cls.baseline = cost.load_baseline(api.ROOT)
        cls.runtimes = {"baseline": cls.baseline, "candidate": cls.runtime}
        cls.cases = {a: {c["name"]: c for c in cost.supplemental_cases(api, r)}
                     for a, r in cls.runtimes.items()}
        cls.rows = []
        cls.transitions = 0
        for name, variants, _ in cost.SUPPLEMENTAL_PLAN:
            for variant in variants:
                for artifact in cost.ARTIFACTS:
                    case = cls.cases[artifact][name]
                    def transition(initial, _env, transactions):
                        cls.transitions += 1
                        return legacy.synthetic_output(initial, transactions[0], case["operation"])
                    cls.rows.append(cost.execute_supplemental_observation(
                        api, case, artifact, variant, transition))
        cost.validate_supplemental_rows(api, cls.rows, cls.runtimes)

    def validate(self, rows=None):
        return cost.validate_supplemental_rows(api, self.rows if rows is None else rows, self.runtimes)

    def mutated(self, scenario, variant, mutate, pattern):
        bad = copy.deepcopy(self.rows)
        row = next(r for r in bad if r["scenario"] == scenario and
                   r["variant"] == variant and r["artifact"] == "candidate")
        mutate(row)
        # Order is not a source of acceptance; put the corrupted cell first.
        bad.remove(row)
        bad.insert(0, row)
        with self.assertRaisesRegex((AssertionError, KeyError), pattern):
            self.validate(bad)

    def test_fixed_population_counts_and_restored_missing_duplicate(self):
        self.assertEqual((len(cost.SUPPLEMENTAL_PLAN), len(cost.supplemental_expected_keys()),
                          self.transitions), (17, 88, 176))
        pairs, warmth = self.validate()
        self.assertEqual((len(pairs), len(warmth)), (44, 54))
        for bad in (self.rows[:-1], self.rows+[self.rows[0]], self.rows[:-1]+[self.rows[0]]):
            with self.assertRaisesRegex(AssertionError, "88-cell bijection"):
                self.validate(bad)
        self.validate()

    def test_exact_independently_signed_holder_and_all_key_sets(self):
        for name, variants, _ in cost.SUPPLEMENTAL_PLAN:
            case = self.cases["candidate"][name]
            for variant in variants:
                transaction = cost.supplemental_transaction(api, case, variant)
                raw = legacy.signed(transaction)
                auth = cost.authenticate_body(legacy.body_of([raw]), [transaction], legacy.root_of(raw))[0]
                self.assertEqual(auth["sender"], api.ALICE)
                keys = {"A": [], "C": [api.CHI_SLOT], "CR": [api.CHI_SLOT, api.RHO_SLOT],
                        "P": [api.PIE_SLOT], "H": [int(auth["sender"], 16)],
                        "HP": [int(auth["sender"], 16), api.PIE_SLOT],
                        "ALL": [api.CHI_SLOT, api.RHO_SLOT, api.PIE_SLOT, int(auth["sender"], 16)]}[variant]
                self.assertEqual(transaction["accessList"], [{"address": api.TARGET,
                    "storageKeys": ["0x"+f"{k:064x}" for k in keys]}])
                self.assertEqual(cost.quantity(transaction["type"]), 1)
        bad = copy.deepcopy(self.cases["candidate"]["join-zero-value"])
        bad["operation"]["transaction"]["secretKey"] = "0x"+f"{api.KEYS[api.BOB]:064x}"
        with self.assertRaisesRegex(AssertionError, "holder/signer differs"):
            cost.supplemental_transaction(api, bad, "H")

    def test_wrong_holder_sender_and_unexpected_warmth_restore(self):
        mutations = (
            (lambda r: r["transaction"]["accessList"][0]["storageKeys"].__setitem__(0, "0x"+f"{int(api.BOB,16):064x}"), "transaction differs"),
            (lambda r: r.__setitem__("sender", api.BOB), "envelope/sender differs"),
            (lambda r: r["warmth"]["initialStorageKeys"].append({"address":api.TARGET,"key":"0x"+"00"*32}), "warmth differs"),
            (lambda r: r["transaction"]["accessList"][0]["storageKeys"].append("0x"+f"{int(api.ALICE,16):064x}"), "transaction differs"),
        )
        for mutate, pattern in mutations:
            self.mutated("join-zero-value", "H", mutate, pattern)
        self.validate()

    def test_synthetic_guard_seed_and_provenance_restore(self):
        case = self.cases["candidate"]["supplemental-exit-total-insufficient"]
        operation = case["operation"]
        storage = api.normalized_storage(operation["preTarget"]["storage"])
        self.assertEqual((storage[api.CHI_SLOT],storage[api.RHO_SLOT],storage[api.PIE_SLOT],
                          storage[int(api.ALICE,16)]), (api.SCALE,api.START,10,11))
        self.assertEqual(operation["transaction"]["input"], api.abi("exit",11))
        self.assertEqual(operation["expectedOutcome"]["status"], 0)
        self.assertEqual(operation["preTarget"], operation["expectedTarget"])
        self.mutated("supplemental-exit-total-insufficient", "HP",
            lambda r:r["initialAllocation"][api.TARGET]["storage"].__setitem__(api.q(api.PIE_SLOT),api.q(11)),
            "initial allocation differs")
        self.mutated("join-cap-row-result", "ALL",
            lambda r:r["seedBoundary"].__setitem__("reachableHistoryWitness",True), "seed provenance differs")
        self.assertTrue(cost.supplemental_seed_boundary("join-cap-row-result")["invariantViolatingGuardSeed"])
        self.validate()

    def test_wrong_artifact_and_unobserved_channels_restore(self):
        for mutate, pattern in (
            (lambda r:r["targetPre"].__setitem__("codeSha256","00"*32), "projection differs|artifact identity"),
            (lambda r:r.__setitem__("artifact","other"), "88-cell bijection"),
            (lambda r:r.__setitem__("grossExecutionGas",1), "projection differs|unobserved channel"),
            (lambda r:r.__setitem__("senderFeeNormalizedTransfer",1), "sender transfer differs"),
        ):
            self.mutated("drip-same-timestamp", "C", mutate, pattern)
        with self.assertRaisesRegex(AssertionError, "baseline identity"):
            cost.validate_supplemental_rows(api,self.rows,{**self.runtimes,"baseline":b"bad"})
        self.validate()

    def test_envelope_receipt_root_and_linked_header_controls_restore(self):
        for mutate, pattern in (
            (lambda r:r.__setitem__("signedBodyRlp",legacy.body_of([])), "body population"),
            (lambda r:r["transitionResult"].__setitem__("receiptsRoot",legacy.ZERO_HASH), "receipt encoding/root"),
            (lambda r:r["transitionResult"].__setitem__("gasUsed","0x1"), "block/receipt gas"),
            (lambda r:r["blockHeader"].__setitem__("parentHash",legacy.ZERO_HASH), "header differs"),
            (lambda r:r.__setitem__("blockRlp","0x"), "serialization differs"),
        ):
            self.mutated("drip-same-timestamp", "C", mutate, pattern)
        self.validate()

    def test_full_prefix_drift_is_rejected_and_restored(self):
        case=self.cases["candidate"]["supplemental-exit-total-insufficient"]
        def observe(corrupt):
            calls=0
            def transition(initial,_env,transactions):
                nonlocal calls
                calls+=1
                out=legacy.synthetic_output(initial,transactions[0],case["operation"])
                if corrupt and calls==2:out.result["stateRoot"]="0x"+"01"*32
                return out
            return cost.execute_supplemental_observation(api,case,"candidate","HP",transition)
        observe(False)
        with self.assertRaisesRegex(AssertionError,"full/prefix stateRoot"):
            observe(True)
        observe(False)

    def test_frozen_cases_legacy_keys_and_zero_loop_semantics(self):
        before=json.dumps(api.cases(self.runtime),sort_keys=True)
        cases=cost.supplemental_cases(api,self.runtime)
        self.assertEqual(before,json.dumps(api.cases(self.runtime),sort_keys=True))
        self.assertEqual(len(cost.expected_keys()),60)
        for case in cases:
            name=case["name"];op=case["operation"]
            if name in {n for n,_,status in cost.SUPPLEMENTAL_PLAN if status==1}:
                rho=api.normalized_storage(op["preTarget"]["storage"])[api.RHO_SLOT]
                self.assertEqual(op["timestamp"]-rho,1 if name=="supplemental-drip-k1" else 0)
                self.assertEqual(op["expectedOutcome"]["status"],1)
            self.assertFalse(cost.supplemental_seed_boundary(name)["reachableHistoryWitness"])
        with self.assertRaisesRegex(AssertionError,"unknown supplemental"):
            cost.supplemental_transaction(api,cases[0],"ALL")

    def test_cli_requires_root_and_rejects_conflicting_modes(self):
        script = str(api.ROOT / "scripts/gen-drip-fixtures.py")
        options = [("--measure-supplemental-costs",)]
        options += [("--measure-supplemental-costs", mode) for mode in
                    ("--measure-costs", "--write", "--check-runtime", "--validate-runtime")]
        for arguments in options:
            with self.subTest(arguments=arguments):
                result = legacy.subprocess.run([sys.executable, "-B", script, *arguments],
                    capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 2)
                self.assertNotIn("DRIP_SUPPLEMENTAL_MEASUREMENTS", result.stdout)

    def test_mocked_dispatch_is_separate_and_never_writes_fixtures(self):
        profile = json.loads((api.ROOT / "scripts/current-mainnet-target.json").read_text())
        runner = object()
        with patch.object(api, "validate_current_mainnet_boundary"), \
             patch.object(api, "resolve_root", return_value=api.ROOT), \
             patch.object(api, "verify_target"), \
             patch.object(api, "target_paths", return_value=SimpleNamespace(python=Path(sys.executable))), \
             patch.object(api, "artifacts", return_value=(self.runtime,self.creation)), \
             patch.object(api, "transition_for", return_value=runner), \
             patch.object(api, "runtime_transaction_population", side_effect=AssertionError("fixture population forbidden")), \
             patch.object(api, "write_or_compare", side_effect=AssertionError("fixture writer forbidden")), \
             patch.object(api, "run_t8n", side_effect=AssertionError("EELS forbidden")), \
             patch.object(cost, "measure", return_value={"syntheticDispatch":True}) as old, \
             patch.object(cost, "measure_supplemental", return_value={"syntheticDispatch":True}) as new:
            for kwargs, chosen, other, marker in (
                ({"measure_supplemental_costs":True},new,old,"DRIP_SUPPLEMENTAL_MEASUREMENTS "),
                ({"measure_costs":True},old,new,"DRIP_WARM_MEASUREMENTS "),
            ):
                chosen.reset_mock(); other.reset_mock()
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    api.execute_and_check(api.ROOT, write=False, **kwargs)
                chosen.assert_called_once(); other.assert_not_called()
                args = chosen.call_args.args
                self.assertEqual(args[:4],(api,profile,self.runtime,self.creation))
                self.assertIs(args[4],runner)
                self.assertIn("scripts/drip_cost_measurements.py",args[5]())
                self.assertTrue(output.getvalue().startswith(marker))
                self.assertEqual(sum(line.startswith(marker) for line in output.getvalue().splitlines()),1)
            # Programmatic conflicts must fail even before source/target reads.
            with patch.object(api, "ROOT", Path("/no-such-source")):
                for flag in ("write", "validate_only", "measure_costs"):
                    kwargs={"write":False,"measure_supplemental_costs":True,flag:True}
                    with self.assertRaisesRegex(AssertionError,"mutually exclusive"):
                        api.execute_and_check(None,**kwargs)

    def test_entrypoint_closed_order_counts_and_identity_controls(self):
        profile=json.loads((api.ROOT/"scripts/current-mainnet-target.json").read_text())
        expected=[(name,variant,a) for name,variants,_ in cost.SUPPLEMENTAL_PLAN
                  for variant in variants for a in cost.ARTIFACTS]
        def run(identity=lambda:{"source":"fixed"}):
            calls=0
            def transition(initial,_env,transactions):
                nonlocal calls
                name,_variant,artifact=expected[calls//2];calls+=1
                return legacy.synthetic_output(initial,transactions[0],self.cases[artifact][name]["operation"])
            result=cost.measure_supplemental(api,profile,self.runtime,self.creation,transition,identity)
            self.assertEqual(calls,176)
            self.assertEqual([(r["scenario"],r["variant"],r["artifact"]) for r in result["transactions"]],expected)
            self.assertEqual((result["scenarioCount"],result["transactionCount"],len(result["artifactPairs"]),
                              len(result["warmthPairs"])),(17,88,44,54))
            return result
        # Mock identity I/O, then forbid every subprocess while exercising the
        # complete callable mode with synthetic transition responses.
        with patch.object(cost,"load_baseline",return_value=self.baseline), \
             patch.object(api,"artifacts",return_value=(self.runtime,self.creation)), \
             patch.object(cost.subprocess,"run",side_effect=AssertionError("subprocess forbidden")), \
             patch.object(api,"run_t8n",side_effect=AssertionError("EELS forbidden")):
            run()
            identities=iter([{"source":"fixed"},{"source":"drift"}])
            with self.assertRaisesRegex(AssertionError,"identity drift"):
                run(lambda:next(identities))
            with patch.object(api,"artifacts",return_value=(self.runtime+b"\x00",self.creation)):
                with self.assertRaisesRegex(AssertionError,"identity drift"):
                    run()
            wrong=copy.deepcopy(profile);wrong["execution"]["fork"]="other"
            with self.assertRaisesRegex(AssertionError,"target identity"):
                cost.measure_supplemental(api,wrong,self.runtime,self.creation,None,lambda:{})
            run()


if __name__ == "__main__":
    unittest.main(verbosity=2)
