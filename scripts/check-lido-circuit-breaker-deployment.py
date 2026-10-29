#!/usr/bin/env python3
"""Fail-closed source assurance for the Lido CircuitBreaker deployment root.

This is deliberately a source gate, not a replay runner.  It pins the complete
normalised public deployment declarations and independently checks the facts
which make a direct, successful, prepared-state deployment meaningful.  The
separate finite replay channel must never be credited as a Lean root.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import axiom_audit  # noqa: E402

DEFAULT_ROOT = Path(__file__).resolve().parent.parent
VERDICT = "S9 Lido CircuitBreaker deployment-root assurance"


class Failure(Exception):
    pass


def fail(message: str) -> None:
    raise Failure(message)


# This exact family is intentionally small: inputs, prepared context, direct
# message execution, transaction, suffix, and root.  WETH is architectural
# evidence only and is forbidden from this family.
SOURCES = {
    "constructor": "Blanc/LidoCircuitBreakerDeploy.lean",
    "compiled": "Blanc/DeploymentCompiled.lean",
    "base": "Blanc/DeploymentMessage.lean",
    "layout": "Blanc/LidoCircuitBreakerDeploymentLayout.lean",
    "trace": "Blanc/LidoCircuitBreakerDeploymentTrace.lean",
    "input": "Blanc/LidoCircuitBreakerDeploymentInput.lean",
    "message": "Blanc/LidoCircuitBreakerDeploymentMessage.lean",
    "transaction": "Blanc/LidoCircuitBreakerDeploymentTransaction.lean",
    "block": "Blanc/LidoCircuitBreakerDeploymentBlock.lean",
    "root": "Blanc/LidoCircuitBreakerDeploymentRoot.lean",
}

# The mainnet specialization is deliberately outside the nine-owner family:
# that family keeps its blanket `mainnet` ban and stays schedule-parametric.
# This one module is scanned separately below, with its own pins, premise
# discipline, inventory, and a binding of its coordinate literals to the
# committed reference manifest.
MAINNET_SOURCE = "Blanc/LidoCircuitBreakerMainnetDeployment.lean"
REFERENCE = "scripts/lido-circuit-breaker-reference.json"

AXIOM_CHECK = "scripts/AxiomCheck.lean"
PUBLIC_THEOREM_COUNT = 179
PUBLIC_THEOREM_INVENTORY_SHA256 = (
    "1deffbff00e45490377687c0e82b817ee2666c841c962586478c4fc1639e54dc"
)
# The whole axiom claim of this family. Every public deployment theorem is covered by the
# repository's one union walk (`scripts/AxiomCheck.lean`, `scripts/check.sh`), which bounds the
# axioms of every Blanc constant by `propext`, `Classical.choice` and `Quot.sound`. These four
# public names are the ones whose axiom sets this gate has always frozen as SMALLER than that
# bound; they stay explicit `#expect_axioms` rows of `scripts/AxiomCheck.lean`, checked in both
# directions, and this table is the copy this gate compares them against, so a claim cannot be
# dropped, weakened or added there without this gate noticing. An empty set is "no axioms at all".
STRICTER_CLAIMS = {
    "Blanc.LidoCircuitBreaker.officialConstructorEventScratch_eq": frozenset(),
    "Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_size": frozenset({"propext"}),
    "Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_read_memory":
        frozenset({"propext", "Quot.sound"}),
    "Blanc.LidoCircuitBreaker.ConstructorPatchInvariant.read_memory":
        frozenset({"propext", "Quot.sound"}),
}

# Kept as digests rather than copies to make this executable readable.  The
# digest is over comment-free, whitespace-normalised *complete declarations*,
# including the proof term; a changed body cannot silently pass.  The separate
# channels below prevent an author from merely updating a digest after a
# weakening.
PINS = {
    # Filled from the committed direct-root interface by this gate's author.
    # Values are patched in with the parser below; an empty value fails closed.
    "OfficialConstructorEffectCheckpoints": "49ebc8bfbc946946b286b7b1cddf0e3cb4983c1fd6fc80fd9e149ead5ff85243",
    "OfficialValidationCheckpoints": "a6195a30db19fd019e8b174e0cbe51d2d52d3dc261744d7403fbcaef5fe07bfe",
    "OfficialConstructorErrorArmLayout": "80f93acfce83bba55420051c4ef35d0add6d305f5c367672a81563807ad4de02",
    "OfficialConstructorExecutionTrace": "c1e4cb156cb9869ecd83e797bc2dd397b0e105b5fa4d5161de881df8b79ba7bd",
    "OfficialCreateMessageExecution": "f3f2fbb91c379302af9eff908b70bb2761b3be215ce7a07049b269f23e64ec58",
    "OfficialCreateMessageResult": "846e6ca7c073eb4575bf827e1e68c4d671a3e35e13624b81c0766376f3263612",
    "OfficialConstructorMessageResult": "ac72fa7080ad768826622ca3a4d17f6a859c7be69d8b52426fffd0304087b5ab",
    "CanonicalDeploymentBase": "baed7dd75d0138d5aa6b8c16e2a0daeebc54b3b76a8edc7d1bef83d730bd8755",
    "CanonicalOfficialDeploymentBlock": "ba7dd045ebdf40cfafa57f4f90c410440d44ec23b190a1dcbec0be7821a08753",
    "PreparedDeploymentContext": "d8e8dc1bd01e4202ba7670315f3a3a464b6e31574ac5b81afe2fe387415ca31f",
    "OfficialDeploymentTransactionResult": "4123d37aa90ea893ad37cbcf73184a94b0dcb2146b7c021a086487935364c62f",
    "OfficialDeploymentSuffixResult": "3c359fd060bd6c981d177062d40bc52e4e7ce5d9d69220e31966b5a02e0f4977",
    "DeploymentRoot": "44c6dc4d3b9ba323222c1fdccbcc40b1679bde862aa6ed74f5b849e33353b04e",
    "canonicalDeploymentStep_establishes_root": "131af7276bc73b82a830489af5300def5716f08c45316f184124928af6947d7e",
    "DeploymentRoot.reflReach": "9df07c7df5c23375cee939340a5af51ea9fbb6a619f2ed9f41fd41b0c9af4926",
    "DeploymentRoot.reachable_registryStable": "218ea1e950cd17776c128b974915ebd3b9810b6fbcb3556c1c7f046b1ffd0081",
    "DeploymentRoot.reachable_code": "81a6786d083b03c2385428f6ca09a79e935ac1ce73242349fe4ecbf136fabbbd",
    "DeploymentRoot.reachable_installedCode": "d7f912846c7b60d6fce05d7ca07e381b861cb00471c5febe7495fb29964db4b8",
    "DeploymentRoot.reachable_witness": "2c7ac7c5246432ba6a0f1b08270f3937641417d5f6c0ca29c2d72774770f0ac1",
    "DeploymentRoot.reachable_membership": "f210b1b06d95c79a9f88e3313ae33a158e2d7fe52b21a423ed9a46ecba05b983",
    "DeploymentRoot.reachable_countConservation": "fa121124d70ca1d41dad767e50c8943c6f1027952e0a04d61ea18bdc4221711e",
    # Selected-fork carriers, root, producer, and reachable family.
    "CanonicalOfficialDeploymentBlockAt": "b6b5ac79b948d1ad37c18278124da9720e07dc630967a793a61f53278fb2eaff",
    "PreparedDeploymentContextAt": "aedd3d0701a396625c84488997ecadde447c234cc8586dfc8ca2282f02e73634",
    "OfficialDeploymentTransactionResultAt": "0a2ed5a117abcdb8297f055be5d7ddcd2d378508c3868d5c58f355ec17c050cc",
    "OfficialDeploymentSuffixResultAt": "e95b09a451db1d73c5bf71fed45eb088519db9d77d4098f65906971b4ec586c6",
    "DeploymentRootAt": "deb41a5a317c98ce5c9627722be2cc8c89a5c107a24e5a78af6d682aa38daf0b",
    "canonicalDeploymentStepAt_establishes_root": "d03be52a5d51d6d960fbc3f41e954aefbf5152ac9f60b6c0d4163c0113ec4f8b",
    "DeploymentRootAt.reflReach": "c1f83b86db89c79b253b8c451bb2895ffeb6c2d6dbf6b170d22d4509eb69b686",
    "DeploymentRootAt.reachable_registryStable": "381a70e663da00964e13b1e44a14fa6fc50a9874bd39aa794e1a6ed81fc62d9b",
    "DeploymentRootAt.reachable_code": "aeebc549abc34458a38bf0c990ac1391fdf794eef7ae477f8dd5b5ce4c3896b6",
    "DeploymentRootAt.reachable_installedCode": "5284daa96b40cb5a23b831f56b1e8f10a60169ed5d1c89f175e1999735d4d926",
    "DeploymentRootAt.reachable_witness": "b1a4a3e9d8399e3ddf6b95f2a7d04f49279e8c479eb0eef1a39babca2d6067fd",
    "DeploymentRootAt.reachable_membership": "52251bd06b362fffa098fb2c9062a7dfd646933a56b4528b9b85037d9f576fc8",
    "DeploymentRootAt.reachable_countConservation": "12e052a5376b3b9c8d0748c7f977774dacfee55d5a033f252272a46b3b37a718",
}

# Complete normalised bodies of every declaration of the mainnet module.
MAINNET_PINS = {
    "officialMainnetDeploymentChainId": "2f6ce48f059b44b098b96e5bbd926e7912a2a45b20e3fe2eeed415ad9a077cc3",
    "officialMainnetDeploymentBlockNumber": "9ff95ef049d11698146f70eb11a8b5f585fba9e981b746da597dc77e71d61afb",
    "officialMainnetDeploymentTimestamp": "529111981b25d17d187bbbe70a08f3b0b6d8c597f46d8d3d86b8adbff8d98e0c",
    "mainnetChainConfig_chainId_eq_officialDeployment": "e93ff444aff2c9fc1bea03d7b34b717d4f4b14f861bad630ef0e8f5cf3c779e4",
    "officialMainnetDeployment_forkAt": "93f5064bdf581555905b74963c2c99d948513a4806e52666aeb7ec6768db2e91",
    "mainnetPragueTimestamp_le_officialDeployment": "63f54fda9bf88e9c2a82e5550b35cfb04a56101e6e848cf2724d16dc2f1aa9c5",
    "MainnetDeploymentRoot": "85580733631bfd2deae2fe9dd309513c16933a61d2418ecb72ba8f6e3c4c5121",
    "canonicalMainnetDeploymentStep_establishes_root": "3616e8365d0804b1fb4a62468dd9d6fbd5e8f9dafbf9ff2076f02709ccfba0fc",
    "mainnetChainConfig_covered_from_officialDeployment": "17615fea4cd3ac127c79d0797a4a48d1e769a42e48581677fd2ff5f1e22cdd5e",
    "MainnetDeploymentRoot.tip_floor": "287dfad2de5d5e8e2ab39ea37e9d215aaf457113efa37aaa4451eceee9bc938e",
    "MainnetDeploymentRoot.reflReach": "1fddcbea9e0532e5aee9ad372764650d666e97d0ab7bb3dfb60cedd07262ba03",
    "MainnetDeploymentRoot.reachable_registryStable": "40b72d554f36212fe5469fb7cb8d352dfda42e0bb96fd365f6b0139e45988bb1",
    "MainnetDeploymentRoot.reachable_code": "c003a3bf61cb8ae6073729dc588d2a6efbec5cad4d6ca606e21e8c3d081065c5",
    "MainnetDeploymentRoot.reachable_installedCode": "f9024936efe520bcbf6a05d1181c2d0b2f49b1753e89211093009042a3ce6aa2",
    "MainnetDeploymentRoot.reachable_witness": "321d6ad3489417f4310d2d4f1035654f127e65c054cf5710edd5013da105db3e",
    "MainnetDeploymentRoot.reachable_membership": "36079ac0668e914456e1c094342c2fb12ed45c81b83e333f7260101872b63166",
    "MainnetDeploymentRoot.reachable_countConservation": "b75f0a16b46efc4b949bca2d458957b3e471c5e78b09e9eaea2ddd69d0bd343e",
}
MAINNET_PUBLIC_THEOREM_COUNT = 13
MAINNET_PUBLIC_THEOREM_INVENTORY_SHA256 = (
    "af230e7211e3e9b04290340a587ab17e752ad5519b14c0e6aa0cf6223ca20f8a"
)

# Lean coordinate definitions and the `deployment.manifest.meta` keys of the
# committed reference manifest they must equal.
MAINNET_COORDINATES = {
    "officialMainnetDeploymentChainId": ("chainId", "UInt64"),
    "officialMainnetDeploymentBlockNumber": ("blockNumber", "Nat"),
    "officialMainnetDeploymentTimestamp": ("timestamp", "Nat"),
}

# Every channel is exact source vocabulary with independent security meaning.
# They are intentionally redundant with PINS: this makes a careless re-pin a
# detectable review event, not a way to bless result smuggling or a weak root.
CHANNELS = {
    "OfficialConstructorEffectCheckpoints": (
        "exactPost :", "state :", "storage :",
        "storage : Devm.getStor post sevm.currentTarget =", "logs :",
        "logs : post.logs = base.logs ++ officialConstructorLogs sevm.currentTarget",
        "stack :", "memory :", "gasLeft :", "output :",
        "output : post.output = lidoCircuitBreakerCode officialParams",
        "refundCounter :", "returnData :",
        "returnData : post.returnData = base.returnData", "error :",
        "accountsToDelete :",
        "createdAccounts :", "accessedAddresses :",
        "accessedStorageKeys :", "transientStorage :", "siteCounts :",
        "constructorProgramSiteCounts = (2, 0, 0)",
        "persistentInventory :", "constructor.pauseDuration",
        "constructor.heartbeatInterval", "transientInventory :",
        "constructorTransientWriteInventory = []",
        "externalCallInventory :", "constructorExternalCallInventory = []",
    ),
    "OfficialValidationCheckpoints": (
        "run :", "Prog.RunCompiled", "effectEntry :", "Func.RunCompiled",
        "inputLength :", "sevm.code.size = 5122", "decodedArguments :",
        "officialConstructorArgumentWord", "canonicalAdmin :",
        "addressMask &&& officialParams.admin = 0", "adminNonzero :",
        "minPauseNonzero :", "pauseBounds :", "minHeartbeatNonzero :",
        "heartbeatBounds :", "initialPauseAboveMin :",
        "initialPauseBelowMax :", "initialHeartbeatAboveMin :",
        "initialHeartbeatBelowMax :",
    ),
    "OfficialConstructorErrorArmLayout": (
        "body :", "constructorBodyForProof 616 4898 4282",
        "main :", "officialConstructorValidationBody <?> (.call 1)",
        "aux :", "constructorErrorForProof \"AdminZero\"",
        "constructorErrorForProof \"HeartbeatIntervalAboveMax\"",
        "sites :", "[1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]",
    ),
    "OfficialConstructorExecutionTrace": (
        "target_eq", "fullInput", "prefixCompile", "validationCheckpoints",
        "errorArmLayout", "effectCheckpoints", "Jaune.exec",
        "officialConstructorRequiredGas",
    ),
    "OfficialCreateMessageExecution": (
        "pipeline :", "benvAfterTransfer = .ok benv",
        "G = msg.gas - officialConstructorRequiredGas",
        "processMessage (processCreateMessage.msg msg) = .ok raw",
        "OfficialConstructorExecutionTrace ca",
        "chargeCodeGas msg.benv.stat.rules raw = .ok charged",
        "post = charged.setCode msg.currentTarget",
    ),
    "OfficialCreateMessageResult": (
        "processCreateMessage", "OfficialCreateMessageExecution", "installed",
        "pauseDuration", "heartbeatInterval", "emptyRegistry", "coherent",
        "officialConstructorLogs", "returnData", "gasLeft", "error",
        "refundCounter", "accountsToDelete", "RegistryStable",
    ),
    "OfficialConstructorMessageResult": (
        "msg.target = none", "processMessageCall", "OfficialCreateMessageResult",
        "officialMessageOutputOf", "installed", "pauseDuration",
        "heartbeatInterval", "emptyRegistry", "officialConstructorLogs",
        "returnData", "gasLeft", "error", "accountsToDelete", "RegistryStable",
    ),
    "CanonicalDeploymentBase": (
        "validContext", "ValidContext", "chainId_eq", "SumNof", "computeContractAddress",
        "target_noCodeOrNonce", "target_noStorage", "beaconCode", "historyCode",
        "withdrawalRequestCode", "consolidationRequestCode",
    ),
    "CanonicalOfficialDeploymentBlock": (
        "txs_eq", "decode_eq", "ommers_eq", "withdrawals_eq", "type_eq", ".two",
        "none []", "value_eq", "officialFullCreateInput", "nonce_eq",
        "recoveredSender", "validated", "checked", "upfront_funded",
        "gas_bound", "block_gas_room", "target_eq",
    ),
    "PreparedDeploymentContext": (
        "DeploymentSystemPrefix", "beginTransaction", "incrNonce", "subBal",
        "prepareMessage", "msg_target_eq", "msg_code_eq", "officialFullCreateInput",
        "noCodeOrNonce", "noStorage", "originalState_eq", "pauseCold",
        "heartbeatCold", "pauseOriginal", "heartbeatOriginal", "msg_static_eq",
    ),
    "OfficialDeploymentTransactionResult": (
        "processTransaction", "OfficialConstructorMessageResult", "installed",
        "pauseDuration", "heartbeatInterval", "emptyRegistry", "RegistryStable",
        "blockLogs :", "officialConstructorLogs", "requests", "depositRequests",
        "receiptKeys", "receiptEntry", "receiptLogs", "receiptSucceeded :",
        "withdrawalRequestCode", "consolidationRequestCode",
    ),
    "OfficialDeploymentSuffixResult": (
        "withdrawalRun", "withdrawalReturnData", "consolidationRun",
        "consolidationReturnData", "processGeneralPurposeRequests", "RegistryStable",
    ),
    "DeploymentRoot": (
        "CanonicalDeploymentBase", "CanonicalOfficialDeploymentBlock",
        "OfficialDeploymentTransactionResult", "OfficialDeploymentSuffixResult",
        "stateTransitionUsing", "ChainConfig.pragueOnly", "applyBody",
        "post = deployed.state", "target_ne_zero", "target_not_precompile",
        "installed", "pauseDuration", "heartbeatInterval", "emptyRegistry",
        "RegistryStable", "deployed_validContext", "deployed_chainId",
    ),
    "canonicalDeploymentStep_establishes_root": (
        "prepareCanonicalDeploymentContext", "canonicalDeploymentTransaction_succeeds",
        "canonicalDeploymentSuffix_succeeds", "canonicalDeploymentApplyBody_succeeds",
        "stateTransitionUsing", "DeploymentRoot",
        # Fixed Prague compatibility specialization of the selected-fork root.
        "canonicalDeploymentStepAt_establishes_root", "CoveredFork.prague",
        "hroot.installed", "hroot.stable",
    ),
    "DeploymentRoot.reflReach": ("ReachUsing", "ChainConfig.pragueOnly", "deployed"),
    "DeploymentRoot.reachable_registryStable": (
        "ReachUsing", "chainUsing_preserves_registryStable", "RegistryStable",
    ),
    "DeploymentRoot.reachable_code": ("ReachUsing", "Prog.compile", "runtime officialParams"),
    "DeploymentRoot.reachable_installedCode": (
        "ReachUsing", "lidoCircuitBreakerCode officialParams",
    ),
    "DeploymentRoot.reachable_witness": ("ReachUsing", "∃ entries", "RegistryWitness"),
    "DeploymentRoot.reachable_membership": (
        "ReachUsing", "canonicalAddress", "assignmentSlot", "indexSlot", "findEntry",
    ),
    "DeploymentRoot.reachable_countConservation": (
        "ReachUsing", "countSlot", "assignmentCount", "entries.length",
    ),
    "CanonicalOfficialDeploymentBlockAt": (
        "txs_eq", "decode_eq", "decodeTx (Fork.ruleSet fork)", "ommers_eq",
        "withdrawals_eq", "type_eq", ".two", "none []", "value_eq",
        "officialFullCreateInput", "nonce_eq", "recoveredSender", "validated",
        "validateTransaction (Fork.ruleSet fork)", "checked",
        "initBenv fork base cb.block.header", "upfront_funded", "gas_bound",
        "block_gas_room", "target_eq",
    ),
    "PreparedDeploymentContextAt": (
        "DeploymentSystemPrefix fork", "beginTransaction", "incrNonce", "subBal",
        "prepareMessage", "msg_target_eq", "msg_code_eq", "officialFullCreateInput",
        "msg_rules_eq : msg.benv.stat.rules = Fork.ruleSet fork",
        "msg_fork_eq : msg.benv.stat.fork = fork",
        "noCodeOrNonce", "noStorage", "originalState_eq", "pauseCold",
        "heartbeatCold", "pauseOriginal", "heartbeatOriginal", "msg_static_eq",
    ),
    "OfficialDeploymentTransactionResultAt": (
        "processTransaction", "OfficialConstructorMessageResult", "installed",
        "pauseDuration", "heartbeatInterval", "emptyRegistry", "RegistryStable",
        "blockLogs :", "officialConstructorLogs", "requests", "depositRequests",
        "receiptKeys", "receiptEntry", "receiptLogs", "receiptSucceeded :",
        "withdrawalRequestCode", "consolidationRequestCode",
    ),
    "OfficialDeploymentSuffixResultAt": (
        "withdrawalRun", "withdrawalReturnData", "consolidationRun",
        "consolidationReturnData", "processGeneralPurposeRequests", "RegistryStable",
    ),
    "DeploymentRootAt": (
        "CoveredFork fork",
        "cfg.forkAt cb.block.header.number cb.block.header.timestamp = .ok fork",
        "cfg.rulesAt cb.block.header.number cb.block.header.timestamp =",
        "CanonicalDeploymentBase fork cfg.chainId",
        "CanonicalOfficialDeploymentBlockAt fork cfg.chainId",
        "OfficialDeploymentTransactionResultAt", "OfficialDeploymentSuffixResultAt",
        "stateTransitionUsing cfg base cb.block = .ok deployed",
        "stateTransitionAt fork base cb.block = .ok deployed",
        "applyBody (initBenv fork", "post = deployed.state",
        "configValid : cfg.Valid", "target_ne_zero", "target_not_precompile",
        "deployed.blocks.getLast? = some tip",
        "cfg.rulesAt tip.header.number tip.header.timestamp = .ok rules",
        "¬ rules.isPrecomp ca",
        "installed", "pauseDuration", "heartbeatInterval", "emptyRegistry",
        "RegistryStable", "deployed_validContext",
        "deployed_chainId : cfg.chainId = deployed.chainId",
    ),
    "canonicalDeploymentStepAt_establishes_root": (
        "prepareCanonicalDeploymentContextAt", "canonicalDeploymentTransactionAt_succeeds",
        "canonicalDeploymentSuffixAt_succeeds", "canonicalDeploymentApplyBodyAt_succeeds",
        "stateTransitionUsing", "stateTransitionUsing_reachedStep",
        "hbase.target_not_precompile", "DeploymentRootAt",
    ),
    "DeploymentRootAt.reflReach": ("ReachUsing cfg", "hroot.configValid", "deployed"),
    "DeploymentRootAt.reachable_registryStable": (
        "ReachUsing cfg", "T ≤ timestamp →", "CoveredFork f",
        "T ≤ tip.header.timestamp", "registryStable_iff_stateInv",
        "chainUsing_preserves_inv_of_reached", "registrySpec_preserves",
        "hroot.stable", "RegistryStable",
    ),
    "DeploymentRootAt.reachable_code": ("ReachUsing cfg", "Prog.compile", "runtime officialParams"),
    "DeploymentRootAt.reachable_installedCode": (
        "ReachUsing cfg", "lidoCircuitBreakerCode officialParams",
    ),
    "DeploymentRootAt.reachable_witness": ("ReachUsing cfg", "∃ entries", "RegistryWitness"),
    "DeploymentRootAt.reachable_membership": (
        "ReachUsing cfg", "canonicalAddress", "assignmentSlot", "indexSlot", "findEntry",
    ),
    "DeploymentRootAt.reachable_countConservation": (
        "ReachUsing cfg", "countSlot", "assignmentCount", "entries.length",
    ),
}

MAINNET_CHANNELS = {
    "officialMainnetDeployment_forkAt": (
        "mainnetChainConfig.forkAt officialMainnetDeploymentBlockNumber",
        "officialMainnetDeploymentTimestamp = .ok .bpo2", "decide",
    ),
    "mainnetChainConfig_chainId_eq_officialDeployment": (
        "mainnetChainConfig.chainId = officialMainnetDeploymentChainId",
    ),
    "MainnetDeploymentRoot": (
        "root : DeploymentRootAt mainnetChainConfig base deployed ca",
        "deployed.blocks.getLast? = some tip",
        "tip.header.number = officialMainnetDeploymentBlockNumber",
        "tip.header.timestamp = officialMainnetDeploymentTimestamp",
    ),
    "canonicalMainnetDeploymentStep_establishes_root": (
        "CanonicalDeploymentBase .bpo2 officialMainnetDeploymentChainId",
        "mainnetChainConfig_chainId_eq_officialDeployment",
        "officialMainnetDeployment_forkAt",
        "canonicalDeploymentStepAt_establishes_root mainnetChainConfig .bpo2",
        "CoveredFork.bpo2", "stateTransitionUsing_reachedStep",
        "MainnetDeploymentRoot",
    ),
    "mainnetChainConfig_covered_from_officialDeployment": (
        "officialMainnetDeploymentTimestamp ≤ timestamp",
        "mainnetChainConfig.forkAt number timestamp = .ok f", "CoveredFork f",
        "mainnetChainConfig_covered", "mainnetPragueTimestamp_le_officialDeployment",
    ),
    "MainnetDeploymentRoot.tip_floor": (
        "hroot.tip", "officialMainnetDeploymentTimestamp ≤ tip.header.timestamp",
    ),
    "MainnetDeploymentRoot.reflReach": (
        "ReachUsing mainnetChainConfig deployed deployed", "hroot.root.reflReach",
    ),
    "MainnetDeploymentRoot.reachable_registryStable": (
        "ReachUsing mainnetChainConfig deployed future",
        "hroot.root.reachable_registryStable", "officialMainnetDeploymentTimestamp",
        "mainnetChainConfig_covered_from_officialDeployment", "hroot.tip_floor",
        "RegistryStable",
    ),
    "MainnetDeploymentRoot.reachable_code": (
        "ReachUsing mainnetChainConfig", "Prog.compile", "runtime officialParams",
    ),
    "MainnetDeploymentRoot.reachable_installedCode": (
        "ReachUsing mainnetChainConfig", "lidoCircuitBreakerCode officialParams",
    ),
    "MainnetDeploymentRoot.reachable_witness": (
        "ReachUsing mainnetChainConfig", "∃ entries", "RegistryWitness",
    ),
    "MainnetDeploymentRoot.reachable_membership": (
        "ReachUsing mainnetChainConfig", "canonicalAddress", "assignmentSlot",
        "indexSlot", "findEntry",
    ),
    "MainnetDeploymentRoot.reachable_countConservation": (
        "ReachUsing mainnetChainConfig", "countSlot", "assignmentCount",
        "entries.length",
    ),
}

ORDERED_CHANNELS = {
    "OfficialValidationCheckpoints": (
        "run :", "effectEntry :", "inputLength :", "decodedArguments :",
        "canonicalAdmin :", "adminNonzero :", "minPauseNonzero :",
        "pauseBounds :", "minHeartbeatNonzero :", "heartbeatBounds :",
        "initialPauseAboveMin :", "initialPauseBelowMax :",
        "initialHeartbeatAboveMin :", "initialHeartbeatBelowMax :",
    ),
    "OfficialConstructorEffectCheckpoints": (
        "exactPost :", "state :", "storage :", "logs :", "stack :",
        "memory :", "gasLeft :", "output :", "refundCounter :",
        "returnData :", "error :", "accountsToDelete :",
        "createdAccounts :", "accessedAddresses :",
        "accessedStorageKeys :", "transientStorage :", "siteCounts :",
        "persistentInventory :", "transientInventory :",
        "externalCallInventory :",
    ),
    "OfficialConstructorErrorArmLayout": (
        "body :", "main :", "aux :", "sites :",
    ),
    "OfficialCreateMessageExecution": (
        "pipeline :", "benvAfterTransfer = .ok benv",
        "G = msg.gas - officialConstructorRequiredGas",
        "processMessage (processCreateMessage.msg msg) = .ok raw",
        "OfficialConstructorExecutionTrace ca",
        "chargeCodeGas msg.benv.stat.rules raw = .ok charged",
        "post = charged.setCode msg.currentTarget",
    ),
}

PROOF_ALIAS_TARGETS = {
    "DeploymentProof.constructorRuntimeBaseForProof": "constructorRuntimeBase",
    "DeploymentProof.constructorEventScratchForProof": "constructorEventScratch",
    "DeploymentProof.pushFixedNatForProof": "pushFixedNat",
    "DeploymentProof.pushCompactNatForProof": "pushCompactNat",
    "DeploymentProof.loadArgumentIndexForProof": "loadArgumentIndex",
    "DeploymentProof.storeByteOffsetForProof": "storeByteOffset",
    "DeploymentProof.constructorErrorForProof": "constructorError",
    "DeploymentProof.patchArgumentIndexForProof": "patchArgumentIndex",
    "DeploymentProof.patchFieldLineForProof": "patchFieldLine",
    "DeploymentProof.patchRuntimeLineForProof": "patchRuntimeLine",
    "DeploymentProof.constructorBodyForProof": "constructorBody",
    "DeploymentProof.constructorProgramForProof": "constructorProgram",
    "DeploymentProof.provisionalConstructorPrefixForProof":
        "provisionalConstructorPrefix",
}

# These are proof-engineering architecture rather than public security claims,
# so keep them distinct from PINS.  Exact hashes make the compact reduction
# interface fail closed: downstream proofs never need to unfold a public alias
# whose body points at an inaccessible private executable helper.
REDUCTION_CERTIFICATE_PINS = {
    "constructorRuntimeBaseForProof_eq":
        "7c426ea6e64e92807736503b754434950728996384aa16689cdb3a06b9e2afc4",
    "constructorEventScratchForProof_eq":
        "11f3afd3869a7e088b05f8caa35ccfa886affccbd42bf837698b8471abaea304",
    "pushFixedNatForProof_eq":
        "8af2621c0d97c0fdf4c5bf2036f57390f65538f7c410ef581a30705626953cc8",
    "pushCompactNatForProof_eq":
        "48aacc9dac407e821560027485983269bb99e8dc534008e548fed5934ef43d89",
    "loadArgumentIndexForProof_eq":
        "d8af6fb0e04124b2c0327733a5ff8a4d55486b237a7c693b0c9e3e1e348779f8",
    "storeByteOffsetForProof_eq":
        "1ec139ad147a1801a4f25652729dd959f6974d198f9a8282db32fa4f1a47bec0",
    "constructorErrorForProof_eq":
        "d4763987d91be32150036da6352592d42c87a86b277d0ede0d33f13e60c1c8cc",
    "patchArgumentIndexForProof_eq":
        "ee7bb202f8884d084b181f6afbd4940ed2953d9529bdb2a7f9705fa3c7f5da52",
    "patchFieldLineForProof_eq":
        "bc7a42b83697bf90c27d025cb798fe93a8531b338433958263169e716834f162",
    "patchRuntimeLineForProof_eq":
        "4aafe97642fcb39c5c4e6d28380a0364af7bcc22e3313456fb265368576aa702",
    "constructorBodyForProof_eq":
        "0561345328f7581e0ff45df3c50d58985173a68c6565ca380aa194787d453fb0",
    "constructorProgramForProof_eq":
        "652f9723dc118af58d1e6f57cf9878ede05592e9091c29420f349c06ef767f9c",
    "provisionalConstructorPrefixForProof_eq":
        "25cb23715e608565d03eaae9b740fad0ecaea18d8bfc61289a4c5bcfda99bea9",
}

DECL_KINDS = r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|example)"
DECL_HEAD = re.compile(
    r"^(?P<mods>(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*)"
    r"(?P<kind>" + DECL_KINDS + r")\s+(?P<name>[^\s({\[:]+)")
DECL_BOUNDARY = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:" + DECL_KINDS + r"|namespace|end|section|variable|open|import|attribute|macro|syntax|notation|set_option)\b")


def strip_comments(source: str) -> str:
    """Blank nested Lean comments without touching strings or offsets."""
    out, i, depth = [], 0, 0
    while i < len(source):
        if depth == 0 and source[i] == '"':
            out.append(source[i]); i += 1
            while i < len(source):
                out.append(source[i])
                if source[i] == "\\" and i + 1 < len(source):
                    out.append(source[i + 1]); i += 2; continue
                if source[i] == '"':
                    i += 1; break
                i += 1
            continue
        if source.startswith("/-", i):
            depth += 1; out.append("  "); i += 2; continue
        if depth and source.startswith("-/", i):
            depth -= 1; out.append("  "); i += 2; continue
        if depth:
            out.append("\n" if source[i] == "\n" else " "); i += 1; continue
        if source.startswith("--", i):
            stop = source.find("\n", i)
            stop = len(source) if stop < 0 else stop
            out.append(" " * (stop - i)); i = stop; continue
        out.append(source[i]); i += 1
    if depth:
        fail("unterminated block comment: cannot distinguish code from comment")
    return "".join(out)


def declarations(source: str) -> dict[str, str]:
    """Extract complete namespace-qualified declarations from comment-free text."""
    code = strip_comments(source)
    lines = code.splitlines(keepends=True)
    starts, pos = [], 0
    for line in lines:
        starts.append(pos); pos += len(line)
    namespaces, found = [], []
    for number, raw in enumerate(lines):
        line = raw.rstrip("\n")
        opening = re.match(r"^namespace\s+(\S+)", line)
        if opening:
            namespaces.append(opening.group(1)); continue
        closing = re.match(r"^end\s+(\S+)", line)
        if closing and namespaces and namespaces[-1] == closing.group(1):
            namespaces.pop()
            continue
        head = DECL_HEAD.match(line)
        if head:
            found.append((starts[number], ".".join(namespaces), head.group("name")))
    result = {}
    for offset, namespace, name in found:
        boundary = DECL_BOUNDARY.search(code, offset + 1)
        end = boundary.start() if boundary else len(code)
        # The controlled owners have no duplicate exported names.  Retaining
        # Lean's spelled declaration name (including `DeploymentRoot.foo`) is
        # both less surprising and lets the shared neutral base be pinned.
        key = name
        result[key] = code[offset:end].rstrip()
    return result


def normalise(text: str) -> str:
    # Strings stay tokenised as strings: this does not treat comment-like text
    # in a string as syntax, and whitespace changes outside strings are benign.
    chunks, i = [], 0
    while i < len(text):
        if text[i] != '"':
            j = text.find('"', i)
            j = len(text) if j < 0 else j
            chunks.append(re.sub(r"\s+", " ", text[i:j])); i = j; continue
        j = i + 1
        while j < len(text):
            if text[j] == "\\": j += 2; continue
            if text[j] == '"': j += 1; break
            j += 1
        chunks.append(text[i:j]); i = j
    return "".join(chunks).strip()


def digest(text: str) -> str:
    return hashlib.sha256(normalise(text).encode()).hexdigest()


def source_map(root: Path) -> dict[str, str]:
    result = {}
    for owner, relative in SOURCES.items():
        path = root / relative
        if not path.is_file():
            fail(f"missing required deployment owner: {relative}")
        result[owner] = path.read_text()
    return result


def mainnet_source(root: Path) -> str:
    """The mainnet specialization, read apart from the nine-owner family."""
    path = root / MAINNET_SOURCE
    if not path.is_file():
        fail(f"missing required mainnet deployment owner: {MAINNET_SOURCE}")
    return path.read_text()


def all_declarations(sources: dict[str, str]) -> dict[str, str]:
    result = {}
    for owner, source in sources.items():
        for name, text in declarations(source).items():
            if name in result:
                fail(f"ambiguous declaration name {name!r} across deployment owners")
            result[name] = text
    return result


def public_theorem_names(sources: dict[str, str]) -> list[str]:
    """Derive every non-private theorem/lemma with its Lean namespace."""
    result: list[str] = []
    for source in sources.values():
        namespaces: list[str] = []
        for line in strip_comments(source).splitlines():
            opening = re.match(r"^namespace\s+(\S+)", line)
            if opening:
                namespaces.append(opening.group(1))
                continue
            closing = re.match(r"^end\s+(\S+)", line)
            if closing and namespaces and namespaces[-1] == closing.group(1):
                namespaces.pop()
                continue
            head = re.match(
                r"^(?P<mods>(?:(?:private|protected|noncomputable)\s+)*)"
                r"(?:theorem|lemma)\s+(?P<name>[^\s({\[:]+)", line,
            )
            if head and "private" not in head.group("mods").split():
                result.append(".".join((*namespaces, head.group("name"))))
    return result


def require_axiom_inventory(root: Path, sources: dict[str, str], mainnet_text: str) -> None:
    """Tie this source family to the repository's axiom audit.

    The constructor owner is included only to enforce the private-to-proof
    façade below.  Its pre-existing theorem inventory is outside the nine
    deployment proof owners and therefore outside this exact 179-name set.
    The mainnet module's public theorems are a separate exact inventory.
    """
    names = public_theorem_names({
        owner: source for owner, source in sources.items()
        if owner != "constructor"
    })
    if len(names) != PUBLIC_THEOREM_COUNT or len(set(names)) != len(names):
        fail(
            "public theorem inventory changed "
            f"(expected {PUBLIC_THEOREM_COUNT} unique names, got "
            f"{len(names)} names/{len(set(names))} unique)"
        )
    inventory = "\n".join(sorted(names)) + "\n"
    if hashlib.sha256(inventory.encode()).hexdigest() != PUBLIC_THEOREM_INVENTORY_SHA256:
        fail("public theorem inventory changed")

    if not (root / AXIOM_CHECK).is_file():
        fail("the repository axiom audit source is missing")
    try:
        claims = axiom_audit.stricter_claims(root, AXIOM_CHECK)
    except axiom_audit.AuditError as exc:
        fail(f"the repository axiom audit source is not valid: {exc}")
    mainnet_names = public_theorem_names({"mainnet": mainnet_text})
    if len(mainnet_names) != MAINNET_PUBLIC_THEOREM_COUNT or \
            len(set(mainnet_names)) != len(mainnet_names):
        fail(
            "mainnet public theorem inventory changed "
            f"(expected {MAINNET_PUBLIC_THEOREM_COUNT} unique names, got "
            f"{len(mainnet_names)} names/{len(set(mainnet_names))} unique)"
        )
    mainnet_inventory = "\n".join(sorted(mainnet_names)) + "\n"
    if hashlib.sha256(mainnet_inventory.encode()).hexdigest() != \
            MAINNET_PUBLIC_THEOREM_INVENTORY_SHA256:
        fail("mainnet public theorem inventory changed")

    family = set(names) | set(mainnet_names) | set(STRICTER_CLAIMS)
    observed = {name: axioms for name, axioms in claims.items() if name in family}
    if observed != STRICTER_CLAIMS:
        fail("deployment stricter axiom claims changed")


def require_channels(decls: dict[str, str], mainnet: dict[str, str]) -> None:
    for table, source in ((CHANNELS, decls), (MAINNET_CHANNELS, mainnet)):
        for name, tokens in table.items():
            text = source.get(name)
            if text is None:
                fail(f"missing required public declaration {name}")
            flat = normalise(text)
            for token in tokens:
                if token not in text and token not in flat:
                    fail(f"{name}: missing required semantic fragment {token!r}")
    for name, tokens in ORDERED_CHANNELS.items():
        text = decls[name]
        positions = [text.index(token) for token in tokens]
        if positions != sorted(positions) or len(set(positions)) != len(positions):
            fail(f"{name}: required semantic order changed")


def require_private_proof_facade(decls: dict[str, str]) -> None:
    """Keep executable helpers private and aliases one-way and proof-only."""
    for alias, target in PROOF_ALIAS_TARGETS.items():
        original = decls.get(target)
        if original is None:
            fail(f"missing original private constructor helper {target}")
        if not normalise(original).startswith(f"private def {target}"):
            fail(f"{target}: original constructor helper is not private")
        proof_alias = decls.get(alias)
        if proof_alias is None:
            fail(f"missing proof-only constructor alias {alias}")
        normalised = normalise(proof_alias)
        if not normalised.startswith(f"abbrev {alias}") or \
                not normalised.endswith(f":= {target}"):
            fail(f"{alias}: proof abbreviation is not a one-way alias to {target}")
    certificate_name = "DeploymentProof.lidoCircuitBreakerConstructorProgram_eq"
    certificate = normalise(decls.get(certificate_name, ""))
    for token in (
        "def DeploymentProof.lidoCircuitBreakerConstructorProgram_eq",
        "lidoCircuitBreakerConstructorProgram =",
        "provisionalConstructorPrefixForProof.length",
        "constructorProgramForProof prefixLength",
        ":= by rfl",
    ):
        if token not in certificate:
            fail(f"{certificate_name}: missing proof bridge fragment {token!r}")
    for name, expected in REDUCTION_CERTIFICATE_PINS.items():
        actual = decls.get(name)
        if actual is None:
            fail(f"missing proof reduction certificate {name}")
        observed = digest(actual)
        if observed != expected:
            fail(
                f"{name}: proof reduction certificate changed "
                f"(expected {expected}, got {observed})"
            )


def require_pins(decls: dict[str, str], mainnet: dict[str, str]) -> None:
    for name, expected, actual in (
        *((name, expected, decls.get(name)) for name, expected in PINS.items()),
        *((name, expected, mainnet.get(name)) for name, expected in MAINNET_PINS.items()),
    ):
        if actual is None:
            fail(f"missing pinned declaration {name}")
        if not expected:
            fail(f"{name}: deployment pin is not installed")
        observed = digest(actual)
        if observed != expected:
            fail(f"{name}: complete normalised body changed (expected {expected}, got {observed})")


def premise_discipline(decls: dict[str, str]) -> None:
    base, block = decls["CanonicalDeploymentBase"], decls["CanonicalOfficialDeploymentBlock"]
    forbidden_inputs = (
        "PreparedDeploymentContext", "OfficialConstructorExecutionTrace",
        "OfficialCreateMessageResult", "OfficialConstructorMessageResult",
        "OfficialDeploymentTransactionResult", "OfficialDeploymentSuffixResult",
        "RegistryCoherent", "RegistryStable", "receiptsTrie", "receipt",
        "post :", "poststate", "installed", "returnData",
    )
    for label, text in (("CanonicalDeploymentBase", base), ("CanonicalOfficialDeploymentBlock", block)):
        for token in forbidden_inputs:
            if token in text:
                fail(f"{label}: forbidden execution/result smuggling token {token!r}")

    theorem = decls["canonicalDeploymentStep_establishes_root"]
    head = theorem.split(":= by", 1)[0]
    binders = re.findall(r"\((h\w+)\s*:", head)
    if binders != ["hbase", "henv", "hstep"]:
        fail("root theorem: expected only hbase, henv, hstep proof premises; got " + repr(binders))
    if "hstep : stateTransitionUsing (ChainConfig.pragueOnly chainId)" not in head or \
            "base cb.block = .ok deployed" not in head:
        fail("root theorem: hstep is not the configured successful transition")
    forbidden_premises = ("receipt", "OfficialDeploymentTransactionResult", "OfficialConstructorMessageResult",
                          "RegistryStable", "RegistryCoherent", "applyBody")
    for token in forbidden_premises:
        if token in head:
            fail(f"root theorem: separate result/receipt premise {token!r} is forbidden")

    blockAt = decls["CanonicalOfficialDeploymentBlockAt"]
    for token in forbidden_inputs:
        if token in blockAt:
            fail(f"CanonicalOfficialDeploymentBlockAt: forbidden execution/result smuggling token {token!r}")

    # The selected-fork producer: the schedule lookup and its coverage are the
    # only additions; the configured transition stays the one chain premise.
    label = "selected-fork root theorem"
    head = premise_head(decls["canonicalDeploymentStepAt_establishes_root"])
    expect_binders(label, head, ["hbase", "henv", "hfork", "hforkAt", "hstep"])
    for fragment in (
        "hbase : CanonicalDeploymentBase fork cfg.chainId base sender ca",
        "henv : CanonicalOfficialDeploymentBlockAt fork cfg.chainId base cb txBytes tx sender ca",
        "hfork : CoveredFork fork",
        "hforkAt : cfg.forkAt cb.block.header.number cb.block.header.timestamp = .ok fork",
        "hstep : stateTransitionUsing cfg base cb.block = .ok deployed",
    ):
        if fragment not in head:
            fail(f"{label}: premise is not exactly {fragment!r}")
    forbid_premises(label, head, forbidden_premises)

    # The selected-fork reachable family takes coverage only at or after a
    # timestamp floor the deployed tip has reached.
    for name in (
        "DeploymentRootAt.reachable_registryStable", "DeploymentRootAt.reachable_code",
        "DeploymentRootAt.reachable_installedCode", "DeploymentRootAt.reachable_witness",
        "DeploymentRootAt.reachable_membership", "DeploymentRootAt.reachable_countConservation",
    ):
        head = premise_head(decls[name])
        expected = ["hroot", "hreach", "hcov", "hstart"]
        if name.endswith("reachable_membership"):
            expected.append("htarget")
        expect_binders(name, head, expected)
        for fragment in (
            "hroot : DeploymentRootAt cfg base deployed ca",
            "hreach : BlockChain.ReachUsing cfg deployed future",
            "(T : Nat)",
            "hcov : ∀ (number timestamp : Nat) (f : Fork), T ≤ timestamp → "
            "cfg.forkAt number timestamp = .ok f → CoveredFork f",
            "hstart : ∃ tip, deployed.blocks.getLast? = some tip ∧ T ≤ tip.header.timestamp",
        ):
            if fragment not in head:
                fail(f"{name}: premise is not exactly {fragment!r}")


def premise_head(text: str) -> str:
    """The normalised statement of a theorem, before its proof."""
    return normalise(text.split(":=", 1)[0])


def expect_binders(label: str, head: str, expected: list[str]) -> None:
    binders = re.findall(r"\((h\w+)\s*:", head)
    if binders != expected:
        fail(f"{label}: expected only {', '.join(expected)} proof premises; got {binders!r}")


def forbid_premises(label: str, head: str, forbidden: tuple[str, ...]) -> None:
    for token in forbidden:
        if token in head:
            fail(f"{label}: separate result/receipt premise {token!r} is forbidden")


def mainnet_discipline(mainnet: dict[str, str], root: Path) -> None:
    """The mainnet producer derives BPO2 from the pinned schedule; its
    consequences carry no coverage premise; its coordinates are the
    reference manifest's."""
    label = "mainnet root theorem"
    head = premise_head(mainnet["canonicalMainnetDeploymentStep_establishes_root"])
    expect_binders(label, head, ["hnumber", "htimestamp", "hbase", "henv", "hstep"])
    for fragment in (
        "hnumber : cb.block.header.number = officialMainnetDeploymentBlockNumber",
        "htimestamp : cb.block.header.timestamp = officialMainnetDeploymentTimestamp",
        "hbase : CanonicalDeploymentBase .bpo2 officialMainnetDeploymentChainId base sender ca",
        "henv : CanonicalOfficialDeploymentBlockAt .bpo2 officialMainnetDeploymentChainId base cb txBytes tx sender ca",
        "hstep : stateTransitionUsing mainnetChainConfig base cb.block = .ok deployed",
    ):
        if fragment not in head:
            fail(f"{label}: premise is not exactly {fragment!r}")
    forbid_premises(label, head, (
        "receipt", "OfficialDeploymentTransactionResult", "OfficialConstructorMessageResult",
        "RegistryStable", "RegistryCoherent", "applyBody", "forkAt", "CoveredFork",
    ))

    for name in (
        "MainnetDeploymentRoot.reflReach",
        "MainnetDeploymentRoot.reachable_registryStable", "MainnetDeploymentRoot.reachable_code",
        "MainnetDeploymentRoot.reachable_installedCode", "MainnetDeploymentRoot.reachable_witness",
        "MainnetDeploymentRoot.reachable_membership",
        "MainnetDeploymentRoot.reachable_countConservation",
    ):
        head = premise_head(mainnet[name])
        expected = ["hroot"] if name.endswith("reflReach") else ["hroot", "hreach"]
        if name.endswith("reachable_membership"):
            expected.append("htarget")
        expect_binders(name, head, expected)
        if "hroot : MainnetDeploymentRoot base deployed ca" not in head:
            fail(f"{name}: root premise is not the mainnet deployment root")
        if "reflReach" not in name and \
                "hreach : BlockChain.ReachUsing mainnetChainConfig deployed future" not in head:
            fail(f"{name}: reachability is not over the full mainnet schedule")

    try:
        meta = json.loads((root / REFERENCE).read_text())["deployment"]["manifest"]["meta"]
    except (KeyError, TypeError, ValueError) as exc:
        fail(f"cannot read deployment.manifest.meta from {REFERENCE}: {exc}")
    for name, (key, typ) in MAINNET_COORDINATES.items():
        text = normalise(mainnet[name])
        match = re.fullmatch(
            r"def " + re.escape(name) + r" : " + re.escape(typ) + r" := ([0-9_]+)", text)
        if match is None:
            fail(f"{name}: coordinate is not a plain {typ} literal definition")
        value = int(match.group(1).replace("_", ""))
        if not isinstance(meta.get(key), int) or isinstance(meta.get(key), bool) or \
                value != meta[key]:
            fail(
                f"{name}: coordinate {value} does not match the reference manifest's "
                f"deployment.manifest.meta.{key} ({meta.get(key)!r})"
            )


def trust_and_scope(sources: dict[str, str]) -> None:
    joined = "\n".join(sources.values())
    code = strip_comments(joined)
    # Local proof trust is forbidden even in a comment: a claimed escape hatch
    # must be visible to review.  `unsafe` is caught as a declaration modifier.
    for token in (
        "sorry", "admit", "axiom", "opaque", "native_decide",
        "implemented_by", "unsafe", "AXIOM_EXCEPTIONS",
    ):
        if re.search(r"\b" + re.escape(token) + r"\b", joined, re.I):
            fail(f"deployment family contains forbidden trust token {token!r}")
    if re.search(r"\b(?:Weth|WETH)\w*\b", code):
        fail("deployment family imports or names WETH; Lido contracts are siblings")
    if re.search(r"(?m)^\s*partial\s+(?:def|theorem|lemma|instance)\b", code):
        fail("deployment family contains a forbidden object-level partial declaration")
    # Scope terms are rejected in code and claims/comments alike.  `create` is
    # not banned: direct top-level creation is required; CREATE2 is not.
    for token in ("factory", "proxy", "CREATE2", "CREATE3", "mainnet", "clone"):
        if re.search(r"\b" + token + r"\b", joined, re.I):
            fail(f"deployment family makes forbidden scope/identity claim {token!r}")


def mainnet_trust_and_scope(source: str) -> None:
    """The family's trust and scope bans, except that this module may name
    mainnet, which is its whole subject."""
    code = strip_comments(source)
    for token in (
        "sorry", "admit", "axiom", "opaque", "native_decide",
        "implemented_by", "unsafe", "AXIOM_EXCEPTIONS",
    ):
        if re.search(r"\b" + re.escape(token) + r"\b", source, re.I):
            fail(f"mainnet deployment module contains forbidden trust token {token!r}")
    if re.search(r"\b(?:Weth|WETH)\w*\b", code):
        fail("mainnet deployment module imports or names WETH; Lido contracts are siblings")
    if re.search(r"(?m)^\s*partial\s+(?:def|theorem|lemma|instance)\b", code):
        fail("mainnet deployment module contains a forbidden object-level partial declaration")
    for token in ("factory", "proxy", "CREATE2", "CREATE3", "clone"):
        if re.search(r"\b" + token + r"\b", source, re.I):
            fail(f"mainnet deployment module makes forbidden scope/identity claim {token!r}")
    imports = re.findall(r"(?m)^import\s+(\S+)", code)
    if imports != ["Blanc.LidoCircuitBreakerDeploymentRoot", "Blanc.LadderReached"]:
        fail(f"mainnet deployment module imports changed: {imports!r}")


def actual_execution_sites(decls: dict[str, str]) -> None:
    """Cross-boundary checks that cannot be satisfied by isolated field names."""
    requirements = {
        "OfficialConstructorExecutionTrace": ("Jaune.exec", "OfficialConstructorEffectCheckpoints"),
        "OfficialCreateMessageResult": ("processCreateMessage msg = .ok post",),
        "OfficialConstructorMessageResult": ("processMessageCall msg = .ok (post, out)",),
        "OfficialDeploymentTransactionResult": ("processTransaction ctx.txInput .init tx 0 = .ok (post, bout)",),
        "OfficialDeploymentSuffixResult": ("processCheckedSystemTransaction", "processGeneralPurposeRequests"),
        "DeploymentRoot": ("stateTransitionUsing", "applyBody", "Nonempty (OfficialDeploymentSuffixResult"),
        "OfficialDeploymentTransactionResultAt": ("processTransaction ctx.txInput .init tx 0 = .ok (post, bout)",),
        "OfficialDeploymentSuffixResultAt": ("processCheckedSystemTransaction", "processGeneralPurposeRequests"),
        "DeploymentRootAt": (
            "stateTransitionUsing cfg base cb.block = .ok deployed",
            "applyBody (initBenv fork base cb.block.header)",
            "Nonempty (OfficialDeploymentSuffixResultAt",
        ),
    }
    for name, fragments in requirements.items():
        for fragment in fragments:
            if fragment not in decls[name]:
                fail(f"{name}: missing actual execution/body site {fragment!r}")


def run(root: Path) -> None:
    sources = source_map(root)
    mainnet_text = mainnet_source(root)
    decls = all_declarations(sources)
    mainnet = declarations(mainnet_text)
    require_pins(decls, mainnet)
    require_channels(decls, mainnet)
    require_private_proof_facade(decls)
    premise_discipline(decls)
    mainnet_discipline(mainnet, root)
    actual_execution_sites(decls)
    trust_and_scope(sources)
    mainnet_trust_and_scope(mainnet_text)
    require_axiom_inventory(root, sources, mainnet_text)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT,
                        help="repository root (used by source-level falsifiers)")
    parser.add_argument("--print-pins", action="store_true",
                        help="print observed pins; review aid, never a passing check")
    args = parser.parse_args(argv)
    try:
        decls = all_declarations(source_map(args.root))
        mainnet = declarations(mainnet_source(args.root))
        if args.print_pins:
            for table, found in ((PINS, decls), (MAINNET_PINS, mainnet)):
                for name in table:
                    if name not in found:
                        fail(f"missing pinned declaration {name}")
                    print(f"{name} {digest(found[name])}")
            return 0
        run(args.root)
    except (Failure, OSError, UnicodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        print(f"{VERDICT}: FAIL", file=sys.stderr)
        return 1
    print(
        f"{VERDICT}: PASS ({len(PINS)} full pins + {len(MAINNET_PINS)} mainnet pins, "
        f"{len(REDUCTION_CERTIFICATE_PINS)} reduction certificates, "
        f"{sum(map(len, CHANNELS.values())) + sum(map(len, MAINNET_CHANNELS.values()))} "
        f"semantic fragments, "
        f"{PUBLIC_THEOREM_COUNT} + {MAINNET_PUBLIC_THEOREM_COUNT} mainnet public theorems "
        f"under the union axiom walk, "
        f"{len(MAINNET_COORDINATES)} coordinates bound to the reference manifest, "
        f"{len(STRICTER_CLAIMS)} stricter claims)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
