#!/usr/bin/env python3
"""Fail-closed local assurance for the Stage 7 Registry-history theorem family.

The family is the induction principle that carries `RegistryWitness` through
*arbitrary* histories: a storage-only coherent state packaged as a
`ContractSpec`, discharged one dispatch target at a time, joined across the
exact hybrid dispatcher, transported across arbitrary external calls, and then
lifted by the generic ladder to messages, transactions, blocks and chain
reachability.

What this gate exists to prevent is not a broken proof -- the elaborator
catches those -- but a *quietly narrowed claim*.  Three narrowings would leave
the family looking untouched:

  1. `RegistryCoherent`, `registrySpec`, `RegistryStable`, `StorFixed` and
     `Coherent` are `def`s and a `structure`.  Gutting any of them leaves every
     theorem header in the family byte-identical while making all of them
     trivially provable and vacuous.  `DEFINITION_PINS` holds their whole
     declaration text, and `SEMANTIC_CHANNELS` holds the tokens each body must
     still mention, so a careless re-pin still trips the second net.

  2. The seventeen dispatch targets are the family's coverage obligation.  An
     endpoint quietly demoted from "proved here" to "assumed by the caller" is
     a strictly weaker theorem that still compiles and still reads as complete.
     `dispatcher_inventory` derives the seventeen entries FROM `funcs`' own
     source and `coverage` requires the proof side to account for exactly them,
     in program order.

  3. A cooperative-world premise -- a pinned callee, a non-reentrancy
     assumption, a direct-call-only depth restriction, target honesty, an
     identification of the post-callback entry list with the entry list, or
     `PauseSuccessNoninterference` itself -- turns an open-world result into a
     closed-world one while every conclusion stays the same.  `open_world_bar`
     is a POSITIVE allowlist: every binder of every pinned statement must
     either be a declared data type or match one of the admissible hypothesis
     shapes below.  A premise nobody anticipated fails by default, whatever it
     is called; a denylist would only catch the names we thought of, so the
     token denylist here is a redundant second net and never the mechanism.

The CLI contract is the house one: exit 0 iff pass, and the output ends with
exactly one verdict line.

Owners
------
All three of `Blanc/LidoCircuitBreakerHistory.lean`,
`Blanc/LidoCircuitBreakerHistoryEndpoints.lean` and
`Blanc/LidoCircuitBreakerHistoryChain.lean` are committed and checked in full.
The Chain owner was dormant behind `CHAIN.active` while `registrySpec_sound`
carried a `sorry`; that proof is closed and the switch is on, so its pins, its
channels, its allowlist, its trust scan and its axiom probe are all live.

A fourth net was added once the family was complete.  `VOCABULARY_PINS` pins
the declarations this family is WRITTEN IN but does not own -- `RegistryWitness`
and the `ContractSpec` premise vocabulary in `Blanc/Ladder.lean`.  Without it a
pinned statement can keep its digest while the words it is made of change
meaning underneath it, which is not hypothetical: threading `Mem.Wf` through
the ladder moved `DispatchInv` and three Chain statements from `Pre` to `PreWf`
while every public S7 digest stayed byte-identical.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

VERDICT = "S7 Registry-history assurance"


# --------------------------------------------------------------------------
# Owners
# --------------------------------------------------------------------------

# The two committed proof owners.  `history` states the invariant, the spec,
# the stable checkpoint, the `StorFixed` API and the exact hybrid-dispatcher
# reduction; `endpoints` discharges the fifteen non-Registry-mutating dispatch
# targets and states the two collection theorems.
OWNERS = {
    "history": "Blanc/LidoCircuitBreakerHistory.lean",
    "endpoints": "Blanc/LidoCircuitBreakerHistoryEndpoints.lean",
}

MODULES = {
    "history": "Blanc.LidoCircuitBreakerHistory",
    "endpoints": "Blanc.LidoCircuitBreakerHistoryEndpoints",
}

# `Blanc.LidoCircuitBreakerHistoryEndpoints` imports `...History`, so importing
# the former alone reaches both owners' declarations.
AXIOM_PROBE_IMPORTS = ("Blanc.LidoCircuitBreakerHistoryEndpoints",)

# The program whose dispatcher the coverage obligation is derived from.  This
# file is NOT an owner: it is read, never pinned, because it is the Lido
# CircuitBreaker program itself and has its own gates.
PROGRAM_SOURCE = "Blanc/LidoCircuitBreaker.lean"


class ChainActivation:
    """The switch for the Chain owner, now ACTIVE.

    `Blanc/LidoCircuitBreakerHistoryChain.lean` was dormant while
    `registrySpec_sound` still carried a `sorry`.  That proof is closed, the
    seventeen endpoint obligations are discharged, and this owner is checked
    in full: its pins, its semantic channels, its open-world allowlist, the
    trust scan and the axiom probe.

    `--chain-dry-run` survives activation as a review aid.  While the owner
    was dormant it read the frozen revision named by `pinned_at`; now that the
    owner is live, reporting about bytes that no longer exist would be worse
    than not reporting at all, so `pinned_at()` resolves the branch tip and
    `chain_source` reads the working file.

    Reactivating a future in-flight successor is the reverse: set `active` to
    `False` and pin `pinned_at` to a literal revision.
    """

    active = True
    key = "chain"
    path = "Blanc/LidoCircuitBreakerHistoryChain.lean"
    module = "Blanc.LidoCircuitBreakerHistoryChain"

    # The revision this owner's pins describe.  While the owner is ACTIVE that
    # is whatever the branch tip currently is, resolved on every call, because
    # the pins are taken from the working tree and a stale literal here would
    # make `--chain-dry-run` report about bytes that no longer exist.  While
    # DORMANT this must be a literal revision, so that a deliberate
    # restatement stays distinguishable from a drifting one.
    _frozen_at = None

    @staticmethod
    def pinned_at() -> str:
        if ChainActivation._frozen_at is not None:
            return ChainActivation._frozen_at
        run = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=ROOT, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        if run.returncode:
            fail("cannot resolve the branch tip for the Chain owner: "
                 + run.stderr.strip())
        return run.stdout.strip()

    # The twelve public statements the packet requires this owner to pin.
    # Checked for presence in `HEADER_PINS["chain"]` whether active or not, so
    # a pin deleted while the owner is dormant still fails the gate.
    required_public = (
        "registrySpec_sound",
        "registrySpec_preserves",
        "processMessageCall_preserves_registryStable",
        "processTransaction_preserves_registryStable",
        "applyTransactions_preserves_registryStable",
        "stateTransitionWith_preserves_registryStable",
        "stateTransitionUsing_preserves_registryStable",
        "stateTransition_preserves_registryStable",
        "chainUsing_preserves_registryStable",
        "chain_preserves_registryStable",
        "coherent_of_call",
        "coherent_of_statcall",
    )


CHAIN = ChainActivation


def active_owners() -> dict:
    owners = dict(OWNERS)
    if CHAIN.active:
        owners[CHAIN.key] = CHAIN.path
    return owners


def active_modules() -> dict:
    modules = dict(MODULES)
    if CHAIN.active:
        modules[CHAIN.key] = CHAIN.module
    return modules


def probe_imports() -> tuple:
    if CHAIN.active:
        return AXIOM_PROBE_IMPORTS + (CHAIN.module,)
    return AXIOM_PROBE_IMPORTS


class Failure(Exception):
    pass


def fail(message: str) -> None:
    raise Failure(message)


# --------------------------------------------------------------------------
# Lean source parsing
# --------------------------------------------------------------------------

OPEN = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
CLOSE = {v: k for k, v in OPEN.items()}

DECL_KINDS = r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|example)"
DECL_HEAD = re.compile(
    r"^(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*)"
    r"(?P<kind>" + DECL_KINDS + r")\s+(?P<name>[^\s({\[:]+)")
DECL_BOUNDARY = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:" + DECL_KINDS +
    r"|namespace|end|section|variable|open|import|attribute|macro|syntax|notation|set_option)\b")


def strip_comments(source: str) -> str:
    """Blank every Lean comment, preserving offsets, newlines and strings.

    Header pins and the open-world bar are computed on this text, so rewording
    a docstring does not force a re-pin -- while a docstring that starts
    claiming something in code does, because the trust scan reads BOTH this
    text and the comment text it removed.  Nesting is honoured (`/- /- -/ -/`),
    `--` inside a string literal is not a comment, and string contents survive
    intact because `funcs`' selector names are parsed out of them.
    """
    out = []
    index, size, depth = 0, len(source), 0
    while index < size:
        char = source[index]
        if depth == 0 and char == '"':
            out.append(char)
            index += 1
            while index < size:
                out.append(source[index])
                if source[index] == "\\" and index + 1 < size:
                    out.append(source[index + 1])
                    index += 2
                    continue
                if source[index] == '"':
                    index += 1
                    break
                index += 1
            continue
        if source.startswith("/-", index):
            depth += 1
            out.append("  ")
            index += 2
            continue
        if depth > 0 and source.startswith("-/", index):
            depth -= 1
            out.append("  ")
            index += 2
            continue
        if depth > 0:
            out.append("\n" if char == "\n" else " ")
            index += 1
            continue
        if source.startswith("--", index):
            end = source.find("\n", index)
            end = size if end < 0 else end
            out.append(" " * (end - index))
            index = end
            continue
        out.append(char)
        index += 1
    if depth:
        fail("unterminated block comment; comment/code separation is unsafe")
    return "".join(out)


def comment_text(source: str) -> str:
    """The complement of `strip_comments`: comment bytes, code blanked."""
    code = strip_comments(source)
    return "".join(
        " " if code[i] not in (" ", "\n") else source[i]
        for i in range(len(source))
    )


def declarations(source: str) -> list:
    """Every declaration in a module, namespace-qualified and sliced exactly.

    A slice never crosses into the next declaration or out of its namespace,
    so a pin can never name one result and hash a neighbour.
    """
    code = strip_comments(source)
    lines = code.split("\n")
    offsets, position = [], 0
    for line in lines:
        offsets.append(position)
        position += len(line) + 1
    namespaces, found = [], []
    for index, line in enumerate(lines):
        opened = re.match(r"^namespace\s+(\S+)", line)
        if opened:
            namespaces.append(opened.group(1))
            continue
        closed = re.match(r"^end\s+(\S+)", line)
        if closed:
            if namespaces and namespaces[-1] == closed.group(1):
                namespaces.pop()
            continue
        head = DECL_HEAD.match(line)
        if head:
            found.append((offsets[index], head, ".".join(namespaces)))
    result = []
    for offset, head, namespace in found:
        boundary = DECL_BOUNDARY.search(code, offset + 1)
        end = boundary.start() if boundary else len(code)
        result.append({
            "kind": head.group("kind"),
            "name": head.group("name"),
            "namespace": namespace,
            "private": "private" in head.group("mods"),
            "text": code[offset:end].rstrip(),
        })
    return result


def key_of(declaration: dict) -> str:
    """The pin key: the declaration's name below `Blanc.LidoCircuitBreaker`."""
    namespace = declaration["namespace"]
    prefix = "Blanc.LidoCircuitBreaker"
    if namespace == prefix:
        return declaration["name"]
    if namespace.startswith(prefix + "."):
        return namespace[len(prefix) + 1:] + "." + declaration["name"]
    fail(f"declaration {declaration['name']} sits outside {prefix} "
         f"(namespace {namespace!r}); this family may not leave that namespace")
    return ""


def qualified(declaration: dict) -> str:
    return declaration["namespace"] + "." + declaration["name"]


def definition_marker(text: str) -> int:
    """Offset of the definition marker: a depth-0 `:=`, or the first `|` arm.

    Equation-compiler declarations (`SilentIn`, `funcInv_prependStoresRev`)
    have no `:=` at all; cutting at their first alternative bar is what keeps
    their statement pinned rather than skipped.
    """
    depth = 0
    for index, char in enumerate(text):
        if char in OPEN:
            depth += 1
        elif char in CLOSE:
            depth -= 1
        elif char == ":" and depth == 0 and text[index:index + 2] == ":=":
            return index
        elif char == "|" and depth == 0 and (
                index == 0 or text[:index].rstrip(" ").endswith("\n")):
            return index
    return -1


def statement_of(declaration: dict) -> str:
    """The declaration's statement: everything before its definition marker."""
    cut = definition_marker(declaration["text"])
    if cut < 0:
        fail(f"{declaration['name']}: no definition marker; the statement "
             "cannot be separated from the proof, so it cannot be pinned")
    return declaration["text"][:cut]


def normalize(text: str) -> str:
    return " ".join(text.split())


def digest(text: str) -> str:
    return hashlib.sha256(normalize(text).encode()).hexdigest()


def split_binders(statement: str, name: str) -> tuple:
    """Split a statement into its binder groups and its conclusion."""
    index = statement.index(name) + len(name)
    depth, start, binders = 0, None, []
    size = len(statement)
    while index < size:
        char = statement[index]
        if char in OPEN:
            if depth == 0:
                start = index
            depth += 1
        elif char in CLOSE:
            depth -= 1
            if depth == 0:
                binders.append(statement[start:index + 1])
                start = None
        elif depth == 0 and char == ":":
            if statement[index:index + 2] in ("::", ":="):
                index += 2
                continue
            return binders, normalize(statement[index + 1:])
        index += 1
    return binders, ""


def binder_parts(binder: str) -> tuple:
    """(bracket, [names], type) for one binder group."""
    bracket, inner = binder[0], binder[1:-1]
    depth = 0
    for index, char in enumerate(inner):
        if char in OPEN:
            depth += 1
        elif char in CLOSE:
            depth -= 1
        elif char == ":" and depth == 0:
            if inner[index:index + 2] in ("::", ":="):
                continue
            if index and inner[index - 1] == ":":
                continue
            return bracket, inner[:index].split(), normalize(inner[index + 1:])
    return bracket, [], normalize(inner)


# --------------------------------------------------------------------------
# Exact pins
# --------------------------------------------------------------------------
#
# `HEADER_PINS` holds the SHA-256 of every theorem's normalized STATEMENT --
# binders, premises, quantifier altitude and conclusion, whitespace-collapsed
# and comment-free.  A weakened hypothesis list, an added premise, a renamed
# binder or a moved quantifier changes the digest; a reflowed docstring does
# not.
#
# `DEFINITION_PINS` holds the SHA-256 of the WHOLE declaration text of every
# `def` and `structure` -- statement and body together -- because these carry
# the family's content where no header pin reaches.  A re-proof of one of
# `registrySpec`'s side-condition fields therefore forces a re-pin and a
# review; that is deliberate, and it is the cheap half of the price for
# catching a gutted `Inv`.
#
# Every declaration in an active owner must appear in exactly one of the two
# tables, and every table entry must name a declaration that exists.  That one
# rule is the deletion control AND the addition control: a pinned theorem that
# is deleted or commented out leaves a table entry with no declaration, and a
# new theorem that nobody pinned leaves a declaration with no entry.

# >>> HEADER PINS >>>
HEADER_PINS = {
    "chain": {
        "RegistryStable.countConservation": "7dc9d9d097f7a5ed984b3426610dfdbcdb007ae711e8b3f0d1ec58b050ed0e9e",
        "RegistryStable.installedCode": "41a7a10fa90009b7ceb0e682eaae597c888428f439cd6b108a02a6293201630b",
        "RegistryStable.membership": "d231f193d9c11dc6e5110e827efc4677d2bdeebbf2b359cf9db98760761b3f88",
        "RegistryStable.witness": "8223252dc9bcc9444e013cf099698c1d1282532a53b5198ec106d5777f413494",
        "applyTransactions_preserves_registryStable": "216b5d62d37262ac4a8283537f335721f10982be48ad92e45921ff6f92c49289",
        "arbitraryExec_post_registryFields": "0a56502f3a3ef61956b59321465e5e6a4a2f6c4369239b0a677cc42ea250110c",
        "arbitraryFuture_registryFields": "622966ab492e4424080b6be75b2db09e86a883be32a3dacdce687bcec0054f36",
        "byteArray_mk_toArray_toList": "833da9eb2aec073dbae18ba4a12124b84186c8c8f7855d5c38f89390dcc8d6ff",
        "canonicalAddress_of_validAdr": "ab44120194f37987906fcff8a601470e5d6915bdd1e86773eb4be3006b3c470c",
        "chainUsing_future_countConservation": "faa418e40238422f55ce6ff55b056985a6b18b6ca3dd736f735d4d4ff970bb01",
        "chainUsing_future_installedCode": "db5ccd573daf4a1378370723f4c68c9302d621c25ae91356616c45b88706ab35",
        "chainUsing_future_membership": "aaad5e70bbf514d0f76c6a05df6dbc65ae05927d5fc8752fa01e007734aeea50",
        "chainUsing_future_witness": "a781e8139ad4980b25abf0164c9002dc670911c29c794c704e88088ee9a7edb4",
        "chainUsing_preserves_registryStable": "5a7616fb3453eb6237cc0f02587269c9dfcea53cb96bef2fee89e10f6a325d9b",
        "chain_future_countConservation": "126adfae446c60cea2733475117b9d5ea131c98a04efbd71446430f54a6bf95d",
        "chain_future_installedCode": "b85f35e640916c95b7bfe327f900c90690428f1a5503c883749eabc03a07465d",
        "chain_future_membership": "fd31c5dcdfbc15de120d9fdb13e8b9239e6a8e07678ea1348a1d3d6cd84d8171",
        "chain_future_witness": "3bc21c16606ed4a08cb11237c2df726208a309c7568452790dbc40279182b899",
        "chain_preserves_registryStable": "379a64905d5e77c1fc786cca27e020af6a21f9eb1081ff4a39c9fc1d86831c7a",
        "code_of_getCode_eq": "9eceb2c4927697718444e48be5ac7244f1bd22b36817c610aab53e3625b5a31b",
        "code_of_ninst": "d2223c28b97a7c0065ded9a7199503aed5682db64f31b588ed9aa2c451e48f97",
        "coherent_decodePausedResult": "a86b5eae04d4ea1ee7fa2f9248cff86e2ff2e50e022bd34cf212ec7aba1b6b96",
        "coherent_of_call": "65c1bb0a008188b7f6ca7530bab5fd7034ec587b3847a061151a750555e49c77",
        "coherent_of_childFrame": "3c66c3cbb5072d6a97364391dff57f663c02dd8b59f116bdc2b4f7c50ca59a3b",
        "coherent_of_pauseKernelRun": "05586b650f7988578c3a7a6300ac20e7c08bb6b8aa6117af516dfb82733015e2",
        "coherent_of_statcall": "8419a5a1efc954bb60e35f6c0e463978f61d1df2600edac30eeeec4e2b110c58",
        "coherent_of_stor_eq": "551252a0eb60d8b475dfcac896f1925944c673ae5727e4b27de9e18f8ed81747",
        "coherent_pause": "f93b9cf653e402f26d5a42959706485877fdc0c78deeafbb97ec6c58afca65df",
        "coherent_pauseAfterSet": "a7011633d88b410cdf8c2553861abbcb4b399a3469cf01998ebaea27ec08db30",
        "coherent_pauseExpiryFinish": "0c60bd470c5dfdf553e744892d43bdbc366c0a10a935fe7ae9675997bd7484f5",
        "coherent_pauseSuccess": "1eb7968c6719dbd66f9595d0f235876bb76794e990e7db3d41eefc5d10087118",
        "coherent_registerPauser": "073d49d054131384f0ea0bc0e1264ccef3451288386883a70a915eeb0626225e",
        "countConservation_of_witness": "d22f06901a52e5c525291e7e5a1b5d823c59a046e50d94f3934d6010eec5c090",
        "emptyRegistryWorld_get": "d26476e458668b113473ec9e9621ac7818d03bfe076fc00c8cb1afefd3b6cd65",
        "emptyRegistryWorld_registryFields": "c1bdbecb7f6ae2edb3bb1732d4ae1af9cedd51f5ca43f9d6595e2387c3cc5886",
        "emptyRegistryWorld_registryStable": "e2f9f534bf9c45ea39ce150d6c978bda0f073260d6b16fb42ca1dd0f9a491184",
        "emptyRegistryWorld_witness": "cc20dec3daeb91307cfc0e7608883ea41a041fbd553d7271a5531d5b81182928",
        "getDelegatedCodeAddress_of_compile": "f66592652157a05d32cda724de8f7223b7bc74467b91d640b75d1610e0c925cf",
        "get_bubbleRevertSlot": "2cacc0b135c8adfd5d72ba23accba9fe28c69039cb9cd5dc2e36134f5323ae84",
        "get_setPauserSlot": "356a0b153cab58e5fc360d6659fad2f00844a0fe5362b87f45a010d563f10cd3",
        "inv_prependStoresRev": "99b793be0df1604ba759744fd411ea3526b27502468e0f6e2627eadc44740507",
        "loadWord_image": "022f4737a3d9e540eda72a78f97afaa5827d2645462fe8befb601c0bf883472c",
        "mem_reads_data": "ab0541e0dfa602787703695b60ad3802a71d8152bef0c99a0165b220a9bce3f7",
        "membership_of_witness": "088e491da668b5dba5ee947948d09559b8ba62ff528e4340160a07ffd7d98bde",
        "mstoreAt_image": "d0096a04bc4e5fd4e171485ed45f392e7a02280c36292d5c51892f8f62d92f54",
        "ninst_codePreserve": "48005abd46b387de3f3e07e7b67984d54094f05aa763c8dd608b3667b4992632",
        "pause_funcSound": "0f8f4f627e60c022bcc8067fed1a0f3eb41e294158283ae53ce11b9972c60a57",
        "prefix_of_loadWord": "928ce57c0b0c886947c16d463eb5845d9325fd6c76ca161aa182a49bd5e8893d",
        "processMessageCall_preserves_registryStable": "3ef951b8bc65c64427d44f69d865aacf7c0249ad03e55af41b7133998331197e",
        "processTransaction_preserves_registryStable": "3bf66acf5d10535ef86e3322c3853939a12b1e1c296a1bdd334fcc5ccc942ade",
        "read_writeAt_before": "85c845d584c9b9bb05ab3773af90d3caacda6169bf1d8cab4fbbd51042c52873",
        "read_writeAt_self": "e99b44fd30069121952d8c4744913f3f87b2208d3e7d3b899837c0c0145031f4",
        "registerPauser_funcSound": "27f070b62065a2522b330ae2fe4089c247837133ac2c194d97735d3bf7d73a6f",
        "registrySpec_preserves": "8c9fd57bcd6db635dcbeeb49151d882c7eed51fd7f14429b61fce9721c6658d3",
        "registrySpec_sound": "9d734939dbef20c5d9ebc23eafbbba573f40928d8d1ddb44c61d874490d3f09b",
        "registryView_getStor": "b1027f30a809194c720b520851cf8c637bfd095562da5a430adacb00110b19ec",
        "stateTransitionUsing_preserves_registryStable": "3bcf31c79ca247a7e1da8257b102850a525da4fbd987bb33dc112f274ea88bfe",
        "stateTransitionWith_preserves_registryStable": "66bad9dce69cb11405add9c6dd4a20b0c1fe65d0478dfa4467c8baaffda9b9b3",
        "stateTransition_preserves_registryStable": "6b35ef2155acbddf9deb5fa585e78e584518a9b2907cb0adc1e8eecda5b5d4ed",
        "storFixed_panicData": "299e2de33b8ee57325bd573d07682a77645dab5966791407b6a72c90891529dd",
        "storFixed_pauseFailedError": "33afc0df5c18a96f633763a2ece5f6d0a759abdbbb3dcf2acbcff00b24070a0e",
        "storFixed_reentrantCallError": "6c06d4a2c38ac889ff0791a9835de3a8685cd7f84fec8da82dc4f0ba19ac9cf8",
        "storFixed_revReturnData": "35fa1fb99aaf5928e589fee886454b23261ab21be3f2acc9f9bc9f6b590cc719",
        "wf_of_mem_eq": "42de7af2573700b9593a25fd9da7ab8ff418dd5f93de91e07bf28e992715cd71"
    },
    "endpoints": {
        "Coherent.branch": "6d6e880d4d47972acf6dae481c57875cb0bf8161d528036caee19823b2fe2726",
        "Coherent.call": "72589160cc127b53a3d2fe62c1828cad25ba91422efd4e7abe70328c42461d48",
        "Coherent.callerTagSstore": "680d078fc12b5012aa2b42beadf5edcff089ac2482634e31059ec3118f531d42",
        "Coherent.next": "52c5fbbd2e35d097197358e1cd45e022196b584d35394483d137f1245f40375c",
        "Coherent.of_storFixed": "1c504862b64e605132238883daacce997a81632b8a5682113fe3e84c80a9462c",
        "Coherent.prepend": "e2818ec9c7614c56810c3266612c6d567a891f54e603bcd2ec0175ded5568d73",
        "Coherent.pushSstore": "8e51982b560a475fdd64392c59bcd4f48194cc7032b4cbe51b3c2c436089564e",
        "RegistryCoherent.config_set": "5b29997ada5d309bae88a4b64562c2034f098339a6c8f7762d6abd473acb823f",
        "RegistryCoherent.expiry_set": "27471922e926a1839d3f618ad0508956051528f215626655422d3f6ee05ab0df",
        "RegistryWitness.config_set": "360c70a19b0b65013d97ed6fa326d3c7b793781c950fbfa06f43dbf0afe19e2f",
        "admin_funcSound": "7cf0756a974d7519ab7e2279f2900afa2560c9d64debcc7d46d89371a4e01c89",
        "canonicalAddress_toB256": "a40444310fd6ae18504a53aa7eb84cd3d1b6f46dd1af079f6b14f61419404ab6",
        "coherent_heartbeat": "b8ad579b5a26addac5308256b841eed25904e32f468ed4ac18d1b46ce1608dd8",
        "coherent_setHeartbeatInterval": "acb55cfc66b3559acb10da681ba0346bf5f14dd1b0f43ad6f5c48fe0ccae7bf0",
        "coherent_setPauseDuration": "0004191063e862f47b57f9990b2a175432906a46dab808cd137ece3cb1892fe8",
        "configSlot_ne_arrayEntrySlot": "0b78be51a44e3cea84583d6679e4a386cf7727dc8dd5b38650ff67147928eac0",
        "configSlot_ne_arrayLengthSlot": "13dbfa4566f7443c5e57f509de41d21cd2505566c6df4895a34f198ced9105ad",
        "configSlot_ne_assignmentSlot": "b659728b90127eea0421050f146b90f1cd579b4a2555ac7cd70f93ae356129d9",
        "configSlot_ne_countSlot": "321e480a4e3d76dd490db50dfeef69beb3323df80fcf09dcd90689a06700f02c",
        "configSlot_ne_indexSlot": "148680149f9074c7e389a09a5e3ea5860bcfcb9261f34d188ef7c244c1e80bf3",
        "enumLoopSlot_closed": "fa07e8d8f7cdb4b725036957a970a7a18543ac68f7f0a4b4a38b804a4f214856",
        "funcInv_prependStoresRev": "6e6c8e8f4f8ee7b5a343d1f477e7c55dc4a258d048afcc90862064620c36662a",
        "funcSound_of_mem_funcs": "df3b9853eae0974020fc74a3698590fb9c0e57adb3b04bbd3f8e48c000b8f839",
        "funcSound_of_mem_nonRegistry": "97c18b9904352c901bfc12ed3c6c08183b9f7748e0113570a0e6f740ae52aaa5",
        "getPausableCount_funcSound": "5d0f7a6b610016015bcf2c19d58510dd57239306e914c7acfac6e13cb727ae27",
        "getPausables_funcSound": "89ef152cf1132d8ead5450a8b2b17697d4670fcac6ee5058711f7676840638a8",
        "getPauser_funcSound": "cb59fd88d6ab7c014ea61af8dd45463f65c883c1018c6a36ee781e59d4286e43",
        "getStor_eq_of_run_silentIn": "59d24991a54c34c73817e2d7543ce3ef23eb2fa7943e4a84822e33c8ca210051",
        "get_arithmeticPanicSlot": "427009816732fcbc1282ff4434fdb2796848eb4da682e73c4fb555d18fbcc20b",
        "get_emptyRevertSlot": "0bc0343bd82804d3eb73760960d28244348e3edcb7aff4651e694f72905c0e80",
        "get_enumLoopSlot": "4fb2ee90afaf9faff053c04ce00885fb838c0958ca32be036d013a3a01a7dd4f",
        "heartbeatExpiry_funcSound": "31ed19562e751c3422842c0fd340b31fd9f29be46fe5bdb9a3c8f9f57e1c5888",
        "heartbeatInterval_funcSound": "d0c5fa85b1f9e1f70b974afff28ca20d33ef1c0881d1bb1f8d61066e3a672b4c",
        "heartbeat_funcSound": "fa4a0224f579692be9ec7d71ada82e7b884855af256be41ad40539a357fc0afe",
        "isPauserLive_funcSound": "c58a0c4608933b25643cb06098f05ec42f4903a65492c3281eb15e6006647f89",
        "maxHeartbeatInterval_funcSound": "ecb628dc0809764c0276dde344b8e42f5ba4249f2dc72235e4169f71a35d92c2",
        "maxPauseDuration_funcSound": "c20a42014feef31c389f13009338a24dc95c5c05815076e397bac6b452fe9457",
        "minHeartbeatInterval_funcSound": "57cbd5ffad9612e4e064ff5d18b549b4ecbfa1b3abb894e9d1d86f29a14649ad",
        "minPauseDuration_funcSound": "24e8b9ab9cd17ae1961a546300e0af10e19f8033dbc07c2b3620e008b6ec6174",
        "one_payload_lt": "d7c2da835a709dfa8f6891c88af9a81d4741f44e10a24a6bfd80e396ace0b868",
        "pauseDuration_funcSound": "13804a724353d418fc64b6896d81b1e662a7f706636eca8b1e33128d58e2bc1a",
        "setHeartbeatInterval_funcSound": "a825e736961582eb19008f1a0301ccfdb176121cbc05fc9a169152c4a99e6870",
        "setPauseDuration_funcSound": "b822c4544022615800989a9c4ae196d01bbc0d5badb7077618ac73184cc60b0b",
        "silentIn_enumLoop": "ae1d775e66e7da89308384e60b797774a1d517c6ad03508be2d34e5c7bad2d70",
        "silentIn_getPausables": "d0473a5fb1f188954db8bdabbe6ccae534be8e393b017c534585c851e41931dd",
        "storFixed_enumLoop": "4d9310b1a72cb13ad313908af32ccf9edb190c6bac0418933db3f98365a7c384",
        "storFixed_getPausableCount": "2241ed2e5f40265e37a4082069c0f4ec90274b56adae3936dd7df70e30b2d23d",
        "storFixed_getPausables": "658b16f9dbfe4f758cbc8ddb79789dd04d7dd22bbd222f2c5943e0c28e1b83f1",
        "storFixed_getPauser": "40b0b66b5fd4b356eea110ed0e72b289b558991719016c6d3935c93415712c37",
        "storFixed_heartbeatAboveMaxError": "e4d604d1a05c5f62f0507e679d62be5993f807538ef0f275e281014074c9d5bf",
        "storFixed_heartbeatBelowMinError": "9c3e618d94736aeb93a4aa212b0fd2919a894f1dbd106ea580af4cf9c1edae59",
        "storFixed_heartbeatExpiredError": "40d3613849896a7767780733acf7faab9f2b793965975417e48f99cc69c4049b",
        "storFixed_heartbeatExpiry": "d027ffde27bf5b80021d9d5c8cc97fc914e2cef7ba41c3c1d1be2cb0dc659a7c",
        "storFixed_heartbeatInterval": "c3063d8c4aa3580e1b336aef47ef185f7c325835bc655ba2775d44f0e1091ea6",
        "storFixed_isPauserLive": "3d1b7c8e712ecaa01d62b7356dd10c4cddacb1975b3d959a61157ada9bfaf318",
        "storFixed_of_silentIn": "0e2d47df687caa133ce8f9fb782b9809eb990598e1e77135c163cebe736f80b5",
        "storFixed_pauseAboveMaxError": "82c38ff461bc2839ab391cd6ba9e906e761109aa19c54c6895e281b61cda6fb7",
        "storFixed_pauseBelowMinError": "66155dbe3f912664a81432e47250764026716100399ad7fd850a9f300cb79137",
        "storFixed_pauseDuration": "d22ee91643fb655f56a4b67fbcbc36eee9f4ca37cdd84e5099835e076e4cba31",
        "storFixed_returnDeployWord": "f77ebf7fcb3651bc6e8e2abd3722b711a0d4b00503d22400c3d520359bfb2dee",
        "storFixed_revData": "0f8902bb6588a058566a133ae37de1dcb7da626c8928b8f11b8ae4c0d8e4bed3",
        "storFixed_senderNotAdminError": "69afe2c41a3fe08019ee6ea78766452766a607b81efae791e4efa3839b902c82",
        "storFixed_senderNotPauserError": "39da74c872f0d44f59db0d31bf9b99240a6b4a4b6d8d1ea8ec3b2bcec79a20b3",
        "storFixed_staticAddressView": "6af19765a36d50b9d5c40637f69bec1dd8e073dfefa2e2eb1b11f56e217ff04a",
        "zero_payload_lt": "922afcf6132058b18913124957a5976912db5b72dc8666229a5a5e13d69aace5"
    },
    "history": {
        "DispatchInv.line": "cff8acdb47e0462f062e95da9430bee555547ba980a87d6a6c0ac3b62d7f0266",
        "StorFixed.branch": "02c20eca6deb206ec555a60141acd73398733b5e4bc8e1ab2bbed0359b1d5c9d",
        "StorFixed.call": "93493a61a89b2062964f285fb45f6cc80f1a8e2c25aa5df70b1398f74afdff56",
        "StorFixed.last": "d7984be51107bca69a3219b910498b877ee908ea7472618058a3ff9b72a08b53",
        "StorFixed.next": "e8866fc822aaf009fc1f235e792710a9de94d6cd1a4e083ea3fbfdc2b4851640",
        "StorFixed.of_inv": "cf86e190fb6367b00f6a0e04352a67551ab252b3356d1673c860685e6104f176",
        "StorFixed.prepend": "f036b548bba1646640804e62587dd9451bbe19a85537e14873d936bc8e70ecd8",
        "StorFixed.rev": "2483e0bde2db00b248786b1cf51c6612f4e252dde99b6f08b301699e3438f991",
        "funcSound_of_registryCore": "b393a69d1eb1d55fdf7987dbcfa1444bba6d5760c69356f8cab024d1dfc0df6d",
        "funcSound_of_storFixed": "b536fd659a256776f912be4fab4e65340ebaf01cd302910c499ef47a710c1ea7",
        "funcSound_pop": "df9bc1880d5b9c391e5bede3727edc90211231e06c1b801b042e26f7085ca519",
        "funcSound_rev": "a061141802da64e50bc083da394c2d0316e2c08c6a6e84d2cd128d88920439ca",
        "popStateInv": "7fa1b42a5901386a4e2690eb4226275f45ae3aa3c2e4c1324a9e488a5962ce15",
        "post_of_run_call": "61234fac0a7dc0b9976d1e06314da47668fe6310941cc3e366ce337901ae430c",
        "post_of_run_hybridDispatch": "ee2a84a8f584d6b689d62b437abfdf80ecb8a6102a4b7d90d7b954502781fafc",
        "post_of_run_linearDispatch": "3a60aaf864531ff7355714f1af86ed58b904c07267b59eebbd90428b969a6953",
        "post_of_run_splitDispatch": "7b3069a2d21f2b66af38249abfedf62de549757092eeaaeeb117b507fb834ab4",
        "registrySpec_sound_of_funcSound": "5feaa2018c3f1dfbc2ab395f186d667197cabaeeca5f14980dcface72fbc4536",
        "registryStable_iff_stateInv": "2cbd9049028adb88b8f4735b8dc38817ba54cefc7dbaaf50e9848ddb07d711a8"
    }
}
# <<< HEADER PINS <<<

# >>> DEFINITION PINS >>>
DEFINITION_PINS = {
    "chain": {
        "emptyRegistryWorld": "998a5a115f4bb8a70f569e7cf09c7c012014b32296c464904b91485534b6170f",
        "registryView": "0a512b4685656d8302e6a33b6f9c9e09ddd782a9e746ed50e1ecdb83041f2177"
    },
    "endpoints": {
        "Coherent": "71e0b8a9297e1779023ccf8d81524e81b2b484acc2c674e6f746e5b3fcdc019a",
        "SilentIn": "439123a9eb01411614919e885f7f655bef1bf6656461efa4cfa728b96a44d531"
    },
    "history": {
        "DispatchInv": "574528abf00a3e3d21cf448fbc6410b106d0987add183df57a88b977ff6b1e2d",
        "RegistryCoherent": "e89b4dcf96254b323d874f57fc07f0c22e642c46297152a325de097ed875fa00",
        "RegistryStable": "099ddbc2833ee8e3ea9bee46492656e357496f545563ee5c63cf3508f4613eba",
        "StorFixed": "1803c987cdacc7b80b0c59518a9878f11bf1803b40f0c27c70c858493da7b123",
        "registrySpec": "9a12c6a59f12d993fdec779bc056711f251424cf854d51639bd0e4e3503b8d19"
    }
}
# <<< DEFINITION PINS <<<

# >>> IMPORT PINS >>>
IMPORT_PINS = {'chain': ('import Blanc.LidoCircuitBreakerHistoryEndpoints',), 'endpoints': ('import Blanc.LidoCircuitBreakerHistory',), 'history': ('import Blanc.LidoCircuitBreakerSuccess',)}
# <<< IMPORT PINS <<<

# >>> VARIABLE PINS >>>
VARIABLE_PINS = {'chain': (), 'endpoints': ('variable {dp : DeployParams}',), 'history': ('variable {c : ContractSpec} {ca : Adr} {k : Nat} {aux : List Func}', 'variable {dp : DeployParams}')}
# <<< VARIABLE PINS <<<

# >>> DISPATCHER PIN >>>
DISPATCHER_PIN = 'c22f8f28a41768dcf6999557f7f0ec5cfc9bfae450842f13225f1d98c809828d'
# <<< DISPATCHER PIN <<<

# >>> COMMENT TRUST ROWS >>>
COMMENT_TRUST_ROWS = ('T6-decide Blanc/LidoCircuitBreakerHistoryEndpoints.lean not be driven by `decide`: deciding anything about these leaves forces the', 'T7-maxRecDepth Blanc/LidoCircuitBreakerHistoryEndpoints.lean `String.keccak` behind every `selector` and blows `maxRecDepth`. -/')
# <<< COMMENT TRUST ROWS <<<


# The second net under `DEFINITION_PINS`.  Each pinned definition must still
# mention every token listed for it.  A re-pin taken carelessly after a body
# was gutted passes the digest check by construction and fails here: a
# `RegistryCoherent` that no longer says `RegistryWitness` is not this
# family's invariant whatever its digest is.
SEMANTIC_CHANNELS = {
    "RegistryCoherent": ("∃", "RegistryWitness", "logicalStorageOfStor"),
    "RegistryStable": ("Prog.compile", "runtime dp", "RegistryCoherent",
                       "w.getStor ca", "w.getCode ca"),
    "registrySpec": ("prog := runtime dp", "RegistryCoherent s",
                     "inv_transfer", "inv_recv_transfer", "inv_addBal"),
    "StorFixed": ("Func.Run", "(runtime dp).main :: aux",
                  "Devm.getStor r = Devm.getStor s"),
    "Coherent": ("Func.Core", "(runtime dp).main :: aux", "RegistryCoherent"),
    "SilentIn": ("Linst.Inv Devm.getStor Devm.getStor",
                 "Ninst.Inv Devm.getStor"),
    # `PreWf` and `Mem.Wf` are listed because the deeper-frame hypothesis is
    # phrased at the STRONGER antecedent, which is what makes the dispatcher
    # lemmas the stronger claim; a re-pin that quietly put `c.Pre ca` back
    # into the `Exec.InvDepth` argument would restore the weaker theorem.
    "DispatchInv": ("c.Pre ca e s", "Mem.Wf s.memory", "Exec.InvDepth",
                    "c.PreWf ca", "c.Post ca"),
}


# --------------------------------------------------------------------------
# Vocabulary pins: declarations this family NAMES but does not own
# --------------------------------------------------------------------------
#
# Every pin above is scoped to an owner, and an owner is a file this gate
# checks in full.  That leaves a hole exactly where the family's meaning
# actually lives: the premise vocabulary its pinned statements are written IN.
#
#   * `RegistryWitness` (`Blanc/LidoCircuitBreakerRegistryModel.lean`) is the
#     structure the whole invariant bottoms out in.  `RegistryCoherent` is
#     `∃ entries, RegistryWitness ... entries`, and SEMANTIC_CHANNELS makes
#     sure it keeps saying so -- but nothing pinned what `RegistryWitness`
#     MEANS.  Gut one field (`arrayWords : ∀ index, index < entries.length →
#     True`) and every S7 pin, every channel token and every allowlist pattern
#     stays byte-identical while the invariant goes near-vacuous.  The registry
#     gate does not cover it either: its coverage is the dotted
#     `RegistryWitness.*` theorems, not the structure.
#
#   * `ContractSpec` and its fields (`Pre`, `PreWf`, `Post`, `Sound`,
#     `FuncSound`, `Preserves`, `StateInv`, `MsgInv`), `Exec.InvDepth`, and
#     `BlockChain.Reach`/`ReachUsing` (`Blanc/Ladder.lean`) are named by pinned
#     S7 statements and pinned by nothing.  The worked exploit: add
#     `block.txs = []` to `BlockChain.ReachUsing.step` and
#     `chain_preserves_registryStable` still READS "every state reachable by
#     the configured valid-chain relation", with an unchanged digest, while
#     covering only empty blocks.
#
# This is not a second owner relation: these files are read, and only the
# named declarations are pinned, exactly as `PROGRAM_SOURCE` is read rather
# than owned.  Nothing here requires the rest of either file to hold still.
#
# The threading of `Mem.Wf` through this vocabulary is precisely the change
# that moved `DispatchInv` and three Chain statements from `Pre` to `PreWf`
# while leaving every public S7 digest untouched -- which is this hole being
# exercised in the ordinary course of work, not a hypothetical.

# The authoritative list of what is pinned, per file.  `VOCABULARY_PINS` below
# holds a digest for exactly these names -- no more, no less -- so that
# dropping a name from this tuple is a visible edit rather than a silently
# missing pin, and so that the digest emitter cannot bootstrap itself from an
# empty table.
VOCABULARY_NAMES = {
    "Blanc/LidoCircuitBreakerRegistryModel.lean": (
        "Blanc.LidoCircuitBreaker.RegistryWitness",
    ),
    "Blanc/Ladder.lean": (
        "Blanc.ContractSpec",
        "Blanc.ContractSpec.Pre",
        "Blanc.ContractSpec.PreWf",
        "Blanc.ContractSpec.Post",
        "Blanc.ContractSpec.Sound",
        "Blanc.ContractSpec.FuncSound",
        "Blanc.ContractSpec.Preserves",
        "Blanc.ContractSpec.StateInv",
        "Blanc.ContractSpec.MsgInv",
        "Blanc.Exec.InvDepth",
        "Blanc.BlockChain.Reach",
        "Blanc.BlockChain.ReachUsing",
    ),
}

VOCABULARY_SOURCES = tuple(VOCABULARY_NAMES)

# >>> VOCABULARY PINS >>>
VOCABULARY_PINS = {
    "Blanc/Ladder.lean": {
        "Blanc.BlockChain.Reach": "f65d2cfb2dd0fa916d35deac841a6eeebd45676aec48c7b5e76c2898807f6244",
        "Blanc.BlockChain.ReachUsing": "cf3e4d62373f92180b65f6a0458426517e58e8ba501c0cf31ec744dd33ce386c",
        "Blanc.ContractSpec": "74cb032721b7e1cdff473d3da8860eda24ad0e2521b806386e659c5201ca116c",
        "Blanc.ContractSpec.FuncSound": "2d6e17d10b936922813c6ed7c44521c2c2771728a130abdb9ab1f8b9f4c09346",
        "Blanc.ContractSpec.MsgInv": "3ef6dcf39e3da7573446e9726f2d8524c4cc58aaef8e682c0f404134a6a527b2",
        "Blanc.ContractSpec.Post": "9f679f2df84d0d895c840ecac3adace6100217e20e096ddb7afb63a6ab369128",
        "Blanc.ContractSpec.Pre": "4bb25d71b8813e4ddb95628f959896908e5e7b6a19bfcbd4fa8f7b27e6859281",
        "Blanc.ContractSpec.PreWf": "3d7d6e012e6ab6371fc1a760edfd3bde1b0b9784ddd6c137172b9c6d062d9955",
        "Blanc.ContractSpec.Preserves": "ab90b4aa2e5f5959592f8fb423c98d56bc572cc2740ab0aabc839c8f071dc4e3",
        "Blanc.ContractSpec.Sound": "e16750a15964eaa6797c0f04c9d06a3a66e07346b1f09c1892b66dfcc7060a38",
        "Blanc.ContractSpec.StateInv": "e934052b2170660338713cb8b3adb45902fd7b1783ad709e4d0ac4947b7dd322",
        "Blanc.Exec.InvDepth": "59fc3b3886be2ff06afcbb5d211e3e6928d37c592221353c4c686f4fdb67e82a"
    },
    "Blanc/LidoCircuitBreakerRegistryModel.lean": {
        "Blanc.LidoCircuitBreaker.RegistryWitness": "56689ed4cf8d2222dfdb372dc7886763d21cb6c5f7b3f62211533861fec8ea0a"
    }
}
# <<< VOCABULARY PINS <<<

# The second net under `VOCABULARY_PINS`, in the same spirit as
# `SEMANTIC_CHANNELS`: a digest re-taken in a hurry over a gutted declaration
# passes by construction and fails here.  For `RegistryWitness` the tokens are
# its field NAMES plus the terms that make each field say something -- a field
# whose body has been replaced by `True` keeps its name but loses its term.
VOCABULARY_CHANNELS = {
    "Blanc.LidoCircuitBreaker.RegistryWitness": (
        "targetsNodup", "targetsValid", "pausersValid", "lengthWord",
        "arrayWords", "assignments", "indices", "counts", "zeroCount",
        # One content token PER FIELD, not one shared token: a field name
        # survives its own body being replaced by `True`, and a token that
        # appears in a sibling field (`nonzeroCanonicalAddress` is in both
        # `targetsValid` and `pausersValid`) would let either be gutted while
        # the other kept the channel satisfied.
        "(entries.map Prod.fst).Nodup",
        "nonzeroCanonicalAddress entry.1",
        "nonzeroCanonicalAddress entry.2",
        "storage.read arrayLengthSlot = Nat.toB256 entries.length",
        "targetAt entries index", "assignmentAt entries target",
        "Nat.toB256 (oneBasedIndexAt entries target)",
        "Nat.toB256 (assignmentCount entries pauser)",
        "storage.read (countSlot 0) = 0"),
    "Blanc.ContractSpec.Pre": ("Prog.compile c.prog", "c.Side devm.getBal",
                               "c.PreInv devm ca sevm"),
    "Blanc.ContractSpec.PreWf": ("c.Pre ca sevm devm",
                                 "Mem.Wf devm.memory"),
    "Blanc.ContractSpec.Post": ("c.Side devm.getBal", "c.PostInv devm ca"),
    "Blanc.ContractSpec.Sound": ("Prog.Run sevm pre c.prog post",
                                 "sevm.currentTarget = ca",
                                 "c.PreWf ca sevm' pre'", "Mem.Wf pre.memory",
                                 "c.Pre ca sevm pre", "c.Post ca sevm post"),
    "Blanc.ContractSpec.Preserves": ("Exec 0 sevm pre (.ok post)",
                                     "Prog.compile c.prog",
                                     "Mem.Wf pre.memory",
                                     "c.Pre ca sevm pre",
                                     "c.Post ca sevm post"),
    "Blanc.ContractSpec.FuncSound": ("c.Pre ca sevm s", "Mem.Wf s.memory",
                                     "Exec.InvDepth sevm.depth ca c.prog",
                                     "c.PreWf ca", "c.Post ca",
                                     "Func.Run (c.prog.main :: aux) sevm s f r"),
    "Blanc.Exec.InvDepth": ("ForallDeeperAt k ca p",
                            "σ sevm pre → ifOk (ρ sevm) exn"),
    # The reachability relations carry the family's headline quantifier.  The
    # tokens are the step rules' own content: drop or restrict a step and the
    # relation still reads as "reachable" while covering less.
    "Blanc.BlockChain.Reach": (
        "refl (ch : BlockChain) : Reach ch ch",
        "sum ch'.state.bal + wdsum block.wds < 2 ^ 256",
        "stateTransition ch' block = .ok ch''", "Reach ch ch''"),
    "Blanc.BlockChain.ReachUsing": (
        "cfg.Valid", "ch.ValidContext", "cfg.chainId = ch.chainId",
        "sum ch'.state.bal + wdsum block.wds < 2 ^ 256",
        "stateTransitionUsing cfg ch' block = .ok ch''",
        "ReachUsing cfg ch ch''"),
    "Blanc.ContractSpec.StateInv": ("Prog.compile c.prog", "c.Side w.bal",
                                    "c.Inv (w.getStor ca) 0 (w.bal ca)"),
}


def vocabulary_key(declaration: dict) -> str:
    namespace = declaration["namespace"]
    return (namespace + "." + declaration["name"]).lstrip(".")


def vocabulary_map(source: str) -> dict:
    found = {}
    for declaration in declarations(source):
        found[vocabulary_key(declaration)] = declaration
    return found


def vocabulary_pins(root: Path) -> None:
    """Pin the named declarations of the files this family is written IN.

    Unlike an owner, only the NAMED declarations are checked; the rest of each
    file is free to move.  Every pinned name must still exist, and every
    channel token must still appear.
    """
    for relative, names in sorted(VOCABULARY_NAMES.items()):
        expected = VOCABULARY_PINS.get(relative) or {}
        if sorted(expected) != sorted(names):
            fail(f"vocabulary pin table for {relative} does not match its "
                 f"name list: pinned {sorted(expected)}, expected "
                 f"{sorted(names)}. The premise vocabulary this family's "
                 "statements are written in must be pinned, or a statement "
                 "can keep its digest while its words change meaning "
                 "underneath it")
        found = vocabulary_map(read_source(root, relative))
        for name, pin in sorted(expected.items()):
            if name not in found:
                fail(f"vocabulary declaration {name} is absent from "
                     f"{relative} -- renamed, moved or deleted; every pinned "
                     "S7 statement that names it now means something this "
                     "gate cannot see")
            actual = digest(found[name]["text"])
            if actual != pin:
                fail(f"vocabulary declaration {name} changed in {relative}. "
                     "A pinned S7 statement can keep its digest while this "
                     "changes underneath it, so this is a claim change until "
                     "review says otherwise")
        for name, tokens in VOCABULARY_CHANNELS.items():
            if name not in found:
                continue
            text = normalize(found[name]["text"])
            for token in tokens:
                if normalize(token) not in text:
                    fail(f"vocabulary declaration {name} no longer mentions "
                         f"{token!r}; its pin may have been re-taken over a "
                         "gutted body")


# --------------------------------------------------------------------------
# The open-world bar
# --------------------------------------------------------------------------
#
# This is the check the family exists to survive, and it is a POSITIVE
# allowlist.  Every binder of every pinned statement is classified: either its
# type is a declared data type, or its type matches one of the admissible
# hypothesis shapes below.  Anything else fails, with no judgement about
# whether it "looks" cooperative -- which is the point.  A weakening hidden
# behind an innocuous wrapper (`(h : LocalWorld dp ca)`) matches nothing and is
# rejected exactly as loudly as `PauseSuccessNoninterference` would be.
#
# Several shapes are admissible only on PRIVATE declarations.  A public
# statement of this family may not, for instance, carry `0 < sevm.depth` or a
# `Func.Run` premise about a particular walk: those are inversion residue that
# belongs inside the module, and hoisting one into a public statement is a
# narrowing even though every token in it already appears in the file.

DATA_TYPES = frozenset({
    "Adr", "B256", "B256 × Func", "Benv", "Block", "BlockChain",
    "BlockOutput", "Bool", "ByteArray", "Bytes", "ChainConfig",
    "ContractSpec", "DeployParams", "Devm", "ForkRules", "Func",
    "Jaune.State", "Line", "Linst", "List (B256 × Func)", "List (Nat × Tx)",
    "List Entry", "List Func", "Mem", "Msg", "MsgCallOutput", "Nat",
    "Nat → Prop",
    "Ninst", "Prog", "Sevm", "Stack", "Stor", "Tx", "Xlot",
})

_ID = r"[A-Za-z_][A-Za-z0-9_'!?]*"

# (label, pattern, public_ok).  Patterns are full-matched against the
# whitespace-normalized binder type.
ADMISSIBLE_HYPOTHESES = (
    # ---- the two assembly disciplines, and their syntactic guard ----
    ("storage-silence of a body", rf"StorFixed dp {_ID}", True),
    ("coherence transport of a body", rf"Coherent dp {_ID}", True),
    ("syntactic storage-silence", rf"SilentIn P {_ID}", False),
    ("closure of the permitted jump indices",
     r"∀ k g, P k → \(\(runtime dp\)\.main :: aux\)\[k\]\? = some g → "
     r"SilentIn P g", False),
    # ---- storage-invariance of a fragment ----
    ("fragment storage-invariance",
     rf"(Func|Linst)\.Inv Devm\.getStor Devm\.getStor {_ID}", True),
    ("line storage-invariance", rf"Line\.Inv Devm\.(getStor|state) {_ID}", True),
    # Added as its own row rather than by widening the alternation above: the
    # dispatcher's selector-comparison lines must leave the MACHINE's memory
    # alone as well as the world's storage, because `DispatchInv` now carries
    # `Mem.Wf`.  Same character as the two projections above -- a line that
    # changes nothing -- and it restricts no callee.
    ("line memory-invariance", rf"Line\.Inv Devm\.memory {_ID}", True),
    ("instruction storage-invariance",
     rf"Ninst\.Hinv Devm\.getStor {_ID}", True),
    # ---- the obligation shapes ----
    ("program-free coherence core",
     r"Func\.Core \(\(runtime dp\)\.main :: aux\) RegistryCoherent f", True),
    ("dispatch-target obligation, generic spec",
     rf"c\.FuncSound ca aux {_ID}", False),
    ("Registry-mutating dispatch-target obligation",
     rf"\(registrySpec dp\)\.FuncSound ca aux \(?{_ID}( dp)?\)?", True),
    ("whole dispatch list, generic spec",
     r"∀ p ∈ entries, c\.FuncSound ca aux p\.2", False),
    ("whole dispatch list",
     r"∀ p ∈ funcs dp, \(registrySpec dp\)\.FuncSound ca aux p\.2", True),
    ("dispatch-list membership", r"p ∈ funcs dp", True),
    ("Registry-mutating exclusion", rf"p\.2 ≠ {_ID}( dp)?", True),
    # ---- the aux table ----
    ("aux-slot occupancy",
     rf"\(\(runtime dp\)\.main :: aux\)\[{_ID}\]\? = some {_ID}", True),
    ("aux-slot occupancy, generic spec",
     rf"\(c\.prog\.main :: aux\)\[{_ID}\]\? = some {_ID}", False),
    # ---- the dispatcher reduction's internals ----
    ("dispatcher scratch invariant", r"DispatchInv c ca e s", False),
    ("dispatcher walk",
     r"Func\.Run \(c\.prog\.main :: aux\) e s \(?[^)]*\)? r", False),
    ("arbitrary-table walk", r"Func\.Run fs sevm s f r", False),
    ("line walk", r"Line\.Run e s L s'", False),
    ("scratch pop", r"Devm\.PopBurn \[w\] s' s''", False),
    ("split-dispatch branch obligation",
     r"∀ \{e : Sevm\} \{s r : Devm\}, DispatchInv c ca e s → "
     r"Func\.Run \(c\.prog\.main :: aux\) e s (left|right) r → "
     r"c\.Post ca e r", False),
    # ---- the invariant itself ----
    ("Registry coherence of a storage image", r"RegistryCoherent s", True),
    ("Registry coherence at the contract's own target",
     r"RegistryCoherent \(Devm\.getStor s sevm\.currentTarget\)", True),
    ("Registry witness",
     r"RegistryWitness \(logicalStorageOfStor s\) entries", True),
    ("stable checkpoint", rf"RegistryStable dp ca {_ID}\.state", True),
    ("canonical-address payload bound", rf"{_ID}\.toNat < 2 \^ 252", True),
    ("canonical address", rf"canonicalAddress {_ID}", True),
    ("region-disjoint key law, fixed key",
     r"∀ \(t : Stor\) \(v : B256\), RegistryCoherent t → "
     r"RegistryCoherent \(t\.set key v\)", True),
    ("region-disjoint key law, caller-tagged key",
     r"∀ \(a : Adr\) \(t : Stor\) \(v : B256\), RegistryCoherent t → "
     r"RegistryCoherent \(t\.set \(slot region a\.toB256\) v\)", True),
    # ---- identification of THIS contract, at ITS OWN address ----
    #
    # The address argument is part of the pattern on purpose.  `some
    # (s.getCode w).toList = Prog.compile (runtime dp)` at any other address is
    # a pinned-callee premise wearing this shape's clothes, and fails here.
    ("installed exact runtime at the contract's own address",
     r"some \(s\.getCode sevm\.currentTarget\)\.toList = "
     r"Prog\.compile \(runtime dp\)", True),
    ("a compiled program, contract-neutral",
     r"some code\.toList = Prog\.compile p", False),
    # ---- the deeper-frame induction hypothesis ----
    #
    # Also address-pinned: this is the hypothesis that says re-entry into THIS
    # contract is handled, and it must be about this contract.
    #
    # The antecedent is `PreWf`, and this row was REPLACED rather than widened
    # to `(Pre|PreWf)` when the ladder started threading `Mem.Wf`.  The
    # direction is what makes that mandatory.  `Exec.InvDepth k ca p σ ρ` puts
    # `σ` in the ANTECEDENT of its implication (`σ sevm pre → ifOk (ρ sevm)`),
    # so `σ` sits in negative position and a STRONGER `σ` yields a WEAKER
    # hypothesis.  `PreWf` is `Pre` plus `sevm.currentTarget = ca → Mem.Wf
    # devm.memory`, hence strictly stronger, hence `InvDepth ... PreWf ...` is
    # the weaker premise and the theorem carrying it is the stronger claim.
    # A row reading `(Pre|PreWf)` would keep admitting the older, stronger
    # premise -- the weaker theorem -- under a label that says the opposite,
    # which is precisely the "widening an allowlist pattern by one character"
    # this file's own comment names as the hazard.
    ("deeper-frame induction hypothesis at the contract's own target",
     r"Exec\.InvDepth sevm\.depth sevm\.currentTarget \(runtime dp\) "
     r"\(\(registrySpec dp\)\.PreWf sevm\.currentTarget\) "
     r"\(\(registrySpec dp\)\.Post sevm\.currentTarget\)", True),
    # ---- the external edges ----
    ("operand-stack prefix",
     rf"\({_ID}(?: :: {_ID})* :: xs\) <<\+ s\.stack", True),
    ("external-edge step", r"Ninst\.Run sevm s (call|statcall) sf", True),
    ("nonzero frame depth", r"0 < sevm\.depth", False),
    ("parent world identity", r"parent\.state = s\.state", False),
    ("return slot filled", r"Xlot\.Filled xl", False),
    ("the machine's own code-selection disjunct",
     r"\(getDelegatedCodeAddress \(s\.getCode target\) = none ∧ "
     r"code = s\.getCode target ∧ del = false\) ∨ "
     r"\(∃ d, getDelegatedCodeAddress \(s\.getCode target\) = some d ∧ "
     r"code = s\.getCode d ∧ del = true\)", False),
    ("the child frame's own message",
     r"ProcessMessage \(callMsg sevm parent gas value sevm\.currentTarget "
     r"target target true isStatic cd code del\) xl \(\.ok child\)", False),
    # ---- the generic ladder's own premises ----
    ("message run", r"processMessageCall msg = \.ok ⟨st', out⟩", True),
    ("transaction run",
     r"processTransaction benv bout tx i = \.ok ⟨st, bout'⟩", True),
    ("transaction-list run",
     r"applyTransactions txis benv bout = \.ok ⟨benv', bout'⟩", True),
    ("block run",
     r"stateTransition(With rules|Using cfg)? ch block = \.ok ch'", True),
    ("message-level invariant", r"\(registrySpec dp\)\.MsgInv ca msg", True),
    ("balance-sum bound", r"sum benv\.state\.bal < 2 \^ 256", True),
    ("balance-sum bound with withdrawals",
     r"sum ch\.state\.bal \+ wdsum block\.wds < 2 \^ 256", True),
    ("account not created in this block", r"ca ∉ benv\.createdAccounts", True),
    ("chain reachability",
     r"BlockChain\.Reach(Using cfg)? checkpoint future", True),

    # ---- `ContractSpec.Preserves`, spelled out ----
    #
    # `arbitraryExec_post_registryFields` is an anti-vacuity control: it takes
    # an ARBITRARY successful execution from the contract's frame and projects
    # real `RegistryWitness` fields out of the post-state.  Its four premises
    # are verbatim the binders of `ContractSpec.Preserves` (`Blanc/Ladder.lean`
    # `Blanc.ContractSpec.Preserves`, whose text this gate now pins), in order:
    # the execution, the code guard, the memory guard and the precondition.
    #
    # None of the four is a cooperative-world premise.  The two implications
    # are guarded by `sevm.currentTarget = ca`, so they say nothing whatever
    # about any other account -- they are the ladder's own way of saying "when
    # this frame IS the contract, its code is the compiled runtime and its
    # memory is well-formed", both of which the rungs above discharge at
    # `initDevm`.  They are listed as four separate rows rather than one
    # catch-all so that a fifth premise appearing alongside them still fails.
    ("Preserves shape: an arbitrary successful execution from frame entry",
     r"Exec 0 sevm pre \(\.ok post\)", True),
    ("Preserves shape: the code guard, on the contract's own frame only",
     r"sevm\.currentTarget = ca → "
     r"some sevm\.code\.toList = Prog\.compile \(runtime dp\)", True),
    ("Preserves shape: the memory guard, on the contract's own frame only",
     r"sevm\.currentTarget = ca → Mem\.Wf pre\.memory", True),
    ("Preserves shape: the frame-entry precondition",
     r"\(registrySpec dp\)\.Pre ca sevm pre", True),

    # ---- the machine's memory invariant ----
    #
    # `Mem.Wf μ` is `μ.data.size ≤ μ.size` (`Blanc/CommonCore.lean`): a
    # statement about the machine's own memory REPRESENTATION, not about the
    # world.  It restricts no callee, no depth and no caller.  It has to be
    # carried rather than derived because `Mem.write`'s in-place branch
    # preserves its negation just as faithfully; the rungs above discharge it
    # at `initDevm` via `Mem.wf_empty`, which is why no headline statement of
    # this family carries it.
    ("machine memory well-formedness", rf"Mem\.Wf {_ID}\.memory", True),
    ("memory unchanged across a step", rf"{_ID}\.memory = {_ID}\.memory", False),
    ("memory image", rf"Mem\.Reads {_ID}\.memory img", False),
    ("memory word read", rf"Bytes\.toB256 \({_ID}\.sliceD \({_ID} \* 32\)"
     rf"\.toNat 32 0\) = (?:{_ID}|[0-9]+)", False),
    ("memory word disjointness",
     rf"\({_ID} \* 32\)\.toNat \+ 32 ≤ \({_ID} \* 32\)\.toNat", False),

    # ---- the stable checkpoint, at a world variable ----
    #
    # The `RegistryStable.*` reader-facing corollaries project the checkpoint
    # predicate at a bare `w : Jaune.State` rather than at `checkpoint.state`.
    # This is the family's own invariant appearing as a hypothesis, which is
    # the thing the corollaries exist to unpack; it constrains nothing beyond
    # the contract's own storage and code.
    ("stable checkpoint at a world", r"RegistryStable dp ca w", True),

    # ---- coherence-preservation of a NAMED body, spelled out ----
    #
    # `coherent_pause` and `coherent_pauseAfterSet` are the `Coherent dp f`
    # discipline written longhand, because these two bodies additionally need
    # the deeper-frame hypothesis and the memory invariant, which `Coherent`
    # does not carry.  `Coherent dp f` and `StorFixed dp f` are already
    # public-admissible and are THEMSELVES universally quantified over
    # `Func.Run ((runtime dp).main :: aux) sevm s f r`, so this row admits no
    # shape those two do not already admit.
    #
    # The pattern is deliberately tight: the walk must be over the EXACT
    # runtime table, the state binders must be the theorem's own universally
    # quantified `sevm`/`s`/`r`, and the body must be a bare name.  A premise
    # about some particular walk supplied from outside cannot wear this shape.
    ("coherence walk of a named body in the exact runtime context",
     rf"Func\.Run \(\(runtime dp\)\.main :: aux\) sevm s {_ID} r", True),
    ("coherence walk of a named body, mid-inversion",
     r"Func\.Run \(\(runtime dp\)\.main :: aux\) sevm [a-z]+ "
     rf"\(?{_ID}( dp)?\)? [a-z]+", False),
    ("line walk of a named fragment", rf"Line\.Run sevm {_ID} \({_ID} {_ID}\) "
     rf"{_ID}", False),
    ("instruction walk", rf"Ninst\.Run sevm {_ID} i {_ID}", False),

    # ---- inversion residue inside the Chain owner ----
    ("storage image unchanged", r"Devm\.getStor s = Devm\.getStor s'", False),
    ("code image unchanged", r"Devm\.getCode s = Devm\.getCode s'", False),
    ("Registry coherence at a named frame's target",
     rf"RegistryCoherent \(Devm\.getStor {_ID} "
     rf"(sevm\.currentTarget|ct)\)", False),
    ("Registry witness at a world's contract storage",
     rf"RegistryWitness \(logicalStorageOfStor \({_ID}\.getStor ca\)\) "
     r"entries", False),
    ("installed exact runtime, mid-inversion",
     rf"some \({_ID}\.getCode (ca|sevm\.currentTarget)\)\.toList = "
     r"Prog\.compile \(runtime dp\)", False),
    ("address-range validity", rf"ValidAdr {_ID}", False),
    ("operand-stack prefix, mid-inversion",
     rf"({_ID} :: )*xs <<\+ {_ID}\.stack", False),
)

# The redundant second net.  These tokens name closed-world restrictions this
# family must never acquire, and none of them appears in any pinned statement
# today.  `ADMISSIBLE_HYPOTHESES` is the mechanism; this list exists so that a
# reviewer re-pinning a digest in a hurry, or widening an allowlist pattern by
# one character, still trips a check whose failure message names the hazard.
COOPERATIVE_WORLD_TOKENS = (
    "PauseSuccessNoninterference", "PauseSuccessInputs",
    "Noninterference", "noninterference",
    "Cooperative", "cooperative",
    "Reentrant", "reentrant", "Reentry", "reentry", "Reenter", "reenter",
    "Honest", "honest", "Benign", "benign", "Trusted", "trusted",
    "WellBehaved", "wellBehaved",
    "DirectCall", "directCall", "TopLevel", "topLevel", "Toplevel",
    "SameEntries", "sameEntries", "entriesEq", "EntriesEq",
    "NoCallback", "noCallback", "NoExternal", "noExternal",
    "Whitelist", "whitelist", "Allowlist", "allowlist",
    "KnownCallee", "knownCallee", "FriendlyTarget", "friendlyTarget",
)

# A public statement may only speak about the code at the contract's own
# address.  `coherent_of_childFrame` reads `s.getCode target` and is private
# and pinned verbatim; a public statement that acquired the same phrase would
# be pinning the callee.
OWN_ADDRESS_TERMS = ("sevm.currentTarget", "ca")


# --------------------------------------------------------------------------
# Checks
# --------------------------------------------------------------------------

def read_source(root: Path, relative: str) -> str:
    path = root / relative
    if not path.is_file():
        fail(f"missing sole production owner {relative}")
    return path.read_text(encoding="utf-8")


def load_owners(root: Path) -> dict:
    return {key: read_source(root, relative)
            for key, relative in active_owners().items()}


def pin_declarations(key: str, source: str) -> dict:
    """Pin every declaration of one owner, and require every pin to land.

    This single function is the header pin, the definition pin, the deletion
    control and the addition control.  There is deliberately no way for a
    declaration to be present and unchecked.
    """
    found = {}
    for declaration in declarations(source):
        name = key_of(declaration)
        if name in found:
            fail(f"{key}: duplicate declaration {name}")
        found[name] = declaration
    headers = HEADER_PINS.get(key, {})
    bodies = DEFINITION_PINS.get(key, {})
    overlap = set(headers) & set(bodies)
    if overlap:
        fail(f"{key}: {sorted(overlap)} pinned as both statement and body")
    for name in sorted(set(headers) | set(bodies)):
        if name not in found:
            fail(f"{key}: pinned declaration {name} is absent -- deleted, "
                 "commented out, renamed or moved out of this owner")
    for name, declaration in sorted(found.items()):
        if name in headers:
            actual = digest(statement_of(declaration))
            if actual != headers[name]:
                fail(f"{key}: normalized statement changed for {name}")
        elif name in bodies:
            actual = digest(declaration["text"])
            if actual != bodies[name]:
                fail(f"{key}: declaration body changed for {name}")
        else:
            fail(f"{key}: declaration {name} ({declaration['kind']}) has no "
                 "pin; every declaration in this family must be pinned as a "
                 "statement or as a body before it can pass")
    return found


def semantic_channels(key: str, found: dict) -> None:
    for name, tokens in SEMANTIC_CHANNELS.items():
        if name not in found:
            continue
        text = normalize(found[name]["text"])
        for token in tokens:
            if normalize(token) not in text:
                fail(f"{key}: {name} no longer mentions {token!r}; its pin may "
                     "have been re-taken over a gutted body")


def pin_imports_and_variables(key: str, source: str) -> None:
    code = strip_comments(source)
    variables = [normalize(line) for line in code.split("\n")
                 if re.match(r"^variable\b", line)]
    # A `variable` line is an implicit binder on every declaration below it, so
    # its binders go through the same bar as a written premise -- and they are
    # checked BEFORE the pin, so that "someone added a hypothesis to the whole
    # section" is reported as that rather than as a changed list.
    for line in variables:
        for binder in split_binders("variable X " + line[len("variable"):],
                                    "X")[0]:
            bracket, names, kind = binder_parts(binder)
            if kind not in DATA_TYPES:
                fail(f"{key}: section variable {' '.join(names) or '_'} of "
                     f"type {kind!r} is not a declared data type; a `variable` "
                     "may not introduce a hypothesis into every declaration "
                     "below it")
    imports = [normalize(line) for line in code.split("\n")
               if line.startswith("import ")]
    expected = IMPORT_PINS.get(key)
    if expected is None:
        fail(f"{key}: no import pin recorded")
    if imports != list(expected):
        fail(f"{key}: import list changed: {imports} != {list(expected)}")
    expected_vars = VARIABLE_PINS.get(key)
    if expected_vars is None:
        fail(f"{key}: no `variable` pin recorded")
    if variables != list(expected_vars):
        fail(f"{key}: section `variable` list changed: a `variable` line is an "
             f"implicit binder on every declaration below it, so this is a "
             f"premise change: {variables} != {list(expected_vars)}")


def open_world_bar(key: str, found: dict) -> int:
    """Every binder of every pinned statement, classified positively."""
    checked = 0
    for name, declaration in sorted(found.items()):
        if declaration["kind"] not in ("theorem", "lemma"):
            continue
        statement = statement_of(declaration)
        flat = normalize(statement)
        public = not declaration["private"]
        for token in COOPERATIVE_WORLD_TOKENS:
            if re.search(r"(?<![A-Za-z0-9_])" + re.escape(token) +
                         r"(?![A-Za-z0-9_])", flat):
                fail(f"{key}: {name} mentions {token!r} -- a cooperative-world "
                     "restriction has entered an open-world statement")
        if public:
            for address in re.findall(r"getCode ([A-Za-z_][A-Za-z0-9_'.]*)",
                                      flat):
                if address not in OWN_ADDRESS_TERMS:
                    fail(f"{key}: public statement {name} reads the code at "
                         f"{address!r}; a public statement of this family may "
                         "only speak about the code at the contract's own "
                         "address, and pinning a callee's bytecode is exactly "
                         "the narrowing this family exists to avoid")
            for compiled in re.findall(r"Prog\.compile \(?([^)]*)\)?", flat):
                if normalize(compiled) != "runtime dp":
                    fail(f"{key}: public statement {name} compiles "
                         f"{compiled!r} rather than `runtime dp`")
        binders, _ = split_binders(statement, declaration["name"])
        for binder in binders:
            bracket, names, kind = binder_parts(binder)
            checked += 1
            if kind in DATA_TYPES:
                continue
            matched = None
            for label, pattern, public_ok in ADMISSIBLE_HYPOTHESES:
                if re.fullmatch(pattern, kind):
                    matched = (label, public_ok)
                    break
            if matched is None:
                fail(f"{key}: {name} carries a binder of an unrecognised "
                     f"shape: {' '.join(names) or '_'} : {kind}\n"
                     "        This gate admits hypotheses by allowlist, not by "
                     "denylist, so an unanticipated premise fails whatever it "
                     "is called. If this shape is genuinely admissible, add it "
                     "to ADMISSIBLE_HYPOTHESES with a label, and say in review "
                     "why it does not restrict the world the theorem quantifies "
                     "over.")
            label, public_ok = matched
            if public and not public_ok:
                fail(f"{key}: public statement {name} carries the "
                     f"{label!r} premise ({kind}). That shape is inversion "
                     "residue admissible only inside the module; hoisting it "
                     "into a public statement narrows the claim.")
    return checked


# --------------------------------------------------------------------------
# Coverage, derived from the program's own dispatcher
# --------------------------------------------------------------------------

def top_level_split(text: str, separator: str = ",") -> list:
    parts, depth, start = [], 0, 0
    for index, char in enumerate(text):
        if char in OPEN:
            depth += 1
        elif char in CLOSE:
            depth -= 1
        elif char == separator and depth == 0:
            parts.append(text[start:index])
            start = index + 1
    parts.append(text[start:])
    return [part.strip() for part in parts if part.strip()]


def head_symbol(expression: str) -> str:
    expression = normalize(expression).strip()
    while expression.startswith("(") and expression.endswith(")"):
        expression = expression[1:-1].strip()
    match = re.match(r"^([A-Za-z_][A-Za-z0-9_']*)", expression)
    if not match:
        fail(f"cannot read a head symbol from {expression!r}")
    return match.group(1)


def dispatcher_inventory(source: str) -> list:
    """The seventeen dispatch entries, derived from `funcs`' own source.

    Nothing here is a hard-coded selector allowlist: the entry count, the
    selector names, the argument types and the body of each entry are read out
    of `Blanc/LidoCircuitBreaker.lean`, so a dispatcher that gains, loses or
    reorders a target changes what the coverage obligation is.
    """
    for declaration in declarations(source):
        if declaration["name"] != "funcs" or declaration["kind"] != "def":
            continue
        cut = definition_marker(declaration["text"])
        body = declaration["text"][cut + 2:]
        start = body.index("[")
        depth = 0
        for index in range(start, len(body)):
            if body[index] in OPEN:
                depth += 1
            elif body[index] in CLOSE:
                depth -= 1
                if depth == 0:
                    inner = body[start + 1:index]
                    break
        else:
            fail("funcs: unterminated dispatch list")
        entries = []
        for element in top_level_split(inner):
            if not (element.startswith("(") and element.endswith(")")):
                fail(f"funcs: dispatch entry is not a pair: {element!r}")
            parts = top_level_split(element[1:-1])
            if len(parts) != 2:
                fail(f"funcs: dispatch entry is not a pair: {element!r}")
            key, target = parts
            match = re.fullmatch(r'selector "([^"]*)" \[(.*)\]', normalize(key))
            if not match:
                fail(f"funcs: dispatch key is not a `selector` literal: "
                     f"{normalize(key)!r}; the coverage obligation is derived "
                     "from this list and cannot be derived from another shape")
            entries.append({
                "selector": match.group(1),
                "args": normalize(match.group(2)),
                "body": normalize(target),
                "head": head_symbol(target),
            })
        if not entries:
            fail("funcs: empty dispatch list")
        return entries
    fail(f"{PROGRAM_SOURCE}: no `def funcs` to derive the dispatcher from")
    return []


def dispatcher_digest(entries: list) -> str:
    return digest(json.dumps(
        [[entry["selector"], entry["args"], entry["body"]] for entry in entries],
        ensure_ascii=False, sort_keys=True))


def collection_arms(found: dict, name: str) -> tuple:
    """The ordered endpoints one collection theorem accounts for.

    Read out of the proof's own case arms, so an endpoint demoted from
    "discharged here" to "assumed by the caller" is visible: the arm stops
    naming a `*_funcSound` theorem and starts naming a binder.
    """
    if name not in found:
        fail(f"endpoints: collection theorem {name} is absent")
    declaration = found[name]
    statement = statement_of(declaration)
    binders, _ = split_binders(statement, declaration["name"])
    assumed, excluded = {}, {}
    for binder in binders:
        bracket, names, kind = binder_parts(binder)
        obligation = re.fullmatch(
            r"\(registrySpec dp\)\.FuncSound ca aux (.+)", kind)
        exclusion = re.fullmatch(r"p\.2 ≠ (.+)", kind)
        for binder_name in names:
            if obligation:
                assumed[binder_name] = head_symbol(obligation.group(1))
            elif exclusion:
                excluded[binder_name] = head_symbol(exclusion.group(1))
    body = declaration["text"][definition_marker(declaration["text"]):]
    rcases = re.search(r"rcases hp with (.+?) <;>", body, re.DOTALL)
    if not rcases:
        fail(f"endpoints: {name} no longer splits `hp` with `rcases ... <;>`; "
             "the coverage obligation is read out of that split and cannot be "
             "read out of another shape")
    arms = len(top_level_split(normalize(rcases.group(1)), "|"))
    order = []
    for term in re.findall(r"(?m)^\s*·\s+exact\s+(.+?)\s*$", body):
        term = normalize(term)
        absurd = re.fullmatch(r"absurd rfl ([A-Za-z_][A-Za-z0-9_']*)", term)
        if absurd:
            if absurd.group(1) not in excluded:
                fail(f"endpoints: {name} excludes via {absurd.group(1)!r}, "
                     "which is not an exclusion premise")
            order.append((excluded[absurd.group(1)], "excluded"))
            continue
        first = term.split()[0]
        if first in assumed:
            order.append((assumed[first], "assumed"))
            continue
        proved = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_']*)_funcSound dp ca", term)
        if proved:
            order.append((proved.group(1), "proved"))
            continue
        fail(f"endpoints: {name} has a coverage arm this gate cannot read: "
             f"{term!r}. Every arm must discharge its endpoint with "
             "`<endpoint>_funcSound dp ca`, with a named Registry-mutating "
             "obligation, or with `absurd rfl <exclusion>`.")
    return arms, order, assumed, excluded


def coverage(program: str, found: dict) -> dict:
    entries = dispatcher_inventory(program)
    if dispatcher_digest(entries) != DISPATCHER_PIN:
        fail(f"the dispatcher `funcs` in {PROGRAM_SOURCE} changed: "
             f"{len(entries)} entries, digest {dispatcher_digest(entries)}. "
             "Every endpoint obligation in this family is indexed to that "
             "list, so a changed dispatcher is a changed coverage obligation "
             "and must be reviewed, not absorbed.")
    program = [entry["head"] for entry in entries]
    if len(set(program)) != len(program):
        fail("the dispatcher names the same body twice; coverage cannot be "
             "read off it")

    funcs_arms, funcs_order, assumed, excluded = collection_arms(
        found, "funcSound_of_mem_funcs")
    non_arms, non_order, _, non_excluded = collection_arms(
        found, "funcSound_of_mem_nonRegistry")

    for label, arms in (("funcSound_of_mem_funcs", funcs_arms),
                        ("funcSound_of_mem_nonRegistry", non_arms)):
        if arms != len(program):
            fail(f"endpoints: {label} splits the dispatch list into {arms} "
                 f"cases but `funcs` has {len(program)} entries")
    for label, order in (("funcSound_of_mem_funcs", funcs_order),
                         ("funcSound_of_mem_nonRegistry", non_order)):
        covered = [endpoint for endpoint, _ in order]
        if len(covered) != len(program):
            fail(f"endpoints: {label} accounts for {len(covered)} endpoints "
                 f"but `funcs` has {len(program)}")
        if len(set(covered)) != len(covered):
            duplicated = sorted({e for e in covered if covered.count(e) > 1})
            fail(f"endpoints: {label} accounts for {duplicated} more than once")
        if covered != program:
            missing = [e for e in program if e not in covered]
            extra = [e for e in covered if e not in program]
            fail(f"endpoints: {label} does not account for the dispatcher's "
                 f"own entries in its own order. missing={missing} "
                 f"unaccounted={extra} program={program} covered={covered}")

    mutating = sorted(assumed.values())
    if sorted(non_excluded.values()) != mutating:
        fail("endpoints: the two collection theorems disagree about which "
             f"targets are Registry-mutating: {mutating} vs "
             f"{sorted(non_excluded.values())}")
    if len(mutating) != 2:
        fail(f"endpoints: expected exactly two Registry-mutating obligations, "
             f"found {mutating}")

    discharged = sorted(endpoint for endpoint, role in funcs_order
                        if role == "proved")
    if len(discharged) + len(mutating) != len(program):
        fail(f"endpoints: {len(discharged)} endpoints discharged plus "
             f"{len(mutating)} Registry-mutating obligations do not account "
             f"for the dispatcher's {len(program)} entries")
    for endpoint in discharged:
        theorem = endpoint + "_funcSound"
        if theorem not in found:
            fail(f"endpoints: coverage arm cites {theorem}, which is absent")
        statement = statement_of(found[theorem])
        _, conclusion = split_binders(statement, theorem)
        match = re.fullmatch(
            r"\(registrySpec dp\)\.FuncSound ca aux (.+)", conclusion)
        if not match:
            fail(f"endpoints: {theorem} does not conclude a `FuncSound` "
                 f"obligation for the exact spec: {conclusion!r}")
        if head_symbol(match.group(1)) != endpoint:
            fail(f"endpoints: {theorem} is named for {endpoint!r} but proves "
                 f"the obligation for {head_symbol(match.group(1))!r}")
    return {
        "entries": entries,
        "program": program,
        "discharged": discharged,
        "mutating": mutating,
    }


# --------------------------------------------------------------------------
# Trust scan
# --------------------------------------------------------------------------
#
# Applied twice over each owner: once to the code with every comment blanked,
# once to the comments with every line of code blanked.  A hit in CODE fails
# outright -- this family has no code-side allowance and is not going to
# acquire one silently.  A hit in a COMMENT must equal a reviewed row below,
# which is what lets `Blanc/LidoCircuitBreakerHistoryEndpoints.lean` keep the
# docstring warning against `decide` and `maxRecDepth` while making it
# impossible for either word to move from that docstring into a tactic.

TRUST_RULES = (
    ("T1-sorry", re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")),
    ("T2-admit", re.compile(r"(?<![A-Za-z0-9_])admit(?![A-Za-z0-9_])")),
    ("T3-axiom", re.compile(r"(?<![A-Za-z0-9_])axiom(?![A-Za-z0-9_])")),
    ("T4-opaque", re.compile(r"(?<![A-Za-z0-9_])opaque(?![A-Za-z0-9_])")),
    ("T5-native-decide",
     re.compile(r"(?<![A-Za-z0-9_])native_decide(?![A-Za-z0-9_])")),
    ("T6-decide", re.compile(r"(?<![A-Za-z0-9_])decide(?![A-Za-z0-9_])")),
    ("T7-maxRecDepth",
     re.compile(r"(?<![A-Za-z0-9_])maxRecDepth(?![A-Za-z0-9_])")),
    ("T8-maxHeartbeats",
     re.compile(r"(?<![A-Za-z0-9_])maxHeartbeats(?![A-Za-z0-9_])")),
    ("T9-set-option",
     re.compile(r"(?<![A-Za-z0-9_])set_option(?![A-Za-z0-9_])")),
    ("T10-implemented-by",
     re.compile(r"(?<![A-Za-z0-9_])implemented_by(?![A-Za-z0-9_])")),
    ("T11-extern", re.compile(r"@\s*\[\s*extern(?:\s|\]|\()")),
    ("T12-partial-def",
     re.compile(r"(?<![A-Za-z0-9_])partial\s+def(?![A-Za-z0-9_])")),
    ("T13-dbg-trace",
     re.compile(r"(?<![A-Za-z0-9_])dbg_trace(?![A-Za-z0-9_])")),
)


def scan_rows(relative: str, text: str) -> set:
    rows = set()
    for line in text.split("\n"):
        for rule, pattern in TRUST_RULES:
            if pattern.search(line):
                rows.add(f"{rule} {relative} {normalize(line)}")
    return rows


def trust_scan(sources: dict) -> tuple:
    owners = active_owners()
    code_rows, comment_rows = set(), set()
    for key, source in sources.items():
        relative = owners[key]
        code_rows |= scan_rows(relative, strip_comments(source))
        comment_rows |= scan_rows(relative, comment_text(source))
    if code_rows:
        fail("trust token in CODE (not in a comment):\n        " +
             "\n        ".join(sorted(code_rows)))
    expected = {normalize(row) for row in COMMENT_TRUST_ROWS}
    unexpected = sorted(comment_rows - expected)
    stale = sorted(expected - comment_rows)
    if unexpected:
        fail("unreviewed trust-token mention in a comment:\n        " +
             "\n        ".join(unexpected))
    if stale:
        fail("reviewed comment row no longer present (reworded or deleted); "
             "a comment that discusses a trust token is reviewed text:\n"
             "        " + "\n        ".join(stale))
    return code_rows, comment_rows


# --------------------------------------------------------------------------
# Axiom expectations
# --------------------------------------------------------------------------
#
# Every public theorem of every active owner is probed INDIVIDUALLY and must
# report exactly `propext`, `Classical.choice`, `Quot.sound`.  There is no
# exception table and no trust shortcut: a theorem that depends on nothing at
# all fails here until someone explains why, and a theorem that acquires a
# fourth axiom -- `sorryAx` above all -- fails at once.
#
# Private declarations cannot be named at the term level from another module,
# so they are not probed directly.  They are not a gap: a private lemma that
# used an axiom would put that axiom into every public theorem that depends on
# it, and a private lemma that no public theorem depends on is dead code that
# the trust scan's `T3-axiom` and `T1-sorry` rules still read.

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


def probe_targets(sources: dict) -> list:
    targets = []
    for key, source in sorted(sources.items()):
        for declaration in declarations(source):
            if declaration["kind"] not in ("theorem", "lemma"):
                continue
            if declaration["private"]:
                continue
            targets.append(qualified(declaration))
    return sorted(set(targets))


def compiled_owners_present(root: Path) -> None:
    for key, module in active_modules().items():
        olean = root / (".lake/build/lib/lean/" +
                        module.replace(".", "/") + ".olean")
        if not olean.is_file():
            fail(f"compiled owner {key} is absent ({olean.name}); run the "
                 "approved elaboration checkpoint before the axiom probe")


def axiom_checks(root: Path, sources: dict) -> int:
    targets = probe_targets(sources)
    compiled_owners_present(root)
    # The probe file lives in a real temporary DIRECTORY, not in the
    # repository.  Written into `root` it was one hard kill away from leaving
    # a stray `history-axioms-*.lean` behind in the tree -- which `lake` would
    # then try to build, and which a `git add -A` would happily commit.
    # `lake env` only sets the environment, so `lean` finds the owners through
    # LEAN_PATH and the probe file itself need not sit inside the package.
    with tempfile.TemporaryDirectory(prefix="s7-axioms-") as staging:
        temporary = Path(staging) / "history-axioms.lean"
        with temporary.open("w", encoding="utf-8") as handle:
            for module in probe_imports():
                handle.write("import " + module + "\n")
            for name in targets:
                handle.write("#print axioms " + name + "\n")
        run = subprocess.run(
            ["lake", "env", "lean", str(temporary)],
            cwd=root, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT)
    if run.returncode:
        fail("axiom probe failed:\n" + run.stdout)
    for name in targets:
        depends = re.search(
            r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]",
            run.stdout, re.DOTALL)
        if depends:
            actual = {item.strip() for item in depends.group(1).split(",")
                      if item.strip()}
        elif re.search(r"'" + re.escape(name) +
                       r"' does not depend on any axioms", run.stdout):
            actual = set()
        else:
            fail(f"{name}: unrecognised #print axioms output")
            actual = set()
        if actual != set(STANDARD_AXIOMS):
            fail(f"{name}: axioms {sorted(actual)}, expected "
                 f"{sorted(STANDARD_AXIOMS)}")
    return len(targets)


# --------------------------------------------------------------------------
# The mutation harness
# --------------------------------------------------------------------------
#
# A pin that nobody has ever seen reject anything is a decoration.  The three
# families below are the ones this gate's design claims to catch, written as
# runnable patches rather than as prose.
#
# The discipline every case obeys is: LIVE FIRST.  A patch that does not
# elaborate is not a weakening, it is a syntax error, and rejecting it proves
# nothing -- so each case is built in an isolated worktree, the affected
# modules are rebuilt there, and only a patch that BUILDS is allowed to have
# its rejection credited.  A case whose build fails is reported as
# LIVE-CONFIRMATION FAILED and fails the harness; it is not quietly counted.
#
# Several cases carry repair edits alongside the weakening.  That is not
# padding: gutting `RegistryCoherent` to `True` makes its own witness lemmas
# ill-typed, so a mutation that only edits the definition would be rejected by
# the elaborator rather than by this gate, which is not what is being measured.
# The repairs are the minimum that keeps the library building while the CLAIM
# is strictly weaker.
#
# The harness never runs against the repository root.
#
# FIRST RUN, against the completed tree: M2 and M5 are CREDITED -- each
# elaborates and is then rejected with every digest re-taken from the mutant.
# M1, M3 and M4 FAIL LIVE CONFIRMATION and are not credited.  All three fail
# for one structural reason, and it is a finding about the family rather than
# a defect in the harness:
#
#   Every one of these patches was designed while the Chain owner was a
#   dormant stub.  That owner is now complete, and it CONSUMES what the
#   patches weaken.  A cooperative-world premise introduced at an internal
#   node (M3 at `registrySpec_sound_of_funcSound`, M4 at `coherent_of_call`)
#   is unsatisfiable at its new consumers, and it cannot be threaded upward
#   to escape them, because the statements above it are typed by
#   `ContractSpec.Sound` / `.FuncSound`, whose shape is fixed in
#   `Blanc/Ladder.lean`.  Threading it there would now trip VOCABULARY_PINS.
#
#   M1 is stronger still: gutting `RegistryCoherent` cannot be repaired at
#   all.  The H8 anti-vacuity controls publicly export `∃ entries,
#   RegistryWitness ...` and every one of the structure's nine fields is
#   projected 12-22 times across the owners, so a vacuous invariant leaves
#   `RegistryStable.witness` and its four reader-facing corollaries with no
#   proof and no possible repair short of DELETING them -- which the pin
#   tables catch as a pinned declaration gone absent.
#
# The honest reading is that families (ii) and (iii) are live-confirmed here,
# and family (i) is now enforced by the module's own structure BEFORE this
# gate ever sees it.  That is a better outcome than a credited rejection, but
# it is not the same claim, and it must not be recorded as one.  Restoring a
# credited family-(i) mutant needs a redesign -- a mutant that guts the
# invariant AND removes the controls that would fail to compile -- which is a
# design decision, not a repair-set adjustment.

MUTATIONS = (
    {
        "name": "M1-registry-coherent-vacuous",
        "family": "(i) the invariant no longer yields a real witness",
        "requires_chain": False,
        "expect": "RegistryCoherent",
        "why": (
            "`RegistryCoherent` is a `def`.  Emptied to `True`, every theorem "
            "header in the family stays byte-identical, every proof still "
            "goes through, and the whole chain result says nothing at all.  "
            "No header pin can see this; DEFINITION_PINS and "
            "SEMANTIC_CHANNELS are what must."),
        "edits": (
            ("Blanc/LidoCircuitBreakerHistory.lean",
             "def RegistryCoherent (s : Stor) : Prop :=\n"
             "  ∃ entries, RegistryWitness (logicalStorageOfStor s) entries",
             "def RegistryCoherent (_s : Stor) : Prop := True"),
            ("Blanc/LidoCircuitBreakerHistoryEndpoints.lean",
             "    RegistryCoherent (s.set (slot configRegion payload) value) :=\n"
             "  h.imp fun _ hw => hw.config_set hpayload",
             "    RegistryCoherent (s.set (slot configRegion payload) value) :=\n"
             "  trivial"),
            ("Blanc/LidoCircuitBreakerHistoryEndpoints.lean",
             "    RegistryCoherent (s.set (expirySlot pauser) value) :=\n"
             "  h.imp fun _ hw => hw.expiry_set hpauser",
             "    RegistryCoherent (s.set (expirySlot pauser) value) :=\n"
             "  trivial"),
            ("Blanc/LidoCircuitBreakerHistoryEndpoints.lean",
             "    (fun _ _ hcoh => hcoh.config_set (payload := 0) zero_payload_lt)",
             "    (fun _ _ _ => trivial)"),
            ("Blanc/LidoCircuitBreakerHistoryEndpoints.lean",
             "    (fun _ _ hcoh => hcoh.config_set (payload := 1) one_payload_lt)",
             "    (fun _ _ _ => trivial)"),
            ("Blanc/LidoCircuitBreakerHistoryEndpoints.lean",
             "    (fun a _ _ hcoh => hcoh.expiry_set (canonicalAddress_toB256 a))",
             "    (fun _ _ _ _ => trivial)"),
        ),
    },
    {
        "name": "M2-endpoint-demoted-to-assumption",
        "family": "(ii) a runtime endpoint omitted from the coverage object",
        "requires_chain": False,
        "expect": "Registry-mutating",
        "why": (
            "`isPauserLive` moves from `discharged here` to `supplied by the "
            "caller`.  The module still compiles, `funcSound_of_mem_funcs` "
            "still reads as the whole dispatch list, and the family now "
            "covers sixteen of seventeen targets.  Only a coverage object "
            "derived from `funcs`' own source can see the difference."),
        "edits": (
            ("Blanc/LidoCircuitBreakerHistoryEndpoints.lean",
             "    (hpause : (registrySpec dp).FuncSound ca aux pause)\n"
             "    {p : B256 × Func} (hp : p ∈ funcs dp) :",
             "    (hpause : (registrySpec dp).FuncSound ca aux pause)\n"
             "    (hlive : (registrySpec dp).FuncSound ca aux isPauserLive)\n"
             "    {p : B256 × Func} (hp : p ∈ funcs dp) :"),
            ("Blanc/LidoCircuitBreakerHistoryEndpoints.lean",
             "  · exact setPauseDuration_funcSound dp ca\n"
             "  · exact isPauserLive_funcSound dp ca\n\n"
             "/-- The same fifteen rows",
             "  · exact setPauseDuration_funcSound dp ca\n"
             "  · exact hlive\n\n"
             "/-- The same fifteen rows"),
            # The Chain owner is now a real consumer of the collection
            # theorem, so the demoted endpoint has to be supplied at its call
            # site or the mutant does not elaborate at all.  It IS suppliable
            # -- `isPauserLive_funcSound` is still proved in the endpoints
            # owner -- which is exactly what makes this a WEAKENING of the
            # collection theorem rather than a broken edit.
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "    funcSound_of_mem_funcs dp ca (registerPauser_funcSound dp ca)\n"
             "      (pause_funcSound dp ca) hp",
             "    funcSound_of_mem_funcs dp ca (registerPauser_funcSound dp ca)\n"
             "      (pause_funcSound dp ca) (isPauserLive_funcSound dp ca) hp"),
        ),
    },
    {
        "name": "M3-cooperative-callee-premise",
        "family": "(iii) a cooperative-callee restriction behind an "
                  "unchanged-looking wrapper",
        "requires_chain": False,
        "expect": "code at",
        "why": (
            "A premise built entirely from vocabulary the family already uses, "
            "with a binder name a reviewer skims past, that quietly says every "
            "account in the world runs this contract's code.  The conclusion "
            "is unchanged and the proof ignores the premise, so the module "
            "builds.  The positive allowlist rejects it because its SHAPE is "
            "not admissible -- not because anyone listed its name."),
        "edits": (
            ("Blanc/LidoCircuitBreakerHistory.lean",
             "theorem registrySpec_sound_of_funcSound (dp : DeployParams) (ca : Adr)\n"
             "    (h_all : ∀ p ∈ funcs dp, (registrySpec dp).FuncSound ca aux p.2) :",
             "theorem registrySpec_sound_of_funcSound (dp : DeployParams) (ca : Adr)\n"
             "    (h_frame : ∀ (s : Devm) (t : Adr),\n"
             "      some (s.getCode t).toList = Prog.compile (runtime dp))\n"
             "    (h_all : ∀ p ∈ funcs dp, (registrySpec dp).FuncSound ca aux p.2) :"),
        ),
    },
    {
        "name": "M4-chain-callee-pinned",
        "family": "(iii) a cooperative-callee restriction, at the external edge",
        "requires_chain": True,
        "expect": "code at",
        "why": (
            "`coherent_of_call` is the one public statement that stands "
            "downstream of arbitrary callee execution.  Pinning the callee's "
            "bytecode there leaves the conclusion identical and the proof "
            "easier, and turns an open-world transport lemma into a "
            "closed-world one.  Two independent nets must reject it: the "
            "own-address rule and the allowlist."),
        "edits": (
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile (runtime dp))\n"
             "    (h_coh : RegistryCoherent (Devm.getStor s sevm.currentTarget))\n"
             "    (h_run : Ninst.Run sevm s call sf) :",
             "    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile (runtime dp))\n"
             "    (h_callee : some (s.getCode w.toAdr).toList = Prog.compile (runtime dp))\n"
             "    (h_coh : RegistryCoherent (Devm.getStor s sevm.currentTarget))\n"
             "    (h_run : Ninst.Run sevm s call sf) :"),
        ),
    },
    {
        "name": "M5-chain-entry-list-identified",
        "family": "(iii) the post-callback entry list identified with the "
                  "entry list",
        "requires_chain": True,
        "expect": "unrecognised",
        "why": (
            "The invariant is existential in the entry list precisely because "
            "a callback may register a pauser.  A premise that identifies the "
            "two lists is the false strengthening the module's own docstring "
            "names, and it would leave `chain_preserves_registryStable` "
            "reading exactly as it does now.  The binder is called `hcarry`, "
            "not `sameEntries`, on purpose: the token denylist must NOT be "
            "what catches this one."),
        # The anchor names the theorem's own header line.  The two-binder
        # anchor this case used while the Chain owner was dormant became
        # ambiguous the moment the H7 reader-facing corollaries landed: three
        # of them carry the same `reach`/`stable` pair, so the patch matched
        # four places and the harness refused it. The MUTATION is unchanged --
        # only the anchor is narrowed to the one theorem it was written for.
        "edits": (
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "theorem chain_preserves_registryStable (dp : DeployParams) "
             "(ca : Adr)\n"
             "    (checkpoint future : BlockChain)\n"
             "    (reach : BlockChain.Reach checkpoint future)\n"
             "    (stable : RegistryStable dp ca checkpoint.state) :",
             "theorem chain_preserves_registryStable (dp : DeployParams) "
             "(ca : Adr)\n"
             "    (checkpoint future : BlockChain)\n"
             "    (reach : BlockChain.Reach checkpoint future)\n"
             "    (hcarry : ∀ entries,\n"
             "      RegistryWitness (logicalStorageOfStor "
             "(checkpoint.state.getStor ca)) entries →\n"
             "      RegistryWitness (logicalStorageOfStor "
             "(future.state.getStor ca)) entries)\n"
             "    (stable : RegistryStable dp ca checkpoint.state) :"),
            # The four reader-facing corollaries call the headline theorem,
            # so a premise added to it has to be threaded through them or
            # nothing elaborates.  Threading it is the honest repair: a
            # narrowing of the headline IS a narrowing of everything that
            # reads through it, and the gate rejects the first of them.
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "theorem chain_future_installedCode (dp : DeployParams) (ca : Adr)\n"
             "    (checkpoint future : BlockChain)\n"
             "    (reach : BlockChain.Reach checkpoint future)\n"
             "    (stable : RegistryStable dp ca checkpoint.state)",
             "theorem chain_future_installedCode (dp : DeployParams) (ca : Adr)\n"
             "    (checkpoint future : BlockChain)\n"
             "    (reach : BlockChain.Reach checkpoint future)\n"
             "    (hcarry : ∀ entries,\n"
             "      RegistryWitness (logicalStorageOfStor "
             "(checkpoint.state.getStor ca)) entries →\n"
             "      RegistryWitness (logicalStorageOfStor "
             "(future.state.getStor ca)) entries)\n"
             "    (stable : RegistryStable dp ca checkpoint.state)"),
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "  (chain_preserves_registryStable dp ca checkpoint future reach\n"
             "    stable).installedCode",
             "  (chain_preserves_registryStable dp ca checkpoint future reach hcarry\n"
             "    stable).installedCode"),
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "theorem chain_future_witness (dp : DeployParams) (ca : Adr)\n"
             "    (checkpoint future : BlockChain)\n"
             "    (reach : BlockChain.Reach checkpoint future)\n"
             "    (stable : RegistryStable dp ca checkpoint.state)",
             "theorem chain_future_witness (dp : DeployParams) (ca : Adr)\n"
             "    (checkpoint future : BlockChain)\n"
             "    (reach : BlockChain.Reach checkpoint future)\n"
             "    (hcarry : ∀ entries,\n"
             "      RegistryWitness (logicalStorageOfStor "
             "(checkpoint.state.getStor ca)) entries →\n"
             "      RegistryWitness (logicalStorageOfStor "
             "(future.state.getStor ca)) entries)\n"
             "    (stable : RegistryStable dp ca checkpoint.state)"),
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "  (chain_preserves_registryStable dp ca checkpoint future "
             "reach stable).witness",
             "  (chain_preserves_registryStable dp ca checkpoint future "
             "reach hcarry stable).witness"),
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "theorem chain_future_membership (dp : DeployParams) (ca : Adr)\n"
             "    (checkpoint future : BlockChain)\n"
             "    (reach : BlockChain.Reach checkpoint future)\n"
             "    (stable : RegistryStable dp ca checkpoint.state)",
             "theorem chain_future_membership (dp : DeployParams) (ca : Adr)\n"
             "    (checkpoint future : BlockChain)\n"
             "    (reach : BlockChain.Reach checkpoint future)\n"
             "    (hcarry : ∀ entries,\n"
             "      RegistryWitness (logicalStorageOfStor "
             "(checkpoint.state.getStor ca)) entries →\n"
             "      RegistryWitness (logicalStorageOfStor "
             "(future.state.getStor ca)) entries)\n"
             "    (stable : RegistryStable dp ca checkpoint.state)"),
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "  (chain_preserves_registryStable dp ca checkpoint future reach\n"
             "    stable).membership htarget",
             "  (chain_preserves_registryStable dp ca checkpoint future reach hcarry\n"
             "    stable).membership htarget"),
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "theorem chain_future_countConservation (dp : DeployParams) (ca : Adr)\n"
             "    (checkpoint future : BlockChain)\n"
             "    (reach : BlockChain.Reach checkpoint future)\n"
             "    (stable : RegistryStable dp ca checkpoint.state)",
             "theorem chain_future_countConservation (dp : DeployParams) (ca : Adr)\n"
             "    (checkpoint future : BlockChain)\n"
             "    (reach : BlockChain.Reach checkpoint future)\n"
             "    (hcarry : ∀ entries,\n"
             "      RegistryWitness (logicalStorageOfStor "
             "(checkpoint.state.getStor ca)) entries →\n"
             "      RegistryWitness (logicalStorageOfStor "
             "(future.state.getStor ca)) entries)\n"
             "    (stable : RegistryStable dp ca checkpoint.state)"),
            ("Blanc/LidoCircuitBreakerHistoryChain.lean",
             "  (chain_preserves_registryStable dp ca checkpoint future reach\n"
             "    stable).countConservation",
             "  (chain_preserves_registryStable dp ca checkpoint future reach hcarry\n"
             "    stable).countConservation"),
        ),
    },
)


def apply_edits(root: Path, edits) -> dict:
    original = {}
    for relative, old, new in edits:
        path = root / relative
        text = path.read_text(encoding="utf-8")
        original.setdefault(relative, text)
        if old not in text:
            fail(f"mutation edit does not apply to {relative}: {old!r}")
        if text.count(old) != 1:
            fail(f"mutation edit is not unique in {relative}: {old!r}")
        path.write_text(text.replace(old, new, 1), encoding="utf-8")
    return original


def restore(root: Path, original: dict) -> None:
    for relative, text in original.items():
        (root / relative).write_text(text, encoding="utf-8")


@contextlib.contextmanager
def repinned(tree: Path):
    """Run the gate as if the author had re-taken every digest.

    This is the campaign's whole point.  A digest catches a mutation once; the
    next person to edit the proof re-takes it, in good faith, and the mutation
    passes forever after.  So every case is judged twice: once against the
    recorded pins, and once against pins recomputed FROM THE MUTANT.  Only the
    second verdict is credited, because only the second measures a net that
    survives ordinary maintenance -- the semantic channels, the open-world
    allowlist, the derived coverage object, the trust scan and the axiom probe.

    The dormant Chain owner's recorded pins are carried through unchanged: a
    re-pin of the active owners must not quietly erase them.
    """
    names = ("HEADER_PINS", "DEFINITION_PINS", "IMPORT_PINS", "VARIABLE_PINS",
             "DISPATCHER_PIN", "COMMENT_TRUST_ROWS", "VOCABULARY_PINS")
    fresh = observed_pins(tree, include_chain=CHAIN.active)
    saved = {name: globals()[name] for name in names}
    try:
        for name in names:
            globals()[name] = fresh[name]
        if not CHAIN.active:
            carried = dict(fresh["HEADER_PINS"])
            carried[CHAIN.key] = saved["HEADER_PINS"].get(CHAIN.key, {})
            globals()["HEADER_PINS"] = carried
        yield
    finally:
        for name in names:
            globals()[name] = saved[name]


def judge_mutant(tree: Path, case: dict) -> tuple:
    """(problems, credited_message) for one mutant already present in `tree`."""
    problems = []
    try:
        run_static_checks(tree)
        problems.append(
            f"{case['name']}: the recorded digests do not even notice this "
            "mutation")
    except Failure:
        pass
    with repinned(tree):
        try:
            run_static_checks(tree)
        except Failure as exc:
            message = str(exc)
            if case["expect"] not in message:
                problems.append(
                    f"{case['name']}: with every digest re-taken it is "
                    f"rejected, but by the wrong check -- expected a message "
                    f"mentioning {case['expect']!r}, got: "
                    f"{message.splitlines()[0]}")
                return problems, None
            return problems, message
        problems.append(
            f"{case['name']}: with every digest re-taken, this gate ACCEPTS "
            "the mutant. Only a digest stood between the family and this "
            "weakening, and a digest is re-taken by whoever next edits the "
            "proof.")
    return problems, None


def stage_mutant(root: Path, case: dict, staging: Path) -> None:
    """Write the mutant into a throwaway tree holding only what the static
    checks read."""
    (staging / "Blanc").mkdir(exist_ok=True)
    texts = {relative: read_source(root, relative)
             for relative in OWNERS.values()}
    texts[PROGRAM_SOURCE] = read_source(root, PROGRAM_SOURCE)
    for relative in VOCABULARY_SOURCES:
        texts[relative] = read_source(root, relative)
    if CHAIN.active:
        texts[CHAIN.path] = read_source(root, CHAIN.path)
    for relative, old, new in case["edits"]:
        if relative not in texts:
            fail(f"{case['name']}: target {relative} is not staged; a "
                 "chain-targeting case cannot be judged while the owner is "
                 "dormant")
        count = texts[relative].count(old)
        if count != 1:
            fail(f"{case['name']}: anchor occurs {count} times in {relative}, "
                 f"expected exactly once: {old.splitlines()[0]!r}")
        texts[relative] = texts[relative].replace(old, new, 1)
    for relative, text in texts.items():
        (staging / relative).write_text(text, encoding="utf-8")


def mutation_anchors_apply(root: Path, case: dict) -> str:
    """Check a patch still applies, reading the dormant Chain owner from git."""
    texts = {relative: read_source(root, relative)
             for relative in OWNERS.values()}
    texts[CHAIN.path] = (read_source(root, CHAIN.path) if CHAIN.active
                         else chain_source(root))
    for relative, old, new in case["edits"]:
        if relative not in texts:
            return f"unknown target {relative}"
        count = texts[relative].count(old)
        if count != 1:
            return (f"anchor occurs {count} times in {relative}, expected "
                    f"exactly once: {old.splitlines()[0]!r}")
        texts[relative] = texts[relative].replace(old, new, 1)
    return ""


def mutations_dry_run(root: Path) -> int:
    """Check every mutation patch still applies, and that this gate rejects it
    -- WITHOUT elaborating anything.

    A mutation harness rots silently: the proof it targets gets reworded, the
    anchor stops matching, and the campaign quietly stops testing anything.
    This mode is cheap enough to run at every checkpoint.

    It is not the campaign and credits nothing.  A patch that this gate
    rejects but that does not ELABORATE is a broken edit, not a weakening, and
    only `--mutations --worktree` can tell the two apart.
    """
    problems = []
    for case in MUTATIONS:
        stale = mutation_anchors_apply(root, case)
        if stale:
            problems.append(f"{case['name']}: {stale}")
            continue
        if case["requires_chain"] and not CHAIN.active:
            print(f"  applies   {case['name']}: {case['family']}"
                  "  (judgement pending chain activation)")
            continue
        with tempfile.TemporaryDirectory() as staging:
            staged = Path(staging)
            try:
                stage_mutant(root, case, staged)
            except Failure as exc:
                problems.append(str(exc))
                continue
            found, credited = judge_mutant(staged, case)
            problems.extend(found)
            if credited:
                print(f"  rejected  {case['name']}: {case['family']}\n"
                      f"            -> {credited.splitlines()[0]}")
    print()
    for problem in problems:
        print("MUTATION-DRY-RUN — " + problem)
    if problems:
        print(f"REGRESSION — {VERDICT} mutation dry run: {len(problems)} "
              "problem(s)")
        return 1
    runnable = sum(1 for case in MUTATIONS
                   if CHAIN.active or not case["requires_chain"])
    print(f"OK — {VERDICT} mutation dry run: {len(MUTATIONS)} patches apply; "
          f"{runnable} rejected by the check each was written for even with "
          f"every digest re-taken from the mutant; "
          f"{len(MUTATIONS) - runnable} pending on {CHAIN.path}. NOT the "
          "campaign: no mutant was elaborated, so nothing here is credited.")
    return 0


def run_mutations(worktree: Path) -> int:
    """The campaign. Live confirmation first, then judgement.

    Each case is applied in the caller's isolated worktree, the owners are
    REBUILT there, and only a mutant that builds has its rejection credited.
    A mutant that does not build is a broken edit whose rejection would prove
    nothing, and is reported as such rather than counted.
    """
    if worktree.resolve() == ROOT:
        print(f"REGRESSION — {VERDICT}: the mutation harness refuses to run "
              "against the repository root; pass --worktree with an isolated "
              "worktree (git worktree add, with .lake cloned into it)")
        return 2
    failures, credited, pending = [], [], []
    for case in MUTATIONS:
        if case["requires_chain"] and not CHAIN.active:
            pending.append(case["name"])
            print(f"PENDING {case['name']}: {case['family']} -- needs "
                  f"{CHAIN.path} to land and CHAIN.active = True")
            continue
        print(f"\n=== {case['name']}: {case['family']}")
        try:
            original = apply_edits(worktree, case["edits"])
        except Failure as exc:
            failures.append(f"{case['name']}: patch did not apply: {exc}")
            continue
        try:
            build = subprocess.run(
                ["lake", "build"] + list(active_modules().values()),
                cwd=worktree, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT)
            if build.returncode:
                failures.append(
                    f"{case['name']}: LIVE-CONFIRMATION FAILED -- the mutant "
                    "does not elaborate, so it is a broken edit and not a "
                    "weakening. Its rejection is NOT credited. Adjust the "
                    "repair edits until the mutant builds, then re-run.\n"
                    + build.stdout[-4000:])
                continue
            print("  live: the mutant elaborates")
            found, message = judge_mutant(worktree, case)
            failures.extend(found)
            if message:
                credited.append(case["name"])
                print(f"  rejected (digests re-taken): "
                      f"{message.splitlines()[0]}")
        finally:
            restore(worktree, original)
    print()
    for message in failures:
        print("MUTATION — " + message)
    if failures:
        print(f"REGRESSION — {VERDICT} mutation campaign: "
              f"{len(credited)} credited, {len(failures)} unrejected or "
              f"unconfirmed, {len(pending)} pending")
        return 1
    print(f"OK — {VERDICT} mutation campaign: {len(credited)} semantic "
          f"weakenings live-confirmed to elaborate and then rejected with "
          f"every digest re-taken from the mutant; {len(pending)} pending on "
          f"{CHAIN.path}")
    return 0


def chain_pin_integrity() -> None:
    """The Chain owner's pins are checked whether or not it is active.

    A dormant owner is the easiest place to lose a pin: nothing reads it, so
    nothing complains.  These two checks are what make `CHAIN.active = True`
    a one-line activation rather than a one-line activation plus a hunt.
    """
    pins = HEADER_PINS.get(CHAIN.key)
    if not pins:
        fail(f"{CHAIN.key}: no header pins recorded; the twelve public "
             "statements of the history ladder must stay pinned even while "
             "the owner is dormant")
    for name in CHAIN.required_public:
        if name not in pins:
            fail(f"{CHAIN.key}: required public statement {name} has no pin")
    if not CHAIN.active:
        path = ROOT / CHAIN.path
        if not path.is_file():
            fail(f"{CHAIN.key}: {CHAIN.path} is absent, but its pins are "
                 "recorded; either the owner moved or the pins are stale")


def run_static_checks(root: Path) -> dict:
    sources = load_owners(root)
    program = read_source(root, PROGRAM_SOURCE)
    chain_pin_integrity()
    vocabulary_pins(root)
    found_by_owner, binders = {}, 0
    for key, source in sorted(sources.items()):
        found = pin_declarations(key, source)
        semantic_channels(key, found)
        pin_imports_and_variables(key, source)
        binders += open_world_bar(key, found)
        found_by_owner[key] = found
    result = coverage(program, found_by_owner["endpoints"])
    trust_scan(sources)
    result["binders"] = binders
    result["found"] = found_by_owner
    result["pins"] = sum(len(HEADER_PINS.get(key, {})) +
                         len(DEFINITION_PINS.get(key, {}))
                         for key in sources)
    result["vocabulary"] = sum(len(names)
                               for names in VOCABULARY_NAMES.values())
    return result


# --------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------
#
# Each case runs ONE check against ONE mutated source, rather than the whole
# pipeline.  That is deliberate.  Running the pipeline would let the header
# pin absorb every case and prove nothing about the other nets; running each
# net alone is what shows that the open-world bar still rejects a premise
# whose digest someone has already re-taken, and that the trust scan really
# does tell a docstring from a tactic.

SELF_TESTS = (
    ("pin: a renamed binder in a public statement", "pin", "history",
     "theorem registrySpec_sound_of_funcSound (dp : DeployParams) (ca : Adr)",
     "theorem registrySpec_sound_of_funcSound (dp : DeployParams) (owner : Adr)",
     "normalized statement changed"),
    ("pin: a pinned theorem deleted", "pin", "endpoints",
     "theorem canonicalAddress_toB256 (a : Adr) :",
     "-- theorem canonicalAddress_toB256 (a : Adr) :",
     "is absent"),
    ("pin: a new theorem nobody pinned", "pin", "endpoints",
     "end LidoCircuitBreaker",
     "theorem selftest_addition : True := trivial\n\nend LidoCircuitBreaker",
     "has no pin"),
    ("open world: a target-code assumption", "world", "history",
     "    (h_all : ∀ p ∈ funcs dp, (registrySpec dp).FuncSound ca aux p.2) :",
     "    (h_frame : ∀ (s : Devm) (t : Adr),\n"
     "      some (s.getCode t).toList = Prog.compile (runtime dp))\n"
     "    (h_all : ∀ p ∈ funcs dp, (registrySpec dp).FuncSound ca aux p.2) :",
     "code at"),
    ("open world: an unanticipated premise with an innocuous shape",
     "world", "history",
     "    (h_all : ∀ p ∈ funcs dp, (registrySpec dp).FuncSound ca aux p.2) :",
     "    (h_frame : ∀ p ∈ funcs dp, Func.Inv Devm.getStor Devm.getStor p.2)\n"
     "    (h_all : ∀ p ∈ funcs dp, (registrySpec dp).FuncSound ca aux p.2) :",
     "unrecognised"),
    ("open world: PauseSuccessNoninterference", "world", "history",
     "    (h_all : ∀ p ∈ funcs dp, (registrySpec dp).FuncSound ca aux p.2) :",
     "    (h_ni : PauseSuccessNoninterference dp ca)\n"
     "    (h_all : ∀ p ∈ funcs dp, (registrySpec dp).FuncSound ca aux p.2) :",
     "PauseSuccessNoninterference"),
    ("open world: inversion residue hoisted into a public statement",
     "world", "endpoints",
     "theorem storFixed_enumLoop (dp : DeployParams) : StorFixed dp enumLoop :=",
     "theorem storFixed_enumLoop (dp : DeployParams)\n"
     "    (hsilent : SilentIn P enumLoop) : StorFixed dp enumLoop :=",
     "admissible only inside the module"),
    ("definition: RegistryCoherent gutted", "pin", "history",
     "def RegistryCoherent (s : Stor) : Prop :=\n"
     "  ∃ entries, RegistryWitness (logicalStorageOfStor s) entries",
     "def RegistryCoherent (_s : Stor) : Prop := True",
     "declaration body changed for RegistryCoherent"),
    ("definition: RegistryCoherent gutted AND its digest re-taken",
     "channels", "history",
     "def RegistryCoherent (s : Stor) : Prop :=\n"
     "  ∃ entries, RegistryWitness (logicalStorageOfStor s) entries",
     "def RegistryCoherent (_s : Stor) : Prop := True",
     "no longer mentions"),
    ("definition: registrySpec.Inv gutted AND its digest re-taken",
     "channels", "history",
     "  Inv := fun s _ _ => RegistryCoherent s",
     "  Inv := fun _ _ _ => True",
     "no longer mentions"),
    ("coverage: an endpoint demoted to an assumption", "coverage", "endpoints",
     "    (hpause : (registrySpec dp).FuncSound ca aux pause)\n"
     "    {p : B256 × Func} (hp : p ∈ funcs dp) :",
     "    (hpause : (registrySpec dp).FuncSound ca aux pause)\n"
     "    (hlive : (registrySpec dp).FuncSound ca aux isPauserLive)\n"
     "    {p : B256 × Func} (hp : p ∈ funcs dp) :",
     "Registry-mutating"),
    ("coverage: an endpoint arm silently dropped", "coverage", "endpoints",
     "  · exact isPauserLive_funcSound dp ca\n\n/-- The same fifteen rows",
     "\n/-- The same fifteen rows",
     "accounts for"),
    ("coverage: the dispatcher's own order permuted", "coverage", "endpoints",
     "  · exact pauseDuration_funcSound dp ca\n"
     "  · exact maxPauseDuration_funcSound dp ca",
     "  · exact maxPauseDuration_funcSound dp ca\n"
     "  · exact pauseDuration_funcSound dp ca",
     "in its own order"),
    ("coverage: a dispatch target removed from the program",
     "coverage", "program",
     "    (selector \"isPauserLive\" [.address], isPauserLive) ]",
     "  ]",
     "changed"),
    ("trust: `decide` moved from a docstring into a tactic", "trust",
     "endpoints",
     "  rw [heq]\n  exact Adr.toNat_lt_size a",
     "  rw [heq]\n  decide",
     "trust token in CODE"),
    ("trust: the docstring warning reworded", "trust", "endpoints",
     "not be driven by `decide`: deciding anything about these leaves forces the",
     "not be driven by `decide`: deciding anything about these targets forces the",
     "unreviewed trust-token mention in a comment"),
    ("trust: the docstring warning deleted", "trust", "endpoints",
     "`String.keccak` behind every `selector` and blows `maxRecDepth`. -/",
     "`String.keccak` behind every `selector`. -/",
     "no longer present"),
    ("trust: a `sorry` introduced", "trust", "history",
     "  exact absurd h_run not_run_rev",
     "  sorry",
     "trust token in CODE"),
    ("variable: a section variable that is a hypothesis", "variable",
     "history",
     "variable {dp : DeployParams}",
     "variable {dp : DeployParams} (hWorld : StorFixed dp Func.rev)",
     "not a declared data type"),
    # The vocabulary net.  Neither of these touches an owner, so every header
    # pin, every definition pin, every channel token and every allowlist
    # pattern in the family stays byte-identical while the meaning of the
    # words the pinned statements are written in changes underneath them.
    ("vocabulary: a RegistryWitness field gutted", "vocabulary",
     "Blanc/LidoCircuitBreakerRegistryModel.lean",
     "  arrayWords : ∀ index, index < entries.length →\n"
     "    storage.read (arrayEntrySlot (Nat.toB256 (index + 1))) = "
     "targetAt entries index",
     "  arrayWords : ∀ index, index < entries.length → True",
     "changed in"),
    ("vocabulary: a RegistryWitness field gutted AND its digest re-taken",
     "vocabulary-channels",
     "Blanc/LidoCircuitBreakerRegistryModel.lean",
     "  arrayWords : ∀ index, index < entries.length →\n"
     "    storage.read (arrayEntrySlot (Nat.toB256 (index + 1))) = "
     "targetAt entries index",
     "  arrayWords : ∀ index, index < entries.length → True",
     "no longer mentions"),
    # Proves the per-field split above is load-bearing: `targetsValid` shares
    # `nonzeroCanonicalAddress` with `pausersValid`, so a single shared token
    # would leave this gutting undetected once the digest was re-taken.
    ("vocabulary: a second RegistryWitness field gutted, digest re-taken",
     "vocabulary-channels",
     "Blanc/LidoCircuitBreakerRegistryModel.lean",
     "  targetsValid : ∀ entry ∈ entries, nonzeroCanonicalAddress entry.1",
     "  targetsValid : ∀ entry ∈ entries, True",
     "no longer mentions"),
    ("vocabulary: valid-chain reachability restricted to empty blocks",
     "vocabulary", "Blanc/Ladder.lean",
     "      ReachUsing cfg ch ch' →\n"
     "      sum ch'.state.bal + wdsum block.wds < 2 ^ 256 →",
     "      ReachUsing cfg ch ch' →\n"
     "      block.txs = [] →\n"
     "      sum ch'.state.bal + wdsum block.wds < 2 ^ 256 →",
     "changed in"),
    ("vocabulary: a pinned premise definition renamed away", "vocabulary",
     "Blanc/Ladder.lean",
     "def Preserves (c : ContractSpec) (ca : Adr) : Prop :=",
     "def PreservesRenamed (c : ContractSpec) (ca : Adr) : Prop :=",
     "is absent from"),
)


def declarations_map(source: str) -> dict:
    return {key_of(declaration): declaration
            for declaration in declarations(source)}


def self_test(root: Path) -> int:
    sources = load_owners(root)
    program = read_source(root, PROGRAM_SOURCE)
    endpoints_found = declarations_map(sources["endpoints"])

    def run(kind: str, key: str, mutated: str):
        if kind == "pin":
            pin_declarations(key, mutated)
        elif kind == "channels":
            semantic_channels(key, declarations_map(mutated))
        elif kind == "world":
            open_world_bar(key, declarations_map(mutated))
        elif kind == "coverage":
            if key == "program":
                coverage(mutated, endpoints_found)
            else:
                coverage(program, declarations_map(mutated))
        elif kind == "trust":
            copy = dict(sources)
            copy[key] = mutated
            trust_scan(copy)
        elif kind == "variable":
            pin_imports_and_variables(key, mutated)
        elif kind in ("vocabulary", "vocabulary-channels"):
            found = vocabulary_map(mutated)
            names = VOCABULARY_NAMES[key]
            for name in names:
                if name not in found:
                    fail(f"vocabulary declaration {name} is absent from "
                         f"{key} -- renamed, moved or deleted")
                if kind == "vocabulary":
                    if digest(found[name]["text"]) != \
                            VOCABULARY_PINS[key][name]:
                        fail(f"vocabulary declaration {name} changed in {key}")
            for name, tokens in VOCABULARY_CHANNELS.items():
                if name not in found:
                    continue
                text = normalize(found[name]["text"])
                for token in tokens:
                    if normalize(token) not in text:
                        fail(f"vocabulary declaration {name} no longer "
                             f"mentions {token!r}")
        else:
            fail(f"unknown self-test kind {kind}")

    problems = []
    for label, kind, key, old, new, expected in SELF_TESTS:
        if kind in ("vocabulary", "vocabulary-channels"):
            base = read_source(root, key)
        elif key == "program":
            base = program
        else:
            base = sources[key]
        if old not in base:
            problems.append(f"{label}: the mutation no longer applies; this "
                            "self-test has gone stale and is proving nothing")
            continue
        mutated = base.replace(old, new, 1)
        try:
            run(kind, key, mutated)
        except Failure as exc:
            message = str(exc)
            if expected not in message:
                problems.append(
                    f"{label}: rejected by the wrong check -- expected a "
                    f"message mentioning {expected!r}, got: "
                    f"{message.splitlines()[0]}")
            else:
                print(f"  rejected  [{kind:9s}] {label}")
            continue
        problems.append(f"{label}: ACCEPTED by the {kind} check")
    print()
    for problem in problems:
        print("SELF-TEST — " + problem)
    if problems:
        print(f"REGRESSION — {VERDICT} self-test: {len(problems)} of "
              f"{len(SELF_TESTS)} falsifiers not rejected as designed")
        return 1
    print(f"OK — {VERDICT} self-test: {len(SELF_TESTS)} falsifiers rejected, "
          "each by the check it was written for")
    return 0


# --------------------------------------------------------------------------
# Digest emission (review aid, never a rebase)
# --------------------------------------------------------------------------

def chain_source(root: Path) -> str:
    """The Chain owner's text.

    While the owner is dormant this reads the pinned revision out of git
    history rather than the working file, which another worker is editing.
    """
    if CHAIN.active:
        return read_source(root, CHAIN.path)
    run = subprocess.run(
        ["git", "show", f"{CHAIN.pinned_at()}:{CHAIN.path}"],
        cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if run.returncode:
        fail(f"cannot read {CHAIN.path} at {CHAIN.pinned_at()}: {run.stderr}")
    return run.stdout


def observed_pins(root: Path, include_chain: bool = True) -> dict:
    """Every pin the given tree implies. Used by the review aid, and by the
    mutation campaign to simulate an author who re-took every digest."""
    sources = {key: read_source(root, relative)
               for key, relative in OWNERS.items()}
    relatives = dict(OWNERS)
    if include_chain:
        sources[CHAIN.key] = chain_source(root)
        relatives[CHAIN.key] = CHAIN.path
    headers, bodies, imports, variables, comment_rows = {}, {}, {}, {}, set()
    for key, source in sources.items():
        headers[key], bodies[key] = {}, {}
        for declaration in declarations(source):
            name = key_of(declaration)
            if declaration["kind"] in ("theorem", "lemma"):
                headers[key][name] = digest(statement_of(declaration))
            else:
                bodies[key][name] = digest(declaration["text"])
        code = strip_comments(source)
        imports[key] = tuple(normalize(line) for line in code.split("\n")
                             if line.startswith("import "))
        variables[key] = tuple(normalize(line) for line in code.split("\n")
                               if re.match(r"^variable\b", line))
        comment_rows |= scan_rows(relatives[key], comment_text(source))
    entries = dispatcher_inventory(read_source(root, PROGRAM_SOURCE))
    vocabulary = {}
    for relative, wanted in VOCABULARY_NAMES.items():
        found = vocabulary_map(read_source(root, relative))
        vocabulary[relative] = {
            name: digest(found[name]["text"])
            for name in sorted(wanted) if name in found}
    return {
        "HEADER_PINS": headers,
        "VOCABULARY_PINS": vocabulary,
        "DEFINITION_PINS": bodies,
        "IMPORT_PINS": {key: tuple(value) for key, value in imports.items()},
        "VARIABLE_PINS": {key: tuple(value)
                          for key, value in variables.items()},
        "DISPATCHER_PIN": dispatcher_digest(entries),
        "COMMENT_TRUST_ROWS": tuple(sorted(comment_rows)),
        "entries": entries,
    }


def print_observed_digests(root: Path) -> int:
    print("# Observed digests. These are a REVIEW AID, not a rebase: pasting")
    print("# them without reading the diff converts this gate into a record")
    print("# of whatever the tree currently says.")
    pins = observed_pins(root)
    headers = pins["HEADER_PINS"]
    bodies = pins["DEFINITION_PINS"]
    imports = pins["IMPORT_PINS"]
    variables = pins["VARIABLE_PINS"]
    comment_rows = pins["COMMENT_TRUST_ROWS"]
    entries = pins["entries"]
    blocks = [
        ("HEADER PINS", "HEADER_PINS = " + json.dumps(headers, indent=4,
                                                      ensure_ascii=False,
                                                      sort_keys=True)),
        ("DEFINITION PINS", "DEFINITION_PINS = " + json.dumps(
            bodies, indent=4, ensure_ascii=False, sort_keys=True)),
        ("IMPORT PINS", "IMPORT_PINS = " + repr(dict(sorted(imports.items())))),
        ("VARIABLE PINS",
         "VARIABLE_PINS = " + repr(dict(sorted(variables.items())))),
        ("DISPATCHER PIN",
         "DISPATCHER_PIN = " + repr(dispatcher_digest(entries))),
        ("COMMENT TRUST ROWS",
         "COMMENT_TRUST_ROWS = " + repr(tuple(sorted(comment_rows)))),
        ("VOCABULARY PINS", "VOCABULARY_PINS = " + json.dumps(
            pins["VOCABULARY_PINS"], indent=4, ensure_ascii=False,
            sort_keys=True)),
    ]
    for label, block in blocks:
        print(f"\n# >>> {label} >>>\n{block}\n# <<< {label} <<<")
    print(f"\n# dispatcher: {len(entries)} entries: "
          f"{[entry['head'] for entry in entries]}")
    return 0


def chain_dry_run(root: Path) -> int:
    """The Chain owner's pins, channels and open-world bar, on their own.

    While the owner was DORMANT this read the frozen revision named by
    `pinned_at`, never the working file, and deliberately skipped the trust
    scan: the committed revision still carried the `sorry` that was the reason
    for dormancy, and pretending otherwise would have been the one thing this
    gate must never do.

    The owner is now ACTIVE, so this reads the working file at the branch tip
    and the trust scan is reported rather than skipped -- a dry run that talks
    about bytes which no longer exist is worse than no dry run.  The mode is
    kept because it isolates this owner's static nets from the other two, and
    because a future in-flight successor will want it back.
    """
    source = chain_source(root)
    found = pin_declarations(CHAIN.key, source)
    semantic_channels(CHAIN.key, found)
    pin_imports_and_variables(CHAIN.key, source)
    binders = open_world_bar(CHAIN.key, found)
    missing = [name for name in CHAIN.required_public if name not in found]
    if missing:
        fail(f"{CHAIN.key}: required public statements absent at "
             f"{CHAIN.pinned_at()}: {missing}")
    code_rows = scan_rows(CHAIN.path, strip_comments(source))
    if CHAIN.active and code_rows:
        fail("trust token in CODE (not in a comment):\n        " +
             "\n        ".join(sorted(code_rows)))
    trust = ("trust scan clean in code" if CHAIN.active else
             "trust scan NOT run (the committed revision still carries "
             f"{sorted(row.split()[0] for row in code_rows)}, which is why "
             "CHAIN.active is False)")
    where = ("the working file at branch tip" if CHAIN.active
             else "the frozen revision")
    print(f"OK — {VERDICT} chain dry run at {CHAIN.pinned_at()} "
          f"({where}): {len(found)} declarations all pinned, "
          f"{len(CHAIN.required_public)} required public statements present, "
          f"{binders} binders past the open-world allowlist; {trust}")
    return 0


def print_inventory(root: Path) -> int:
    result = run_static_checks(root)
    for entry in result["entries"]:
        role = ("Registry-mutating" if entry["head"] in result["mutating"]
                else "discharged")
        print(f"  {entry['selector']:24s} [{entry['args']:19s}] "
              f"{entry['head']:22s} {role}")
    print(f"  -- {len(result['program'])} dispatch entries, "
          f"{len(result['discharged'])} discharged, "
          f"{len(result['mutating'])} Registry-mutating")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--list", action="store_true",
                        help="print the derived dispatcher inventory")
    parser.add_argument("--self-test", action="store_true",
                        help="run this gate's own falsifiers (no Lean)")
    parser.add_argument("--mutations", action="store_true",
                        help="run the semantic mutation campaign; requires "
                             "--worktree")
    parser.add_argument("--mutations-dry-run", action="store_true",
                        help="check that every mutation patch still applies; "
                             "builds and judges nothing")
    parser.add_argument("--worktree", type=Path,
                        help="isolated worktree for --mutations")
    parser.add_argument("--print-observed-digests", action="store_true",
                        help="print the pin tables the current tree implies")
    parser.add_argument("--static-only", action="store_true",
                        help="skip the Lean axiom probe")
    parser.add_argument("--chain-dry-run", action="store_true",
                        help="check the dormant Chain owner's pins, channels "
                             "and open-world bar against its pinned committed "
                             "revision, without reading the working file")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        if args.print_observed_digests:
            return print_observed_digests(root)
        if args.chain_dry_run:
            return chain_dry_run(root)
        if args.self_test:
            return self_test(root)
        if args.mutations_dry_run:
            return mutations_dry_run(root)
        if args.mutations:
            if args.worktree is None:
                print(f"REGRESSION — {VERDICT}: --mutations needs --worktree "
                      "pointing at an isolated worktree with a cloned .lake; "
                      "the campaign rebuilds mutated modules and must never "
                      "run in the shared tree")
                return 2
            return run_mutations(args.worktree.resolve())
        if args.list:
            return print_inventory(root)
        result = run_static_checks(root)
        probed = 0 if args.static_only else axiom_checks(root, load_owners(root))
    except Failure as exc:
        print(f"REGRESSION — {VERDICT}: {exc}")
        return 1
    pending = "" if CHAIN.active else (
        f"; {len(HEADER_PINS.get(CHAIN.key, {}))} {CHAIN.key} pins recorded "
        f"and PENDING on {CHAIN.path} (CHAIN.active = False)")
    print(
        f"OK — {VERDICT}: {result['pins']} exact pins across "
        f"{len(active_owners())} owners, every declaration pinned as a "
        f"statement or as a body; {result['binders']} binders past the "
        f"open-world allowlist with no target-code, non-reentrancy, "
        f"direct-call, target-honesty, entry-list-identification or "
        f"PauseSuccessNoninterference premise admitted; the invariant, the "
        f"spec, the stable checkpoint and both assembly disciplines held to "
        f"their semantic channels; {result['vocabulary']} premise-vocabulary "
        f"declarations pinned across {len(VOCABULARY_NAMES)} files this "
        f"family is written in but does not own; "
        f"{len(result['program'])} dispatch entries "
        f"derived from `funcs` and matched in program order against "
        f"{len(result['discharged'])} discharged endpoints plus "
        f"{len(result['mutating'])} Registry-mutating obligations "
        f"({', '.join(result['mutating'])}); trust scan clean in code with "
        f"{len(COMMENT_TRUST_ROWS)} reviewed comment mention(s); "
        + (f"{probed} public theorems each probed for exactly "
           f"{sorted(STANDARD_AXIOMS)}" if probed else
           "axiom probe SKIPPED (--static-only)")
        + pending)
    return 0


if __name__ == "__main__":
    sys.exit(main())
