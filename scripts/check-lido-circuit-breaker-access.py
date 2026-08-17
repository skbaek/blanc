#!/usr/bin/env python3
"""Fail-closed local assurance for access/temporal-authority S5 controls.

It owns the gate fixture, exact public-role headers, trust/deletion/mutation
controls, and exact axiom expectations for the landed S5 theorem family: the
AT4 structural twenty-site classifier, the AT2 temporal views, the AT3
interval/heartbeat transitions, AT5 raw all-frame write authority, and the AT6
owner-closure/retained-last-writer settlement bridge.
"""
from __future__ import annotations

import re
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The six proof owners of this family.  `sites` classifies, `access` states the
# temporal views and transitions, `authority` attributes a raw same-frame
# write, `ownerClosure` bridges to committed frames, `retained` settles, and
# `deploy` owns the disjoint constructor effect domain.
OWNERS = {
    "sites": ROOT / "Blanc/LidoCircuitBreakerSites.lean",
    "access": ROOT / "Blanc/LidoCircuitBreakerAccess.lean",
    "authority": ROOT / "Blanc/LidoCircuitBreakerAuthority.lean",
    "ownerClosure": ROOT / "Blanc/LidoCircuitBreakerOwnerClosure.lean",
    "retained": ROOT / "Blanc/LidoCircuitBreakerRetainedAuthority.lean",
    "deploy": ROOT / "Blanc/LidoCircuitBreakerDeploy.lean",
}
# AT7 registration transitions are still being proved.  The module is inside
# the trust scan from the first day it exists, but none of its headers are
# pinned yet; see AT7_ROLES below.
TEMPORAL_TRANSITIONS = ROOT / "Blanc/LidoCircuitBreakerTemporalTransitions.lean"
FIXTURE = ROOT / "scripts/LidoCircuitBreakerAccessControls.lean"

# Lean module names, used by the compiled-owner guard and the axiom probe.
MODULES = {
    "sites": "Blanc.LidoCircuitBreakerSites",
    "access": "Blanc.LidoCircuitBreakerAccess",
    "authority": "Blanc.LidoCircuitBreakerAuthority",
    "ownerClosure": "Blanc.LidoCircuitBreakerOwnerClosure",
    "retained": "Blanc.LidoCircuitBreakerRetainedAuthority",
    "deploy": "Blanc.LidoCircuitBreakerDeploy",
}

REQUIRED = (
    # AT2 temporal-view boundary controls.
    "expiry_boundary_strict_control",
    "expiry_boundary_inclusive_rejected",
    "canonical_expiry_view_control",
    "heartbeat_interval_view_control",
    # AT3 transition controls.
    "checked_extension_strict_control",
    "settled_error_restores_owner_control",
    # AT4 classifier controls.
    "twenty_site_inventory_control",
    "site_row_relabel_rejected",
    "three_domain_separation_control",
    "constructor_domain_separate_control",
    # AT5 raw-authority controls.
    "permitted_role_widening_rejected",
    "raw_occurrence_commitment_premise_rejected",
    "guard_after_write_rejected",
    # AT6 closure/settlement controls.
    "owner_closure_assumed_premise_rejected",
    "first_writer_substitution_rejected",
    "storage_owner_identity_required_control",
    "code_address_identity_required_control",
    "noncommitting_root_has_no_authority_control",
)
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|opaque|native_decide|implemented_by)\b")

# Exact SHA-256 of each pinned public header, normalized by `normalized_header`.
# A header is pinned when a reviewer would have to re-read the proof if its
# statement moved: premises, quantifier altitude, and conclusion.
ROLES = {
    # ---- AT4: structural twenty-site classifier and per-site role domain ----
    "sites": {
        # Exact row cardinality of the typed inventory.
        "RuntimePersistentWrite.all_length":
            "7d4cd3c7c03cd46bdc7fd16b39c64c4f23a3cc813282c81a6a7cdaff16111ef3",
        # Semantic label order is aligned with the frozen literal inventory:
        # this is the row-relabelling pin.
        "RuntimePersistentWrite.inventory_exact":
            "7370ae545385f0d0cbf8d671fec120f52c6582a6b91dafab5994887704015c41",
        # A looked-up row can only name an actual structural runtime SSTORE.
        "RuntimePersistentWrite.sourceSite?_sound":
            "cff8ce690c1d300ce608e20e5303eaf6404079e433a75a7266a720e12b0c4ca1",
        # Rows and structural sites are the same finite domain, not merely
        # equinumerous lists.
        "RuntimePersistentWrite.sourceSites_exact":
            "adf339524782b1c35b6c4a39310ac803a40b5126385a92a5faa73039e2ba5509",
        # Uniqueness: two typed rows cannot name the same source site.
        "RuntimePersistentWrite.sourceSite?_injective":
            "31f28be5bbbb623bacc8b24e91643c0bda6ebf86caeb7c2d66ecbd15fe16fed2",
        # Every row decodes to SSTORE in any certified compilation.
        "RuntimePersistentWrite.sourceSite?_compiledAt":
            "3cdef4d0ecf0a43356bb39a6ae977ec8a80d3acb9d6a5e7b35d76d1f38a6c9e5",
        # Exact three-domain PC inventory of the official parameterization.
        "runtimeSourceEffectPcs_official":
            "9c722708eff3d261fcf253a4305910900a7725610139ad0d3b0ccbc4576ff3cb",
        # Exact compiled PCs of the twenty structural SSTORE sites.
        "runtimePersistentSourceSites_pcs":
            "49ee1e94b82a772e9d9dc5755d944c2212192d992c1e7c9d09f1dc4c724e6ccc",
        "runtimePersistentSourceSites_length":
            "70883bef0d27c945c102910df78392ef1fc4c5c82967f508cfe71b58e28b1572",
        "runtimePersistentSourceSites_nodup":
            "4817fab718855c25cf6626361e0b5dd1c621cf453699dbe7c597cca4ccf53aed",
        # Inverse coverage in both directions.
        "runtimePersistentSourceSite_iff_row":
            "8c37ef62bfe7951aa1de4bc4a60e9b6d39f09dda52d01154875392160516decc",
        # Classifier soundness and completeness against the row domain.
        "classifyRuntimePersistentWrite_sound":
            "3cb9356f31aa0b67e6bb40a45fdd46785a04f6df043c13eddb2f9b1a2c0f6b08",
        "classifyRuntimePersistentWrite_complete":
            "cc3a0ced6083db2a6fea70eb3b53b6341686694531f950a01f9e6cca520ebf66",
        # Transient and external-call domains, pinned by exact PC.
        "runtimeTransientSourceSites_pcs":
            "616fd72949f7ff3fb030a055dde74171ad80370492b848fe9451f9099c23f0f1",
        "runtimeExternalCallSourceSites_pcs":
            "5fe29bd85d1092b9ce8ab9f418f01522dfce2c921830c0ee411224d185c47253",
        # The two structural external edges are exactly CALL/STATICCALL.
        "runtimeExternalCallSourceSite_instruction_exact":
            "6514ff9a4a6584f0519a61da213ca9a20a55e3714e898a51a8830e390cb24723",
        # Executable-boundary version of the same fact: PUSH payload bytes that
        # look like opcodes are excluded by the `ParentPrefix` premise.
        "runtimeExec_instruction_exact":
            "85ccc6c8341720c8d16d6e325abc6a25e4fdbc049af9cfd0b3c149b652f42a62",
        # The three effect domains are pairwise disjoint.
        "runtimePersistent_effectDomains_separate":
            "bde74c901f9474287ea8116262a5c275319a938e79dd1bc7f7128d8bebdf2bc7",
    },
    # ---- AT2 temporal views and AT3 interval/heartbeat transitions ----
    "access": {
        # Liveness is strict at its own boundary.
        "IsPauserLiveAt.irrefl":
            "f40bc0eb76f7106f80c55a4c6b4affaa1903934056dfb888501924271c7d784c",
        # Exact public dispatch representative at the strict expiry boundary:
        # `timestamp = expiry` reads false.
        "isPauserLive_runCompiled_at_expiry":
            "8208f7812acc094b6b61014447bfde53101c2c3b6f844c2c8482b4ff9dd2b215",
        # Exact direct public execution for an arbitrary stored expiry.
        "isPauserLive_runCompiled":
            "8059dc66dfb56b630a00af0c8e4ed0f74e8632316334bb386c184f07fc5e71d2",
        # Strict-live corollary (returns one).
        "isPauserLive_runCompiled_of_live":
            "cb64d9c77a1128dbf79fae336cc37474c45ffec745f5f4337de9f7d383fa92ba",
        # Strictly-later corollary (returns zero).
        "isPauserLive_runCompiled_of_later":
            "b2575351c1c5348cf706e8197f3260362571b962b87d7e601f3c40c889e3f281",
        # Canonical configuration and expiry views.
        "heartbeatInterval_runCompiled":
            "707a5a835dac676344a6d57cf98981f4a526827c5758eea7efb5bc4c98a50b88",
        "heartbeatExpiry_runCompiled":
            "74eeb9b79e1f45b7f5b1fd52419a2dd4b2247659f2daf59ae75484f793d16526",
        # Configuration/expiry key separation used by the setter transition.
        "expirySlot_ne_heartbeatIntervalSlot":
            "2e2f697c43d7bbfcb11e9d35fec84a9d25aec7cdb3c37584b5f03e6a85a216c8",
        # Checked heartbeat extension is strictly increasing and exact.
        "CheckedHeartbeatExtension.strict_of_interval_pos":
            "12f2f0fb2d8bb619fbcfba0cb6561b2369eecc24fc105ff7534aa88b43dcccbe",
        "CheckedHeartbeatExtension.add_eq":
            "17c41f6ee3cddd262e039503e707b03beffb4b4e2e87b47283708688b413fd4c",
        # Admin necessity and the inclusive bound as a success requirement.
        "setHeartbeatInterval_runCompiledTo_success_requires_admin_and_inclusive":
            "8305c396a90f8370dfe3d729562b365d2c22f0cae38ec4ef454e6719db5445e9",
        "setHeartbeatInterval_runCompiledTo_error_of_not_admin":
            "4f888541658dc5f620da17968c55f68b3e5f37b75170ae8b1e6ff72cf0e29289",
        "setHeartbeatInterval_success_settled_effects":
            "d90aa89857c20d4fb9e3a986bd63336eb0bcde4fac0b8bd17b1bee313cbee4ed",
        "setHeartbeatInterval_settled_error_restores_owner":
            "14f02920900d8dfc5c484da2f3de4f47a2a7726d6dd9a358533d5edf3deeff37",
        # Heartbeat success arm and its three source-ordered failure arms.
        "heartbeat_runCompiledTo_of_checkedExtension":
            "b78969ae27a4200bde7c90312bd4b5bcbf462395377c71183ae9dd97dcc5785e",
        "heartbeat_runCompiledTo_error_of_count_zero":
            "8e867bf6b32dcb0306fc92e46287bf0f5803729f87542ab8140ce241700e85c9",
        "heartbeat_runCompiledTo_error_of_expired":
            "0eaeda9d9e940760b003605ddea5b7fc44315d477d876fff704d12597b190ce2",
        "heartbeat_runCompiledTo_error_of_add_wrap":
            "8f55801187b898ede05b35a66eb7e87ee1d5ef9aa2959c12fe07474634434403",
        "heartbeat_success_settled_effects":
            "468003beedf81569a4c5456967a6fa875e8358159f7f16224d3860e96fa04c78",
        "heartbeat_settled_error_restores_owner":
            "eaba8350289f67a716a5960880ba8a6a4ba3d056d7c8583b3f07ff514dac12c8",
    },
    # ---- AT5: raw all-frame authority (no success/commitment premise) ----
    "authority": {
        # Every same-frame runtime SSTORE in an exact selected raw invocation
        # has exactly one source row.
        "Exec.NinstOccurrence.runtimePersistentWrite_of_rawFrameRoot":
            "c73d59eb2e4a9975569a304e2b6362cdd95a5669ec866aec459681a1c9462e4f",
        # ... and one of that row's actual permitted runtime authority roles,
        # for an enclosing invocation of any terminal outcome.
        "Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot":
            "e755bf90f38ef62672e6dd79df675b41027cf702678c8bf73882bced5d546bb2",
        # Settlement-altitude storage bridge; deliberately not a log claim.
        "ProcessMessage.runtimeOwnerStorage_eq_committedPost":
            "cd2eeef907ec3f7af5ec7baac493cc3f8310d72c14d9f3926af36e2fc9c7a586",
    },
    # ---- AT6: owner-closure bridge ----
    "ownerClosure": {
        "Exec.coreRuntimeOwnerClosed":
            "36f6c39e0a3c3b6b15eeb365177244b95e6ac40375ed94bd8575873dde88664a",
        # Public committed-frame closure for a global execution.
        "Exec.runtimeOwnerClosure":
            "d480130bb42bb2983d217135981d42fccec22274c5b361d1765470f604d018f1",
        # Retained owner write => committed exact frame with a same-frame
        # prefix.  No chosen-writer identity premise.
        "Exec.retainedSstore_runtimeOwnerClosure":
            "d20dc486e06b4c3e2cf126db9bf69c41d743ad525a789dfaff7061cd7704335b",
    },
    # ---- AT6: retained last writer and settlement ----
    "retained": {
        "Exec.runtimeOwnerCellAuthority_of_committedPost_ne":
            "b8bf33d562eb4bc032c42c35b4923d86308f7825d20f77bf6fa47d2603824def",
        "ProcessMessage.runtimeOwnerCellAuthority_of_clean_settled_ne":
            "c7029557823b890b66aa3b9ae0fca0843cfe2a7ed82b7a8f3408db103290dcb3",
        "ProcessMessage.runtime_settled_error_restores_owner":
            "957cd337dc365f28fe56bb835e6dca42d3e9be20f70e5ced21d5235c4a867ce5",
        # The three noncommitting negatives that keep the family honest.
        "Exec.no_committedFrame_of_not_commits":
            "128b8cc756ff9839426dbd301cc2871bd807ca1b91fcd02d3fe1322c64aba544",
        "Exec.no_retainedOwnerSstore_of_not_commits":
            "ad344bf0a6b420483880699de2285e7641c255e2ef31ef1a0193f4fd26313dca",
        "Exec.no_runtimeOwnerCellAuthority_of_not_commits":
            "2131d148eaa357898a5b0858a673361e2c1d75c2f069167b48d0ecf878f22437",
    },
    # ---- Constructor effect domain, disjoint from the runtime source map ----
    "deploy": {
        # The 2/0/0 constructor separation result.
        "constructor_program_site_counts_exact":
            "00eb29cd2261371383664d8b8d65efef355d1f4d8ed5826f2ff68648ad66d937",
        "constructor_inventory_cardinalities":
            "6afbd83f5e15d39d0f5510085468508c4e43cc81ff277dcaabd869cda2578f69",
    },
}

# AT7 registration transitions (`Blanc/LidoCircuitBreakerTemporalTransitions.lean`)
# are still being proved.  The module is trust-scanned above but no header is
# pinned yet.  The lead fills this in when the registration partitions land
# (fresh/nonzero, absent/zero, found-zero-retained) and folds it into ROLES.
AT7_ROLES: dict = {}

EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def fail(message: str) -> None:
    raise SystemExit(f"REGRESSION — S5 access assurance: {message}")

def text(path: Path) -> str:
    if not path.is_file():
        fail(f"missing required file {path.relative_to(ROOT)}")
    return path.read_text()

def require_controls(source: str) -> None:
    for name in REQUIRED:
        if not re.search(rf"(?m)^theorem\s+{re.escape(name)}\b", source):
            fail(f"missing positive/deletion control {name}")
    for token in ("RuntimeWriteAuthority", "RuntimeOwnerCellAuthority",
                  "RuntimePersistentWrite.permittedRoles",
                  "runtimePersistentSourceSites", "classifyRuntimePersistentWrite",
                  "IsPauserLiveAt", "CheckedHeartbeatExtension",
                  "Exec.rawFrameRoots", "Exec.committedFrames",
                  "exactInvocation", "expirySlot", "heartbeatIntervalSlot"):
        if token not in source:
            fail(f"fixture no longer owns required semantic channel {token}")

def no_trust_shortcut(path: Path) -> None:
    match = FORBIDDEN.search(text(path))
    if match:
        fail(f"forbidden trust token {match.group(1)!r} in {path.relative_to(ROOT)}")

_DECL_START = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|example|class)\b")


def declaration_slice(source: str, name: str) -> str:
    """Exact source text of one declaration, never crossing into the next.

    The earlier `.*?:= by` form silently ran past a term-mode declaration and
    digested a blend of two theorems, so a pin could name one result and hash
    another.  Slicing first makes that impossible.
    """
    start = re.search(rf"(?m)^theorem\s+{re.escape(name)}\b", source)
    if not start:
        fail(f"missing pinned public role {name}")
    rest = source[start.end():]
    following = _DECL_START.search(rest)
    end = start.end() + (following.start() if following else len(rest))
    return source[start.start():end]


def normalized_header(name: str, source: str) -> str:
    declaration = declaration_slice(source, name)
    tactic = re.search(r"(?s)^.*?:(?==\s*by\b)", declaration)
    if tactic:
        header = tactic.group(0)
    else:
        depth = 0
        cut = -1
        for index, char in enumerate(declaration):
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth -= 1
            elif char == ":" and depth == 0 and declaration[index:index + 2] == ":=":
                cut = index
        if cut < 0:
            fail(f"pinned public role {name} has no definition marker")
        header = declaration[:cut + 1]
    return " ".join(header.split())


def pin_role_headers(key: str, source: str) -> None:
    for name, expected in ROLES[key].items():
        actual = hashlib.sha256(normalized_header(name, source).encode()).hexdigest()
        if actual != expected:
            fail(f"normalized public header changed for {name} in {key}")

def deletion_control(source: str) -> None:
    # Mutate a required declaration name in a temporary copy: the parser must
    # reject it before any compiler result can make the gate vacuous.
    with tempfile.TemporaryDirectory() as td:
        mutant = Path(td) / "controls.lean"
        mutant.write_text(
            source.replace("twenty_site_inventory_control", "removed_control", 1))
        mutated = mutant.read_text()
        if re.search(r"(?m)^theorem\s+twenty_site_inventory_control\b", mutated):
            fail("deletion-control mutation did not apply")
        try:
            require_controls(mutated)
        except SystemExit:
            return
        fail("required-control deletion was accepted")

# Every entry changes theorem-level semantics inside a protected public role.
# The trailing comment on each label names the AT8 requirement it discharges.
MUTATIONS = {
    "sites": {
        # AT8: the twenty structural SSTORE sites are pinned by exact PC, so a
        # relabelled site row cannot pass as the same classifier.
        "structural site row relabelled": (
            "413, 1333, 1745", "413, 1333, 1746",
        ),
        # AT8: row/site coverage is an equivalence, not a one-way inclusion —
        # dropping the reverse direction would permit unaccounted rows.
        "inverse row coverage weakened to one direction": (
            "runtimePersistentSourceSites dp ↔\n"
            "      ∃ row ∈ RuntimePersistentWrite.all,",
            "runtimePersistentSourceSites dp →\n"
            "      ∃ row ∈ RuntimePersistentWrite.all,",
        ),
        # AT8: source ownership is unique at row identity, not merely at the
        # numeric index that indexes into the site list.
        "row uniqueness weakened to index equality": (
            "    left = right := by", "    left.index = right.index := by",
        ),
        # AT8: a permitted effect domain may not be widened — the persistent
        # domain must stay disjoint from BOTH other structural domains.
        "effect-domain separation widened for external calls": (
            "    site ∉ runtimeTransientSourceSites dp ∧\n"
            "      site ∉ runtimeExternalCallSourceSites dp := by",
            "    site ∉ runtimeTransientSourceSites dp := by",
        ),
        # AT8: the frozen literal inventory fixes each row's label; a
        # relabelled inventory row must not survive.
        "frozen inventory label order relabelled": (
            "RuntimePersistentWrite.inventoryOrder.map\n"
            "        RuntimePersistentWrite.inventoryEntry =\n"
            "      persistentWriteInventory",
            "RuntimePersistentWrite.inventoryOrder.map\n"
            "        RuntimePersistentWrite.inventoryEntry.symm =\n"
            "      persistentWriteInventory",
        ),
    },
    "access": {
        # AT8: liveness is STRICT at the boundary — the success arm may not be
        # relaxed to admit `timestamp = oldExpiry`.
        "strict liveness premise weakened to ≤": (
            "(holdLive : timestamp < oldExpiry)",
            "(holdLive : timestamp ≤ oldExpiry)",
        ),
        # AT8: the same boundary from the failing side — the expired arm must
        # keep covering `oldExpiry = timestamp`.
        "expired arm boundary narrowed to strict": (
            "(hexpired : oldExpiry ≤ timestamp)",
            "(hexpired : oldExpiry < timestamp)",
        ),
        # AT8: the public later-than corollary is the strict complement of
        # liveness; weakening it would double-count the boundary.
        "later-expiry corollary boundary weakened to ≤": (
            "(later : expiry < sevm.benvStat.time)",
            "(later : expiry ≤ sevm.benvStat.time)",
        ),
        # AT8: code-address identity may not be dropped from an exact-instance
        # premise — without it the view claim is not about this deployment.
        "code-address identity dropped from exact-instance premise": (
            "    (_hcodeAddress : sevm.codeAddress = some sevm.currentTarget)\n",
            "",
        ),
        # AT8: storage-owner identity may not be dropped or redirected — a
        # foreign account's storage is not this contract's view.
        "foreign storage owner in exact view premise": (
            "Devm.getStorVal base sevm.currentTarget", "Devm.getStorVal base ca",
        ),
        # AT8: the admin guard is a NECESSARY condition of success; deleting it
        # from the conclusion turns the theorem into a bounds-only claim.
        "admin necessity dropped from the success conclusion": (
            "    sevm.caller.toB256 = dp.admin ∧\n"
            "      dp.minHeartbeatInterval ≤ newInterval ∧",
            "      dp.minHeartbeatInterval ≤ newInterval ∧",
        ),
    },
    "authority": {
        # AT8: a raw-occurrence theorem must NOT acquire a success or
        # commitment premise — that is exactly the altitude it exists to hold.
        "raw-occurrence theorem given a commitment premise": (
            "    (selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)\n"
            "    (invocation : frameRoot.exactInvocation (runtime dp) ca ca)",
            "    (selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)\n"
            "    (committed : Execution.commits globalRoot.exc = true)\n"
            "    (invocation : frameRoot.exactInvocation (runtime dp) ca ca)",
        ),
        # AT8: the exhibited role must lie in THIS row's permitted role set; a
        # widened role set would let any write claim any authority.
        "permitted role set widened to all roles": (
            "role ∈ row.permittedRoles ∧", "role ∈ InvocationRole.all ∧",
        ),
        # AT8: authority evidence (the guard) is anchored at the frame root and
        # precedes the write; re-anchoring it at the write would admit a guard
        # occurring AFTER the store.
        "guard evidence anchored after the write": (
            "          RuntimeWriteAuthority dp frameRoot occurrence.node role := by",
            "          RuntimeWriteAuthority dp occurrence.node frameRoot role := by",
        ),
        # AT8: the settlement storage bridge is about the exact owner account
        # and its committed raw post, not an arbitrary supplied world.
        "settlement bridge given a caller-supplied committed post": (
            "    (committed : Execution.commits out = true) :\n"
            "    Devm.getStor settled ca =",
            "    (committed : Execution.commits out = true)\n"
            "    (supplied : Devm.getStor settled ca = Devm.getStor pre ca) :\n"
            "    Devm.getStor settled ca =",
        ),
    },
    "ownerClosure": {
        # AT8: owner closure must be DERIVED from the installed exact runtime,
        # never assumed by the caller.
        "owner-closure premise replaced by a caller-supplied assumption": (
            "    (rootExact :\n"
            "      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation\n"
            "        (runtime dp) ca ca)\n"
            "    (write : Exec.SuccessfulSstoreOccurrence",
            "    (closure : ∀ frame ∈ Exec.committedFrames run,\n"
            "      frame.exactInvocation (runtime dp) ca ca)\n"
            "    (write : Exec.SuccessfulSstoreOccurrence",
        ),
        # AT8: attribution is to the LAST retained writer; a first-writer
        # premise attributes the surviving word to a superseded store.
        "first writer substituted for last-retained writer": (
            "    (retained : write.Retained)", "    (first : write.FirstInFrame)",
        ),
        # AT8: storage-owner identity may not be dropped from the exact
        # instance — a write owned by another account is not our evidence.
        "storage-owner identity dropped from the closure premise": (
            "    (owner : write.storageOwner = ca) :",
            "    (_owner : True) :",
        ),
    },
    "retained": {
        # AT8: the installed exact-code premise pins WHICH program ran; without
        # it the retained authority claim is about no particular contract.
        "installed code identity dropped from the exact instance": (
            "    (installed : Prog.At (runtime dp) ca pc sevm pre)",
            "    (_installed : True)",
        ),
        # AT8: commitment is derived from the concrete clean settlement, not
        # supplied for the selected writer.
        "clean-settlement premise replaced by a supplied commitment": (
            "    (clean : settled.error.isSome = false)",
            "    (committed : Execution.commits out = true)",
        ),
        # AT8: the noncommitting negative must keep the owner conjunct;
        # dropping it changes which writes the negative rules out.
        "storage-owner identity dropped from the noncommitting negative": (
            "      write.Retained ∧ write.storageOwner = ca := by",
            "      write.Retained := by",
        ),
        # AT8: settled-error restoration covers persistent AND transient
        # storage; narrowing it hides a transient leak.
        "settled-error restoration narrowed to persistent storage": (
            "    Devm.getStor post ca = msg.benv.state.getStor ca ∧\n"
            "      post.transientStorage = msg.tenv.transientStorage := by",
            "    Devm.getStor post ca = msg.benv.state.getStor ca := by",
        ),
    },
    "deploy": {
        # AT8: the constructor's effect domain is exactly 2/0/0 and separate
        # from the runtime's 20/3/2 source map.
        "constructor site counts relabelled": (
            "constructorProgramSiteCounts = (2, 0, 0) := by",
            "constructorProgramSiteCounts = (2, 1, 0) := by",
        ),
    },
}

def header_mutation_controls(sources: dict) -> None:
    for key, mutations in MUTATIONS.items():
        source = sources[key]
        for label, (old, new) in mutations.items():
            mutant = source.replace(old, new)
            if mutant == source:
                fail(f"{key}: {label} mutation did not apply")
            try:
                pin_role_headers(key, mutant)
            except SystemExit:
                continue
            fail(f"{key}: {label} mutation was accepted")

def compile_fixture() -> None:
    for key, module in MODULES.items():
        olean = ROOT / (".lake/build/lib/lean/" + module.replace(".", "/") + ".olean")
        if not olean.is_file():
            fail(f"compiled {key} owner is absent; run the approved elaboration "
                 "checkpoint before this fixture gate")
    run = subprocess.run(
        ["lake", "env", "lean", "scripts/LidoCircuitBreakerAccessControls.lean"],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if run.returncode:
        fail("fixture failed to compile:\n" + run.stdout)

def axiom_checks() -> None:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="access-axioms-", dir=ROOT,
        encoding="utf-8", delete=False,
    ) as handle:
        temporary = Path(handle.name)
        for module in MODULES.values():
            handle.write("import " + module + "\n")
        for names in ROLES.values():
            for name in names:
                handle.write(
                    "#print axioms Blanc.LidoCircuitBreaker." + name + "\n"
                )
    try:
        run = subprocess.run(
            ["lake", "env", "lean", str(temporary.relative_to(ROOT))],
            cwd=ROOT, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    finally:
        temporary.unlink(missing_ok=True)
    if run.returncode:
        fail("axiom probe failed:\n" + run.stdout)
    for names in ROLES.values():
        for name in names:
            qualified = "Blanc.LidoCircuitBreaker." + name
            match = re.search(
                r"'" + re.escape(qualified) +
                r"' depends on axioms: \[([^\]]*)\]",
                run.stdout, re.DOTALL,
            )
            if not match:
                fail(f"{qualified}: unrecognised #print axioms output")
            actual = {
                item.strip() for item in match.group(1).split(",") if item.strip()
            }
            if actual != EXPECTED_AXIOMS:
                fail(
                    f"{qualified}: axioms {sorted(actual)}, "
                    f"expected {sorted(EXPECTED_AXIOMS)}"
                )

def main() -> None:
    # Static owner-side checks run first so the gate fails before any Lean
    # subprocess is started.
    for key, path in OWNERS.items():
        if not path.is_file():
            fail(f"missing sole production owner for {key}")
        no_trust_shortcut(path)
    # AT7 is unpinned but never exempt from the trust scan.
    no_trust_shortcut(TEMPORAL_TRANSITIONS)
    if AT7_ROLES:
        fail("AT7 headers are pinned in AT7_ROLES but not folded into ROLES")
    sources = {key: text(path) for key, path in OWNERS.items()}
    for key, source in sources.items():
        pin_role_headers(key, source)
    header_mutation_controls(sources)
    # Fixture-side static checks.
    fixture = text(FIXTURE)
    no_trust_shortcut(FIXTURE)
    require_controls(fixture)
    deletion_control(fixture)
    # Lean subprocesses last.
    compile_fixture()
    axiom_checks()
    pinned = sum(len(names) for names in ROLES.values())
    controls = sum(len(mutations) for mutations in MUTATIONS.values())
    print(f"OK — S5 access assurance: {len(REQUIRED)} Lean controls; "
          f"{pinned} exact public headers and axiom pins across six owners; "
          "AT4 twenty-site classifier uniqueness/inverse-coverage/exact-PC and "
          "three-domain separation; AT2 strict-liveness boundary, interval and "
          "canonical expiry views; AT3 admin-necessity and checked-extension "
          "transitions; AT5 raw all-frame write authority with permitted roles; "
          "AT6 owner closure, retained last writer, settlement and the "
          "noncommitting negatives; constructor 2/0/0 domain separation; "
          f"{controls} labelled header mutations, deletion and trust controls")

if __name__ == "__main__":
    main()
