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
    # AT7 registration chronologies.  `substrate` holds the walks every leaf
    # composes; the four leaves are siblings and may not import one another.
    "substrate": ROOT / "Blanc/LidoCircuitBreakerRegistrySubstrate.lean",
    "fresh": ROOT / "Blanc/LidoCircuitBreakerFreshRegistration.lean",
    "absent": ROOT / "Blanc/LidoCircuitBreakerAbsentRegistration.lean",
    "unregister": ROOT / "Blanc/LidoCircuitBreakerUnregisterRegistration.lean",
    "replacement": ROOT / "Blanc/LidoCircuitBreakerReplacementRegistration.lean",
    # AT7's pause conditional suffix, and the AT8 attainment family.  Every one
    # of these is now in `Blanc.lean`'s import closure and so is reached by
    # `check-trust-surface.sh` as well; they were not when this block was
    # written, and carrying them here is still what puts their exact headers
    # under a pin and an axiom probe.
    "pauseSuffix": ROOT / "Blanc/LidoCircuitBreakerPauseSuffix.lean",
    "sourceAttainment": ROOT / "Blanc/SourceAttainment.lean",
    "attainment": ROOT / "Blanc/LidoCircuitBreakerAttainment.lean",
    "registrationWorld": ROOT / "Blanc/LidoCircuitBreakerRegistrationWorld.lean",
    "replacementWorld": ROOT / "Blanc/LidoCircuitBreakerReplacementWorld.lean",
    "pauseAttainment": ROOT / "Blanc/LidoCircuitBreakerPauseAttainment.lean",
    "unregisterWorld": ROOT / "Blanc/LidoCircuitBreakerUnregisterWorld.lean",
    "unregisterAttainment":
        ROOT / "Blanc/LidoCircuitBreakerUnregisterAttainment.lean",
    # The pause `.ok` family.  `pauseJoin` states the goal's claims, and the
    # route and world-run modules state the two halves it joins; the remaining
    # four are internal.  `pauseWalk` -> `pauseSuffixWalk` -> `pauseWorldRunKit`
    # -> `pauseWorldRun` is a *linear* chain, so each of those three is consumed
    # by exactly one downstream module whose own public statement is pinned
    # here, and `pauseWorld` is a concrete witness world, not a claim.  They are
    # therefore registered pin-free, on the same footing as `registrationWorld`
    # and `sourceAttainment`: the trust scan, the compiled-owner guard and the
    # axiom probe's import list all reach them.
    "pauseWalk": ROOT / "Blanc/LidoCircuitBreakerPauseWalk.lean",
    "pauseWorld": ROOT / "Blanc/LidoCircuitBreakerPauseWorld.lean",
    "pauseSuffixWalk": ROOT / "Blanc/LidoCircuitBreakerPauseSuffixWalk.lean",
    "pauseWorldRunKit":
        ROOT / "Blanc/LidoCircuitBreakerPauseWorldRunKit.lean",
    "pauseWorldRun": ROOT / "Blanc/LidoCircuitBreakerPauseWorldRun.lean",
    "pauseOkRoute": ROOT / "Blanc/LidoCircuitBreakerPauseOkRoute.lean",
    "pauseJoin": ROOT / "Blanc/LidoCircuitBreakerPauseJoin.lean",
    # The message altitude above `pauseWorldRun`: what a cooperative pause
    # actually leaves behind once the frame settles.
    "pauseSettlement":
        ROOT / "Blanc/LidoCircuitBreakerPauseSettlement.lean",
    # Stage 6's first cut: what the CircuitBreaker has already settled at the
    # moment an arbitrary target receives control.  This is the first owner in
    # the family whose statements quantify over the callee's bytecode, so its
    # pins are what a callee-pinning weakening would have to move.
    "preControl": ROOT / "Blanc/LidoCircuitBreakerPreControl.lean",
    # Stage 6's second cut: what the CircuitBreaker SENDS that target, and the
    # order it sends it in.  Its statements sit downstream of arbitrary callee
    # execution, so what they OMIT -- every storage, code or memory conjunct a
    # cooperative callee would supply -- is as load-bearing as what they carry.
    "callBoundary": ROOT / "Blanc/LidoCircuitBreakerCallBoundary.lean",
    "observation": ROOT / "Blanc/LidoCircuitBreakerObservation.lean",
}
FIXTURE = ROOT / "scripts/LidoCircuitBreakerAccessControls.lean"

# Lean module names, used by the compiled-owner guard and the axiom probe.
MODULES = {
    "sites": "Blanc.LidoCircuitBreakerSites",
    "access": "Blanc.LidoCircuitBreakerAccess",
    "authority": "Blanc.LidoCircuitBreakerAuthority",
    "ownerClosure": "Blanc.LidoCircuitBreakerOwnerClosure",
    "retained": "Blanc.LidoCircuitBreakerRetainedAuthority",
    "deploy": "Blanc.LidoCircuitBreakerDeploy",
    "substrate": "Blanc.LidoCircuitBreakerRegistrySubstrate",
    "fresh": "Blanc.LidoCircuitBreakerFreshRegistration",
    "absent": "Blanc.LidoCircuitBreakerAbsentRegistration",
    "unregister": "Blanc.LidoCircuitBreakerUnregisterRegistration",
    "replacement": "Blanc.LidoCircuitBreakerReplacementRegistration",
    "pauseSuffix": "Blanc.LidoCircuitBreakerPauseSuffix",
    "sourceAttainment": "Blanc.SourceAttainment",
    "attainment": "Blanc.LidoCircuitBreakerAttainment",
    "registrationWorld": "Blanc.LidoCircuitBreakerRegistrationWorld",
    "replacementWorld": "Blanc.LidoCircuitBreakerReplacementWorld",
    "pauseAttainment": "Blanc.LidoCircuitBreakerPauseAttainment",
    "unregisterWorld": "Blanc.LidoCircuitBreakerUnregisterWorld",
    "unregisterAttainment": "Blanc.LidoCircuitBreakerUnregisterAttainment",
    "pauseWalk": "Blanc.LidoCircuitBreakerPauseWalk",
    "pauseWorld": "Blanc.LidoCircuitBreakerPauseWorld",
    "pauseSuffixWalk": "Blanc.LidoCircuitBreakerPauseSuffixWalk",
    "pauseWorldRunKit": "Blanc.LidoCircuitBreakerPauseWorldRunKit",
    "pauseWorldRun": "Blanc.LidoCircuitBreakerPauseWorldRun",
    "pauseOkRoute": "Blanc.LidoCircuitBreakerPauseOkRoute",
    "pauseJoin": "Blanc.LidoCircuitBreakerPauseJoin",
    "pauseSettlement": "Blanc.LidoCircuitBreakerPauseSettlement",
    "preControl": "Blanc.LidoCircuitBreakerPreControl",
    "callBoundary": "Blanc.LidoCircuitBreakerCallBoundary",
    "observation": "Blanc.LidoCircuitBreakerObservation",
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
    # Within-role guard strength, which no header pin can reach: the pause
    # arm's strict entry liveness and its assignment conjunct are extracted
    # from an arbitrary actual authority, so weakening either stops the
    # fixture elaborating.  VERIFIED non-vacuous by mutating the constructor
    # field *and* its construction site together, so the whole library still
    # compiled and only this control failed.
    "pause_within_role_guard_strength_control",
    # `Attainable` is a `def`, so a dropped conjunct would leave every
    # `attainable_*` header byte-identical while making all of them cheaper to
    # prove.  The shape control is the only thing that catches it.
    "attainable_shape_control",
    # The same blind spot one layer up: `PauseExpiryValue` is a `def`, and it
    # carries the whole content of both pause joins' third conjunct.  This
    # control extracts the concrete stored word at each witness world -- `0` at
    # row 19, `2592010` and nonzero at row 18 -- from an ARBITRARY join,
    # through `PauseExpiryValue`'s own laws.  VERIFIED non-vacuous by six
    # single-edit rewrites of the control, each rejected; see its docstring.
    "pause_join_expiry_value_control",
    # One layer up again, and the same blind spot: `ProcessMessage` is a `def`
    # whose whole content the two settlements borrow, so emptying it would
    # leave every pinned header in `pauseSettlement` byte-identical while
    # making both settlements trivially provable.  This control holds
    # `RunFrame`'s content at the call frame universally, and reads each
    # world's surviving expiry word back out THROUGH its `ProcessMessage` --
    # `0` at row 19, `2592010` and nonzero at row 18.  VERIFIED non-vacuous by
    # seven single-edit rewrites of the control, each rejected; see its
    # docstring.
    "pause_settlement_message_content_control",
    # AT8: row 0's executable controls -- the site reached by a real
    # invocation, and its permitted-role set shown exact rather than sound.
    "setPauseDurationConfig_admin_site_control",
    "setPauseDurationConfig_role_tightness_control",
    "setHeartbeatIntervalConfig_admin_site_control",
    "setHeartbeatIntervalConfig_role_tightness_control",
    # The one control that exhibits a `.heartbeatExpiry` authority at all, so
    # `admin_heartbeat_within_role_guard_strength_control`'s heartbeat conjunct
    # is non-vacuous rather than true-because-unreachable.
    "heartbeatExpiry_live_site_control",
    "heartbeatExpiry_role_tightness_control",
    # AT8 asks for *each* admin/heartbeat/pause guard weakening to be rejected;
    # the pause control covers one of the three, this covers the other two.
    "admin_heartbeat_within_role_guard_strength_control",
    "raw_occurrence_commitment_premise_rejected",
    "guard_after_write_rejected",
    # AT6 closure/settlement controls.
    "owner_closure_assumed_premise_rejected",
    "first_writer_substitution_rejected",
    "storage_owner_identity_required_control",
    "code_address_identity_required_control",
    "noncommitting_root_has_no_authority_control",
    # Stage 6 pre-control.  No header pin can reach the quantifier this family
    # exists for: every one of P1-P4 is *stated* over an arbitrary callee, and
    # a weakening that pinned the target's code would leave each header's
    # meaning changed but its shape recognisable.  The control instantiates the
    # family at a universally quantified `code`, carries that same code across
    # the span to the CALL, and joins the halves into the consequence none of
    # them states alone -- so a pinned callee has nothing to discharge it with.
    "pre_control_arbitrary_target_code_control",
    # Stage 6 call boundary.  The same blind spot one cut later, and wider:
    # `PauseCallBoundary` and `PauseStatBoundary` are `def`s, so every clause
    # that says what the CircuitBreaker SENDS -- the argument window's encoder,
    # the callee, the caller, the value, the static flag, the transient storage
    # handed over -- sits where no header pin reaches.  Three weakenings would
    # leave `pauseCall_boundary`, `pauseStat_boundary` and
    # `pause_externalBoundary` byte-identical: substituting the window's own
    # content for the encoder, pinning the callee's bytecode, and adding a
    # cooperative-callee premise on the STATICCALL leg, which sits downstream
    # of arbitrary callee execution.  This control reads each edge's argument
    # window AND its `ProcessMessage` fact out of the RELATIONS -- never from a
    # staging lemma, which would re-establish the encoder behind the relation's
    # back -- spells both encoders out rather than naming `pauseForCalldata` or
    # `isPausedCalldata`, carries the surviving target word across the
    # callback, and says nothing about the code at `target` beyond a
    # universally quantified `ByteArray`.  Reading BOTH calldata clauses is
    # measured, not decorative: a draft that read only `msg.data` survived the
    # window substitution, because the relation pins its calldata twice and the
    # two clauses are independent.  All three weakenings verified rejected with
    # the library rebuilt; see the control's docstring.
    "call_boundary_arbitrary_target_code_control",
    "observation_arbitrary_answer_control",
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
    # ---- AT7: the registration chronologies' public boundary ----
    # The four Registry write chronologies are complete, so their public
    # boundary is pinned here rather than merely trust-scanned.  What is pinned
    # per leaf is the source-trace witness, each `RunCompiledTo` dispatch, and
    # each `success_settled_effects` -- the strongest claim the leaf makes, and
    # the one a weakening would most plausibly hide in.  The substrate pins the
    # walks every leaf composes; the leaves are siblings and cannot import one
    # another, so a walk two of them need lives there.
    #
    # `MUTATIONS` now carries semantic entries for `fresh`, `unregister`,
    # `replacement` and `substrate`, so a clause silently dropped from a
    # chronology's conclusion is rejected and not merely a renamed header.  What
    # a header pin still cannot see is a proof rewritten to a
    # weaker-but-identically-typed statement whose *text* is unchanged; that is
    # what the Lean controls in `scripts/LidoCircuitBreakerAccessControls.lean`
    # exist for, and why a control was needed for the pause guard, whose payload
    # sits inside an inductive's constructor where no header pin reaches.
    "fresh": {
        "freshRegistration_sourceTrace_witness":
            "46aa83f709300ccb03334e27aee03b0fca8b9cbd1c5d3892d9404cb7a23f4657",
        "registerPauser_runCompiledTo_freshNonzero":
            "ee93c3052e9e62df1c5922e9be164c97c6301109db893a497d5d1296f8ef98e0",
        "registerPauser_freshNonzero_success_settled_effects":
            "077a0ecd6b4b32b32b8cd4f908d287bf9076118588300a722073416f95e99e6d",
    },
    "absent": {
        "absentZeroRegistration_sourceTrace_witness":
            "d73d20a0ad2e60eeac554250fb6ca9458afd6d1a5607565a8fc01bd71ec0508a",
        "registerPauser_runCompiledTo_absentZero":
            "ed4ca68e9b95155c3f8de0352cb2cf9fef8475a72aa026fb810de3cf8d180327",
        "registerPauser_absentZero_success_settled_effects":
            "8593869f241db143f0cb0ce6af0a5aa9fc895b669ff561faba5c80f1650a330d",
    },
    "unregister": {
        "foundZeroRetainedRegistration_sourceTrace_witness":
            "9e62f0cdecca971234d4cc239118aecefd58d3072f44f9df2ccc7a8a0c4e1439",
        "registerPauser_runCompiledTo_foundZeroRetainedLast":
            "1517babc34cf57a4397e1ea2b1ca1203760b804325eea455a6f514a7070df9c8",
        "registerPauser_foundZeroRetainedLast_success_settled_effects":
            "164008b806a8dad2af19dc522be8213e869df1bdbfb881a094c7ab0d2003d168",
        "registerPauser_runCompiledTo_foundZeroRetainedSwapPop":
            "9475ec1efded9d6d5a96174ad375d4b4e2423b7a171f37e73171f9b4e1b43ef0",
        "registerPauser_foundZeroRetainedSwapPop_success_settled_effects":
            "b43709356925020af281aae9405cbc1a03a974ffd38aee20e7308ff747791aa8",
        "registerPauser_runCompiledTo_foundZeroOldLast":
            "5b296587c33c08d7885654e4f9446e94a2fd57ac13e73bfcc08679a27f94de1d",
        "registerPauser_foundZeroOldLast_success_settled_effects":
            "1cab442db7419c6c13044e7c3ea15c0259369cb8f6a1f82a34e3716cfd63535a",
        "registerPauser_runCompiledTo_foundZeroOldLastSwapPop":
            "8a7b652f2ac8cd40bd4770baf375a417d806b3ff949affd8ec41905d1faad7c6",
        "registerPauser_foundZeroOldLastSwapPop_success_settled_effects":
            "bcac04940e2eb03de51412de209a4da22f2cb600dd4a4e75afc8b5ca997974b4",
    },
    "replacement": {
        "foundNonzeroReplacement_sourceTrace_witness":
            "39984f11d713ee86af9155e04308c48289e011a3f9718ba707f4d0f6d5032094",
        "registerPauser_runCompiledTo_retainedNonzero":
            "37df45cd0713d59a849980061e9066bd981dd0f7bb777fcdcc96b218f375bb89",
        "registerPauser_retainedNonzero_success_settled_effects":
            "5396bd8cb9b1a8a870a6d1140d703941a3b6023dce600dc817aa03f091b35995",
        "registerPauser_runCompiledTo_oldLastNonzero":
            "79c74357179e41621599b9410872ce4d2aff9b20892b2e20222ba1483bed0231",
        "registerPauser_oldLastNonzero_success_settled_effects":
            "60a9a066c7026f82799dcbd27852be7390f400ad24ac62499b057fc9fc23b674",
    },
    "substrate": {
        "registerPauser_stageArgs_runCompiled":
            "8a710dafebb8b781eeb19ed8ccdf05e0a9517d607112c15cb1d6d0aec0e0b32b",
        "setPauserKernel_foundNonzero_finishSetPauser_runCompiled":
            "0af32ada94fc35c9d271a7ef683a2d5ff95fe3e2d140a9343cc45e08c8e08ded",
        "removeTarget_toFinish_runCompiled":
            "96f7f047283f23c3f6ff7369b697ba8b6e42c169427c2380c08e7ed07eef9073",
        "removeTarget_runCompiled":
            "a8d1d747346cfcb3970e5ecbf8f8b9f96a6418c5cc6e89d6465d106c1fdef706",
        "removeTarget_swapPop_toFinish_runCompiled":
            "caf85d5050af3da4be4a174c0fe8e4c518dfb2b914c0ecada07bd9e140c70018",
        "removeTarget_swapPop_runCompiled":
            "5f8400bca3bb429dda0b2dcaf1c8b80e24e13724e35f7dacb2da415751f5ab1a",
    },
    # ---- AT7 pause suffix and AT8 inhabitation ----
    # `sourceAttainment` and `registrationWorld` are owners for the trust scan
    # and the compiled-owner guard but pin no header: the first is
    # contract-neutral route machinery whose consumers pin what matters, and the
    # second is a concrete world, not a claim.
    "pauseSuffix": {
        "pauseSuccess_expiryWrite_dichotomy":
            "6f110d5b3b181e962b2d85f9bef8a8ea700fd2cc8997db0d0c3e9d194f3fb87f",
        "pauseSuccess_expiryWrite_of_reached":
            "571d0deef20617a570c60a61ef1465cf0663257145dbbfbe52a53817ab2d32be",
        "pauseSuccess_expiryWrite_stores_zero_iff":
            "e02394008e792f65b8f60ab38bbce2e8ee365b3a3f92d5c1a1a7cf2c311cfb1d",
        # The same two results with the function table fixed to the deployed
        # runtime's own, `(runtime dp).main :: (runtime dp).aux`.  Pinned
        # because the whole content of each is that specialization: relax `fs`
        # back to an arbitrary table and the walk is a same-shaped fragment
        # resolved anywhere, which is the finding these close.
        "pauseSuccess_expiryWrite_of_reached_runtime":
            "d728d528cc6de079b108cba8c8ab8cb9902b2e3af69bb41e4e88f2d06b627fbc",
        "pauseSuccess_expiryWrite_stores_zero_iff_runtime":
            "4dee7d19b270f0f7d108af4233d2f9d068a641835b5ccac85f99988f6c7d62cb",
    },
    "attainment": {
        "not_attainable_afterOldNewCount_pauseRegistry":
            "76df5c887a7a8a89b1b17a14dc8f355696c64b744226d1c5fa04457b84c794ef",
        # The two refutations the later per-role site pins made provable.
        # Each is exactly one role/row incompatibility at the source-function
        # level; relax either role's `writeSite` and the proof dies.
        "not_attainable_setPauserAssignment_adminConfiguration":
            "aef338999302856bab253bea316d899c40ee484a1ad4c7bcdf1ea2cb602e5d4e",
        "not_attainable_pauseLastTargetExpiry_heartbeatExpiry":
            "70e694dd8e0b968fca29e0f84321a200e7e8b4c1b99a563c391f79d6a8c78a4b",
        # Row 0, the one site with no control reaching it until now.  The
        # whole supporting chain is pinned, not just the witness: this row is
        # the only one whose route is a *main-function* route, so its concrete
        # world, dispatcher walk, body walk, index pin and route are each a
        # place a weakening could hide without touching the witness header.
        "attainable_setPauseDurationConfig_adminConfiguration":
            "6714f8bb2410d6ce7df5e0690b738ae13a3689c084628207585ea8bed6b78553",
        "runtimeMain_routeTo_setPauseDurationConfig":
            "b2ffa9bb5f5ac0a8c49cb4600bb43ee9884c36d9214042af07f8158042753349",
        "setPauseDurationConfig_index_pin":
            "74891c0ed2080ea8f89c3c895de54c1cb0138ba3d0dab02e29af3875250d3d53",
        "configWorld_run":
            "b5844c465656c0994589bc4b1c98c01ea6db763dbd2da5cff89f5d2a81f013ef",
        "setPauseDuration_body_runCompiledTo":
            "133ef1542d557a2778e459fa4d346174436df6cbbd4926dd31d8bd4e92360463",
        "setPauseDuration_dispatch_runCompiledTo":
            "b899ab2a93dc3b88ab00d37530c546d88545f688cb10241b2590ef60350cd96d",
        # The shared witness tail.  Every main-function witness routes through
        # it, so a weakening here is invisible in each witness's own header --
        # which is exactly the blind spot `attainable_shape_control` covers for
        # `Attainable` itself.
        "attainable_of_entryRoute":
            "e043cfd2d00a919420ed2b46a1033f06bd83f3cb2c2f6e7c222daef20d989de5",
        "prefix_of_lastLinearTest":
            "0d76807e9d0eba727a45a8e0e603f744034574aefe4400bcedcd3f85c8c024f1",
        "breakerState_stor":
            "6afa08b9b9387e42c9adb2162e2ce652ed084b14e4b8d9312913caaabf693885",
        "breakerMsg_codeBytes":
            "f61472e8f23473faa40dbe7aeade667b3c2cb5b1751baf11caf3dcec450bb16e",
        # Row 1 -- `setPauseDuration`'s structural twin, one dispatcher pivot
        # deeper.
        "attainable_setHeartbeatIntervalConfig_adminConfiguration":
            "ba9e20fa34a7dbeb1c2d83eb72ff7e260631c68944f44f2c4549c48c4f827687",
        "runtimeMain_routeTo_setHeartbeatIntervalConfig":
            "f378058ecb01ea9084e460502663b4b977fdc7e8d7709ca152e66a79144f54ed",
        "setHeartbeatIntervalConfig_index_pin":
            "4273b02a82a0d0c861f36b2146ae760100ff971de5e6f0c79642ec0c23c84c17",
        "intervalWorld_run":
            "8dfd1c053a0e6d894fd58d804a79f82bd5c3df4892ecd9895a56cdd6404b42f4",
        # Row 2 -- the only witness at the `.heartbeatExpiry` role.
        "attainable_heartbeatExpiry_heartbeatExpiry":
            "4fbef29a1506c97b2efdd4341573b864ad3f579981883a8b6f4f8dafac369943",
        "runtimeMain_routeTo_heartbeatExpiry":
            "716c4635c53be00cbf618fc138e1feec6a58b5c421c726ace693a3d7cb4d6752",
        "heartbeatExpiry_index_pin":
            "ed70bd7e5ce821810e7970f8f1395bec188158711bd12528822fd326c1d36e83",
        "heartbeatWorld_run":
            "82bd70d34750714acf01a22898d74be39df85e36e0dfb6f42c770745ea844ddf",
        # The frame-carrying generalization every storage- or memory-valued
        # branch word needs.  `attainable_of_entryRoute` is now a one-line
        # corollary of it and its own digest is unchanged -- which is exactly
        # why this one is pinned: a weakening would live here, invisible above.
        "attainable_of_entryRoute_frame":
            "56a2e093b20e77157aaf56e32027b3b3ec422345dc0de167a90efd3f8cfe5c94",
        # Rows 14, 15, 16 -- the `registerAfterSet` expiry arms behind
        # `previousPauser != 0`.  Row 14 is the retained arm and is named for
        # it; before the 14/17 name exchange it was called Fresh, so reports
        # and commits older than that exchange use the opposite pairing.
        "attainable_registerRetainedOldNewExpiry_adminExpiry":
            "2504e9425955b64ced04c55c90cab0ffc40d406aeadc305bada085bbac17b2a6",
        "attainable_registerLastOldClear_adminExpiry":
            "e3ce8d3bc78211e4db499566a84d5761ac52781f064fab0dac9a0b7661d9578e",
        "attainable_registerLastOldNewExpiry_adminExpiry":
            "0b13cd926cf154ef25db16bbca27ce5e7f7b5624d902c585462cd5e9ede0e263",
        "runtimeMain_routeTo_registerRetainedArmExpiry":
            "b5894749eda1284b0dc905733aad08c3a6e9360ecd46ca127ed7e6bc366b0238",
        "runtimeMain_routeTo_registerOldLastClear":
            "c68ec4502e84f963f68a2ef5fb6fedcd196e09ff748d895936a92b290feb2086",
        "runtimeMain_routeTo_registerOldLastNewExpiry":
            "a42db3eb31f1cb420a323e6ad8ef74b92277773989a983b946f596c0b723a413",
        "runtimeMain_routeTo_replacementRegisterAfterSetCall":
            "97f9b0a18f070579d5494469feb61d084de2e59e501543dac84aac45d66aab80",
        "registerReplacementArm_index_pins":
            "a23fed0347e5f2a214f92f3ecaf9d650fc3a68724b0ec7dd121fc5e08634ebbf",
        "replWorld_previousPauserPresent":
            "9ffeec75db74df68de416abc14b58c52ec4e0baaf3dfec5ac63f870e3e8da2dd",
        "replWorld_countDecrement":
            "661e9f76d3a9f7287a2b38239b2501699c9ad0f4e3e95b0c46e2e7db08a8a369",
        "replWorld_newCountWrite":
            "6275481fc8d9d1d6a1a3d8d979e54cea37a759e2257b330badecae6a9228c982",
        "replWorld_previousCountWord":
            "b345d4cba0f7b2bf9750668a2a4eb73940e822685226350afd51dc51e66a0e88",
        "replWorld_stagedEntry":
            "c65e892128be93b5d07fd93bd274cbf3c695cb575b55f6d123b3c68a8b1a796c",
        "attainable_setPauserAssignment_adminRegistry":
            "ec8411f23b0b0af25af485aae39ebcc0169663b17b986694c8eb94183ae1f399",
        "attainable_appendArrayEntry_adminRegistry":
            "4a240aa5825d9e2f8553a48ed74a0722e11c89f2781d857dc51a24095b6ff242",
        "attainable_appendReverseIndex_adminRegistry":
            "cefa921980af451e7295d2b7c17b22d54e4711b44fadbebe8a11b5fed9b76c26",
        "attainable_appendArrayLength_adminRegistry":
            "ad9ec293069a766f4107e25c31481fa74bb871613c172a8a2f8bcf4b2b975cc9",
        "attainable_afterOldNewCount_adminRegistry":
            "a5c9d06bb34ca29d012c48e8e4e4dc2b67d45093034e34ff7de7c2af11a82a87",
        "attainable_registerFreshExpiry_adminExpiry":
            "e8685b88c683d9b49dd12caf46123234dd7006c3dbf6d61c3338c521f96252b8",
    },
    # The admin unregistration world: one concrete `Msg`-rooted, gas-exact
    # execution whose run ends `.ok`, unlike the pause world's, and the only
    # world in the family that satisfies the Registry projections at entry.
    "unregisterWorld": {
        "unregisterWorld_run":
            "d0d9af792251bcd66f56956c96668677c0b2feb99c044ec6332e58ee4f0cfe98",
        "unregisterWorld_effects":
            "5a9bf307d176bc10f6a5c4985711011d145f9cb626a1dfee42b454bd3ee483d9",
        "unregisterWorld_settles":
            "63ca8c1fe4d55f812474e1a687575d43aecc9fb34012ef5b168abdb80e7b47e8",
        "unregWorldStor_witness":
            "ae7af3faf795fe84a5b7cabd23ea39824b30b55df8b22924bec102a80ebcaa91",
        "unregWorld_bodyGasEq":
            "e57e87e73035c51199cd43cb551a957cd66fa5482362d24e749257491fe9c5a8",
    },
    # The `.adminRegistry` half of the six rows the pause world attains at
    # `.pauseRegistry`.  The route and the shared tail are pinned alongside the
    # six witnesses: a weakening in either would leave all six headers
    # byte-identical.
    "unregisterAttainment": {
        "attainable_setPauserOldCount_adminRegistry":
            "ea81e3701aed1f88410fb72919c563ffcefb0545f6c3e948a11e44052f85d206",
        "attainable_removeArrayHole_adminRegistry":
            "26ad08fe8f74b500530cab0eab041a4b8a370ff4d6c9dc74c7baac69dc2a7b75",
        "attainable_removeMovedIndex_adminRegistry":
            "be7a7223a50751a2c3e6c5db8762e667cef33f23420f4050b87cb78262bf352f",
        "attainable_removeClearTail_adminRegistry":
            "118563e572542d2ce493bbedd21e79502480889883e5a07a91689568deb094dc",
        "attainable_removeArrayLength_adminRegistry":
            "e6ccd0fda666c1d677cf21e1bfb5b920c4f34b2ab2fa765520daf2b9a6b89424",
        "attainable_removeClearTargetIndex_adminRegistry":
            "69eb21a8bc06e8a05196419d664ef827e80af522f7cd4c32d69f91ee8e67e6cf",
        "attainable_adminRegistry_of_route":
            "6b62790f8a04ce0a8f5271cfb34dad6b0403987351086b5e76cd51781477d83d",
        "runtimeMain_routeTo_unregisterKernel":
            "b149a880509ae920c2c934a76abf5141e883250516309610c5a807857f453d00",
        "registerStaging_windows":
            "2256e1201cdfc7541f09bd675564463b08dd964e96a80b51aecc562c9a48052e",
    },
    "replacementWorld": {
        "replRetainedWorld_run":
            "b28c60f646af32812fa0d2753ef8ac2171470bda9a207ddaeae754c440055219",
        "replOldLastWorld_run":
            "8a6d999da42519c4a5a0df8fc0228134a42827f3ef032543938c8fdd07b8f319",
        "replRetained_bodyGasEq":
            "6b06405c7f08a8cbb26b2a784be00b7f18f2c4e5aa13c2dd09133fa961e7a787",
        "replOldLast_bodyGasEq":
            "85cc5d8429b92d42b011a2f4247983aeffc1011bdd7374b966ad6912bf03ccdf",
    },
    # The seven `.pauseRegistry` rows.  Every one is reached in an execution
    # that then REVERTS -- the codeless-target pause -- so these are
    # raw-occurrence witnesses and nothing more.  That is the correct dual of
    # AT5, which quantifies over raw writes under any outcome; it must never be
    # read as "a pause can persist a Registry change".
    "pauseAttainment": {
        "attainable_setPauserAssignment_pauseRegistry":
            "1eb2a23250677909a4e5dff76078fb84c4c2a0af7d640ffea0d53e15b02ef627",
        "attainable_setPauserOldCount_pauseRegistry":
            "5b24894cc5acec73433f3453a9f0f8496e0821137e637ef85513d474f85fce4f",
        "attainable_removeArrayHole_pauseRegistry":
            "7ac4b0d6d2fbd18558b5e0653c03871ddfaabf14f5ea0ad78f39d44c8f93f967",
        "attainable_removeMovedIndex_pauseRegistry":
            "abb9d107fd1a0e76c5d27518c903970de73e1cad090a39c5e4b65e5fb5a64660",
        "attainable_removeClearTail_pauseRegistry":
            "9c4f540f9a61fc036390b9707051722c80eaeaa1cfa9c40376ff069f8b6ee13a",
        "attainable_removeArrayLength_pauseRegistry":
            "6eeb108a74d6e75e9b4386fc55f123bd20bdc002d112a0ea95a2cbe6da02ecd9",
        "attainable_removeClearTargetIndex_pauseRegistry":
            "fab24c66d8295131031c2a465c033ba25990334517f61232c2ca27f09f7cc7fa",
        "attainable_pauseRegistry_of_route":
            "38c8fb1aa7bc9abc2cda5a20fe72f80a5a904a8a7b509af041ee7c7d20172cec",
        "runtimeMain_routeTo_pauseAssignment":
            "de0279a875cbab93b68223e54c36f0fdb4317d074a0d149d100bfe79d3f837a0",
        "runtimeMain_routeTo_pauseKernel":
            "dce61c19ade44c703e27d664d2ef4ffd29ff0079877e77f90653b65a28ca418e",
    },
    # ---- The two `.pauseExpiry` rows, on runs that SUCCEED ----
    #
    # Read the `pauseAttainment` comment above first, and do not read these
    # three blocks as widening it.  Those seven rows are `.pauseRegistry`
    # raw-occurrence witnesses inside executions that then REVERT.  Rows 18 and
    # 19 below are the family's first `.pauseExpiry` rows and their executions
    # END `.ok` -- `pauseLastWorld_run` and `pauseRetainedWorld_run` each
    # exhibit a `Prog.RunCompiledTo ... (.ok post)`.  So the two claims are
    # different in kind, and neither implies the other: a succeeding pause is
    # exhibited *here*, at the expiry cell, and nowhere else in this family; a
    # pause that reaches a Registry row still reverts.
    #
    # What the succeeding runs do NOT claim is also on the record, in each
    # join's own docstring honesty register: the entry world is Registry-well
    # formed by *projection*, with no genesis- or deployment-reachability
    # claim, and the callee is a neutral responder written for the crossing.
    "pauseWorldRun": {
        # The two concrete worlds' runs, and the `pauseSuccess` boundary each
        # hands the dichotomy.  The boundary carries the post-callback count
        # word -- `0` at row 19, `1` at row 18 -- which is the whole reason the
        # two joins land on different arms of the value law.
        "pauseLastWorld_run":
            "b309478eecbbfaca97d5555ecbd5036b21133a1589de6d2582c45748b69f82f2",
        "pauseRetainedWorld_run":
            "95ff593a6342c46f442ef6503e254705a82f52c10be83ea96878a3d440998014",
        "pauseLastWorld_successBoundary":
            "4e526688540eee93d297279261e9024919be585a19dd8e3fc1c94991d84b7a65",
        "pauseRetainedWorld_successBoundary":
            "58c6cae27de0737a14b21558f68ddbe75841c84a5b003ae16d26bb0d641ee0d3",
        # The full effect conjunctions the two above project out of.
        "pauseLastWorld_effects":
            "b806f3c14303c770b43d6b8b1bca6436cf40e79968e0b29040678ca7ea002697",
        "pauseRetainedWorld_effects":
            "2f1195252b0a13183e29f3277d7f1036f3d6a42e6a927885b77dd30f2dbb6c91",
    },
    "pauseOkRoute": {
        # The two route finals, one per arm.
        "runtimeMain_routeTo_pauseLastExpiry":
            "3e75afe3366337ef76660926d0190bcc1d6af75483128b36d8f6f363b7e06aa5",
        "runtimeMain_routeTo_pauseRetainedExpiry":
            "5f290ce093f34d5a02363a28dd7e9a5085a871762a21b4b2c916c519617c2fd6",
        # The shared tail both witnesses route through -- the burn-carrying
        # sibling of `attainable_of_entryRoute_frame`, needed because this
        # route reads `transientStorage` and must pin its states against a
        # concrete world.  A weakening here is invisible in either witness's
        # own header, which is exactly why it is pinned.
        "attainable_of_entryRoute_frame_burn":
            "9ae59f4ead58345814151e46d1c44b443176273be375a258fc896e43f62314e5",
        # The four route segments the finals compose, in program order.
        "runtimeMain_routeTo_pauseKernel_ok":
            "d10ad2d51832b98554875e3eb339c993880c6b9292ee1a4f766dfd967578ac8f",
        "pause_routeTo_setPauserCall_ok":
            "4bdbb39aa2664f81937dfe8f995d8b019b4b9e9a797b8832a5ea0bb0c3f7b229",
        "setPauserKernel_routeTo_pauseAfterSetCall":
            "412ad15155258112fbd7dcafa6cc0c116e4da5705dccab4422c6e795e6270cc9",
        "pauseAfterSet_routeTo_countBranch":
            "946c8717d0a918e16d37bf84bdead65a999597a17d5bf20d8d2d409043eaa260",
    },
    "pauseJoin": {
        # J1/J2: the two rows attained at `.pauseExpiry`.
        "attainable_pauseLastTargetExpiry_pauseExpiry":
            "82f9b2ae0e4593c6c8443e449fb4741d2c3919451cb8d0c1b07ad784a56beb19",
        "attainable_pauseRetainedTargetExpiry_pauseExpiry":
            "d9e1ecb8c415a96218ba85ab6b393816b95849cc205f8c1f9bc52a317b68ebd9",
        # J3: the joins themselves.  Each conclusion carries FOUR conjuncts --
        # the boundary walk, the reached expiry write, the value law at this
        # world's count, and the attained row -- and dropping any one of them
        # is a different, weaker claim.  `MUTATIONS` below rejects two such
        # drops; `pause_join_expiry_value_control` in the fixture covers what a
        # header pin cannot see, namely `PauseExpiryValue` being gutted as a
        # `def` while both headers stay byte-identical.
        "pauseLastWorld_join":
            "a5ac85a9e93e62b1b66237ebb5e692ee1f70794a16394156e4c470d7bce852bc",
        "pauseRetainedWorld_join":
            "41a00c2f6264d4b1a588eb27714ecf9b824addc480e6deb830a3c3c9932f630d",
        # The two index pins that make each route's path identify its row.
        "pauseLastExpiry_index_pin":
            "98c7b749e19b4671ef1cc75c9ba37085e06f9f9bc829c62109ac0100d841a720",
        "pauseRetainedExpiry_index_pin":
            "4caae19165afad2d4c71c8ee35e29256d126473f237d47f0381da4fb18c6aecf",
        # The responder-crossing effect lemmas.  These are what let the route
        # cross a CALL and a STATICCALL into a foreign account and still know
        # the caller's storage, code and staged memory word survive; relax
        # either conclusion and the crossing stops being a crossing.
        "responder_call_effects":
            "1e99a8c96ab905d1bfce1e4683e8186d200b37e487cf2dda97676266dc4964a2",
        "responder_statcall_effects":
            "0ebc83d783d16c055c8e9f4c7f41dea051fe58ae96de4ec0a82e3d54764128e7",
        "responder_hcall":
            "742387998c56dd1902b6a24592238b48df17689b2af9c6c2512dd644d8dec7a5",
        "responder_hstat":
            "b1bcfd15b76d6e617bb94d77319735ffa6dc0c117c4fc8cf54101fb9c656dbfa",
    },
    # ---- What the settled MESSAGE leaves behind, at the same two worlds ----
    #
    # `pauseWorldRun`'s two `_effects` say what the RAW poststate contains;
    # these four say what survives the frame's settlement, which is a strictly
    # stronger and differently falsifiable thing.  Each `_settles` conclusion
    # carries the exec equation, the `ProcessMessage` at this world's own
    # message, and then the surviving cells, the ordered log triple and
    # other-pauser noninterference; the two rows differ exactly in their
    # content -- row 19 retires the pauser and stores `0`, row 18 retains it and
    # stores `pauseWorldInterval + pauseWorldTime` -- so restating either at the
    # other's value is a different claim, not a rephrasing.  `MUTATIONS` below
    # rejects three such rewrites: a dropped `ProcessMessage` conjunct, row 18's
    # surviving expiry restated as row 19's `0`, and a relabelled post-removal
    # entry list.
    #
    # What no header pin here can see is `RunFrame`/`ProcessMessage` gutted in
    # `Blanc/Semantics.lean` as `def`s while all four headers stay
    # byte-identical -- both settlements would then be trivially provable and
    # would say nothing.  That is what
    # `pause_settlement_message_content_control` in the fixture exists for, the
    # same blind spot `pause_join_expiry_value_control` covers for
    # `PauseExpiryValue`.
    #
    # The two projections are model-side by construction: they are stated over
    # the model's applied writes, not the settled storage, and are pinned so
    # that a widening to a poststate `RegistryWitness` cannot land silently.
    # `pauseWorld_projectionAgrees` is the only place the model side and the
    # run side meet, and what it pins is exactly how far the agreement goes:
    # the two sides agree at the slots the trace TOUCHES -- five at the last
    # world, seven at the swap-popping retained one -- and not at every slot,
    # which would need the universal storage frame the walk does not export.
    # Its agreement list is therefore content, not bookkeeping: `MUTATIONS`
    # rejects narrowing the retained world's seven back to five, which would
    # silently stop checking the two cells the swap-pop moves while the
    # theorem still read as an agreement result.
    "pauseSettlement": {
        "pauseLastWorld_settles":
            "f546d1ce25eea5c4f18e7d92b530aa21cf95b61653f3dd5fd6a050f1efe6dcac",
        "pauseRetainedWorld_settles":
            "91e0b7040e229c854ce6df20f292ede85a9adf046e5389b6eb55c123e99e4073",
        "pauseLastWorld_registryProjection":
            "bcb1a349f313b376e38af771aeaf696f53132f65de0bb6eeeae0b822264b6a7f",
        "pauseRetainedWorld_registryProjection":
            "7e62753e46d772a674e4f888469b81d1660e5bb1cc7d4569f78c29f11c8d2820",
        "pauseWorld_projectionAgrees":
            "c4ebe339e0da9136cc0f309f5341969bc0d135d5894666b72b5209dfa1fbee32",
    },
    # ---- Stage 6: settled before the target gets control ----
    "preControl": {
        # P2: the lock is set at the state `pause` hands its own body.
        "pauseLockPost_lock":
            "981e902f2bbf28e9686a38258607169ec396bf44bb100d076486addfb784ab23",
        # P2: and it is still held where the Registry kernel is entered.
        "pauseKernelBase_lock":
            "d3e6d198d9213f0c92d2a430bffc44edbfbf74ba64cd732b622a7be57aa687be",
        # P1: the kernel's clearing write, read back at the cell it lands in.
        "assignmentPost_assignment":
            "ec11a7f06a49a484ba2abe253dcb6869179ccb74549bac85466008f54f74099d",
        # The removal span's storage frame: a cell missing all five written keys survives it. The swap-pop tower subsumes the degenerate walk, so this serves both.
        "removalPost_getStorVal_other":
            "0056a01ad9bfdd138d960238b5d39b74379def77f2a9a1c57cda53751ba95bfd",
        # P1: the clearing survives the old pauser's count decrement.
        "foundKernelPost_assignment":
            "5a8e7737063afd6bfd92923c2426db142a47d850600dc30672fa985055bfa4c1",
        # P1: the assignment cell is zero at the state `pause` hands `pauseAfterSet`, for arbitrary target bytecode.
        "pauseAfterSetEntry_assignment":
            "addd5265deefc79b9627c31db14841831fcf00f35c6cc970c02c571992f579a3",
        # What makes the line above a fact about the pause: the tower plus the `PauserSet` record IS `pauseAfterSet`'s entry, on the pause's continuation.
        "removeTarget_pauseAfterSet_runCompiled":
            "cb411ff1fcfae53f3e13a2c9b3b8e9721d3f80b837a41ffdebdfdcfd4f4bbc28",
        # P3: neither storage nor transient storage moves between the boundary and the CALL.
        "pauseCallEntry_frame":
            "3ab2582962f43225ded36acf5f835fdffdbda408072fdd3c9f96c4acca0e6566",
        # P1 and P2 carried to the CALL itself -- the instant the target receives control.
        "pauseCallEntry_assignment_and_lock":
            "870ecb2b55649c76bd502afc1d08443d562651d5c27dfee94af9b5c3f669cb48",
        # P4: a re-entering pause takes the lock guard's refusal arm, whatever the target's code.
        "pause_body_runCompiledTo_error_of_locked":
            "d121c6dbb924db996636324f0d041038e41cc3cf4eb35b939cc3e4b0b672459c",
        # P4 at the deployed runtime's own entry.
        "pause_runCompiledTo_error_of_locked":
            "20f5072a984703c8d8d89ab0a3053c3e545a849e4c1064d42dc45659fd61473f",
    },
    # ---- Stage 6: what the CircuitBreaker SENDS, and in what order ----
    #
    # `PauseCallBoundary` and `PauseStatBoundary` are `def`s, and they carry
    # this family's whole content: the argument windows' encoders, the callee,
    # the caller, the value, the static flag, the transient storage handed
    # over.  Emptying either would leave every header below byte-identical
    # while making all of them trivially provable, so the pins here hold the
    # statements' SHAPE and `call_boundary_arbitrary_target_code_control` in
    # the fixture holds the relations' content -- the same division of labour
    # `pause_join_expiry_value_control` performs for `PauseExpiryValue`.
    #
    # What the pins do reach is every place a premise could smuggle a
    # cooperative callee in.  Each header below is stated at a universally
    # quantified target, and the two that cross the callback -- the surviving
    # target word and the joined boundary -- are pinned precisely because a
    # weakening that added "suppose memory is unchanged after the callback"
    # would still read as a crossing result.
    "callBoundary": {
        # The zero-byte return window is why the staged target word survives an
        # arbitrary callee: the resume writes `child.output.take 0`.  A widened
        # window makes this false rather than merely unproved.
        "pauseCall_targetWord_survives":
            "1db9b831ce405eab72549860ba80644bc7573fd80e8a403cb97205183320062e",
        # The two edges themselves, each inverted out of the machine's own
        # crossing for arbitrary target bytecode.  `pauseStat_boundary` sits
        # downstream of the callee's whole run and still carries no premise
        # about it.
        "pauseCall_boundary":
            "5305fcec2a37665ade6f7b77d8edd2f493d8c65cb3a3f9f87ade7357d3a75499",
        "pauseStat_boundary":
            "7ca1442b6252e24ef29693089cbd298a41e5a0b5d0993d30f00d688ba285ddfa",
        # The program cut the ordering results are stated against.  It is a
        # `rfl` identity with `pauseAfterSet`, so the branch results below are
        # about the deployed program and not about a paraphrase of it.
        "pauseAfterSet_eq_afterCall":
            "ed220079a2b0e3cfa820425b27e82417100444b0f71c2fd20dec4e6b0f2c0e3d",
        # The word the branch reads: the CALL's flag, inverted by the `ISZERO`
        # between them, equal to the child's error -- and taking exactly two
        # values, neither of which this family decides.
        "pauseCall_branchWord":
            "874625371dbe0826a8b2d9811c07cd0880b37266033d0cb801a3ab600e8c95d5",
        "pauseCall_flag_dichotomy":
            "3c96881687529c2e088856895179efb12edf4a698f9b79121724778e97834e6c",
        # Both arms, PRODUCED from the derivation rather than assumed on either
        # side.  The continuation is universally quantified, so this is a
        # statement about the branch and not about what the success arm does.
        "pauseAfterCall_arms":
            "706a4d75c76db8f071614200d540983d2861dcc513ef41067ddf4bc6758298bf",
        # The bubble slot's binding, discharged by the deployed table itself so
        # the arm theorems' lookup premise is not left to a consumer.
        "runtime_bubbleRevertSlot":
            "91f34f8b61dc1595aa321501e1a98956cc33125cc8a169d774079b6d04cc4ac6",
        # The failure arm: it reaches the bubble still holding the child's
        # returndata, settles at an outcome that cannot commit, and outputs
        # either that returndata or the bubble's own memory-expansion refusal.
        # The payload's `List.take` at the length round trip is content, not
        # bookkeeping -- collapsing it to `child.output` would take a premise
        # about what the callee returned, which this family admits nowhere.
        "pauseCall_failureArm_bubbles":
            "4122d1ebc430e8a82a9182d29d55760499b472729afd6f5d2c80388ed5278ef7",
        "pauseCall_failureArm_neverCommits":
            "9a383c051c3f665a098f6f70123cceebdda5dd0bd0947e9c232a11037857f9a3",
        "pauseCall_failureArm_payload":
            "82a97e33bfab77f19d288436cc01e958a644ea15d531c3325335f64b11dc3f96",
        # The success arm is the only route to the STATICCALL, handing on the
        # crossing premise `pauseStat_boundary` consumes; and its `.ok` shadow,
        # which carries no case hypothesis at all and converts "the frame got
        # past the branch" into "the pauseFor(uint256) call succeeded".
        "pauseCall_successArm_reachesStatcall":
            "623499f01e5574230c23b97bea25e9a782745487c9dfb40920894112ad71e3dc",
        "pauseAfterCall_ok_forces_callSuccess":
            "084d8e98ce45cd1fb40d975e73245ac9cb0fbe3a7e9f471b40f1617ed7d5c700",
        # The CALL's argument window built from the staged duration word by the
        # CircuitBreaker's own straight-line code.  No callee appears in the
        # statement, because the staging runs strictly before the crossing.
        "pauseCallStaging_calldata":
            "327e214d91ae56d3067bb996bd59dc9d96a819891297af5b364d0bb359555344",
        # The joined boundary: both messages at the SAME target, both operand
        # stacks derived by forward evaluation rather than assumed, and the
        # second staging reached through the target word carried across the
        # callback.  The order is in the statement's own shape.
        "pause_externalBoundary":
            "a85d61145a4f802704234fd2dae7e78629a73c2283377a2831fc3d0ebd76608c",
    },
    # The observation cut: what the CircuitBreaker does with the target's
    # answer.  Every outcome is indexed to a projection of the child's
    # output, never to the word memory happened to hold, and the
    # short-return arm draws no conclusion about that word at all.
    "observation": {
        "pauseStat_stagedWord_survives":
            "851cfb0593ea694d4bff6b1fd2b6c2ab3a6f42983ec8aae8b769167e54d9fe84",
        "pauseStat_window_holdsAnswer":
            "b6147d863384ce4e0cb3df0b0aaf9c334f29cbb48a60801a5947bae3623d9142",
        "runCompiledTo_next_inv":
            "df77fdecaedf00c38e5d5bc385431712e65d7aa1b2c8064646fbcda13442f799",
        "runCompiledTo_branch_inv":
            "4f7adbbad3acb9008f35a7e1fd3ccdd988cb33c9d652b758e8c6ca2097952dd0",
        "runCompiledTo_call_inv":
            "946d4c4dc0f8cffd31285982d456299b5734938c2cef3952d661e392421853df",
        "runCompiledTo_prepend_inv":
            "6c3c0a7264e74aa0af713f1d29377cbd7c2a09ebf56c677d88e56bd4a495ded2",
        "iszero_stack_inv":
            "906557b6157bed0f18371fc7fb7eed0eb6e6330d2dbf533927ca45787c0bdd60",
        "pauseObservation_arms":
            "f65847961b539aec689255a7894acd4f4b11b7cb43342e6de47aba6228433362",
        "pauseObservation_failureArm_bubbles":
            "2ab199bc7e200393783dd79e446834cd28ac520e9ef1fae53deedf0a271a3366",
        "pauseObservation_failureArm_payload":
            "3f6f470536548f712f76f572c5231f9055fc64e31aa5b27a6b1436eeda71c666",
        "pauseObservation_successArm_reachesDecode":
            "9cf326e7bee90e0142af6e60d9568422169162fe74521cfcba0ee12e4308726a",
        "toB256_lt_32_of_lt":
            "97b943b7017d0d4b2bb6be5f46af15b4e5b76863cdb456f79b7fea5814b9f152",
        "le_length_of_not_toB256_lt_32":
            "3509e338b41374da0cf8b82cac49d7ae291c374911cd7c6ffa9830c5fc661111",
        "pauseDecode_loadWord_eq_answer":
            "d3b48bef5db1230359b40947514a7d8cba3f1ba3cf2d7b69d599149b50014097",
        "pauseDecode_arms":
            "8f8e6421e31e8608159adc50ae600ac248141981cce9a0cdb2de70d65ac11006",
        "runCompiledTo_last_inv":
            "212935a36e629c97d8b84cb3ab7a7fd42afae88e77446e72c87b9a609408fe39",
        "runCompiledTo_rev_inv":
            "4a7305a9f3950009b6f46121a7e9ba19cd748d3b23c6ce849fde3a17b60c3823",
        "runCompiledTo_revSelector_inv":
            "1a6c71f3ccbf28859fc5f4943ce70a8f3d9172db5db5298bc074d8a2dec4a4d7",
        "runtime_emptyRevertSlot":
            "4a4f3ec95f01060c2d9d806322baa7566fe4df9686e86f3ba0b89c653b61d4af",
        "runtime_pauseFailedErrorSlot":
            "9b538e272656e8be46949c9a84e31cb595468beebabd7be5f015d473d6835921",
        "pauseDecode_shortReturn_payload":
            "4ea8c2494c109b8ea43f5332b935ce82cd7fa5b31b4c25ee574d5ce8041766d7",
        "pauseDecode_false_payload":
            "196d728999b6d8e8c2e0ca8fa86a00d5b8bf4ea38e9d4d304a73539b52fa1315",
        "pauseDecode_noncanonical_payload":
            "330e67ac43353358aa8bafcfd605f46c75d374dfb8a0c4debb2fd8ff08544efb",
        "pauseDecode_accepts_one":
            "65e14cd6b758a0929a30f9297c32bb1a61a6929fb62843787d0a821e248059a5",
        "pauseDecode_accepts_one_withTail":
            "a7915d8553aef5031a4041a57bd7786da7bb04e8d4a856e0617f3d43a85ea4f6",
        "pauseObservation_outcomes":
            "c76ce7cee3f7bd67079157693a9ba48fffac877ddf8b84dddf3240f25fb7a5f7",
        "pauseAfterSet_codeGuard_arms":
            "23b220b4371839569937945ba4b532ada6456c62d1610534100b160e4459926d",
        "pauseAfterSet_outcomes":
            "a51a3a9f543bc979c519e91d1733f807f0245f0d1168f4dde1fe808d8caa63c7",
    },
}

# Per-pin axiom expectations, on the contract `scripts/check.sh` already uses
# for its 439 audited rows: an EMPTY expectation means the theorem must depend
# on NO axioms at all, passing on Lean's "does not depend on any axioms" report
# and failing on any axiom whatsoever.
#
# A flat set cannot express that, and this gate probes every pin rather than a
# hand-picked few, so the flat form was not merely imprecise here - it could not
# pass. Three of the 52 pins are decision procedures depending on nothing, and
# Lean's report for them does not match the "depends on axioms: [...]" shape at
# all, so the gate failed with "unrecognised #print axioms output" rather than
# with an axiom comparison. That was invisible because the missing-fixture check
# aborts this gate long before the axiom probe runs.
#
# Every expectation is MEASURED, not inferred from the proof. Do not guess from
# the tactic: `runtimeSourceEffectPcs_official` is `by decide +kernel` and still
# reports all three, because the definitions it references carry them.
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Pins whose expectation is not STANDARD_AXIOMS. A pin absent from this table
# must report exactly STANDARD_AXIOMS, so a new pin depending on nothing fails
# until it is declared here, and a listed pin that acquires an axiom fails at
# once.
AXIOM_EXCEPTIONS: dict = {
    "RuntimePersistentWrite.all_length": set(),
    "RuntimePersistentWrite.inventory_exact": set(),
    "constructor_inventory_cardinalities": set(),
}

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
    # An owner may be carried for its trust scan, compiled-owner guard and axiom
    # probe without pinning any header -- contract-neutral route machinery whose
    # consumers pin what matters, and concrete worlds, which are not claims.
    for name, expected in ROLES.get(key, {}).items():
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
        # AT8, "expired heartbeat renewal": the expiry boundary is inclusive on
        # the failing side -- equality is expired. Narrowing the error theorem's
        # premise to strict would leave `timestamp = oldExpiry` unaccounted, i.e.
        # an expired pauser renewing itself.
        "expired-heartbeat error premise narrowed to strict": (
            "(hexpired : oldExpiry \u2264 timestamp) :",
            "(hexpired : oldExpiry < timestamp) :",
        ),
        # AT8, "unchecked wrap": on checked-overflow the revert must leave owner
        # storage untouched. Dropping the clause admits a wrapped write that is
        # then reverted-but-observed.
        "checked-overflow revert allowed to move storage": (
            "      post.output = heartbeatArithmeticPanicData \u2227\n"
            "      post.logs = base.logs \u2227\n"
            "      (\u2200 a k, post.getStorVal a k = base.getStorVal a k) \u2227",
            "      post.output = heartbeatArithmeticPanicData \u2227\n"
            "      post.logs = base.logs \u2227",
        ),
        # AT8, heartbeat guard weakening: `SenderNotPauser` has precedence when
        # the entry count is zero, and that failure must not write.
        "zero-count heartbeat guard allowed to move storage": (
            "      post.output = customErrorData \"SenderNotPauser\" \u2227\n"
            "      post.logs = base.logs \u2227\n"
            "      (\u2200 a k, post.getStorVal a k = base.getStorVal a k) \u2227",
            "      post.output = customErrorData \"SenderNotPauser\" \u2227\n"
            "      post.logs = base.logs \u2227",
        ),
        # AT8, "retroactive interval mutation": an interval update governs the
        # NEXT successful registration or heartbeat and must move no existing
        # expiry. Dropping the universally quantified preservation clause is
        # exactly the retroactive reading.
        "interval update no longer preserves existing expiries": (
            "          old.toBytes ++ newInterval.toBytes\u27e9] \u2227\n"
            "      \u2200 pauser, canonicalAddress pauser \u2192\n"
            "        settled.getStorVal ca (expirySlot pauser) =\n"
            "          (initDevm msg).getStorVal ca (expirySlot pauser) := by",
            "          old.toBytes ++ newInterval.toBytes\u27e9] := by",
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
    # ---- AT7: registration chronology weakenings ----
    "fresh": {
        # AT8, "registration revival requiring prior liveness": admin
        # registration may revive an expired pauser, subject only to checked
        # addition. Adding a liveness premise to the fresh-registration success
        # theorem is exactly the forbidden reading -- it would make revival
        # conditional on the pauser not having already expired.
        "fresh registration made conditional on prior liveness": (
            "    (hstatic : (initSevm msg).isStatic = false)\n"
            "    (hextension : CheckedHeartbeatExtension timestamp interval expiry)",
            "    (hstatic : (initSevm msg).isStatic = false)\n"
            "    (hlive : timestamp < currentExpiry)\n"
            "    (hextension : CheckedHeartbeatExtension timestamp interval expiry)",
        ),
    },
    "unregister": {
        # AT8, "lost last-pauser cleanup": when the removed target was the old
        # pauser's last, that pauser's expiry MUST be cleared.  Dropping the
        # clause leaves a retired pauser holding a live expiry.
        "last-pauser expiry cleanup dropped from the conclusion": (
            "settled.getStorVal ca (expirySlot oldPauser) = 0 \u2227\n"
            "      \u2200 pauser, canonicalAddress pauser \u2192 pauser \u2260 oldPauser \u2192",
            "      \u2200 pauser, canonicalAddress pauser \u2192 pauser \u2260 oldPauser \u2192",
        ),
        # AT8: the retired rows claim every *other* canonical pauser's expiry is
        # preserved.  Narrowing the quantifier to the old pauser turns a
        # noninterference claim into a restatement of the clause above it.
        "other-pauser expiry preservation narrowed to the old pauser": (
            "\u2200 pauser, canonicalAddress pauser \u2192 pauser \u2260 oldPauser \u2192",
            "\u2200 pauser, canonicalAddress pauser \u2192 pauser = oldPauser \u2192",
        ),
    },
    "replacement": {
        # AT8: `HeartbeatUpdated` count and order *after* `PauserSet` is a named
        # AT7 obligation, so an inverted record order must not pass as the same
        # claim.
        "emitted record order inverted": (
            "[\u27e8ca, [pauserSetEvent, target, oldPauser, newPauser], []\u27e9,\n"
            "         \u27e8ca, [heartbeatUpdatedEvent, newPauser], expiry.toBytes\u27e9]",
            "[\u27e8ca, [heartbeatUpdatedEvent, newPauser], expiry.toBytes\u27e9,\n"
            "         \u27e8ca, [pauserSetEvent, target, oldPauser, newPauser], []\u27e9]",
        ),
        # AT8: the old-last arm retires the previous pauser, so its expiry cell
        # must be pinned, not merely left unmentioned.  Dropping the clause is
        # exactly the omission the review found.
        "retired-pauser expiry cleanup dropped from the conclusion": (
            "      settled.getStorVal ca (expirySlot oldPauser) =\n"
            "        (if oldPauser = newPauser then expiry else 0) \u2227\n",
            "",
        ),
        # AT8: that clause's value is `0` on the separated instantiation.  If it
        # read back the entry expiry the clause would assert preservation of the
        # very cell the walk clears.
        "retired-pauser cleanup value replaced by the entry expiry": (
            "        (if oldPauser = newPauser then expiry else 0) \u2227",
            "        (if oldPauser = newPauser then expiry else oldExpiry) \u2227",
        ),
        # AT8: the old-last arm writes two expiry cells, so its noninterference
        # quantifier excludes two pausers.  Flipping either exclusion to an
        # equation collapses noninterference into a restatement.
        "old-last expiry noninterference narrowed to the old pauser": (
            "pauser \u2260 oldPauser \u2192\n        pauser \u2260 newPauser \u2192",
            "pauser = oldPauser \u2192\n        pauser \u2260 newPauser \u2192",
        ),
        "retained-arm expiry noninterference narrowed to the new pauser": (
            "(\u2200 pauser, canonicalAddress pauser \u2192 pauser \u2260 newPauser \u2192\n"
            "        settled.getStorVal ca (expirySlot pauser) =",
            "(\u2200 pauser, canonicalAddress pauser \u2192 pauser = newPauser \u2192\n"
            "        settled.getStorVal ca (expirySlot pauser) =",
        ),
    },
    "substrate": {
        # AT8: the general swap-pop walk derives ten slot-disjointness facts from
        # `idx \u2260 len`.  Without it the hole write and the tail clear may
        # coincide and the walk degenerates into the target-is-last case it was
        # written to generalise.
        "swap-pop interior-target premise dropped": (
            "(hidxNeLen : idx \u2260 len)", "",
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
    # ---- The pause `.ok` family's weakenings ----
    "pauseWorldRun": {
        # AT8: the witness run must be a run of the DEPLOYED program.  Drop the
        # compiled-code identity and `.ok` is reached by some program, which is
        # not a statement about this contract at all.
        "witness run's compiled-code identity dropped": (
            "        (.ok post) ∧\n"
            "        some pauseLastSevm.code.toList =\n"
            "          Prog.compile (runtime officialParams) := by",
            "        (.ok post) := by",
        ),
    },
    "pauseOkRoute": {
        # AT8: the shared burn-carrying tail derives its `exactInvocation` from
        # storage-owner AND code-address identity.  Dropping the code address
        # would let the route be attributed to a delegating frame.
        "code-address identity dropped from the shared route tail": (
            "    (codeAddress : sevm.codeAddress = some ca)\n", "",
        ),
    },
    "pauseJoin": {
        # AT8: the join's content is that the reached expiry write obeys the
        # value law at THIS world's post-callback count.  Dropping the conjunct
        # leaves a bare occurrence claim -- the write happened, with nothing
        # said about the word stored -- which is the reading J5 exists to
        # exclude.
        "row-19 join value law dropped from the conclusion": (
            "      PauseExpiryValue pauseLastSevm.benvStat.time "
            "pauseWorldInterval 0\n        value ∧\n",
            "",
        ),
        # AT8: row 18 is the CHECKED arm and its count word is `1`.  Restating
        # it at `0` would claim the zero arm's law -- stored word zero -- for
        # the arm that stores `pauseWorldTime + pauseWorldInterval`.
        "row-18 join count argument replaced by the zero arm's": (
            "PauseExpiryValue pauseRetainedSevm.benvStat.time "
            "pauseWorldInterval 1",
            "PauseExpiryValue pauseRetainedSevm.benvStat.time "
            "pauseWorldInterval 0",
        ),
        # AT8: the two attained rows are distinct inventory rows, 19 and 18.
        # A relabelled witness would attain one row twice and leave the other
        # unattained while every header downstream still read the same.
        "row-19 attainment witness relabelled to row 18": (
            "theorem attainable_pauseLastTargetExpiry_pauseExpiry :\n"
            "    Attainable officialParams .pauseLastTargetExpiry "
            ".pauseExpiry := by",
            "theorem attainable_pauseLastTargetExpiry_pauseExpiry :\n"
            "    Attainable officialParams .pauseRetainedTargetExpiry "
            ".pauseExpiry := by",
        ),
    },
    "pauseSettlement": {
        # AT8: the whole point of the settlement altitude is the
        # `ProcessMessage` conjunct -- without it the theorem says only what
        # the RAW run reached, which `pauseLastWorld_effects` already said, and
        # nothing about what the MESSAGE left behind.
        "row-19 settlement's ProcessMessage conjunct dropped": (
            "      ProcessMessage (pauseWorldMsg pauseLastWorldStor "
            "pauseLastWorldGas)\n"
            "        (.some \u27e8\u27e80, pauseLastSevm, pauseLastPre\u27e9, "
            "(.ok post : Execution)\u27e9)\n"
            "        (.ok post) \u2227\n",
            "",
        ),
        # AT8: row 18 RETAINS the pauser, so its expiry cell is stored at the
        # checked arm.  Restating it as row 19's `0` would claim the retiring
        # arm's cleanup for a pauser that is still registered -- a live pauser
        # silently expired.
        "row-18 surviving expiry restated as row 19's zero": (
            "      post.getStorVal configWorldOwner (expirySlot "
            "pauseWorldPauser) =\n"
            "        pauseWorldInterval + pauseWorldTime \u2227",
            "      post.getStorVal configWorldOwner (expirySlot "
            "pauseWorldPauser) = 0 \u2227",
        ),
        # AT8: the agreement list IS the reach of the model/run agreement, and
        # the two cells a swap-pop moves -- the vacated array slot and the
        # moved target's reverse index -- are exactly the ones only the
        # retained world has.  Narrowing seven slots to five stops checking
        # them while the theorem still reads as an agreement result.
        "retained world's agreement narrowed to the last world's five slots": (
            " \u2227\n"
            "          applied.get (arrayEntrySlot 2) =\n"
            "            post.getStorVal configWorldOwner (arrayEntrySlot 2) "
            "\u2227\n"
            "          applied.get (indexSlot pauseWorldT2) =\n"
            "            post.getStorVal configWorldOwner (indexSlot "
            "pauseWorldT2))) := by",
            ")) := by",
        ),
        # AT8: the Registry projection's content is the post-removal entry
        # list.  Row 18's removal is a swap-pop that RETAINS the pauser's
        # second target; relabelling its post-list as empty would project the
        # row-19 outcome onto the row-18 world.
        "row-18 projection's post-removal entry list emptied": (
            "      trace.postEntries = [(pauseWorldT2, pauseWorldPauser)] "
            "\u2227",
            "      trace.postEntries = [] \u2227",
        ),
    },
}

def header_mutation_controls(sources: dict) -> None:
    for key, mutations in MUTATIONS.items():
        if key not in ROLES:
            fail(f"{key}: mutations without pinned headers cannot be rejected")
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
            expected = AXIOM_EXCEPTIONS.get(name, STANDARD_AXIOMS)
            match = re.search(
                r"'" + re.escape(qualified) +
                r"' depends on axioms: \[([^\]]*)\]",
                run.stdout, re.DOTALL,
            )
            if match:
                actual = {
                    item.strip()
                    for item in match.group(1).split(",") if item.strip()
                }
            elif re.search(
                r"'" + re.escape(qualified) +
                r"' does not depend on any axioms",
                run.stdout,
            ):
                # Lean reports a wholly axiom-free result in a different shape.
                # Reading it as the empty set is what lets an empty expectation
                # mean "no axioms at all" rather than "unparseable".
                actual = set()
            else:
                fail(f"{qualified}: unrecognised #print axioms output")
            if actual != expected:
                fail(
                    f"{qualified}: axioms {sorted(actual)}, "
                    f"expected {sorted(expected) if expected else 'none'}"
                )

def main() -> None:
    # Static owner-side checks run first so the gate fails before any Lean
    # subprocess is started.
    for key, path in OWNERS.items():
        if not path.is_file():
            fail(f"missing sole production owner for {key}")
        no_trust_shortcut(path)
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
          f"{pinned} exact public headers and axiom pins across "
          f"{len(OWNERS)} owners; "
          "AT4 twenty-site classifier uniqueness/inverse-coverage/exact-PC and "
          "three-domain separation; AT2 strict-liveness boundary, interval and "
          "canonical expiry views; AT3 admin-necessity and checked-extension "
          "transitions; AT5 raw all-frame write authority with permitted roles; "
          "AT6 owner closure, retained last writer, settlement and the "
          "noncommitting negatives; constructor 2/0/0 domain separation; "
          "the pause .ok family's two .pauseExpiry rows, their route, worlds "
          "and joins, with the joins' value law extracted from an arbitrary "
          "join; what the settled pause MESSAGE leaves behind at those two "
          "worlds, its model-side Registry projections and the slotwise "
          "model/run agreement between them, with each world's surviving "
          "expiry word read back through its own ProcessMessage; "
          "Stage 6's pre-control family -- the cleared assignment and held "
          "lock at the moment an arbitrary target receives control, the "
          "removal span's storage frame, the boundary's identification with "
          "pauseAfterSet's own entry, and the refusal of a re-entering pause "
          "-- with the family instantiated at a universally quantified target "
          "bytecode carried across the span; "
          "Stage 6's call boundary -- the pause's two outgoing messages, each "
          "read out of its own relation as an argument window against the "
          "spelled-out encoder plus a ProcessMessage fact naming callee, "
          "caller, value and static flag, with the staged target word carried "
          "across arbitrary callee execution and nothing said about the code "
          "at the target beyond a universally quantified ByteArray; that "
          "call's argument window built from the staged duration word by the "
          "CircuitBreaker's own straight-line staging, and the two edges "
          "joined at one target with both operand stacks derived rather than "
          "assumed; and the ORDER between them -- pauseAfterSet cut at its own "
          "CALL by a rfl identity, the branch flag shown to take exactly two "
          "values and to invert the callee's error, both arms produced from "
          "the derivation rather than assumed, the failure arm reaching the "
          "deployed table's own revReturnData slot, settling at no commit and "
          "outputting the child's returndata or the bubble's own "
          "memory-expansion refusal, the success arm as the sole route to the "
          "STATICCALL, and any successful walk past the branch forcing the "
          "pauseFor(uint256) call to have succeeded; Stage 6's observation "
          "cut -- what the CircuitBreaker does with the target's answer, for "
          "an arbitrary answer: all seven outcomes named with the aux slot "
          "each reaches and the bytes each outputs, the decoded word proved "
          "equal to a projection of the child's returned bytes rather than to "
          "whatever memory held, the length guard deciding the short-return "
          "arm on the answer's length alone with no premise about the "
          "CircuitBreaker's prior memory and no claim about the mixed word "
          "there, a valid word with any trailing bytes accepted, words staged "
          "at or beyond 32 bytes surviving the observation whatever the child "
          "returned while the word at zero is clobbered by the answer, and "
          "one theorem partitioning pauseAfterSet's derivations across all "
          "seven with both out-of-gas legs explicit and both boundary "
          "relations applied at the states the derivation actually reaches; "
          f"{controls} labelled header mutations, deletion and trust controls")

if __name__ == "__main__":
    main()
