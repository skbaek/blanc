#!/usr/bin/env python3
"""Run the Prague EELS t8n module after the shared loader guard is live."""

from __future__ import annotations

import runpy
import sys

import eels_semantic_closure


eels_semantic_closure.assert_loader_guard_installed(
    eels_semantic_closure.fail, label="Prague t8n entrypoint"
)

sys.argv = ["ethereum_spec_tools.evm_tools", *sys.argv[1:]]
runpy.run_module("ethereum_spec_tools.evm_tools", run_name="__main__")
