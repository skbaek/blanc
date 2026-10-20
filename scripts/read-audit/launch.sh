# Audit-only adapter. Ordinary commands and their environment stay unchanged.
gate_audit_python() {
  if [ -n "${GATE_READ_AUDIT:-}" ]; then
    /usr/bin/python3 -I -B "$SCRIPT_DIR/read-audit/launcher.py" \
      "$GATE_READ_AUDIT" "$@"
  else
    "$@"
  fi
}

# Preserve the original wrapper's exec boundary as well as its child command.
gate_audit_exec_python() {
  if [ -n "${GATE_READ_AUDIT:-}" ]; then
    exec /usr/bin/python3 -I -B "$SCRIPT_DIR/read-audit/launcher.py" \
      "$GATE_READ_AUDIT" "$@"
  else
    exec "$@"
  fi
}
