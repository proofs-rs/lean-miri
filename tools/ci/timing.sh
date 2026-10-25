#!/usr/bin/env bash
# Preserve normal local execution; record a command only when timing is enabled.
ci_step() {
  local label=$1
  shift
  if [[ -n "${CI_TIMING_FILE:-}" ]]; then
    python3 "${BASH_SOURCE[0]%/*}/time_command.py" "$label" -- "$@"
  else
    "$@"
  fi
}
