#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

usage() {
  cat <<'EOF'
Usage: scripts/lint.sh [--fix|--check] [--ci]

Modes:
  --fix     Auto-fix formatting and safe lint fixes (default).
  --check   Check only; do not modify files.
  --ci      Strict mode intended for PRs: fails on any Pyright warning and
            enforces formatting via `ruff format --check`.

Notes:
  - In non-CI mode, Pyright warnings are allowed, but Pyright errors fail.
EOF
}

MODE=dev
RUFF_MODE=fix

while [[ $# -gt 0 ]]; do
  case "$1" in
    --ci) MODE=ci; RUFF_MODE=check; shift ;;
    --fix) RUFF_MODE=fix; shift ;;
    --check) RUFF_MODE=check; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; usage >&2; exit 64 ;;
  esac
done

if [[ $RUFF_MODE == fix ]]; then
  uv run ruff format .
  uv run ruff check --fix .
else
  uv run ruff format --check .
  uv run ruff check .
fi

if [[ $MODE == ci ]]; then
  # Fail CI on any diagnostics (errors or warnings).
  uv run pyright --outputjson | python3 -c '
import json
import sys

data = json.load(sys.stdin)
diagnostics = data.get("generalDiagnostics", [])
bad = [d for d in diagnostics if d.get("severity") in ("error", "warning")]

if not bad:
    raise SystemExit(0)

print(f"[pyright] strict mode: {len(bad)} diagnostics (errors/warnings)", file=sys.stderr)
for d in bad[:50]:
    file = d.get("file", "<unknown file>")
    rng = d.get("range", {})
    start = rng.get("start", {})
    line = int(start.get("line", 0)) + 1
    col = int(start.get("character", 0)) + 1
    severity = d.get("severity", "?")
    message = d.get("message", "").rstrip()
    rule = d.get("rule", "")
    suffix = f" ({rule})" if rule else ""
    print(f"{file}:{line}:{col}: {severity}: {message}{suffix}", file=sys.stderr)

raise SystemExit(1)
'
else
  # In dev mode, allow warnings but fail on errors.
  uv run pyright
fi
