# CC Web Startup Hook/Settings Crash Investigation

## Problem Statement

The startup hook or settings in CC web are crashing hard. This document identifies the most likely offenders and provides methods to disable them for testing.

## Analysis Overview

The CC web environment has several known limitations that could cause crashes:
1. **apt-get blocked** - DNS proxy architecture blocks package management
2. **Skills broken** - Skill descriptions and names are not autoloaded
3. **Playwright cannot install browsers** - Browser automation fails
4. **No persistent storage** - Git worktrees cannot be used

The `.claude/hooks/session-start.sh` hook and `.claude/settings.json` contain several components that could fail in CC web.

## Potential Offenders Table

| Component | Location | Risk Level | Failure Mode | How to Disable |
|-----------|----------|------------|--------------|----------------|
| **bash -lc flag** | `settings.json` hook command | **HIGH** | `-l` (login shell) may fail if shell profile crashes or is missing | Change `bash -lc` to `bash -c` in `.claude/settings.json` line 25 |
| **CLAUDE_PROJECT_DIR** | `session-start.sh` line 20, 25 | **HIGH** | Variable may be unset/empty in CC web causing path errors | Add fallback: `${CLAUDE_PROJECT_DIR:-.}` or skip if unset |
| **set -e** | `session-start.sh` line 6 | **MEDIUM** | Any command failure terminates the entire script | Remove `set -e` or add `|| true` to risky commands |
| **file-index.py** | `session-start.sh` line 20 | **MEDIUM** | Python script could crash on pathological file trees | Already has `2>/dev/null \|\| echo ...` fallback - OK |
| **wget download** | `session-start.sh` lines 41-53 | **MEDIUM** | Network timeout, DNS issues, or disk space errors | Already exits 0 on failure (line 53) - but could hang on timeout |
| **gh CLI installation** | `session-start.sh` lines 25-64 | **LOW** | Installation fails but script continues with warnings | Already has non-blocking logic (exits 0 on line 66) |
| **jq parsing** | `session-start.sh` line 10 | **LOW** | Input parsing could fail if stdin format is wrong | Add `\|\| echo "startup"` fallback |
| **Environment variables** | `settings.json` lines 3-9 | **LOW** | Git environment vars unlikely to cause crashes | Already safe - just configuration |
| **Permission denials** | `settings.json` lines 14-17 | **LOW** | Permission denials should fail gracefully | Already safe - Claude Code handles this |
| **LSP tool enable** | `settings.json` line 9 | **LOW** | LSP might fail in CC web but shouldn't crash | Can be removed or set to "false" |

## Recommended Testing Sequence

### Option 1: Minimal Settings (Safest)
Create a minimal `.claude/settings.json` with no hooks:

```json
{
  "env": {
    "GIT_PAGER": "cat"
  },
  "permissions": {
    "defaultMode": "bypassPermissions"
  }
}
```

### Option 2: Remove Login Shell Flag
Change line 25 in `.claude/settings.json`:
```diff
-            "command": "bash -lc \"$CLAUDE_PROJECT_DIR/.claude/hooks/session-start.sh\""
+            "command": "bash -c \"${CLAUDE_PROJECT_DIR:-.}/.claude/hooks/session-start.sh\""
```

### Option 3: Disable File Index Only
Modify `session-start.sh` to skip file index:
```bash
# Comment out or skip the file index section (lines 16-22)
# echo "=== Session Startup: Repository File Index ==="
# python3 "$CLAUDE_PROJECT_DIR/.claude/hooks/file-index.py" 2>/dev/null || echo "(file-index.py not available)"
```

### Option 4: Disable gh CLI Installation
Modify `session-start.sh` to skip gh installation:
```bash
# Add early exit before gh installation (after line 24):
exit 0
```

### Option 5: Disable Entire Hook
Comment out or remove the entire `hooks` section in `.claude/settings.json` (lines 19-30).

## High-Priority Fixes

Based on risk analysis, the top 3 issues to address:

1. **bash -lc flag**: The `-l` flag loads login shell configuration which may fail
   - **Fix**: Change to `bash -c` and add `CLAUDE_PROJECT_DIR` fallback

2. **CLAUDE_PROJECT_DIR undefined**: Variable may not be set in CC web
   - **Fix**: Use `${CLAUDE_PROJECT_DIR:-.}` or check if set before using

3. **set -e early termination**: Script exits on first error instead of continuing
   - **Fix**: Remove `set -e` or make critical sections more resilient

## Testing Commands

Test each component individually:

```bash
# Test 1: Validate settings.json
jq '.' .claude/settings.json

# Test 2: Test hook with mock input
echo '{"source":"startup"}' | bash .claude/hooks/session-start.sh

# Test 3: Test file-index.py directly
python3 .claude/hooks/file-index.py

# Test 4: Check environment variables
env | grep CLAUDE

# Test 5: Test without login shell
bash -c 'echo "test"'
bash -lc 'echo "test"'
```

## Patch Files

### Patch 1: Minimal Safe Settings
File: `.claude/settings.minimal.json`
```json
{
  "env": {
    "GIT_PAGER": "cat",
    "GIT_EDITOR": "true"
  },
  "permissions": {
    "defaultMode": "bypassPermissions",
    "deny": [
      "Read(.env)",
      "Read(.env.*)",
      "Read(**/secrets/**)"
    ]
  }
}
```

Usage: `mv .claude/settings.json .claude/settings.json.bak && cp .claude/settings.minimal.json .claude/settings.json`

### Patch 2: Resilient Hook
Key changes to `session-start.sh`:
- Remove `set -e`
- Add CLAUDE_PROJECT_DIR fallback
- Add timeout to wget
- Make all sections independently failsafe

## Conclusion

The most likely offenders are:
1. **bash -lc** flag causing shell initialization failures
2. **CLAUDE_PROJECT_DIR** being unset in CC web environment
3. **set -e** causing premature script termination

Start testing with minimal settings (Option 1) and gradually add components back to isolate the exact failure point.
