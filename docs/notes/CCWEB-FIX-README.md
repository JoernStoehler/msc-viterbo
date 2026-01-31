# CC Web Crash Fix - Complete Guide

## Table: Most Likely Offenders & How to Disable Them

| Rank | Offender | Location | Risk | Why It Crashes | How to Disable |
|------|----------|----------|------|----------------|----------------|
| 1 | **bash -lc flag** | `.claude/settings.json` line 25 | **HIGH** | Login shell loads `~/.bashrc` which may fail or hang in CC web | Replace `bash -lc` with `bash -c` |
| 2 | **$CLAUDE_PROJECT_DIR unset** | `.claude/hooks/session-start.sh` lines 20, 25 | **HIGH** | Variable doesn't exist in CC web → path errors | Use `${CLAUDE_PROJECT_DIR:-.}` fallback |
| 3 | **set -e termination** | `.claude/hooks/session-start.sh` line 6 | **MEDIUM** | First error kills entire script → no recovery | Remove `set -e` line |
| 4 | **wget timeout** | `.claude/hooks/session-start.sh` lines 47 | **MEDIUM** | Network hang blocks startup indefinitely | Add `--timeout=30` to wget command |
| 5 | **jq parse failure** | `.claude/hooks/session-start.sh` line 10 | **LOW** | Malformed stdin crashes jq | Add `\|\| echo "startup"` after jq |
| 6 | **file-index.py** | `.claude/hooks/session-start.sh` line 20 | **LOW** | Python script fails on pathological file trees | Already has `2>/dev/null \|\| echo...` - OK |
| 7 | **gh CLI install** | `.claude/hooks/session-start.sh` lines 40-64 | **LOW** | Installation fails but non-blocking | Already exits 0 on failure - OK |
| 8 | **LSP tool** | `.claude/settings.json` line 9 | **LOW** | LSP might fail but shouldn't crash | Set to `"false"` or remove line |

## Quick Fix Options (In Order of Safety)

### Option 1: Emergency - No Hooks (Safest)
**Use when:** CC web won't start at all
```bash
cp .claude/settings.minimal.json .claude/settings.json
# Restart CC web session
```

### Option 2: Minimal Hooks - Fixed Version
**Use when:** Want to test if hooks work with fixes
```bash
cp .claude/settings.with-hook-fixed.json .claude/settings.json
cp .claude/hooks/session-start.resilient.sh .claude/hooks/session-start.sh
# Restart CC web session
```

### Option 3: Manual Edit - Remove Hooks Section
**Use when:** Want to manually control what's enabled
```bash
# Edit .claude/settings.json and delete lines 19-30 (the "hooks" section)
```

### Option 4: Manual Edit - Disable File Index Only
**Use when:** Suspect file-index.py is the issue
```bash
# Edit .claude/hooks/session-start.sh
# Comment out lines 16-22 (file index section)
```

### Option 5: Manual Edit - Disable gh Install Only
**Use when:** Suspect gh CLI installation is the issue
```bash
# Edit .claude/hooks/session-start.sh
# Add "exit 0" after line 24
```

## Files Created by This Fix

| File | Size | Purpose |
|------|------|---------|
| `.claude/settings.minimal.json` | 222 bytes | Emergency settings (no hooks) |
| `.claude/settings.with-hook-fixed.json` | 750 bytes | Settings with bash flag fix |
| `.claude/hooks/session-start.resilient.sh` | 2.8 KB | Error-proof hook script |
| `docs/notes/ccweb-crash-investigation.md` | 5.6 KB | Full technical analysis |
| `docs/notes/ccweb-crash-testing-guide.md` | 3.3 KB | Step-by-step testing guide |
| `docs/notes/ccweb-crash-summary.md` | 3.5 KB | Quick reference summary |

## Testing Commands

```bash
# Test 1: Validate settings JSON
jq '.' .claude/settings.json

# Test 2: Test current hook
echo '{"source":"startup"}' | bash .claude/hooks/session-start.sh

# Test 3: Test resilient hook
echo '{"source":"startup"}' | bash .claude/hooks/session-start.resilient.sh

# Test 4: Check environment
env | grep CLAUDE

# Test 5: Test file index
python3 .claude/hooks/file-index.py
```

## What Was Fixed

### Settings Fix (`.claude/settings.with-hook-fixed.json`)
```diff
Original:
- "command": "bash -lc \"$CLAUDE_PROJECT_DIR/.claude/hooks/session-start.sh\""

Fixed:
+ "command": "bash -c \"${CLAUDE_PROJECT_DIR:-.}/.claude/hooks/session-start.sh\""
```

### Hook Fix (`.claude/hooks/session-start.resilient.sh`)
1. ✅ Removed `set -e` (no early termination)
2. ✅ Added `CLAUDE_PROJECT_DIR="${CLAUDE_PROJECT_DIR:-.}"` fallback
3. ✅ Added `--timeout=30` to wget
4. ✅ Added `|| true` to non-critical commands
5. ✅ Added file existence checks
6. ✅ Better error messages

## Restore Original Settings

```bash
# If you want to go back
cp .claude/settings.json.backup .claude/settings.json
cp .claude/hooks/session-start.sh.backup .claude/hooks/session-start.sh
```

## Next Steps

1. **Immediate**: Try Option 1 (minimal settings) to get CC web working
2. **Diagnostic**: Run testing commands to identify exact failure
3. **Fix**: Use Option 2 (resilient versions) once minimal settings work
4. **Verify**: Ensure file index and gh CLI work correctly
5. **Document**: Note which option worked for future reference

## Related Documentation

- `.devcontainer/ccweb/README.md` - CC web environment overview
- `.devcontainer/README.md` - All development environments
- `docs/notes/ccweb-crash-investigation.md` - Detailed technical analysis
- `docs/notes/ccweb-crash-testing-guide.md` - Testing procedures
- `docs/notes/ccweb-crash-summary.md` - Quick reference

## Known CC Web Limitations

From `.devcontainer/ccweb/README.md`:
- ❌ apt-get blocked (DNS proxy bug)
- ❌ Skills broken (not autoloaded)
- ❌ Playwright cannot install browsers
- ❌ No persistent storage (no git worktrees)
- ✅ Rust, Python, Node.js, Git pre-installed
- ✅ gh CLI auto-installed by hook (if hook works)

---

**Created:** 2026-01-31  
**Issue:** CC web startup hook/settings crash  
**Repository:** JoernStoehler/msc-viterbo  
**By:** GitHub Copilot
