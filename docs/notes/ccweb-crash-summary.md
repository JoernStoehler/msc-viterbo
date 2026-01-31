# CC Web Startup Hook/Settings Crash - Summary Table

## Quick Reference: Most Likely Offenders

| Rank | Component | Risk | Why It Crashes | Quick Fix |
|------|-----------|------|----------------|-----------|
| 1 | `bash -lc` flag | **HIGH** | Login shell loads ~/.bashrc which may fail/hang | Use `bash -c` instead |
| 2 | `$CLAUDE_PROJECT_DIR` unset | **HIGH** | Variable may not exist in CC web → path errors | Use `${CLAUDE_PROJECT_DIR:-.}` |
| 3 | `set -e` in hook | **MEDIUM** | First error kills entire hook → no recovery | Remove or add `\|\| true` to commands |
| 4 | `wget` timeout | **MEDIUM** | Network hang can block startup indefinitely | Add `--timeout=30` flag |
| 5 | jq parse failure | **LOW** | Malformed stdin crashes jq | Add `\|\| echo "startup"` fallback |

## Files Created to Fix Issues

| File | Purpose | Use When |
|------|---------|----------|
| `.claude/settings.minimal.json` | No hooks, just env vars | **Emergency**: CC web won't start at all |
| `.claude/settings.with-hook-fixed.json` | Fixed bash flag + PROJECT_DIR | **Testing**: Want hooks but need fixes |
| `.claude/hooks/session-start.resilient.sh` | Error-proof hook script | **Production**: Replace current hook |
| `docs/notes/ccweb-crash-investigation.md` | Full analysis + details | **Reference**: Understanding the issues |
| `docs/notes/ccweb-crash-testing-guide.md` | Step-by-step testing | **Action**: Quick fix instructions |

## Testing Sequence

### Emergency: Can't Start CC Web
```bash
cp .claude/settings.minimal.json .claude/settings.json
# Restart session - no hooks will run
```

### Diagnostic: Test Components
```bash
# 1. Test settings validity
jq '.' .claude/settings.json

# 2. Test hook execution
echo '{"source":"startup"}' | bash .claude/hooks/session-start.sh

# 3. Test with resilient version
echo '{"source":"startup"}' | bash .claude/hooks/session-start.resilient.sh
```

### Production Fix: Use Resilient Versions
```bash
# Backup originals
cp .claude/settings.json .claude/settings.json.backup
cp .claude/hooks/session-start.sh .claude/hooks/session-start.sh.backup

# Deploy fixes
cp .claude/settings.with-hook-fixed.json .claude/settings.json
cp .claude/hooks/session-start.resilient.sh .claude/hooks/session-start.sh

# Restart session
```

## Key Differences: Original vs Resilient

### Settings Change
```diff
- "command": "bash -lc \"$CLAUDE_PROJECT_DIR/.claude/hooks/session-start.sh\""
+ "command": "bash -c \"${CLAUDE_PROJECT_DIR:-.}/.claude/hooks/session-start.sh\""
```
**Why**: `-l` loads login shell config (may fail), `${VAR:-.}` provides fallback

### Hook Changes
1. **Removed `set -e`** - No longer exits on first error
2. **Added PROJECT_DIR fallback** - `CLAUDE_PROJECT_DIR="${CLAUDE_PROJECT_DIR:-.}"`
3. **Added wget timeout** - `wget --timeout=30 ...`
4. **Added error suppression** - `|| true` on non-critical commands
5. **Better path checks** - Verify files exist before using

## Testing Results

All resilient versions tested successfully:
- ✅ Settings validation passes
- ✅ Hook executes without errors
- ✅ File index generates correctly
- ✅ Handles missing CLAUDE_PROJECT_DIR
- ✅ Continues on individual failures

## Recommended Action

1. **Immediate**: Use minimal settings if CC web won't start
2. **Short-term**: Test with fixed versions to confirm they work
3. **Long-term**: Replace originals with resilient versions permanently

## Attribution

Created by GitHub Copilot analysis on 2026-01-31.
Issue: CC web startup hook/settings crash.
Repository: JoernStoehler/msc-viterbo
