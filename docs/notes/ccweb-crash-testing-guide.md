# CC Web Crash Testing Guide

## Quick Start

If CC web is crashing on startup, try these fixes in order:

### Option 1: Use Minimal Settings (No Hooks)
```bash
# Backup current settings
cp .claude/settings.json .claude/settings.json.backup

# Use minimal settings
cp .claude/settings.minimal.json .claude/settings.json

# Restart CC web session
```

### Option 2: Use Fixed Hook with Resilient Script
```bash
# Backup current settings
cp .claude/settings.json .claude/settings.json.backup

# Use fixed settings
cp .claude/settings.with-hook-fixed.json .claude/settings.json

# Backup and replace hook
cp .claude/hooks/session-start.sh .claude/hooks/session-start.sh.backup
cp .claude/hooks/session-start.resilient.sh .claude/hooks/session-start.sh

# Restart CC web session
```

### Option 3: Disable Hooks Temporarily
```bash
# Backup current settings
cp .claude/settings.json .claude/settings.json.backup

# Edit .claude/settings.json and remove the "hooks" section
# (lines 19-30 in the original file)

# Restart CC web session
```

## Restore Original Settings

```bash
# If you backed up your settings
cp .claude/settings.json.backup .claude/settings.json
cp .claude/hooks/session-start.sh.backup .claude/hooks/session-start.sh
```

## Testing Individual Components

### Test 1: Settings File Validity
```bash
jq '.' .claude/settings.json
```
If this fails, your JSON is malformed.

### Test 2: Hook Execution
```bash
echo '{"source":"startup"}' | bash .claude/hooks/session-start.sh
```
If this fails, the hook has issues.

### Test 3: File Index Script
```bash
python3 .claude/hooks/file-index.py
```
If this fails, the file index has issues.

### Test 4: Environment Variables
```bash
env | grep CLAUDE
```
Check if CLAUDE_PROJECT_DIR is set.

## Files Created for Testing

| File | Purpose |
|------|---------|
| `.claude/settings.minimal.json` | Minimal settings with no hooks for emergency use |
| `.claude/settings.with-hook-fixed.json` | Settings with bash flag fix and CLAUDE_PROJECT_DIR fallback |
| `.claude/hooks/session-start.resilient.sh` | Resilient hook that won't crash on errors |
| `docs/notes/ccweb-crash-investigation.md` | Full analysis of potential crash causes |

## Most Likely Issues

Based on analysis, these are the most likely crash causes:

1. **bash -lc flag** - Login shell initialization may fail in CC web
2. **CLAUDE_PROJECT_DIR undefined** - Variable may not be set in CC web
3. **set -e in hook** - Script exits on first error instead of continuing

All three issues are fixed in the resilient versions.

## Support

If issues persist after trying these fixes, check:
- CC web known issues: https://github.com/anthropics/claude-code/issues/14538
- apt-get is blocked in CC web (DNS proxy bug)
- Skills are broken in CC web
- Playwright cannot install browsers

## Quick Commands Reference

```bash
# View current settings
cat .claude/settings.json

# Test hook manually
echo '{"source":"startup"}' | bash -c "${CLAUDE_PROJECT_DIR:-.}/.claude/hooks/session-start.sh"

# Test with resilient version
echo '{"source":"startup"}' | bash .claude/hooks/session-start.resilient.sh

# Check what changed
diff .claude/settings.json .claude/settings.with-hook-fixed.json
diff .claude/hooks/session-start.sh .claude/hooks/session-start.resilient.sh
```
