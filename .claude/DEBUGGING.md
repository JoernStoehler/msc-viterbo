# CC Crash Debugging - Disabled Features

**Status**: All SessionStart hook features DISABLED to isolate crash cause

## What Was Disabled

### 1. SessionStart Hook (settings.json)
**Disabled**: Entire hook removed from configuration
- **Original**: Hook executed `.claude/hooks/session-start.sh` on startup
- **Now**: Empty hooks object `{}`
- **To test**: Re-add hook definition to settings.json

### 2. File Index (session-start.sh)
**Disabled**: File index generation and printing
- **Original**: Ran `file-index.py` to print compressed repo structure
- **Impact**: Agents won't have automatic file awareness at startup
- **To re-enable**: See git history for `file-index.py` invocation

### 3. gh CLI Installation (session-start.sh)
**Disabled**: Automatic gh CLI installation for CC Web
- **Original**: Downloaded and installed gh CLI tarball on CC Web startup
- **Impact**: gh commands won't work until manual install
- **To re-enable**: See git history for wget/tar installation logic

### 4. Environment Detection (session-start.sh)
**Disabled**: All environment-specific logic
- **Original**: Detected CC Web, Codespaces via environment variables
- **To re-enable**: See git history for environment detection

### 5. jq Parsing (session-start.sh)
**Disabled**: Hook input JSON parsing
- **Original**: Used jq to parse hook input for source type
- **To re-enable**: See git history for jq invocation

## Current State

**settings.json**: Minimal config with empty hooks
**session-start.sh**: No-op script that consumes stdin and exits 0

## Gradual Re-enabling Strategy

Test CC startup after each step:

1. **Test with completely disabled hooks** (current state)
   - If CC works: crash was in hooks system
   - If CC crashes: crash is elsewhere (not hooks)

2. **Re-enable hook but keep script minimal** 
   - Add hook back to settings.json
   - Keep session-start.sh as no-op
   - If crashes: hook invocation itself causes crash

3. **Add file index only**
   - Re-enable file-index.py call
   - If crashes: file-index.py is the culprit

4. **Add environment detection**
   - Re-enable environment variable checks
   - If crashes: environment logic causes crash

5. **Add gh CLI installation**
   - Re-enable wget/tar operations
   - If crashes: gh installation causes crash

## How to Restore Original Functionality

```bash
# View what was removed:
git show HEAD~1:.claude/settings.json
git show HEAD~1:.claude/hooks/session-start.sh

# Or restore from git:
git checkout HEAD~1 -- .claude/settings.json
git checkout HEAD~1 -- .claude/hooks/session-start.sh
```

## Related Files

- `.claude/settings.json` - Claude Code project settings
- `.claude/hooks/session-start.sh` - SessionStart hook script
- `.claude/hooks/file-index.py` - File index generator (still present, not deleted)
- `.devcontainer/ccweb/README.md` - CC Web environment documentation
