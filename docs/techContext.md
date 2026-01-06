# Tech Context

## Stack
- Lean4: `leanprover/lean4:v4.21.0-rc3` (see `lean-toolchain`).
- Mathlib via Lake (see `lakefile.toml`).
- `autoImplicit = false` is enabled; write binders explicitly.

## Repository Conventions
- Main library lives under `Autoomaton/` and is built via the `Autoomaton` Lean library target.
- `Autoomaton.lean` is the root module for the library and should import any modules that must build by default.

## Common Commands
- Build: `lake build`
- Check a file: `lake env lean Autoomaton/Ordinal2.lean`

## Agent Tooling (Lean MCP)
When editing Lean, rely heavily on:
- `mcp__lean4__lean_diagnostic_messages` for fast feedback,
- `mcp__lean4__lean_goal` for interactive proof state inspection,
- `mcp__lean4__lean_file_outline`/`mcp__lean4__lean_hover_info` for discovery.

