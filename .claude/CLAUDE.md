# Foundation Project Instructions

- Before committing or submitting PRs, read **`contribute/index.md`**.
- Before writing or refactoring proofs, read **`contribute/style.md`**, **`contribute/refactoring.md`**.

## Setup

Proof work in this repository uses the `lean4` plugin (marketplace `lean4-skills`, providing `/lean4:autoprove` etc.) and the `lean-lsp` MCP server (defined in `.mcp.json`; requires `uv` and `ripgrep`). Enable both after cloning:

```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4@lean4-skills
```
