# Foundation Project Instructions

- Before committing or submitting PRs, read **`contribute/index.md`**.
- Before writing or refactoring proofs, read **`contribute/style.md`**, **`contribute/refactoring.md`**.

## Setup

Proof work in this repository uses the `lean4` plugin (marketplace `lean4-skills`, providing
`/lean4:autoprove` etc.) and the `lean-lsp` MCP server (defined in `.mcp.json`; requires `uv` and
`ripgrep`). Enable both after cloning:

```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4@lean4-skills
```

## Specialized agents

Delegate matching work to these project agents when they are available:

- `lean4-proof-writer`: formalize a new Lean proof from an already-decided mathematical plan.
- `lean4-proof-refactorer`: clean up an existing proof that already compiles without `sorry`.
- `transporter-alpha-centauri`: faithfully port an existing result from AlphaCentauri.

Their tool-independent role definitions live in `.agents/roles/`. Tool-specific agent files are
adapters and must keep the matching shared role as their authoritative instructions.
