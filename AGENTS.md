# Foundation Project Instructions

- Before committing or submitting PRs, read **`contribute/index.md`**.
- Before writing or refactoring proofs, read **`contribute/style.md`**, **`contribute/refactoring.md`**.

## Setup

Proof work in this repository uses two things, and each has to be enabled once per client:

- the **`lean4` plugin** from the `lean4-skills` marketplace (`cameronfreer/lean4-skills`), which
  provides `/lean4:autoprove` and its siblings;
- the **`lean-lsp` MCP server**, launched as `uvx lean-lsp-mcp` (requires `uv` and `ripgrep`).

Claude Code:

```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4@lean4-skills
```

and it picks the MCP server up from `.mcp.json` in this repository.

Codex:

```
codex plugin marketplace add cameronfreer/lean4-skills
codex plugin add lean4@lean4-skills
codex mcp add lean-lsp -- uvx lean-lsp-mcp
```

Codex does not read `.mcp.json`, so the MCP server has to be registered separately; the command
above writes it into `~/.codex/config.toml`.

## Agent configuration

Shared, tool-independent definitions live in `.agents/`: roles under `.agents/roles/`, skills under
`.agents/skills/`. Each client picks them up its own way — see [`.agents/README.md`](.agents/README.md)
for the layout and for what to do when adding a client.

Delegate matching work to these roles when the client exposes them:

- `lean4-proof-writer`: formalize a new Lean proof from an already-decided mathematical plan.
- `lean4-proof-refactorer`: clean up an existing proof that already compiles without `sorry`.
- `transporter-alpha-centauri`: faithfully port an existing result from AlphaCentauri.
