# Shared agent configuration

Every AI coding client used on this repository takes its instructions from here, so that they do
not drift apart. `.agents/roles/` says what an agent of a given kind must do; `.agents/skills/`
holds procedures it can be asked to follow. Both are addressed to whoever executes them and name
no client — client-specific commands, tool parameters and directories stay out.

A client's own configuration is an adapter: it registers a shared definition under a name, with the
description used to select it and whatever model and tool permissions that client wants, and points
at the shared file instead of restating it.

| | Claude Code | Codex |
| --- | --- | --- |
| roles | `.claude/agents/<name>.md` | `.codex/agents/<name>.toml` |
| skills | `.claude/skills/<name>/SKILL.md` | reads `.agents/skills/` directly |
| project instructions | `.claude/CLAUDE.md`, a symlink to `AGENTS.md` | `AGENTS.md` |

To add a client, write adapters in its format for everything under `.agents/`, give it `AGENTS.md`,
and add a row above. Keep the descriptions in step across adapters: that text is what decides when
a role gets picked. Adapter schemas can be strict — Codex drops a whole `.toml` on one unknown key
— so check the client still lists the role after editing one.
