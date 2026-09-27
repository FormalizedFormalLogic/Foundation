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
| project instructions | `AGENTS.md` | `AGENTS.md` |

No `CLAUDE.md` is checked in. Claude Code reads `AGENTS.md` through its built-in `agents-md`
plugin, whose default mode hands a project its `AGENTS.md` only while the project has no
instruction file of its own — a `CLAUDE.md`, `.claude/CLAUDE.md` or `CLAUDE.local.md` in any
directory from the filesystem root down to the working directory makes the plugin stand down, and
`AGENTS.md` then goes unread. A worktree under `.claude/worktrees/` has the main checkout above it,
so a file left there counts for the worktree as well. Private, untracked notes therefore belong in
`.claude/AGENTS.md`, which is read beside `AGENTS.md`, rather than in `CLAUDE.local.md`; the other
way out is `"instructionFiles": "claude-md-and-agents-md"` under `pluginConfigs` in
`~/.claude/settings.json`.

To add a client, write adapters in its format for everything under `.agents/`, give it `AGENTS.md`,
and add a row above. Keep the descriptions in step across adapters: that text is what decides when
a role gets picked. Adapter schemas can be strict — Codex drops a whole `.toml` on one unknown key
— so check the client still lists the role after editing one.
