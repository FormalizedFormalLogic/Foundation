# Shared agent roles

This directory contains tool-independent role definitions shared by Claude Code and Codex.

The files under `.claude/agents/` and `.codex/agents/` only register each role with a specific
client. Keep behavioral instructions here so the two clients do not drift apart.

When changing a role, update its description in both adapters if the situations in which it should
be selected have changed.
