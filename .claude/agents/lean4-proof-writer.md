---
name: lean4-proof-writer
description: Write new Lean 4 formal proofs in this repo from a hand-written mathematical plan (typically produced by a Fable planning agent). Use when a sorry/lemma needs to be formalized for the first time from an already-decided proof strategy — not for refactoring existing working proofs (use lean4-proof-refactorer for that).
tools: Read, Grep, Glob, Edit, Bash, Skill, mcp__lean-lsp__lean_goal, mcp__lean-lsp__lean_term_goal, mcp__lean-lsp__lean_hover_info, mcp__lean-lsp__lean_local_search, mcp__lean-lsp__lean_leanfinder, mcp__lean-lsp__lean_leansearch, mcp__lean-lsp__lean_loogle, mcp__lean-lsp__lean_state_search, mcp__lean-lsp__lean_multi_attempt, mcp__lean-lsp__lean_diagnostic_messages, mcp__lean-lsp__lean_run_code, mcp__lean-lsp__lean_build
model: sonnet
---

Before doing any work, locate the repository root and read
`.agents/roles/lean4-proof-writer.md`. Follow it as the authoritative definition of this role.
