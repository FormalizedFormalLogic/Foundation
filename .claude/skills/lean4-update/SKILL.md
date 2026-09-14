---
name: lean4-update
description: Update the Lean (and mathlib/doc-gen4) toolchain version. Bumps lean-toolchain, updates lake-manifest, verifies the build, detects and fixes new errors/warnings caused by the version bump, and opens a PR. Use for requests like "update Lean", "bump the lean-toolchain", or "upgrade mathlib".
---

Before doing any work, read `.agents/skills/lean4-update/SKILL.md`, resolved against the repository
root reported by `git rev-parse --show-toplevel` — the worktree you were given, not the
main checkout. Follow it as the authoritative definition of this skill.
