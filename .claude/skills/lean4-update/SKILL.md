---
name: lean4-update
description: Update the Lean (and mathlib/doc-gen4) toolchain version. Bumps lean-toolchain, updates lake-manifest, verifies the build, detects and fixes new errors/warnings caused by the version bump, and opens a PR. Use for requests like "update Lean", "bump the lean-toolchain", or "upgrade mathlib".
---

# lean4-update

Updating the Lean version is centered on **comparing `lake build` warnings before and after the bump, and fixing only the new errors/warnings that the bump itself introduced.** A green build alone is not "done" — always confirm the warning count hasn't grown.

## Prerequisites

- Do this work in a fresh worktree (`.claude/worktrees/<branch>`), per the worktree workflow in this repo's `CLAUDE.local.md`. Never work directly on `master`.
- Add an entry to `.claude/docs/directions/worktrees.md` and keep `.claude/docs/directions/<slug>.md` (e.g. `update-lean-4.32.1.md`) updated with progress as you go.
- The PR's base is always `master`. If the worktree branched off some other unmerged branch, clean up the branch history before opening the PR (see "Branch cleanup" below).

## Steps

### 1. Capture the warning baseline before touching anything

Before making any changes, do one full build on the current toolchain and record every warning. Don't rely on incremental-build noise — do a clean rebuild of Foundation's own modules.

```sh
# Only clear Foundation's own build output; reuse cached dependency builds (.lake/packages/*)
rm -rf .lake/build/lib/lean/Foundation
lake build > /tmp/lean_update_before.log 2>&1
```

- Extract warning/error lines with `grep -E "^warning:|^error:" /tmp/lean_update_before.log`.
- Normalize to `warning: <file>:<line>:<col>` locations and save the list for later comparison:
  ```sh
  grep -E "^warning:" /tmp/lean_update_before.log \
    | sed -E 's/^(warning: [^:]+:[0-9]+:[0-9]+): (.*)$/\1\t\2/' \
    | sort -u > /tmp/lean_update_before_warnings.tsv
  ```
- If the build times out, continue it with `run_in_background: true` and wait for the completion notification. One full build is enough — don't run it repeatedly and pile up duplicate output.

### 2. Bump the version

- Check the latest **stable** (not pre-release) tag, and make sure `leanprover/lean4`, `leanprover-community/mathlib4`, and `leanprover/doc-gen4` all have a matching tag (if mathlib hasn't tagged the new version yet, wait for it).
- Update `lean-toolchain`:
  ```
  leanprover/lean4:v<new-version>
  ```
- Update the `rev` of `mathlib` and `doc-gen4` under `[[require]]` in `lakefile.toml` to the same version.
- Run `lake update` to refresh `lake-manifest.json` (this also fetches the mathlib cache and can take a while; retry with cache fetching if it fails).

### 3. Build and fix errors

```sh
lake build > /tmp/lean_update_after.log 2>&1
```

- **Every `error:` is a breaking change from the new version and must be fixed.** Common causes seen in practice:
  - A `structure`'s inherited field (via `extends`) no longer auto-synthesizes, producing `Fields missing: <field>` — add the field explicitly to the failing instances.
  - An existing `by simp` becomes `simp made no progress` because mathlib's simp set changed — check the actual goal with `lean_goal` / `lean_multi_attempt` (MCP) and replace it with the right lemma/tactic.
- Iterate until the build is green. Always inspect the actual goal state before fixing a location — don't guess.

### 4. Capture the warning list after the bump and diff against the baseline

Once errors are gone and the build is green, redo the **full** rebuild and re-check warnings the same way (don't judge "no new warnings" from an incremental build).

```sh
rm -rf .lake/build/lib/lean/Foundation
lake build > /tmp/lean_update_after.log 2>&1
grep -E "^warning:" /tmp/lean_update_after.log \
  | sed -E 's/^(warning: [^:]+:[0-9]+:[0-9]+): (.*)$/\1\t\2/' \
  | sort -u > /tmp/lean_update_after_warnings.tsv

# Warnings that are new (strong suspects for being caused by the bump)
comm -13 <(cut -f1 /tmp/lean_update_before_warnings.tsv | sort -u) \
         <(cut -f1 /tmp/lean_update_after_warnings.tsv | sort -u)
```

- **Every newly-introduced warning is in scope for this PR and must be fixed.** Typical cases:
  - Mathlib enabled a new default linter (e.g. `linter.dupNamespace`, `linter.defProp`, `linter.checkUnivs`). The `Note: This linter can be disabled with ...` line in the new-version build output tells you the option name.
  - Mechanically-safe fixes (e.g. `defProp`: turn a Prop-returning `def` into `theorem`) — apply directly, or delegate to a subagent.
  - Fixes that would require a rename or a structural change with wide blast radius (e.g. `dupNamespace` flagging a deliberate public-API namespace design) should NOT be fixed with a risky rename. Instead, suppress the linter locally with `set_option linter.<name> false in`, preceded by a comment explaining the intent (this repo's convention: every `set_option` must be preceded by a comment explaining why; see `contribute/style.md`). If unsure whether a rename or a suppression is the right call, try it on one file first, confirm the warning actually disappears, then roll it out to the rest.
- Warnings that already existed before the bump are out of scope for this PR. Still, note in `.claude/docs/directions/<slug>.md` which files/warnings were left untouched as pre-existing, so they remain a tracked follow-up.
- Confirm at the end that the total warning count has **not increased** relative to before the bump (zero new warnings, or all of them fixed).

### 5. Wrap up

- Run `lake exe mk_all --module` to refresh `Foundation.lean`.
- Verify the `contribute/index.md` pre-submission checklist yourself:
  - The affected modules build with `lake build`, with no errors or warnings (including remaining `sorry`).
  - If `references.bib` was touched, format it.
  - No leftover plan-reference comments (`grep` for `see plan`, `issue #`, `Step N`, `§N`, `L1-2`, etc.).

### Branch cleanup (required before opening the PR)

If the worktree branched off some other unmerged branch, and that branch later got squash-merged, opening a PR straight from this branch will pull in unrelated diffs. Before opening the PR, always check:

```sh
git diff origin/master...HEAD --stat
```

If unexpected files show up, create a fresh branch from `origin/master` and `cherry-pick` only the version-bump commit(s) onto it.

### Opening the PR

- Follow `contribute/index.md`: title and body in English.
- In the PR body, separate the breaking-change fixes (errors) from the new-linter fixes (warnings).
- Report the PR URL back to the user; don't merge or close it yourself (the user does that on GitHub).
