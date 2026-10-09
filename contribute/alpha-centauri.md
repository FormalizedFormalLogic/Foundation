# Porting from AlphaCentauri

How to bring results from [AlphaCentauri](https://github.com/FormalizedFormalLogic/AlphaCentauri), the sibling incubator repository, into Foundation. Read [index.md](./index.md) and [style.md](./style.md) first; this page only says how to apply them to a port.

Arithmetic is always ported from AlphaCentauri, never re-formalized from scratch.

## A port is a transplant

Copy statements and proofs, then adapt them to the house style. Do not generalize, reorder, or add lemmas that are not in the source, and do not weaken, strengthen, or restate what a declaration proves.

If a proof fails to compile after the move, fix it minimally and say what changed. If it cannot be fixed minimally, stop and report instead of reproving it another way. Long hand-computed estimates may be shortened by tagging monotonicity/bound lemmas with `@[gcongr]`, `@[simp]`, `@[grind]`, or `@[bound]` so the computation is closed by `gcongr`/`bound`/`grind`/`simp`.

Treat the AlphaCentauri checkout as read-only: `git pull` it before reading, and note the source commit in the PR.

## Never port anything resting on a disallowed axiom

The allowlist is `propext`, `Classical.choice`, `Quot.sound`. Anything reaching `sorryAx`, `Lean.ofReduceBool` (`native_decide`), or a bespoke `axiom` must not come over, even if it builds in AlphaCentauri. Check candidates with `#print axioms` (or `lean_verify`) before porting; port the clean part and leave the rest.

## Style adaptation

- Keep a short module docstring per file; delete per-declaration docstrings. Collect the source's citations into a `## References` section at the end of the module docstring (the key must exist in `references.bib`).
- Remove development-time artifacts: PR/issue numbers, plan steps, section labels, and proof-strategy comments. See [style.md](./style.md#stale-comments-and-planning-artifacts).
- Do not name declarations or files after vocabulary specific to one source (e.g. a nickname used by a single paper); use the general term and cite the source.
- Factor repeated binders into `variable` within scoped `section`s, keeping each declaration's implicit arguments unchanged (compare `#check @<name>` before and after).
- Prefer existing Mathlib/Foundation lemmas over ad-hoc steps. Reusable helpers are public declarations (none are `private` under `Foundation/Vorspiel/`).
- A small addition goes at the end of a related existing file, in a `section`, rather than in a new file.
- Every `set_option` has a comment saying why; never raise `maxHeartbeats` just to pass.
- Lines are at most 100 characters; count characters, not bytes.
- Refactor the result before submitting (shorten, remove inferable annotations, see [refactoring.md](./refactoring.md)).

## Placement

Put a file where its dependencies sit rather than mirroring AlphaCentauri's tree. Watch for import cycles through hand-curated aggregator modules (e.g. `Foundation/FirstOrder/Arithmetic/Basic.lean`). `Foundation.lean` is generated and flat.

## Checks before the PR

From the worktree root:

1. `lake build <module>` with `--wfail`: no errors or warnings.
2. `lake build Foundation`.
3. `just mk-all`: no diff in `Foundation.lean`.
4. `just forgive`.
5. No `sorry` in the ported files.
6. `lake shake --keep-public <module>`, dropping the imports it reports as redundant (not the project-wide `just shake`, which passes `--fix`).
7. No development-time artifacts (`grep -n "see plan\|issue #\|Step [0-9]\|§[0-9]\|L[0-9]-[0-9]\|PR [0-9]"`).

## Branch and PR

- Name the branch `alpha-centauri/<slug>`.
- Open the PR as a draft, labeled `Arithmetic`, `Alpha-Centauri`, and `AI-assisted`.
- Dependent ports are stacked PRs: base each on the previous branch.
