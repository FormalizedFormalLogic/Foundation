# Contributing to Foundation

How to contribute to Foundation: the flow to `master`, PR/commit titles, pre-submission checks, and disclosure of AI involvement. For the coding conventions of the Lean sources, see [style.md](./style.md).

Items marked 🤖 are especially directed at AI coding agents.

## How changes land on `master`

All changes to `master` go through GitHub pull requests. PRs are always squash-merged, so the PR title becomes the commit message on `master` — hence the title convention below.

## PR titles and commit convention

PR titles are in English, in the usual conventional-commit form:

```
<type>(scope): <subject>
```

`<type>` is one of the following (do not use `feat`):

| type | meaning |
| --- | --- |
| `add` | new results, definitions, theorems |
| `fix` | fixing something misformalized |
| `refactor` | renaming/organizing; existing facts essentially unchanged |
| `doc` | documents |
| `ci` | GitHub Actions |
| `chore` | other maintenance (e.g. version-up) |

`scope` is optional; specify the affected module (`FirstOrder`, `Modal/Kripke`, …) if needed, following precedents in `git log --oneline`.

For `<subject>`, name one representative result of the PR; no verb phrases like "formalize the …" — write "Strict arithmetical hierarchy theorem", not "formalize the strict arithmetical hierarchy theorem".

PRs (title and body) are written in English.

## Before submitting

- The affected modules build with `lake build`, with no errors or warnings (including remaining `sorry`).
- 🤖 Run `just axiom-audit` and confirm it passes before submitting a PR. This checks sorry-freeness and the axiom allowlist across the project, and CI re-runs it on every PR — a failing audit blocks the merge.
- Run import-all to keep `Foundation.lean` up to date:
  ```shell
  lake exe mk_all --module
  ```
- If you added entries to `references.bib`, format it:
  ```shell
  bibtool -r .bibtoolrsc -i references.bib -o references.bib
  ```
- 🤖 No development-time artifacts survive in the code — plan references, issue numbers, step numbers, stale skeleton-era comments. See [style.md](./style.md#stale-comments-and-planning-artifacts).

## Disclosing AI involvement

🤖 Whenever an AI agent was involved in producing the changes — fully generated or merely assisted — this must be disclosed in the contribution itself:

- every commit created with an AI agent carries a co-author trailer, e.g.
  ```
  Co-Authored-By: Claude <noreply@anthropic.com>
  ```
- the PR states in natural language (in the body, or in the title if appropriate) that an AI agent was used.
