# Downstream migration guide

This guide applies the indexed hierarchy API now present in the working tree. It is
intended for small coding agents handling assigned downstream files. The recorded
baseline is a scoped `lake build --wfail` through
`Arithmetic.Definability.Absoluteness` and `StrictDefinable`, including their common
dependencies. Remaining downstream consumers have not been validated. The current
instruction is documentation-only: this guide does not authorize a build or code edits.

## Start safely

Before touching code, read `AGENTS.md`, `contribute/style.md`, and
`contribute/refactoring.md`. Read `instruction.md` for the mathematical boundaries and
the current accepted API. Treat the existing staged and unstaged changes as owned work:
inspect `git status --short`, do not reset, restore, stage, or reformat unrelated files.
Read-only inspection of any file or diff is permitted; coordinate with the assigned owner
before editing a file another contributor owns.

The root user assigns file ownership and a single build coordinator. Edit only your
assigned files, and report completion before taking another file. Do not run full or
downstream builds, including a targeted Lean build, until the user authorizes a
verification phase. The coordinator cannot override this user constraint. Read-only
review commands such as `git diff --check` and source scans are allowed. Routine
elaboration failures belong in the migration report; ask the
coordinator only when an error indicates a real missing API or mathematical requirement.
Give the exact file and declaration, smallest error/type/location excerpt, a minimal
reproduction, and the proposed API-level fix.

Use `rg` to find references, then inspect each result. Matches can be raw hierarchy
syntax, comments, strings, metaprogram quotations, or theory names; do not apply a global
replacement. Compare the affected declaration with `git show master:<path>` before
changing a proof. Prefer its concise proof under the new API, and preserve unrelated
branch work. Keep changed Lean lines within 100 columns and do not add trailing
semicolons.

## Core API and scopes

There is one indexed symbol type:

```lean
FFL.FirstOrder.Bounding.HierarchySymbol ℬ
```

`ℬ` is a phantom type parameter, not a stored field. The shared formula and definability
definitions live in `Bounding.HierarchySymbol` and its subnamespaces. General notation
uses an explicit bounding; arithmetic notation specializes the same constructor to
`ℬ[<, ℒₒᵣ]`.

Add the narrow scopes required by each notation family:

```lean
open scoped FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Bounding
```

The shared scope is named `Bounding`. Arithmetic notation is scoped under `Arithmetic`.
Do not introduce broad namespace opens to make old names resolve. If syntax remains
ambiguous, qualify the reference or use a narrow scope in the relevant section.

| Meaning | General bounding | Arithmetic specialization |
| --- | --- | --- |
| Sigma, Pi, Delta, arbitrary polarity at rank `i` | `𝚺-[ℬ, i]`, `𝚷-[ℬ, i]`, `𝚫-[ℬ, i]`, `Γ-[ℬ, i]` | `𝚺ᴬ-[i]`, `𝚷ᴬ-[i]`, `𝚫ᴬ-[i]`, `Γᴬ-[i]` |
| Named ranks zero and one | `𝚺-[ℬ, 0]`, etc. | `𝚺ᴬ₀`, `𝚷ᴬ₀`, `𝚫ᴬ₀`; `𝚺ᴬ₁`, `𝚷ᴬ₁`, `𝚫ᴬ₁` |
| General indexed type | `HierarchySymbol ℬ` | `HierarchySymbol ℬ[<, ℒₒᵣ]` |
| Formula and sentence wrappers | `ℌ.Semiformula ξ n`, `ℌ.Semisentence n`, `ℌ.Sentence` | Same receiver notation on `𝚺ᴬ₁`, etc. |

The old context-dependent `Γ-[i]` family has no common meaning. In general code, write
the bounding explicitly. In Arithmetic, use the `ᴬ` notation. This language is fixed to
`ℒₒᵣ`: an arbitrary language with `<` does not support the arithmetic operations,
`𝗣𝗔⁻`, or arithmetic completeness.

Do not confuse indexed hierarchy notation with theory constants such as `𝗜𝚺₁` or
`𝗜𝚺₀`. Do not replace every textual occurrence of Sigma notation. Likewise distinguish
the object language `L` in bootstrapping/incompleteness syntax from the arithmetic coding
language `ℒₒᵣ` used by the indexed symbol.

## Formula and definability argument inference

For formula wrappers and `Definable`, let Lean infer the language and bounding from the
symbol receiver:

```lean
ℌ.Semiformula ξ n
ℌ.Semisentence n
ℌ.Definable P
ℌ.DefinableFunction f
```

Do not pass a redundant explicit `ℬ` after `ℌ`. The shared `Defined` family infers its
symbol from the formula argument. The generic `DefinedFunction f φ` does the same, so
the canonical fully qualified form is
`Bounding.HierarchySymbol.DefinedFunction f φ`.

The arity aliases intentionally differ: `DefinedPred`, `DefinedRel`, and
`DefinedFunction₀` through `DefinedFunction₅` take the hierarchy symbol explicitly.
The notation families such as `Γ-Function₁ f via φ` are usually the clearest client
form. Do not uniformly remove a symbol argument from every alias.

Shared notation is declared once in the common definability module. Use its notation
families for predicates, relations, functions, `via` forms, and explicit models, for
example `Γ-Relation[V] R via φ`. Do not redeclare Arithmetic copies.

## Namespace migration map

The canonical receiver namespace now owns declarations, including arithmetic
specializations. Use an `arithmetic_` prefix when the result genuinely depends on the
arithmetic bounding or arithmetic laws.

| Old/general or arithmetic-facing name | Current ownership / spelling |
| --- | --- |
| Hierarchy symbol, wrappers, common definability | `Bounding.HierarchySymbol` and its existing child namespaces |
| Formula operations and properness | `Bounding.HierarchySymbol.Semiformula` and its `ProperOn` / `ProperWithParamOn` namespaces |
| Common definability closure and graph conversion | `Bounding.HierarchySymbol.Definable`, `Defined`, `DefinedFunction`, and related existing receiver namespaces |
| Arithmetic indexed-formula result | Canonical receiver namespace, `arithmetic_` prefix; e.g. `Semiformula.ProvablyProperOn.arithmetic_ofProperOn` |
| Arithmetic definability specialization | `Bounding.HierarchySymbol.Definable.arithmetic_*` |
| Arithmetic bound types and their methods | `Arithmetic` / `DefinableBoundedFunction` as currently declared |
| Embeddings, raw hierarchy, and generic absoluteness | Existing `Bounding` namespaces |
| Arithmetic casts, models, completeness, order laws | `Arithmetic` |

There is no `Arithmetical` namespace for methods on the shared indexed receiver. Do not
restore an Arithmetic facade, copied `HierarchySymbol`, copied definability aliases,
`CompatibleLE`, or an Arithmetic `Basic.Monotone` module. That module was deleted; import
`Tarski.Monotone` where needed. Generic methods such as `and`, `or`, `comp`, `graph_delta`,
`var`, and `const` need no Arithmetic forwards when their argument types already
specialize them. Retain arithmetic-specific methods that select `<` or rely on arithmetic
laws, with their current `arithmetic_` names.

Field notation follows the receiver. For example, use
`hP.arithmetic_bounded_comp₁ hf` when `hP` is the predicate instance, or
`hF.definable.arithmetic_bounded_comp hf` for a definable function with a bounded
argument. Instance binders are intentionally supplied by typeclass inference. Some
generic arity adapters may need a qualified call to disambiguate namespaces; qualify the
existing declaration rather than adding a forwarding theorem.

## Arithmetic helper map

These helpers remain in the common indexed receiver API and are specialized to
`ℬ[<, ℒₒᵣ]`:

| Helper | Use |
| --- | --- |
| `Semiformula.arithmetic_ball`, `arithmetic_bexs` | Construct strict-order bounded universal / existential indexed formulas |
| `Semiformula.val_arithmetic_ball`, `val_arithmetic_bexs` | Simplify their underlying first-order formulas |
| `Definable.arithmetic_ball`, `arithmetic_bexs` | Close definability under arithmetic semiterm bounds `< t` |
| `Definable.arithmetic_ball'`, `arithmetic_bexs'` | Close under `≤ t`, using the successor bound and `𝗣𝗔⁻` |
| `Definable.arithmetic_ballCons`, `arithmetic_bexsCons` | Bounded closure when the variable is consed onto the assignment |
| `Definable.arithmetic_ball_lt`, `arithmetic_bexs_lt` | Bound by a definable function; the function is Sigma at successor rank |
| `Definable.arithmetic_ball_le`, `arithmetic_bexs_le` | `≤` versions; require the arithmetic model assumption |
| `Definable.arithmetic_ball_lt'`, `arithmetic_ball_le'` | Implicit-binder universal forms |
| `Definable.arithmetic_sigma_succ_induction` | Arithmetic Sigma successor induction; retain its full bounded-quantifier cases |
| `Definable.arithmetic_bounded_substitution` | Substitute a vector of arithmetic bounded functions |
| `Definable.arithmetic_bounded_comp₁` … `₄` | Compose a definable predicate/relation with bounded arguments |
| `Definable.arithmetic_bounded_comp₁_zero` … `₄_zero` | Rank-zero versions for an arbitrary polarity symbol |
| `DefinableFunction.arithmetic_bounded_comp` | Compose a definable function with a vector of bounded functions |
| `DefinableFunction₁` … `₃.arithmetic_bounded_comp` | Arity conveniences for one to three bounded arguments |
| `Definable.arithmetic_ball_mem`, `arithmetic_bexs_mem` | Set-membership bounded variants in `Exponential/Bit.lean` |

The following mappings apply only to the old Arithmetic/Arithmetical specializations.
The shared common declarations such as `Definable.sigma_succ_induction`, `ball`, and
`bexs` remain available under their existing names.

| Earlier name | Current name |
| --- | --- |
| `bcomp₁` … `bcomp₄` | `Definable.arithmetic_bounded_comp₁` … `arithmetic_bounded_comp₄` |
| `bcomp₁_zero` … `bcomp₄_zero` | `Definable.arithmetic_bounded_comp₁_zero` … `arithmetic_bounded_comp₄_zero` |
| Function `bcomp` with a vector of inputs | `DefinableFunction.arithmetic_bounded_comp` |
| `ball_blt`, `bexs_blt` | `Definable.arithmetic_ball_blt`, `arithmetic_bexs_blt` |
| `ball_ble`, `bexs_ble` | `Definable.arithmetic_ball_ble`, `arithmetic_bexs_ble` |
| `ball_blt_zero`, `bexs_blt_zero` | `Definable.arithmetic_ball_blt_zero`, `arithmetic_bexs_blt_zero` |
| `ball_ble_zero`, `bexs_ble_zero` | `Definable.arithmetic_ball_ble_zero`, `arithmetic_bexs_ble_zero` |
| `bexs_vec_le_boldfaceBoundedFunction` | `Definable.arithmetic_bexs_vec_le_boundedFunction` |
| `substitution_boldfaceBoundedFunction` | `Definable.arithmetic_bounded_substitution` |
| `sigma_succ_induction` | `Definable.arithmetic_sigma_succ_induction` |
| `ProvablyProperOn.ofProperOn` | `Semiformula.ProvablyProperOn.arithmetic_ofProperOn` |

Check the receiver and current file before applying a mapping; qualify the declaration if
its short name is ambiguous.

Arithmetic-specific instances also use the prefix in their receiver namespaces:

| Earlier instance | Current instance |
| --- | --- |
| `le` | `DefinableRel.arithmetic_le` |
| `add`, `hAdd` | `DefinableFunction₂.arithmetic_add`, `arithmetic_hAdd` |
| `mul`, `hMul` | `DefinableFunction₂.arithmetic_mul`, `arithmetic_hMul` |
| `sq`, `pow3`, `pow4` | `DefinableFunction₁.arithmetic_sq`, `arithmetic_pow3`, `arithmetic_pow4` |

Respect the receiver namespace in the file; the table shortens the common prefix
`Bounding.HierarchySymbol`. The generic and arithmetic composition adapters can coexist;
choose the one whose hypotheses match the client. For substitution of a `Definable`
hypothesis, use the existing definable receiver or function adapter rather than inventing
a `hf` receiver. For bounded predicate composition, the receiver is the predicate
instance and the function-bound proof is the explicit argument.

## High-risk client areas

| Area | Migration guidance |
| --- | --- |
| `Arithmetic/Collection/Equiv.lean` | Preserve the concise proof around `arithmetic_sigma_succ_induction`; inspect binder order and expected types before adding annotations. |
| `Arithmetic/Bootstrapping/Syntax/Theory.lean` | Avoid namespace opens that shadow `Theory` or `Semiformula`. Keep `singleton.mem_iff`, `ofList`, and `insert` in their concise `simp` / `by ext; simp` forms. |
| `Arithmetic/Bootstrapping/Syntax/Formula/Basic.lean` | Remove temporary typed hypothesis copies when the shared `DefinedFunction` head now infers from its formula. Keep object-language `L` distinct from `ℒₒᵣ`. |
| `Arithmetic/HFS/PRF.lean`, `Bootstrapping/Syntax/Term/Basic.lean` | Use common graph conversion. Do not restore the removed arithmetic `DefinedFunction.graph_delta` wrapper. |
| `Arithmetic/Exponential/Bit.lean` | `arithmetic_ball_mem` and `arithmetic_bexs_mem` live on common `Definable`; distinguish coding membership facts from hierarchy notation. |
| Incompleteness and provability logic | Migrate only indexed hierarchy expressions and notation scopes. Preserve theory names, object-language formulas, assumptions, and raw hierarchy statements. |

For arithmetic bounded quantifier closure lemmas such as `arithmetic_ball_lt`,
`arithmetic_ball_le`, and their existential counterparts, preserve the original
quantified formula type `Γ : SigmaPiDelta`, including Delta. Do not narrow those binders
to `Polarity`: this changes the elaborated type and has broken Aesop matching downstream.
Preserve each other declaration's original binder too; raw hierarchy induction can
legitimately use `Polarity`, and `arithmetic_sigma_succ_induction` has a fixed Sigma
conclusion. Do not generalize or narrow binders uniformly.

Delta formulas retain separate Sigma and Pi representatives at the same rank. Keep
`ProperOn`, `ProperWithParamOn`, or `ProvablyProperOn` premises where present, including
graph conversion and absoluteness. Do not narrow a quantifier binder to simplify an
induction proof, replace Delta by an intersection predicate, or erase a representative's
properness proof. Preserve the distinction between `SigmaPiDelta` and `Polarity`.

## Work order and handoff

Migrate in dependency order: arithmetic definability and schemata, basic closure clients,
collection and induction, exponential/HFS, bootstrapping, then incompleteness and
provability logic. Use the import graph to adjust this order when needed. At each step:

1. Search and classify matches; identify indexed symbols separately from raw `Hierarchy`
   and theory names.
2. Compare declarations with `master` and first try the short proof under canonical
   notation and names.
3. Check scopes, expected types, receiver heads, and lost simp/automation registrations
   before changing proof structure.
4. Make only the assigned-file edits, preserve unrelated changes, and send the coordinator
   the changed declaration names plus any blocker details described above.

Do not run `lake build`, `just mk-all`, `just forgive`, or other build commands until the
user explicitly authorizes a verification phase. A coordinator assignment alone does not
grant authorization. Read-only scans and diff checks remain allowed. If later authorized,
the coordinator should state exactly which builds and repository checks to run.

For a final source audit, search and classify results in context rather than applying
global substitutions. For example:

```sh
rg -n -F -e 'Arithmetical' -e 'Arithmetic.HierarchySymbol' -e 'Γ-[' -e '𝚺-[' -e '𝚷-[' -e '𝚫-[' Foundation
rg -n 'bcomp|ball_blt|ball_ble|bexs_blt|bexs_ble|boldfaceBoundedFunction|ofProperOn' Foundation
rg -n 'HierarchySymbol|Hierarchy Γ|𝗜𝚺' Foundation/FirstOrder
git diff --check
```

Raw `Arithmetic.Hierarchy` and `SetTheory.Hierarchy` APIs are unchanged and should not be
redesigned here. Do not add Levy closure results or `CompatibleLE`; indexing the common
symbol does not establish those results.

## Completion report

For each assigned batch, report files and declarations migrated, any arithmetic-specific
results retained, remaining obsolete-name references (classified as real use or harmless
text), and blockers. Report relevant before/after line counts and percentage change for
the coherent proof blocks or modules, separating removed duplication from added common
functionality and unrelated branch work. State clearly that reference migration does not
establish downstream compilation. Validation status remains pending until separately
authorized and actually performed; do not imply that the scoped baseline build validates
downstream clients. Report completed reference migration separately from pending
validation, and name exactly which checks were performed.
