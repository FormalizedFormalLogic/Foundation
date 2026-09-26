# Refactoring hierarchical definability around an indexed hierarchy symbol

## Objective and guiding priority

Make `FFL.FirstOrder.Bounding.HierarchySymbol` a genuine structure parameterized by a
bounding `ℬ : Bounding L`. Use this parameter to infer the language and bounding in the
formula and definability APIs. Arithmetic must use these same definitions, specialized by
notation to `ℬ[<, ℒₒᵣ]`, without copying them into an Arithmetic namespace.

**Preserve the concise mathematical code on `master` wherever possible.** The current
branch already contains the generalization, but also contains adaptations made to work
around namespace and elaboration failures. Do not treat those adaptations as the desired
API. Repair the shared API so that short proofs remain short. This is an incremental
refactor of the existing implementation, not a reconstruction of the development.

The intended end state has:

- One definition of each hierarchy-indexed formula type and definability predicate.
- One copy of every genuinely general theorem, instance, and automation rule.
- Arithmetic-specific notation and genuinely arithmetic-specific results.
- Explicit, predictable names for specialized results.
- Downstream proofs close to `master`, with mostly notation and name changes.
- The same mathematical assumptions and the same interpretation of Delta classes.

This document describes the implementation task. Writing this document does not itself
authorize unrelated repository changes, commits, publication, or toolchain updates.

## 1. Establish the baseline before editing

Read `AGENTS.md`, `contribute/style.md`, and `contribute/refactoring.md`. Read
`contribute/index.md` before committing or submitting anything. Follow the repository's
proof-role delegation rules when applicable.

Record the current branch, HEAD, `master`, merge base, and working-tree/index status.
Inspect both committed branch changes and uncommitted changes. Useful read-only commands:

```sh
git status --short
git log -1 --oneline
git log -1 --oneline master
git merge-base master HEAD
git diff --stat master...HEAD
git diff
git diff --cached
git show master:Foundation/FirstOrder/Arithmetic/Definability/Definable.lean
```

The three-dot diff is relative to the merge base. It is not necessarily a list of changes
made for this refactor: the branch contains merged work on other topics. Compare individual
declarations with `git show master:<path>` as well. Do not reset files to `master`, undo
unrelated changes, or overwrite another contributor's edits. Preserve the existing staging
state unless staging is explicitly requested.

For each relevant changed declaration, classify the difference as one of:

1. Required generalization or specialization.
2. Necessary adaptation to the new canonical names or notation.
3. A workaround that can disappear after fixing inference or name resolution.
4. An independent change that must be preserved.

Do not optimize for the raw size of the whole branch diff, which includes unrelated work.
Measure the affected APIs and proof bodies separately.

## 2. Fixed mathematical boundaries

Keep the existing set-based bounding interface:

```lean
ℬ : Bounding L
R ∈ ℬ
ℬ.Closure φ
ℬ.Hierarchy Γ i φ
ℬ[<, L]
ℬ[∈, L]
```

Do not reintroduce `Bounding.ofOperator`, `BoundingOperator`, `Arithmetic.bounding`, or
`SetTheory.bounding`. Do not use `R ∈ ℬ.set` at call sites.

The change to `HierarchySymbol` does not change the inductive definition of
`Bounding.Hierarchy`. In particular, do not parameterize the initial class by an arbitrary
class `C`, redesign strict hierarchies, or strengthen closure properties as part of this
task.

Preserve the current Arithmetic interpretation of Delta:

- A Delta formula has separate Sigma and Pi representatives at the same rank.
- Its underlying formula is selected as in the current implementation.
- Equivalence of the representatives is expressed by `ProperOn`, `ProperWithParamOn`, or
  `ProvablyProperOn`, as appropriate.
- Keep the corresponding properness requirements in `Defined`, `IsDefinedByWithParam`,
  `Definable`, graph conversion, and absoluteness.

Do not replace this representation by an intersection predicate or require a uniform
equivalence proof in every formula constructor. Do not change the sorts of existing
classes or their constructive/noncomputable status incidentally.

Arithmetic term bounds, `Bounded`, `DefinableBoundedFunction`, and results using arithmetic
order laws stay in Arithmetic. Do not restore `CompatibleLE` in the common API. This does
not prohibit the existing common syntactic `Closure` or bounded-formula absoluteness.

Set theory will use the Levy hierarchy. Preserve the existing membership-bounding syntax
and its restrictions. Do not add arithmetic-style bounded-function infrastructure to set
theory or design a new quantifier-term restriction framework now. Any genuinely new Levy
closure result requires its own mathematical analysis.

## 3. Canonical definition of the symbol

Keep the canonical name:

```lean
FFL.FirstOrder.Bounding.HierarchySymbol
```

Its intended shape is:

```lean
structure HierarchySymbol {L : Language} (ℬ : Bounding L) where
  Γ : SigmaPiDelta
  rank : ℕ
```

The bounding is a phantom **parameter**, not a stored field. Use a real structure whose
type retains the parameter. Do not implement it as an `abbrev` that discards `ℬ`, as an
unindexed pair, or as a structure containing an existentially packaged bounding.

Keep `SigmaPiDelta`, `Polarity`, and their existing relationship. Distinguish variables in
signatures: for example, `Γ : SigmaPiDelta` versus `ℌ : HierarchySymbol ℬ`. Preserve the
current meaning of the `Γ` and `rank` projections.

Propagate universe parameters from the existing implementation. Do not restrict a general
language or variable type to the smallest universe simply to make an application work.

Different boundings give different symbol types. Do not add coercions between them. A
conversion of the two metadata fields would not justify transferring a formula or a
definability proof. Equality transport or monotonicity under inclusion can be developed
when a concrete application needs it; neither needs a new general framework here.

## 4. Notation and inference contract

### General symbols

Provide scoped notation under `Bounding` for:

```lean
Γ-[ℬ, i]
𝚺-[ℬ, i]
𝚷-[ℬ, i]
𝚫-[ℬ, i]
```

These must expand directly to the canonical constructor, with `ℬ` supplying its phantom
parameter. Check the generated constructor's binders before implementing the notation.
Support the existing uses with `Γ : Polarity` through the existing coercion, if required.

Do not keep a second, context-dependent interpretation of the old `Γ-[i]` syntax in the
final API. General code should identify its bounding explicitly in the symbol notation.

### Arithmetic symbols

Provide scoped notation under `Arithmetic`:

```lean
Γᴬ-[i]       -- Γ-[ℬ[<, ℒₒᵣ], i]
𝚺ᴬ-[i]
𝚷ᴬ-[i]
𝚫ᴬ-[i]
𝚺ᴬ₀  𝚷ᴬ₀  𝚫ᴬ₀
𝚺ᴬ₁  𝚷ᴬ₁  𝚫ᴬ₁
```

These are syntax for the common constructor, not new definitions of symbols, formula
types, or predicates. Verify tokenization, precedence, and constructor-pattern usage in
the initial pilot. Keep the distinction between arithmetic syntax and theory constants
such as `𝗜𝚺₁`; a textual replacement of every occurrence of Sigma notation is unsafe.

Fix Arithmetic notation to `ℒₒᵣ`. A language merely having `<` is not enough to support
addition, multiplication, `𝗣𝗔⁻`, or arithmetic completeness. Order-language results that
really hold for arbitrary `[L.LT]` should use `Γ-[ℬ[<, L], i]` directly.

Do not introduce a copied SetTheory symbol type. Explicit `Γ-[ℬ[∈, L], i]` is sufficient
for current generic checks. Add a separate scoped Levy shorthand only if a real consumer
needs it; it must also expand to the common constructor.

### Formula and predicate applications

The intended user-facing forms are:

```lean
-- General context: ℌ : Bounding.HierarchySymbol ℬ
ℌ.Semiformula ξ n
ℌ.Semisentence n
ℌ.Sentence
ℌ.Definable P
ℌ.DefinableFunction f

-- Arithmetic context
𝚺ᴬ₁.Semisentence n
𝚺ᴬ₁.Definable P
𝚫ᴬ₁.DefinableFunction f
```

`L` and `ℬ` are implicit parameters of these definitions, inferred from `ℌ`. Do not
retain a redundant explicit `ℬ` argument after the symbol. For definitions such as
`DefinedFunction` that infer their symbol from a formula argument, preserve that useful
argument inference too.

A bare rank and polarity cannot determine an arbitrary bounding without an expected
type. Do not conceal this fact with a default bounding, a global instance, or an
`outParam` workaround. The explicit general notation and fixed Arithmetic notation are
the solution.

Move the shared `-Predicate`, `-Relation`, `-Function`, and `via` notation families into
the common definability module. They must refer to the canonical definitions and accept
an indexed symbol. Include the existing explicit-model forms, such as `-Predicate[V]`.
Declare the notation once, with an appropriate scope, and update scope usage in clients.

## 5. Namespace ownership

Use the following namespace organization. File location and declaration namespace need
not coincide: specialized declarations remain in Arithmetic files.

| Content | Canonical namespace |
| --- | --- |
| Raw bounding syntax and hierarchy | `FFL.FirstOrder.Bounding` |
| Indexed symbol and shared definitions | `FFL.FirstOrder.Bounding.HierarchySymbol` |
| Formula operations and properness | `...HierarchySymbol.Semiformula` |
| Shared definability lemmas | `...HierarchySymbol.Definable`, `Defined`, etc. |
| Arithmetic-specific indexed-formula results | `...HierarchySymbol.Arithmetical.Semiformula` |
| Arithmetic-specific definability results | `...HierarchySymbol.Arithmetical.Definable`, etc. |
| Arithmetic bound types and their own methods | `FFL.FirstOrder.Arithmetic.Bounded`, etc. |
| Common embeddings and absoluteness | `FFL.FirstOrder.Bounding` and its existing subnamespaces |
| Natural casts, arithmetic models, completeness | `FFL.FirstOrder.Arithmetic` |

`...` in this table means `FFL.FirstOrder.Bounding`; it is not literal Lean syntax.
`Arithmetical` is a namespace, not a new type, typeclass, or copied hierarchy symbol.

For example, specialize a common type in a statement declared as:

```text
FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical.Definable.ball_lt
FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical.Semiformula.ProvablyProperOn.ofProperOn
```

The hypotheses and conclusions of these declarations use the canonical common types,
with their symbols restricted to `ℬ[<, ℒₒᵣ]`.

### Field notation policy

Common lemmas belong to the namespaces associated with their common receiver types.
Preserve useful calls such as `h.graph_delta`, `h.and h'`, `h.retraction e`, `φ.rew ω`,
and `h.proper` wherever supported by the existing API. Check the receiver's actual
declaration head, implicit binders, and reducibility when such a call fails.

Arithmetic-specific lemmas are deliberately grouped under `Arithmetical`. Lean does not
automatically search that namespace because a receiver happens to use an arithmetic
bounding. Use a qualified call to a specialized lemma when necessary. Do not add a second
forwarding theorem solely to obtain a shorter field name.

Do not copy generic `and`, `or`, `comp`, `graph_delta`, `var`, or `const` into
`Arithmetical`. Specialization follows from their argument types. Arithmetic-specific
bounded quantifier conveniences may remain when they select the `<` operator and remove
an operator-membership premise; those change the useful interface rather than merely
renaming a general theorem.

Avoid broad `open ...Semiformula` declarations to recover many old names at once. Prefer
receiver notation, narrow tested opens, or qualification at the use site. Namespace
changes can alter the interpretation of `Theory`, `Semiformula`, and related identifiers
even when the underlying mathematics is unchanged.

## 6. Definition and module consolidation

### Common formula wrappers

Edit `Foundation/FirstOrder/Tarski/HierarchicalDefinability/Hierarchy.lean` in place.

- Change the symbol parameter and notation.
- Adapt the indexed `Semiformula` constructors without changing their representation.
- Infer the bounding from the symbol in `Semisentence`, `Sentence`, and all operations.
- Preserve `.val`, `.sigma`, `.pi`, `ofZero`, `ofDeltaOne`, rewriting, substitution,
  logical operations, quantification, properness, and `graphDelta` behavior.
- Preserve the existing coercions and constructor proof defaults. Do not broaden the
  coercion graph merely to hide an inference problem.
- Update dependent matches and induction patterns carefully; an implicit phantom
  parameter is not an additional data field to destructure.

### Common definability

Edit `Foundation/FirstOrder/Tarski/HierarchicalDefinability/Basic.lean` in place.

Keep one canonical family of `IsDefinedBy`, `IsDefinedByWithParam`, `Defined`,
`Definable`, `DefinedPred`, `DefinedRel`, `DefinedFunction`, and their existing arity
variants. Arity conveniences in the shared API are useful; duplicate Arithmetic copies
of those conveniences are not.

Infer `ℬ` from the indexed symbol throughout. Preserve the distinction between a
specified defining formula (`DefinedFunction`) and existence of a defining formula
(`DefinableFunction`). Both have graph-related results: do not conflate their signatures
or ranks while moving names.

Keep general closure, retraction, composition, graph conversion, and rank-changing
proofs here. Port their existing proofs with the smallest changes that the new parameter
requires. Keep any genuinely necessary equality or structure hypotheses.

### Arithmetic formula and definability modules

In `Foundation/FirstOrder/Arithmetic/Definability/Hierarchy.lean`:

- Delete the copied `HierarchySymbol` type, constructor aliases, level constants, and
  copied `Semiformula`, `Semisentence`, and `Sentence` definitions.
- Introduce only the Arithmetic notation for indexed symbols.
- Keep the useful `<`-quantifier conveniences in the specialized namespace.
- Keep the arithmetic completeness result `ProvablyProperOn.ofProperOn` specialized to
  the existing arithmetic models and theories. Move its name under `Arithmetical`.

In `Foundation/FirstOrder/Arithmetic/Definability/Definable.lean`:

- Delete the copied definability and definedness families.
- Delete forwarding wrappers for general logical closure, composition, graph conversion,
  variables, constants, and other results obtained by supplying only the bounding.
- Use the single shared notation family instead of redeclaring it for arithmetic aliases.
- Retain arithmetic interpretations of addition, multiplication, powers, and order.
- Retain results depending on arithmetic order laws, successor bounds, or arithmetic
  theories. Put the indexed definability results under `Arithmetical`.
- Preserve useful specialization lemmas only when they actually simplify a recurring
  arithmetic interface, and document the reason in the implementation report.

The recent Arithmetic `DefinedFunction.graph_delta` wrapper must disappear. Its original
motivation was the duplicate declaration heads and field-notation resolution. Fix that
cause through the common indexed API rather than maintaining another wrapper.

### Bounded functions and absoluteness

`Arithmetic/Definability/BoundedDefinable.lean` retains its arithmetic bound types and
proofs. Change its hierarchy symbols and canonical definability references. Put specialized
lemmas whose subject is the shared indexed definability API under `Arithmetical`; methods
whose subject is an arithmetic-specific bound type stay with that type.

`Tarski/HierarchicalDefinability/Absoluteness.lean` retains `Bounding.IsInitial` and the
general embedding-based results. Its raw `Closure`/`Hierarchy` statements need no phantom
parameter redesign. Adapt only statements using indexed formula wrappers and definitions.
Do not weaken the operator preservation, initiality, or model-specific properness premises.

`Arithmetic/Definability/Absoluteness.lean` retains `natCastEmbedding`, its initiality
instance, numeral substitution, and arithmetic completeness. Natural-cast corollaries may
remain when they express the concrete Arithmetic interface and discharge embedding
hypotheses. Do not copy the general proofs into them.

`Arithmetic/Basic/Monotone.lean` has already been removed. Keep it removed. Import
`Tarski.Monotone` where its declarations are needed; do not recreate an empty compatibility
module under the deleted name.

### Lower syntactic hierarchy APIs

`Arithmetic/Basic/Hierarchy.lean` and `SetTheory/Basic/Hierarchy.lean` concern raw formulas.
Their `Hierarchy` and `DeltaZero` specializations are distinct from the copied
`HierarchySymbol` API being removed. Do not redesign these modules wholesale.

Keep existing short domain-specific statements useful to `master` clients. Audit redundant
constructor/recursor aliases only where necessary for this migration; do not create a new
parallel recursor API. If induction breaks, examine the canonical inductive predicate and
its actual constructor arguments before adding wrappers. Preserve any real restrictions
or differences between raw arithmetic, strict arithmetic, and membership hierarchies.

### Imports

The dependency direction remains:

```text
Syntax/Classical/Bounding and BoundingHierarchy
    -> Tarski/HierarchicalDefinability/Hierarchy
    -> Tarski/HierarchicalDefinability/Basic
    -> Tarski/HierarchicalDefinability/Absoluteness
```

Arithmetic modules import these common modules and their required arithmetic background.
Common modules must not import Arithmetic or SetTheory. Arithmetic notation is declared
only after the arithmetic language is available. Avoid creating an import cycle to expose
a shorter name.

## 7. Keep downstream code close to master

For every affected consumer, first read the corresponding `master` declaration. Attempt
its proof with the new notation and canonical names before retaining a longer branch proof.

If a formerly short proof fails, investigate in this order:

1. Name resolution and active notation scopes.
2. Missing expected types or a badly placed explicit/implicit parameter.
3. A receiver type still headed by an obsolete alias.
4. Existing simp lemmas, instances, and automation registrations lost during the move.
5. A genuine change in the elaborated statement or in the needed mathematical assumptions.

Only the last item should motivate a different mathematical proof. Do not react to the
first four by expanding every client proof, adding annotations everywhere, or inserting
typeclass forwarding instances.

Pay particular attention to:

- `Arithmetic/Bootstrapping/Syntax/Theory.lean`: retain the concise `singleton.mem_iff`,
  `ofList`, and `insert` proofs. Removing a broad namespace open already allowed these to
  return to `simp` and `by ext; simp`. A small `by intro; rfl` properness proof is acceptable.
- `Arithmetic/HFS/PRF.lean` and `Bootstrapping/Syntax/Term/Basic.lean`: common graph
  conversion should work without an Arithmetic copy of `DefinedFunction` or its theorem.
- `Bootstrapping/Syntax/Formula/Basic.lean`: avoid retaining local typed copies of hypotheses
  whose only purpose was to expose the general `DefinedFunction` head.
- `Arithmetic/HFS/Fixpoint.lean`, collection, induction, and definability consumers: preserve
  their short compositions and uses of `by definability`.
- Incompleteness and provability-logic files: migrate relevant syntax only. Preserve
  independent changes elsewhere in the branch.

Use the existing module boundaries. A user requesting fewer wrappers has not requested a
new framework, new facade modules, or a replacement hierarchy of helper structures.

## 8. Instances, simp, and automation

Retain a single canonical class head for each shared property. Arithmetic instances must
produce that class specialized to an arithmetic symbol, not a copied class.

Audit `[simp]`, `[aesop ... (rule_sets := [Definability])]`, coercions, and rank-normalizing
instances as declarations move. Register general rules once in the common modules and
arithmetic-only rules in the arithmetic modules. Preserve priorities unless a demonstrated
failure requires changing them.

Check that existing zero-rank and successor-rank inference still works. Do not invent an
instance that guesses the bounding, a second `Tarski.Structure` for arithmetic models, or
a self-reproducing instance to make a failed search pass. Use the existing `ORingStructure`
bridge and its coherence conventions.

The phantom parameter does not by itself solve every field-notation or automation issue.
When `h.graph_delta` or `by definability` fails, inspect the elaborated type and rule
signature. Resolve the cause in the canonical API before adding a downstream workaround.

## 9. Implementation sequence and checkpoints

### Phase A: inventory and a small API pilot

Make a declaration migration table using the categories above. Identify true arithmetic
results before deleting wrappers. Prototype the phantom symbol, notation, and representative
definitions in a small temporary module or a tightly scoped first edit.

Confirm the following before converting the whole tree:

- `Γ-[ℬ, i]` and Arithmetic notation construct the intended canonical symbol.
- `ℌ.Semiformula ξ n` and `ℌ.Definable P` infer both language and bounding.
- Constructor notation and dependent matches work at Sigma, Pi, and Delta.
- The canonical `DefinedFunction.graph_delta` can be used by field notation from an
  arithmetic-specialized hypothesis, including rank zero.
- A shared closure lemma works with both order and membership boundings.
- Arithmetic and SetTheory imports can coexist without changing notation meaning.

Temporary pilot declarations must not survive as an additional public API.

### Phase B: migrate the common implementation

Update `Hierarchy.lean`, then `Basic.lean`, then the common absoluteness module. Preserve
proof bodies and simplification behavior. Establish the final shared notation here.

### Phase C: remove the Arithmetic facade and organize specialization

Introduce Arithmetic symbol notation, delete copied types and forwarding lemmas, and move
genuinely specialized results to the namespaces specified above. Update bounded functions,
natural-cast results, and their automation registrations.

This phase may temporarily break clients; do not solve that by preserving a second public
copy of the old API. Migrate clients in the next phase and remove temporary scaffolding.

### Phase D: migrate consumers in dependency order

Start with arithmetic definability, schemata, and basic closure consumers. Continue through
collection/induction, exponential/HFS, bootstrapping, incompleteness, and provability logic.
Use the actual import graph to settle ordering rather than relying only on this outline.

At each step, compare the proof with `master` and prefer its concise structure. Distinguish
raw hierarchy notation from indexed-symbol notation. Update explicit-model notation,
coercions, and namespace-qualified references as well as ordinary theorem statements.

### Phase E: audit and verify

Search the final tree for the removed Arithmetic type aliases and generic forwarding
lemmas, old symbol notation declarations, obsolete imports, and redundant registrations.
Inspect actual matches: many raw hierarchy uses and arithmetic theory names must remain.

Review all relevant changed declarations against `master`, not only the most recently
edited files. Review the general modules as adaptations of the original concise proofs.
Explain every substantial proof-size increase that remains.

## 10. Verification policy

Use the user's latest verification constraints. For the eventual implementation, prefer
`lake build` to repeatedly building long dependency chains through individual targets.
Small Lean/LSP checks are appropriate for the API pilot and for isolating an elaboration
failure; they are not a substitute for final integration verification.

Once the tree is coherent, run the repository's warning-as-error build:

```sh
lake build --wfail
```

Before submission, run the required checks from `contribute/index.md`, including
`just mk-all` and `just forgive`. If import generation changes `Foundation.lean`, ensure
that final state is included in build verification. Preserve unrelated import entries.
Do not change the Lean/mathlib versions, suppress warnings, or introduce `sorry` or axioms.

Validate meaningful API behaviors, not a collection of tests that merely repeats the new
implementation. Existing consumers are the main integration evidence. Explicitly exercise:

- Shared field notation and graph conversion in arithmetic clients.
- `simp` for values of constructors, rewriting, connectives, and properness.
- Existing `by definability` proofs, including bounded quantifiers and composition.
- Class inference and coercions at ranks zero, one, and a variable successor rank.
- General statements with a non-arithmetic bounding.
- The two different `graph_delta` APIs for defined and definable functions.
- Natural-cast absoluteness with its existing assumptions and Delta properness proofs.

After checks pass, rerun only when subsequent edits or a concrete remaining risk require
it. Report exactly what was checked. Do not claim that a check of one file validated the
whole tree.

## 11. Formatting and proof discipline

Keep Lean lines at most 100 characters. Break before or after complete binders such as
`(h : ...)`, and after the statement's colon when appropriate. Keep short type applications,
function applications, notation tokens, and lambda binders together. A scan only for
`(h :` at the end of a line is insufficient; inspect all changed multiline declarations.

For example, prefer:

```lean
lemma example_name (long_argument : SomeType)
    (h : CompleteHypothesis) :
    CompleteConclusion := by
  ...
```

Do not split `Semiformula L ξ n`, `ℬ[<, ℒₒᵣ]`, a short function type, or a lambda expression
just to fill the previous line. Review branch-added awkward wrapping in downstream files
such as `HFS/Fixpoint.lean` as well as the common definability modules.

Do not add trailing semicolons after commands or `end`. Preserve concise existing proof
idioms where compatible with current lint rules. Use direct terms when a lemma application
suffices. Prefer field notation when its receiver and target declaration are unambiguous.
Do not hide unresolved design problems with `set_option`, large proof scripts, redundant
aliases, or repeated casts.

## 12. Completion criteria and implementation report

The refactor is complete when:

1. `HierarchySymbol ℬ` is the single canonical indexed symbol type.
2. Shared formula and definability APIs infer bounding and language from the symbol.
3. Arithmetic uses notation for the common symbols and has no copied symbol/definability
   type families or generic theorem facade.
4. Arithmetic-specific results have the documented ownership and retain their assumptions.
5. General graph conversion and logical closure require no Arithmetic forwarding lemmas.
6. Delta semantics, existing formula values, and the arithmetic mathematical results are
   preserved; no unsupported Levy closure claims have been introduced.
7. Downstream proofs follow the concise `master` forms except for justified API adaptations.
8. Namespace problems have not been converted into repeated manual proofs or type casts.
9. Existing automation and the required integration checks pass without new warnings.
10. No temporary compatibility layer, obsolete imports, or duplicate instances remain.

Report the namespace and notation changes, deleted wrapper families, genuinely specialized
APIs retained, and verification performed. Include before/after line counts and percentage
changes for affected modules or coherent proof blocks, separating deleted duplication from
new general functionality and from unrelated branch changes. State any remaining increase
in downstream proof size and why it is necessary.

Do not claim byte-for-byte compatibility with the previous declarations: their indexed
types, notation, and qualified names intentionally change. The preservation target is the
mathematical content, computational behavior of the formula wrappers, and concise client
proofs under the new API.
