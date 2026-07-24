module

public import Foundation.FirstOrder.Basic.Coding
public import Foundation.Vorspiel.Computability
public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Incompleteness.RosserProvability
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import Foundation.FirstOrder.Incompleteness.Halting
public import Mathlib.Computability.Reduce

/-!
# Church's undecidability theorem

`church_theoremAux` shows that for every arithmetic theory `T ⊇ 𝗥₀` sound on `𝚺₁` sentences, the
set of `T`-provable sentences is not computable, by a direct diagonalization on the self-applied
substitution `σ ↦ σ/[⌜σ⌝]` (no fixed-point/Gödel-numbering machinery beyond weak representability
of r.e. predicates, `re_complete`, is needed, unlike Gödel's first incompleteness theorem).
`church_theorem` specializes this to `T = ∅`: since `𝗣𝗔⁻` is finitely axiomatizable, `∅`-provability
computably many-one reduces `𝗣𝗔⁻`-provability to itself, removing the `𝗥₀ ⪯ T` and soundness
hypotheses needed by `church_theoremAux`.

This file is currently a skeleton: every helper lemma (`A2`-`A9`, `C1`-`C4` in the accompanying
proof plan) is stated with `sorry`; only `church_theoremAux` and `church_theorem` themselves have
complete proofs, assembled from those (sorry'd) facts.

- folklore; the standard proof of Church's theorem via undecidability of `𝚺₁`-completeness, see
  e.g. Rogers, *Theory of Recursive Functions and Effective Computability*, or Smoryński's chapter
  in the *Handbook of Mathematical Logic*.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open Bootstrapping Bootstrapping.Arithmetic

section Diagonalization

/-! ### Part I: Church's theorem for an arbitrary theory `T ⊇ 𝗥₀` -/

/-- A total function on `ℕ` whose graph is r.e. is computable. -/
lemma computable_of_graph_rePred {g : ℕ → ℕ} (h : REPred fun p : ℕ × ℕ ↦ p.2 = g p.1) :
    Computable g := by
  sorry

/-- A `𝚺₁`-definable binary relation on `ℕ` is r.e. -/
lemma rePred_of_sigma1_relation {R : ℕ → ℕ → Prop} (h : 𝚺₁-Relation R) :
    REPred fun p : ℕ × ℕ ↦ R p.1 p.2 := by
  sorry

/-- The code-level diagonal self-substitution: if `n` is the code of a `Semisentence ℒₒᵣ 1`,
`d n` is the code of its self-substitution `n/[⌜n⌝]`. This is `Bootstrapping.Arithmetic.substNumeral`
applied to `n` twice, i.e. the same expression as the `D` used in `Incompleteness/First.lean`. -/
noncomputable def d (n : ℕ) : ℕ := substNumeral (V := ℕ) n n

/-- The graph of `d` is `𝚺₁`-definable. -/
lemma d_graph_sigma1 : 𝚺₁-Relation fun n m : ℕ ↦ m = d n := by
  sorry

/-- `d` is computable. -/
lemma d_computable : Computable d := by
  sorry

/-- `d` applied to the code of `σ` is the code of `σ`'s diagonal self-substitution. -/
lemma d_quote_eq (σ : ArithmeticSemisentence 1) :
    d (⌜σ⌝ : ℕ) = (⌜(σ/[⌜σ⌝] : ArithmeticSentence)⌝ : ℕ) :=
  substNumeral_app_quote σ σ

/-- The diagonal substitution `σ ↦ σ/[⌜σ⌝]`. -/
noncomputable def f (σ : ArithmeticSemisentence 1) : ArithmeticSentence := σ/[⌜σ⌝]

/-- `f` is computable. -/
lemma f_computable : Computable f := by
  sorry

variable {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- If `T`-provability is computable, so is `σ ↦ T ⊬ f σ`. -/
lemma D_computable (hC : ComputablePred {σ : ArithmeticSentence | T ⊢ σ}) :
    ComputablePred (fun σ : ArithmeticSemisentence 1 ↦ T ⊬ f σ) := by
  sorry

/-- The diagonal fixed point for `σ ↦ T ⊬ f σ`: a sentence whose `T`-provability and
`T`-unprovability (after diagonal substitution) coincide, obtained from `codeOfREPred` and
`re_complete` applied to the decode-lifted predicate `σ ↦ T ⊬ f σ`. -/
lemma D_diagonal (hD : ComputablePred (fun σ : ArithmeticSemisentence 1 ↦ T ⊬ f σ)) :
    ∃ δ : ArithmeticSemisentence 1, (T ⊬ f δ) ↔ T ⊢ f δ := by
  sorry

/-- Church's theorem, for an arbitrary arithmetic theory `T ⊇ 𝗥₀` sound on `𝚺₁` sentences: the set
of `T`-provable sentences is not computable. -/
theorem church_theoremAux : ¬ComputablePred {σ : ArithmeticSentence | T ⊢ σ} := by
  intro hC
  obtain ⟨δ, hδ⟩ := D_diagonal (D_computable hC)
  by_cases h : T ⊢ f δ
  · exact hδ.mpr h h
  · exact h (hδ.mp h)

end Diagonalization

section PeanoMinusReduction

/-! ### Part II: Church's theorem for `T = ∅`, via a reduction through `𝗣𝗔⁻` -/

/-- `𝗣𝗔⁻` is finitely axiomatized. -/
lemma exists_peanoMinus_list :
    ∃ Γ : List ArithmeticSentence, ∀ σ, σ ∈ (𝗣𝗔⁻ : ArithmeticTheory) ↔ σ ∈ Γ := by
  sorry

open Classical in
/-- A fixed finite list of axioms for `𝗣𝗔⁻`, chosen once and for all from
`exists_peanoMinus_list`. -/
noncomputable def peanoMinusList : List ArithmeticSentence := exists_peanoMinus_list.choose

lemma mem_peanoMinusList_iff {σ : ArithmeticSentence} :
    σ ∈ (𝗣𝗔⁻ : ArithmeticTheory) ↔ σ ∈ peanoMinusList :=
  exists_peanoMinus_list.choose_spec σ

/-- `𝗣𝗔⁻` proves the conjunction of its own (finitely many) axioms. -/
lemma peanoMinus_provable_conj : (𝗣𝗔⁻ : ArithmeticTheory) ⊢ peanoMinusList.foldr (· ⋏ ·) ⊤ := by
  sorry

/-- The deduction theorem for the finite theory `𝗣𝗔⁻`: `𝗣𝗔⁻` proves `σ` iff `∅` proves the
conjunction of `𝗣𝗔⁻`'s axioms implies `σ`. -/
lemma peanoMinus_provable_iff (σ : ArithmeticSentence) :
    (𝗣𝗔⁻ : ArithmeticTheory) ⊢ σ ↔ (∅ : ArithmeticTheory) ⊢ peanoMinusList.foldr (· ⋏ ·) ⊤ 🡒 σ := by
  sorry

/-- The many-one reduction witness from `𝗣𝗔⁻`-provability to `∅`-provability,
`σ ↦ (conjunction of 𝗣𝗔⁻'s axioms) 🡒 σ`. -/
noncomputable def peanoMinusReduction (σ : ArithmeticSentence) : ArithmeticSentence :=
  peanoMinusList.foldr (· ⋏ ·) ⊤ 🡒 σ

/-- `peanoMinusReduction` is computable: prepending a fixed sentence is elementary. -/
lemma peanoMinusReduction_computable : Computable peanoMinusReduction := by
  sorry

/-- Church's theorem: the set of (purely logically, i.e. `∅`-)provable sentences is not
computable. -/
theorem church_theorem : ¬ComputablePred {σ : ArithmeticSentence | (∅ : ArithmeticTheory) ⊢ σ} := by
  intro hC
  have hred : (fun σ : ArithmeticSentence ↦ (𝗣𝗔⁻ : ArithmeticTheory) ⊢ σ)
      ≤₀ (fun σ : ArithmeticSentence ↦ (∅ : ArithmeticTheory) ⊢ σ) :=
    ⟨peanoMinusReduction, peanoMinusReduction_computable, peanoMinus_provable_iff⟩
  exact church_theoremAux (T := 𝗣𝗔⁻) (ComputablePred.computable_of_manyOneReducible hred hC)

end PeanoMinusReduction

end LO.FirstOrder.Arithmetic

end
