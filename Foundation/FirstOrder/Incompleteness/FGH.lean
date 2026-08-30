module

public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.FirstOrder.Arithmetic.Sigma1WitnessForm

/-!
# The Friedman–Goldfarb–Harrington theorem

For every `Σ₁` sentence `σ` there is a `Σ₁` sentence `π` such that `𝗜𝚺₁` proves
`□_T π ↔ σ ∨ □_T ⊥`, and consequently `T ∪ Con_T ⊢ σ ↔ □_T π`.

- A. Visser, *Faith & Falsity*, Annals of Pure and Applied Logic, 2005.
-/

@[expose] public section

open Classical

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable (T : ArithmeticTheory) [T.Δ₁] (θ : ArithmeticSemisentence 1)

/-! ### The FGH sentence -/

def _root_.LO.FirstOrder.Theory.WitnessedBefore (x : V) : Prop :=
  ∃ w, V ⊧/![w] θ ∧ ∀ p < w, ¬Proof T p x

def _root_.LO.FirstOrder.Theory.ProvedBefore (x : V) : Prop :=
  ∃ p, Proof T p x ∧ ∀ w ≤ p, ¬V ⊧/![w] θ

noncomputable def _root_.LO.FirstOrder.Theory.witnessedBefore : ArithmeticSemisentence 1 :=
  “x. ∃ w, !θ w ∧ ∀ p < w, ¬!(proof T).pi p x”

noncomputable def _root_.LO.FirstOrder.Theory.provedBefore : ArithmeticSemisentence 1 :=
  “x. ∃ p, !(proof T).sigma p x ∧ ∀ w <⁺ p, ¬!θ w”

noncomputable def _root_.LO.FirstOrder.Theory.fghSentence : ArithmeticSentence :=
  fixedpoint (T.witnessedBefore θ)

noncomputable def _root_.LO.FirstOrder.Theory.fghSentenceSigma : ArithmeticSentence :=
  (T.witnessedBefore θ)/[⌜T.fghSentence θ⌝]

/-! ### Evaluation and complexity -/

lemma eval_witnessedBefore {x : V} :
    V ⊧/![x] (T.witnessedBefore θ) ↔ T.WitnessedBefore θ x := by
  simp [Theory.witnessedBefore, Theory.WitnessedBefore]

lemma eval_provedBefore {x : V} :
    V ⊧/![x] (T.provedBefore θ) ↔ T.ProvedBefore θ x := by
  simp [Theory.provedBefore, Theory.ProvedBefore]

lemma hierarchy_witnessedBefore (hθ : Hierarchy 𝚺 0 θ) : Hierarchy 𝚺 1 (T.witnessedBefore θ) := by
  simp [Theory.witnessedBefore, hθ.mono (by omega)]

lemma hierarchy_provedBefore (hθ : Hierarchy 𝚺 0 θ) : Hierarchy 𝚺 1 (T.provedBefore θ) := by
  simp [Theory.provedBefore, (Hierarchy.pi_zero_iff_sigma_zero.mpr hθ).mono (by omega : (0:ℕ) ≤ 1)]

lemma hierarchy_fghSentenceSigma (hθ : Hierarchy 𝚺 0 θ) : Hierarchy 𝚺 1 (T.fghSentenceSigma θ) := by
  simp [Theory.fghSentenceSigma, hierarchy_witnessedBefore T θ hθ]

/-! ### Exclusivity of witness and proof -/

lemma not_witnessedBefore_of_provedBefore {x : V} :
    T.ProvedBefore θ x → ¬T.WitnessedBefore θ x := by
  rintro ⟨p, hp, hbound⟩ ⟨w, hw, hbound'⟩
  rcases lt_or_ge p w with h | h
  · exact hbound' p h hp
  · exact hbound w h hw

lemma provedBefore_imp_not_witnessedBefore (ρ : ArithmeticSentence) :
    𝗜𝚺₁ ⊢ (T.provedBefore θ)/[⌜ρ⌝] 🡒 ∼(T.witnessedBefore θ)/[⌜ρ⌝] :=
  complete 𝗜𝚺₁ _ fun (W : Type) _ _ ↦ by
    simpa [models_iff, eval_witnessedBefore, eval_provedBefore, Sentence.coe_quote_eq_quote] using
      not_witnessedBefore_of_provedBefore (T := T) (θ := θ) (x := (⌜ρ⌝ : W))

/-! ### Internal logic helpers -/

lemma provable_of_provable_bot {σ : ArithmeticSentence} :
    Provable T (⌜(⊥ : ArithmeticSentence)⌝ : V) → Provable T (⌜σ⌝ : V) :=
  modus_ponens_sentence T (internalize_provability (V := V) Entailment.efq)

lemma provable_bot_of_provable_of_provable_neg {σ : ArithmeticSentence} :
    Provable T (⌜σ⌝ : V) → Provable T (⌜∼σ⌝ : V) → Provable T (⌜(⊥ : ArithmeticSentence)⌝ : V) :=
  fun hσ hnσ ↦
    modus_ponens_sentence T
      (modus_ponens_sentence T (internalize_provability (V := V) (by cl_prover)) hσ) hnσ

variable [𝗜𝚺₁ ⪯ T]

/-! ### The refutability lemma -/

lemma refutable_fghSentence_of_provedBefore :
    T ⊢ (T.provedBefore θ)/[⌜T.fghSentence θ⌝] 🡒 ∼T.fghSentence θ := by
  set π := T.fghSentence θ with hπ
  have h1 : T ⊢ (T.provedBefore θ)/[⌜π⌝] 🡒 ∼(T.witnessedBefore θ)/[⌜π⌝] :=
    Entailment.WeakerThan.pbl (provedBefore_imp_not_witnessedBefore T θ π)
  have h2 : T ⊢ π 🡘 (T.witnessedBefore θ)/[⌜π⌝] := hπ ▸ diagonal (T.witnessedBefore θ)
  exact Entailment.C_trans h1 (Entailment.contra (Entailment.K_left h2))

/-! ### Provability of the FGH sentence -/

lemma provable_fghSentence_of_witness (hθ : Hierarchy 𝚺 0 θ) :
    (∃ w, V ⊧/![w] θ) → Provable T (⌜T.fghSentence θ⌝ : V) := sorry

lemma provable_fghSentence_of_provable_bot :
    Provable T (⌜(⊥ : ArithmeticSentence)⌝ : V) → Provable T (⌜T.fghSentence θ⌝ : V) := sorry

lemma witness_or_provable_bot_of_provable_fghSentence (hθ : Hierarchy 𝚺 0 θ) :
    Provable T (⌜T.fghSentence θ⌝ : V) → (∃ w, V ⊧/![w] θ) ∨ Provable T (⌜(⊥ : ArithmeticSentence)⌝ : V) := sorry

/-! ### The FGH equation -/

local prefix:90 "□" => provabilityPred T

lemma fgh_equation (hθ : Hierarchy 𝚺 0 θ) {σ : ArithmeticSentence}
    (hwit : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ) :
    𝗜𝚺₁ ⊢ □(T.fghSentence θ) 🡘 σ ⋎ □⊥ := sorry

lemma provable_fghSentence_iff_sigma (hθ : Hierarchy 𝚺 0 θ) :
    𝗜𝚺₁ ⊢ □(T.fghSentence θ) 🡘 □(T.fghSentenceSigma θ) := sorry

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

theorem fgh_theorem {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ∃ π : ArithmeticSentence, Hierarchy 𝚺 1 π ∧ 𝗜𝚺₁ ⊢ provabilityPred T π 🡘 σ ⋎ provabilityPred T ⊥ := sorry

theorem fgh_theorem_con {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ∃ π : ArithmeticSentence, Hierarchy 𝚺 1 π ∧ T ∪ T.Con ⊢ σ 🡘 provabilityPred T π := sorry

end LO.FirstOrder.Arithmetic
