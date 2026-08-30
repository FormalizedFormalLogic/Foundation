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

local notation:max "𝗪" ρ:max => (T.witnessedBefore θ)/[⌜ρ⌝]
local notation:max "𝗣" ρ:max => (T.provedBefore θ)/[⌜ρ⌝]

noncomputable def _root_.LO.FirstOrder.Theory.fghSentence : ArithmeticSentence :=
  fixedpoint (T.witnessedBefore θ)

noncomputable def _root_.LO.FirstOrder.Theory.fghSentenceSigma : ArithmeticSentence :=
  𝗪(T.fghSentence θ)

/-! ### Evaluation and complexity -/

private lemma eval_witnessedBefore {x : V} :
    V ⊧/![x] (T.witnessedBefore θ) ↔ T.WitnessedBefore θ x := by
  simp [Theory.witnessedBefore, Theory.WitnessedBefore]

private lemma eval_provedBefore {x : V} :
    V ⊧/![x] (T.provedBefore θ) ↔ T.ProvedBefore θ x := by
  simp [Theory.provedBefore, Theory.ProvedBefore]

private lemma hierarchy_witnessedBefore (hθ : Hierarchy 𝚺 0 θ) : Hierarchy 𝚺 1 (T.witnessedBefore θ) := by
  simp [Theory.witnessedBefore, hθ.mono (by omega)]

private lemma hierarchy_provedBefore (hθ : Hierarchy 𝚺 0 θ) : Hierarchy 𝚺 1 (T.provedBefore θ) := by
  simp [Theory.provedBefore, (Hierarchy.pi_zero_iff_sigma_zero.mpr hθ).mono (by omega : (0:ℕ) ≤ 1)]

private lemma hierarchy_fghSentenceSigma (hθ : Hierarchy 𝚺 0 θ) : Hierarchy 𝚺 1 (T.fghSentenceSigma θ) := by
  simp [Theory.fghSentenceSigma, hierarchy_witnessedBefore T θ hθ]

/-! ### Exclusivity of witness and proof -/

private lemma not_witnessedBefore_of_provedBefore {x : V} :
    T.ProvedBefore θ x → ¬T.WitnessedBefore θ x := by
  rintro ⟨p, hp, hbound⟩ ⟨w, hw, hbound'⟩
  rcases lt_or_ge p w with h | h
  · exact hbound' p h hp
  · exact hbound w h hw

private lemma provedBefore_imp_not_witnessedBefore (ρ : ArithmeticSentence) :
    𝗜𝚺₁ ⊢ 𝗣ρ 🡒 ∼𝗪ρ :=
  complete 𝗜𝚺₁ _ fun (W : Type) _ _ ↦ by
    simpa [models_iff, eval_witnessedBefore, eval_provedBefore, Sentence.coe_quote_eq_quote] using
      not_witnessedBefore_of_provedBefore (T := T) (θ := θ) (x := (⌜ρ⌝ : W))

/-! ### Internal logic helpers -/

local notation:max "□" σ:max => Provable T (⌜σ⌝ : V)

lemma provable_of_provable_bot {σ : ArithmeticSentence} :
    □(⊥ : ArithmeticSentence) → □σ :=
  modus_ponens_sentence T (internalize_provability (V := V) Entailment.efq)

lemma provable_bot_of_provable_of_provable_neg {σ : ArithmeticSentence} :
    □σ → □(∼σ) → □(⊥ : ArithmeticSentence) :=
  fun hσ hnσ ↦
    modus_ponens_sentence T
      (modus_ponens_sentence T (internalize_provability (V := V) (by cl_prover)) hσ) hnσ

private lemma provable_fghSentence_of_provable_bot :
    □(⊥ : ArithmeticSentence) → □(T.fghSentence θ) :=
  provable_of_provable_bot T

variable [𝗜𝚺₁ ⪯ T]

/-! ### The refutability lemma -/

private lemma refutable_fghSentence_of_provedBefore :
    T ⊢ 𝗣(T.fghSentence θ) 🡒 ∼T.fghSentence θ := by
  set π := T.fghSentence θ with hπ
  have h1 : T ⊢ 𝗣π 🡒 ∼𝗪π :=
    Entailment.WeakerThan.pbl (provedBefore_imp_not_witnessedBefore T θ π)
  have h2 : T ⊢ π 🡘 𝗪π := hπ ▸ diagonal (T.witnessedBefore θ)
  exact Entailment.C_trans h1 (Entailment.contra (Entailment.K_left h2))

/-! ### Provability of the FGH sentence -/

private lemma provable_fghSentence_of_witness (hθ : Hierarchy 𝚺 0 θ) :
    (∃ w, V ⊧/![w] θ) → □(T.fghSentence θ) := by
  rintro ⟨w₀, hw₀⟩
  set π := T.fghSentence θ with hπ
  by_cases hp : ∃ p < w₀, Proof T p (⌜π⌝ : V)
  · obtain ⟨p, -, hp⟩ := hp
    exact ⟨p, hp⟩
  · push Not at hp
    have h2 : V↓[ℒₒᵣ] ⊧ 𝗪π := by
      simpa [models_iff] using
        (eval_witnessedBefore T θ).mpr (⟨w₀, hw₀, hp⟩ : T.WitnessedBefore θ (⌜π⌝ : V))
    have hdiag : T ⊢ T.fghSentenceSigma θ 🡒 π :=
      Entailment.K_right (hπ ▸ diagonal (T.witnessedBefore θ) : T ⊢ π 🡘 𝗪π)
    exact modus_ponens_sentence T (internalize_provability hdiag)
      (Bootstrapping.Arithmetic.sigma_one_complete T (hierarchy_fghSentenceSigma T θ hθ) h2)

private lemma witness_or_provable_bot_of_provable_fghSentence (hθ : Hierarchy 𝚺 0 θ) :
    □(T.fghSentence θ) → (∃ w, V ⊧/![w] θ) ∨ □(⊥ : ArithmeticSentence) := by
  intro hprov
  by_cases hw : ∃ w, V ⊧/![w] θ
  · exact Or.inl hw
  · push Not at hw
    set π := T.fghSentence θ with hπ
    obtain ⟨p₀, hp₀⟩ := hprov
    have h2 : V↓[ℒₒᵣ] ⊧ 𝗣π := by
      simpa [models_iff] using
        (eval_provedBefore T θ).mpr (⟨p₀, hp₀, fun w _ ↦ hw w⟩ : T.ProvedBefore θ (⌜π⌝ : V))
    have hp2 : □𝗣π :=
      Bootstrapping.Arithmetic.sigma_one_complete T (by simp [hierarchy_provedBefore T θ hθ]) h2
    have hrefut : T ⊢ 𝗣π 🡒 ∼π := hπ ▸ refutable_fghSentence_of_provedBefore T θ
    exact Or.inr (provable_bot_of_provable_of_provable_neg T ⟨p₀, hp₀⟩
      (modus_ponens_sentence T (internalize_provability hrefut) hp2))

/-! ### The FGH equation -/

lemma fgh_equation (hθ : Hierarchy 𝚺 0 θ) {σ : ArithmeticSentence}
    (hwit : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ) :
    𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence θ) 🡘 σ ⋎ provabilityPred T ⊥ :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, hwit V] using
      Iff.intro (witness_or_provable_bot_of_provable_fghSentence T θ hθ)
        (fun h ↦ h.elim (provable_fghSentence_of_witness T θ hθ)
          (provable_fghSentence_of_provable_bot T θ))

private lemma provable_fghSentence_iff_sigma :
    𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence θ) 🡘 provabilityPred T (T.fghSentenceSigma θ) := by
  have h : 𝗜𝚺₁ ⊢ T.fghSentence θ 🡘 T.fghSentenceSigma θ := diagonal (T.witnessedBefore θ)
  exact Entailment.E_intro (T.standardProvability.mono' (Entailment.K_left h))
    (T.standardProvability.mono' (Entailment.K_right h))

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}

theorem fgh_theorem (hσ : Hierarchy 𝚺 1 σ) :
  ∃ π : ArithmeticSentence, Hierarchy 𝚺 1 π ∧ 𝗜𝚺₁ ⊢ provabilityPred T π 🡘 σ ⋎ provabilityPred T ⊥ := by
  obtain ⟨θ, hθ, hwit⟩ := exists_delta0_witness_form hσ
  refine ⟨T.fghSentenceSigma θ, hierarchy_fghSentenceSigma T θ hθ, ?_⟩
  have heq : 𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence θ) 🡘 σ ⋎ provabilityPred T ⊥ :=
    fgh_equation T θ hθ (fun V _ _ ↦ hwit V ![])
  have hiff : 𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence θ) 🡘 provabilityPred T (T.fghSentenceSigma θ) :=
    provable_fghSentence_iff_sigma T θ
  exact Entailment.E_trans (Entailment.E_symm hiff) heq

theorem fgh_theorem_con (hσ : Hierarchy 𝚺 1 σ) :
  ∃ π : ArithmeticSentence, Hierarchy 𝚺 1 π ∧ T ∪ T.Con ⊢ σ 🡘 provabilityPred T π := by
  obtain ⟨π, hπ, heq⟩ := fgh_theorem (T := T) hσ
  have : 𝗜𝚺₁ ⪯ T ∪ T.Con := Entailment.WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ T) inferInstance
  refine ⟨π, hπ, ?_⟩
  have heq' : T ∪ T.Con ⊢ provabilityPred T π 🡘 σ ⋎ provabilityPred T ⊥ := Entailment.WeakerThan.pbl heq
  have hcon : T ∪ T.Con ⊢ ∼provabilityPred T ⊥ := Entailment.by_axm (Or.inr rfl)
  cl_prover [heq', hcon]

end LO.FirstOrder.Arithmetic
