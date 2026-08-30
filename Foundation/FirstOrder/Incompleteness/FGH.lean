module

public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.FirstOrder.Arithmetic.Sigma1WitnessForm

/-!
# The Friedman–Goldfarb–Harrington theorem

For a `Δ₀` formula `θ`, `𝗜𝚺₁` proves `□_T (T.fghSentenceSigma θ) ↔ (∃¹ θ) ∨ □_T ⊥`,
and consequently `T ∪ Con_T ⊢ (∃¹ θ) ↔ □_T (T.fghSentenceSigma θ)`. Every `Σ₁` sentence
is of the form `∃¹ θ` for some `Δ₀` witness form `θ`, by `exists_delta0_witness_form`.
-/

@[expose] public section

open Classical

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {x : V}

variable (T : ArithmeticTheory) [T.Δ₁] (θ : ArithmeticSemisentence 1)

def _root_.LO.FirstOrder.Theory.WitnessedBefore (φ : V) := ∃ b, V ⊧/![b] θ ∧ ∀ b' < b, ¬Proof T b' φ

def _root_.LO.FirstOrder.Theory.ProvedBefore (φ : V) := ∃ b, Proof T b φ ∧ ∀ b' ≤ b, ¬V ⊧/![b'] θ

noncomputable def _root_.LO.FirstOrder.Theory.witnessedBefore : ArithmeticSemisentence 1 :=
  “x. ∃ w, !θ w ∧ ∀ p < w, ¬!(proof T).pi p x”

noncomputable def _root_.LO.FirstOrder.Theory.provedBefore : ArithmeticSemisentence 1 :=
  “x. ∃ p, !(proof T).sigma p x ∧ ∀ w <⁺ p, ¬!θ w”

noncomputable def _root_.LO.FirstOrder.Theory.fghSentence : ArithmeticSentence :=
  fixedpoint (T.witnessedBefore θ)

noncomputable def _root_.LO.FirstOrder.Theory.fghSentenceSigma : ArithmeticSentence :=
  (T.witnessedBefore θ)/[⌜T.fghSentence θ⌝]

lemma eval_witnessedBefore : V ⊧/![x] (T.witnessedBefore θ) ↔ T.WitnessedBefore θ x := by
  simp [Theory.witnessedBefore, Theory.WitnessedBefore]

lemma eval_provedBefore : V ⊧/![x] (T.provedBefore θ) ↔ T.ProvedBefore θ x := by
  simp [Theory.provedBefore, Theory.ProvedBefore]

lemma hierarchy_fghSentenceSigma (hθ : Hierarchy 𝚺 0 θ) : Hierarchy 𝚺 1 (T.fghSentenceSigma θ) := by
  simp [Theory.fghSentenceSigma, Theory.witnessedBefore, hθ.mono (by omega)]

lemma not_witnessedBefore_of_provedBefore : T.ProvedBefore θ x → ¬T.WitnessedBefore θ x := by
  rintro ⟨p, hp, hbound⟩ ⟨w, hw, hbound'⟩
  rcases lt_or_ge p w with h | h <;> grind

local notation:max "□" σ:max => Provable T (⌜σ⌝ : V)

variable {σ : ArithmeticSentence}

lemma provable_of_provable_bot : □(⊥ : ArithmeticSentence) → □σ :=
  modus_ponens_sentence T (internalize_provability (V := V) Entailment.efq)

lemma provable_bot_of_provable_of_provable_neg : □σ → □(∼σ) → □(⊥ : ArithmeticSentence) := fun hσ hnσ ↦
  modus_ponens_sentence T (modus_ponens_sentence T (internalize_provability (by cl_prover)) hσ) hnσ

variable [𝗜𝚺₁ ⪯ T]

lemma refutable_fghSentence_of_provedBefore :
    T ⊢ (T.provedBefore θ)/[⌜T.fghSentence θ⌝] 🡒 ∼T.fghSentence θ := by
  set π := T.fghSentence θ with hπ
  have h1 : T ⊢ (T.provedBefore θ)/[⌜π⌝] 🡒 ∼(T.witnessedBefore θ)/[⌜π⌝] :=
    Entailment.WeakerThan.pbl
      (show 𝗜𝚺₁ ⊢ (T.provedBefore θ)/[⌜π⌝] 🡒 ∼(T.witnessedBefore θ)/[⌜π⌝] by
        apply complete
        intro (W : Type) _ _
        simpa [models_iff, eval_witnessedBefore, eval_provedBefore, Sentence.coe_quote_eq_quote]
          using not_witnessedBefore_of_provedBefore (T := T) (θ := θ) (x := ⌜π⌝))
  have h2 : T ⊢ π 🡘 (T.witnessedBefore θ)/[⌜π⌝] := hπ ▸ diagonal (T.witnessedBefore θ)
  exact Entailment.C_trans h1 (Entailment.contra (Entailment.K_left h2))

lemma provable_fghSentence_iff (hθ : Hierarchy 𝚺 0 θ) :
    □(T.fghSentence θ) ↔ (∃ w, V ⊧/![w] θ) ∨ □(⊥ : ArithmeticSentence) := by
  set π := T.fghSentence θ with hπ
  constructor
  · intro hprov
    by_cases hw : ∃ w, V ⊧/![w] θ
    · exact Or.inl hw
    · push Not at hw
      obtain ⟨p₀, hp₀⟩ := hprov
      have h2 : V↓[ℒₒᵣ] ⊧ (T.provedBefore θ)/[⌜π⌝] := by
        simpa [models_iff] using
          (eval_provedBefore T θ).mpr (⟨p₀, hp₀, fun w _ ↦ hw w⟩ : T.ProvedBefore θ (⌜π⌝ : V))
      have hp2 : □((T.provedBefore θ)/[⌜π⌝]) :=
        Bootstrapping.Arithmetic.sigma_one_complete T
          (by simp [Theory.provedBefore, (Hierarchy.pi_zero_iff_sigma_zero.mpr hθ).mono
            (by omega : (0:ℕ) ≤ 1)]) h2
      have hrefut : T ⊢ (T.provedBefore θ)/[⌜π⌝] 🡒 ∼π :=
        hπ ▸ refutable_fghSentence_of_provedBefore T θ
      exact Or.inr (provable_bot_of_provable_of_provable_neg T ⟨p₀, hp₀⟩
        (modus_ponens_sentence T (internalize_provability hrefut) hp2))
  · rintro (⟨w₀, hw₀⟩ | hbot)
    · by_cases hp : ∃ p < w₀, Proof T p (⌜π⌝ : V)
      · obtain ⟨p, -, hp⟩ := hp
        use p
      · push Not at hp
        have h2 : V↓[ℒₒᵣ] ⊧ (T.witnessedBefore θ)/[⌜π⌝] := by
          simpa [models_iff] using (eval_witnessedBefore T θ).mpr (⟨w₀, hw₀, hp⟩ : T.WitnessedBefore θ (⌜π⌝ : V))
        have hdiag : T ⊢ T.fghSentenceSigma θ 🡒 π :=
          Entailment.K_right
            (hπ ▸ diagonal (T.witnessedBefore θ) : T ⊢ π 🡘 (T.witnessedBefore θ)/[⌜π⌝])
        exact modus_ponens_sentence T (internalize_provability hdiag)
          (Bootstrapping.Arithmetic.sigma_one_complete T (hierarchy_fghSentenceSigma T θ hθ) h2)
    · exact provable_of_provable_bot T hbot

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (θ : ArithmeticSemisentence 1)

theorem fgh_theorem (hθ : Hierarchy 𝚺 0 θ) :
    𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentenceSigma θ) 🡘 (∃¹ θ) ⋎ provabilityPred T ⊥ := by
  have heq : 𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence θ) 🡘 (∃¹ θ) ⋎ provabilityPred T ⊥ := by
    apply complete.{0};
    intro V _ _;
    simpa [models_iff] using provable_fghSentence_iff T θ hθ
  have hdiag : 𝗜𝚺₁ ⊢ T.fghSentence θ 🡘 T.fghSentenceSigma θ := diagonal (T.witnessedBefore θ)
  have hiff : 𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence θ) 🡘 provabilityPred T (T.fghSentenceSigma θ) :=
    Entailment.E_intro (T.standardProvability.mono' (Entailment.K_left hdiag))
      (T.standardProvability.mono' (Entailment.K_right hdiag))
  exact Entailment.E_trans (Entailment.E_symm hiff) heq

theorem fgh_theorem_con (hθ : Hierarchy 𝚺 0 θ) :
    T ∪ T.Con ⊢ (∃¹ θ) 🡘 provabilityPred T (T.fghSentenceSigma θ) := by
  have heq := fgh_theorem T θ hθ;
  have : 𝗜𝚺₁ ⪯ T ∪ T.Con := Entailment.WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ T) inferInstance;
  have heq' : T ∪ T.Con ⊢ provabilityPred T (T.fghSentenceSigma θ) 🡘 (∃¹ θ) ⋎ provabilityPred T ⊥ :=
    Entailment.WeakerThan.pbl heq;
  have hcon : T ∪ T.Con ⊢ ∼provabilityPred T ⊥ := Entailment.by_axm (Or.inr rfl);
  generalize T.fghSentenceSigma θ = π at heq' ⊢;
  cl_prover [heq', hcon]

end LO.FirstOrder.Arithmetic
