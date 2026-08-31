module

public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.FirstOrder.Arithmetic.Sigma1WitnessForm

/-!
# The Friedman–Goldfarb–Harrington theorem
-/

@[expose] public section

open Classical

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open LO.Entailment

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {x : V}

variable (T : ArithmeticTheory) [T.Δ₁] (θ : 𝚺₀.Semisentence 1)


def _root_.LO.FirstOrder.Theory.WitnessedBefore (φ : V) := ∃ b, V ⊧/![b] θ.val ∧ ∀ b' < b, ¬Proof T b' φ

noncomputable def _root_.LO.FirstOrder.Theory.witnessedBefore : 𝚺₁.Semisentence 1 := .mkSigma
  “x. ∃ w, !θ w ∧ ∀ p < w, ¬!(proof T).pi p x”

instance _root_.LO.FirstOrder.Theory.WitnessedBefore.defined :
    𝚺₁-Predicate[V] T.WitnessedBefore θ via T.witnessedBefore θ := .mk fun v ↦ by
  simp [Theory.witnessedBefore, Theory.WitnessedBefore];

instance _root_.LO.FirstOrder.Theory.WitnessedBefore.definable :
    𝚺₁-Predicate[V] T.WitnessedBefore θ := (Theory.WitnessedBefore.defined T θ).to_definable


def _root_.LO.FirstOrder.Theory.ProvedBefore (φ : V) := ∃ b, Proof T b φ ∧ ∀ b' ≤ b, ¬V ⊧/![b'] θ.val

noncomputable def _root_.LO.FirstOrder.Theory.provedBefore : 𝚺₁.Semisentence 1 := .mkSigma
  “x. ∃ p, !(proof T).sigma p x ∧ ∀ w <⁺ p, ¬!θ w”

instance _root_.LO.FirstOrder.Theory.ProvedBefore.defined :
    𝚺₁-Predicate[V] T.ProvedBefore θ via T.provedBefore θ := .mk fun v ↦ by
  simp [Theory.provedBefore, Theory.ProvedBefore];

instance _root_.LO.FirstOrder.Theory.ProvedBefore.definable :
    𝚺₁-Predicate[V] T.ProvedBefore θ := (Theory.ProvedBefore.defined T θ).to_definable


lemma not_witnessedBefore_of_provedBefore {T : ArithmeticTheory} [T.Δ₁] {θ}
  : T.ProvedBefore θ x → ¬T.WitnessedBefore θ x := by
  rintro ⟨p, hp, hbound⟩ ⟨w, hw, hbound'⟩;
  rcases lt_or_ge p w with h | h <;> grind;


noncomputable def _root_.LO.FirstOrder.Theory.fghSentence : ArithmeticSentence :=
  fixedpoint (T.witnessedBefore θ).val

noncomputable def _root_.LO.FirstOrder.Theory.fghSentence' : ArithmeticSentence :=
  (T.witnessedBefore θ).val/[⌜T.fghSentence θ⌝]

@[simp, grind .]
lemma hierarchy_fghSentence' {T : ArithmeticTheory} [T.Δ₁] {θ} : Hierarchy 𝚺 1 (T.fghSentence' θ) := by
  simp [Theory.fghSentence'];


variable {T : ArithmeticTheory} [T.Δ₁] {θ : 𝚺₀.Semisentence 1} {σ : ArithmeticSentence}

local notation:max "□" σ:max => Provable T (⌜σ⌝ : V)

lemma provable_of_provable_bot : □(⊥ : ArithmeticSentence) → □σ :=
  modus_ponens_sentence T $ internalize_provability efq

lemma provable_bot_of_provable_of_provable_neg : □σ → □(∼σ) → □(⊥ : ArithmeticSentence) := fun hσ hnσ ↦
  modus_ponens_sentence T (modus_ponens_sentence T (internalize_provability (by cl_prover)) hσ) hnσ

variable [𝗜𝚺₁ ⪯ T]

lemma refutable_fghSentence_of_provedBefore :
  T ⊢ (T.provedBefore θ).val/[⌜T.fghSentence θ⌝] 🡒 ∼T.fghSentence θ := by
  set π := T.fghSentence θ with hπ;
  have h1 : T ⊢ (T.provedBefore θ).val/[⌜π⌝] 🡒 ∼(T.witnessedBefore θ).val/[⌜π⌝] :=
    WeakerThan.pbl $
      show 𝗜𝚺₁ ⊢ (T.provedBefore θ).val/[⌜π⌝] 🡒 ∼(T.witnessedBefore θ).val/[⌜π⌝] by
      apply complete.{0};
      intro W _ _;
      simpa [models_iff, Sentence.coe_quote_eq_quote] using not_witnessedBefore_of_provedBefore;
  have h2 : T ⊢ π 🡘 (T.witnessedBefore θ).val/[⌜π⌝] := hπ ▸ diagonal (T.witnessedBefore θ).val;
  exact C_trans h1 $ contra $ K_left h2;

lemma witness_or_provable_bot_of_provable_fghSentence :
  □(T.fghSentence θ) → (∃ w, V ⊧/![w] θ.val) ∨ □(⊥ : ArithmeticSentence) := by
  set π := T.fghSentence θ with hπ;
  intro hprov;
  by_cases hw : ∃ w, V ⊧/![w] θ.val;
  . tauto;
  . push Not at hw;
    obtain ⟨p₀, hp₀⟩ := hprov;
    have h2 : V↓[ℒₒᵣ] ⊧ (T.provedBefore θ).val/[⌜π⌝] := by
      have hpb : T.ProvedBefore θ (⌜π⌝ : V) := ⟨p₀, hp₀, fun w _ ↦ hw w⟩;
      simpa [models_iff] using hpb;
    have hp2 : □((T.provedBefore θ).val/[⌜π⌝]) :=
      Bootstrapping.Arithmetic.sigma_one_complete T (by simp) h2;
    have hrefut : T ⊢ (T.provedBefore θ).val/[⌜π⌝] 🡒 ∼π :=
      hπ ▸ refutable_fghSentence_of_provedBefore;
    right;
    apply provable_bot_of_provable_of_provable_neg (T := T) (σ := π);
    . use p₀;
    . exact modus_ponens_sentence T (internalize_provability hrefut) hp2;

lemma provable_fghSentence_of_witness_or_provable_bot :
  (∃ w, V ⊧/![w] θ.val) ∨ □(⊥ : ArithmeticSentence) → □(T.fghSentence θ) := by
  set π := T.fghSentence θ with hπ;
  rintro (⟨w₀, hw₀⟩ | hbot);
  . by_cases hp : ∃ p < w₀, Proof T p (⌜π⌝ : V);
    . obtain ⟨p, -, hp⟩ := hp;
      use p;
    . push Not at hp;
      have h2 : V↓[ℒₒᵣ] ⊧ (T.witnessedBefore θ).val/[⌜π⌝] := by
        have hwb : T.WitnessedBefore θ (⌜π⌝ : V) := ⟨w₀, hw₀, hp⟩;
        simpa [models_iff] using hwb;
      have hdiag : T ⊢ T.fghSentence' θ 🡒 π :=
        K_right
          (hπ ▸ diagonal (T.witnessedBefore θ).val : T ⊢ π 🡘 (T.witnessedBefore θ).val/[⌜π⌝]);
      exact modus_ponens_sentence T (internalize_provability hdiag)
        (Bootstrapping.Arithmetic.sigma_one_complete T (by simp) h2);
  . exact provable_of_provable_bot hbot;

lemma provable_fghSentence_iff : □(T.fghSentence θ) ↔ (∃ w, V ⊧/![w] θ.val) ∨ □(⊥ : ArithmeticSentence) := ⟨
  witness_or_provable_bot_of_provable_fghSentence,
  provable_fghSentence_of_witness_or_provable_bot
⟩

/-- The constructive form of the FGH theorem: `T.fghSentence θ` is an explicit witness. -/
lemma provable_fixedpoint_iff_exs_or_provable_bot :
  𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence θ) 🡘 (∃¹ θ.val) ⋎ provabilityPred T ⊥ := by
  apply complete.{0};
  intro V _ _;
  simpa [models_iff] using provable_fghSentence_iff;

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

open Bootstrapping
open LO.Entailment

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}

theorem fgh_theorem (hσ : Hierarchy 𝚺 1 σ) :
  ∃ π : ArithmeticSentence, Hierarchy 𝚺 1 π ∧ 𝗜𝚺₁ ⊢ provabilityPred T π 🡘 σ ⋎ provabilityPred T ⊥ := by
  obtain ⟨θ, hθ, hwit⟩ := exists_delta0_witness_form.{0} hσ;
  set θ' : 𝚺₀.Semisentence 1 := .mkSigma θ hθ with hθ';
  use T.fghSentence' θ';
  and_intros;
  . simp;
  . have heq : 𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence θ') 🡘 σ ⋎ provabilityPred T ⊥ := by
      apply complete.{0};
      intro V _ _;
      have hwit' : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ := hwit V ![];
      simpa [models_iff, hwit', hθ'] using provable_fghSentence_iff (θ := θ');
    have hdiag : 𝗜𝚺₁ ⊢ T.fghSentence θ' 🡘 T.fghSentence' θ' := diagonal (T.witnessedBefore θ').val;
    have hiff : 𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence θ') 🡘 provabilityPred T (T.fghSentence' θ') :=
      E_intro (T.standardProvability.mono' (K_left hdiag)) (T.standardProvability.mono' (K_right hdiag));
    exact E_trans (E_symm hiff) heq;

theorem fgh_theorem_con (hσ : Hierarchy 𝚺 1 σ) :
  ∃ π : ArithmeticSentence, Hierarchy 𝚺 1 π ∧ 𝗜𝚺₁ ∪ T.Con ⊢ σ 🡘 provabilityPred T π := by
  obtain ⟨π, hπ, heq⟩ := fgh_theorem T hσ;
  use π;
  and_intros;
  . assumption;
  . have heq' : 𝗜𝚺₁ ∪ T.Con ⊢ provabilityPred T π 🡘 σ ⋎ provabilityPred T ⊥ := WeakerThan.pbl heq;
    have hcon : 𝗜𝚺₁ ∪ T.Con ⊢ ∼provabilityPred T ⊥ := by_axm (by simp [Theory.consistent]);
    cl_prover [heq', hcon];

end LO.FirstOrder.Arithmetic
