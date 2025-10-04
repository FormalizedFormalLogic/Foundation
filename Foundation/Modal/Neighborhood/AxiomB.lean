import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.Supplementation


namespace LO.Modal


section

variable {α : Type*} [DecidableEq α]
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S} [Entailment.Cl 𝓢]

abbrev Proofset (𝓢 : S) := Set (MaximalConsistentSet 𝓢)
abbrev Nonproofset (𝓢 : S) := { P : Proofset 𝓢 // ∀ φ, P ≠ proofset 𝓢 φ }

end


namespace Neighborhood

section

open MaximalConsistentSet

variable [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.E 𝓢]

def Canonicity.box (𝓒 : Canonicity 𝓢) : Proofset 𝓢 → Proofset 𝓢 := λ X => { w | X ∈ 𝓒.𝒩 w }
def Canonicity.dia (𝓒 : Canonicity 𝓢) : Proofset 𝓢 → Proofset 𝓢 := λ X => (𝓒.box Xᶜ)ᶜ

abbrev relativeMinimalCanonicity (𝓢 : S) [Entailment.E 𝓢] (𝓧 : MaximalConsistentSet 𝓢 → Set (Proofset 𝓢)) (h𝓧 : ∀ A, ∀ X ∈ 𝓧 A, ∀ φ, X ≠ proofset 𝓢 φ) : Canonicity 𝓢 where
  𝒩 A := (minimalCanonicity 𝓢 |>.𝒩 A) ∪ (𝓧 A);
  def_𝒩 := by
    intro X φ;
    constructor;
    . intro h;
      left;
      use φ;
    . rintro (⟨ψ, hψ₁, hψ₂⟩ | h);
      . have := proofset.eq_boxed_of_eq hψ₂;
        grind;
      . simpa using h𝓧 _ _ h φ;
  V a := proofset 𝓢 (.atom a);
  def_V := by simp;

abbrev relativeMinimalCanonicity.of_box (𝓢 : S) [Entailment.E 𝓢]
  (𝓑 : Proofset 𝓢 → Proofset 𝓢)
  (h𝓑 : ∀ X, ∀ A ∈ 𝓑 X, ∀ φ, X ≠ proofset 𝓢 φ)
  : Canonicity 𝓢 := relativeMinimalCanonicity 𝓢
  (λ x => { X | x ∈ 𝓑 X })
  (by grind)

abbrev canonicity_for_EB (𝓢 : S) [Entailment.E 𝓢] : Canonicity 𝓢 := relativeMinimalCanonicity.of_box 𝓢 (λ X A => (∀ φ, X ≠ proofset 𝓢 φ) ∧ (minimalCanonicity 𝓢).dia ((minimalCanonicity 𝓢).box X) A) $ by
  rintro X A ⟨_, _⟩;
  assumption;

instance [Entailment.HasAxiomB 𝓢] : (canonicity_for_EB 𝓢).toModel.IsSymmetric := by
  constructor;
  intro X Γ hΓ;
  by_cases h : ∀ φ, X ≠ proofset 𝓢 φ;
  . sorry;
  . push_neg at h;
    obtain ⟨φ, rfl⟩ := h;
    simp only [Canonicity.dia_proofset, Canonicity.box_proofset] at hΓ ⊢;
    apply proofset.imp_subset.mp (by simp) hΓ;

def maximalCanonicity (𝓢 : S) [Entailment.E 𝓢] : Canonicity 𝓢 where
  𝒩 A := (minimalCanonicity 𝓢 |>.𝒩 A) ∪ ({ X | ∀ φ, X ≠ proofset 𝓢 φ})
  def_𝒩 := by
    intro X φ;
    constructor;
    . intro h;
      left;
      use φ;
    . rintro (⟨ψ, hψ₁, hψ₂⟩ | h);
      . have := proofset.eq_boxed_of_eq hψ₂;
        grind;
      . grind;
  V a := proofset 𝓢 (.atom a);
  def_V := by simp;

open LO.Entailment

instance [Entailment.HasAxiomFive 𝓢] : (maximalCanonicity 𝓢).toModel.IsEuclidean := by
  apply Frame.IsEuclidean.of_alt;
  rintro A X hX;
  obtain ⟨hX, ⟨φ, rfl⟩⟩ : X ∉ (minimalCanonicity 𝓢).𝒩 A ∧ ∃ x, X = proofset 𝓢 x := by simpa [Canonicity.toModel, maximalCanonicity] using hX;

  suffices proofset 𝓢 (◇(∼φ)) = {b | proofset 𝓢 φ ∉ (maximalCanonicity 𝓢).toModel.𝒩 b} by
    have H : proofset 𝓢 (◇(∼φ)) ∈ (maximalCanonicity 𝓢).𝒩 A := (maximalCanonicity 𝓢).def_𝒩 _ _ |>.mp
      $ MaximalConsistentSet.mdp_provable (show 𝓢 ⊢ ∼□φ ➝ □◇(∼φ) by exact C!_trans (by simp) Entailment.axiomFive!)
      $ MaximalConsistentSet.iff_mem_neg.mpr
      $ by apply Canonicity.iff_box.not.mpr; simpa [Canonicity.toModel, maximalCanonicity];
    rwa [this] at H;

  ext _;
  simp [←(maximalCanonicity 𝓢).dia_proofset, Canonicity.toModel];

instance [Entailment.HasAxiomB 𝓢] : (maximalCanonicity 𝓢).toModel.IsSymmetric := by sorry;

end

end Neighborhood

end LO.Modal
