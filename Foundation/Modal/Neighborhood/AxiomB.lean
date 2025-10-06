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

def relativeMinimalCanonicity (𝓢 : S) [Entailment.E 𝓢] (P : MaximalConsistentSet 𝓢 → Set (Proofset 𝓢)) : Canonicity 𝓢 where
  𝒩 A := (minimalCanonicity 𝓢 |>.𝒩 A) ∪ ({ X | (∀ φ, X ≠ proofset 𝓢 φ) ∧ (X ∈ P A) });
  def_𝒩 := by
    intro X φ;
    constructor;
    . intro h;
      left;
      use φ;
    . rintro (⟨ψ, hψ₁, hψ₂⟩ | h);
      . have := proofset.eq_boxed_of_eq hψ₂;
        grind;
      . simpa using h.1 φ;
  V a := proofset 𝓢 (.atom a);
  def_V := by simp;

omit [Entailment.Consistent 𝓢] in
lemma relativeMinimalCanonicity.mem_nonproofset {P A X} (hX : ∀ φ, X ≠ proofset 𝓢 φ) (hP : X ∈ P A) : X ∈ (relativeMinimalCanonicity 𝓢 P).𝒩 A := by
  right;
  constructor;
  . assumption;
  . assumption;

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

open LO.Entailment in
instance Canonicity.isEuclidean {𝓒 : Canonicity 𝓢} [Entailment.HasAxiomFive 𝓢]
  (h : ∀ A X, (∀ φ, X ≠ proofset 𝓢 φ) → { B | X ∉ 𝓒.𝒩 B } ∈ 𝓒.𝒩 A)
  : 𝓒.toModel.IsEuclidean := by
  apply Frame.IsEuclidean.of_alt;
  rintro A X hX;
  by_cases hA : ∀ φ, X ≠ proofset 𝓢 φ;
  . apply h;
    assumption;
  . push_neg at hA;
    obtain ⟨φ, rfl⟩ := hA;
    suffices proofset 𝓢 (◇(∼φ)) = {b | proofset 𝓢 φ ∉ 𝓒.toModel.𝒩 b} by
      have H : proofset 𝓢 (◇(∼φ)) ∈ 𝓒.𝒩 A := 𝓒.def_𝒩 _ _ |>.mp
        $ MaximalConsistentSet.mdp_provable (show 𝓢 ⊢ ∼□φ ➝ □◇(∼φ) by exact C!_trans (by simp) Entailment.axiomFive!)
        $ MaximalConsistentSet.iff_mem_neg.mpr
        $ by apply Canonicity.iff_box.not.mpr; simpa [Canonicity.toModel];
      rwa [this] at H;
    ext _;
    simp [←𝓒.dia_proofset, Canonicity.toModel];

open LO.Entailment in
instance relativeMinimalCanonicity.isEuclidean [Entailment.HasAxiomFive 𝓢] {P}
  (hP : ∀ X A, { B | X ∉ (relativeMinimalCanonicity 𝓢 P).𝒩 B} ∈ (relativeMinimalCanonicity 𝓢 P).𝒩 A)
  : (relativeMinimalCanonicity 𝓢 P).toModel.IsEuclidean := by
  apply Frame.IsEuclidean.of_alt;
  rintro A X hX;
  by_cases hX_np : ∀ φ, X ≠ proofset 𝓢 φ;
  . apply hP;
  . push_neg at hX_np;
    obtain ⟨φ, rfl⟩ := hX_np;
    suffices proofset 𝓢 (◇(∼φ)) = {b | proofset 𝓢 φ ∉ (relativeMinimalCanonicity 𝓢 P).toModel.𝒩 b} by
      have H : proofset 𝓢 (◇(∼φ)) ∈ (relativeMinimalCanonicity 𝓢 P).𝒩 A := (relativeMinimalCanonicity 𝓢 P).def_𝒩 _ _ |>.mp
        $ MaximalConsistentSet.mdp_provable (show 𝓢 ⊢ ∼□φ ➝ □◇(∼φ) by exact C!_trans (by simp) Entailment.axiomFive!)
        $ MaximalConsistentSet.iff_mem_neg.mpr
        $ by apply Canonicity.iff_box.not.mpr; simpa [Canonicity.toModel];
      rwa [this] at H;
    ext _;
    simp [←(relativeMinimalCanonicity 𝓢 P).dia_proofset, Canonicity.toModel];

open LO.Entailment in
instance maximalCanonicity.isEuclidean [Entailment.HasAxiomFive 𝓢]
  : (maximalCanonicity 𝓢).toModel.IsEuclidean := by
  apply Frame.IsEuclidean.of_alt;
  rintro A X hX;
  by_cases hA : ∀ φ, X ≠ proofset 𝓢 φ;
  . replace ⟨_, ⟨ψ, hψ⟩⟩ : X ∉ (minimalCanonicity 𝓢).𝒩 A ∧ ∃ x, X = proofset 𝓢 x := by
      simpa [maximalCanonicity, Canonicity.toModel] using hX;
    grind;
  . push_neg at hA;
    obtain ⟨φ, rfl⟩ := hA;
    suffices proofset 𝓢 (◇(∼φ)) = {b | proofset 𝓢 φ ∉ (maximalCanonicity 𝓢).toModel.𝒩 b} by
      have H : proofset 𝓢 (◇(∼φ)) ∈ (maximalCanonicity 𝓢).𝒩 A := (maximalCanonicity 𝓢).def_𝒩 _ _ |>.mp
        $ MaximalConsistentSet.mdp_provable (show 𝓢 ⊢ ∼□φ ➝ □◇(∼φ) by exact C!_trans (by simp) Entailment.axiomFive!)
        $ MaximalConsistentSet.iff_mem_neg.mpr
        $ by apply Canonicity.iff_box.not.mpr; simpa [Canonicity.toModel];
      rwa [this] at H;
    ext _;
    simp [←(maximalCanonicity 𝓢).dia_proofset, Canonicity.toModel];

def E5_canonicity (𝓢 : S) [Entailment.E 𝓢] : Canonicity 𝓢 := relativeMinimalCanonicity 𝓢 (λ A X => { B | X ∉ (minimalCanonicity 𝓢).𝒩 B } ∈ (minimalCanonicity 𝓢).𝒩 A)

instance E5_canonicity.isEuclidean [Entailment.HasAxiomFive 𝓢] : (E5_canonicity 𝓢).toModel.IsEuclidean := by
  apply relativeMinimalCanonicity.isEuclidean;
  intro X A;
  sorry;

end

end Neighborhood

end LO.Modal
