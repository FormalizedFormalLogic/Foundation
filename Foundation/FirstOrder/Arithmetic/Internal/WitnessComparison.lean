import Foundation.FirstOrder.Arithmetic.Internal.DerivabilityCondition
import Foundation.Logic.HilbertStyle.Supplemental

/-!
# Witness comparisons of provability
-/

namespace LO.FirstOrder.Arithmetic.Internal

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

section WitnessComparisons

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (T : Theory L) [T.Δ₁]

def _root_.LO.FirstOrder.Theory.ProvabilityComparison (φ ψ : V) : Prop :=
  ∃ b, T.Proof b φ ∧ ∀ b' < b, ¬T.Proof b' ψ

section

noncomputable def _root_.LO.FirstOrder.Theory.provabilityComparison : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ b, !T.proof.sigma b φ ∧ ∀ b' < b, ¬!T.proof.pi b' ψ”

instance _root_.LO.FirstOrder.Theory.provability_comparison_defined :
    𝚺₁-Relation[V] T.ProvabilityComparison via T.provabilityComparison := .mk fun v ↦ by
  simp [Theory.provabilityComparison, Theory.ProvabilityComparison]

instance _root_.LO.FirstOrder.Theory.provability_comparison_definable : 𝚺₁-Relation[V] T.ProvabilityComparison :=
  T.provability_comparison_defined.to_definable

/-- instance for definability tactic-/
instance _root_.LO.FirstOrder.Theory.provability_comparison_definable' :
    𝚺-[0 + 1]-Relation[V] T.ProvabilityComparison := T.provability_comparison_definable

end

variable {T}

namespace ProvabilityComparison

variable {φ ψ : V}

lemma to_provable : T.ProvabilityComparison φ ψ → T.Provable φ := by rintro ⟨b, hb, _⟩; exact ⟨b, hb⟩

lemma refl_iff_provable : T.ProvabilityComparison φ φ ↔ T.Provable φ := by
  constructor
  · exact to_provable
  · rintro ⟨b, hb⟩
    have : ∃ b, T.Proof b φ ∧ ∀ z < b, ¬T.Proof z φ :=
      InductionOnHierarchy.least_number_sigma 𝚺 1 (P := (T.Proof · φ)) (by definability) hb
    rcases this with ⟨b, bd, h⟩
    exact ⟨b, bd, h⟩

lemma antisymm : T.ProvabilityComparison φ ψ → T.ProvabilityComparison ψ φ → φ = ψ := by
  rintro ⟨b, hb, Hb⟩ ⟨d, hd, Hd⟩
  have : b = d := by
    by_contra ne
    wlog lt : b < d
    · have : b ≤ d := le_of_not_gt <| this d hd Hd b hb Hb (Ne.symm ne)
      have : d ≤ b := le_of_not_gt lt
      have : b = d := le_antisymm (by assumption) (by assumption)
      contradiction
    have : ¬T.Proof b φ := Hd b lt
    contradiction
  have : ({φ} : V) = {ψ} := by simp [←hb.1, ←hd.1, this]
  simpa using this

lemma find_minimal_proof_fintype [Fintype ι] (φ : ι → V) (H : T.Provable (φ i)) :
    ∃ j, ∀ k, T.ProvabilityComparison (φ j) (φ k) := by
  rcases show ∃ dᵢ, T.Proof dᵢ (φ i)from H with ⟨dᵢ, Hdᵢ⟩
  have : ∃ z, (∃ j, T.Proof z (φ j)) ∧ ∀ w < z, ∀ x, ¬T.Proof w (φ x) := by
    simpa using
      InductionOnHierarchy.least_number_sigma 𝚺 1 (P := fun z ↦ ∃ j, T.Proof z (φ j))
        (HierarchySymbol.Definable.fintype_ex fun j ↦ by definability) (x := dᵢ) ⟨i, Hdᵢ⟩
  rcases this with ⟨z, ⟨j, hj⟩, H⟩
  exact ⟨j, fun k ↦ ⟨z, hj, fun w hw ↦ H w hw k⟩⟩

end ProvabilityComparison

end WitnessComparisons

end LO.FirstOrder.Arithmetic.Internal
