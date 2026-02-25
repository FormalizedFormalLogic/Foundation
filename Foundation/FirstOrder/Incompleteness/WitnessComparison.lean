module

public import Foundation.FirstOrder.Incompleteness.StandardProvability

@[expose] public section
/-!
# Witness comparisons of provability
-/

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

section WitnessComparisons

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (T : Theory L) [T.Δ₁]

def _root_.LO.FirstOrder.Theory.ProvabilityComparisonLE (φ ψ : V) : Prop :=
  ∃ b, T.Proof b φ ∧ ∀ b' < b, ¬T.Proof b' ψ

def _root_.LO.FirstOrder.Theory.ProvabilityComparisonLT (φ ψ : V) : Prop :=
  ∃ b, T.Proof b φ ∧ ∀ b' ≤ b, ¬T.Proof b' ψ

section

noncomputable def _root_.LO.FirstOrder.Theory.provabilityComparisonLE : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ b, !T.proof.sigma b φ ∧ ∀ b' < b, ¬!T.proof.pi b' ψ”

instance _root_.LO.FirstOrder.Theory.provability_comparison_le_defined :
    𝚺₁-Relation[V] T.ProvabilityComparisonLE via T.provabilityComparisonLE := .mk fun v ↦ by
  simp [Theory.provabilityComparisonLE, Theory.ProvabilityComparisonLE]

instance _root_.LO.FirstOrder.Theory.provability_comparison_le_definable : 𝚺₁-Relation[V] T.ProvabilityComparisonLE :=
  T.provability_comparison_le_defined.to_definable

/-- instance for definability tactic -/
instance _root_.LO.FirstOrder.Theory.provability_comparison_le_definable' :
    𝚺-[0 + 1]-Relation[V] T.ProvabilityComparisonLE := T.provability_comparison_le_definable


noncomputable def _root_.LO.FirstOrder.Theory.provabilityComparisonLT : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ b, !T.proof.sigma b φ ∧ ∀ b' <⁺ b, ¬!T.proof.pi b' ψ”

instance _root_.LO.FirstOrder.Theory.provability_comparison_lt_defined :
    𝚺₁-Relation[V] T.ProvabilityComparisonLT via T.provabilityComparisonLT := .mk fun v ↦ by
  simp [Theory.provabilityComparisonLT, Theory.ProvabilityComparisonLT]

instance _root_.LO.FirstOrder.Theory.provability_comparison_lt_definable : 𝚺₁-Relation[V] T.ProvabilityComparisonLT :=
  T.provability_comparison_lt_defined.to_definable

/-- instance for definability tactic -/
instance _root_.LO.FirstOrder.Theory.provability_comparison_lt_definable' :
    𝚺-[0 + 1]-Relation[V] T.ProvabilityComparisonLT := T.provability_comparison_lt_definable

end

variable {T : Theory L} [T.Δ₁]

namespace ProvabilityComparison

variable {φ ψ χ : V}

local infixl:50 "≼" => T.ProvabilityComparisonLE
local infixl:50 "≺" => T.ProvabilityComparisonLT
local prefix:50 "□" => T.Provable

@[grind =>]
lemma le_of_lt : φ ≺ ψ → φ ≼ ψ := by rintro ⟨b, _⟩; exact ⟨b, by grind⟩

@[grind =>]
lemma le_to_provable : φ ≼ ψ → □φ := by rintro ⟨b, hb, _⟩; exact ⟨b, by grind⟩

@[grind =>]
lemma le_trans : φ ≼ ψ → ψ ≼ χ → φ ≼ χ := by rintro ⟨b, hb, h⟩ ⟨d, hd, H⟩; use b; grind;

@[grind =>]
lemma le_antisymm : φ ≼ ψ → ψ ≼ φ → φ = ψ := by
  rintro ⟨b, hb, Hb⟩ ⟨d, hd, Hd⟩
  have : b = d := by
    by_contra ne
    wlog lt : b < d
    · grind;
    have : ¬T.Proof b φ := Hd b lt
    contradiction
  have : ({φ} : V) = {ψ} := by simp [←hb.1, ←hd.1, this]
  simpa using this


lemma iff_le_refl_provable : φ ≼ φ ↔ □φ := by
  constructor
  · exact le_to_provable
  · rintro ⟨b, hb⟩
    have : ∃ b, T.Proof b φ ∧ ∀ z < b, ¬T.Proof z φ :=
      InductionOnHierarchy.least_number_sigma 𝚺 1 (P := (T.Proof · φ)) (by definability) hb
    rcases this with ⟨b, bd, h⟩
    exact ⟨b, bd, h⟩

@[grind .]
lemma lt_irrefl : ¬φ ≺ φ := by rintro ⟨b, hb, h⟩; have : ¬T.Proof b φ := h b (by simp); contradiction

@[grind =>]
lemma lt_trans : φ ≺ ψ → ψ ≺ χ → φ ≺ χ := by rintro ⟨b, hb, h⟩ ⟨d, hd, H⟩; use b; grind;


@[grind =>]
lemma not_lt_of_le : φ ≼ ψ → ¬ψ ≺ φ := by grind;


lemma find_minimal_proof_fintype [Fintype ι] (φ : ι → V) (H : □(φ i)) :
    ∃ j, ∀ k, (φ j) ≼ (φ k) := by
  rcases show ∃ dᵢ, T.Proof dᵢ (φ i)from H with ⟨dᵢ, Hdᵢ⟩
  have : ∃ z, (∃ j, T.Proof z (φ j)) ∧ ∀ w < z, ∀ x, ¬T.Proof w (φ x) := by
    simpa using
      InductionOnHierarchy.least_number_sigma 𝚺 1 (P := fun z ↦ ∃ j, T.Proof z (φ j))
        (HierarchySymbol.Definable.fintype_exs fun j ↦ by definability) (x := dᵢ) ⟨i, Hdᵢ⟩
  rcases this with ⟨z, ⟨j, hj⟩, H⟩
  exact ⟨j, fun k ↦ ⟨z, hj, fun w hw ↦ H w hw k⟩⟩

end ProvabilityComparison

end WitnessComparisons

end LO.FirstOrder.Arithmetic.Bootstrapping
