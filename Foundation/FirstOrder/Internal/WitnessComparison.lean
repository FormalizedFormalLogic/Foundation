import Foundation.FirstOrder.Incompleteness.Second
import Foundation.Logic.HilbertStyle.Supplemental

/-!
# Witness comparisons of provability

-/

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

section WitnessComparisons

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (T : Theory L) [T.Δ₁Definable]

def _root_.LO.FirstOrder.Theory.DerivabilityComparison (s₁ s₂ : V) : Prop :=
  ∃ d₁, T.DerivationOf d₁ s₁ ∧ ∀ d₂ < d₁, ¬T.DerivationOf d₂ s₂

def _root_.LO.FirstOrder.Theory.ProvabilityComparison (φ ψ : V) : Prop :=
  T.DerivabilityComparison (V := V) {φ} {ψ}

section

def _root_.LO.FirstOrder.Theory.derivabilityComparison : 𝚺₁.Semisentence 2 := .mkSigma
  “s₁ s₂. ∃ d₁, !T.derivationOf.sigma d₁ s₁ ∧ ∀ d₂ < d₁, ¬!T.derivationOf.pi d₂ s₂”

lemma _root_.LO.FirstOrder.Theory.derivability_comparison_defined :
    𝚺₁-Relation[V] T.DerivabilityComparison via T.derivabilityComparison := by
  intro v
  simp [Theory.derivabilityComparison, HierarchySymbol.Semiformula.val_sigma,
    Theory.DerivationOf.defined.df.iff, Theory.DerivationOf.defined.proper.iff', Theory.DerivabilityComparison]

instance _root_.LO.FirstOrder.Theory.derivability_comparison_definable : 𝚺₁-Relation[V] T.DerivabilityComparison :=
  T.derivability_comparison_defined.to_definable

def _root_.LO.FirstOrder.Theory.provabilityComparison : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ sφ sψ, !insertDef sφ φ 0 ∧ !insertDef sψ ψ 0 ∧ !T.derivabilityComparison sφ sψ”

lemma _root_.LO.FirstOrder.Theory.provability_comparison_defined : 𝚺₁-Relation[V] T.ProvabilityComparison via T.provabilityComparison := by
  intro v; simp [Theory.provabilityComparison, T.derivability_comparison_defined.df.iff,
    Theory.ProvabilityComparison, singleton_eq_insert, emptyset_def]

instance _root_.LO.FirstOrder.Theory.provability_comparison_definable : 𝚺₁-Relation[V] T.ProvabilityComparison :=
  T.provability_comparison_defined.to_definable

/-- instance for definability tactic-/
instance _root_.LO.FirstOrder.Theory.provability_comparison_definable' :
    𝚺-[0 + 1]-Relation[V] T.ProvabilityComparison := T.provability_comparison_definable

@[simp] lemma _root_.LO.FirstOrder.Theory.ProvabilityComparison.eval (v) :
    Semiformula.Evalbm V v T.provabilityComparison.val ↔ T.ProvabilityComparison (v 0) (v 1) :=
  (T.provability_comparison_defined).df.iff v

end

variable {T}

namespace DerivabilityComparison

variable {Γ Δ : V}

lemma refl_iff_derivable : T.DerivabilityComparison Γ Γ ↔ T.Derivable Γ := by
  constructor
  · rintro ⟨d, dd, hd⟩
    exact ⟨d, dd⟩
  · rintro ⟨d, dd⟩
    have : ∃ b, T.DerivationOf b Γ ∧ ∀ z < b, ¬T.DerivationOf z Γ :=
      InductionOnHierarchy.least_number_sigma 𝚺 1 (P := (T.DerivationOf · Γ)) (by definability) dd
    rcases this with ⟨b, bd, h⟩
    exact ⟨b, bd, h⟩

lemma antisymm : T.DerivabilityComparison Γ Δ → T.DerivabilityComparison Δ Γ → Γ = Δ := by
  rintro ⟨dΓ, dΓd, HΓ⟩ ⟨dΔ, dΔd, HΔ⟩
  have : dΓ = dΔ := by
    by_contra ne
    wlog lt : dΓ < dΔ
    · have : dΓ ≤ dΔ := le_of_not_gt <| this dΔ dΔd HΔ dΓ dΓd HΓ (Ne.symm ne)
      have : dΔ ≤ dΓ := le_of_not_gt lt
      have : dΓ = dΔ := le_antisymm (by assumption) (by assumption)
      contradiction
    have : ¬T.DerivationOf dΓ Γ := HΔ dΓ lt
    contradiction
  have : fstIdx dΔ = Δ := dΔd.1
  have : fstIdx dΓ = Γ := dΓd.1
  simp_all

lemma find_minimal_proof_fintype [Fintype ι] (Γ : ι → V) (H : T.Derivable (Γ i)) :
    ∃ j, ∀ k, T.DerivabilityComparison (Γ j) (Γ k) := by
  rcases show ∃ dᵢ, T.DerivationOf dᵢ (Γ i)from H with ⟨dᵢ, Hdᵢ⟩
  have : ∃ z, (∃ j, T.DerivationOf z (Γ j)) ∧ ∀ w < z, ∀ (x : ι), ¬T.DerivationOf w (Γ x) := by
    simpa using
      InductionOnHierarchy.least_number_sigma 𝚺 1 (P := fun z ↦ ∃ j, T.DerivationOf z (Γ j))
        (HierarchySymbol.Boldface.fintype_ex fun j ↦ by definability) (x := dᵢ) ⟨i, Hdᵢ⟩
  rcases this with ⟨z, ⟨j, hj⟩, H⟩
  exact ⟨j, fun k ↦ ⟨z, hj, fun w hw ↦ H w hw k⟩⟩

end DerivabilityComparison

namespace ProvabilityComparison

variable {φ ψ : V}

lemma refl_iff_provable : T.ProvabilityComparison φ φ ↔ T.Provable φ := DerivabilityComparison.refl_iff_derivable

lemma antisymm : T.ProvabilityComparison φ ψ → T.ProvabilityComparison ψ φ → φ = ψ :=
  fun h₁ h₂ ↦ by
    simpa using mem_ext_iff.mp (DerivabilityComparison.antisymm h₁ h₂) φ

lemma find_minimal_proof_fintype [Fintype ι] (φ : ι → V) (H : T.Provable (φ i)) :
    ∃ j, ∀ k, T.ProvabilityComparison (φ j) (φ k) := DerivabilityComparison.find_minimal_proof_fintype _ H

end ProvabilityComparison

end WitnessComparisons

end LO.ISigma1.Metamath
