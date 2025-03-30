import Foundation.Incompleteness.Arith.D3
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Incompleteness.ToFoundation.Basic

noncomputable section

open Classical
namespace LO.Arith

open LO.FirstOrder LO.FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

section WitnessComparisons

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

variable (T : L.Theory) {pT : pL.TDef} [T.Defined pT]

def Language.Theory.DerivabilityComparison (s₁ s₂ : V) : Prop := ∃ d₁, T.DerivationOf d₁ s₁ ∧ ∀ d₂ < d₁, ¬T.DerivationOf d₂ s₂

def Language.Theory.ProvabilityComparison (φ ψ : V) : Prop := T.DerivabilityComparison {φ} {ψ}

section

def _root_.LO.FirstOrder.Arith.LDef.TDef.derivabilityComparisonDef {pL : LDef} (pT : pL.TDef) : 𝚺₁.Semisentence 2 := .mkSigma
  “s₁ s₂. ∃ d₁, !pT.derivationOfDef.sigma d₁ s₁ ∧ ∀ d₂ < d₁, ¬!pT.derivationOfDef.pi d₂ s₂” (by simp)

lemma Language.Theory.derivabilityComparison_defined : 𝚺₁-Relation T.DerivabilityComparison via pT.derivabilityComparisonDef := by
  intro v
  simp [LDef.TDef.derivabilityComparisonDef, HierarchySymbol.Semiformula.val_sigma,
    T.derivationOf_defined.df.iff, T.derivationOf_defined.proper.iff', Language.Theory.DerivabilityComparison]

instance Language.Theory.derivabilityComparison_definable : 𝚺₁-Relation T.DerivabilityComparison := T.derivabilityComparison_defined.to_definable

def _root_.LO.FirstOrder.Arith.LDef.TDef.provabilityComparisonDef {pL : LDef} (pT : pL.TDef) : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ sφ sψ, !insertDef sφ φ 0 ∧ !insertDef sψ ψ 0 ∧ !pT.derivabilityComparisonDef sφ sψ” (by simp)

lemma Language.Theory.provabilityComparison_defined : 𝚺₁-Relation T.ProvabilityComparison via pT.provabilityComparisonDef := by
  intro v; simp [LDef.TDef.provabilityComparisonDef, T.derivabilityComparison_defined.df.iff, Language.Theory.ProvabilityComparison, singleton_eq_insert, emptyset_def]

instance Language.Theory.provabilityComparison_definable : 𝚺₁-Relation T.ProvabilityComparison := T.provabilityComparison_defined.to_definable

/-- instance for definability tactic-/
instance Language.Theory.provabilityComparison_definable' : 𝚺-[0 + 1]-Relation T.ProvabilityComparison := T.provabilityComparison_definable

end

variable {T}

namespace Language.Theory.DerivabilityComparison

variable {Γ Δ : V}

lemma refl_iff_derivable : T.DerivabilityComparison Γ Γ ↔ T.Derivable Γ := by
  constructor
  · rintro ⟨d, dd, hd⟩
    exact ⟨d, dd⟩
  · rintro ⟨d, dd⟩
    have : ∃ b, T.DerivationOf b Γ ∧ ∀ z < b, ¬T.DerivationOf z Γ :=
      least_number_hh 𝚺 1 (P := (T.DerivationOf · Γ)) (by definability) dd
    rcases this with ⟨b, bd, h⟩
    exact ⟨b, bd, h⟩

lemma antisymm : T.DerivabilityComparison Γ Δ → T.DerivabilityComparison Δ Γ → Γ = Δ := by
  rintro ⟨dΓ, dΓd, HΓ⟩ ⟨dΔ, dΔd, HΔ⟩
  have : dΓ = dΔ := by
    by_contra ne
    wlog lt : dΓ < dΔ
    · have : dΓ ≤ dΔ := le_of_not_lt <| this dΔ dΔd HΔ dΓ dΓd HΓ (Ne.symm ne)
      have : dΔ ≤ dΓ := le_of_not_lt lt
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
      least_number_hh 𝚺 1 (P := fun z ↦ ∃ j, T.DerivationOf z (Γ j))
        (HierarchySymbol.Boldface.fintype_ex fun j ↦ by definability) (x := dᵢ) ⟨i, Hdᵢ⟩
  rcases this with ⟨z, ⟨j, hj⟩, H⟩
  exact ⟨j, fun k ↦ ⟨z, hj, fun w hw ↦ H w hw k⟩⟩

end Language.Theory.DerivabilityComparison

namespace Language.Theory.ProvabilityComparison

variable {φ ψ : V}

lemma refl_iff_provable : T.ProvabilityComparison φ φ ↔ T.Provable φ := Language.Theory.DerivabilityComparison.refl_iff_derivable

lemma antisymm : T.ProvabilityComparison φ ψ → T.ProvabilityComparison ψ φ → φ = ψ :=
  fun h₁ h₂ ↦ by
    simpa using mem_ext_iff.mp (Language.Theory.DerivabilityComparison.antisymm h₁ h₂) φ

lemma find_minimal_proof_fintype [Fintype ι] (φ : ι → V) (H : T.Provable (φ i)) :
    ∃ j, ∀ k, T.ProvabilityComparison (φ j) (φ k) := DerivabilityComparison.find_minimal_proof_fintype _ H

end Language.Theory.ProvabilityComparison

end WitnessComparisons

section ProvabilityComparisonOnArithmetic

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

/-- Provability predicate for arithmetic stronger than $\mathbf{R_0}$. -/
def _root_.LO.FirstOrder.Theory.ProvabilityComparisonₐ (φ ψ : V) : Prop := ((T + 𝐑₀').codeIn V).ProvabilityComparison φ ψ

def _root_.LO.FirstOrder.Theory.provabilityComparisonₐDef : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. !(T + 𝐑₀').tDef.provabilityComparisonDef φ ψ” (by simp)

lemma provabilityComparisonₐ_defined : 𝚺₁-Relation (T.ProvabilityComparisonₐ : V → V → Prop) via T.provabilityComparisonₐDef := by
  intro v; simp [FirstOrder.Theory.provabilityComparisonₐDef, FirstOrder.Theory.ProvabilityComparisonₐ, ((T + 𝐑₀').codeIn V).provabilityComparison_defined.df.iff]

@[simp] lemma eval_provabilityComparisonₐ (v) :
    Semiformula.Evalbm V v T.provabilityComparisonₐDef.val ↔ T.ProvabilityComparisonₐ (v 0) (v 1) := (provabilityComparisonₐ_defined T).df.iff v

instance provabilityComparisonₐ_definable : 𝚺₁-Relation (T.ProvabilityComparisonₐ : V → V → Prop) := (provabilityComparisonₐ_defined T).to_definable

/-- instance for definability tactic-/
instance provabilityComparisonₐ_definable' : 𝚺-[0 + 1]-Relation (T.ProvabilityComparisonₐ : V → V → Prop) := provabilityComparisonₐ_definable T

end ProvabilityComparisonOnArithmetic

end LO.Arith
