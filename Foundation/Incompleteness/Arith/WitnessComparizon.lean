import Foundation.Incompleteness.Arith.D3
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Incompleteness.ToFoundation.Basic

noncomputable section

open Classical

namespace LO.Arith

open LO.FirstOrder LO.FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

variable (T : L.Theory) {pT : pL.TDef} [T.Defined pT]

def Language.Theory.DerivabilityComparizon (s₁ s₂ : V) : Prop := ∃ d₁, T.DerivationOf d₁ s₁ ∧ ∀ d₂ < d₁, ¬T.DerivationOf d₂ s₂

def Language.Theory.ProvabilityComparizon (φ ψ : V) : Prop := T.DerivabilityComparizon {φ} {ψ}

section

def _root_.LO.FirstOrder.Arith.LDef.TDef.derivabilityComparizonDef {pL : LDef} (pT : pL.TDef) : 𝚺₁.Semisentence 2 := .mkSigma
  “s₁ s₂. ∃ d₁, !pT.derivationOfDef.sigma d₁ s₁ ∧ ∀ d₂ < d₁, ¬!pT.derivationOfDef.pi d₂ s₂” (by simp)

lemma Language.Theory.derivabilityComparizon_defined : 𝚺₁-Relation T.DerivabilityComparizon via pT.derivabilityComparizonDef := by
  intro v
  simp [LDef.TDef.derivabilityComparizonDef, HierarchySymbol.Semiformula.val_sigma,
    T.derivationOf_defined.df.iff, T.derivationOf_defined.proper.iff', Language.Theory.DerivabilityComparizon]

instance Language.Theory.derivabilityComparizon_definable : 𝚺₁-Relation T.DerivabilityComparizon := T.derivabilityComparizon_defined.to_definable

def _root_.LO.FirstOrder.Arith.LDef.TDef.provabilityComparizonDef {pL : LDef} (pT : pL.TDef) : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ sφ sψ, !insertDef sφ φ 0 ∧ !insertDef sψ ψ 0 ∧ !pT.derivabilityComparizonDef sφ sψ” (by simp)

lemma Language.Theory.provabilityComparizon_defined : 𝚺₁-Relation T.ProvabilityComparizon via pT.provabilityComparizonDef := by
  intro v; simp [LDef.TDef.provabilityComparizonDef, T.derivabilityComparizon_defined.df.iff, Language.Theory.ProvabilityComparizon, singleton_eq_insert, emptyset_def]

instance Language.Theory.provabilityComparizon_definable : 𝚺₁-Relation T.ProvabilityComparizon := T.provabilityComparizon_defined.to_definable

/-- instance for definability tactic-/
instance Language.Theory.provabilityComparizon_definable' : 𝚺-[0 + 1]-Relation T.ProvabilityComparizon := T.provabilityComparizon_definable

end

variable {T}

namespace Language.Theory.DerivabilityComparizon

variable {Γ Δ : V}

lemma refl_iff_derivable : T.DerivabilityComparizon Γ Γ ↔ T.Derivable Γ := by
  constructor
  · rintro ⟨d, dd, hd⟩
    exact ⟨d, dd⟩
  · rintro ⟨d, dd⟩
    have : ∃ b, T.DerivationOf b Γ ∧ ∀ z < b, ¬T.DerivationOf z Γ :=
      least_number_hh 𝚺 1 (P := (T.DerivationOf · Γ)) (by definability) dd
    rcases this with ⟨b, bd, h⟩
    exact ⟨b, bd, h⟩

lemma antisymm : T.DerivabilityComparizon Γ Δ → T.DerivabilityComparizon Δ Γ → Γ = Δ := by
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

end Language.Theory.DerivabilityComparizon

namespace Language.Theory.ProvabilityComparizon

variable {φ ψ : V}

lemma refl_iff_provable : T.ProvabilityComparizon φ φ ↔ T.Provable φ := Language.Theory.DerivabilityComparizon.refl_iff_derivable

lemma antisymm : T.ProvabilityComparizon φ ψ → T.ProvabilityComparizon ψ φ → φ = ψ :=
  fun h₁ h₂ ↦ by
    simpa using mem_ext_iff.mp (Language.Theory.DerivabilityComparizon.antisymm h₁ h₂) φ

end Language.Theory.ProvabilityComparizon

end LO.Arith

namespace LO.FirstOrder.Arith



end LO.FirstOrder.Arith
