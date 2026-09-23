module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic

@[expose] public section
/-!
# Local reflection principles for the provability abstraction

Local reflection schemas for an abstract provability predicate and their relation to consistency.

## References

- [Lin97]
- [AB05]
-/

namespace FFL.FirstOrder.ProvabilityAbstraction.Provability

open FFL.Entailment Axiomatized

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T)

abbrev refl (σ : Sentence L) : Sentence L := 𝔅 σ 🡒 σ

def reflOn (Γ : Sentence L → Prop) : Set (Sentence L) := Set.image 𝔅.refl Γ

variable {Γ Γ' : Sentence L → Prop}

@[simp]
lemma mem_localReflectionOn_iff {ψ : Sentence L} :
    ψ ∈ 𝔅.reflOn Γ ↔ ∃ σ, Γ σ ∧ ψ = 𝔅.refl σ := by
  simp [reflOn, refl, Set.image];
  tauto;

lemma localReflectionOn_mono (h : ∀ σ, Γ σ → Γ' σ) : 𝔅.reflOn Γ ⊆ 𝔅.reflOn Γ' :=
  Set.image_mono fun σ hσ ↦ h σ hσ

variable [L.DecidableEq]

theorem con_of_localReflection (h : Γ ⊥) : T ∪ 𝔅.reflOn Γ ⊢ 𝔅.con := by
  have h₁ : T ∪ 𝔅.reflOn Γ ⊢ 𝔅.refl ⊥ :=
    Axiomatized.by_axm (Set.mem_union_right _ ((mem_localReflectionOn_iff 𝔅).mpr ⟨⊥, h, rfl⟩));
  change T ∪ 𝔅.reflOn Γ ⊢ ∼𝔅 ⊥;
  cl_prover [h₁];

variable {σ : Sentence L}

theorem localReflection_of_con [𝔅.HBL2] [𝔅.FormalizedCompleteOn (∼σ)] :
    T₀ ⊢ 𝔅.con 🡒 𝔅.refl σ := by
  have h₁ : T₀ ⊢ ∼σ 🡒 𝔅 (∼σ) := formalized_complete_on;
  have h₂ : T₀ ⊢ 𝔅 (σ 🡒 ∼σ 🡒 ⊥) := D1 (by cl_prover);
  have h₃ : T₀ ⊢ 𝔅 (σ 🡒 ∼σ 🡒 ⊥) 🡒 𝔅 σ 🡒 𝔅 (∼σ 🡒 ⊥) := D2;
  have h₄ : T₀ ⊢ 𝔅 (∼σ 🡒 ⊥) 🡒 𝔅 (∼σ) 🡒 𝔅 ⊥ := D2;
  change T₀ ⊢ ∼𝔅 ⊥ 🡒 𝔅.refl σ;
  cl_prover [h₁, h₂, h₃, h₄];

variable {π : Sentence L}

theorem inconsistent_of_localReflection_provable [Diagonalization T₀] [T₀ ⪯ T] [𝔅.HBL]
    (h : insert π T ⊢ 𝔅.refl (∼π)) : Inconsistent (insert π T) := by
  have h₁ : T ⊢ π 🡒 𝔅.refl (∼π) := deduction_iff.mp h;
  have h₂ : T ⊢ ∼π := löb_theorem (by cl_prover [h₁]);
  exact inconsistent_of_provable <| by cl_prover [adjoin! π T, to_adjoin (φ := π) h₂];

theorem inconsistent_of_provable_localReflectionOn_insert
    [Diagonalization T₀] [T₀ ⪯ T] [𝔅.HBL] {Γ Γ' : Sentence L → Prop}
    (hd : ∀ σ, Γ σ → Γ' (∼σ)) (hπ : Γ π) (h : insert π T ⊢* 𝔅.reflOn Γ') :
    Inconsistent (insert π T) :=
  inconsistent_of_localReflection_provable 𝔅
    (h ((mem_localReflectionOn_iff 𝔅).mpr ⟨∼π, hd π hπ, rfl⟩))

end FFL.FirstOrder.ProvabilityAbstraction.Provability
