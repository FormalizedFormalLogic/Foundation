module

public import Foundation.SecondOrder.LK.Basic

/-!
# Second-order one-sided $\mathbf{LK}$ with restricted comprehension

The structural rules are the standard local weakening and contraction rules.
-/

@[expose] public section

namespace FFL.SecondOrder

open FirstOrder

variable {L : Language}

namespace LK.Derivation

def RestrictedComprehension (C : Semiproposition L 0 1 → Prop) :
    {Γ : Sequent L} → Derivation Γ → Prop
  | _, .identity => True
  | _, .cut d₁ d₂ => d₁.RestrictedComprehension C ∧ d₂.RestrictedComprehension C
  | _, .contraction d => d.RestrictedComprehension C
  | _, .weakening d => d.RestrictedComprehension C
  | _, .verum => True
  | _, .and d₁ d₂ => d₁.RestrictedComprehension C ∧ d₂.RestrictedComprehension C
  | _, .or d => d.RestrictedComprehension C
  | _, .all₁ d => d.RestrictedComprehension C
  | _, .exs₁ d => d.RestrictedComprehension C
  | _, .all₂ d => d.RestrictedComprehension C
  | _, .exs₂ (ψ := ψ) d => d.RestrictedComprehension C ∧ C ψ

namespace RestrictedComprehension

variable {C : Semiproposition L 0 1 → Prop} {Γ Δ Ξ : Sequent L} {φ ψ χ : Proposition L}

@[simp] lemma cut_iff
    (d₁ : Derivation (Γ + ⦃φ⦄)) (d₂ : Derivation (Δ + ⦃∼φ⦄)) :
    (d₁.cut d₂).RestrictedComprehension C ↔
    d₁.RestrictedComprehension C ∧ d₂.RestrictedComprehension C := Iff.rfl

@[simp] lemma contraction_iff
    (d : Derivation (Γ + ⦃φ, φ⦄)) :
    d.contraction.RestrictedComprehension C ↔ d.RestrictedComprehension C := Iff.rfl

@[simp] lemma weakening_iff
    (d : Derivation Γ) :
    (d.weakening : Derivation (Γ + ⦃φ⦄)).RestrictedComprehension C ↔
    d.RestrictedComprehension C := Iff.rfl

@[simp] lemma or_iff
    (d : Derivation (Γ + ⦃φ, ψ⦄)) :
    d.or.RestrictedComprehension C ↔ d.RestrictedComprehension C := Iff.rfl

@[simp] lemma all₁_iff
    {φ : Semiproposition L 0 1}
    (d : Derivation (LK.Sequent.shift₀ Γ + ⦃φ.free₀⦄)) :
    d.all₁.RestrictedComprehension C ↔ d.RestrictedComprehension C := Iff.rfl

@[simp] lemma exs₁_iff
    {φ : Semiproposition L 0 1} {t}
    (d : Derivation (Γ + ⦃φ/[t]⦄)) :
    d.exs₁.RestrictedComprehension C ↔ d.RestrictedComprehension C := Iff.rfl

@[simp] lemma all₂_iff
    {φ : Semiproposition L 1 0}
    (d : Derivation (LK.Sequent.shift₁ Γ + ⦃φ.free₁⦄)) :
    d.all₂.RestrictedComprehension C ↔ d.RestrictedComprehension C := Iff.rfl

@[simp] lemma exs₂_iff
    {φ : Semiproposition L 1 0} {ψ : Semiproposition L 0 1}
    (d : Derivation (Γ + ⦃φ/⟦ψ⟧⦄)) :
    d.exs₂.RestrictedComprehension C ↔ d.RestrictedComprehension C ∧ C ψ := Iff.rfl

end RestrictedComprehension

end LK.Derivation

abbrev LK.DerivationRestrictedComprehension (C : Semiproposition L 0 1 → Prop) (Γ : Sequent L) :=
  {d : LK.Derivation Γ // d.RestrictedComprehension C}

variable (L)

structure TheoryRestrictedComprehension where
  theory : Set (Sentence L)
  comprehension : Semiproposition L 0 1 → Prop

variable {L}

@[coe] def Theory.toTheoryRestrictedComprehension (T : Theory L) :
    TheoryRestrictedComprehension L :=
  { theory := T, comprehension _ := True }

instance : Coe (Theory L) (TheoryRestrictedComprehension L) :=
  ⟨Theory.toTheoryRestrictedComprehension⟩

structure TheoryRestrictedComprehension.Proof
    (T : TheoryRestrictedComprehension L) (σ : Sentence L) where
  axioms : Multiset (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T.theory
  derivation :
    OneSidedLK.Pullback
      (LK.DerivationRestrictedComprehension T.comprehension)
      (Rew.emb.app.comp FirstOrder.Rewriting.emb)
    (⦃σ⦄ + ∼axioms)

namespace TheoryRestrictedComprehension.Proof

instance : Entailment (TheoryRestrictedComprehension L) (Sentence L) where
  Entails 𝓢 φ := Nonempty (TheoryRestrictedComprehension.Proof 𝓢 φ)

attribute [simp] TheoryRestrictedComprehension.Proof.axioms_mem

end TheoryRestrictedComprehension.Proof

end FFL.SecondOrder
