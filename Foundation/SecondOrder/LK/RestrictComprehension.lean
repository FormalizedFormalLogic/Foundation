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

inductive RestrictedComprehension (C : Semiproposition L 0 1 → Prop) :
    {Γ : Sequent L} → Derivation Γ → Prop
| identity : RestrictedComprehension C Derivation.identity
| cut {Γ Δ φ} {d₁ : Derivation (Γ + ⦃φ⦄)} {d₂ : Derivation (Δ + ⦃∼φ⦄)} :
    d₁.RestrictedComprehension C → d₂.RestrictedComprehension C →
    (d₁.cut d₂).RestrictedComprehension C
| contraction {Γ φ} {d : Derivation (Γ + ⦃φ, φ⦄)} :
    d.RestrictedComprehension C → d.contraction.RestrictedComprehension C
| weakening {Γ} {d : Derivation Γ} :
    d.RestrictedComprehension C → d.weakening.RestrictedComprehension C
| verum : RestrictedComprehension C Derivation.verum
| and {Γ φ ψ} {d₁ : Derivation (Γ + ⦃φ⦄)} {d₂ : Derivation (Γ + ⦃ψ⦄)} :
    d₁.RestrictedComprehension C → d₂.RestrictedComprehension C →
      (d₁.and d₂).RestrictedComprehension C
| or {Γ φ ψ} {d : Derivation (Γ + ⦃φ, ψ⦄)} :
    d.RestrictedComprehension C → d.or.RestrictedComprehension C
| all₁ {Γ} {φ : Semiproposition L 0 1} {d : Derivation (LK.Sequent.shift₀ Γ + ⦃φ.free₀⦄)} :
    d.RestrictedComprehension C → d.all₁.RestrictedComprehension C
| exs₁ {Γ φ t} {d : Derivation (Γ + ⦃φ/[t]⦄)} :
    d.RestrictedComprehension C → d.exs₁.RestrictedComprehension C
| all₂ {Γ} {φ : Semiproposition L 1 0} {d : Derivation (LK.Sequent.shift₁ Γ + ⦃φ.free₁⦄)} :
    d.RestrictedComprehension C → d.all₂.RestrictedComprehension C
| exs₂ {Γ φ} {ψ : Semiproposition L 0 1} {d : Derivation (Γ + ⦃φ/⟦ψ⟧⦄)} :
    d.RestrictedComprehension C → C ψ → d.exs₂.RestrictedComprehension C

namespace RestrictedComprehension

variable {C : Semiproposition L 0 1 → Prop} {Γ Δ Ξ : Sequent L} {φ ψ χ : Proposition L}

attribute [simp] identity verum

@[simp] lemma cut_iff
    (d₁ : Derivation (Γ + ⦃φ⦄)) (d₂ : Derivation (Δ + ⦃∼φ⦄)) :
    (d₁.cut d₂).RestrictedComprehension C ↔
    d₁.RestrictedComprehension C ∧ d₂.RestrictedComprehension C := sorry

@[simp] lemma contraction_iff
    (d : Derivation (Γ + ⦃φ, φ⦄)) :
    d.contraction.RestrictedComprehension C ↔ d.RestrictedComprehension C := sorry

@[simp] lemma weakening_iff
    (d : Derivation Γ) :
    (d.weakening : Derivation (Γ + ⦃φ⦄)).RestrictedComprehension C ↔
    d.RestrictedComprehension C := sorry

@[simp] lemma or_iff
    (d : Derivation (Γ + ⦃φ, ψ⦄)) :
    d.or.RestrictedComprehension C ↔ d.RestrictedComprehension C := sorry

@[simp] lemma all₁_iff
    {φ : Semiproposition L 0 1}
    (d : Derivation (LK.Sequent.shift₀ Γ + ⦃φ.free₀⦄)) :
    d.all₁.RestrictedComprehension C ↔ d.RestrictedComprehension C := sorry

@[simp] lemma exs₁_iff
    {φ : Semiproposition L 0 1} {t}
    (d : Derivation (Γ + ⦃φ/[t]⦄)) :
    d.exs₁.RestrictedComprehension C ↔ d.RestrictedComprehension C := sorry

@[simp] lemma all₂_iff
    {φ : Semiproposition L 1 0}
    (d : Derivation (LK.Sequent.shift₁ Γ + ⦃φ.free₁⦄)) :
    d.all₂.RestrictedComprehension C ↔ d.RestrictedComprehension C := sorry

@[simp] lemma exs₂_iff
    {φ : Semiproposition L 1 0} {ψ : Semiproposition L 0 1}
    (d : Derivation (Γ + ⦃φ/⟦ψ⟧⦄)) :
    d.exs₂.RestrictedComprehension C ↔ d.RestrictedComprehension C ∧ C ψ := sorry

end RestrictedComprehension

end LK.Derivation

abbrev LK.DerivationRestrictedComprehension (C : Semiproposition L 0 1 → Prop) (Γ : Sequent L) :=
  {d : LK.Derivation Γ // d.RestrictedComprehension C}

variable (L)

structure TheoryWithComprehension where
  theory : Theory L
  comprehension : Semiproposition L 0 1 → Prop

variable {L}

structure TheoryWithComprehension.Proof
    (T : TheoryWithComprehension L) (σ : Sentence L) where
  axioms : Multiset (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T.theory
  derivation :
    OneSidedLK.Pullback
      (LK.DerivationRestrictedComprehension T.comprehension)
      (Rew.emb.app.comp FirstOrder.Rewriting.emb)
    (⦃σ⦄ + ∼axioms)

namespace TheoryWithComprehension.Proof

instance : Entailment (TheoryWithComprehension L) (Sentence L) where
  Entails 𝓢 φ := Nonempty (TheoryWithComprehension.Proof 𝓢 φ)

attribute [simp] TheoryWithComprehension.Proof.axioms_mem

end TheoryWithComprehension.Proof

end FFL.SecondOrder
