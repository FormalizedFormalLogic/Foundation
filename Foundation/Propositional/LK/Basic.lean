module

public import Foundation.Propositional.Formula.NNFormula
public import Foundation.Logic.Calculus

@[expose] public section

namespace FFL.Propositional

abbrev Sequent (α : Type*) := Multiset (NNFormula α)

inductive Derivation : Sequent α → Type _
| identity (a : α) : Derivation ⦃NNFormula.atom a, NNFormula.natom a⦄
| cut : Derivation (Γ + ⦃φ⦄) → Derivation (Δ + ⦃∼φ⦄) → Derivation (Γ + Δ)
| contraction : Derivation (Γ + ⦃φ, φ⦄) → Derivation (Γ + ⦃φ⦄)
| weakening : Derivation Γ → Derivation (Γ + ⦃φ⦄)
| verum : Derivation ⦃⊤⦄
| or : Derivation (Γ + ⦃φ, ψ⦄) → Derivation (Γ + ⦃φ ⋎ ψ⦄)
| and : Derivation (Γ + ⦃φ⦄) → Derivation (Γ + ⦃ψ⦄) → Derivation (Γ + ⦃φ ⋏ ψ⦄)

prefix:45 "⊢ᴸᴷ⁰ " => Derivation

namespace Derivation

variable {T U : Theory α} {Δ Δ₁ Δ₂ Γ : Sequent α}

def height {Δ : Sequent α} : ⊢ᴸᴷ⁰ Δ → ℕ
  |identity _ => 0
  | cut dp dn => max dp.height dn.height + 1
  | contraction d | weakening d => d.height + 1
  |     verum => 0
  |      or d => d.height + 1
  | and dp dq => max (height dp) (height dq) + 1

protected abbrev cast (d : ⊢ᴸᴷ⁰ Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴷ⁰ Γ := e ▸ d

@[simp] lemma height_cast (d : ⊢ᴸᴷ⁰ Δ) (e : Δ = Γ) : height (Derivation.cast d e) = height d := by
  rcases e with rfl; simp [Derivation.cast]

instance : Structural (Derivation (α := α)) where
  weakening d := d.weakening
  contraction d := d.contraction

/-- Enumerates the end sequent by recursion on the local inference rules.
This is a routine syntactic construction. -/
def traversal [DecidableEq α] {Γ : Sequent α} : ⊢ᴸᴷ⁰ Γ → Γ.Traversal
  | identity a => (Multiset.Traversal.atom (NNFormula.atom a)).succ (NNFormula.natom a)
  | cut d dn => d.traversal.remove.add dn.traversal.remove
  | contraction (φ := φ) d => (d.traversal.cast (by abel)).remove (a := φ)
  | weakening (φ := φ) d => d.traversal.succ φ
  | verum => .atom ⊤
  | or (φ := φ) (ψ := ψ) d =>
      ((d.traversal.cast (by abel)).remove (a := ψ)).remove (a := φ) |>.succ (φ ⋎ ψ)
  | and (φ := φ) (ψ := ψ) d _ => d.traversal.remove.succ (φ ⋏ ψ)

/-- Applies structural rules along supplied traversals (a routine derived rule). -/
def contra [DecidableEq α] (d : ⊢ᴸᴷ⁰ Δ) (t : Γ.Traversal)
    (h : Δ ⊆ Γ := by simp) : ⊢ᴸᴷ⁰ Γ :=
  Structural.ofSubset d.traversal t d h

/-- Combines two derivations by weakening and conjunction (a standard derived rule). -/
def tensor {φ ψ} (tΓ : Γ.Traversal) (tΔ : Δ.Traversal)
    (dφ : ⊢ᴸᴷ⁰ Γ + ⦃φ⦄) (dψ : ⊢ᴸᴷ⁰ Δ + ⦃ψ⦄) : ⊢ᴸᴷ⁰ Γ + Δ + ⦃φ ⋏ ψ⦄ :=
  and (Structural.weakenMany tΔ dφ |>.cast) (Structural.weakenMany tΓ dψ |>.cast)

/-- Identity expansion; the standard structural induction on propositional formulas (folklore). -/
def eta : (φ : NNFormula α) → ⊢ᴸᴷ⁰ ⦃φ, ∼φ⦄
  | .atom a => identity a
  | .natom a => (identity a).cast (by simp [add_comm])
  | ⊤ => verum.weakening
  | ⊥ => (verum.weakening (φ := ⊥)).cast (by simp [add_comm])
  | φ ⋏ ψ =>
    (or (Γ := ⦃φ ⋏ ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
      (tensor (Γ := ⦃∼φ⦄) (Δ := ⦃∼ψ⦄) (φ := φ) (ψ := ψ)
        (.atom _) (.atom _) (eta φ).cast (eta ψ).cast).cast).cast (by simp [add_comm])
  | φ ⋎ ψ =>
    (or (Γ := ⦃∼φ ⋏ ∼ψ⦄) (φ := φ) (ψ := ψ)
      (tensor (Γ := ⦃φ⦄) (Δ := ⦃ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
        (.atom _) (.atom _) (eta φ) (eta ψ)).cast).cast (by simp [add_comm])

instance : OneSidedLK (Derivation (α := α)) where
  weakening d := d.weakening
  contraction d := d.contraction
  verum := verum
  and d₁ d₂ := d₁.and d₂
  or d := d.or
  identity φ := eta φ

instance : OneSidedLK.Cut (Derivation (α := α)) where
  cut dp dn := cut dp dn

end Derivation

/-! ## Classical proof system -/

inductive Proof.Symbol (α : Type*) : Type
  | symbol

notation "𝐋𝐊⁰" => Proof.Symbol.symbol

abbrev Proof (φ : NNFormula α) := ⊢ᴸᴷ⁰ ⦃φ⦄

instance : Entailment (Proof.Symbol α) (NNFormula α) where
  Prf _ := Proof

namespace Proof

lemma def_eq (φ : NNFormula α) : (𝐋𝐊⁰ ⊢! φ) = (⊢ᴸᴷ⁰ ⦃φ⦄) := rfl

instance : OneSidedLK.PrincipalEntailment (Derivation (α := α)) (𝐋𝐊⁰ : Proof.Symbol α) where
  equiv := Equiv.refl _

instance classical : Entailment.Cl (𝐋𝐊⁰ : Proof.Symbol α) := inferInstance

end Proof

abbrev NNFormula.IsTautology (φ : NNFormula α) : Prop := 𝐋𝐊⁰ ⊢ φ

end FFL.Propositional

end
