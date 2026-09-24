module

public import Foundation.Propositional.Formula.NNFormula
public import Foundation.Logic.Calculus

@[expose] public section

namespace FFL.Propositional

abbrev LK.Sequent (α : Type*) := Multiset (NNFormula α)

inductive LK.Derivation {α : Type*} : LK.Sequent α → Type _
| identity (a : α) : LK.Derivation ⦃NNFormula.atom a, NNFormula.natom a⦄
| cut {Γ Δ : LK.Sequent α} {φ : NNFormula α} :
    LK.Derivation (Γ + ⦃φ⦄) → LK.Derivation (Δ + ⦃∼φ⦄) → LK.Derivation (Γ + Δ)
| contraction {Γ : LK.Sequent α} {φ : NNFormula α} :
    LK.Derivation (Γ + ⦃φ, φ⦄) → LK.Derivation (Γ + ⦃φ⦄)
| weakening {Γ : LK.Sequent α} {φ : NNFormula α} : LK.Derivation Γ → LK.Derivation (Γ + ⦃φ⦄)
| verum : LK.Derivation ⦃⊤⦄
| or {Γ : LK.Sequent α} {φ ψ : NNFormula α} :
    LK.Derivation (Γ + ⦃φ, ψ⦄) → LK.Derivation (Γ + ⦃φ ⋎ ψ⦄)
| and {Γ : LK.Sequent α} {φ ψ : NNFormula α} :
    LK.Derivation (Γ + ⦃φ⦄) → LK.Derivation (Γ + ⦃ψ⦄) → LK.Derivation (Γ + ⦃φ ⋏ ψ⦄)

prefix:45 "⊢ᴸᴷ⁰ " => LK.Derivation

namespace LK.Derivation

variable {α : Type*} {T U : Theory α} {Δ Δ₁ Δ₂ Γ : LK.Sequent α}

def height {Δ : LK.Sequent α} : ⊢ᴸᴷ⁰ Δ → ℕ
  |identity _ => 0
  | cut dp dn => max dp.height dn.height + 1
  | contraction d | weakening d => d.height + 1
  |     verum => 0
  |      or d => d.height + 1
  | and dp dq => max (height dp) (height dq) + 1

protected abbrev cast (d : ⊢ᴸᴷ⁰ Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴷ⁰ Γ := e ▸ d

@[simp] lemma height_cast (d : ⊢ᴸᴷ⁰ Δ) (e : Δ = Γ) :
    height (LK.Derivation.cast d e) = height d := by
  rcases e with rfl; simp [LK.Derivation.cast]

instance : Structural (LK.Derivation (α := α)) where
  weakening d := d.weakening
  contraction d := d.contraction

/-- Enumerates the end sequent by recursion on the local inference rules.
This is a routine syntactic construction. -/
def traversal [DecidableEq α] {Γ : LK.Sequent α} : ⊢ᴸᴷ⁰ Γ → Γ.Traversal
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

instance : OneSidedLK (LK.Derivation (α := α)) where
  weakening d := d.weakening
  contraction d := d.contraction
  verum := verum
  and d₁ d₂ := d₁.and d₂
  or d := d.or
  identity φ := eta φ

instance : OneSidedLK.Cut (LK.Derivation (α := α)) where
  cut dp dn := cut dp dn

end LK.Derivation

/-! ## Classical proof system -/

inductive LK.Proof.Symbol (α : Type*) : Type
  | symbol

notation "𝐋𝐊⁰" => LK.Proof.Symbol.symbol

variable {α : Type*}

abbrev LK.Proof (φ : NNFormula α) := ⊢ᴸᴷ⁰ ⦃φ⦄

instance : Entailment (LK.Proof.Symbol α) (NNFormula α) where
  Entails _ φ := Nonempty (LK.Proof φ)

namespace LK.Proof

instance : OneSidedLK.PrincipalEntailment (LK.Derivation (α := α)) (𝐋𝐊⁰ : LK.Proof.Symbol α) where
  iff := Iff.rfl

instance classical : Entailment.Cl (𝐋𝐊⁰ : LK.Proof.Symbol α) := inferInstance

end LK.Proof

abbrev NNFormula.IsTautology (φ : NNFormula α) : Prop := 𝐋𝐊⁰ ⊢ φ

end FFL.Propositional

end
