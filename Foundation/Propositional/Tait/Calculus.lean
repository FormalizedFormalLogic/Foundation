module

public import Foundation.Propositional.Formula.NNFormula
public import Foundation.Logic.Calculus

@[expose] public section

namespace LO.Propositional

abbrev Sequent (α : Type*) := List (NNFormula α)

inductive Derivation : Sequent α → Type _
| identity (a : α) : Derivation [NNFormula.atom a, NNFormula.natom a]
| cut : Derivation (φ :: Γ) → Derivation (∼φ :: Δ) → Derivation (Γ ++ Δ)
| wk : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| verum : Derivation [⊤]
| or : Derivation (φ :: ψ :: Γ) → Derivation (φ ⋎ ψ :: Γ)
| and : Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ⋏ ψ :: Γ)

prefix:45 "⊢ᴸᴷ⁰ " => Derivation

namespace Derivation

variable {T U : Theory α} {Δ Δ₁ Δ₂ Γ : Sequent α}

def height {Δ : Sequent α} : ⊢ᴸᴷ⁰ Δ → ℕ
  |identity _ => 0
  | cut dp dn => max dp.height dn.height + 1
  |    wk d _ => d.height + 1
  |     verum => 0
  |      or d => d.height + 1
  | and dp dq => max (height dp) (height dq) + 1

protected def cast (d : ⊢ᴸᴷ⁰ Δ) (e : Δ = Γ) : ⊢ᴸᴷ⁰ Γ := cast (by simp [e]) d

@[simp] lemma height_cast (d : ⊢ᴸᴷ⁰ Δ) (e : Δ = Γ) : height (Derivation.cast d e) = height d := by
  rcases e with rfl; simp [Derivation.cast]

def weakening (d : ⊢ᴸᴷ⁰ Δ) (h : Δ ⊆ Γ := by simp) : ⊢ᴸᴷ⁰ Γ := wk d h

def top (h : ⊤ ∈ Δ := by simp) : ⊢ᴸᴷ⁰ Δ := verum.wk (by simp [h])

def identity' (a : α) (hpos : .atom a ∈ Δ := by simp) (hneg : .natom a ∈ Δ := by simp) : ⊢ᴸᴷ⁰ Δ :=
  (identity a).wk (by simp [hpos, hneg])

def tensor {φ ψ} (dφ : ⊢ᴸᴷ⁰ φ :: Γ) (dψ : ⊢ᴸᴷ⁰ ψ :: Δ) : ⊢ᴸᴷ⁰ φ ⋏ ψ :: (Γ ++ Δ) := and dφ.weakening dψ.weakening

def rotate (d : ⊢ᴸᴷ⁰ φ :: Γ) : ⊢ᴸᴷ⁰ Γ ++ [φ] := d.weakening

def eta : (φ : NNFormula α) → ⊢ᴸᴷ⁰ [φ, ∼φ]
  | .atom a | .natom a => identity' a
  | ⊤ | ⊥ => top
  | φ ⋏ ψ => ((eta φ).tensor (eta ψ)).rotate.or.rotate
  | φ ⋎ ψ => ((eta φ).rotate.tensor (eta ψ).rotate).rotate.or

def close (φ : NNFormula α) (hp : φ ∈ Δ := by simp) (hn : ∼φ ∈ Δ := by simp) : ⊢ᴸᴷ⁰ Δ :=
  eta φ |>.weakening (by simp [hp, hn])

instance : OneSidedLK (Derivation (α := α)) where
  verum := verum
  and d₁ d₂ := d₁.and d₂
  or d := d.or
  wk d ss := d.wk ss
  identity φ := eta φ

instance : OneSidedLK.Cut (Derivation (α := α)) where
  cut dp dn := cut dp dn

end Derivation

/-! ## Classical proof system -/

inductive Proof.Symbol (α : Type*) : Type
  | symbol

notation "𝐋𝐊⁰" => Proof.Symbol.symbol

abbrev Proof (φ : NNFormula α) := ⊢ᴸᴷ⁰ [φ]

instance : Entailment (Proof.Symbol α) (NNFormula α) where
  Prf _ := Proof

namespace Proof

lemma def_eq (φ : NNFormula α) : (𝐋𝐊⁰ ⊢! φ) = (⊢ᴸᴷ⁰ [φ]) := rfl

instance : OneSidedLK.PrincipalEntailment (Derivation (α := α)) (𝐋𝐊⁰ : Proof.Symbol α) where
  equiv := Equiv.refl _

instance classical : Entailment.Cl (𝐋𝐊⁰ : Proof.Symbol α) := inferInstance

end Proof

abbrev NNFormula.IsTautology (φ : NNFormula α) : Prop := 𝐋𝐊⁰ ⊢ φ

end LO.Propositional

end
