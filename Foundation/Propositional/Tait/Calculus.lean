module

public import Foundation.Propositional.Formula.NNFormula
public import Foundation.Logic.Calculus

@[expose] public section

namespace FFL.Propositional

abbrev Sequent (α : Type*) := Multiset (NNFormula α)

inductive Derivation : Sequent α → Type _
| identity (a : α) : Derivation ⦃NNFormula.atom a, NNFormula.natom a⦄
| cut : Derivation (Γ + ⦃φ⦄) → Derivation (Δ + ⦃∼φ⦄) → Derivation (Γ + Δ)
| wk : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| verum : Derivation ⦃⊤⦄
| or : Derivation (Γ + ⦃φ, ψ⦄) → Derivation (Γ + ⦃φ ⋎ ψ⦄)
| and : Derivation (Γ + ⦃φ⦄) → Derivation (Γ + ⦃ψ⦄) → Derivation (Γ + ⦃φ ⋏ ψ⦄)

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

protected abbrev cast (d : ⊢ᴸᴷ⁰ Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴷ⁰ Γ := e ▸ d

@[simp] lemma height_cast (d : ⊢ᴸᴷ⁰ Δ) (e : Δ = Γ) : height (Derivation.cast d e) = height d := by
  rcases e with rfl; simp [Derivation.cast]

def weakening (d : ⊢ᴸᴷ⁰ Δ) (h : Δ ⊆ Γ := by simp) : ⊢ᴸᴷ⁰ Γ := wk d h

def top (h : ⊤ ∈ Δ := by simp) : ⊢ᴸᴷ⁰ Δ := verum.wk (by simp [h])

def identity' (a : α) (hpos : .atom a ∈ Δ := by simp) (hneg : .natom a ∈ Δ := by simp) : ⊢ᴸᴷ⁰ Δ :=
  (identity a).wk (by intro φ hφ; rcases Multiset.mem_add.mp hφ with hφ | hφ <;> simp_all)

def tensor {φ ψ} (dφ : ⊢ᴸᴷ⁰ Γ + ⦃φ⦄) (dψ : ⊢ᴸᴷ⁰ Δ + ⦃ψ⦄) :
    ⊢ᴸᴷ⁰ Γ + Δ + ⦃φ ⋏ ψ⦄ :=
  and
    (dφ.weakening (by intro χ hχ; rcases Multiset.mem_add.mp hχ with hχ | hχ <;> simp_all))
    (dψ.weakening (by intro χ hχ; rcases Multiset.mem_add.mp hχ with hχ | hχ <;> simp_all))

/-- Identity expansion; the standard structural induction on propositional formulas (folklore). -/
def eta : (φ : NNFormula α) → ⊢ᴸᴷ⁰ ⦃φ, ∼φ⦄
  | .atom a | .natom a => identity' a
  | ⊤ | ⊥ => top
  | φ ⋏ ψ =>
    (or (Γ := ⦃φ ⋏ ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
      (tensor (Γ := ⦃∼φ⦄) (Δ := ⦃∼ψ⦄) (φ := φ) (ψ := ψ)
        (eta φ).cast (eta ψ).cast).cast).cast (by simp [add_comm])
  | φ ⋎ ψ =>
    (or (Γ := ⦃∼φ ⋏ ∼ψ⦄) (φ := φ) (ψ := ψ)
      (tensor (Γ := ⦃φ⦄) (Δ := ⦃ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
        (eta φ) (eta ψ)).cast).cast (by simp [add_comm])

def close (φ : NNFormula α) (hp : φ ∈ Δ := by simp) (hn : ∼φ ∈ Δ := by simp) : ⊢ᴸᴷ⁰ Δ :=
  eta φ |>.weakening (by intro ψ hψ; rcases Multiset.mem_add.mp hψ with hψ | hψ <;> simp_all)

instance : OneSidedLK (Derivation (α := α)) where
  weakening d := d.wk (by simp)
  contraction d := d.wk (by simp)
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
