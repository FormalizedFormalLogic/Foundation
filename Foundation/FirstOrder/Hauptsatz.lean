import Foundation.IntFO.Translation

/-!
#Algebraic Proofs of Cut Elimination

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination, The Journal of Logic and Algebraic Programming, Volume 49, Issues 1–2, 2001, Pages 15-30
 -/

namespace LO.FirstOrder

variable {L : Language}

inductive CFDerivationFrom (Ξ : Sequent L) : Sequent L → Type _
| axL (Γ) {k} (r : L.Rel k) (v) : CFDerivationFrom Ξ (.rel r v :: .nrel r v :: Γ)
| verum (Γ)    : CFDerivationFrom Ξ (⊤ :: Γ)
| or {Γ φ ψ}   : CFDerivationFrom Ξ (φ :: ψ :: Γ) → CFDerivationFrom Ξ (φ ⋎ ψ :: Γ)
| and {Γ φ ψ}  : CFDerivationFrom Ξ (φ :: Γ) → CFDerivationFrom Ξ (ψ :: Γ) → CFDerivationFrom Ξ (φ ⋏ ψ :: Γ)
| all {Γ φ z} (hφ : ¬φ.FVar? z) (hΓ : ∀ ψ ∈ Γ, ¬ψ.FVar? z) :
  CFDerivationFrom Ξ (φ/[&z] :: Γ) → CFDerivationFrom Ξ ((∀' φ) :: Γ)
| ex {Γ φ} (t) : CFDerivationFrom Ξ (φ/[t] :: Γ) → CFDerivationFrom Ξ ((∃' φ) :: Γ)
| wk {Γ Δ}     : CFDerivationFrom Ξ Δ → Δ ⊆ Γ → CFDerivationFrom Ξ Γ
| protected id : CFDerivationFrom Ξ Ξ

infix:45 " ⟶ᶜᶠ " => CFDerivationFrom

namespace CFDerivationFrom

variable {Ξ Γ Δ : Sequent L}

def trans {Ξ Γ Δ : Sequent L} : Ξ ⟶ᶜᶠ Γ → Γ ⟶ᶜᶠ Δ → Ξ ⟶ᶜᶠ Δ
  | _, .axL Γ r v => axL Γ r v
  | _, verum Γ    => verum Γ
  | b, or d       => or (b.trans d)
  | b, and d₁ d₂  => and (b.trans d₁) (b.trans d₂)
  | b, all hφ h d => all hφ h (b.trans d)
  | b, ex t d     => ex t (b.trans d)
  | b, wk d h     => wk (b.trans d) h
  | b, .id        => b

def cons {Ξ Γ : Sequent L} (φ) : Ξ ⟶ᶜᶠ Γ → φ :: Ξ ⟶ᶜᶠ φ :: Γ
  | .axL Γ r v => wk (axL Γ r v) (List.subset_cons_self _ _)
  | verum Γ    => wk (verum Γ) (List.subset_cons_self _ _)
  | @or _ _ Γ ψ χ d  =>
    have : φ :: Ξ ⟶ᶜᶠ ψ :: χ :: φ :: Γ := wk (cons φ d) (by simp; intro k; simp; tauto)
    wk (or this) (by simp)
  | @and _ _ Γ ψ χ d₁ d₂  =>
    have b₁ : φ :: Ξ ⟶ᶜᶠ ψ :: φ :: Γ := wk (cons φ d₁) (by simp)
    have b₂ : φ :: Ξ ⟶ᶜᶠ χ :: φ :: Γ := wk (cons φ d₂) (by simp)
    wk (and b₁ b₂) (by simp)
  | @all _ _ Γ ψ z hz Hz d      =>
    by {
    have : φ :: Ξ ⟶ᶜᶠ ψ/[&z] :: φ :: Γ := wk (cons φ d) (by simp)
    wk (all this) (by simp)}
  | ex t d     => wk (ex t (weaken hΞ (by rfl) d)) hΓ
  | wk d h     => wk (wk (weaken hΞ (by rfl) d) h) hΓ
  | .id        => by {  }

def weaken {Ξ Ξ' Γ Γ' : Sequent L} (hΞ : Ξ ⊆ Ξ') (hΓ : Γ ⊆ Γ') : Ξ ⟶ᶜᶠ Γ → Ξ' ⟶ᶜᶠ Γ'
  | .axL Γ r v => wk (axL Γ r v) hΓ
  | verum Γ    => wk (verum Γ) hΓ
  | or d       => wk (or (weaken hΞ (by rfl) d)) hΓ
  | and d₁ d₂  => wk (and (weaken hΞ (by rfl) d₁) (weaken hΞ (by rfl) d₂)) hΓ
  | all d      => wk (all (weaken hΞ (by rfl) d)) hΓ
  | ex t d     => wk (ex t (weaken hΞ (by rfl) d)) hΓ
  | wk d h     => wk (wk (weaken hΞ (by rfl) d) h) hΓ
  | .id        => by {  }

def wk (d : T ⟹ᶜᶠ Γ) (h : Γ ⊆ Δ) : T ⟹ᶜᶠ Δ := ⟨d.derivation.wk h, IsCutFree.wk h d.prop⟩

end CFDerivationFrom

namespace Hauptsatz

local notation "ℙ" => Sequent L

structure StrongerThan (q p : ℙ) where
  val : ∼p ⟹ᶜᶠ ∼q

scoped infix:60 " ≼ " => StrongerThan

namespace StrongerThan

protected def id (p : ℙ) : p ≼ p := ⟨id⟩

def trans {r q p : ℙ} (srq : r ≼ q) (sqp : q ≼ p) : r ≼ p := ⟨fun dq ↦ srq.val (sqp.val dq)⟩

def ofSubset {q p : ℙ} (h : q ⊇ p) : q ≼ p := ⟨fun d ↦ d.wk <| List.map_subset _ h⟩

def and {q p : ℙ} (φ ψ : SyntacticFormula L) : φ ⋏ ψ :: p ≼ φ :: ψ :: φ ⋏ ψ :: p := ⟨by { simp }⟩

end StrongerThan

end Hauptsatz

end LO.FirstOrder
