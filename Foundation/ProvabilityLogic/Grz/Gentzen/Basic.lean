module

public import Foundation.ProvabilityLogic.Sequent

/-!
# The sequent calculus of `Grz`

## References

- [Avr84]
- [SS21, Figure 1]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace Grz

variable {α : Type*} [DecidableEq α]

/-- The cut-free sequent calculus of `Grz`. -/
inductive Gentzen : Sequent α → Prop
  | axm (A) : Gentzen ({A} ⟹ {A})
  | botL : Gentzen ({⊥} ⟹ ∅)
  | wkL {Γ Γ' Δ} : Gentzen (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → Gentzen (Γ' ⟹ Δ)
  | wkR {Γ Δ Δ'} : Gentzen (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → Gentzen (Γ ⟹ Δ')
  | impL {Γ Δ A B} :
    Gentzen (Γ ⟹ insert A Δ) → Gentzen (insert B Γ ⟹ Δ) → Gentzen (insert (A 🡒 B) Γ ⟹ Δ)
  | impR {Γ Δ A B} : Gentzen (insert A Γ ⟹ insert B Δ) → Gentzen (Γ ⟹ insert (A 🡒 B) Δ)
  | boxT {Γ Δ A} : Gentzen (insert A Γ ⟹ Δ) → Gentzen (insert (□A) Γ ⟹ Δ)
  | boxGrz {Γ : FormulaFinset α} {A} : Gentzen (insert (□(A 🡒 □A)) Γ.box ⟹ {A}) → Gentzen (Γ.box ⟹ {□A})

@[inherit_doc] notation:45 "⊢ᴳ[Grz] " S:50 => Gentzen S

notation:45 "⊬ᴳ[Grz] " S:50 => ¬Gentzen S

namespace Gentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A : Formula α} {S : Sequent α}

lemma union (A) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᴳ[Grz] Γ ⟹ Δ :=
  wkR (wkL (axm A) (by simpa)) (by simpa)

lemma union' (A) (hΓ : A ∈ S.ant) (hΔ : A ∈ S.suc) : ⊢ᴳ[Grz] S := union A hΓ hΔ

lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᴳ[Grz] Γ ⟹ Δ := wkR (wkL botL (by simpa)) (by simp)

lemma wk (h : ⊢ᴳ[Grz] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[Grz] Γ' ⟹ Δ' := wkR (wkL h hΓ) hΔ

end Gentzen

end Grz

end FFL.ProvabilityLogic

end
