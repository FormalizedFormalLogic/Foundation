module

public import Foundation.ProvabilityLogic.Gentzen.Sequent

/-!
# The sequent calculus of `GL`

The cut-free sequent calculus of `GL`.

## References

- [SV82]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace GL

variable {α : Type*} [DecidableEq α]

/-- Derivability in the cut-free sequent calculus of `GL`. -/
inductive Gentzen : Sequent α → Prop
  | axm (A) : Gentzen ({A} ⟹ {A})
  | botL : Gentzen ({⊥} ⟹ ∅)
  | wkL {Γ Γ' Δ} : Gentzen (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → Gentzen (Γ' ⟹ Δ)
  | wkR {Γ Δ Δ'} : Gentzen (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → Gentzen (Γ ⟹ Δ')
  | impL {Γ Δ A B} :
    Gentzen (Γ ⟹ insert A Δ) → Gentzen (insert B Γ ⟹ Δ) → Gentzen (insert (A 🡒 B) Γ ⟹ Δ)
  | impR {Γ Δ A B} : Gentzen (insert A Γ ⟹ insert B Δ) → Gentzen (Γ ⟹ insert (A 🡒 B) Δ)
  | boxGL {Γ A} : Gentzen (insert (□A) (Γ ∪ Γ.box) ⟹ {A}) → Gentzen (Γ.box ⟹ {□A})

@[inherit_doc] notation:45 "⊢ᴳ[GL] " S:50 => Gentzen S

notation:45 "⊬ᴳ[GL] " S:50 => ¬Gentzen S

namespace Gentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α} {S : Sequent α}

lemma union (A) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᴳ[GL] Γ ⟹ Δ :=
  wkR (wkL (axm A) (by simpa)) (by simpa)

lemma union' (A) (hΓ : A ∈ S.ant) (hΔ : A ∈ S.suc) : ⊢ᴳ[GL] S := union A hΓ hΔ

lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᴳ[GL] Γ ⟹ Δ := wkR (wkL botL (by simpa)) (by simp)

lemma wk (h : ⊢ᴳ[GL] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[GL] Γ' ⟹ Δ' := wkR (wkL h hΓ) hΔ

end Gentzen

end GL

end FFL.ProvabilityLogic

end
