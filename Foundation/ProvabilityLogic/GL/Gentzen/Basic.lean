module

public import Foundation.ProvabilityLogic.Sequent

/-!
# The sequent calculus of `GL`

## References

- [SV82]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace GL

variable {α : Type*} [DecidableEq α]

/-- The cut-free sequent calculus of `GL`. -/
inductive Gentzen : Sequent α → Prop
  | axm (A) : Gentzen ({A} ⟹ {A})
  | botL : Gentzen ({⊥} ⟹ ∅)
  | wkL {Γ Γ' Δ} : Gentzen (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → Gentzen (Γ' ⟹ Δ)
  | wkR {Γ Δ Δ'} : Gentzen (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → Gentzen (Γ ⟹ Δ')
  | impL {Γ Δ A B} :
    Gentzen (Γ ⟹ insert A Δ) → Gentzen (insert B Γ ⟹ Δ) → Gentzen (insert (A 🡒 B) Γ ⟹ Δ)
  | impR {Γ Δ A B} : Gentzen (insert A Γ ⟹ insert B Δ) → Gentzen (Γ ⟹ insert (A 🡒 B) Δ)
  | boxGL {Γ A} : Gentzen (insert (□A) (Γ ∪ Γ.box) ⟹ {A}) → Gentzen (Γ.box ⟹ {□A})

@[inherit_doc] notation:45 "⊢ᴳ[𝐆𝐋] " S:50 => Gentzen S

notation:45 "⊬ᴳ[𝐆𝐋] " S:50 => ¬Gentzen S

namespace Gentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α} {S : Sequent α}

lemma union (A) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ :=
  wkR (wkL (axm A) (by simpa)) (by simpa)

lemma union' (A) (hΓ : A ∈ S.ant) (hΔ : A ∈ S.suc) : ⊢ᴳ[𝐆𝐋] S := union A hΓ hΔ

lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ := wkR (wkL botL (by simpa)) (by simp)

lemma wk (h : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐆𝐋] Γ' ⟹ Δ' := wkR (wkL h hΓ) hΔ

lemma negL (h : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert A Δ) : ⊢ᴳ[𝐆𝐋] insert (∼A) Γ ⟹ Δ :=
  impL h (botL_mem (Finset.mem_insert_self _ _))

lemma negR (h : ⊢ᴳ[𝐆𝐋] insert A Γ ⟹ Δ) : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert (∼A) Δ := impR (wkR h)

lemma orL (h₁ : ⊢ᴳ[𝐆𝐋] insert A Γ ⟹ Δ) (h₂ : ⊢ᴳ[𝐆𝐋] insert B Γ ⟹ Δ) :
    ⊢ᴳ[𝐆𝐋] insert (A ⋎ B) Γ ⟹ Δ := impL (negR h₁) h₂

lemma orR (h : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert A (insert B Δ)) : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert (A ⋎ B) Δ := impR (negL h)

end Gentzen

end GL

end FFL.ProvabilityLogic

end
