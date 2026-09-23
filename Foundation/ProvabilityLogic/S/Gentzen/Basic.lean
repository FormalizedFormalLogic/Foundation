module

public import Foundation.ProvabilityLogic.GL.Gentzen.Basic

/-!
# The sequent calculus of `S`

## References

- [KK23]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace S

variable {α : Type*} [DecidableEq α]

/-- The upper layer of the two-layered cut-free sequent calculus of `S`, whose lower layer is the
sequent calculus of `GL`. -/
inductive Gentzen : Sequent α → Prop
  | ofGL {S} : ⊢ᴳ[GL] S → Gentzen S
  | impL {Γ Δ A B} :
    Gentzen (Γ ⟹ insert A Δ) → Gentzen (insert B Γ ⟹ Δ) → Gentzen (insert (A 🡒 B) Γ ⟹ Δ)
  | impR {Γ Δ A B} : Gentzen (insert A Γ ⟹ insert B Δ) → Gentzen (Γ ⟹ insert (A 🡒 B) Δ)
  | boxL {Γ Δ A} : Gentzen (insert A Γ ⟹ Δ) → Gentzen (insert (□A) Γ ⟹ Δ)

@[inherit_doc] notation:45 "⊢ᴳ[S] " S:50 => Gentzen S

notation:45 "⊬ᴳ[S] " S:50 => ¬Gentzen S

lemma Gentzen.isImpClosed : Sequent.IsImpClosed (Gentzen (α := α)) :=
  ⟨fun h₁ h₂ ↦ .ofGL (GL.Gentzen.union' _ h₁ h₂), .impL, .impR⟩

end S

end FFL.ProvabilityLogic

end
