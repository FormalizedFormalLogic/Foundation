module

public import Foundation.ProvabilityLogic.GL.Gentzen.Basic

/-!
# The sequent calculus of `A`

## References

- [AB05, Lemma 51]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace A

variable {α : Type*} [DecidableEq α]

/-- The two-layered cut-free sequent calculus of `A`: the lower layer is that of `GL`, and the
upper layer may assume the consistency statements `∼□^[n]⊥`.

- [AB05, Lemma 51]
-/
inductive Gentzen : LayeredSequent 2 α → Prop
  | axm (ℓ) (A) : Gentzen ({A} ⟹[ℓ] {A})
  | botL (ℓ) : Gentzen ({⊥} ⟹[ℓ] ∅)
  | wkL {ℓ Γ Γ' Δ} : Gentzen (Γ ⟹[ℓ] Δ) → (_ : Γ ⊆ Γ' := by grind) → Gentzen (Γ' ⟹[ℓ] Δ)
  | wkR {ℓ Γ Δ Δ'} : Gentzen (Γ ⟹[ℓ] Δ) → (_ : Δ ⊆ Δ' := by grind) → Gentzen (Γ ⟹[ℓ] Δ')
  | impL {ℓ Γ Δ A B} :
    Gentzen (Γ ⟹[ℓ] insert A Δ) → Gentzen (insert B Γ ⟹[ℓ] Δ) →
      Gentzen (insert (A 🡒 B) Γ ⟹[ℓ] Δ)
  | impR {ℓ Γ Δ A B} : Gentzen (insert A Γ ⟹[ℓ] insert B Δ) → Gentzen (Γ ⟹[ℓ] insert (A 🡒 B) Δ)
  | liftUp {Γ Δ} : Gentzen (Γ ⟹[0] Δ) → Gentzen (Γ ⟹[1] Δ)
  | boxGL {Γ A} : Gentzen (insert (□A) (Γ ∪ Γ.box) ⟹[0] {A}) → Gentzen (Γ.box ⟹[0] {□A})
  | boxGP {Γ Δ n} : Gentzen (Γ ⟹[1] insert (□^[n]⊥) Δ) → Gentzen (Γ ⟹[1] Δ)

@[inherit_doc] notation:45 "⊢ᴳ[𝐀] " S:50 => Gentzen S

notation:45 "⊬ᴳ[𝐀] " S:50 => ¬Gentzen S

namespace Gentzen

variable {Γ Δ : FormulaFinset α}

lemma of_GL {S : Sequent α} (h : ⊢ᴳ[𝐆𝐋] S) : ⊢ᴳ[𝐀] S.ant ⟹[0] S.suc := by
  induction h with
  | axm A => exact axm 0 A;
  | botL => exact botL 0;
  | wkL _ h ih => exact wkL ih h;
  | wkR _ h ih => exact wkR ih h;
  | impL _ _ ih₁ ih₂ => exact impL ih₁ ih₂;
  | impR _ ih => exact impR ih;
  | boxGL _ ih => exact boxGL ih;

lemma toGL {T : LayeredSequent 2 α} (h : ⊢ᴳ[𝐀] T) : T.level = 0 → ⊢ᴳ[𝐆𝐋] T.toSequent := by
  induction h with
  | axm => exact fun _ ↦ .axm _;
  | botL => exact fun _ ↦ .botL;
  | wkL _ h ih => exact fun hl ↦ .wkL (ih hl) h;
  | wkR _ h ih => exact fun hl ↦ .wkR (ih hl) h;
  | impL _ _ ih₁ ih₂ => exact fun hl ↦ .impL (ih₁ hl) (ih₂ hl);
  | impR _ ih => exact fun hl ↦ .impR (ih hl);
  | boxGL _ ih => exact fun hl ↦ .boxGL (ih hl);
  | liftUp | boxGP => nofun;

/-- The lower layer is the sequent calculus of `GL`. -/
theorem iff_GL : ⊢ᴳ[𝐀] Γ ⟹[0] Δ ↔ ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ := ⟨fun h ↦ h.toGL rfl, of_GL⟩

lemma isPropClosed : LayeredSequent.IsPropClosed (Gentzen (α := α)) :=
  ⟨axm, botL, fun h h' ↦ wkL h h', fun h h' ↦ wkR h h', impL, impR⟩

lemma of_GL_boxItr_bot {n : ℕ} (h : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert (□^[n]⊥) Δ) : ⊢ᴳ[𝐀] Γ ⟹[1] Δ :=
  boxGP (liftUp (iff_GL.mpr h))

end Gentzen

end A

end FFL.ProvabilityLogic

end
