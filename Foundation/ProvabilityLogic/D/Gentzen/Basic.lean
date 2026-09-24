module

public import Foundation.ProvabilityLogic.S.Gentzen.Basic

/-!
# The sequent calculus of `D`

## References

- [KKIM25]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace D

variable {α : Type*} [DecidableEq α]

/-- The three-layered cut-free sequent calculus of `D`: the layers `0` and `1` are those of `S`.

- [KKIM25, §3]
-/
inductive Gentzen : LayeredSequent 3 α → Prop
  | axm (ℓ) (A) : Gentzen ({A} ⟹[ℓ] {A})
  | botL (ℓ) : Gentzen ({⊥} ⟹[ℓ] ∅)
  | wkL {ℓ Γ Γ' Δ} : Gentzen (Γ ⟹[ℓ] Δ) → (_ : Γ ⊆ Γ' := by grind) → Gentzen (Γ' ⟹[ℓ] Δ)
  | wkR {ℓ Γ Δ Δ'} : Gentzen (Γ ⟹[ℓ] Δ) → (_ : Δ ⊆ Δ' := by grind) → Gentzen (Γ ⟹[ℓ] Δ')
  | impL {ℓ Γ Δ A B} :
    Gentzen (Γ ⟹[ℓ] insert A Δ) → Gentzen (insert B Γ ⟹[ℓ] Δ) →
      Gentzen (insert (A 🡒 B) Γ ⟹[ℓ] Δ)
  | impR {ℓ Γ Δ A B} : Gentzen (insert A Γ ⟹[ℓ] insert B Δ) → Gentzen (Γ ⟹[ℓ] insert (A 🡒 B) Δ)
  | boxGL {Γ A} : Gentzen (insert (□A) (Γ ∪ Γ.box) ⟹[0] {A}) → Gentzen (Γ.box ⟹[0] {□A})
  | liftUp₀₁ {Γ Δ} : Gentzen (Γ ⟹[0] Δ) → Gentzen (Γ ⟹[1] Δ)
  | boxL {Γ Δ A} : Gentzen (insert A Γ ⟹[1] Δ) → Gentzen (insert (□A) Γ ⟹[1] Δ)
  | liftUp₁₂ {Γ Δ : FormulaFinset α} : Gentzen (Γ.box ⟹[1] Δ.box) → Gentzen (Γ.box ⟹[2] Δ.box)

@[inherit_doc] notation:45 "⊢ᴳ[𝐃] " S:50 => Gentzen S

notation:45 "⊬ᴳ[𝐃] " S:50 => ¬Gentzen S

namespace Gentzen

variable {Γ Δ : FormulaFinset α}

lemma isPropClosed : LayeredSequent.IsPropClosed (Gentzen (α := α)) :=
  ⟨axm, botL, fun h h' ↦ wkL h h', fun h h' ↦ wkR h h', impL, impR⟩

lemma toGL {T : LayeredSequent 3 α} (h : ⊢ᴳ[𝐃] T) : T.level = 0 → ⊢ᴳ[𝐆𝐋] T.toSequent := by
  induction h with
  | axm => exact fun _ ↦ .axm _;
  | botL => exact fun _ ↦ .botL;
  | wkL _ h ih => exact fun hl ↦ .wkL (ih hl) h;
  | wkR _ h ih => exact fun hl ↦ .wkR (ih hl) h;
  | impL _ _ ih₁ ih₂ => exact fun hl ↦ .impL (ih₁ hl) (ih₂ hl);
  | impR _ ih => exact fun hl ↦ .impR (ih hl);
  | boxGL _ ih => exact fun hl ↦ .boxGL (ih hl);
  | liftUp₀₁ | boxL | liftUp₁₂ => nofun;

lemma toS {T : LayeredSequent 3 α} (h : ⊢ᴳ[𝐃] T) : T.level = 1 → ⊢ᴳ[𝐒] T.ant ⟹[1] T.suc := by
  induction h with
  | axm => exact fun _ ↦ .axm _ _;
  | botL => exact fun _ ↦ .botL _;
  | wkL _ h ih => exact fun hl ↦ .wkL (ih hl) h;
  | wkR _ h ih => exact fun hl ↦ .wkR (ih hl) h;
  | impL _ _ ih₁ ih₂ => exact fun hl ↦ .impL (ih₁ hl) (ih₂ hl);
  | impR _ ih => exact fun hl ↦ .impR (ih hl);
  | liftUp₀₁ h => exact fun _ ↦ .liftUp (S.Gentzen.of_GL (h.toGL rfl));
  | boxL _ ih => exact fun hl ↦ .boxL (ih hl);
  | boxGL | liftUp₁₂ => nofun;

lemma of_S {T : LayeredSequent 2 α} (h : ⊢ᴳ[𝐒] T) : ⊢ᴳ[𝐃] T.ant ⟹[T.level.castSucc] T.suc := by
  induction h with
  | axm ℓ A => exact axm _ A;
  | botL => exact botL _;
  | wkL _ h ih => exact wkL ih h;
  | wkR _ h ih => exact wkR ih h;
  | impL _ _ ih₁ ih₂ => exact impL ih₁ ih₂;
  | impR _ ih => exact impR ih;
  | liftUp _ ih => exact liftUp₀₁ ih;
  | boxGL _ ih => exact boxGL ih;
  | boxL _ ih => exact boxL ih;

/-- The layer `0` is the sequent calculus of `GL`.

- [KKIM25, Theorem 4.1]
-/
theorem iff_GL : ⊢ᴳ[𝐃] Γ ⟹[0] Δ ↔ ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ :=
  ⟨fun h ↦ h.toGL rfl, fun h ↦ of_S (S.Gentzen.iff_GL.mpr h)⟩

/-- The layer `1` is the upper layer of the sequent calculus of `S`.

- [KKIM25, Theorem 4.2]
-/
theorem iff_S : ⊢ᴳ[𝐃] Γ ⟹[1] Δ ↔ ⊢ᴳ[𝐒] Γ ⟹[1] Δ := ⟨fun h ↦ h.toS rfl, of_S⟩

/-- - [KKIM25, Theorem 4.3] -/
lemma liftUp₀₂ {S : Sequent α} (h : ⊢ᴳ[𝐆𝐋] S) : ⊢ᴳ[𝐃] S.ant ⟹[2] S.suc := by
  induction h with
  | axm A => exact axm 2 A;
  | botL => exact botL 2;
  | wkL _ h ih => exact wkL ih h;
  | wkR _ h ih => exact wkR ih h;
  | impL _ _ ih₁ ih₂ => exact impL ih₁ ih₂;
  | impR _ ih => exact impR ih;
  | @boxGL Γ A h =>
    have : ({□A} : FormulaFinset α) = ({A} : FormulaFinset α).box := by simp;
    exact this ▸ liftUp₁₂ (liftUp₀₁ (this ▸ iff_GL.mpr (.boxGL h)));

end Gentzen

end D

end FFL.ProvabilityLogic

end
