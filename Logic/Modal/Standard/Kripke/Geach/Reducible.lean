import Logic.Modal.Standard.Kripke.Reducible
import Logic.Modal.Standard.Kripke.Geach.Definability
import Logic.Modal.Standard.Kripke.Geach.Completeness

namespace LO.Modal.Standard

open Kripke
open AxiomSet

variable {α : Type u} [DecidableEq α] [Inhabited α]

section

variable {Λ₁ Λ₂ : AxiomSet α} [hG₁ : Λ₁.IsGeachLogic] [hG₂ : Λ₂.IsGeachLogic]

lemma reducible_of_geach_defnability
  (hs : ∀ {W : Type u}, [Inhabited W] → ∀ {F : Frame W α}, MultiGeachConfluent hG₂.taples F → MultiGeachConfluent hG₁.taples F)
  : (Λ₁ ≤ₛ Λ₂) := reducible_of_definability (definability₁ := IsGeachLogic.definability) (definability₂ := IsGeachLogic.definability) hs

lemma equiv_of_geach_defnability
  (hs : ∀ {W : Type u}, [Inhabited W] → ∀ {F : Frame W α}, MultiGeachConfluent hG₁.taples F ↔ MultiGeachConfluent hG₂.taples F)
  : (Λ₁ =ₛ Λ₂) := equiv_of_iff_definability (definability₁ := IsGeachLogic.definability) (definability₂ := IsGeachLogic.definability) hs

end

@[simp]
theorem reducible_KD_KT : (𝐊𝐃 : AxiomSet α) ≤ₛ 𝐊𝐓 := by apply reducible_of_geach_defnability; simp_all [serial_of_refl];

@[simp]
theorem reducible_S4_S5 : (𝐒𝟒 : AxiomSet α) ≤ₛ 𝐒𝟓 := by apply reducible_of_geach_defnability; simp_all [trans_of_refl_eucl];

@[simp]
theorem equiv_S5_KT4B : (𝐒𝟓 : AxiomSet α) =ₛ 𝐊𝐓𝟒𝐁 := by apply equiv_of_geach_defnability; intros; constructor <;> simp_all [symm_of_refl_eucl, trans_of_refl_eucl, eucl_of_symm_trans];

/- TODO: strict reducible
theorem LogicalStrictStrong.KD_KT [hβ : Nontrivial β] : (𝐊𝐃 : AxiomSet β) <ᴸ 𝐊𝐓 := by
  constructor;
  . simp;
  . obtain ⟨x, y, hxy⟩ := hβ.exists_pair_ne
    simp only [LogicalStrong, not_forall];
    use (□(Formula.atom default) ⟶ (Formula.atom default));
    use ⟨Deduction.maxm (by simp)⟩
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ _ w₂ => w₂ = y);
    constructor;
    . simp only [AxiomSetFrameClass.geach];
      apply GeachLogic.frameClassDefinability_aux.mp;
      simp [Serial];
    . simp [Formula.FrameConsequence];
      use (λ w _ => w = y);
      simp;
      use x;

theorem LogicalStrictStrong.K4_S4 [hβ : Nontrivial β] : (𝐊𝟒 : AxiomSet β) <ᴸ 𝐒𝟒 := by
  constructor;
  . apply LogicalStrong.of_subset; simp;
  . obtain ⟨x, y, hxy⟩ := hβ.exists_pair_ne;
    simp only [LogicalStrong, not_forall];
    use (□(Formula.atom default) ⟶ (Formula.atom default));
    use ⟨Deduction.maxm (by simp)⟩
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ _ w₂ => w₂ = y);
    constructor;
    . simp only [AxiomSetFrameClass.geach];
      apply GeachLogic.frameClassDefinability_aux.mp;
      simp [Transitive];
    . simp [Formula.FrameConsequence];
      use (λ w _ => w = y);
      simp;
      use x;

theorem LogicalStrictStrong.S4_S5 : (𝐒𝟒 : AxiomSet (Fin 3)) <ᴸ 𝐒𝟓 := by
  constructor;
  . simp;
  . simp only [LogicalStrong, not_forall];
    existsi (◇(Formula.atom default) ⟶ □◇(Formula.atom default));
    use ⟨Deduction.maxm (by simp)⟩;
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0 ∧ w₂ = 1) ∨ (w₁ = 0 ∧ w₂ = 2));
    constructor;
    . simp only [AxiomSetFrameClass.geach];
      apply GeachLogic.frameClassDefinability_aux.mp;
      simp [Reflexive, Transitive];
      aesop;
    . simp [Formula.FrameConsequence];
      use (λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0 ∧ w₂ = 1) ∨ (w₁ = 0 ∧ w₂ = 2));
      aesop;
-/

end LO.Modal.Standard
