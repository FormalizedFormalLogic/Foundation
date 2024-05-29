import Logic.Modal.Standard.Kripke.Reducible
import Logic.Modal.Standard.Kripke.Geach.Definability
import Logic.Modal.Standard.Kripke.Geach.Completeness

namespace LO.Modal.Standard

open Kripke
open AxiomSet

variable {α : Type u} [DecidableEq α] [Inhabited α]
variable {Λ₁ Λ₂ : AxiomSet α}
variable [System.Consistent Λ₁] [System.Consistent Λ₂]
variable [hG₁ : Λ₁.IsGeachLogic] [hG₂ : Λ₂.IsGeachLogic]

lemma reducible_of_geach_defnability
  (hs : ∀ {W : Type u}, [Inhabited W] → ∀ {F : Frame W α}, MultiGeachConfluent hG₂.taples F → MultiGeachConfluent hG₁.taples F)
  : (Λ₁ ≤ₛ Λ₂) := by
  apply reducible_of_definability (IsGeachLogic.definability (Λ := Λ₁)) (IsGeachLogic.definability (Λ := Λ₂));
  intro W _ F hF;
  exact @hs W _ F hF;

lemma equiv_of_geach_defnability
  (hs : ∀ {W : Type u}, [Inhabited W] → ∀ {F : Frame W α}, MultiGeachConfluent hG₁.taples F ↔ MultiGeachConfluent hG₂.taples F)
  : (Λ₁ =ₛ Λ₂) := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_geach_defnability; intros; apply hs.mpr; assumption;
  . apply reducible_of_geach_defnability; intros; apply hs.mp; assumption;

@[simp]
theorem reducible_KD_KT : (𝐊𝐃 : AxiomSet α) ≤ₛ 𝐊𝐓 := by
  apply reducible_of_geach_defnability;
  simp; intros;
  exact serial_of_refl (by assumption);

@[simp]
theorem reducible_S4_S5 : (𝐒𝟒 : AxiomSet α) ≤ₛ 𝐒𝟓 := by
  apply reducible_of_geach_defnability;
  simp; intros;
  refine ⟨(trans_of_refl_eucl (by assumption) (by assumption)), (by assumption)⟩;

@[simp]
theorem equiv_S5_KT4B : (𝐒𝟓 : AxiomSet α) =ₛ 𝐊𝐓𝟒𝐁 := by
  apply equiv_of_geach_defnability; simp; intros;
  constructor;
  . rintro ⟨hEucl, hRefl⟩;
    exact ⟨symm_of_refl_eucl hRefl hEucl, trans_of_refl_eucl hRefl hEucl, hRefl⟩
  . rintro ⟨hSymm, hTrans, hRefl⟩;
    exact ⟨eucl_of_symm_trans hSymm hTrans, hRefl⟩;

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
