import Logic.Modal.Standard.Kripke.Reducible
import Logic.Modal.Standard.Kripke.Geach.Definability
import Logic.Modal.Standard.Kripke.Geach.Completeness

namespace LO.Modal.Standard

open Kripke

variable (W) {α : Type*} [DecidableEq α] [Inhabited α]
variable {Λ₁ Λ₂ : AxiomSet α}
variable [hG₁ : Λ₁.IsGeach] [hG₂ : Λ₂.IsGeach]

lemma reducible_of_geach_defnability
  (hs : ∀ {F : Frame W α}, MultiGeachConfluent (AxiomSet.IsGeach.taples Λ₂) F → MultiGeachConfluent (AxiomSet.IsGeach.taples Λ₁) F)
  : (Λ₁ ≤ₛ Λ₂) := by
  apply reducible_of_definability
    (default : AxiomSetFrameClass W Λ₁)
    (default : AxiomSetFrameClass W Λ₂)
    (AxiomSet.IsGeach.definability W Λ₁)
    (AxiomSet.IsGeach.definability W Λ₂);
  intro F hF;
  exact hs hF;

lemma equiv_of_geach_defnability
  (hs : ∀ {F : Frame W α}, MultiGeachConfluent (AxiomSet.IsGeach.taples Λ₁) F ↔ MultiGeachConfluent (AxiomSet.IsGeach.taples Λ₂) F)
  : (Λ₁ =ₛ Λ₂) := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_geach_defnability W; intro F hF; exact hs.mpr hF;
  . apply reducible_of_geach_defnability W; intro F hF; exact hs.mp hF

@[simp]
theorem reducible_KD_KT : (𝐊𝐃 : AxiomSet α) ≤ₛ 𝐊𝐓 := by
  apply reducible_of_geach_defnability W;
  simp;
  rintro _ hRefl;
  exact serial_of_refl hRefl;

@[simp]
theorem reducible_S4_S5 : (𝐒𝟒 : AxiomSet α) ≤ₛ 𝐒𝟓 := by
  apply reducible_of_geach_defnability W;
  simp;
  rintro F hRefl hEucl;
  refine ⟨hRefl, (trans_of_refl_eucl hRefl hEucl)⟩;

@[simp]
theorem equiv_S5_KT4B : (𝐒𝟓 : AxiomSet α) =ₛ 𝐊𝐓𝟒𝐁 := by
  apply equiv_of_geach_defnability W;
  simp_all;
  rintro F hRefl;
  constructor;
  . intro hEucl;
    refine ⟨trans_of_refl_eucl hRefl hEucl, symm_of_refl_eucl hRefl hEucl⟩
  . rintro ⟨hTrans, hSymm⟩;
    exact eucl_of_symm_trans hSymm hTrans;

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
