import Logic.Modal.Normal.Strength.Semantical
import Logic.Modal.Normal.Geach

/-!
  # Logical Strength Analysis of Geach Logics

  Semantical logical strength analysis of Geach logics.
-/

namespace LO.Modal.Normal

variable {α β}
variable [Inhabited α]
variable [Inhabited β] [DecidableEq β]
variable {Λ₁ Λ₂ : AxiomSet β}

lemma LogicalStrong.of_geach [hG₁ : Geach Λ₁] [hG₂ : Geach Λ₂]
  (hFrame : ∀ {F : Frame (MaximalConsistentTheory Λ₂)}, GeachConfluencyList hG₂.taples F → GeachConfluencyList hG₁.taples F)
  : (Λ₁ ≤ᴸ Λ₂) := by
  apply of_axiomset_definability
    GeachLogic.kripkeCompletes
    GeachLogic.frameClassDefinability
    GeachLogic.frameClassDefinability;
  assumption;

lemma LogicalEquivalence.of_geach [hG₁ : Geach Λ₁] [hG₂ : Geach Λ₂]
  (hFrame₂₁ : ∀ {F : Frame (MaximalConsistentTheory Λ₂)}, GeachConfluencyList hG₂.taples F → GeachConfluencyList hG₁.taples F)
  (hFrame₁₂ : ∀ {F : Frame (MaximalConsistentTheory Λ₁)}, GeachConfluencyList hG₁.taples F → GeachConfluencyList hG₂.taples F)
  : (Λ₁ =ᴸ Λ₂) := by
  apply of_axiomset_definability;
  case hComp₁ => exact GeachLogic.kripkeCompletes;
  case hComp₂ => exact GeachLogic.kripkeCompletes;
  case hDef₁₂ => exact GeachLogic.frameClassDefinability;
  case hDef₁₁ => exact GeachLogic.frameClassDefinability;
  case hDef₂₂ => exact GeachLogic.frameClassDefinability;
  case hDef₂₁ => exact GeachLogic.frameClassDefinability;
  case hFrame₂₁ => assumption;
  case hFrame₁₂ => assumption;

@[simp]
theorem LogicalStrong.KD_KT : (𝐊𝐃 : AxiomSet β) ≤ᴸ 𝐊𝐓 := by
  apply LogicalStrong.of_geach;
  simp;
  intro _ hRefl;
  exact serial_of_refl hRefl;

@[simp]
theorem LogicalStrong.S4_S5 : (𝐒𝟒 : AxiomSet β) ≤ᴸ 𝐒𝟓 := by
  apply LogicalStrong.of_geach;
  simp;
  intro _ hRefl hEucl;
  exact ⟨by assumption, trans_of_refl_eucl hRefl hEucl⟩;

@[simp]
theorem LogicalEquivalence.S5_KT4B : (𝐒𝟓 : AxiomSet β) =ᴸ 𝐊𝐓𝟒𝐁 := by
  apply LogicalEquivalence.of_geach;
  case hFrame₂₁ =>
    simp;
    intro _ hRefl hTrans hSymm;
    exact ⟨by assumption, eucl_of_symm_trans hSymm hTrans⟩
  case hFrame₁₂ =>
    simp;
    intro _ hRefl hEucl;
    exact ⟨by assumption, trans_of_refl_eucl hRefl hEucl, symm_of_refl_eucl hRefl hEucl⟩

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

end LO.Modal.Normal
