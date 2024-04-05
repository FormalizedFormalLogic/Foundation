import Logic.Modal.Normal.Soundness
import Logic.Modal.Normal.Completeness
import Logic.Modal.Normal.Geach

/-!
  Strength of modal logics
-/

class _root_.Distinct₃ (α : Type*) : Prop where
  existance : ∃ x₁ x₂ x₃ : α, x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃

namespace LO.Modal.Normal

open GeachConfluency

variable {α β : Type u}

variable {Λ₁ Λ₂ : AxiomSet β}
variable [Inhabited α]
variable [Inhabited β] [DecidableEq β]

def LogicalStrong (Λ₁ Λ₂ : AxiomSet β) := ∀ {p : Formula β}, (∅ ⊢ᴹ[Λ₁]! p) → (∅ ⊢ᴹ[Λ₂]! p)
infix:20 " ≤ᴸ " => LogicalStrong

namespace LogicalStrong

@[refl]
protected lemma refl : (Λ ≤ᴸ Λ) := by simp_all [LogicalStrong];

@[trans]
protected lemma trans : (Λ₁ ≤ᴸ Λ₂) → (Λ₂ ≤ᴸ Λ₃) → (Λ₁ ≤ᴸ Λ₃) := by simp_all only [LogicalStrong]; aesop;

instance : IsPreorder (AxiomSet β) (· ≤ᴸ ·) where
  refl := by apply LogicalStrong.refl;
  trans := by apply LogicalStrong.trans;

lemma deducible (hS : Λ₁ ≤ᴸ Λ₂) : (∅ ⊢ᴹ[Λ₁]! p) → (∅ ⊢ᴹ[Λ₂]! p) := by apply hS;

lemma of_frameclass (hComp₂ : KripkeCompleteness Λ₂ (𝔽(Λ₂) : FrameClass γ)) (h : (𝔽(Λ₂) : FrameClass γ) ⊆ (𝔽(Λ₁) : FrameClass γ)) : (Λ₁ ≤ᴸ Λ₂) := by
  intro p h₁;
  apply hComp₂;
  intro F hF₂;
  apply AxiomSet.sounds h₁;
  exact h hF₂;

lemma of_frameclass_geach [IsGeachLogic Λ₂] (h : (𝔽(Λ₂) : FrameClass (MaximalConsistentTheory Λ₂)) ⊆ (𝔽(Λ₁) : FrameClass (MaximalConsistentTheory Λ₂))) : (Λ₁ ≤ᴸ Λ₂) := by
  apply of_frameclass;
  case hComp₂ => apply GeachLogic.kripkeCompletes;
  case h => exact h;

variable (hS : Λ₁ ≤ᴸ Λ₂) {Γ : Theory β} {p : Formula β}

end LogicalStrong

abbrev LogicalStrictStrong (Λ₁ Λ₂ : AxiomSet β) := (Λ₁ ≤ᴸ Λ₂) ∧ ¬(Λ₂ ≤ᴸ Λ₁)
infix:20 " <ᴸ " => LogicalStrictStrong

namespace LogicalStrictStrong

protected lemma irrefl : ¬(Λ <ᴸ Λ) := by simp [LogicalStrictStrong]

@[trans]
protected lemma trans : (Λ₁ <ᴸ Λ₂) → (Λ₂ <ᴸ Λ₃) → (Λ₁ <ᴸ Λ₃) := by
  intro h₁₂ h₂₃;
  simp_all only [LogicalStrictStrong, LogicalStrong];
  constructor;
  . tauto;
  . simp only [not_forall];
    obtain ⟨x, h₂, hn₁⟩ := by simpa using h₁₂.right;
    existsi x, h₂₃.left ⟨h₂⟩;
    simpa;

instance : IsStrictOrder (AxiomSet β) (· <ᴸ ·) where
  irrefl := by apply LogicalStrictStrong.irrefl;
  trans := by apply LogicalStrictStrong.trans

variable {Λ₁ Λ₂ : AxiomSet β} (hS : Λ₁ <ᴸ Λ₂)
variable [DecidableEq β]

lemma deducible : (∅ ⊢ᴹ[Λ₁]! p) → (∅ ⊢ᴹ[Λ₂]! p) := by apply hS.left;

end LogicalStrictStrong

@[simp]
def LogicalEquivalence (Λ₁ Λ₂ : AxiomSet β) := (Λ₁ ≤ᴸ Λ₂) ∧ (Λ₂ ≤ᴸ Λ₁)
infix:75 " =ᴸ " => LogicalEquivalence

namespace LogicalEquivalence

@[refl]
protected lemma refl : (Λ =ᴸ Λ) := by simp_all; rfl;

@[symm]
protected lemma symm : (Λ₁ =ᴸ Λ₂) → (Λ₂ =ᴸ Λ₁) := by simp_all [LogicalEquivalence];

@[trans]
protected lemma trans : (Λ₁ =ᴸ Λ₂) → (Λ₂ =ᴸ Λ₃) → (Λ₁ =ᴸ Λ₃) := by
  simp_all;
  intros;
  constructor <;> exact LogicalStrong.trans (by assumption) (by assumption)

instance : IsEquiv (AxiomSet β) (· =ᴸ ·) where
  refl := by apply LogicalEquivalence.refl;
  trans := by apply LogicalEquivalence.trans
  symm := by apply LogicalEquivalence.symm;

lemma deducible (hE : Λ₁ =ᴸ Λ₂) : (∅ ⊢ᴹ[Λ₁]! p) ↔ (∅ ⊢ᴹ[Λ₂]! p) := by
  obtain ⟨h₁, h₂⟩ := hE;
  constructor;
  . apply h₁.deducible;
  . apply h₂.deducible;

lemma of_frameclass
  (hComp₁ : KripkeCompleteness Λ₁ (𝔽(Λ₁) : FrameClass γ₁))
  (hComp₂ : KripkeCompleteness Λ₂ (𝔽(Λ₂) : FrameClass γ₂))
  (h₁ : (𝔽(Λ₁) : FrameClass γ₁) ⊆ (𝔽(Λ₂) : FrameClass γ₁))
  (h₂ : (𝔽(Λ₂) : FrameClass γ₂) ⊆ (𝔽(Λ₁) : FrameClass γ₂))
  : (Λ₁ =ᴸ Λ₂) := by
  constructor;
  . apply LogicalStrong.of_frameclass hComp₂; simpa;
  . apply LogicalStrong.of_frameclass hComp₁; simpa;

lemma of_frameclass_geach [IsGeachLogic Λ₁] [IsGeachLogic Λ₂]
  (h₁ : (𝔽(Λ₁) : FrameClass (MaximalConsistentTheory Λ₁)) ⊆ (𝔽(Λ₂) : FrameClass (MaximalConsistentTheory Λ₁)))
  (h₂ : (𝔽(Λ₂) : FrameClass (MaximalConsistentTheory Λ₂)) ⊆ (𝔽(Λ₁) : FrameClass (MaximalConsistentTheory Λ₂)))
  : (Λ₁ =ᴸ Λ₂) :=
  of_frameclass GeachLogic.kripkeCompletes GeachLogic.kripkeCompletes h₁ h₂

end LogicalEquivalence

section

variable {p : Formula β}

lemma strong_K4_S4 : (𝐊𝟒 : AxiomSet β) ≤ᴸ 𝐒𝟒 := by
  simp only [LogicalStrong];
  apply LogicalStrong.of_frameclass_geach;
  simp only [AxiomSetFrameClass.geach];
  intro F hF;
  obtain ⟨_, hTrans⟩ := by simpa [-GeachConfluency] using GeachLogic.FrameClassDefinabilityAux.mpr hF;
  apply GeachLogic.FrameClassDefinabilityAux.mp;
  simp [GeachConfluency, -GeachConfluency];
  assumption;

theorem sstrong_K4_S4 [hβ : Nontrivial β] : (𝐊𝟒 : AxiomSet β) <ᴸ 𝐒𝟒 := by
  constructor;
  . apply strong_K4_S4;
  . obtain ⟨x, y, hxy⟩ := hβ.exists_pair_ne;
    simp only [LogicalStrong, not_forall];
    use (□(Formula.atom default) ⟶ (Formula.atom default));
    use ⟨Deduction.maxm (by simp [LogicKT4, AxiomT.set, AxiomT])⟩
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ _ w₂ => w₂ = y);
    constructor;
    . simp only [AxiomSetFrameClass.geach];
      apply GeachLogic.FrameClassDefinabilityAux.mp;
      simp;
    . simp [Formula.FrameConsequence];
      use (λ w _ => w = y);
      simp;
      use x;

lemma strong_KD_KT : (𝐊𝐃 : AxiomSet β) ≤ᴸ 𝐊𝐓 := by
  simp only [LogicalStrong];
  apply LogicalStrong.of_frameclass_geach;
  simp only [AxiomSetFrameClass.geach];
  intro F hF;
  have hRefl : Reflexive F := by
    simp [Reflexive];
    intros;
    simpa using GeachLogic.FrameClassDefinabilityAux.mpr hF;
  have hSerial : Serial F := serial_of_refl hRefl;
  apply GeachLogic.FrameClassDefinabilityAux.mp;
  simp;
  apply hSerial;

theorem sstrong_KD_KT [hβ : Nontrivial β] : (𝐊𝐃 : AxiomSet β) <ᴸ 𝐊𝐓 := by
  constructor;
  . apply strong_KD_KT;
  . obtain ⟨x, y, hxy⟩ := hβ.exists_pair_ne
    simp only [LogicalStrong, not_forall];
    use (□(Formula.atom default) ⟶ (Formula.atom default));
    use ⟨Deduction.maxm (by simp [LogicKT, AxiomT.set, AxiomT])⟩
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ _ w₂ => w₂ = y);
    constructor;
    . simp only [AxiomSetFrameClass.geach];
      apply GeachLogic.FrameClassDefinabilityAux.mp;
      simp;
    . simp [Formula.FrameConsequence];
      use (λ w _ => w = y);
      simp;
      use x;

lemma strong_S4_S5 : (𝐒𝟒 : AxiomSet β) ≤ᴸ 𝐒𝟓 := by
  simp only [LogicalStrong];
  apply LogicalStrong.of_frameclass_geach;
  simp only [AxiomSetFrameClass.geach];
  intro F hF;
  obtain ⟨hRefl, hEucl⟩ := by simpa [-GeachConfluency] using GeachLogic.FrameClassDefinabilityAux.mpr hF;
  replace hRefl : Reflexive F := reflexive_def.mpr hRefl;
  replace hEucl : Euclidean F := euclidean_def.mpr hEucl;
  apply GeachLogic.FrameClassDefinabilityAux.mp;
  simp [-GeachConfluency];
  exact ⟨
    by apply reflexive_def.mp; simpa,
    by apply transitive_def.mp; exact trans_of_refl_eucl hRefl hEucl,
  ⟩;

-- TODO: migrate `Distinct₃ β`
theorem sstrong_S4_S5 : (𝐒𝟒 : AxiomSet (Fin 3)) <ᴸ 𝐒𝟓 := by
  constructor;
  . apply strong_S4_S5;
  . simp only [LogicalStrong, not_forall];
    existsi (◇(Formula.atom default) ⟶ □◇(Formula.atom default));
    use ⟨Deduction.maxm (by simp [LogicKT5, Axiom5.set, Axiom5])⟩;
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0 ∧ w₂ = 1) ∨ (w₁ = 0 ∧ w₂ = 2));
    constructor;
    . simp only [AxiomSetFrameClass.geach];
      apply GeachLogic.FrameClassDefinabilityAux.mp;
      aesop;
    . simp [Formula.FrameConsequence];
      use (λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0 ∧ w₂ = 1) ∨ (w₁ = 0 ∧ w₂ = 2));
      aesop;

theorem equivalent_S5_KT4B : (𝐒𝟓 : AxiomSet β) =ᴸ 𝐊𝐓𝟒𝐁 := by
  apply LogicalEquivalence.of_frameclass_geach;
  case h₁ =>
    simp only [AxiomSetFrameClass.geach];
    intro F hF;
    obtain ⟨hRefl, hEucl⟩ := by simpa [-GeachConfluency] using GeachLogic.FrameClassDefinabilityAux.mpr hF;
    replace hRefl : Reflexive F := reflexive_def.mpr hRefl;
    replace hEucl : Euclidean F := euclidean_def.mpr hEucl;
    apply GeachLogic.FrameClassDefinabilityAux.mp;
    simp [-GeachConfluency];
    exact ⟨
      by apply reflexive_def.mp; assumption,
      by apply transitive_def.mp; exact trans_of_refl_eucl hRefl hEucl,
      by apply symmetric_def.mp; exact symm_of_refl_eucl hRefl hEucl,
    ⟩
  case h₂ =>
    simp only [AxiomSetFrameClass.geach];
    intro F hF;
    obtain ⟨hRefl, hTrans, hSymm⟩ := by simpa [-GeachConfluency] using GeachLogic.FrameClassDefinabilityAux.mpr hF;
    replace hRefl : Reflexive F := reflexive_def.mpr hRefl;
    replace hTrans : Transitive F := transitive_def.mpr hTrans;
    replace hSymm : Symmetric F := symmetric_def.mpr hSymm;
    apply GeachLogic.FrameClassDefinabilityAux.mp;
    simp [-GeachConfluency];
    exact ⟨
      by apply reflexive_def.mp; assumption,
      by apply euclidean_def.mp; exact eucl_of_symm_trans hSymm hTrans,
    ⟩

end

end LO.Modal.Normal
