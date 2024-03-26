/-
 ## References

 * <https://plato.stanford.edu/entries/logic-modal/#MapRelBetModLog>
-/

import Logic.Modal.Normal.Soundness
import Logic.Modal.Normal.Completeness

namespace LO.Modal.Normal

variable {α β : Type u}

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

lemma of_frameclass (h : (𝔽(Λ₂) : FrameClass β) ⊆ (𝔽(Λ₁) : FrameClass β)) (hComp₂ : Completeness Λ₂ (𝔽(Λ₂) : FrameClass β)) : (Λ₁ ≤ᴸ Λ₂) := by
  intro p h₁;
  apply hComp₂;
  intro F hF₂;
  exact AxiomSet.sounds h₁ _ $ h hF₂;

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

end LogicalEquivalence

variable {α β : Type u} [Inhabited β] [DecidableEq β]

lemma strong_K4_S4 : (𝐊𝟒 : AxiomSet β) ≤ᴸ 𝐒𝟒 := by
  simp only [LogicalStrong];
  apply LogicalStrong.of_frameclass;
  case h =>
    intro F hF;
    obtain ⟨_, hTrans⟩ := LogicS4.FrameClassDefinability.mpr hF;
    exact LogicK4.FrameClassDefinability.mp hTrans;
  case hComp₂ => exact LogicS4.Hilbert.completes;

theorem sstrong_K4_S4 [Nontrivial β] : (𝐊𝟒 : AxiomSet β) <ᴸ 𝐒𝟒 := by
  simp only [LogicalStrictStrong];
  constructor;
  . apply strong_K4_S4;
  . obtain ⟨x, y, hxy⟩ := @Nontrivial.exists_pair_ne β _;
    simp only [LogicalStrong, not_forall];
    use (□(Formula.atom default) ⟶ (Formula.atom default));
    use ⟨Deduction.maxm (by simp [LogicKT4, AxiomT.set, AxiomT])⟩
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ _ w₂ => w₂ = y);
    constructor;
    . apply LogicK4.FrameClassDefinability.mp;
      simp [Transitive];
    . simp [Formula.FrameConsequence];
      use (λ w _ => w = y);
      simp;
      use x;

lemma strong_KD_KT : (𝐊𝐃 : AxiomSet β) ≤ᴸ 𝐊𝐓 := by
  apply LogicalStrong.of_frameclass;
  case h =>
    intro F hF;
    obtain hRefl := LogicKT.FrameClassDefinability.mpr hF;
    have hSerial := serial_of_refl hRefl;
    exact LogicKD.FrameClassDefinability.mp hSerial;
  case hComp₂ => exact LogicKT.Hilbert.completes;

theorem sstrong_KD_KT [Nontrivial β] : (𝐊𝐃 : AxiomSet β) <ᴸ 𝐊𝐓 := by
  constructor;
  . apply strong_KD_KT;
  . obtain ⟨x, y, hxy⟩ := @Nontrivial.exists_pair_ne β _;
    simp only [LogicalStrong, not_forall];
    use (□(Formula.atom default) ⟶ (Formula.atom default));
    use ⟨Deduction.maxm (by simp [LogicKT, AxiomT.set, AxiomT])⟩
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ _ w₂ => w₂ = y);
    constructor;
    . apply LogicKD.FrameClassDefinability.mp;
      simp [Serial];
    . simp [Formula.FrameConsequence];
      use (λ w _ => w = y);
      simp;
      use x;

lemma strong_S4_S5 : (𝐒𝟒 : AxiomSet β) ≤ᴸ 𝐒𝟓 := by
  apply LogicalStrong.of_frameclass;
  case h =>
    intro F hF;
    obtain ⟨hRefl, hEucl⟩ := LogicS5.FrameClassDefinability.mpr hF;
    have hTrans := trans_of_refl_eucl hRefl hEucl;
    exact LogicS4.FrameClassDefinability.mp ⟨hRefl, hTrans⟩;
  case hComp₂ => exact LogicS5.Hilbert.completes;

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
    . apply LogicS4.FrameClassDefinability.mp;
      simp [Reflexive, Transitive];
      aesop;
    . simp [Formula.FrameConsequence];
      use (λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0 ∧ w₂ = 1) ∨ (w₁ = 0 ∧ w₂ = 2));
      aesop;

theorem equivalent_S5_KT4B : (𝐒𝟓 : AxiomSet β) =ᴸ 𝐊𝐓𝟒𝐁 := by
  constructor;
  . apply LogicalStrong.of_frameclass;
    case h =>
      intro F hF;
      obtain ⟨hRefl, hTrans, hSymm⟩ := LogicKT4B.FrameClassDefinability.mpr hF;
      have hEucl := eucl_of_symm_trans hSymm hTrans;
      exact LogicS5.FrameClassDefinability.mp ⟨hRefl, hEucl⟩;
    case hComp₂ => exact LogicKT4B.Hilbert.completes;
  . apply LogicalStrong.of_frameclass;
    case h =>
      intro F hF;
      obtain ⟨hRefl, hEucl⟩ := LogicS5.FrameClassDefinability.mpr hF;
      have hTrans := trans_of_refl_eucl hRefl hEucl;
      have hSymm := symm_of_refl_eucl hRefl hEucl;
      exact LogicKT4B.FrameClassDefinability.mp ⟨hRefl, hTrans, hSymm⟩;
    case hComp₂ => exact LogicS5.Hilbert.completes;

end LO.Modal.Normal
