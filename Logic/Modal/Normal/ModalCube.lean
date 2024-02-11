/-
 Reserved to compare the strengh of normal modal logic proof systems.

 ## References

 * <https://plato.stanford.edu/entries/logic-modal/#MapRelBetModLog>
-/

import Logic.Modal.Normal.Soundness
import Logic.Modal.Normal.Completeness

namespace LO.Modal.Normal

def LogicalStrong (Λ₁ Λ₂ : AxiomSet β) := ∀ (p : Formula β), (⊧ᴹ[(𝔽(Λ₁) : FrameClass β)] p) → (⊧ᴹ[(𝔽(Λ₂) : FrameClass β)] p)
infix:20 " ≤ᴸ " => LogicalStrong

namespace LogicalStrong

instance : IsPreorder (AxiomSet β) (· ≤ᴸ ·) where
  refl := by simp_all [LogicalStrong];
  trans := by intro Λ₁ Λ₂ Λ₃ h₁₂ h₂₃ p hF; exact h₂₃ p (h₁₂ p hF);

variable {α β : Type u}
variable {Λ₁ Λ₂ : AxiomSet β}
variable [Inhabited α] [DecidableEq β]

lemma iff : (Λ₁ ≤ᴸ Λ₂) ↔ (∀ {F : Frame β}, (F ∈ 𝔽(Λ₂) → F ∈ (𝔽(Λ₁)))) := by
  constructor;
  . intro h F hF₂ p hp;
    exact h p (by simp [Formula.FrameClasses]; aesop) F hF₂;
  . intro h₁ p h₂ F hF₂;
    exact h₂ F $ h₁ hF₂;

lemma not_iff : ¬(Λ₁ ≤ᴸ Λ₂) ↔ (∃ F ∈ 𝔽(Λ₂), (F : Frame β) ∉ 𝔽(Λ₁)) := by simpa using iff.not

variable (hS : Λ₁ ≤ᴸ Λ₂)

lemma consequence {Γ} {p : Formula β} : (Γ ⊨ᴹ[(𝔽(Λ₂) : FrameClass α)] p) → (Γ ⊨ᴹ[(𝔽(Λ₁) : FrameClass α)] p) := by
  have := hS;
  sorry;

lemma deducible (hComp : Completeness Λ₁ (𝔽(Λ₁) : FrameClass α)) {Γ} {p : Formula β} (hd : Γ ⊢ᴹ[Λ₂]! p) : Γ ⊢ᴹ[Λ₁]! p := by
  exact hComp Γ p $ consequence hS $ AxiomSet.ssounds hd;

end LogicalStrong

abbrev LogicalStrictStrong (Λ₁ Λ₂ : AxiomSet β) := (Λ₁ ≤ᴸ Λ₂) ∧ ¬(Λ₂ ≤ᴸ Λ₁)
infix:20 " <ᴸ " => LogicalStrictStrong

namespace LogicStrictStronger

instance : IsStrictOrder (AxiomSet β) (· <ᴸ ·) where
  irrefl := by simp [LogicalStrong]
  trans := by
    simp [LogicalStrictStrong, LogicalStrong];
    intro Λ₁ Λ₂ Λ₃ h₁₂ _ _ _ h₂₃ y _ _;
    constructor;
    . intro p h₁; exact h₂₃ p $ h₁₂ p h₁;
    . existsi y;
      constructor;
      . simpa;
      . by_contra hn₁;
        have := h₁₂ y hn₁;
        contradiction;

variable {Λ₁ Λ₂ : AxiomSet β} (hS : Λ₁ <ᴸ Λ₂)
variable [DecidableEq β]

end LogicStrictStronger

abbrev LogicalEquivalence (Λ₁ Λ₂ : AxiomSet β) := (Λ₁ ≤ᴸ Λ₂) ∧ (Λ₂ ≤ᴸ Λ₁)
infix:75 " =ᴸ " => LogicalEquivalence

namespace LogicalEquivalence

instance : IsEquiv (AxiomSet β) (· =ᴸ ·) where
  refl := by simp; apply IsRefl.refl;
  trans := by
    simp;
    intros _ _ _ h₁₂ h₂₁ h₂₃ h₃₂;
    constructor;
    . exact IsTrans.trans _ _ _ h₁₂ h₂₃;
    . exact IsTrans.trans _ _ _ h₃₂ h₂₁;
  symm := by
    simp;
    intros;
    constructor <;> simpa;

variable {α₁ α₂ β} [Inhabited α₁] [Inhabited α₂] [DecidableEq β]

lemma deducible
  {Λ₁ Λ₂ : AxiomSet β} (h : Λ₁ =ᴸ Λ₂)
  (hComp₁ : Completeness Λ₁ (𝔽(Λ₁) : FrameClass α₁))
  (hComp₂ : Completeness Λ₂ (𝔽(Λ₂) : FrameClass α₂))
  {Γ} {p : Formula β} : (Γ ⊢ᴹ[Λ₁]! p) ↔ (Γ ⊢ᴹ[Λ₂]! p) := by
  constructor;
  . exact LogicalStrong.deducible h.2 hComp₂;
  . exact LogicalStrong.deducible h.1 hComp₁;

end LogicalEquivalence

variable {α β : Type u} [Inhabited β] [DecidableEq β]
variable {p : Formula β}

def LogicKT : AxiomSet α := 𝐊 ∪ 𝐓
notation "𝐊𝐓" => LogicKT

namespace LogicKT

@[simp] lemma subset_K : 𝐊 ⊆ (𝐊𝐓 : AxiomSet α) := by simp [LogicKT]
@[simp] lemma subset_T : 𝐓 ⊆ (𝐊𝐓 : AxiomSet α) := by simp [LogicKT]

instance FrameClassDefinability : @FrameClassDefinability α β 𝐊𝐓 (λ F => (Reflexive F)) := by
  intro F;
  simp [LogicKT, AxiomSetFrameClass.union];
  have := AxiomK.defines β F;
  have := AxiomT.defines β F;
  aesop;

end LogicKT

theorem sstrong_KD_KT : (𝐊𝐃 : AxiomSet (Fin 2)) <ᴸ 𝐊𝐓 := by
  constructor;
  . apply LogicalStrong.iff.mpr;
    intro F hF;
    obtain hRefl := LogicKT.FrameClassDefinability.mpr hF;
    apply LogicKD.FrameClassDefinability.mp;
    exact serial_of_refl hRefl;
  . apply LogicalStrong.not_iff.mpr;
    existsi (λ _ w₂ => w₂ = 1);
    constructor;
    . apply LogicKD.FrameClassDefinability.mp;
      simp [Serial];
    . apply LogicKT.FrameClassDefinability.not.mp;
      simp [Reflexive]
      existsi 0;
      trivial;

theorem sstrong_S4_S5 : (𝐒𝟒 : AxiomSet (Fin 3)) <ᴸ 𝐒𝟓 := by
  constructor;
  . apply LogicalStrong.iff.mpr;
    intro F hF;
    obtain ⟨hRefl, hEucl⟩ := LogicS5.FrameClassDefinability.mpr hF;
    apply LogicS4.FrameClassDefinability.mp;
    constructor;
    . exact hRefl;
    . exact trans_of_refl_eucl hRefl hEucl;
  . apply LogicalStrong.not_iff.mpr;
    existsi (λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0 ∧ w₂ = 1) ∨ (w₁ = 0 ∧ w₂ = 2));
    constructor;
    . apply LogicS4.FrameClassDefinability.mp;
      simp [Reflexive, Transitive];
      trivial;
    . apply LogicS5.FrameClassDefinability.not.mp;
      simp [Reflexive, Euclidean];
      existsi 0, 1, 2;
      trivial;

def LogicKT4B : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒 ∪ 𝐁
notation "𝐊𝐓𝟒𝐁" => LogicKT4B

namespace LogicKT4B

@[simp] lemma subset_K : 𝐊 ⊆ (𝐊𝐓𝟒𝐁 : AxiomSet α) := by simp [LogicKT4B, LogicK]
@[simp] lemma subset_T : 𝐓 ⊆ (𝐊𝐓𝟒𝐁 : AxiomSet α) := by simp [LogicKT4B, LogicK]
@[simp] lemma subset_4 : 𝟒 ⊆ (𝐊𝐓𝟒𝐁 : AxiomSet α) := by simp [LogicKT4B, LogicK]
@[simp] lemma subset_B : 𝐁 ⊆ (𝐊𝐓𝟒𝐁 : AxiomSet α) := by simp [LogicKT4B, LogicK]

instance FrameClassDefinability : @FrameClassDefinability α β 𝐊𝐓𝟒𝐁 (λ F => (Reflexive F ∧ Transitive F ∧ Symmetric F)) := by
  intro F;
  simp [LogicKT4B, AxiomSetFrameClass.tetraunion];
  have := AxiomK.defines β F;
  have := AxiomT.defines β F;
  have := Axiom4.defines β F;
  have := AxiomB.defines β F;
  aesop;

abbrev CanonicalModel {β} := Normal.CanonicalModel (𝐊𝐓𝟒𝐁 : AxiomSet β)
theorem Hilbert.completes : @Completeness (MaximalConsistentTheory (𝐊𝐓𝟒𝐁 : AxiomSet β)) β 𝐊𝐓𝟒𝐁 (𝔽((𝐊𝐓𝟒𝐁 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐊𝐓𝟒𝐁 : AxiomSet β))) := by
  apply completeness_def.mpr;
  intro Γ hConsisΓ;
  let ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory hConsisΓ;
  existsi CanonicalModel.frame;
  constructor;
  . apply FrameClassDefinability.mp; simp_all;
  . existsi CanonicalModel.val, Ω;
    apply truthlemma' (by simp) |>.mpr;
    assumption;

end LogicKT4B

theorem equivalent_S5_KT4B : (𝐒𝟓 : AxiomSet β) =ᴸ 𝐊𝐓𝟒𝐁 := by
  constructor;
  . apply LogicalStrong.iff.mpr;
    intro F hF;
    obtain ⟨hRefl, hTrans, hSymm⟩ := LogicKT4B.FrameClassDefinability.mpr hF;
    apply LogicS5.FrameClassDefinability.mp;
    exact ⟨hRefl, eucl_of_symm_trans hSymm hTrans⟩
  . apply LogicalStrong.iff.mpr;
    intro F hF;
    obtain ⟨hRefl, hEucl⟩ := LogicS5.FrameClassDefinability.mpr hF;
    apply LogicKT4B.FrameClassDefinability.mp;
    exact ⟨hRefl, trans_of_refl_eucl hRefl hEucl, symm_of_refl_eucl hRefl hEucl⟩

theorem deducible_equivalent_S5_KT4B {Γ} {p : Formula β} : (Γ ⊢ᴹ[𝐒𝟓]! p) ↔ (Γ ⊢ᴹ[𝐊𝐓𝟒𝐁]! p) := by
  exact LogicalEquivalence.deducible equivalent_S5_KT4B LogicS5.Hilbert.completes LogicKT4B.Hilbert.completes

end LO.Modal.Normal
