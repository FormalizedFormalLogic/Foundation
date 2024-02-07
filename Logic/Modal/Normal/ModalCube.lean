/-
 Reserved to compare the strengh of normal modal logic proof systems.

 ## References

 * <https://plato.stanford.edu/entries/logic-modal/#MapRelBetModLog>
-/

import Logic.Modal.Normal.Soundness
import Logic.Modal.Normal.Completeness

namespace LO.Modal.Normal

def LogicStronger (Λ₁ Λ₂ : AxiomSet β) := ∀ (p : Formula β), (⊧ᴹ[(𝔽(Λ₁) : FrameClass β)] p) → (⊧ᴹ[(𝔽(Λ₂) : FrameClass β)] p)
infix:20 " ⪯ᴸ " => LogicStronger

namespace LogicStronger

instance : IsPreorder (AxiomSet β) (· ⪯ᴸ ·) where
  refl := by simp_all [LogicStronger];
  trans := by intro Λ₁ Λ₂ Λ₃ h₁₂ h₂₃ p hF; exact h₂₃ p (h₁₂ p hF);

variable {α β : Type u}
variable {Λ₁ Λ₂ : AxiomSet β} (hS : Λ₁ ⪯ᴸ Λ₂)
variable [DecidableEq β]

lemma consequence {Γ} {p : Formula β} : (Γ ⊨ᴹ[(𝔽(Λ₂) : FrameClass α)] p) → (Γ ⊨ᴹ[(𝔽(Λ₁) : FrameClass α)] p) := by
  have := hS;
  sorry;

lemma deducible (hComp : Completeness Λ₁ (𝔽(Λ₁) : FrameClass α)) {Γ} {p : Formula β} (hd : Γ ⊢ᴹ[Λ₂]! p) : Γ ⊢ᴹ[Λ₁]! p := by
  exact hComp Γ p $ consequence hS $ AxiomSet.ssounds hd;

end LogicStronger

def LogicStrictStronger (Λ₁ Λ₂ : AxiomSet β) := (Λ₁ ⪯ᴸ Λ₂) ∧ ¬(Λ₂ ⪯ᴸ Λ₁)
infix:20 " ≺ᴸ " => LogicStrictStronger

namespace LogicStrictStronger

variable {Λ₁ Λ₂ : AxiomSet β} (hS : Λ₁ ≺ᴸ Λ₂)
variable [DecidableEq β]

/-
lemma exists_undeducible_formula
  (hComp₁ : Completeness Λ₁ (𝔽(Λ₁) : FrameClass β))
  (hComp₂ : Completeness Λ₂ (𝔽(Λ₂) : FrameClass β))
  {Γ} : ∃ p, ((Γ ⊢ᴹ[Λ₂]! p) ∧ (Γ ⊬ᴹ[Λ₁]! p)) := by
  by_contra hC;
  have : ∀ (p : Formula β), (Γ ⊢ᴹ[Λ₂]! p) → (Γ ⊢ᴹ[Λ₁]! p) := by simpa using hC;
  apply hS.2;
-/

end LogicStrictStronger

def LogicEquivalence (Λ₁ Λ₂ : AxiomSet β) := (Λ₁ ⪯ᴸ Λ₂) ∧ (Λ₂ ⪯ᴸ Λ₁)
infix:75 " ≃ᴸ " => LogicEquivalence

namespace LogicEquivalence

instance : IsEquiv (AxiomSet β) (· ≃ᴸ ·) where
  refl := by simp [LogicEquivalence]; apply IsRefl.refl;
  trans := by
    simp [LogicEquivalence];
    intros _ _ _ h₁₂ h₂₁ h₂₃ h₃₂;
    constructor;
    . exact IsTrans.trans _ _ _ h₁₂ h₂₃;
    . exact IsTrans.trans _ _ _ h₃₂ h₂₁;
  symm := by
    simp [LogicEquivalence];
    intros;
    constructor <;> simpa;

variable {α₁ α₂ β} [DecidableEq β]

lemma deducible
  {Λ₁ Λ₂ : AxiomSet β} (h : Λ₁ ≃ᴸ Λ₂)
  (hComp₁ : Completeness Λ₁ (𝔽(Λ₁) : FrameClass α₁))
  (hComp₂ : Completeness Λ₂ (𝔽(Λ₂) : FrameClass α₂))
  {Γ} {p : Formula β} : (Γ ⊢ᴹ[Λ₁]! p) ↔ (Γ ⊢ᴹ[Λ₂]! p) := by
  constructor;
  . exact LogicStronger.deducible h.2 hComp₂;
  . exact LogicStronger.deducible h.1 hComp₁;

end LogicEquivalence

variable {α β : Type u} [Inhabited β] [DecidableEq β]
variable {p : Formula β}

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
theorem Hilbert.completes : Completeness (𝐊𝐓𝟒𝐁 : AxiomSet β) (𝔽((𝐊𝐓𝟒𝐁 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐊𝐓𝟒𝐁 : AxiomSet β))) := by
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

theorem equivalent_S5_KT4B : (𝐒𝟓 : AxiomSet β) ≃ᴸ 𝐊𝐓𝟒𝐁 := ⟨
  by
    intro p h F hF;
    exact h F (by
      have ⟨hRefl, hTrans, hSymm⟩ := LogicKT4B.FrameClassDefinability.mpr hF;
      apply LogicS5.FrameClassDefinability.mp;
      exact ⟨
        by simpa,
        eucl_of_symm_trans hSymm hTrans,
      ⟩;
    ),
  by
    intro p h F hF;
    exact h F (by
      have ⟨hRefl, hEucl⟩ := LogicS5.FrameClassDefinability.mpr hF;
      apply LogicKT4B.FrameClassDefinability.mp;
      exact ⟨
        by simpa,
        trans_of_refl_eucl hRefl hEucl,
        symm_of_refl_eucl hRefl hEucl,
      ⟩;
    );
⟩

theorem deducible_equivalent_S5_KT4B {Γ} {p : Formula β} : (Γ ⊢ᴹ[𝐒𝟓]! p) ↔ (Γ ⊢ᴹ[𝐊𝐓𝟒𝐁]! p) :=
  LogicEquivalence.deducible equivalent_S5_KT4B LogicS5.Hilbert.completes LogicKT4B.Hilbert.completes

end LO.Modal.Normal
