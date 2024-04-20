import Logic.Modal.Normal.Deduction

namespace LO.Modal.Normal

variable {α β}
variable [DecidableEq β]
variable {Λ₁ Λ₂ : AxiomSet β}
variable {T : Theory β} {p : Formula β}

def LogicalStrong (Λ₁ Λ₂ : AxiomSet β) := ∀ {p : Formula β}, (∅ ⊢ᴹ[Λ₁]! p) → (∅ ⊢ᴹ[Λ₂]! p)
infix:80 " ≤ᴸ " => LogicalStrong

abbrev LogicalStrictStrong (Λ₁ Λ₂ : AxiomSet β) := (Λ₁ ≤ᴸ Λ₂) ∧ ¬(Λ₂ ≤ᴸ Λ₁)
infix:80 " <ᴸ " => LogicalStrictStrong

abbrev LogicalEquivalence (Λ₁ Λ₂ : AxiomSet β) := (Λ₁ ≤ᴸ Λ₂) ∧ (Λ₂ ≤ᴸ Λ₁)
infix:80 " =ᴸ " => LogicalEquivalence


namespace LogicalStrong

@[refl]
protected lemma refl {Λ : AxiomSet β} : Λ ≤ᴸ Λ := by
  simp_all [LogicalStrong];

@[trans]
protected lemma trans {Λ₁ Λ₂ Λ₃ : AxiomSet β} : Λ₁ ≤ᴸ Λ₂ → Λ₂ ≤ᴸ Λ₃ → Λ₁ ≤ᴸ Λ₃ := by
  simp_all only [LogicalStrong];
  aesop;

instance : IsPreorder (AxiomSet β) (· ≤ᴸ ·) where
  refl := by apply LogicalStrong.refl;
  trans := by apply LogicalStrong.trans; simp;

lemma deducible (hS : Λ₁ ≤ᴸ Λ₂) (d₁ : T ⊢ᴹ[Λ₁]! p) : (T ⊢ᴹ[Λ₂]! p) := by
    have ⟨Δ, sΔ, dΔ⟩ := d₁.compact;
    replace dΔ : (∅ ∪ ↑Δ) ⊢ᴹ[Λ₁]! p := by simpa using dΔ;
    have d₂ : ↑Δ ⊢ᴹ[Λ₂]! p := by simpa using Hilbert.finset_dt!.mpr $ hS $ Hilbert.finset_dt!.mp dΔ;
    exact Hilbert.weakening! sΔ d₂;

lemma of_subset (h : Λ₁ ⊆ Λ₂) : (Λ₁ ≤ᴸ Λ₂) := by
  intro p;
  apply Deduction.maxm_subset!;
  assumption;

end LogicalStrong


namespace LogicalStrictStrong

@[trans]
protected lemma trans : Λ₁ <ᴸ Λ₂ → Λ₂ <ᴸ Λ₃ → Λ₁ <ᴸ Λ₃ := by
  intro h₁₂ h₂₃;
  constructor;
  . tauto;
  . simp_all only [LogicalStrictStrong, LogicalStrong, not_forall];
    obtain ⟨x, h₂, hn₁⟩ := by simpa using h₁₂.right;
    existsi x, h₂₃.left h₂;
    simpa;

instance : IsStrictOrder (AxiomSet β) (· <ᴸ ·) where
  irrefl := by simp;
  trans Λ₁ Λ₂ Λ₃ := by apply LogicalStrictStrong.trans;

lemma deducible (hS : Λ₁ <ᴸ Λ₂) : (T ⊢ᴹ[Λ₁]! p) → (T ⊢ᴹ[Λ₂]! p) := LogicalStrong.deducible hS.left

end LogicalStrictStrong


namespace LogicalEquivalence

@[trans]
protected lemma trans : Λ₁ =ᴸ Λ₂ → Λ₂ =ᴸ Λ₃ → Λ₁ =ᴸ Λ₃ := by
  simp only [LogicalEquivalence];
  rintro ⟨h₁₂, h₂₁⟩ ⟨h₂₃, h₃₂⟩;
  constructor <;> { trans Λ₂; assumption; assumption; }

@[symm]
protected lemma symm : Λ₁ =ᴸ Λ₂ → Λ₂ =ᴸ Λ₁ := by
  simp only [LogicalEquivalence];
  rintro ⟨h₁₂, h₂₁⟩;
  constructor <;> assumption;

@[refl]
protected lemma refl : Λ₁ =ᴸ Λ₁ := by
  simp only [LogicalEquivalence];
  constructor <;> apply LogicalStrong.refl;

instance : IsEquiv (AxiomSet β) (· =ᴸ ·) where
  refl := by apply LogicalEquivalence.refl;
  symm := by apply LogicalEquivalence.symm;
  trans := by apply LogicalEquivalence.trans;

lemma deducible (hS : Λ₁ =ᴸ Λ₂) : (T ⊢ᴹ[Λ₁]! p) ↔ (T ⊢ᴹ[Λ₂]! p) := by
  constructor;
  exact LogicalStrong.deducible hS.left;
  exact LogicalStrong.deducible hS.right;

end LogicalEquivalence

namespace LogicalStrong

local infix:80 (priority := high) " ≤ᴸ " => @LogicalStrong β

@[simp] theorem K_KB : 𝐊 ≤ᴸ 𝐊𝐁 := by apply of_subset; simp;

@[simp] theorem K_KD : 𝐊 ≤ᴸ 𝐊𝐃 := by apply of_subset; simp;

@[simp] theorem K_K4 : 𝐊 ≤ᴸ 𝐊𝟒 := by apply of_subset; simp;

@[simp] theorem K_K5 : 𝐊 ≤ᴸ 𝐊𝟓 := by apply of_subset; simp;

@[simp] theorem K_GL : 𝐊 ≤ᴸ 𝐆𝐋 := by apply of_subset; simp;

@[simp] theorem KT_S4 : 𝐊𝐓 ≤ᴸ 𝐒𝟒 := by apply of_subset; simp;

@[simp] theorem K4_S4 : 𝐊𝟒 ≤ᴸ 𝐒𝟒 := by apply of_subset; simp;

@[simp] theorem S4_S4Dot2 : 𝐒𝟒 ≤ᴸ 𝐒𝟒.𝟐 := by apply of_subset; simp;

@[simp] theorem S4_S4Dot3 : 𝐒𝟒 ≤ᴸ 𝐒𝟒.𝟑 := by apply of_subset; simp;

@[simp] theorem S4_S4Grz : 𝐒𝟒 ≤ᴸ 𝐒𝟒𝐆𝐫𝐳 := by apply of_subset; simp;

end LogicalStrong

end LO.Modal.Normal
