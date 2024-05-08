import Logic.Modal.Standard.Deduction

section

namespace Set

variable {s₁ s₂ s₃ s₄ : Set F}

@[simp] lemma subset_triunion₁ : s₁ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans (Set.subset_union_left _ _) (Set.subset_union_left _ _)

@[simp] lemma subset_triunion₂ : s₂ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans (Set.subset_union_right _ _) (Set.subset_union_left _ _)

@[simp] lemma subset_triunion₃ : s₃ ⊆ (s₁ ∪ s₂ ∪ s₃) := by simp only [Set.subset_union_right]

@[simp] lemma subset_tetraunion₁ : s₁ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) :=
  Set.Subset.trans
    (Set.subset_union_left _ _)
    $ Set.Subset.trans (Set.subset_union_left _ _) (Set.subset_union_left _ _)

@[simp]
lemma subset_tetraunion₂ : s₂ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) :=
  Set.Subset.trans
    (Set.subset_union_right _ _)
    $ Set.Subset.trans (Set.subset_union_left _ _) (Set.subset_union_left _ _)

@[simp] lemma subset_tetraunion₃ : s₃ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) := by simp_all
@[simp] lemma subset_tetraunion₄ : s₄ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) := by simp_all

end Set

end


namespace LO.Modal.Standard

variable {Λ₁ Λ₂ : AxiomSet α}

lemma reducible_of_subset (hs : Λ₁ ⊆ Λ₂ := by simp) : Λ₁ ≤ₛ Λ₂ := by
  rintro p hp;
  simp_all [System.theory];
  exact maxm_subset! hs hp;

-- trivial reducible

@[simp] lemma reducible_K_KT : (𝐊 : AxiomSet α) ≤ₛ 𝐊𝐓 := reducible_of_subset

@[simp] lemma reducible_K_KB : (𝐊 : AxiomSet α) ≤ₛ 𝐊𝐁 := reducible_of_subset

@[simp] lemma reducible_K_KD : (𝐊 : AxiomSet α) ≤ₛ 𝐊𝐃 := reducible_of_subset

@[simp] lemma reducible_K_K4 : (𝐊 : AxiomSet α) ≤ₛ 𝐊𝟒 := reducible_of_subset

@[simp] lemma reducible_K_K5 : (𝐊 : AxiomSet α) ≤ₛ 𝐊𝟓 := reducible_of_subset

@[simp] lemma reducible_K_GL : (𝐊 : AxiomSet α) ≤ₛ 𝐆𝐋 := reducible_of_subset

@[simp] lemma reducible_KT_S4 : (𝐊𝐓 : AxiomSet α) ≤ₛ 𝐒𝟒 := reducible_of_subset

@[simp] lemma reducible_K4_S4 : (𝐊𝟒 : AxiomSet α) ≤ₛ 𝐒𝟒 := reducible_of_subset

@[simp] lemma reducible_S4_S4Dot2 : (𝐒𝟒 : AxiomSet α) ≤ₛ 𝐒𝟒.𝟐 := reducible_of_subset

@[simp] lemma reducible_S4_S4Dot3 : (𝐒𝟒 : AxiomSet α) ≤ₛ 𝐒𝟒.𝟑 := reducible_of_subset

@[simp] lemma reducible_S4_S4Grz : (𝐒𝟒 : AxiomSet α) ≤ₛ 𝐒𝟒𝐆𝐫𝐳 := reducible_of_subset

end LO.Modal.Standard
