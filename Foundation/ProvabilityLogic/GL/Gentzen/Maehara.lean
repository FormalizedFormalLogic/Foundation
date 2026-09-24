module

public import Foundation.ProvabilityLogic.GL.Gentzen.Basic

/-!
# Maehara's method for `GL`

## References

- [SV82]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace GL.Gentzen

variable {α : Type*} [DecidableEq α] {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {C : Formula α}
  {S : Sequent α}

/-- `C` is an interpolant of the sequent `Γ₁, Γ₂ ⟹ Δ₁, Δ₂` along the split into
`Γ₁ ⟹ Δ₁` and `Γ₂ ⟹ Δ₂`. -/
structure IsInterpolant (Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α) (C : Formula α) : Prop where
  left : ⊢ᴳ[GL] Γ₁ ⟹ insert C Δ₁
  right : ⊢ᴳ[GL] insert C Γ₂ ⟹ Δ₂
  atoms : C.atoms ⊆ (Γ₁ ∪ Δ₁).atoms ∩ (Γ₂ ∪ Δ₂).atoms

lemma IsInterpolant.swap (h : IsInterpolant Γ₂ Γ₁ Δ₂ Δ₁ C) :
    IsInterpolant Γ₁ Γ₂ Δ₁ Δ₂ (∼C) where
  left := negR h.right
  right := negL h.left
  atoms := by simpa [Finset.inter_comm] using h.atoms

lemma exists_interpolant_of_swap (h : ∃ C, IsInterpolant Γ₂ Γ₁ Δ₂ Δ₁ C) :
    ∃ C, IsInterpolant Γ₁ Γ₂ Δ₁ Δ₂ C := by
  obtain ⟨C, hC⟩ := h;
  exact ⟨_, hC.swap⟩;

/-- - [SV82] -/
theorem exists_interpolant (h : ⊢ᴳ[GL] S) (hΓ : S.ant ⊆ Γ₁ ∪ Γ₂) (hΔ : S.suc ⊆ Δ₁ ∪ Δ₂) :
    ∃ C, IsInterpolant Γ₁ Γ₂ Δ₁ Δ₂ C := by
  induction h generalizing Γ₁ Γ₂ Δ₁ Δ₂ with
  | axm A =>
    dsimp only at hΓ hΔ;
    wlog hA : A ∈ Γ₁ generalizing Γ₁ Γ₂ Δ₁ Δ₂;
    · exact exists_interpolant_of_swap <|
        this (by rwa [Finset.union_comm]) (by rwa [Finset.union_comm]) (by grind);
    by_cases hA' : A ∈ Δ₁;
    · exact ⟨⊥, union A, botL_mem, by simp⟩;
    · have h₁ := FormulaFinset.atoms_subset_of_mem hA;
      have h₂ := FormulaFinset.atoms_subset_of_mem (show A ∈ Δ₂ by grind);
      exact ⟨A, union A, union A (by simp) (by grind), by simp [Finset.subset_iff] at *; grind⟩;
  | botL =>
    dsimp only at hΓ;
    wlog h : ⊥ ∈ Γ₁ generalizing Γ₁ Γ₂ Δ₁ Δ₂;
    · exact exists_interpolant_of_swap <|
        this (by rwa [Finset.union_comm]) (by rwa [Finset.union_comm]) (by grind);
    exact ⟨⊥, botL_mem, botL_mem, by simp⟩;
  | wkL _ h ih => exact ih (h.trans hΓ) hΔ;
  | wkR _ h ih => exact ih hΓ (h.trans hΔ);
  | @impL Γ Δ A B _ _ ih₁ ih₂ =>
    dsimp only at hΓ hΔ ih₁ ih₂;
    wlog h : A 🡒 B ∈ Γ₁ generalizing Γ₁ Γ₂ Δ₁ Δ₂;
    · have h' := (Finset.mem_union.mp (hΓ (Finset.mem_insert_self _ _))).resolve_left h;
      exact exists_interpolant_of_swap <|
        this (by rwa [Finset.union_comm]) (by rwa [Finset.union_comm]) h';
    obtain ⟨C₁, hC₁⟩ :=
      ih₁ (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ₁ := insert A Δ₁) (Δ₂ := Δ₂) (by grind) (by grind);
    obtain ⟨C₂, hC₂⟩ :=
      ih₂ (Γ₁ := insert B Γ₁) (Γ₂ := Γ₂) (Δ₁ := Δ₁) (Δ₂ := Δ₂) (by grind) (by grind);
    clear ih₁ ih₂;
    have h₁ : ⊢ᴳ[GL] Γ₁ ⟹ insert A (insert (C₁ ⋎ C₂) Δ₁) :=
      wkR (orR (wkR (Δ' := insert C₁ (insert C₂ (insert A Δ₁))) hC₁.left));
    have h₂ : ⊢ᴳ[GL] insert B Γ₁ ⟹ insert (C₁ ⋎ C₂) Δ₁ :=
      orR (wkR (Δ' := insert C₁ (insert C₂ Δ₁)) hC₂.left);
    have h₃ := hC₁.atoms;
    have h₄ := hC₂.atoms;
    have h₅ := FormulaFinset.atoms_subset_of_mem h;
    use C₁ ⋎ C₂;
    constructor;
    · exact wkL (impL h₁ h₂);
    · exact orL hC₁.right hC₂.right;
    · simp [Finset.subset_iff] at h₃ h₄ h₅ ⊢;
      grind;
  | @impR Γ Δ A B _ ih =>
    dsimp only at hΓ hΔ ih;
    wlog h : A 🡒 B ∈ Δ₁ generalizing Γ₁ Γ₂ Δ₁ Δ₂;
    · have h' := (Finset.mem_union.mp (hΔ (Finset.mem_insert_self _ _))).resolve_left h;
      exact exists_interpolant_of_swap <|
        this (by rwa [Finset.union_comm]) (by rwa [Finset.union_comm]) h';
    obtain ⟨C, hC⟩ :=
      ih (Γ₁ := insert A Γ₁) (Γ₂ := Γ₂) (Δ₁ := insert B Δ₁) (Δ₂ := Δ₂) (by grind) (by grind);
    clear ih;
    have h₁ := hC.atoms;
    have h₂ := FormulaFinset.atoms_subset_of_mem h;
    use C;
    constructor;
    · exact wkR (impR (wkR (Δ' := insert B (insert C Δ₁)) hC.left));
    · exact hC.right;
    · simp [Finset.subset_iff] at h₁ h₂ ⊢;
      grind;
  | @boxGL Γ A _ ih =>
    dsimp only at hΓ hΔ ih;
    wlog h : □A ∈ Δ₂ generalizing Γ₁ Γ₂ Δ₁ Δ₂;
    · clear ih;
      exact exists_interpolant_of_swap <|
        this (by rwa [Finset.union_comm]) (by rwa [Finset.union_comm]) (by grind);
    have hΓ' : ∀ B ∈ Γ, □B ∈ Γ₁ ∨ □B ∈ Γ₂ :=
      fun B hB ↦ Finset.mem_union.mp (hΓ (Finset.mem_image_of_mem _ hB));
    obtain ⟨C, hC⟩ := ih (Γ₁ := Γ₁.prebox ∪ Γ₁.prebox.box)
      (Γ₂ := insert (□A) (Γ₂.prebox ∪ Γ₂.prebox.box)) (Δ₁ := ∅) (Δ₂ := {A})
      (by intro B; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]; grind)
      (by simp);
    clear ih;
    have h₁ : ⊢ᴳ[GL] Γ₁.prebox.box ⟹ {□C} := boxGL (wkL hC.left);
    have h₂ : ⊢ᴳ[GL] (insert C Γ₂.prebox).box ⟹ {□A} := boxGL (wkL hC.right);
    have h₃ := hC.atoms;
    have h₄ := FormulaFinset.atoms_subset_of_mem h;
    have h₅ := FormulaFinset.atoms_prebox (Γ := Γ₁);
    have h₆ := FormulaFinset.atoms_prebox (Γ := Γ₂);
    use □C;
    constructor;
    · exact wk h₁ (by grind) (by simp);
    · exact wk h₂ (by grind) (by simpa);
    · simp [Finset.subset_iff] at h₃ h₄ h₅ h₆ ⊢;
      grind;

end GL.Gentzen

end FFL.ProvabilityLogic

end
