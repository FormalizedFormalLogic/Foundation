import Logic.Modal.Standard.Kripke.Completeness
import Logic.Modal.Standard.Kripke.Geach.Definability

namespace LO.Modal.Standard

namespace Kripke

open System
open Formula

variable {W α : Type*}
variable {Λ : AxiomSet α} [Inhabited α] [DecidableEq α]

instance AxiomSet.Geach.Canonical_with_K (t) : Canonical (𝐊 ∪ 𝐠𝐞(t) : AxiomSet α) where
  valid := by
    simp only [Semantics.RealizeSet.union_iff];
    constructor;
    . apply AxiomSet.K.definability.defines _ |>.mp; trivial;
    . apply AxiomSet.Geach.definability t |>.defines _ |>.mp;
      rintro Ω₁ Ω₂ Ω₃ ⟨hi, hj⟩;
      let ⟨Ω, hΩ⟩ := MaximalΛConsistentTheory.lindenbaum (Λ := 𝐊 ∪ 𝐠𝐞(t)) (T := (□⁻¹^[t.m]Ω₂.theory) ∪ (□⁻¹^[t.n]Ω₃.theory)) (by
        intro Γ hΓ;
        sorry;

        -- have h₂ : □^[l.m](⋀Δ₂) ∈ Ω₂ := by sorry;
        -- have h₃ : □^[l.n](⋀Δ₃) ∈ Ω₃ := by sorry;
      );
      existsi Ω;
      constructor;
      . apply Kripke.CanonicalModel.multiframe_def_multibox.mpr;
        intro p hp;
        apply hΩ;
        simp_all;
      . apply Kripke.CanonicalModel.multiframe_def_multibox.mpr;
        intro p hp;
        apply hΩ;
        simp_all;

lemma subset_Canonical₂ (hΛ : Λ ⊆ Λ') (h : CanonicalFrame Λ ⊧ p) : CanonicalFrame Λ' ⊧ p := by
  intro V w;
  have := h (CanonicalModel Λ).valuation;



lemma subset_Canonical (hΛ : Λ ⊆ Λ') (h : CanonicalFrame Λ ⊧* P) : CanonicalFrame Λ' ⊧* P := by
  simp_all only [Semantics.realizeSet_iff];
  intro p hp;
  exact subset_Canonical₂ hΛ $ h hp;


instance AxiomSet.GeachLogic.Canonical (ts) : Canonical (𝐆𝐞(ts) : AxiomSet α) where
  valid := by
    induction ts with
    | nil => apply AxiomSet.K.definability.defines _ |>.mp; trivial;
    | cons t ts ih =>
      simp;
      constructor;
      . have := by simpa only [Semantics.RealizeSet.union_iff] using AxiomSet.Geach.Canonical_with_K (α := α) t |>.valid;
        exact subset_Canonical (by simp; apply Set.subset_union_of_subset_right AxiomSet.GeachLogic.subsetK;) this.2 ;
      . exact subset_Canonical (by simp) ih;
    /-
    apply AxiomSet.GeachLogic.definability l |>.defines _ |>.mp;
    | cons t ts ih =>
      simp only [CanonicalFrame, CanonicalModel];
      constructor;
      . sorry;
      . sorry;
    -/
    /-
    rintro Ω₁ Ω₂ Ω₃ ⟨hi, hj⟩;
    let ⟨Ω, hΩ⟩ := MaximalΛConsistentTheory.lindenbaum (Λ := AxiomSet.Geach t) (T := (□⁻¹^[t.m]Ω₂.theory) ∪ (□⁻¹^[t.n]Ω₃.theory)) (by
      intro Γ hΓ;
      sorry;

      -- have h₂ : □^[l.m](⋀Δ₂) ∈ Ω₂ := by sorry;
      -- have h₃ : □^[l.n](⋀Δ₃) ∈ Ω₃ := by sorry;
    );
    existsi Ω;
    constructor;
    . apply Kripke.CanonicalModel.multiframe_def_multibox.mpr;
      intro p hp;
      apply hΩ;
      simp_all;
    . sorry;
  -/

instance [Λ.IsGeach] : Canonical Λ := by
  rw [AxiomSet.IsGeach.char (Λ := Λ)];
  apply AxiomSet.GeachLogic.Canonical;

instance [Λ.IsGeach] : Complete Λ 𝔽(Λ, MCT Λ) := inferInstance

instance : Complete (𝐒𝟒 : AxiomSet α) 𝔽((𝐒𝟒 : AxiomSet α), MCT (𝐒𝟒 : AxiomSet α)) := inferInstance

instance : Complete (𝐒𝟓 : AxiomSet α) 𝔽((𝐒𝟓 : AxiomSet α), MCT (𝐒𝟓 : AxiomSet α)) := inferInstance

end Kripke

end LO.Modal.Standard
