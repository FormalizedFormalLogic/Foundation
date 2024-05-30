import Logic.Modal.Standard.Kripke.Completeness
import Logic.Modal.Standard.Kripke.Geach.Definability

namespace LO.Modal.Standard

namespace Kripke

open System
open Formula

variable {Λ : AxiomSet α} [Inhabited α] [DecidableEq α]

/-
instance AxiomSet.Geach.Canonical_with_K [Inhabited (MCT (α := α) 𝐠𝐞(t))] (t) : Canonical (α := α) 𝐠𝐞(t) where
  realize := by
    sorry;
    /-
    -- simp only [Semantics.RealizeSet.union_iff];
    apply AxiomSet.Geach.definability t |>.defines _ |>.mp;
    constructor;
    . apply AxiomSet.K.definability.defines _ _ |>.mp; trivial;
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
    -/
-/

/-
lemma subset_Canonical₂ [HasAxiomK Λ] (hΛ : Λ ⊆ Λ') (h : CanonicalFrame Λ ⊧ p) : CanonicalFrame Λ' ⊧ p := by
  sorry;

lemma subset_Canonical [HasAxiomK Λ] (hΛ : Λ ⊆ Λ') (h : CanonicalFrame Λ ⊧* P) : CanonicalFrame Λ' ⊧* P := by
  simp_all only [Semantics.realizeSet_iff];
  intro p hp;
  exact subset_Canonical₂ hΛ $ h hp;

lemma str {P : ∀ {W}, (Frame W α) → Prop} (hs : Λ ⊆ Λ') : P (CanonicalFrame Λ) → P (CanonicalFrame Λ') := by
  sorry;
-/

/-
instance AxiomSet.GeachLogic.Canonical (ts) : Canonical (𝐆𝐞(ts) : AxiomSet α) where
  realize := by
    apply AxiomSet.GeachLogic.definability ts |>.defines _ _ |>.mpr;
    induction ts with
    | nil => simp [MultiGeachConfluent];
    | cons t ts ih =>
      simp;
      sorry;
      /-
      constructor;
      . exact str (P := GeachConfluent t) (Λ := 𝐠𝐞(t)) (by simp) (by
          apply AxiomSet.Geach.definability t |>.defines _ _ |>.mp;

          sorry
        );
        apply str (P := GeachConfluent t) (α := α) (Λ := 𝐠𝐞(t)) (Λ' := 𝐆𝐞(ts) ∪ 𝐠𝐞(t)) (by simp);
        exact AxiomSet.Geach.Canonical_with_K t |>.realize;
      . exact str (P := MultiGeachConfluent ts) (by simp) ih;
      -/

    /-
    induction ts with
    | nil => apply AxiomSet.K.definability.defines _ |>.mp; trivial;
    | cons t ts ih =>
      simp;
      constructor;
      . have := by simpa only [Semantics.RealizeSet.union_iff] using AxiomSet.Geach.Canonical_with_K (α := α) t |>.valid;
        exact subset_Canonical (by simp; apply Set.subset_union_of_subset_right AxiomSet.GeachLogic.subsetK;) this.2 ;
      . exact subset_Canonical (by simp) ih;
    -/
-/


instance geach_canonical : Canonical (𝐆𝐞(l) : DeductionParameter α) := canonical_of_definability (AxiomSet.MultiGeach.definability l) (by sorry)

variable {L : DeductionParameter α}

instance [geach : L.IsGeach] : Canonical L := by
  convert geach_canonical (α := α) (l := geach.taples);
  exact geach.char

instance [L.IsGeach] : Complete L 𝔽(Ax(L)) := instComplete

instance : Complete (𝐒𝟒 : DeductionParameter α) 𝔽(Ax(𝐒𝟒)) := instComplete

instance : Complete (𝐒𝟓 : DeductionParameter α) 𝔽(Ax(𝐒𝟓)) := instComplete

end Kripke

end LO.Modal.Standard
