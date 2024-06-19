import Logic.Modal.Standard.Kripke.Completeness
import Logic.Modal.Standard.Kripke.Geach.Definability

namespace LO.Modal.Standard

namespace Kripke

open System
open Formula

variable [Inhabited α] [DecidableEq α]

open Theory MaximalConsistentTheory CanonicalFrame in
lemma definability_canonicalFrame_GeachAxiom {𝓓 : DeductionParameter α} [𝓓.HasNecOnly] [includeK : 𝓓.IsIncludeK] [Inhabited (𝓓)-MCT] (hAx : 𝗴𝗲(t) ⊆ Ax(𝓓)) : GeachConfluent t (CanonicalFrame 𝓓) := by
  have : 𝓓.IsNormal := ⟨⟩;

  intro Ω₁ Ω₂ Ω₃ h;
  have ⟨r₁₂, r₁₃⟩ := h; clear h;
  have ⟨Ω, hΩ⟩ := MaximalConsistentTheory.lindenbaum (𝓓 := 𝓓) (T := ((□''⁻¹^[t.m]Ω₂.theory) ∪ (□''⁻¹^[t.n]Ω₃.theory))) $ by
    apply intro_union_Consistent;
    intro Γ Δ hΓ hΔ hC;
    replace hΓ : ∀ p ∈ Γ, □^[t.m]p ∈ Ω₂.theory := by simpa using hΓ;
    have hΓconj : □^[t.m](Γ.conj') ∈ Ω₂.theory := iff_mem_multibox_conj'.mpr hΓ;

    replace hΔ : ∀ p ∈ Δ, □^[t.n]p ∈ Ω₃.theory := by simpa using hΔ;
    have : □^[t.n](Δ.conj') ∈ Ω₃.theory := iff_mem_multibox_conj'.mpr hΔ;

    have : □^[t.j](◇^[t.n](Γ.conj')) ∈ Ω₁.theory := iff_mem_imp.mp
      (membership_iff.mpr $ Context.of! ⟨Deduction.maxm (by apply hAx; simp_all)⟩)
      (multiframe_def_multidia.mp r₁₂ hΓconj)
    have : ◇^[t.n]Γ.conj' ∈ Ω₃.theory := multiframe_def_multibox.mp r₁₃ this;

    have : 𝓓 ⊢! □^[t.n](Δ.conj') ⋏ ◇^[t.n](Γ.conj') ⟶ ⊥ := by
      apply and_imply_iff_imply_imply'!.mpr;
      exact imp_trans''!
        (show 𝓓 ⊢! □^[t.n](Δ.conj') ⟶ □^[t.n](~Γ.conj') by exact imply_multibox_distribute'! $ contra₁'! $ and_imply_iff_imply_imply'!.mp hC)
        (show 𝓓 ⊢! □^[t.n](~Γ.conj') ⟶ ~(◇^[t.n]Γ.conj') by exact contra₁'! $ and₁'! $ multidia_duality!);
    have : 𝓓 ⊬! □^[t.n](Δ.conj') ⋏ ◇^[t.n](Γ.conj') ⟶ ⊥ := by simpa using Ω₃.consistent (Γ := [□^[t.n](Δ.conj'), ◇^[t.n](Γ.conj')]) (by simp_all)

    contradiction;
  existsi Ω;
  simp [multiframe_def_multibox];
  constructor <;> { intros; apply hΩ; simp_all; }

lemma definability_canonicalFrame_multiGeachAxiom {𝓓 : DeductionParameter α} [𝓓.HasNecOnly] [Inhabited (𝓓)-MCT] (hAx : 𝗚𝗲(ts) ⊆ Ax(𝓓)) : MultiGeachConfluent ts (CanonicalFrame 𝓓) := by
  induction ts with
  | nil => simp [MultiGeachConfluent];
  | cons t ts ih =>
    simp;
    constructor;
    . exact definability_canonicalFrame_GeachAxiom (includeK := ⟨(Set.Subset.trans AxiomSet.MultiGeach.subsetK hAx)⟩) (by aesop)
    . apply ih;
      simp_all;

instance geach_canonical : Canonical (𝐆𝐞(l) : DeductionParameter α) := canonical_of_definability (AxiomSet.MultiGeach.definability l) $ definability_canonicalFrame_multiGeachAxiom (by simp)

variable {𝓓 : DeductionParameter α}

instance [geach : 𝓓.IsGeach] : Canonical 𝓓 := by
  convert geach_canonical (α := α) (l := geach.taples);
  exact geach.char

instance [𝓓.IsGeach] : Complete 𝓓 𝔽(Ax(𝓓)) := instComplete

instance : Complete (𝐒𝟒 : DeductionParameter α) 𝔽(Ax(𝐒𝟒)) := instComplete

instance : Complete (𝐒𝟓 : DeductionParameter α) 𝔽(Ax(𝐒𝟓)) := instComplete

end Kripke

end LO.Modal.Standard
