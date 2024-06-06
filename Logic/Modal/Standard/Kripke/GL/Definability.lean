import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

variable {W α : Type u} [Inhabited W] [Inhabited α]

open System
open Kripke
open Formula Formula.Kripke

variable {F : Kripke.Frame' α}

private lemma AxiomSet.L.definability.implies_transitive : F ⊧* 𝗟 → Transitive F.Rel := by
  contrapose;
  intro hT; simp [Transitive] at hT;
  obtain ⟨w₁, w₂, r₁₂, w₃, r₂₃, nr₁₃⟩ := hT;
  simp only [Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, ValidOnFrame,
    ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models, forall_exists_index,
    forall_apply_eq_imp_iff, Satisfies.imp_def, Satisfies.box_def, not_forall, exists_prop];
  existsi (atom default), (λ w' _ => w' ≠ w₂ ∧ w' ≠ w₃), w₁;
  constructor;
  . intro x hx h;
    by_cases hx₂ : x = w₂;
    . subst hx₂; simpa [Satisfies] using h w₃ r₂₃;
    . by_cases hx₃ : x = w₃ <;> simp_all [Satisfies, hx₃];
  . existsi w₂; simpa [Satisfies];

private lemma AxiomSet.L.definability.implies_cwf  : F ⊧* 𝗟 → ConverseWellFounded F.Rel := by
  contrapose;
  intro hCF;
  obtain ⟨X, hX₁, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
  simp only [Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, ValidOnFrame,
    ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models, forall_exists_index,
    forall_apply_eq_imp_iff, Satisfies.imp_def, Satisfies.box_def, not_forall, exists_prop];
  existsi (atom default), (λ w _ => w ∉ X), hX₁.some;
  constructor;
  . intro x _;
    by_cases hxs : x ∈ X
    . obtain ⟨y, hy₁, hy₂⟩ := hX₂ x hxs;
      intro h;
      exact h x (by simp_all only [Satisfies]);
    . aesop;
  . obtain ⟨w', hw'₁, hw'₂⟩ := hX₂ hX₁.some (by apply Set.Nonempty.some_mem);
    existsi w';
    constructor;
    . simpa using hw'₂;
    . simpa [Satisfies];

private lemma AxiomSet.L.definability.impliedby : (Transitive F.Rel ∧ ConverseWellFounded F.Rel) → F ⊧* 𝗟 := by
  rintro ⟨hTrans, hWF⟩;
  simp [AxiomSet.L, Axioms.L];
  intro p V w;
  simp only [Satisfies.iff_models, Satisfies.imp_def];
  contrapose;
  intro h;
  obtain ⟨z, rwz, hz⟩ := by simpa using h;
  obtain ⟨xm, ⟨hxm₁, hxm₂⟩⟩ := hWF.has_min ({ x | (F.Rel w x) ∧ ¬(Satisfies ⟨F, V⟩ x p) }) (by existsi z; simp_all)
  simp [Satisfies.box_def];
  existsi xm;
  have : Satisfies ⟨F, V⟩ xm (□p) := by
    by_contra hC;
    obtain ⟨y, hy₁, hy₂⟩ := by simpa using hC;
    have : ¬(xm ≺ y) := hxm₂ y ⟨(hTrans (by simp_all) hy₁), hy₂⟩;
    contradiction;
  simp_all;

open AxiomSet.L.definability in
instance AxiomSet.L.definability : Definability (α := α) 𝗟 (λ F => Transitive F.Rel ∧ ConverseWellFounded F.Rel) where
  defines F := by
    constructor;
    . intro h;
      constructor;
      . exact implies_transitive h;
      . exact implies_cwf h;
    . intro h;
      apply impliedby;
      simp_all;

instance AxiomSet.L.finiteDefinability : FiniteDefinability (α := α) 𝗟 (λ F => Transitive F.Rel ∧ Irreflexive F.Rel) where
  fin_defines F := by
    constructor;
    . intro h;
      obtain ⟨hTrans, hCWF⟩ := L.definability.defines F.toFrame |>.mp h;
      constructor;
      . simpa;
      . by_contra hIrrefl;
        have := ConverseWellFounded.iff_has_max.mp hCWF;
        simp [Irreflexive] at hIrrefl;
        obtain ⟨w, h⟩ := hIrrefl;
        have := this {w} (by simp);
        simp_all;
    . rintro ⟨hTrans, hIrrefl⟩;
      apply AxiomSet.L.definability.defines F.toFrame |>.mpr;
      exact ⟨hTrans, @Finite.converseWellFounded_of_trans_irrefl _ F.Rel F.World_finite ⟨hTrans⟩ ⟨hIrrefl⟩⟩;

instance : FiniteFrameClass.IsNonempty (𝔽ꟳ(𝗟) : FiniteFrameClass' α) where
  nonempty := by
    existsi { World := PUnit, Rel := λ _ _ => False };
    apply iff_finiteDefinability_memFiniteFrameClass (AxiomSet.L.finiteDefinability) |>.mpr;
    simp [Transitive, Irreflexive];

instance : FiniteFrameClass.IsNonempty (𝔽ꟳ(Ax(𝐆𝐋)) : FiniteFrameClass' α) where
  nonempty := by
    existsi { World := PUnit, Rel := λ _ _ => False };
    apply iff_finiteDefinability_memFiniteFrameClass
      (show FiniteDefinability (α := α) (𝗞 ∪ 𝗟) (λ F => Transitive F.Rel ∧ Irreflexive F.Rel) by infer_instance)
      |>.mpr;
    simp [Transitive, Irreflexive];

instance : System.Consistent (𝐆𝐋 : DeductionParameter α) := inferInstance

end LO.Modal.Standard
