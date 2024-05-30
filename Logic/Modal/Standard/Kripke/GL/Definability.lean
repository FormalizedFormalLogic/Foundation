import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

variable {W α : Type*}  [Inhabited W] [Inhabited α]

open System
open Kripke
open Formula Formula.Kripke

variable {F: Kripke.Frame W α}

private lemma AxiomSet.L.definability.implies_transitive : F ⊧* 𝐋 → Transitive F := by
  contrapose;
  intro hT; simp [Transitive] at hT;
  obtain ⟨w₁, w₂, w₃, r₂₃, r₁₂, nr₁₃⟩ := hT;
  simp only [AxiomSet.L, Axioms.L, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff,
    ValidOnFrame, ValidOnModel.iff_models, ValidOnModel, forall_exists_index,
    forall_apply_eq_imp_iff, Semantics.Tarski.realize_imp, Satisfies.box_def, not_forall,
    exists_prop];
  existsi (atom default), (λ w' _ => (w' ≠ w₂ ∧ w' ≠ w₃)), w₁;
  constructor;
  . intro x hx h;
    by_cases hx₂ : x = w₂;
    . subst hx₂; simpa using h w₃ r₂₃;
    . by_cases hx₃ : x = w₃ <;> simp_all [hx₃];
  . existsi w₂;
    simpa;

private lemma AxiomSet.L.definability.implies_cwf  : F ⊧* 𝐋 → ConverseWellFounded F := by
  contrapose;
  intro hCF;
  obtain ⟨X, hX₁, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
  let V : Valuation W α := λ w _ => w ∉ X;
  let w := hX₁.some;
  let a : Formula α := atom default;
  simp only [AxiomSet.L, Axioms.L, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff,
    ValidOnFrame, ValidOnModel.iff_models, ValidOnModel, forall_exists_index,
    forall_apply_eq_imp_iff, Semantics.Tarski.realize_imp, Satisfies.box_def, not_forall,
    exists_prop];
  existsi (atom default), V, w;
  constructor;
  . intro x _;
    by_cases hxs : x ∈ X
    . obtain ⟨y, hy₁, hy₂⟩ := hX₂ x hxs;
      intro h;
      exact h x (by aesop);
    . aesop;
  . obtain ⟨w', hw'₁, hw'₂⟩ := hX₂ w (by apply Set.Nonempty.some_mem);
    simp;
    existsi w';
    constructor;
    . simpa [flip] using hw'₂;
    . simp_all [V, w, a];

private lemma AxiomSet.L.definability.impliedby : (Transitive F ∧ ConverseWellFounded F) → F ⊧* 𝐋 := by
  rintro ⟨hTrans, hWF⟩;
  simp [AxiomSet.L, Axioms.L];
  intro p V w;
  let M := Model.mk F V;
  simp only [Semantics.Tarski.realize_imp];
  contrapose;

  intro h;
  obtain ⟨z, rwz, hz⟩ := by simpa using h;
  obtain ⟨xm, ⟨hxm₁, hxm₂⟩⟩ := hWF.has_min ({ x | (F w x) ∧ ¬((M, x) ⊧ p) }) (by existsi z; simp_all)
  simp [Satisfies.box_def];

  have : ((M, xm) ⊧ □p) := by
    by_contra hC;
    obtain ⟨y, hy₁, hy₂⟩ := by simpa using hC;
    have : ¬(F xm y) := hxm₂ y ⟨(hTrans (by simp_all) hy₁), hy₂⟩;
    contradiction;
  existsi xm;
  simp_all;

open AxiomSet.L.definability in
instance AxiomSet.L.definability : Definability (α := α) 𝐋 (λ F => Transitive F ∧ ConverseWellFounded F) where
  defines W _ F := by
    constructor;
    . intro h;
      constructor;
      . exact implies_transitive h;
      . exact implies_cwf h;
    . intro h;
      apply impliedby;
      simp_all;

instance AxiomSet.L.finiteDefinability : FiniteDefinability (α := α) 𝐋 (λ F => Transitive F ∧ Irreflexive F) where
  fin_defines W _ _ F := by
    constructor;
    . intro h;
      obtain ⟨hTrans, hCWF⟩ := L.definability.defines W F |>.mp h;
      constructor;
      . simpa;
      . by_contra hIrrefl;
        have := ConverseWellFounded.iff_has_max.mp hCWF;
        simp [Irreflexive] at hIrrefl;
        obtain ⟨w, h⟩ := hIrrefl;
        have := this {w} (by simp);
        simp_all;
    . rintro ⟨hTrans, hIrrefl⟩;
      apply AxiomSet.L.definability.defines W F |>.mpr;
      exact ⟨hTrans, @Finite.converseWellFounded_of_trans_irrefl _ F _ ⟨hTrans⟩ ⟨hIrrefl⟩⟩;

instance : FiniteFrameClass.Nonempty (α := α) 𝔽ꟳ(𝐋) where
  W := PUnit;
  existsi := by
    existsi (λ _ _ => False);
    apply iff_finiteDefinability_memFiniteFrameClass (AxiomSet.L.finiteDefinability) |>.mpr;
    simp [Transitive, Irreflexive];

instance AxiomSet.GL.definability : Definability (α := α) 𝐆𝐋 (λ F => Transitive F ∧ ConverseWellFounded F) := inferInstance

instance AxiomSet.GL.finiteDefinability : FiniteDefinability (α := α) 𝐆𝐋 (λ F => Transitive F ∧ Irreflexive F) := inferInstance

instance : FiniteFrameClass.Nonempty (α := α) 𝔽ꟳ(𝐆𝐋) where
  W := PUnit;
  existsi := by
    existsi (λ _ _ => False);
    apply iff_finiteDefinability_memFiniteFrameClass (AxiomSet.GL.finiteDefinability) |>.mpr;
    simp [Transitive, Irreflexive];

instance : System.Consistent (𝐆𝐋 : AxiomSet α) := inferInstance

end LO.Modal.Standard
