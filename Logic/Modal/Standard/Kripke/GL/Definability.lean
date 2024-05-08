import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

variable {W α : Type*} [Inhabited α]

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
    exists_prop]; -- TODO: cleanup
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
    exists_prop]; -- TODO: cleanup
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
  simp [AxiomSet.L, Axioms.L]; -- TODO: cleanup
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
instance AxiomSet.L.definability : Kripke.AxiomSetDefinability W (𝐋 : AxiomSet α) (λ F => Transitive F ∧ ConverseWellFounded F) where
  defines F := by
    constructor;
    . intro h;
      apply impliedby;
      simp_all;
    . intro h;
      constructor;
      . exact implies_transitive h;
      . exact implies_cwf h;

instance AxiomSet.L.finiteDefinability [Finite W] : Kripke.AxiomSetDefinability W (𝐋 : AxiomSet α) (λ F => Transitive F ∧ Irreflexive F) where
  defines F := by
    constructor;
    . rintro ⟨hTrans, hIrrefl⟩;
      have hCWF := @Finite.converseWellFounded_of_trans_irrefl _ F _ ⟨hTrans⟩ ⟨hIrrefl⟩;
      apply AxiomSet.L.definability.defines F |>.mp;
      constructor <;> simpa;
    . intro h;
      obtain ⟨hTrans, hCWF⟩ := AxiomSet.L.definability.defines F |>.mpr h;
      constructor;
      . simpa;
      . by_contra hIrrefl;
        have := ConverseWellFounded.iff_has_max.mp hCWF;
        simp [Irreflexive] at hIrrefl;
        obtain ⟨w, h⟩ := hIrrefl;
        have := this {w} (by simp);
        simp_all;

instance [Finite W] {𝔽 : AxiomSetFrameClass W (𝐋 : AxiomSet α)} : Set.Nonempty 𝔽.frameclass := by
  existsi (λ _ _ => False);
  apply iff_definability_memAxiomSetFrameClass AxiomSet.L.finiteDefinability |>.mp;
  constructor;
  . simp [Transitive];
  . simp [Irreflexive];

instance AxiomSet.GL.definability : Kripke.AxiomSetDefinability W (𝐆𝐋 : AxiomSet α) (λ F => Transitive F ∧ ConverseWellFounded F) := inferInstance

end LO.Modal.Standard
