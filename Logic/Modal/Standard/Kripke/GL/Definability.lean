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
  -- simp [AxiomSet.L, Axioms.L, ValidOnFrame, ValidOnModel];
  -- existsi (atom default);
  -- existsi (λ w' _ => (w' ≠ w₂ ∧ w' ≠ w₃)), w₁;
  sorry;
  -- constructor;
  -- . intro x hx h;
  --   by_cases hx₂ : x = w₂;
  --   . simp_all [hx₂]; simpa using h w₃ r₂₃;
  --   . by_cases hx₃ : x = w₃ <;> simp_all [hx₃];
  -- . existsi w₂;
  --   aesop;

private lemma AxiomSet.L.definability.implies_cwf  : F ⊧* 𝐋 → ConverseWellFounded F := by
  sorry;
  /-
  contrapose;
  intro hCF;
  obtain ⟨X, hX₁, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
  let V : Valuation α β := λ w _ => w ∉ X;
  let w := hX₁.some;
  let a : Formula β := atom default;
  apply Theory.not_Frames;
  simp [Theory.Satisfies, -Satisfies.box_def];
  existsi V, w, a;
  constructor;
  . simp only [Formula.Satisfies.box_def];
    intro x _;
    by_cases hxs : x ∈ X
    . obtain ⟨y, hy₁, hy₂⟩ := hX₂ x hxs;
      simp only [Formula.Satisfies.imp_def];
      left;
      simp;
      existsi y;
      constructor;
      . simpa [flip] using hy₂;
      . simpa [V, w, a];
    . aesop;
  . obtain ⟨w', hw'₁, hw'₂⟩ := hX₂ w (by apply Set.Nonempty.some_mem);
    simp;
    existsi w';
    constructor;
    . simpa [flip] using hw'₂;
    . simp_all [V, w, a];
  -/

private lemma AxiomSet.L.definability.impliedby : (Transitive F ∧ ConverseWellFounded F) → F ⊧* 𝐋 := by
  sorry;
  /-
  rintro ⟨hTrans, hWF⟩;
  simp [axiomL, AxiomSet.L];
  intro p V w;
  simp only [Formula.Satisfies.imp_def'];
  suffices (w ⊮ᴹ[⟨F, V⟩] □p) → (w ⊮ᴹ[⟨F, V⟩] □(□p ⟶ p)) by exact not_imp_not.mp this;

  intro h; simp [Unsatisfies] at h;
  obtain ⟨z, rwz, hz⟩ := h;
  obtain ⟨xm, ⟨hxm₁, hxm₂⟩⟩ := hWF.has_min ({ x | (F w x) ∧ (x ⊮ᴹ[⟨F, V⟩] p) }) (by existsi z; simp [rwz, hz];)

  have h₁ : (xm ⊩ᴹ[⟨F, V⟩] □p) := by
    simp [Satisfies.box_def];
    intro y hy;
    have : F w y := hTrans (by simp_all) hy;
    by_contra hC;
    have := hxm₂ y ⟨(hTrans (by simp_all) hy), hC⟩;
    contradiction;
  have h₂ : (xm ⊮ᴹ[⟨F, V⟩] (□p ⟶ p)) := by
    simp only [Unsatisfies, Formula.Satisfies.imp_def', not_imp];
    constructor;
    . exact h₁
    . simp_all;
  have h₃ : w ⊮ᴹ[⟨F, V⟩] □(□p ⟶ p) := by
    simp [Unsatisfies, Satisfies.box_def, -Satisfies.imp_def'];
    existsi xm;
    constructor;
    . simp_all;
    . exact h₂;
  exact h₃;
  -/

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
