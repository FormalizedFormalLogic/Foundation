import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

namespace Kripke

open LO.Kripke
open System
open Kripke
open Formula

variable {α : Type u} [Inhabited α]

variable {F : Kripke.Frame}

abbrev TransitiveCWFFrameClass : FrameClass := λ F => Transitive F ∧ ConverseWellFounded F

private lemma trans_of_L : F#α ⊧* (𝗟 : AxiomSet α) → Transitive F.Rel := by
  contrapose;
  intro hT; simp [Transitive] at hT;
  obtain ⟨w₁, w₂, r₁₂, w₃, r₂₃, nr₁₃⟩ := hT;
  apply iff_not_validOnFrame.mpr;
  use (Axioms.L (atom default));
  constructor;
  . simp;
  . use (λ w' _ => w' ≠ w₂ ∧ w' ≠ w₃), w₁;
    simp only [Kripke.Satisfies]; simp;
    constructor;
    . intro x hx h;
      by_cases hx₂ : x = w₂;
      . subst hx₂;
        simpa using h _ r₂₃;
      . by_cases hx₃ : x = w₃ <;> simp_all [Kripke.Satisfies, hx₃];
    . existsi w₂; simpa [Kripke.Satisfies];

private lemma cwf_of_L  : F#α ⊧* (𝗟 : AxiomSet α) → ConverseWellFounded F.Rel := by
  contrapose;
  intro hCF;
  obtain ⟨X, ⟨x, _⟩, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
  apply iff_not_validOnFrame.mpr;
  use (Axioms.L (atom default));
  constructor;
  . simp;
  . use (λ w _ => w ∉ X), x;
    simp only [Kripke.Satisfies]; simp;
    constructor;
    . intro y _;
      by_cases hys : y ∈ X
      . obtain ⟨z, _, Rxz⟩ := hX₂ y hys;
        simp_all;
        use z;
      . aesop;
    . obtain ⟨y, _, _⟩ := hX₂ x (by assumption);
      use y;

private lemma L_of_trans_and_cwf : (Transitive F.Rel ∧ ConverseWellFounded F.Rel) → F#α ⊧* (𝗟 : AxiomSet α) := by
  rintro ⟨hTrans, hWF⟩;
  simp [Axioms.L];
  intro p V w;
  apply Kripke.Satisfies.imp_def.mpr;
  contrapose;
  intro h; simp [Kripke.Satisfies] at h;
  obtain ⟨x, Rwx, h⟩ := h;
  obtain ⟨m, ⟨⟨rwm, hm⟩, hm₂⟩⟩ := hWF.has_min ({ x | (F.Rel w x) ∧ ¬(Kripke.Satisfies ⟨F, V⟩ x p) }) $ by use x; tauto;
  simp [Kripke.Satisfies];
  use m;
  constructor;
  . exact rwm;
  . constructor;
    . simp [flip] at hm₂;
      intro n rmn;
      apply not_imp_not.mp $ hm₂ n (hTrans rwm rmn);
      exact rmn;
    . exact hm;

lemma axiomL_defines : ∀ {F : Kripke.Frame}, F#α ⊧* 𝗟 ↔ F ∈ TransitiveCWFFrameClass := by
  intro F;
  constructor;
  . intro h;
    constructor;
    . exact trans_of_L h;
    . exact cwf_of_L h;
  . exact L_of_trans_and_cwf;


abbrev TransitiveIrreflexiveFrameClass : FrameClass := λ F => Transitive F ∧ Irreflexive F

/-
lemma TransitiveIrreflexiveFiniteFrameClass.nonempty : TransitiveIrreflexiveFrameClass.Nonempty.{0} := by
  use PointFrame;
  simp [Transitive, Irreflexive];
-/

lemma axiomL_finite_defines : ∀ {F : FiniteFrame}, F#α ⊧* 𝗟 ↔ F ∈ TransitiveIrreflexiveFrameClassꟳ := by
  intro F;
  constructor;
  . intro h;
    obtain ⟨hTrans, hCWF⟩ := axiomL_defines.mp h;
    simp;
    use F;
    refine ⟨⟨hTrans, ?irreflexive⟩, rfl⟩;
    . intro w;
      simpa using ConverseWellFounded.iff_has_max.mp hCWF {w} (by simp);
  . simp;
    rintro FF ⟨FF_trans, FF_irrefl⟩ e p;
    have := @axiomL_defines α _ FF |>.mpr ?_;
    simp [e] at this;
    have := this p;
    apply this;
    constructor;
    . exact FF_trans;
    . apply Finite.converseWellFounded_of_trans_irrefl';
      . infer_instance;
      . assumption;
      . assumption;

instance GL_characterizable : 𝔽(𝐆𝐋 of α).Characteraizable (TransitiveIrreflexiveFrameClassꟳ) := characterizable_of_valid_axiomset (by sorry) (by sorry)

instance GL_sound : Sound 𝐆𝐋 (TransitiveIrreflexiveFrameClassꟳ#α) := sound_of_finitely_defines axiomL_finite_defines

instance : System.Consistent (𝐆𝐋 : DeductionParameter α) := consistent_of_finitely_defines.{u} axiomL_finite_defines $ by
  use PointFrame;
  simp [Transitive, Irreflexive];

end Kripke

end LO.Modal.Standard
