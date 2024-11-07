import Foundation.Vorspiel.BinaryRelations
import Foundation.Modal.Kripke.Semantics

namespace LO.Modal

namespace Kripke

open LO.Kripke
open System
open Kripke
open Formula

variable {α : Type u}

private lemma L_of_trans_and_cwf {F : Kripke.Frame} : (Transitive F.Rel ∧ ConverseWellFounded F.Rel) → F#α ⊧* 𝗟 := by
  rintro ⟨hTrans, hWF⟩;
  simp [Axioms.L];
  intro φ V w;
  apply Kripke.Satisfies.imp_def.mpr;
  contrapose;
  intro h; simp [Kripke.Satisfies] at h;
  obtain ⟨x, Rwx, h⟩ := h;
  obtain ⟨m, ⟨⟨rwm, hm⟩, hm₂⟩⟩ := hWF.has_min ({ x | (F.Rel w x) ∧ ¬(Kripke.Satisfies ⟨F, V⟩ x φ) }) $ by use x; tauto;
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

private lemma trans_of_L  [Inhabited α] {F : Kripke.Frame} : F#α ⊧* 𝗟 → Transitive F.Rel := by
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

variable [Inhabited α]

private lemma cwf_of_L {F : Kripke.Frame} : F#α ⊧* 𝗟 → ConverseWellFounded F.Rel := by
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
      . intros;
        simp_all only [not_false_eq_true];
    . obtain ⟨y, _, _⟩ := hX₂ x (by assumption);
      use y;

instance axiomL_definability : 𝔽((𝗟 : Theory α)).DefinedBy (TransitiveConverseWellFoundedFrameClass) where
  define := by
    intro F;
    constructor;
    . intro h;
      constructor;
      . exact trans_of_L h;
      . exact cwf_of_L h;
    . exact L_of_trans_and_cwf;
  nonempty := by
    use ⟨PUnit,  λ _ _ => False⟩;
    refine ⟨by tauto, ?_⟩;
    simp [Transitive, ConverseWellFounded];
    apply WellFounded.trivial_wellfounded;

instance : Sound (Hilbert.GL α) (TransitiveConverseWellFoundedFrameClass#α) := inferInstance
instance : System.Consistent (Hilbert.GL α) := inferInstance

instance axiomL_finite_definability : 𝔽ꟳ((𝗟 : Theory α)).DefinedBy (TransitiveIrreflexiveFrameClassꟳ) where
  define := by
    intro F;
    constructor;
    . rintro h;
      obtain ⟨hTrans, hCWF⟩ := axiomL_definability.define.mp h;
      refine ⟨hTrans, ?irreflexive⟩;
      intro w;
      simpa using ConverseWellFounded.iff_has_max.mp hCWF {w} (by simp);
    . rintro ⟨hTrans, hIrrefl⟩;
      apply axiomL_definability.define.mpr;
      refine ⟨hTrans, ?_⟩;
      apply Finite.converseWellFounded_of_trans_irrefl';
      . infer_instance;
      . assumption;
      . assumption;
  nonempty := by
    use ⟨PUnit,  λ _ _ => False⟩;
    refine ⟨?_, ?_⟩ <;> tauto;

instance GL_finite_sound : Sound (Hilbert.GL α) (TransitiveIrreflexiveFrameClassꟳ#α) := inferInstance

end Kripke

end LO.Modal
