import Foundation.Modal.Kripke.Geach.Systems

namespace LO

namespace Modal

namespace Kripke

open System
open Kripke
open Formula (atom)
open Formula.Kripke
open Relation (IrreflGen)

abbrev ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass : FrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel ∧ WeaklyConverseWellFounded F.Rel }
abbrev ReflexiveTransitiveAntisymmetricFiniteFrameClass : FiniteFrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel ∧ Antisymmetric F.Rel }

variable {F : Kripke.Frame}

lemma Grz_of_WCWF : (Reflexive F.Rel ∧ Transitive F.Rel ∧ WeaklyConverseWellFounded F.Rel) → F ⊧* 𝗚𝗿𝘇 := by
  rintro ⟨hRefl, hTrans, hWCWF⟩;
  simp [Axioms.Grz];
  intro φ V;

  let X := { x | Satisfies ⟨F, V⟩ x (□(□(φ ➝ □φ) ➝ φ)) ∧ ¬(Satisfies ⟨F, V⟩ x φ) };
  let Y := { x | Satisfies ⟨F, V⟩ x (□(□(φ ➝ □φ) ➝ φ)) ∧ ¬(Satisfies ⟨F, V⟩ x (□φ)) ∧ (Satisfies ⟨F, V⟩ x φ) };
  have : (X ∩ Y) = ∅ := by aesop;

  suffices ∀ x ∈ X ∪ Y, ∃ y ∈ X ∪ Y, (IrreflGen F.Rel) x y by
    have : (X ∪ Y) = ∅ := by
      by_contra hC;
      replace hC := Set.nonempty_iff_ne_empty.mpr hC;
      obtain ⟨z, z_sub, hz⟩ := hWCWF.has_min (X ∪ Y) hC;
      obtain ⟨x, x_sub, hx⟩ := this z z_sub;
      exact hz x x_sub hx;
    have : X = ∅ := by aesop;
    -- TODO: need more refactor
    have := Set.not_nonempty_iff_eq_empty.mpr this;
    have := Set.nonempty_def.not.mp this; push_neg at this;
    simp [X] at this;
    exact this;

  intro w hw;
  rcases hw with (⟨hw₁, hw₂⟩ | ⟨hw₁, hw₂, hw₃⟩);
  . have := hw₁ _ (by apply hRefl);
    have := not_imp_not.mpr this hw₂;
    simp [Satisfies] at this;
    obtain ⟨x, Rwx, hx, hbx⟩ := this;
    use x;
    constructor;
    . right;
      refine ⟨?_, (by simp [Satisfies, hbx]), (by assumption)⟩;
      intro y Rxy hy;
      exact hw₁ _ (hTrans Rwx Rxy) hy;
    . constructor;
      . aesop;
      . exact Rwx;
  . simp [Satisfies] at hw₂;
    obtain ⟨x, Rwx, hx⟩ := hw₂;
    use x;
    constructor;
    . left;
      refine ⟨?_, (by assumption)⟩;
      intro y Rxy hy;
      exact hw₁ _ (hTrans Rwx Rxy) hy;
    . constructor;
      . aesop;
      . exact Rwx;


lemma valid_on_frame_T_and_Four_of_Grz (h : F ⊧* 𝗚𝗿𝘇) : F ⊧* ({□φ ➝ (φ ⋏ (□φ ➝ □□φ)) | (φ : Formula ℕ)}) := by
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro φ V x;
  let ψ := φ ⋏ (□φ ➝ □□φ);
  have h₁ : Satisfies ⟨F, V⟩ x (□φ ➝ □(□(ψ ➝ □ψ) ➝ ψ)) := Hilbert.K.Kripke.sound.sound lemma_Grz₁! (by simp) V x;
  have h₂ : Satisfies ⟨F, V⟩ x (□(□(ψ ➝ □ψ) ➝ ψ) ➝ ψ)  := h ψ V x;
  exact λ f => h₂ (h₁ f);

lemma valid_on_frame_T_of_Grz (h : F ⊧* 𝗚𝗿𝘇) : F ⊧* 𝗧 := by
  have := valid_on_frame_T_and_Four_of_Grz h;
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro φ V x hx;
  exact Satisfies.and_def.mp (this φ V x hx) |>.1

lemma valid_on_frame_Four_of_Grz (h : F ⊧* 𝗚𝗿𝘇) : F ⊧* 𝟰 := by
  have := valid_on_frame_T_and_Four_of_Grz h;
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro φ V x hx;
  exact (Satisfies.and_def.mp (this φ V x hx) |>.2) hx;

lemma refl_of_Grz (h : F ⊧* 𝗚𝗿𝘇) : Reflexive F := by
  apply ReflexiveFrameClass.isDefinedBy F |>.mpr;
  apply valid_on_frame_T_of_Grz h;

lemma trans_of_Grz (h : F ⊧* 𝗚𝗿𝘇) : Transitive F := by
  apply TransitiveFrameClass.isDefinedBy F |>.mpr;
  apply valid_on_frame_Four_of_Grz h;

lemma WCWF_of_Grz (h : F ⊧* 𝗚𝗿𝘇) : WCWF F := by
  have F_trans : Transitive F := trans_of_Grz h;
  have F_refl : Reflexive F := refl_of_Grz h;

  revert h;
  contrapose;
  intro hWCWF;

  replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
  push_neg at hWCWF;
  obtain ⟨f, hf⟩ := dependent_choice hWCWF; clear hWCWF;
  simp [IrreflGen] at hf;

  simp [Semantics.Realize, ValidOnFrame, ValidOnModel];
  use (atom default);
  . by_cases H : ∀ j₁ j₂, (j₁ < j₂ → f j₂ ≠ f j₁)
    . use (λ v _ => ∀ i, v ≠ f (2 * i)), (f 0);
      apply Classical.not_imp.mpr
      constructor;
      . suffices Satisfies ⟨F, _⟩ (f 0) (□(∼(atom default) ➝ ∼(□(atom default ➝ □atom default)))) by
          intro x hx;
          exact not_imp_not.mp $ this _ hx;
        simp [Satisfies];
        rintro v h0v j rfl;
        use f (2 * j + 1);
        refine ⟨?_, ?_, f ((2 * j) + 2), ?_, ?_⟩;
        . apply hf _ |>.2;
        . intro i;
          rcases (lt_trichotomy i j) with (hij | rfl | hij);
          . apply H; omega;
          . apply H; omega;
          . apply @H _ _ ?_ |>.symm; omega;
        . apply hf _ |>.2;
        . use (j + 1); rfl;
      . simp [Satisfies];
        use 0;
    . push_neg at H;
      obtain ⟨j, k, ljk, ejk⟩ := H;
      let V : Valuation F := (λ v _ => v ≠ f j);
      use V, (f j);
      apply Classical.not_imp.mpr;
      constructor;
      . have : Satisfies ⟨F, V⟩ (f (j + 1)) (∼((atom default) ➝ □(atom default))) := by
          simp_all [Satisfies, V];
          constructor;
          . exact Ne.symm $ (hf j).1;
          . rw [←ejk];
            have H : ∀ {x y : ℕ}, x < y → F.Rel (f x) (f y) := by
              intro x y hxy;
              induction hxy with
              | refl => exact (hf x).2;
              | step _ ih => exact F_trans ih (hf _).2;
            by_cases h : j + 1 = k;
            . subst_vars
              apply F_refl;
            . have : j + 1 < k := by omega;
              exact H this;
        have : Satisfies ⟨F, V⟩ (f j) (□(∼(atom default) ➝ ∼□((atom default) ➝ □atom default))) := by
          simp_all [Satisfies, V];
          rintro x hx rfl;
          use f (j + 1);
          refine ⟨(hf j).2, Ne.symm $ (hf j).1, this.2⟩;
        intro x hx;
        contrapose;
        exact this _ hx;
      . simp [Satisfies, V];

lemma ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass.is_defined_by_Grz : ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass.DefinedBy 𝗚𝗿𝘇 := by
  intro F;
  constructor;
  . rintro ⟨hRefl, hTrans, hWCWF⟩;
    apply Grz_of_WCWF;
    exact ⟨hRefl, hTrans, hWCWF⟩;
  . rintro h;
    refine ⟨refl_of_Grz h, trans_of_Grz h, WCWF_of_Grz h⟩;

lemma ReflexiveTransitiveAntisymmetricFiniteFrameClass.is_defined_by_Grz : ReflexiveTransitiveAntisymmetricFiniteFrameClass.DefinedBy 𝗚𝗿𝘇 := by
  intro F;
  constructor;
  . rintro ⟨hRefl, hTrans, hAntisymm⟩;
    apply Grz_of_WCWF;
    refine ⟨hRefl, hTrans, ?_⟩;
    apply WCWF_of_finite_trans_antisymm;
    . exact F.world_finite;
    . assumption;
    . assumption;
  . rintro h;
    refine ⟨refl_of_Grz h, trans_of_Grz h, antisymm_of_WCWF $ WCWF_of_Grz h⟩;

end Kripke


namespace Hilbert

open Modal.Kripke
open Hilbert.Kripke

instance Grz.Kripke.sound : Sound (Hilbert.Grz ℕ) (ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass) :=
  instSound_of_frameClass_definedBy ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass.is_defined_by_Grz rfl

instance Grz.Kripke.finite_sound : Sound (Hilbert.Grz ℕ) (ReflexiveTransitiveAntisymmetricFiniteFrameClass) :=
  instSound_of_finiteFrameClass_definedBy ReflexiveTransitiveAntisymmetricFiniteFrameClass.is_defined_by_Grz rfl

instance Grz.consistent : System.Consistent (Hilbert.Grz ℕ) := Kripke.instConsistent_of_nonempty_finiteFrameclass (FC := ReflexiveTransitiveAntisymmetricFiniteFrameClass) $ by
  use reflexivePointFrame;
  simp [Transitive, Reflexive, Antisymmetric];

end Hilbert

end LO.Modal
