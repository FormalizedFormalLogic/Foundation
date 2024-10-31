import Foundation.Modal.Kripke.Geach

namespace LO

namespace Modal

namespace Kripke

open LO.Kripke
open System
open Kripke
open Formula (atom)
open Formula.Kripke
open Relation (IrreflGen)

variable {α : Type u}
variable {F : Kripke.Frame}

private lemma Grz_of_wcwf : (Reflexive F.Rel ∧ Transitive F.Rel ∧ WeaklyConverseWellFounded F.Rel) → F#α ⊧* 𝗚𝗿𝘇 := by
  rintro ⟨hRefl, hTrans, hWCWF⟩;
  simp [Axioms.Grz];
  intro p V;

  let X := { x | Satisfies ⟨F, V⟩ x (□(□(p ➝ □p) ➝ p)) ∧ ¬(Satisfies ⟨F, V⟩ x p) };
  let Y := { x | Satisfies ⟨F, V⟩ x (□(□(p ➝ □p) ➝ p)) ∧ ¬(Satisfies ⟨F, V⟩ x (□p)) ∧ (Satisfies ⟨F, V⟩ x p) };
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


variable [DecidableEq α]

private lemma valid_on_frame_T_and_Four_of_Grz (h : F#α ⊧* 𝗚𝗿𝘇) : F#α ⊧* ({□p ➝ (p ⋏ (□p ➝ □□p)) | (p : Formula α)}) := by
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro p V x;
  let q := p ⋏ (□p ➝ □□p);
  have h₁ : Satisfies ⟨F#α, V⟩ x (□p ➝ □(□(q ➝ □q) ➝ q)) := K_sound.sound lemma_Grz₁! (by simp) V x;
  have h₂ : Satisfies ⟨F#α, V⟩ x (□(□(q ➝ □q) ➝ q) ➝ q)  := h q V x;
  exact λ f => h₂ (h₁ f);

private lemma valid_on_frame_T_of_Grz (h : F#α ⊧* 𝗚𝗿𝘇) : F#α ⊧* 𝗧 := by
  have := valid_on_frame_T_and_Four_of_Grz h;
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro p V x hx;
  exact Satisfies.and_def.mp (this p V x hx) |>.1

private lemma valid_on_frame_Four_of_Grz (h : F#α ⊧* 𝗚𝗿𝘇) : F#α ⊧* 𝟰 := by
  have := valid_on_frame_T_and_Four_of_Grz h;
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro p V x hx;
  exact (Satisfies.and_def.mp (this p V x hx) |>.2) hx;

variable [Inhabited α]

private lemma refl_of_Grz (h : F#α ⊧* 𝗚𝗿𝘇) : Reflexive F := by
  exact axiomT_defines.define.mp $ valid_on_frame_T_of_Grz h;

private lemma trans_of_Grz (h : F#α ⊧* 𝗚𝗿𝘇) : Transitive F := by
  exact axiomFour_defines.define.mp $ valid_on_frame_Four_of_Grz h;

private lemma WCWF_of_Grz (h : F#α ⊧* 𝗚𝗿𝘇) : WCWF F := by
  have F_trans : Transitive F := trans_of_Grz h;
  have F_refl : Reflexive F := refl_of_Grz h;

  revert h;
  contrapose;
  intro hWCWF;

  replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
  push_neg at hWCWF;
  obtain ⟨f, hf⟩ := dependent_choice hWCWF; clear hWCWF;
  simp [IrreflGen] at hf;

  apply iff_not_validOnFrame.mpr;
  use (Axioms.Grz (atom default));
  constructor;
  . simp;
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
      . simp [Satisfies]; use 0;
    . push_neg at H;
      obtain ⟨j, k, ljk, ejk⟩ := H;
      let V : Valuation F α := (λ v _ => v ≠ f j);
      use (λ v _ => v ≠ f j), (f j);
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

instance axiomGrz_defineability : 𝔽((𝗚𝗿𝘇 : Theory α)).DefinedBy ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass where
  define := by
    intro F;
    constructor;
    . intro h;
      refine ⟨refl_of_Grz h, trans_of_Grz h, WCWF_of_Grz h⟩;
    . exact Grz_of_wcwf;
  nonempty := by
    use ⟨PUnit,  λ _ _ => True⟩;
    refine ⟨by tauto, by tauto, ?_⟩;
    simp [WeaklyConverseWellFounded, ConverseWellFounded, IrreflGen];
    apply WellFounded.trivial_wellfounded;

instance : Sound (𝐆𝐫𝐳 : Hilbert α) (ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass#α) := inferInstance
instance : System.Consistent (𝐆𝐫𝐳 : Hilbert α) := inferInstance

instance axiomGrz_finite_defines : 𝔽ꟳ((𝗚𝗿𝘇 : Theory α)).DefinedBy ReflexiveTransitiveAntisymmetricFrameClassꟳ where
  define := by
    intro F;
    constructor;
    . rintro h;
      obtain ⟨F_refl, F_trans, hCWF⟩ := axiomGrz_defineability.define.mp h;
      refine ⟨F_refl, F_trans, antisymm_of_WCWF hCWF⟩;
    . rintro ⟨F_Refl, F_trans, F_antisymm⟩;
      apply axiomGrz_defineability.define.mpr;
      refine ⟨F_Refl, F_trans, ?_⟩;
      apply WCWF_of_finite_trans_antisymm;
      . exact F.World_finite;
      . assumption;
      . assumption;
  nonempty := by
    use ⟨PUnit, λ _ _ => True⟩;
    refine ⟨?_, ?_, ?_⟩ <;> tauto;

instance : Sound (𝐆𝐫𝐳 : Hilbert α) (ReflexiveTransitiveAntisymmetricFrameClassꟳ#α) := inferInstance

end Kripke

end LO.Modal
