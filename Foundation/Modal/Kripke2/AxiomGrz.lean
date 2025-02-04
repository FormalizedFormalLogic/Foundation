import Foundation.Vorspiel.BinaryRelations
import Foundation.Modal.Kripke2.FiniteFrame
import Foundation.Modal.Kripke2.K
import Foundation.Modal.Kripke2.AxiomGeach

namespace LO.Modal

namespace Kripke

open System
open Kripke
open Formula.Kripke
open Relation (IrreflGen)

abbrev ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass : FrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel ∧ WeaklyConverseWellFounded F.Rel }
abbrev ReflexiveTransitiveAntiSymmetricFiniteFrameClass : FiniteFrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel ∧ AntiSymmetric F.Rel }


variable {F : Kripke.Frame}

lemma validate_Grz_of_refl_trans_wcwf
  (hRefl : Reflexive F.Rel)
  (hTrans : Transitive F.Rel)
  (hWCWF : WeaklyConverseWellFounded F.Rel)
  : F ⊧ (Axioms.Grz (.atom 0)) := by
  intro V;

  let X := { x | Satisfies ⟨F, V⟩ x (□(□((.atom 0) ➝ □(.atom 0)) ➝ (.atom 0))) ∧ ¬(Satisfies ⟨F, V⟩ x (.atom 0)) };
  let Y := { x | Satisfies ⟨F, V⟩ x (□(□((.atom 0) ➝ □(.atom 0)) ➝ (.atom 0))) ∧ ¬(Satisfies ⟨F, V⟩ x (□(.atom 0))) ∧ (Satisfies ⟨F, V⟩ x (.atom 0)) };
  have : (X ∩ Y) = ∅ := by aesop;

  suffices ∀ x ∈ X ∪ Y, ∃ y ∈ X ∪ Y, (IrreflGen F.Rel) x y by
    have : (X ∪ Y) = ∅ := by
      by_contra hC;
      replace hC := Set.nonempty_iff_ne_empty.mpr hC;
      obtain ⟨z, z_sub, hz⟩ := hWCWF.has_min (X ∪ Y) hC;
      obtain ⟨x, x_sub, hx⟩ := this z z_sub;
      exact hz x x_sub hx;
    have : X = ∅ := by tauto_set;
    -- TODO: need more refactor
    have := Set.not_nonempty_iff_eq_empty.mpr this;
    have := Set.nonempty_def.not.mp this; push_neg at this;
    simp [X] at this;
    exact this;

  rintro w (⟨hw₁, hw₂⟩ | ⟨hw₁, hw₂, hw₃⟩);
  . have := hw₁ _ (by apply hRefl);
    have := not_imp_not.mpr this hw₂;
    obtain ⟨x, Rwx, hx, ⟨y, Rxy, hy⟩⟩ := by simpa [Satisfies] using this;
    use x;
    constructor;
    . right;
      refine ⟨?_, ?_, by assumption⟩;
      . intro z Rxz hz;
        exact hw₁ z (hTrans Rwx Rxz) hz;
      . simp [Satisfies];
        use y;
    . constructor;
      . sorry;
      . assumption;
  . obtain ⟨x, Rwx, hx⟩ := by simpa [Satisfies] using hw₂;
    use x;
    constructor;
    . left;
      refine ⟨?_, (by assumption)⟩;
      . intro y Rxy hy;
        exact hw₁ _ (hTrans Rwx Rxy) hy;
    . constructor;
      . sorry;
      . assumption;


lemma validate_T_Four_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) : F ⊧ □(.atom 0) ➝ ((.atom 0) ⋏ □□(.atom 0)) := by
  let ψ : Formula _ := (.atom 0) ⋏ (□(.atom 0) ➝ □□(.atom 0));
  intro V x;
  simp only [Axioms.Grz, ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models, ValidOnModel] at h;
  suffices Satisfies { toFrame := F, Val := V } x (□(.atom 0) ➝ ψ) by
    intro h₁;
    have h₂ := Satisfies.and_def.mp $ this h₁;
    apply Satisfies.and_def.mpr;
    constructor;
    . exact h₂.1;
    . exact h₂.2 h₁;
  intro h₁;
  have h₂ : Satisfies ⟨F, V⟩ x (□(.atom 0) ➝ □(□(ψ ➝ □ψ) ➝ ψ)) := by sorry; -- by soundness of K and lemmaGrz!
  have h₃ : Satisfies ⟨F, V⟩ x (□(□(ψ ➝ □ψ) ➝ ψ) ➝ ψ) := Satisfies.iff_subst_self (s := λ a => if a = 0 then ψ else a) |>.mp $ h _ _;
  exact h₃ $ h₂ $ h₁;

lemma validate_T_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) : F ⊧ (Axioms.T (.atom 0)) := by
  intro V x hx;
  exact Satisfies.and_def.mp (validate_T_Four_of_validate_Grz h V x hx) |>.1;

lemma reflexive_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) : Reflexive F := by
  apply reflexive_of_validate_AxiomT;
  simpa using validate_T_of_validate_Grz h;

lemma validate_Four_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) : F ⊧ (Axioms.Four (.atom 0))  := by
  intro V x hx;
  exact Satisfies.and_def.mp (validate_T_Four_of_validate_Grz h V x hx) |>.2;

lemma transitive_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) : Transitive F := by
  apply transitive_of_validate_AxiomFour;
  simpa using validate_Four_of_validate_Grz h;

lemma WCWF_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) : WCWF F := by
  have F_trans : Transitive F := transitive_of_validate_Grz h;
  have F_refl : Reflexive F := reflexive_of_validate_Grz h;

  revert h;
  contrapose;
  intro hWCWF;

  replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
  push_neg at hWCWF;
  obtain ⟨f, hf⟩ := dependent_choice hWCWF; clear hWCWF;
  simp only [IrreflGen, ne_eq] at hf;
  apply ValidOnFrame.not_of_exists_valuation_world;
  by_cases H : ∀ j₁ j₂, (j₁ < j₂ → f j₂ ≠ f j₁)
  . use (λ v _ => ∀ i, v ≠ f (2 * i)), (f 0);
    apply Classical.not_imp.mpr
    constructor;
    . suffices Satisfies ⟨F, _⟩ (f 0) (□(∼(.atom 0) ➝ ∼(□((.atom 0) ➝ □(.atom 0))))) by
        intro x hx;
        exact not_imp_not.mp $ this _ hx;
      suffices ∀ y, f 0 ≺ y → ∀ j, y = f (2 * j) → ∃ x, y ≺ x ∧ (∀ i, ¬x = f (2 * i)) ∧ ∃ z, x ≺ z ∧ ∃ x, z = f (2 * x) by
        simpa [Satisfies];
      rintro v h0v j rfl;
      use f (2 * j + 1);
      refine ⟨?_, ?_, f ((2 * j) + 2), ?_, ?_⟩;
      . apply hf _ |>.2;
      . intro i;
        rcases (lt_trichotomy i j) with (hij | rfl | hij);
        . apply H;
          omega;
        . apply H;
          omega;
        . apply @H _ _ ?_ |>.symm;
          omega;
      . apply hf _ |>.2;
      . use (j + 1);
        rfl;
    . simp [Satisfies];
      use 0;
  . push_neg at H;
    obtain ⟨j, k, ljk, ejk⟩ := H;
    let V : Valuation F := (λ v _ => v ≠ f j);
    use V, (f j);
    apply Classical.not_imp.mpr;
    constructor;
    . have : Satisfies ⟨F, V⟩ (f (j + 1)) (∼((.atom 0) ➝ □(.atom 0))) := by
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
      have : Satisfies ⟨F, V⟩ (f j) (□(∼(.atom 0) ➝ ∼□((.atom 0) ➝ □(.atom 0)))) := by
        simp_all [Satisfies, V];
        rintro x hx rfl;
        use f (j + 1);
        refine ⟨(hf j).2, Ne.symm $ (hf j).1, this.2⟩;
      intro x hx;
      contrapose;
      exact this _ hx;
    . simp [Satisfies, V];

instance ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass.is_defined_by_Grz
  : ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass.DefinedBy {Axioms.Grz (.atom 0)} := ⟨by
  intro F;
  constructor;
  . rintro ⟨hRefl, hTrans, hWCWF⟩;
    suffices ValidOnFrame F (Axioms.Grz (.atom 0)) by simpa;
    apply validate_Grz_of_refl_trans_wcwf <;> assumption;
  . rintro h;
    replace h : ValidOnFrame F (Axioms.Grz (.atom 0)) := by simpa using h;
    refine ⟨?_, ?_, ?_⟩;
    . exact reflexive_of_validate_Grz h;
    . exact transitive_of_validate_Grz h;
    . exact WCWF_of_validate_Grz h;
⟩

instance : ReflexiveTransitiveAntiSymmetricFiniteFrameClass.DefinedBy {Axioms.Grz (.atom 0)} := ⟨by
  intro F;
  constructor;
  . rintro ⟨hRefl, hTrans, hAntisymm⟩;
    suffices ValidOnFiniteFrame F (Axioms.Grz (.atom 0)) by simpa;
    apply validate_Grz_of_refl_trans_wcwf;
    . assumption;
    . assumption;
    . apply WCWF_of_finite_trans_antisymm;
      . exact F.world_finite;
      . assumption;
      . assumption;
  . rintro h;
    replace h : ValidOnFiniteFrame F (Axioms.Grz (.atom 0)) := by simpa using h;
    refine ⟨?_, ?_, ?_⟩;
    . exact reflexive_of_validate_Grz h;
    . exact transitive_of_validate_Grz h;
    . exact antisymm_of_WCWF $ WCWF_of_validate_Grz h;
⟩

end Kripke

end LO.Modal
