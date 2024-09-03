import Logic.Modal.Standard.Kripke.Geach

namespace LO.Modal.Standard

namespace Kripke

open LO.Kripke
open System
open Kripke
open Formula (atom)
open Formula.Kripke
open Relation (IrreflGen)

variable {α : Type u} [Inhabited α] [DecidableEq α]
variable {F : Kripke.Frame}

lemma axiomT_defines : ∀ {F : Frame}, (F#α ⊧* 𝗧 ↔ F ∈ ReflexiveFrameClass) := by
  intro F;
  have := @axiomGeach_defines (α := α) _ (t := ⟨0, 0, 1, 0⟩) (F := F);
  simp [AxiomSet.Geach.T_def, GeachConfluentFrameClass, GeachConfluent] at this;
  simp [Semantics.RealizeSet];
  constructor;
  . intro h x; exact this.mp h;
  . intro h; exact this.mpr (by apply h);

lemma axiomFour_defines : ∀ {F : Frame}, (F#α ⊧* 𝟰 ↔ F ∈ TransitiveFrameClass) := by
  intro F;
  have := @axiomGeach_defines (α := α) _ (t := ⟨0, 2, 1, 0⟩) (F := F);
  simp [AxiomSet.Geach.Four_def, GeachConfluentFrameClass, GeachConfluent] at this;
  simp [Semantics.RealizeSet];
  constructor;
  . intro h x y z Rxy Ryz;
    exact this.mp (by assumption) rfl _ Rxy Ryz;
  . intro h;
    apply this.mpr;
    rintro x _ z rfl y Rxy Ryz;
    exact h Rxy Ryz;

private lemma valid_on_frame_T_and_Four_of_Grz (h : F#α ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : F#α ⊧* ({□p ⟶ (p ⋏ (□p ⟶ □□p)) | (p : Formula α)}) := by
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro p V x;
  let q := p ⋏ (□p ⟶ □□p);
  have h₁ : Satisfies ⟨F#α, V⟩ x (□p ⟶ □(□(q ⟶ □q) ⟶ q)) := K_sound.sound lemma_Grz₁! (by simp) V x;
  have h₂ : Satisfies ⟨F#α, V⟩ x (□(□(q ⟶ □q) ⟶ q) ⟶ q)  := h q V x;
  exact λ f => h₂ (h₁ f);

private lemma valid_on_frame_T_of_Grz (h : F#α ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : F#α ⊧* (𝗧 : AxiomSet α) := by
  have := valid_on_frame_T_and_Four_of_Grz h;
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro p V x hx;
  exact Satisfies.and_def.mp (this p V x hx) |>.1

private lemma valid_on_frame_Four_of_Grz (h : F#α ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : F#α ⊧* (𝟰 : AxiomSet α) := by
  have := valid_on_frame_T_and_Four_of_Grz h;
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro p V x hx;
  exact (Satisfies.and_def.mp (this p V x hx) |>.2) hx;

private lemma refl_of_Grz (h : F#α ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : Reflexive F := by
  exact axiomT_defines.mp $ (valid_on_frame_T_of_Grz h);

private lemma trans_of_Grz (h : F#α ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : Transitive F := by
  exact axiomFour_defines.mp $ (valid_on_frame_Four_of_Grz h);

private lemma WCWF_of_Grz (h : F#α ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : WCWF F := by
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
      . suffices Satisfies ⟨F, _⟩ (f 0) (□(~(atom default) ⟶ ~(□(atom default ⟶ □atom default)))) by
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
      . have : Satisfies ⟨F, V⟩ (f (j + 1)) (~((atom default) ⟶ □(atom default))) := by
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
        have : Satisfies ⟨F, V⟩ (f j) (□(~(atom default) ⟶ ~□((atom default) ⟶ □atom default))) := by
          simp_all [Satisfies, V];
          rintro x hx rfl;
          use f (j + 1);
          refine ⟨(hf j).2, Ne.symm $ (hf j).1, this.2⟩;
        intro x hx;
        contrapose;
        exact this _ hx;
      . simp [Satisfies, V];

private lemma Grz_of_wcwf : (Reflexive F.Rel ∧ Transitive F.Rel ∧ WeaklyConverseWellFounded F.Rel) → F#α ⊧* (𝗚𝗿𝘇 : AxiomSet α) := by
  rintro ⟨hRefl, hTrans, hWCWF⟩;
  simp [Axioms.Grz];
  intro p V;

  let X := { x | Satisfies ⟨F, V⟩ x (□(□(p ⟶ □p) ⟶ p)) ∧ ¬(Satisfies ⟨F, V⟩ x p) };
  let Y := { x | Satisfies ⟨F, V⟩ x (□(□(p ⟶ □p) ⟶ p)) ∧ ¬(Satisfies ⟨F, V⟩ x (□p)) ∧ (Satisfies ⟨F, V⟩ x p) };
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

abbrev ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass : FrameClass := λ F => Reflexive F.Rel ∧ Transitive F ∧ WeaklyConverseWellFounded F
lemma axiomGrz_defines : AxiomSet.DefinesKripkeFrameClass (α := α) 𝗚𝗿𝘇 (ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass) := by
  intro F;
  constructor;
  . intro h; refine ⟨refl_of_Grz h, trans_of_Grz h, wcwf_of_Grz h⟩;
  . exact Grz_of_wcwf;


abbrev ReflexiveTransitiveAntisymmetricFrameClass : FrameClass := λ F => Reflexive F.Rel ∧ Transitive F ∧ Antisymmetric F
lemma axiomGrz_finite_defines : AxiomSet.FinitelyDefinesKripkeFrameClass (α := α) 𝗚𝗿𝘇 ReflexiveTransitiveAntisymmetricFrameClass := by
  intro F;
  constructor;
  . intro h;
    obtain ⟨hRefl, hTrans, hCWF⟩ := axiomGrz_defines.mp h;
    refine ⟨hRefl, hTrans, antisymm_of_WCWF hCWF⟩;
  . intro d;
    have ⟨hRefl, hTrans, hAsymm⟩ := d;
    apply axiomGrz_defines.mpr;
    refine ⟨hRefl, hTrans, ?_⟩;
    apply WCWF_of_antisymm_trans;
    . exact F.World_finite;
    . assumption;
    . assumption;

instance Grz_sound : Sound (𝐆𝐫𝐳 : DeductionParameter α) ReflexiveTransitiveAntisymmetricFrameClassꟳ# := sound_of_finitely_defines axiomGrz_finite_defines

instance : System.Consistent (𝐆𝐫𝐳 : DeductionParameter α) := consistent_of_finitely_defines.{u} axiomGrz_finite_defines $ by
  use terminalFrame; refine ⟨?_, ?_, ?_⟩ <;> simp [Reflexive, Transitive, Antisymmetric];

end Kripke

end LO.Modal.Standard
