import Logic.Modal.Standard.Kripke.Geach

def irreflexivize (R : α → α → Prop) := λ x y => x ≠ y ∧ R x y
postfix:max "⁻ʳ" => irreflexivize

abbrev WeaklyConverseWellFounded (R : α → α → Prop) := ConverseWellFounded R⁻ʳ

-- TODO: move?
lemma dependent_choice
  {R : α → α → Prop} (h : ∃ s : Set α, s.Nonempty ∧ ∀ a ∈ s, ∃ b ∈ s, R a b)
  : ∃ f : ℕ → α, ∀ x, R (f x) (f (x + 1))
  := by
  obtain ⟨s, ⟨x, hx⟩, h'⟩ := h;
  choose! f hfs hR using h';
  use fun n ↦ f^[n] x;
  intro n;
  simp only [Function.iterate_succ'];
  refine hR (f^[n] x) ?a;
  induction n with
  | zero => simpa;
  | succ n ih => simp only [Function.iterate_succ']; apply hfs _ ih;

lemma antisymm_of_WCWF : WeaklyConverseWellFounded R → Antisymmetric R := by
  contrapose;
  simp [Antisymmetric];
  intro x y Rxy Ryz hxy;
  apply ConverseWellFounded.iff_has_max.not.mpr;
  push_neg;
  use {x, y};
  constructor;
  . simp;
  . intro z hz;
    by_cases z = x;
    . use y; simp_all [irreflexivize];
    . use x; simp_all [irreflexivize];

-- TODO: move?
lemma Finite.exists_ne_map_eq_of_infinite_lt {α β} [LinearOrder α] [Infinite α] [Finite β] (f : α → β)
  : ∃ x y : α, (x < y) ∧ f x = f y
  := by
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f;
    rcases lt_trichotomy i j with (hij | _ | hij);
    . use i, j;
    . contradiction;
    . use j, i; simp [hij, e];

lemma WCWF_of_antisymm_trans
  {R : α → α → Prop}
  (hFin : Finite α) (R_trans : Transitive R)
  : Antisymmetric R → WeaklyConverseWellFounded R := by
  contrapose;
  intro hWCWF;
  replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
  push_neg at hWCWF;
  obtain ⟨f, hf⟩ := dependent_choice hWCWF; clear hWCWF;
  simp [irreflexivize] at hf;

  simp [Antisymmetric];
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite_lt f;
  use (f i), (f (i + 1));
  have ⟨hi₁, hi₂⟩ := hf i;
  refine ⟨(by assumption), ?_, (by assumption)⟩;

  have : i + 1 < j := lt_iff_le_and_ne.mpr ⟨by omega, by aesop⟩;
  have H : ∀ i j, i < j → R (f i) (f j) := by
    intro i j hij
    induction hij with
    | refl => exact hf i |>.2;
    | step _ ih => exact R_trans ih $ hf _ |>.2;
  have := H (i + 1) j this;
  simpa [e];

namespace LO.Modal.Standard

namespace Kripke

open System
open Kripke
open Formula (atom)
open Formula.Kripke

abbrev ConnectedFrameClass : FrameClass := { F | Connected F }

variable {α : Type u} [Inhabited α] [DecidableEq α]
variable {F : Kripke.Frame}

lemma axiomT_defines : AxiomSet.DefinesKripkeFrameClass (α := α) 𝗧 (ReflexiveFrameClass) := by
  have := @axiomGeach_defines (α := α) _ (t := ⟨0, 0, 1, 0⟩);
  simp [AxiomSet.Geach.T_def, GeachConfluentFrameClass] at this;
  apply this;

lemma axiomFour_defines : AxiomSet.DefinesKripkeFrameClass (α := α) 𝟰 (TransitiveFrameClass) := by
  have := @axiomGeach_defines (α := α) _ (t := ⟨0, 2, 1, 0⟩);
  simp [AxiomSet.Geach.Four_def, GeachConfluentFrameClass] at this;
  apply this;


private lemma valid_on_frame_T_and_Four_of_Grz (h : F# ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : F# ⊧* ({□p ⟶ (p ⋏ (□p ⟶ □□p)) | (p : Formula α)}) := by
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro p V x;
  let q := p ⋏ (□p ⟶ □□p);
  have h₁ : Satisfies ⟨F#, V⟩ x (□p ⟶ □(□(q ⟶ □q) ⟶ q)) := K_sound.sound lemma_Grz₁! (by simp) V x;
  have h₂ : Satisfies ⟨F#, V⟩ x (□(□(q ⟶ □q) ⟶ q) ⟶ q)  := h q V x;
  exact λ f => h₂ (h₁ f);

private lemma valid_on_frame_T_of_Grz (h : F# ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : F# ⊧* (𝗧 : AxiomSet α) := by
  have := valid_on_frame_T_and_Four_of_Grz h;
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro p V x hx;
  exact this p V x hx |>.1;

private lemma valid_on_frame_Four_of_Grz (h : F# ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : F# ⊧* (𝟰 : AxiomSet α) := by
  have := valid_on_frame_T_and_Four_of_Grz h;
  simp_all [ValidOnFrame, ValidOnModel, Axioms.T, Axioms.Grz];
  intro p V x hx;
  exact (this p V x hx |>.2) hx;

private lemma refl_of_Grz (h : F# ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : Reflexive F := by
  exact axiomT_defines.mp $ (valid_on_frame_T_of_Grz h);

private lemma trans_of_Grz (h : F# ⊧* (𝗚𝗿𝘇 : AxiomSet α)) : Transitive F := by
  exact axiomFour_defines.mp $ (valid_on_frame_Four_of_Grz h);

open Classical in
private lemma wcwf_of_Grz : F# ⊧* (𝗚𝗿𝘇 : AxiomSet α) → WeaklyConverseWellFounded F := by
  intro h;
  have : Transitive F := trans_of_Grz h;
  have : Reflexive F := refl_of_Grz h;
  revert h;

  contrapose;
  intro hWCWF;

  replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
  push_neg at hWCWF;
  obtain ⟨f, hf⟩ := dependent_choice hWCWF; clear hWCWF;
  simp [irreflexivize] at hf;

  apply iff_not_validOnFrame.mpr;
  use (Axioms.Grz (atom default));
  constructor;
  . simp;
  . by_cases H : ∀ j₁ j₂, (j₁ < j₂ → f j₁ ≠ f j₂)
    . let V : Valuation F α := (λ v _ => ∀ i, v ≠ f (2 * i));
      use V, (f 0);
      apply Classical.not_imp.mpr
      constructor;
      . sorry;
      . simp [Satisfies, V]; use 0;
    . push_neg at H;
      obtain ⟨j₁, j₂, ljk, ejk⟩ := H;
      let V : Valuation F α := (λ v _ => v ≠ f j₁);
      use V, (f j₁);
      apply Classical.not_imp.mpr;
      constructor;
      . suffices Satisfies ⟨F, V⟩ (f j₁) (□(~(atom default) ⟶ ~(□(atom default ⟶ □atom default)))) by
          intro x hx;
          exact not_imp_not.mp $ this hx;
        suffices H : Satisfies ⟨F, V⟩ (f (j₁ + 1)) (~(atom default ⟶ □atom default)) by
          sorry;
        simp [Satisfies, V];
        constructor;
        . have := @hf j₁ |>.1; aesop;
        . sorry;
      . simp [Satisfies, V];

private lemma Grz_of_wcwf : (Reflexive F.Rel ∧ Transitive F.Rel ∧ WeaklyConverseWellFounded F.Rel) → F# ⊧* (𝗚𝗿𝘇 : AxiomSet α) := by
  rintro ⟨hRefl, hTrans, hWCWF⟩;
  simp [Axioms.Grz];
  intro p V;

  let X := { x | Satisfies ⟨F, V⟩ x (□(□(p ⟶ □p) ⟶ p)) ∧ ¬(Satisfies ⟨F, V⟩ x p) };
  let Y := { x | Satisfies ⟨F, V⟩ x (□(□(p ⟶ □p) ⟶ p)) ∧ ¬(Satisfies ⟨F, V⟩ x (□p)) ∧ (Satisfies ⟨F, V⟩ x p) };
  have : (X ∩ Y) = ∅ := by aesop;

  suffices ∀ x ∈ X ∪ Y, ∃ y ∈ X ∪ Y, F.Rel⁻ʳ x y by
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
  . have := hw₁ (by apply hRefl);
    have := not_imp_not.mpr this hw₂;
    simp [Satisfies] at this;
    obtain ⟨x, Rwx, hx, hbx⟩ := this;
    use x;
    constructor;
    . right;
      refine ⟨?_, (by simp [Satisfies, hbx]), (by assumption)⟩;
      intro y Rxy hy;
      exact hw₁ (hTrans Rwx Rxy) hy;
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
      exact hw₁ (hTrans Rwx Rxy) hy;
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
