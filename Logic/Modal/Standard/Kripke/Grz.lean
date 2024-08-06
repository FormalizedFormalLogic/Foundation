import Logic.Modal.Standard.Kripke.Geach

def irreflexivize (R : α → α → Prop) := λ x y => x ≠ y ∧ R x y
postfix:max "⁻ʳ" => irreflexivize

abbrev WeaklyConverseWellFounded (R : α → α → Prop) := ConverseWellFounded R⁻ʳ


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


private lemma wcwf_of_Grz : F# ⊧* (𝗚𝗿𝘇 : AxiomSet α) → WeaklyConverseWellFounded F := by
  contrapose;
  intro hWCWF;

  replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
  push_neg at hWCWF;
  obtain ⟨X, ⟨x, hx⟩, hX⟩ := hWCWF;

  apply iff_not_validOnFrame.mpr;
  use (Axioms.Grz (atom default));
  constructor;
  . simp;
  . sorry;
    /-
    use (λ w _ => w ∉ X), x;
    simp only [Formula.Kripke.Satisfies]; push_neg;
    constructor;
    . intro y Rxy h;
      have := @h x;
    . assumption;
    -/

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
alias GrzFrameClass := ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass

lemma axiomGrz_defines : AxiomSet.DefinesKripkeFrameClass (α := α) 𝗚𝗿𝘇 (GrzFrameClass) := by
  intro F;
  constructor;
  . intro h; refine ⟨refl_of_Grz h, trans_of_Grz h, wcwf_of_Grz h⟩;
  . exact Grz_of_wcwf;

end Kripke

end LO.Modal.Standard
