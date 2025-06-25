import Foundation.Modal.Modality.Basic
import Foundation.Modal.Kripke.Logic.S4

namespace LO.Modal


section

open Modality Modalities

variable {L : Logic} {M : Modalities} {n : ℕ} {n : ℕ}

structure ModalityReducing (L : Logic) (n : ℕ) (M : Modalities) where
  M_size : ∀ m ∈ M, m.size ≤ n
  M_mem  : ∀ m ∈ Modalities.allOfSize n, ∃ m' ∈ M, m ⤳[L] m'

abbrev ModalReducible (L : Logic) (n : ℕ) (M : Modalities) := ∀ m ∈ Modalities.allOfSize n, ∃ m' ∈ M, m ⤳[L] m'

lemma ModalReducible.size_max {M_ne} : ModalReducible L (M.max_size M_ne) M → ModalReducible L (M.max_size M_ne + 1) M := by
  generalize hn : M.max_size _ = n;
  intro hM m hm;
  obtain ⟨m', hm', (rfl | rfl | rfl)⟩ := allOfSize.eq_succ hm;
  . sorry;
  . sorry;
  . sorry;

end


namespace Logic.S4

variable {m m₁ m₂ : Modality}

open Entailment
open Modality
open Formula
open Kripke

instance box_box_eq_box : (□□) ≅[Logic.S4] (□)  := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0);
    simp;
  . infer_instance;

instance dia_dia_eq_dia : (◇◇) ≅[Logic.S4] (◇)  := by
  apply iff_equivalence_bi_translate.mpr;
  constructor <;>
  . apply translation_of_axiomInstance (a := 0);
    simp;

instance dia_box_dia_to_dia : (◇□◇) ⤳[Logic.S4] (◇) := by
  constructor;
  intro a;
  suffices Kripke.FrameClass.S4 ⊧ ◇□◇(atom a) ➝ ◇(atom a) by
    simpa [S4.Kripke.preorder];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  intro V x hx;
  obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp hx;
  have := hy y F.refl;
  obtain ⟨z, Ryz, hz⟩ := Satisfies.dia_def.mp this;

  apply Satisfies.dia_def.mpr;
  use z;
  constructor;
  . exact F.trans Rxy Ryz;
  . assumption;

instance box_dia_box_dia_eq_box_dia : (□◇□◇) ≅[Logic.S4] (□◇) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . constructor;
    intro a;
    apply imply_box_distribute'!;
    apply dia_box_dia_to_dia.translate;
  . constructor;
    intro a;
    suffices Kripke.FrameClass.S4 ⊧ □◇(atom a) ➝ □◇□◇(atom a) by
      simpa [S4.Kripke.preorder];
    intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    intro V x hx y Rxy;
    apply Satisfies.dia_def.mpr;
    use y;
    constructor;
    . simp;
    . intro z Ryz;
      apply hx;
      apply F.trans Rxy Ryz;

instance dia_box_dia_box_eq_dia_box : (◇□◇□) ≅[Logic.S4] (◇□) := by
  constructor;
  intro a;
  suffices Kripke.FrameClass.S4 ⊧ (◇□◇□(atom a)) ⭤ (◇□(atom a)) by
    simpa [S4.Kripke.preorder];
  intro F hF V x;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply Satisfies.iff_def.mpr;
  constructor;
  . intro h;
    obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp h;
    have := hy y F.refl;
    obtain ⟨z, Rxz, hz⟩ := Satisfies.dia_def.mp this;
    apply Satisfies.dia_def.mpr;
    use z;
    constructor;
    . apply F.trans Rxy Rxz;
    . assumption;
  . intro h;
    obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp h;
    apply Satisfies.dia_def.mpr;
    use y;
    constructor;
    . simpa;
    . intro z Ryz;
      apply Satisfies.dia_def.mpr;
      use z;
      constructor;
      . simp;
      . intro w Rzw;
        apply hy;
        exact F.trans Ryz Rzw;

macro "reduce_to " t:term : tactic => `(tactic| focus
  existsi $t;
  constructor;
  . simp;
  . infer_instance;
)



abbrev modalities : Modalities := {-, ∼, □, ◇, ∼□, ∼◇, □◇, ◇□, ∼◇□, ◇□◇, ∼□◇}

section

set_option linter.style.multiGoal false

lemma modal_reducible_0 : ModalReducible Logic.S4 0 Logic.S4.modalities := by
  simp [ModalReducible];
  tauto;

lemma modal_reducible_1 : ModalReducible Logic.S4 1 Logic.S4.modalities := by
  intro m hm;
  simp only [Modalities.allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union, Finset.mem_singleton] at hm;
  rcases hm with rfl | rfl | rfl;
  . reduce_to (∼);
  . reduce_to (□);
  . reduce_to (◇);

instance : (∼∼) ≅[Logic.S4] (-)  := inferInstance
instance : (∼□) ≅[Logic.S4] (∼□) := inferInstance
instance : (∼◇) ≅[Logic.S4] (∼◇) := inferInstance
instance : (□∼) ≅[Logic.S4] (∼◇) := inferInstance
instance : (□□) ≅[Logic.S4] (□)  := inferInstance
instance : (□◇) ≅[Logic.S4] (□◇) := inferInstance
instance : (◇∼) ≅[Logic.S4] (∼□) := inferInstance
instance : (◇□) ≅[Logic.S4] (◇□) := inferInstance
instance : (◇◇) ≅[Logic.S4] (◇)  := inferInstance

instance : (◇◇m) ≅[Logic.S4] (◇m)  := equivalence_expand_right (◇◇) (◇) m
instance : (∼∼m) ≅[Logic.S4] (m)   := equivalence_expand_right (∼∼) (-) m


lemma modal_reducible_2 : ∀ m ∈ Modalities.allOfSize 2, ∃ m' ∈ Logic.S4.modalities, m ⤳[Logic.S4] m' := by
  intro m hm;
  simp only [
    Modalities.allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union,
    Finset.mem_image, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left
  ] at hm;
  rcases hm with (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl);
  . reduce_to (-);
  . reduce_to (∼□);
  . reduce_to (∼◇);
  . reduce_to (∼◇);
  . reduce_to (□);
  . reduce_to (□◇);
  . reduce_to (∼□);
  . reduce_to (◇□);
  . reduce_to (◇);

instance : (∼∼∼) ≅[Logic.S4] (∼)   := equivalence_expand_right (∼∼) (-) (∼)
instance : (∼∼□) ≅[Logic.S4] (□)   := equivalence_expand_right (∼∼) (-) (□)
instance : (∼∼◇) ≅[Logic.S4] (◇)   := equivalence_expand_right (∼∼) (-) (◇)
instance : (∼□∼) ≅[Logic.S4] (◇)   := by trans (∼∼◇); exact equivalence_expand_left (□∼) (∼◇) (∼); exact equivalence_expand_right (∼∼) (-) (◇)
instance : (∼□□) ≅[Logic.S4] (∼□)  := equivalence_expand_left (□□) (□) (∼)
instance : (∼□◇) ≅[Logic.S4] (∼□◇) := inferInstance
instance : (∼◇∼) ≅[Logic.S4] (□)   := by trans (∼∼□); exact equivalence_expand_left (◇∼) (∼□) (∼); exact equivalence_expand_right (∼∼) (-) (□)
instance : (∼◇□) ≅[Logic.S4] (∼◇□) := inferInstance
instance : (∼◇◇) ≅[Logic.S4] (∼◇)  := equivalence_expand_left (◇◇) (◇) (∼)
/-
instance : (□∼∼) ⤳[Logic.S4] (-)   := translation_expand_left (∼∼) (-) (□)
instance : (□∼□) ⤳[Logic.S4] (∼□)  := inferInstance
instance : (□∼◇) ⤳[Logic.S4] (∼◇)  := inferInstance
instance : (□□∼) ≅[Logic.S4] (∼◇)  := by trans (□∼) <;> infer_instance
instance : (□□□) ≅[Logic.S4] (□)   := by trans (□□); exact equivalence_expand_right (□□) (□) (□); infer_instance;
instance : (□□◇) ≅[Logic.S4] (□◇)  := equivalence_expand_right (□□) (□) (◇)
instance : (□◇∼) ⤳[Logic.S4] (∼□)  := by trans (◇∼) <;> infer_instance
instance : (□◇□) ⤳[Logic.S4] (◇□)  := by trans (◇□) <;> infer_instance
instance : (□◇◇) ⤳[Logic.S4] (◇)   := by trans (◇◇) <;> infer_instance
-/
instance : (◇∼∼) ≅[Logic.S4] (◇)   := by trans (∼□∼); exact equivalence_expand_right (◇∼) (∼□) (∼); infer_instance;
instance : (◇∼□) ≅[Logic.S4] (∼□)  := by trans (∼□□); exact equivalence_expand_right (◇∼) (∼□) (□); exact equivalence_expand_left (□□) (□) (∼)
instance : (◇∼◇) ≅[Logic.S4] (∼□◇) := equivalence_expand_right (◇∼) (∼□) (◇)
instance : (◇□∼) ≅[Logic.S4] (∼□◇) := by trans (◇∼◇); exact equivalence_expand_left (□∼) (∼◇) (◇); infer_instance;
instance : (◇□□) ≅[Logic.S4] (◇□)  := equivalence_expand_left (□□) (□) (◇)
instance : (◇□◇) ≅[Logic.S4] (◇□◇) := inferInstance
instance : (◇◇∼) ≅[Logic.S4] (∼□)  := by trans (◇∼); exact equivalence_expand_right (◇◇) (◇) (∼); infer_instance;
instance : (◇◇□) ≅[Logic.S4] (◇□)  := equivalence_expand_right (◇◇) (◇) (□)
instance : (◇◇◇) ≅[Logic.S4] (◇)   := by trans (◇◇); exact equivalence_expand_left (◇◇) (◇) (◇); infer_instance;

lemma modal_reducible_3 : ∀ m ∈ Modalities.allOfSize 3, ∃ m' ∈ Logic.S4.modalities, m ⤳[Logic.S4] m' := by
  intro m hm₃;
  obtain ⟨m, hm₂, (rfl | rfl | rfl)⟩ := Modalities.allOfSize.eq_succ hm₃;
  . replace hm₂ : (∼∼ = m ∨ ∼□ = m ∨ ∼◇ = m) ∨ (□∼ = m ∨ □□ = m ∨ □◇ = m) ∨ (◇∼ = m ∨ ◇□ = m ∨ ◇◇ = m) := by
      simpa [Modalities.allOfSize] using hm₂;
    rcases hm₂ with (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl);
    . reduce_to (∼);
    . reduce_to (□);
    . reduce_to (◇);
    . reduce_to (◇);
    . reduce_to (∼□);
    . reduce_to (∼□◇);
    . reduce_to (□);
    . reduce_to (∼◇□);
    . reduce_to (∼◇);
  . obtain ⟨m', hm', hm'_reduce⟩ := modal_reducible_2 _ hm₂;
    use m';
    constructor;
    . assumption;
    . trans m;
      . infer_instance;
      . assumption;
  . replace hm₂ : (∼∼ = m ∨ ∼□ = m ∨ ∼◇ = m) ∨ (□∼ = m ∨ □□ = m ∨ □◇ = m) ∨ (◇∼ = m ∨ ◇□ = m ∨ ◇◇ = m) := by
      simpa [Modalities.allOfSize] using hm₂;
    rcases hm₂ with (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl);
    . reduce_to (◇);
    . reduce_to (∼□);
    . reduce_to (∼□◇);
    . reduce_to (∼□◇);
    . reduce_to (◇□);
    . reduce_to (◇□◇);
    . reduce_to (∼□);
    . reduce_to (◇□);
    . reduce_to (◇);

lemma modal_reducible_4 : ∀ m ∈ Modalities.allOfSize 4, ∃ m' ∈ Logic.S4.modalities, m ⤳[Logic.S4] m' := by
  intro m hm₄;
  obtain ⟨m, hm₃, (rfl | rfl | rfl)⟩ := Modalities.allOfSize.eq_succ hm₄;
  . obtain ⟨m, hm₂, (rfl | rfl | rfl)⟩ := Modalities.allOfSize.eq_succ hm₃;
    . obtain ⟨m', hm', hm'_reduce⟩ := modal_reducible_2 _ hm₂;
      use m';
      constructor;
      . assumption;
      . trans m;
        . sorry;
        . assumption;
    . sorry;
    . sorry;
  . obtain ⟨m', hm', hm'_reduce⟩ := modal_reducible_3 _ hm₃;
    use m';
    constructor;
    . assumption;
    . trans m;
      . infer_instance;
      . assumption;
  . obtain ⟨m', hm', hm'_reduce⟩ := modal_reducible_3 _ hm₃;
    use m';
    constructor;
    . assumption;
    . match m with
      | -  => sorry;
      | ∼m =>
        sorry;
      | □m =>
        sorry;
      | ◇m =>
        trans (◇m);
        . infer_instance;
        . infer_instance;

lemma modal_reducible_lt_5 : ∀ μ ∈ Modalities.allOfSize (n + 4), ∃ μ' ∈ modalities, μ ⤳[Logic.S4] μ' := by
  induction n with
  | zero => sorry;
  | succ n ih =>
    intro μ hμ₁;
    obtain ⟨μ, hμ₂, (rfl | rfl | rfl)⟩ := Modalities.allOfSize.eq_succ hμ₁;
    . sorry;
    . sorry;
    . sorry;

lemma modal_reducible : ∀ n, ∀ μ ∈ Modalities.allOfSize n, ∃ μ' ∈ Logic.S4.modalities, μ ⤳[Logic.S4] μ' := by
  intro n;
  match n with
  | 0 => exact modal_reducible_0;
  | 1 => exact modal_reducible_1;
  | 2 => exact modal_reducible_2;
  | 3 => exact modal_reducible_3;
  | 4 => exact modal_reducible_4;
  | n + 4 =>
    sorry;

end

end Logic.S4

end LO.Modal
