import Foundation.Modal.Modality.Basic
import Foundation.Modal.Kripke.Logic.S4

namespace LO.Modal


section

open Modality Modalities

variable {M : Modalities} {n : ℕ} {L : Logic} {n : ℕ}

structure ModalityReducing (L : Logic) (n : ℕ) (M : Modalities) where
  M_size : ∀ m ∈ M, m.size ≤ n
  M_mem  : ∀ m ∈ Modalities.allOfSize n, ∃ m' ∈ M, m ⤳[L] m'

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

abbrev modalities : Modalities := {-, ∼, □, ◇, ∼□, ∼◇, □◇, ◇□, □◇□, ◇□◇, ∼□◇□, ∼◇□◇}



section

set_option linter.style.multiGoal false

instance : (□□) ≅[Logic.S4] (□)  := inferInstance
instance : (□◇) ≅[Logic.S4] (□◇) := inferInstance
instance : (□∼) ≅[Logic.S4] (∼◇) := inferInstance
instance : (◇□) ≅[Logic.S4] (◇□) := inferInstance
instance : (◇◇) ≅[Logic.S4] (◇)  := inferInstance
instance : (◇∼) ≅[Logic.S4] (∼□) := inferInstance
instance : (∼□) ≅[Logic.S4] (∼□) := inferInstance
instance : (∼◇) ≅[Logic.S4] (∼◇) := inferInstance
instance : (∼∼) ≅[Logic.S4] (-)  := inferInstance

instance : (∼□□) ≅[Logic.S4] (∼□)  := equivalence_expand_left (□□) (□) (∼)
instance : (∼□◇) ≅[Logic.S4] (∼□◇) := inferInstance
instance : (∼□∼) ≅[Logic.S4] (◇)   := by trans (∼∼◇); exact equivalence_expand_left (□∼) (∼◇) (∼); exact equivalence_expand_right (∼∼) (-) (◇)
instance : (∼◇□) ≅[Logic.S4] (∼◇□) := inferInstance
instance : (∼◇◇) ≅[Logic.S4] (∼◇)  := equivalence_expand_left (◇◇) (◇) (∼)
instance : (∼◇∼) ≅[Logic.S4] (□)   := by trans (∼∼□); exact equivalence_expand_left (◇∼) (∼□) (∼); exact equivalence_expand_right (∼∼) (-) (□)
instance : (∼∼□) ≅[Logic.S4] (□)   := equivalence_expand_right (∼∼) (-) (□)
instance : (∼∼◇) ≅[Logic.S4] (◇)   := equivalence_expand_right (∼∼) (-) (◇)
instance : (∼∼∼) ≅[Logic.S4] (∼)   := equivalence_expand_right (∼∼) (-) (∼)
instance : (□∼□) ⤳[Logic.S4] (∼□)  := inferInstance
instance : (□∼◇) ⤳[Logic.S4] (∼◇)  := inferInstance
instance : (□∼∼) ⤳[Logic.S4] (-)   := translation_expand_left (∼∼) (-) (□)
instance : (□□□) ≅[Logic.S4] (□)   := by trans (□□); exact equivalence_expand_right (□□) (□) (□); infer_instance;
instance : (□□◇) ≅[Logic.S4] (□◇)  := equivalence_expand_right (□□) (□) (◇)
instance : (□□∼) ≅[Logic.S4] (∼◇)  := by trans (□∼) <;> infer_instance
instance : (□◇□) ⤳[Logic.S4] (◇□)  := by trans (◇□) <;> infer_instance
instance : (□◇◇) ⤳[Logic.S4] (◇)   := by trans (◇◇) <;> infer_instance
instance : (□◇∼) ⤳[Logic.S4] (∼□)  := by trans (◇∼) <;> infer_instance
instance : (◇∼□) ≅[Logic.S4] (∼□)  := by trans (∼□□); exact equivalence_expand_right (◇∼) (∼□) (□); exact equivalence_expand_left (□□) (□) (∼)
instance : (◇∼◇) ≅[Logic.S4] (∼□◇) := equivalence_expand_right (◇∼) (∼□) (◇)
instance : (◇∼∼) ≅[Logic.S4] (◇)   := by trans (∼□∼); exact equivalence_expand_right (◇∼) (∼□) (∼); infer_instance;
instance : (◇□□) ≅[Logic.S4] (◇□)  := equivalence_expand_left (□□) (□) (◇)
instance : (◇□◇) ≅[Logic.S4] (◇□◇) := inferInstance
instance : (◇□∼) ≅[Logic.S4] (∼□◇) := by trans (◇∼◇); exact equivalence_expand_left (□∼) (∼◇) (◇); infer_instance;
instance : (◇◇□) ≅[Logic.S4] (◇□)  := equivalence_expand_right (◇◇) (◇) (□)
instance : (◇◇◇) ≅[Logic.S4] (◇)   := by trans (◇◇); exact equivalence_expand_left (◇◇) (◇) (◇); infer_instance;
instance : (◇◇∼) ≅[Logic.S4] (∼□)  := by trans (◇∼); exact equivalence_expand_right (◇◇) (◇) (∼); infer_instance;

end


#eval Modalities.more { m ∈ modalities | m.size = 2 }

lemma reducing_modalities_degree_0 : ModalityReducing Logic.S4 0 (modalities.filter (·.size ≤ 0)) where
  M_size := by decide
  M_mem m hm := by
    simp only [Modalities.allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union, Finset.mem_singleton] at hm;
    subst hm;
    reduce_to -;

lemma reducing_modalities_degree_1 : ModalityReducing Logic.S4 1 (modalities.filter (·.size ≤ 1)) where
  M_size := by decide
  M_mem m hm := by
    simp only [
      Modalities.allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union, Finset.mem_singleton
    ] at hm;
    rcases hm with rfl | rfl | rfl;
    . reduce_to □;
    . reduce_to ◇;
    . reduce_to ∼;

/-
lemma reducing_modalities_degree_2 : ModalityReducing Logic.S4 2 (modalities.filter (·.size ≤ 2)) where
  M_size := by decide
  M_mem m hm := by
    simp only [
      Modalities.allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union,
      Finset.mem_image, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left
    ] at hm;
    rcases hm with (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl);
    . reduce_to □;
    . reduce_to □◇;
    . reduce_to ∼◇;
    . reduce_to ◇□;
    . reduce_to ◇;
    . reduce_to ∼□;
    . reduce_to ∼□;
    . reduce_to ∼◇;
    . reduce_to -;
-/

/-
lemma reducing_modalities_degree_3 : ModalityReducing Logic.S4 3 (modalities.filter (·.size ≤ 3)) where
  M_size := by decide
  M_mem m hm := by
    simp only [
      Modalities.allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union,
      Finset.mem_image, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left
    ] at hm;
    rcases hm with
      ⟨m, (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl), rfl⟩ |
      ⟨m, (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl), rfl⟩ |
      ⟨m, (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl), rfl⟩;
    . reduce_to □;
    . reduce_to □◇;
    . reduce_to ∼;
    . reduce_to ◇□;
    . sorry;
    . sorry;
    . sorry;
    . sorry;
    . sorry;
    . sorry;
    . reduce_to ◇□◇;
    . sorry;
    . reduce_to ◇□;
    . reduce_to ◇;
    . sorry;
    . sorry;
    . sorry;
    . sorry;
    . sorry;
    . sorry;
    . sorry;
    . sorry;
    . sorry;
    . sorry;
    . reduce_to □;
    . reduce_to ◇;
    . reduce_to ∼;
-/

end Logic.S4

end LO.Modal
