import Foundation.Modal.Modality.Basic
import Foundation.Modal.Entailment.S5
import Foundation.Modal.Kripke.Logic.S5

namespace LO.Modal


section

open Modality Modalities

variable {L : Logic} {M : Modalities} {n : ℕ} {n : ℕ}

/-- In `L`, every `n`-size modality is reduced to some modality in `M` -/
abbrev ModalReducible (L : Logic) (n : ℕ) (M : Modalities) := ∀ m, m.size = n → ∃ m' ∈ M, m ⤳[L] m'

lemma ModalReducible.of_allOfSize (h : ∀ m, m ∈ allOfSize n → ∃ m' ∈ M, m ⤳[L] m') : ModalReducible L n M := by
  intro m hm;
  apply h;
  exact allOfSize.iff_mem_eq_size.mpr hm;

/-- In `L`, every modality of size less than `n` is reduced to some modality in `M` -/
abbrev ModalReducibleLe (L : Logic) (n : ℕ) (M : Modalities) := ∀ m, m.size ≤ n → ∃ m' ∈ M, m ⤳[L] m'

lemma ModalReducibleLe.of_allOfSizeLe (h : ∀ m, m ∈ allOfSizeLe n → ∃ m' ∈ M, m ⤳[L] m') : ModalReducibleLe L n M := by
  intro m hm;
  apply h;
  exact allOfSizeLe.iff_mem_le_size.mpr hm;

lemma ModalReducibleLe.of_cumulative (h : ∀ n' ≤ n, ModalReducible L n' M) : ModalReducibleLe L n M := by
  intro m hm;
  apply h m.size ?_ m ?_ <;> tauto;

lemma ModalReducibleLe.gt (h : ModalReducibleLe L n M) (hn : n ≥ n'): ModalReducibleLe L n' M := by
  intro m hm;
  apply h m (by omega);


lemma ModalReducible.of_le (h : ModalReducibleLe L n M) : ModalReducible L n M := by
  intro m hm;
  apply h m (by omega);


macro "reduce_to " t:term : tactic => `(tactic| focus
  try simp only [add_empty_left, add_box_left, add_dia_left, add_neg_left];
  existsi $t;
  constructor;
  . set_option linter.unnecessarySimpa false in
    simpa;
  . infer_instance;
)

section

variable [L.IsNormal]

lemma ModalReducible.reducible_0_of_mem (hM : (-) ∈ M) : ModalReducible L 0 M := by
  apply of_allOfSize;
  intro m hm;
  simp only [allOfSize.eq_zero, Finset.mem_singleton] at hm;
  subst hm;
  reduce_to (-);

lemma ModalReducible.reducible_1_of_mem (hNeg : (∼) ∈ M) (hBox : (□) ∈ M) (hDia : (◇) ∈ M) : ModalReducible L 1 M := by
  apply of_allOfSize;
  intro m hm;
  simp only [
    allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union,
    Finset.mem_singleton
  ] at hm;
  rcases hm with (rfl | rfl | rfl);
  . reduce_to (∼);
  . reduce_to (□);
  . reduce_to (◇);

end

end


namespace Logic.S5

set_option linter.style.multiGoal false

variable {m m₁ m₂ : Modality} {n}

open Entailment
open Modality
open Formula
open Kripke
open Modalities

protected abbrev modalities : Modalities := {-, ∼, □, ◇, ∼□, ∼◇}

lemma modal_reducible_0 : ModalReducible Logic.S5 0 Logic.S5.modalities := ModalReducible.reducible_0_of_mem $ by simp;

lemma modal_reducible_1 : ModalReducible Logic.S5 1 Logic.S5.modalities := ModalReducible.reducible_1_of_mem (by simp) (by simp) (by simp)

instance : (□□) ≅[Logic.S5] (□) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0);
    simp;
  . apply translation_of_axiomInstance (a := 0);
    apply S5.proper_extension_of_S4.subset;
    simp;
instance : (□◇) ≅[Logic.S5] (◇) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0); simp;
  . apply translation_of_axiomInstance (a := 0); simp;
instance : (◇◇) ≅[Logic.S5] (◇) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0);
    apply S5.proper_extension_of_S4.subset;
    simp;
  . apply translation_of_axiomInstance (a := 0);
    apply S5.proper_extension_of_S4.subset;
    simp;
instance : (◇□) ≅[Logic.S5] (□) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0); simp;
  . apply translation_of_axiomInstance (a := 0); simp;

lemma modal_reducible_2 : ModalReducible Logic.S5 2 S5.modalities := by
  apply ModalReducible.of_allOfSize;
  intro m hm;
  simp only [
    allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union,
    Finset.mem_image, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left
  ] at hm;
  rcases hm with (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl);
  . reduce_to (-);
  . reduce_to (∼□);
  . reduce_to (∼◇);
  . reduce_to (∼◇);
  . reduce_to (□);
  . reduce_to (◇);
  . reduce_to (∼□);
  . reduce_to (□);
  . reduce_to (◇);

instance : (∼□∼) ≅[Logic.S5] (◇)  := by trans (∼∼◇); exact equivalence_expand_left (□∼) (∼◇) (∼); exact equivalence_expand_right (∼∼) (-) (◇)
instance : (∼□□) ≅[Logic.S5] (∼□) := equivalence_expand_left (□□) (□) (∼)
instance : (∼◇◇) ≅[Logic.S5] (∼◇) := equivalence_expand_left (◇◇) (◇) (∼)
instance : (∼□◇) ≅[Logic.S5] (∼◇) := equivalence_expand_left (□◇) (◇) (∼)
instance : (∼◇□) ≅[Logic.S5] (∼□) := equivalence_expand_left (◇□) (□) (∼)
instance : (◇∼∼) ≅[Logic.S5] (◇)  := by trans (∼□∼); exact equivalence_expand_right (◇∼) (∼□) (∼); infer_instance;
instance : (◇∼□) ≅[Logic.S5] (∼□) := by trans (∼□□); exact equivalence_expand_right (◇∼) (∼□) (□); exact equivalence_expand_left (□□) (□) (∼)
instance : (◇∼◇) ≅[Logic.S5] (∼◇) := by trans (∼□◇); exact equivalence_expand_right (◇∼) (∼□) (◇); infer_instance;
instance : (◇□□) ≅[Logic.S5] (□)  := by trans (◇□); exact equivalence_expand_left (□□) (□) (◇); infer_instance;
instance : (◇□◇) ≅[Logic.S5] (◇)  := by trans (◇◇); exact equivalence_expand_left (□◇) (◇) (◇);  infer_instance;
instance : (◇□∼) ≅[Logic.S5] (∼◇) := by trans (□∼); exact equivalence_expand_right (◇□) (□) (∼); infer_instance;
instance : (◇◇∼) ≅[Logic.S5] (∼□) := by trans (◇∼); exact equivalence_expand_right (◇◇) (◇) (∼); infer_instance;
instance : (◇◇□) ≅[Logic.S5] (◇□) := by trans (◇□); exact equivalence_expand_right (◇◇) (◇) (□); infer_instance;
instance : (◇◇◇) ≅[Logic.S5] (◇)  := by trans (◇◇); exact equivalence_expand_left (◇◇) (◇) (◇); infer_instance;

lemma modal_reducible_3 : ModalReducible Logic.S5 3 S5.modalities := by
  intro m hm;
  obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := split_left₁ hm;
  rcases iff_size_1.mp hm₁ with (rfl | rfl | rfl);
  . obtain ⟨m', _, _⟩ := modal_reducible_2 m₂ hm₂;
    use m';
    constructor;
    . assumption;
    . trans m₂;
      . apply translation_expand_right (□) (-);
      . assumption;
  . obtain ⟨m₁, m₂, hm₁, hm₂', rfl⟩ := split_left₁ hm₂;
    rcases iff_size_1.mp hm₁ with (rfl | rfl | rfl);
    . rcases iff_size_1.mp hm₂' with (rfl | rfl | rfl);
      . reduce_to (□);
      . reduce_to (◇);
      . reduce_to (∼◇);
    . obtain ⟨m', _, _⟩ := modal_reducible_2 (◇m₂) (by simpa);
      use m';
      constructor;
      . assumption;
      . trans (◇m₂)
        . apply translation_expand_right (◇◇) (◇);
        . assumption;
    . rcases iff_size_1.mp hm₂' with (rfl | rfl | rfl);
      . reduce_to (∼□);
      . reduce_to (∼◇);
      . reduce_to (◇);
  . obtain ⟨m₁, m₂, hm₁, hm₂', rfl⟩ := split_left₁ hm₂;
    rcases iff_size_1.mp hm₁ with (rfl | rfl | rfl);
    . rcases iff_size_1.mp hm₂' with (rfl | rfl | rfl);
      . reduce_to (∼□);
      . reduce_to (∼◇);
      . reduce_to (◇);
    . rcases iff_size_1.mp hm₂' with (rfl | rfl | rfl);
      . reduce_to (∼□);
      . reduce_to (∼◇);
      . reduce_to (□);
    . use m₂;
      constructor;
      . rcases iff_size_1.mp hm₂' with (rfl | rfl | rfl) <;> tauto;
      . apply translation_expand_right (∼∼) (-);

lemma modal_reducible_le_3 : ModalReducibleLe Logic.S5 3 S5.modalities := by
  apply ModalReducibleLe.of_cumulative;
  intro n hn;
  match n with
  | 0 => exact modal_reducible_0;
  | 1 => exact modal_reducible_1;
  | 2 => exact modal_reducible_2;
  | 3 => exact modal_reducible_3;

lemma modal_reducible_le_succ_4 (n) : ModalReducibleLe Logic.S5 (n + 4) S5.modalities := by
  intro m hm;
  obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ : ∃ m₁ m₂, m₁.size ≤ 3 ∧ m₂.size ≤ n + 1 ∧ m = m₁ + m₂ := split_le $ by omega;
  induction n generalizing m₂ with
  | zero =>
    obtain ⟨m₃, hm₃, _⟩ := modal_reducible_le_3 m₁ hm₁;
    obtain ⟨m₄, hm₄, _⟩ := modal_reducible_le_3 (m₃ + m₂) $ by
      simp only [add_size];
      have : m₃.size ≤ 2 := @Modalities.lt_max_size_of_mem _ S5.modalities (by simp) hm₃;
      omega;
    use m₄;
    constructor;
    . assumption;
    . trans (m₃ + m₂);
      . apply translation_expand_right;
      . assumption;
  | succ n ih =>
    obtain ⟨m₃, m₄, hm₃, hm₄, rfl⟩ := split_right_le₁ hm₂;
    obtain ⟨m₅, hm₅, _⟩ := @ih m₃ hm₃ (by simp; omega);
    obtain ⟨m₆, hm₆, _⟩ := modal_reducible_le_3 (m₅ + m₄) $ by
      simp only [add_size];
      have : m₅.size ≤ 2 := @Modalities.lt_max_size_of_mem _ S5.modalities (by simp) hm₅;
      omega;
    use m₆;
    constructor;
    . assumption;
    . trans (m₅ + m₄);
      . rw [show (m₁ + (m₃ + m₄)) = ((m₁ + m₃) + m₄) by simp];
        apply translation_expand_right;
      . assumption;

lemma modal_reducible_le (n : ℕ) : ModalReducibleLe Logic.S5 n S5.modalities := by
  match n with
  | 0 | 1 | 2 | 3 => apply ModalReducibleLe.gt modal_reducible_le_3 (by omega);
  | n + 4 => apply modal_reducible_le_succ_4;

theorem modal_reducible (n : ℕ) : ModalReducible Logic.S5 n S5.modalities := by
  apply ModalReducible.of_le;
  exact modal_reducible_le n;

end Logic.S5

end LO.Modal
