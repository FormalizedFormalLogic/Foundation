import Foundation.Modal.Modality.Basic
import Foundation.Modal.Entailment.S5
import Foundation.Modal.Kripke.Logic.S5

namespace LO.Modal


section

open Modality Modalities

variable {L : Logic} [L.IsNormal] {M : Modalities} {n : ℕ} {n : ℕ}

abbrev ModalReducible (L : Logic) (n : ℕ) (M : Modalities) := ∀ m ∈ Modalities.allOfSize n, ∃ m' ∈ M, m ⤳[L] m'

macro "reduce_to " t:term : tactic => `(tactic| focus
  existsi $t;
  constructor;
  . set_option linter.unnecessarySimpa false in
    simpa;
  . infer_instance;
)

lemma ModalReducible.reducible_0 (hM : (-) ∈ M) : ModalReducible L 0 M := by
  simp only [ModalReducible, allOfSize.eq_zero, Finset.mem_singleton, forall_eq];
  reduce_to (-);

lemma ModalReducible.reducible_1 (hNeg : (∼) ∈ M) (hBox : (□) ∈ M) (hDia : (◇) ∈ M) : ModalReducible L 1 M := by
  simp only [
    ModalReducible, allOfSize, Finset.image_singleton, Finset.union_assoc,
    Finset.mem_union, Finset.mem_singleton, forall_eq_or_imp, forall_eq
  ];
  refine ⟨?_, ?_, ?_⟩;
  . reduce_to (∼);
  . reduce_to (□);
  . reduce_to (◇);

end


namespace Logic.S5

set_option linter.style.multiGoal false

variable {m m₁ m₂ : Modality}

open Entailment
open Modality
open Formula
open Kripke
open Modalities

protected abbrev modalities : Modalities := {-, ∼, □, ◇, ∼□, ∼◇}

lemma modal_reducible_0 : ModalReducible Logic.S5 0 Logic.S5.modalities := ModalReducible.reducible_0 $ by simp;

lemma modal_reducible_1 : ModalReducible Logic.S5 1 Logic.S5.modalities := ModalReducible.reducible_1 (by simp) (by simp) (by simp)

instance : (□□) ≅[Logic.S5] (□)  := by
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
instance : (◇◇) ≅[Logic.S5] (◇)  := by
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
  . reduce_to (◇);
  . reduce_to (∼□);
  . reduce_to (□);
  . reduce_to (◇);

lemma modal_reducible_3 : ModalReducible Logic.S5 3 S5.modalities := by
  intro m hm₃;
  rcases Modalities.allOfSize.eq_succ_right hm₃ with ⟨m, hm₂, (rfl | rfl | rfl)⟩;
  . obtain ⟨m', hm, hm_reducible⟩ := modal_reducible_2 m hm₂;
    use m';
    constructor;
    . assumption;
    . sorry;
  . sorry;
  . sorry;

end Logic.S5

end LO.Modal
