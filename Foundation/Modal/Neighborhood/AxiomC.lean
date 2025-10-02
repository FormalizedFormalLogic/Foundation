import Foundation.Modal.Neighborhood.Basic
import Foundation.Modal.Neighborhood.Completeness

namespace LO.Modal.Neighborhood

open Formula.Neighborhood

variable {F : Frame}

class Frame.IsRegular (F : Frame) : Prop where
  regular : ∀ X Y, (F.box X) ∩ (F.box Y) ⊆ F.box (X ∩ Y)

lemma Frame.regular [Frame.IsRegular F] {X Y : Set F} : (F.box X) ∩ (F.box Y) ⊆ F.box (X ∩ Y) := by apply IsRegular.regular

open Classical in
lemma Frame.regular_finset_iUnion [F.IsRegular] (s : Finset (Set F)) (hs : s.Nonempty) : (⋂ i ∈ s, F.box i) ⊆ F.box (⋂ i ∈ s, i) := by
  induction s using Finset.induction_on with
  | empty => simp_all;
  | insert i s hi ih =>
    wlog hs : s.Nonempty;
    . simp_all;
    replace ih := ih hs;
    apply Set.Subset.trans ?_ (show i ∩ ⋂ j ∈ s, j = ⋂ j ∈ insert i s, j by simp ▸ F.regular (X := i) (Y := ⋂ j ∈ s, j));
    suffices (F.box i) ∩ (⋂ j ∈ s, F.box j) ⊆ F.box (⋂ j ∈ s, j) by simpa;
    grind;

open Classical in
lemma Frame.regular_finite_iUnion [F.IsRegular] {ι} [h : Fintype ι] [Nonempty ι] {X : ι → Set F} : (⋂ i : ι, F.box (X i)) ⊆ F.box (⋂ i : ι, X i) := by
  simpa using Frame.regular_finset_iUnion (Finset.univ.image X) (by simp);

instance : Frame.simple_blackhole.IsRegular := ⟨by
  intro X Y e;
  simp_all;
⟩

@[simp]
lemma valid_axiomC_of_isRegular [F.IsRegular] : F ⊧ Axioms.C (.atom 0) (.atom 1) := by
  intro V x;
  simp only [
    Satisfies, Model.truthset.eq_imp, Model.truthset.eq_and, Model.truthset.eq_box,
    Model.truthset.eq_atom, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq
  ];
  apply not_or_of_imp;
  rintro ⟨h₁, h₂⟩;
  apply F.regular;
  constructor;
  . apply h₁;
  . apply h₂;

lemma isRegular_of_valid_axiomC (h : F ⊧ Axioms.C (.atom 0) (.atom 1)) : F.IsRegular := by
  constructor;
  rintro X Y w ⟨hwX, hwY⟩;
  have := @h (λ a => match a with | 0 => X | 1 => Y | _ => ∅) w;
  simp [Satisfies] at this;
  grind;

section

variable [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.EC 𝓢]

open Entailment
open MaximalConsistentSet

instance : (minimalCanonicalFrame 𝓢).IsRegular := by
  constructor;
  rintro X Y Γ ⟨hX, hY⟩;
  obtain ⟨φ, rfl, hφ⟩ := minimalCanonicalFrame.exists_box X Γ hX;
  obtain ⟨ψ, rfl, hψ⟩ := minimalCanonicalFrame.exists_box Y Γ hY;
  suffices Γ ∈ proofset 𝓢 (□(φ ⋏ ψ)) by
    rwa [(show proofset 𝓢 φ ∩ proofset 𝓢 ψ = proofset 𝓢 (φ ⋏ ψ) by grind), minimalCanonicalFrame.box_proofset];
  have : proofset 𝓢 (□φ ⋏ □ψ) ⊆ proofset 𝓢 (□(φ ⋏ ψ)) := proofset.imp_subset |>.mp (by simp);
  exact this $ by
    simp only [proofset.eq_and, Set.mem_inter_iff];
    constructor;
    . apply hφ ▸ hX;
    . apply hψ ▸ hY;

end

end LO.Modal.Neighborhood
