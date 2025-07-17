import Foundation.Modal.Neighborhood.Basic
import Foundation.Modal.Neighborhood.Completeness

namespace LO.Modal.Neighborhood

open Formula.Neighborhood

variable {F : Frame}

class Frame.IsRegular (F : Frame) : Prop where
  regular : ∀ X Y : Set F, (ℬ X) ∩ (ℬ Y) ⊆ ℬ (X ∩ Y)

lemma Frame.regular [Frame.IsRegular F] {X Y : Set F} : (ℬ X) ∩ (ℬ Y) ⊆ ℬ (X ∩ Y) := by apply IsRegular.regular

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


section

variable [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.EC 𝓢]

open Entailment
open MaximalConsistentSet

instance : (mkCanonicalFrame 𝓢 (minimal_canonical_box 𝓢)).IsRegular := by
  constructor;
  rintro X Y Γ ⟨hX, hY⟩;
  obtain ⟨φ, rfl, hφ⟩ := minimal_canonical_box.exists_box X Γ hX;
  obtain ⟨ψ, rfl, hψ⟩ := minimal_canonical_box.exists_box Y Γ hY;
  rw [(show proofset 𝓢 φ ∩ proofset 𝓢 ψ = proofset 𝓢 (φ ⋏ ψ) by simp)];
  have : proofset 𝓢 (□φ ⋏ □ψ) ⊆ proofset 𝓢 (□(φ ⋏ ψ)) := proofset.imp_subset |>.mp (by simp);
  have : Γ ∈ proofset 𝓢 (□(φ ⋏ ψ)) := this $ by
    simp only [proofset.eq_and, Set.mem_inter_iff];
    constructor;
    . apply hφ ▸ hX;
    . apply hψ ▸ hY;
  apply minimal_canonical_box 𝓢 |>.canonicity _ ▸ this;

end

end LO.Modal.Neighborhood
