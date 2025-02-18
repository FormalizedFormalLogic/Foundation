
import Foundation.Modal.Kripke.Basic
import Foundation.Modal.Kripke.Hilbert.Geach

section

variable {α : Type u} (rel : α → α → Prop)

def McKinseyan := ∀ x, ∃ y, rel x y ∧ (∀ z, rel y z → y = z)

end


namespace LO.Modal

open Formula.Kripke

namespace Kripke

variable {F : Kripke.Frame}

private lemma not_PseudoMcKinseyan_of_validate_M (h : ¬F ⊧ (Axioms.M (.atom 0))) :
  ∃ x : F.World, ∀ y, x ≺ y → (∃ z w, (y ≺ z ∧ y ≺ w ∧ z ≠ w))
  := by
    obtain ⟨V, x, hx⟩ := ValidOnFrame.exists_valuation_world_of_not h;
    have := Satisfies.imp_def₂.not.mp hx;
    push_neg at this;
    obtain ⟨h₁, h₂⟩ := this;
    use x;
    intro y Rxy;
    obtain ⟨z, Ryz, hz⟩ := Satisfies.dia_def.mp $ h₁ _ Rxy;
    obtain ⟨w, Ryw, hw⟩ := by
      have := Satisfies.dia_def.not.mp h₂;
      push_neg at this;
      have := Satisfies.box_def.not.mp $ this y Rxy;
      push_neg at this;
      exact this;
    have : z ≠ w := by
      intro h;
      subst h;
      contradiction;
    use z, w;

private lemma not_McKinseyan_of_notPseudoMcKinseyan
  (hMc : ∃ x : F.World, ∀ y, x ≺ y → (∃ z w, (y ≺ z ∧ y ≺ w ∧ z ≠ w)))
  : ¬McKinseyan F.Rel := by
  unfold McKinseyan;
  push_neg;
  obtain ⟨x, h⟩ := hMc;
  use x;
  intro y Rxy;
  obtain ⟨u, v, Ryu, Ryv, huv⟩ := h y Rxy;
  by_cases hyu : y = u;
  . subst hyu;
    use v;
  . use u;

lemma notMcKinseyan_of_not_validate_M (h : ¬F ⊧ (Axioms.M (.atom 0))) : ¬McKinseyan F.Rel :=
  not_McKinseyan_of_notPseudoMcKinseyan $ not_PseudoMcKinseyan_of_validate_M h

lemma mcKinseyan_of_validate_M_trans : McKinseyan F → F ⊧ (Axioms.M (.atom 0)) := by
  contrapose;
  exact notMcKinseyan_of_not_validate_M;

lemma validate_M_of_mckinseyan_trans (hTrans : Transitive F) : F ⊧ (Axioms.M (.atom 0)) → McKinseyan F := by
  contrapose;
  intro hMc;
  unfold McKinseyan at hMc;
  push_neg at hMc;
  obtain ⟨x, h⟩ := hMc;
  by_cases hDead : ∀ y, ¬x ≺ y;
  . apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ _ _ => True), x;
    suffices (∀ y, x ≺ y → ∃ x, y ≺ x) ∧ ∀ y, ¬x ≺ y by
      simpa [Satisfies];
    constructor;
    . intro y Rxy;
      have := hDead y Rxy;
      contradiction;
    . assumption;
  . push_neg at hDead;
    obtain ⟨y, Rxy⟩ := hDead;
    apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ z _ =>
      x ≺ z ∧ ∀ u, x ≺ u → ∃ v, (v ≠ z ∧ u ≺ z ∧ u ≺ v)
    ), x;
    apply Satisfies.imp_def₂.not.mpr;
    push_neg;

    constructor;
    . apply Satisfies.box_def.mpr;
      intro w Rxw;
      apply Satisfies.dia_def.mpr;
      obtain ⟨z, Rwz, hwz⟩ := h w Rxw;
      use z;
      constructor;
      . assumption;
      . simp [Semantics.Realize, Satisfies];
        constructor;
        . exact hTrans Rxw Rwz;
        . intro u Rxu;
          use w;
          refine ⟨?_, ?_, ?_⟩;
          . tauto;
          . sorry
          . sorry;
    . apply Satisfies.dia_def.not.mpr
      push_neg;
      intro z Rxz;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      obtain ⟨w, Rzw, hzw⟩ := h z Rxz;
      use w;
      constructor;
      . assumption;
      . simp [Semantics.Realize, Satisfies];
        intro Rxw;
        use z;
        constructor;
        . assumption;
        . intro v hvw _;
          sorry;

abbrev TransitiveMcKinseyanFrameClass : FrameClass := { F | Transitive F ∧ McKinseyan F }

instance TransitiveMcKinseyanFrameClass.DefinedByFourAndM : TransitiveMcKinseyanFrameClass.DefinedBy {Axioms.Four (.atom 0), Axioms.M (.atom 0)} := ⟨by
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, ValidOnFrame.models_iff, forall_eq_or_imp, forall_eq];
  intro F;
  constructor;
  . rintro ⟨hT, hM⟩;
    refine ⟨?_, ?_⟩;
    . exact iff_transitive_validate_AxiomFour.mp hT;
    . exact mcKinseyan_of_validate_M_trans hM;
  . rintro ⟨hFour, hM⟩;
    have := iff_transitive_validate_AxiomFour.mpr hFour;
    constructor;
    . assumption;
    . exact validate_M_of_mckinseyan_trans this hM;
⟩

instance : Kripke.TransitiveMcKinseyanFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Transitive, McKinseyan];

end Kripke

end LO.Modal
