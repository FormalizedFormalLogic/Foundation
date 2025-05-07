import Foundation.Propositional.Hilbert.Int
import Foundation.Propositional.Kripke.Hilbert.Int

namespace LO.Propositional

abbrev Logic := Set (Formula ℕ)


abbrev Hilbert.logic (H : Hilbert ℕ) : Logic := { φ | H ⊢! φ }


protected abbrev Logic.Int : Logic := Hilbert.Int.logic


namespace Logic

class IsSuperintuitionistic (L : Logic) where
  subset_Int : Logic.Int ⊆ L
  mdp_closed {φ ψ} : φ ➝ ψ ∈ L → φ ∈ L → ψ ∈ L
  subst_closed {φ} : φ ∈ L → ∀ s, φ⟦s⟧ ∈ L

class Consistent (L : Logic) : Prop where
  consis : L ≠ Set.univ
attribute [simp] Consistent.consis

end Logic


namespace Hilbert

open Entailment

variable {H : Hilbert ℕ}

protected instance superintuitionistic [H.HasEFQ] : (H.logic).IsSuperintuitionistic where
  subset_Int := by
    intro φ hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with ⟨s, rfl⟩; simp;
    | mdp ihφψ ihφ => exact mdp! ihφψ ihφ;
    | _ => simp;
  mdp_closed := by
    intro φ ψ hφψ hφ;
    exact hφψ ⨀ hφ;
  subst_closed := by
    intro φ hφ s;
    exact Hilbert.Deduction.subst! s hφ;

end Hilbert


instance : (Logic.Int).IsSuperintuitionistic := Hilbert.superintuitionistic

instance Logic.consistent_of_consistent_hilbert {H : Hilbert ℕ} [Entailment.Consistent H] : Consistent (H.logic) := ⟨by
  apply Set.eq_univ_iff_forall.not.mpr;
  push_neg;
  obtain ⟨φ, hφ⟩ : ∃ φ, H ⊬ φ := Entailment.Consistent.exists_unprovable inferInstance;
  use φ;
  simpa;
⟩

section

open Kripke

abbrev Kripke.FrameClass.logic (C : FrameClass) : Logic := { φ | C ⊧ φ }

lemma Logic.eq_Hilbert_Logic_KripkeFrameClass_Logic {H : Hilbert ℕ} {C : FrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  . exact sound.sound;
  . exact complete.complete;

lemma Logic.Int.Kripke.eq_all : Logic.Int = FrameClass.all.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

lemma Logic.Int.Kripke.eq_all_finite : Logic.Int = FrameClass.finite_all.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic



end


end LO.Propositional
