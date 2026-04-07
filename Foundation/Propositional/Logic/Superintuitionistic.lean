module

public import Foundation.Propositional.Hilbert.Minimal.Basic

@[expose] public section

namespace LO.Propositional

abbrev SuperintuitionisticLogic (α) := Logic.ExtensionOf (Propositional.Int : Logic α)

namespace SuperintuitionisticLogic

variable {L : SuperintuitionisticLogic α} {φ ψ : Formula α}

lemma subset_Int (h : φ ∈ Propositional.Int) : φ ∈ L.logic := L.subset_L h

lemma trivial_of_mem_bot (h : ⊥ ∈ L.toLogic) : ∀ {φ}, φ ∈ L.toLogic := L.mdp (L.subset_Int Entailment.efq!) h
instance (h : ⊥ ∈ L.toLogic) : L.IsTrivial := ⟨Set.eq_univ_iff_forall.mpr $ @trivial_of_mem_bot α L h⟩

class Consistent (L : SuperintuitionisticLogic α) : Prop where
  not_mem_bot : ⊥ ∉ L.logic
export Consistent (not_mem_bot)
attribute [simp, grind .] not_mem_bot

lemma ssubset_univ [L.Consistent] : L.logic ⊂ Propositional.Trivial.logic := by
  apply Set.ssubset_iff_exists.mpr;
  constructor;
  . tauto;
  . use ⊥;
    grind;

end SuperintuitionisticLogic

end LO.Propositional


end
