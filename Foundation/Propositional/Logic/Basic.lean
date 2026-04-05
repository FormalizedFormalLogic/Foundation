module

public import Foundation.Propositional.Formula.Basic
public import Foundation.Propositional.Entailment.Cl.Basic

@[expose] public section

namespace LO.Propositional

open LO.Entailment
open Entailment

@[ext]
structure Logic (α) where
  logic : Set (Formula α)
  subst : ∀ s, ∀ φ ∈ logic, φ⟦s⟧ ∈ logic
  mdp : ∀ {φ ψ}, φ 🡒 ψ ∈ logic → φ ∈ logic → ψ ∈ logic

namespace Logic

instance : SetLike (Logic α) (Formula α) where
  coe := logic
  coe_injective' _ _ := Logic.ext

class IsTrivial (L : Logic α) : Prop where
  eq_univ : L.logic = Set.univ

structure ExtensionOf (L : Logic α) extends Logic α where
  subset_L : ∀ {φ}, φ ∈ L → φ ∈ logic

end Logic


protected abbrev Trivial : Logic α := ⟨Set.univ, by tauto, by tauto⟩

instance : (Propositional.Trivial : Logic α).IsTrivial  := ⟨rfl⟩


end LO.Propositional


end
