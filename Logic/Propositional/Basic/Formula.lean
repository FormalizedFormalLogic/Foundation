import Logic.Vorspiel.Vorspiel

namespace LO

namespace Propositional

inductive Formula (α : Type u) : Type u where
  | verum  : Formula α
  | falsum : Formula α
  | atom   : α → Formula α
  | natom  : α → Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α

namespace Formula

variable
  {α : Type u} {α₁ : Type u₁} {α₂ : Type u₂} {α₃ : Type u₃}

def neg : Formula α → Formula α
  | verum    => falsum
  | falsum   => verum
  | atom a  => natom a
  | natom a => atom a
  | and p q  => or (neg p) (neg q)
  | or p q   => and (neg p) (neg q)

lemma neg_neg (p : Formula α) : neg (neg p) = p :=
  by induction p <;> simp[*, neg]

instance : LogicSymbol (Formula α) where
  tilde := neg
  arrow := fun p q => or (neg p) q
  wedge := and
  vee := or
  top := verum
  bot := falsum

end Formula

end Propositional

end LO