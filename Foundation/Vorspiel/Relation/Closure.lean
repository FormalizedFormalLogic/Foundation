import Mathlib.Logic.Relation
import Mathlib.Tactic.ByContra

namespace Relation

variable {α} {r : α → α → Prop}


namespace ReflGen

instance : IsRefl α (ReflGen r) := ⟨by apply ReflGen.refl⟩

instance [IsTrans _ r] : IsTrans α (ReflGen r) := ⟨by
  rintro a b c (rfl | Rab) (rfl | Rbc);
  . exact ReflGen.refl;
  . exact ReflGen.single Rbc;
  . exact ReflGen.single Rab;
  . exact ReflGen.single $ IsTrans.trans a b c Rab Rbc;
⟩

instance [IsIrrefl _ r] [IsTrans _ r] : IsAntisymm α (ReflGen r) := ⟨by
  rintro a b (rfl | Rab) (rfl | Rba);
  . trivial;
  . trivial;
  . trivial;
  . exfalso;
    exact IsIrrefl.irrefl a $ IsTrans.trans a b a Rab Rba
⟩

instance [IsTrans _ r] [IsIrrefl _ r] : IsPartialOrder α (ReflGen r) where

end ReflGen


namespace TransGen

instance : IsTrans α (TransGen r) := ⟨by apply TransGen.trans⟩

end TransGen


section Irrefl

def IrreflGen (r : α → α → Prop) := λ x y => x ≠ y ∧ r x y

instance : IsIrrefl α (IrreflGen r) := ⟨by simp [IrreflGen]⟩

instance [IsTrans α r] [IsAntisymm α r] : IsTrans α (IrreflGen r) := ⟨by
  rintro a b c ⟨hne, Rab⟩ ⟨_, Rbc⟩;
  constructor;
  . by_contra hC;
    subst hC;
    exact hne $ IsAntisymm.antisymm a b Rab Rbc;
  . exact IsTrans.trans a b c Rab Rbc;
⟩

end Irrefl


end Relation
