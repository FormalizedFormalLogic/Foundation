import Logic.Logic.System

namespace LO

variable {F : Type*} [LogicalConnective F] {α : Type*} [Semantics F α]

namespace Semantics

def Equiv (p q : F) : Prop := Valid (p ⟷ q)

namespace Equiv

@[refl] lemma refl (p : F) : Equiv p p := fun a ↦ by simp

@[symm] lemma symm {p q : F} : Equiv p q → Equiv q p := fun h a ↦ by
  have : a ⊧ p ↔ a ⊧ q := by simpa using @h a
  simpa using this.symm

@[trans] lemma trans {p q r : F} : Equiv p q → Equiv q r → Equiv p r := fun hp hq a ↦ by
  have hp : a ⊧ p ↔ a ⊧ q := by simpa using @hp a
  have hq : a ⊧ q ↔ a ⊧ r := by simpa using @hq a
  simpa using Iff.trans hp hq

end Equiv

end Semantics

end LO
