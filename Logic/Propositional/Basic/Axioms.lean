import Logic.Propositional.Basic.Formula

namespace LO.Propositional.Basic

section Axioms

variable {F : Type u} [LogicalConnective F] (p q : F)

abbrev AxiomSet (α) := Set (Formula α)

abbrev axiomEFQ := ⊥ ⟶ p

abbrev axiomLEM := p ⋎ ~p

abbrev axiomWeakLEM := ~p ⋎ ~~p

abbrev axiomDummett := (p ⟶ q) ⋎ (q ⟶ p)

abbrev axiomDNE := ~~p ⟶ p

end Axioms

section AxiomSet

variable {p q : Formula F}


abbrev AxiomSet.EFQ : AxiomSet α := { axiomEFQ p | p }

notation "𝐄𝐅𝐐" => AxiomSet.EFQ

@[simp] lemma AxiomSet.EFQ.include : axiomEFQ p ∈ 𝐄𝐅𝐐 := by simp


abbrev AxiomSet.LEM : AxiomSet α := { axiomLEM p | p }

notation "𝐋𝐄𝐌" => AxiomSet.LEM

@[simp] lemma AxiomSet.LEM.include : axiomLEM p ∈ 𝐋𝐄𝐌 := by simp


abbrev AxiomSet.WeakLEM : AxiomSet α := { axiomWeakLEM p | p }

notation "𝐰𝐋𝐄𝐌" => AxiomSet.WeakLEM

@[simp] lemma AxiomSet.WeakLEM.include : axiomWeakLEM p ∈ 𝐰𝐋𝐄𝐌 := by simp


abbrev AxiomSet.Dummett : AxiomSet α := { axiomDummett p q | (p) (q) }

notation "𝐆𝐃" => AxiomSet.Dummett

@[simp] lemma AxiomSet.Dummett.include : axiomDummett p q ∈ 𝐆𝐃 := by aesop


abbrev AxiomSet.DNE : AxiomSet α := { axiomDNE p | p }

notation "𝐃𝐍𝐄" => AxiomSet.DNE

@[simp] lemma AxiomSet.DNE.include : axiomDNE p ∈ 𝐃𝐍𝐄 := by simp

end AxiomSet

end LO.Propositional.Basic
