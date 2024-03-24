import Logic.Propositional.Intuitionistic.Formula

namespace LO.Propositional.Intuitionistic

section Axioms

variable {F : Type u} [LogicalConnective F] (p q : F)

abbrev AxiomSet (α) := Set (Formula α)

def AxiomEFQ := ⊥ ⟶ p

def AxiomLEM := p ⋎ ~p

def AxiomWeakLEM := ~p ⋎ ~~p

def AxiomDummett := (p ⟶ q) ⋎ (q ⟶ p)

def AxiomDNE := ~~p ⟶ p

end Axioms

section AxiomSet

variable {p q : Formula F}


def AxiomEFQ.set : AxiomSet α := { AxiomEFQ p | p }

notation "𝐄𝐅𝐐" => AxiomEFQ.set

@[simp] lemma AxiomEFQ.set.include : AxiomEFQ p ∈ 𝐄𝐅𝐐 := by simp [set, AxiomEFQ]


def AxiomLEM.set : AxiomSet α := { AxiomLEM p | p }

notation "𝐋𝐄𝐌" => AxiomLEM.set

@[simp] lemma AxiomLEM.set.include : AxiomLEM p ∈ 𝐋𝐄𝐌 := by simp [set, AxiomLEM]


def AxiomWeakLEM.set : AxiomSet α := { AxiomWeakLEM p | p }

notation "𝐰𝐋𝐄𝐌" => AxiomWeakLEM.set

@[simp] lemma AxiomWeakLEM.set.include : AxiomWeakLEM p ∈ 𝐰𝐋𝐄𝐌 := by simp [set, AxiomWeakLEM]


def AxiomDummett.set : AxiomSet α := { AxiomDummett p q | (p) (q) }

notation "𝐆𝐃" => AxiomDummett.set

@[simp] lemma AxiomDummett.set.include : AxiomDummett p q ∈ 𝐆𝐃 := by simp [set, AxiomDummett]; aesop;


def AxiomDNE.set : AxiomSet α := { AxiomDNE p | p }

notation "𝐃𝐍𝐄" => AxiomDNE.set

@[simp] lemma AxiomDNE.set.include : AxiomDNE p ∈ 𝐃𝐍𝐄 := by simp [set, AxiomDNE]

end AxiomSet

end LO.Propositional.Intuitionistic
