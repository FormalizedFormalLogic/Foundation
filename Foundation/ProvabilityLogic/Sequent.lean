module

public import Foundation.ProvabilityLogic.Formula

/-!
# Sequents
-/

@[expose] public section

namespace FFL.ProvabilityLogic

structure Sequent (α : Type*) where
  ant : FormulaFinset α
  suc : FormulaFinset α

infix:50 " ⟹ " => Sequent.mk

namespace Sequent

variable {α : Type*} {S T : Sequent α} {B C : Formula α}

structure Subset (S T : Sequent α) : Prop where
  ant : S.ant ⊆ T.ant
  suc : S.suc ⊆ T.suc

instance : HasSubset (Sequent α) := ⟨Subset⟩

@[simp] lemma subset_iff : S ⊆ T ↔ S.ant ⊆ T.ant ∧ S.suc ⊆ T.suc :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

structure Saturated (S : Sequent α) : Prop where
  impL : ∀ {A B}, A 🡒 B ∈ S.ant → A ∈ S.suc ∨ B ∈ S.ant
  impR : ∀ {A B}, A 🡒 B ∈ S.suc → A ∈ S.ant ∧ B ∈ S.suc

variable [DecidableEq α]

@[grind]
def subfmls (S : Sequent α) : FormulaFinset α := S.ant.subfmls ∪ S.suc.subfmls

@[grind .] lemma subset_subfmls : S.ant ∪ S.suc ⊆ S.subfmls := by
  have := FormulaFinset.subset_subfmls (Γ := S.ant);
  have := FormulaFinset.subset_subfmls (Γ := S.suc);
  grind;

@[grind →]
lemma mem_subfmls_subfmls (hB : B ∈ S.subfmls) (hC : C ∈ B.subfmls) : C ∈ S.subfmls := by
  grind [FormulaFinset.mem_subfmls_subfmls];

end Sequent

end FFL.ProvabilityLogic

end
