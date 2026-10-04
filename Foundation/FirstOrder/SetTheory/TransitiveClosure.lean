module

public import Foundation.FirstOrder.SetTheory.ZF
public import Foundation.FirstOrder.SetTheory.NaturalNumberRec

/-!
# Transitive closure in Zermelo set theory

-/

@[expose] public section

namespace FFL.FirstOrder.SetTheory

namespace TransitiveClosure

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (x : V)

/-! ## Iterating union -/

def itersUnionBlueprint : NaturalNumberRec.Blueprint 1 := {
  zero := “y x. y = x”
  succ := “y z i x. !sUnion.dfn y z”
}

#check itersUnionBlueprint.resultDef

/-- Iterates `⋃ˢ`. -/
noncomputable def itersUnion : NaturalNumberRec.Construction V itersUnionBlueprint := {
  zero := fun v ↦ v 0
  zero_defined := ⟨fun v ↦ by aesop⟩
  succ := fun _ _ z ↦ ⋃ˢ z
  succ_defined := ⟨fun v ↦ by
    simp only [Nat.reduceAdd, Fin.isValue, Fin.succ_zero_eq_one]
    exact sUnion.defined.eval_iff ![v 0, v 1]⟩
}

#check itersUnion.result ![x]

/-! ## Collecting iterated unions with replacement -/

def auxBlueprint : Repl.Blueprint 1 := {
  graph := itersUnionBlueprint.resultDef
}

/-- For taking images of sets (namely `ω`) under `itersUnion.result`. -/
noncomputable def auxConstruction : Repl.Construction V auxBlueprint := {
  map := itersUnion.result
  map_defined := itersUnion.result_defined
}

/-- The transitive closure of a set `x`. -/
noncomputable def transitiveClosure : V := ⋃ˢ auxConstruction.result ![x] ω

#check auxConstruction.mem_result (v := ![x]) (X := ω)

/-! ## Lemmas about transitive closure -/

variable {x}

@[simp]
lemma mem_transitiveClosure_iff {y : V} : y ∈ transitiveClosure x ↔
    ∃ n ∈ (ω : V), y ∈ itersUnion.result ![x] n := by
  refine ⟨fun h ↦ ?_, fun ⟨n, hn, hyn⟩ ↦ mem_sUnion_iff.mpr
    ⟨itersUnion.result ![x] n, ⟨auxConstruction.mem_result.mpr ⟨n, hn, rfl⟩, hyn⟩⟩⟩
  obtain ⟨z, hz⟩ := mem_sUnion_iff.mp h
  aesop

/-- The transitive closure is transitive. -/
instance isTransitive_transitiveClosure : IsTransitive (transitiveClosure x) where
  transitive := by
    intro y h
    obtain ⟨n, hn, hyn⟩ := mem_transitiveClosure_iff.mp h
    intro z hzy
    have hzn : z ∈ itersUnion.result ![x] (succ n) :=
      itersUnion.result_succ ![x] hn ▸ mem_sUnion_iff.mpr ⟨y, ⟨hyn, hzy⟩⟩
    exact mem_transitiveClosure_iff.mpr ⟨succ n, ω_succ_closed hn, hzn⟩

lemma itersUnion_subset_of_isTransitive {n y : V} (hxy : x ⊆ y) (hy : IsTransitive y) (hn : n ∈ (ω : V)) :
    itersUnion.result ![x] n ⊆ y := by
  refine naturalNumber_induction (fun n ↦ itersUnion.result ![x] n ⊆ y) ?_
    (itersUnion.result_zero ![x] ▸ hxy) (fun n hn ih z hz ↦ ?_) n hn
  · have : ℒₛₑₜ-function₁ itersUnion.result ![x] := by
      unfold Language.DefinableFunction₁
      -- unfold Language.DefinableFunction
      #check itersUnion.result_definable
      sorry
    definability
  · obtain ⟨w, hw, hzw⟩ := mem_sUnion_iff.mp (itersUnion.result_succ ![x] hn ▸ hz)
    exact hy.transitive w (ih w hw) z hzw

/-- The transitive closure of `x` is the `⊆`-minimal transitive set containing `x`. -/
theorem eq_transitiveClosure_of_subset_subset {y : V} (hxy : x ⊆ y) (hytc : y ⊆ transitiveClosure x)
    (hy : IsTransitive y) : y = transitiveClosure x := by
  suffices transitiveClosure x ⊆ y from subset_antisymm hytc this
  intro z hz
  obtain ⟨n, hn, hzn⟩ := mem_transitiveClosure_iff.mp hz
  exact itersUnion_subset_of_isTransitive hn hxy hy z hzn

end TransitiveClosure

end FFL.FirstOrder.SetTheory
