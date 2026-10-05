module

public import Foundation.FirstOrder.SetTheory.ZF.ZF
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
noncomputable def transClosure : V := ⋃ˢ auxConstruction.result ![x] ω

/-! ## Lemmas about iterated unions -/

variable {x}

/-- If `y` includes `x` and is transitive, then each iterated union of `x`
is a subset of `y`. -/
lemma itersUnion_subset_of_isTransitive {n y : V} (hxy : x ⊆ y) (hy : IsTransitive y)
    (hnω : n ∈ (ω : V)) : itersUnion.result ![x] n ⊆ y := by
  refine naturalNumber_induction (fun n ↦ itersUnion.result ![x] n ⊆ y) ?_
    (itersUnion.result_zero ![x] ▸ hxy) (fun n hnω ih z hz ↦ ?_) n hnω
  · have : ℒₛₑₜ-function₁ itersUnion.result ![x] := by
      refine ⟨⟨itersUnionBlueprint.resultDef.emb/[#0, #1, &x], ?_⟩⟩
      intro v
      simp [itersUnion.result_defined (V := V).iff ![v 0, v 1, x]]
      simp [Matrix.vec_single_eq_const]
    definability
  · obtain ⟨w, hw, hzw⟩ := mem_sUnion_iff.mp (itersUnion.result_succ ![x] hnω ▸ hz)
    exact hy.transitive w (ih w hw) z hzw

/-! ## Lemmas about transitive closure -/

@[simp]
lemma mem_transClosure_iff {y : V} : y ∈ transClosure x ↔
    ∃ n ∈ (ω : V), y ∈ itersUnion.result ![x] n := by
  refine ⟨fun h ↦ ?_, fun ⟨n, hnω, hyn⟩ ↦ mem_sUnion_iff.mpr
    ⟨itersUnion.result ![x] n, ⟨auxConstruction.mem_result.mpr ⟨n, hnω, rfl⟩, hyn⟩⟩⟩
  obtain ⟨z, hz⟩ := mem_sUnion_iff.mp h
  aesop

def transClosure.dfn : SetTheorySemisentence 2 :=
  f“y x. ∀ z, z ∈ y ↔ ∃ n, (n ∈ !isω ∧ z ∈ !itersUnionBlueprint.resultDef n x)”

lemma transClosure.defined : ℒₛₑₜ-function₁[V] transClosure via transClosure.dfn := by
  refine ⟨fun v ↦ ?_⟩
  simp [dfn, itersUnion.result_defined.iff, mem_ext_iff (x := v 0)]
  simp [Matrix.vec_single_eq_const]

lemma transClosure.definable : ℒₛₑₜ-function₁[V] transClosure := transClosure.defined.to_definable

lemma self_subset_transClosure : x ⊆ transClosure x := by
  intro z hz
  apply mem_transClosure_iff.mpr
  refine ⟨0, zero_mem_ω, itersUnion.result_zero ![x] ▸ hz⟩

/-- The transitive closure is transitive. -/
instance isTransitive_transClosure : IsTransitive (transClosure x) where
  transitive := by
    intro y h
    obtain ⟨n, hnω, hyn⟩ := mem_transClosure_iff.mp h
    intro z hzy
    have hzn : z ∈ itersUnion.result ![x] (succ n) :=
      itersUnion.result_succ ![x] hnω ▸ mem_sUnion_iff.mpr ⟨y, ⟨hyn, hzy⟩⟩
    exact mem_transClosure_iff.mpr ⟨succ n, ω_succ_closed hnω, hzn⟩

/-- The transitive closure of `x` is the `⊆`-minimal transitive set containing `x`. -/
lemma eq_transClosure_of_subset_subset {y : V} (hxy : x ⊆ y) (hytc : y ⊆ transClosure x)
    (hy : IsTransitive y) : y = transClosure x := by
  suffices transClosure x ⊆ y from subset_antisymm hytc this
  intro z hz
  obtain ⟨n, hnω, hzn⟩ := mem_transClosure_iff.mp hz
  exact itersUnion_subset_of_isTransitive hxy hy hnω z hzn

@[simp]
lemma transClosure_eq_self_iff : transClosure x = x ↔ IsTransitive x := by
  refine ⟨fun h ↦ h ▸ isTransitive_transClosure,
    fun h ↦ Eq.symm <| eq_transClosure_of_subset_subset (y := x) (subset_refl x)
      self_subset_transClosure h⟩

lemma transClosure_monotonic {y : V} (hxy : x ⊆ y) : transClosure x ⊆ transClosure y := by
  intro z hz
  obtain ⟨n, hnω, hzn⟩ := mem_transClosure_iff.mp hz
  have hxtc : x ⊆ transClosure y := subset_trans hxy self_subset_transClosure
  exact itersUnion_subset_of_isTransitive hxtc isTransitive_transClosure hnω z hzn

/-! ### Examples of transitive closures -/

@[simp]
lemma transClosure_empty : transClosure (∅ : V) = ∅ :=
  transClosure_eq_self_iff.mpr inferInstance

end TransitiveClosure

end FFL.FirstOrder.SetTheory
