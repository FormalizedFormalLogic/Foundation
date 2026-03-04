module

public import Foundation.FirstOrder.SetTheory.Basic.Axioms

@[expose] public section
/-! # Basic properties of model of set theory-/

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

scoped instance : HasSubset V := ⟨fun x y ↦ ∀ z ∈ x, z ∈ y⟩

lemma subset_def {a b : V} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b := by rfl

instance Subset.defined_isSubsetOf : ℒₛₑₜ-relation[V] Subset via isSubsetOf :=
  ⟨fun v ↦ by simp [isSubsetOf, subset_def]⟩

instance Subset.definable : ℒₛₑₜ-relation[V] Subset := defined_isSubsetOf.to_definable

@[simp, refl] lemma subset_refl (x : V) : x ⊆ x := by simp [subset_def]

@[simp, trans] lemma subset_trans {x y z : V} : x ⊆ y → y ⊆ z → x ⊆ z := fun hxy hyz v hv ↦ hyz v (hxy v hv)

instance : Std.Refl (α := V) Subset := ⟨subset_refl⟩

instance : IsTrans V Subset := ⟨fun _ _ _ ↦ subset_trans⟩

def IsEmpty (a : V) : Prop := ∀ x, x ∉ a

lemma IsEmpty.not_mem {a x : V} (h : IsEmpty a) : x ∉ a := h x

instance IsEmpty.defined : ℒₛₑₜ-predicate[V] IsEmpty via isEmpty :=
  ⟨fun v ↦ by simp [isEmpty, IsEmpty]⟩

instance IsEmpty.definable : ℒₛₑₜ-predicate[V] IsEmpty := defined.to_definable

class IsNonempty (a : V) : Prop where
  nonempty : ∃ x, x ∈ a

lemma isNonempty_def {x : V} : IsNonempty x ↔ ∃ y, y ∈ x := ⟨fun h ↦ h.nonempty, fun h ↦ ⟨h⟩⟩

instance IsNonempty.defined_isNonempty : ℒₛₑₜ-predicate[V] IsNonempty via isNonempty :=
  ⟨fun v ↦ by simp [isNonempty, isNonempty_def]⟩

instance IsNonempty.definable : ℒₛₑₜ-predicate[V] IsNonempty := defined_isNonempty.to_definable

@[simp] lemma not_isEmpty_iff_isNonempty {x : V} :
    ¬IsEmpty x ↔ IsNonempty x := by simp [IsEmpty, isNonempty_def]

@[simp] lemma not_isNonempty_iff_isEmpty {x : V} :
    ¬IsNonempty x ↔ IsEmpty x := by simp [IsEmpty, isNonempty_def]

scoped instance : CoeSort V (Type _) := ⟨fun x ↦ {z : V // z ∈ x}⟩

def SSubset (x y : V) : Prop := x ⊆ y ∧ x ≠ y

infix:50 " ⊊ " => SSubset

lemma ssubset_def {x y : V} : x ⊊ y ↔ x ⊆ y ∧ x ≠ y := by rfl

def SSubset.dfn : SetTheorySemisentence 2 := “x y. x ⊆ y ∧ x ≠ y”

instance SSubset.defined : ℒₛₑₜ-relation[V] SSubset via SSubset.dfn := ⟨fun v ↦ by simp [ssubset_def, SSubset.dfn]⟩

instance SSubset.definable : ℒₛₑₜ-relation[V] SSubset := SSubset.defined.to_definable

@[simp] lemma SSubset.irrefl (x : V) : ¬x ⊊ x := by simp [ssubset_def]

lemma SSubset.subset {x y : V} : x ⊊ y → x ⊆ y := fun h ↦ h.1

lemma val_isSucc_iff {v : Fin 2 → V} :
    V ⊧/v isSucc ↔ ∀ z, z ∈ v 0 ↔ z = v 1 ∨ z ∈ v 1 := by
  simp [isSucc]

section

variable [Nonempty V]

instance [V ⊧ₘ* 𝗭] [V ⊧ₘ* 𝗔𝗖] : V ⊧ₘ* 𝗭𝗖 := inferInstance

instance [V ⊧ₘ* 𝗭𝗙] [V ⊧ₘ* 𝗔𝗖] : V ⊧ₘ* 𝗭𝗙𝗖 := inferInstance

instance : V ⊧ₘ* (𝗘𝗤 : SetTheory) := Structure.Eq.models_eqAxiom' ℒₛₑₜ V

end

section

variable {U : Set V}

instance submodel (U : Set V) : SetStructure U := ⟨fun y x ↦ x.val ∈ y.val⟩

lemma submodel_mem_iff {x y : U} :
    x ∈ y ↔ x.val ∈ y.val := by rfl

@[simp] lemma mk_mem_mk_iff_mem {x y : V} {hx hy} :
    (⟨x, hx⟩ : U) ∈ (⟨y, hy⟩ : U) ↔ x ∈ y := by rfl

end

end LO.FirstOrder.SetTheory
