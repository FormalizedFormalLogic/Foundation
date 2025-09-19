import Foundation.FirstOrder.SetTheory.Axioms
import Foundation.Vorspiel.ExistsUnique

/-!
# Zermelo set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth"
-/

namespace LO

namespace FirstOrder


namespace Semiformula

variable {L : Language} {V : Type*} [DecidableEq V] [Inhabited V] [Structure L V]

-- TODO: move to somewhere in Basic
@[simp] lemma eval_enumarateFVar_idxOfFVar_eq_id (φ : Semiformula L V n) (v) :
    Semiformula.Evalm V v (fun x ↦ φ.enumarateFVar (φ.idxOfFVar x)) φ ↔ Semiformula.Evalm V v id φ :=
  Semiformula.eval_iff_of_funEqOn _ <| by intro x hx; simp [Semiformula.enumarateFVar_idxOfFVar (Semiformula.mem_fvarList_iff_fvar?.mpr hx)]

end Semiformula

end FirstOrder

open FirstOrder SetTheory

inductive Zermelo : Theory ℒₛₑₜ
  | axiom_of_equality : ∀ φ ∈ 𝗘𝗤, Zermelo φ
  | axiom_of_empty_set : Zermelo Axiom.empty
  | axiom_of_extentionality : Zermelo Axiom.extentionality
  | axiom_of_pairing : Zermelo Axiom.pairing
  | axiom_of_union : Zermelo Axiom.union
  | axiom_of_power_set : Zermelo Axiom.power
  | axiom_of_infinity : Zermelo Axiom.infinity
  | axiom_of_foundation : Zermelo Axiom.foundation
  | axiom_of_separation (φ : SyntacticSemiformula ℒₛₑₜ 1) : Zermelo (Axiom.separationSchema φ)

notation "𝗭" => Zermelo

namespace Zermelo

instance : 𝗘𝗤 ⪯ 𝗭 := Entailment.WeakerThan.ofSubset Zermelo.axiom_of_equality

variable {V : Type*} [SetStructure V]

scoped instance : HasSubset V := ⟨fun x y ↦ ∀ z ∈ x, z ∈ y⟩

lemma subset_def {a b : V} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b := by rfl

lemma Subset.defined_isSubsetOf : ℒₛₑₜ-relation[V] Subset via isSubsetOf := fun v ↦ by simp [isSubsetOf, subset_def]

instance Subset.definable : ℒₛₑₜ-relation[V] Subset := defined_isSubsetOf.to_definable

def IsEmpty (a : V) : Prop := ∀ x, x ∉ a

lemma IsEmpty.not_mem {a x : V} (h : IsEmpty a) : x ∉ a := h x

lemma IsEmpty.defined_isEmpty : ℒₛₑₜ-predicate[V] IsEmpty via isEmpty := fun v ↦ by simp [isEmpty, IsEmpty]

instance IsEmpty.definable : ℒₛₑₜ-predicate[V] IsEmpty := defined_isEmpty.to_definable

def IsNonempty (a : V) : Prop := ∃ x, x ∈ a

lemma IsNonempty.defined_isNonempty : ℒₛₑₜ-predicate[V] IsNonempty via isNonempty := fun v ↦ by simp [isNonempty, IsNonempty]

instance IsNonempty.definable : ℒₛₑₜ-predicate[V] IsNonempty := defined_isNonempty.to_definable

@[simp] lemma not_isEmpty_iff_isNonempty {x : V} :
    ¬IsEmpty x ↔ IsNonempty x := by simp [IsEmpty, IsNonempty]

@[simp] lemma not_isNonempty_iff_isEmpty {x : V} :
    ¬IsNonempty x ↔ IsEmpty x := by simp [IsEmpty, IsNonempty]

variable [Nonempty V] [V ⊧ₘ* 𝗭]

/-! ## Axiom of extentionality -/

lemma mem_ext_iff {x y : V} : x = y ↔ ∀ z, z ∈ x ↔ z ∈ y  := by
  have := by simpa [models_iff, Axiom.extentionality] using ModelsTheory.models V Zermelo.axiom_of_extentionality
  exact this x y

alias ⟨_, mem_ext⟩ := mem_ext_iff

attribute [ext] mem_ext

lemma subset_antisymm {x y : V} (hxy : x ⊆ y) (hyx : y ⊆ x) : x = y := by
  ext z; constructor
  · exact hxy z
  · exact hyx z

/-! ## Axiom of empty set -/

lemma emptyset_exists : ∃ e : V, IsEmpty e := by simpa [models_iff] using ModelsTheory.models V Zermelo.axiom_of_empty_set

lemma emptyset_existsUnique : ∃! e : V, IsEmpty e := by
  rcases emptyset_exists (V := V) with ⟨e, he⟩
  apply ExistsUnique.intro e he
  intro x hx
  ext y
  simp [hx.not_mem, he.not_mem]

open Classical

noncomputable scoped instance : EmptyCollection V := ⟨Classical.choose! emptyset_existsUnique⟩

@[simp] lemma IsEmpty.emptyset : IsEmpty (∅ : V) := Classical.choose!_spec emptyset_existsUnique

@[simp] lemma not_mem_emptyset {x} : x ∉ (∅ : V) := IsEmpty.emptyset.not_mem

lemma eq_empty_iff_isEmpty {x : V} :
    x = ∅ ↔ IsEmpty x := ⟨by rintro rfl; simp, by intro h; ext; simp[h.not_mem]⟩

lemma ne_empty_iff_isNonempty {x : V} :
    x ≠ ∅ ↔ IsNonempty x := by simp [eq_empty_iff_isEmpty]

/-! ## Axiom of pairing -/

lemma pairing_exists : ∀ x y : V, ∃ z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  simpa [models_iff, Axiom.pairing] using ModelsTheory.models V Zermelo.axiom_of_pairing

lemma pairing_existsUnique (x y : V) : ∃! z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y  := by
  rcases pairing_exists x y with ⟨p, hp⟩
  apply ExistsUnique.intro p hp
  intro q hq
  ext z; simp_all

noncomputable def doubleton (x y : V) : V := Classical.choose! (pairing_existsUnique x y)

@[simp] lemma mem_doubleton_iff {x y z : V} : z ∈ doubleton x y ↔ z = x ∨ z = y := Classical.choose!_spec (pairing_existsUnique x y) z

def doubleton.dfn : Semisentence ℒₛₑₜ 3 := “p x y. ∀ z, z ∈ p ↔ z = x ∨ z = y”

lemma doubleton.defined : ℒₛₑₜ-function₂[V] doubleton via doubleton.dfn := by
  intro v; simp [doubleton.dfn, mem_ext_iff]

instance doubleton.definable : ℒₛₑₜ-function₂[V] doubleton := doubleton.defined.to_definable

noncomputable def singleton (x : V) : V := doubleton x x

noncomputable scoped instance : Singleton V V := ⟨singleton⟩

lemma singleton_def (x : V) : ({x} : V) = doubleton x x := rfl

@[simp] lemma mem_singleton_iff {x z : V} : z ∈ ({x} : V) ↔ z = x := by simp [singleton_def]

def singleton.dfn : Semisentence ℒₛₑₜ 2 := “p x. !doubleton.dfn p x x”

lemma singleton.defined : ℒₛₑₜ-function₁[V] Singleton.singleton via singleton.dfn := by
  intro v; simp [singleton.dfn, doubleton.defined.iff]; rfl

instance singleton.definable : ℒₛₑₜ-function₁[V] Singleton.singleton := singleton.defined.to_definable

/-! ## Axiom of union -/

lemma union_exists : ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w := by
  simpa [models_iff, Axiom.union] using ModelsTheory.models V Zermelo.axiom_of_union

lemma union_existsUnique (x : V) : ∃! y : V, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w := by
  rcases union_exists x with ⟨u, hu⟩
  apply ExistsUnique.intro u hu
  intro v hv
  ext z; simp_all

noncomputable def sUnion (x : V) : V := Classical.choose! (union_existsUnique x)

prefix:110 "⋃ˢ " => sUnion

@[simp] lemma mem_sUnion_iff {x z : V} : z ∈ ⋃ˢ x ↔ ∃ y ∈ x, z ∈ y := Classical.choose!_spec (union_existsUnique x) z

def sUnion.dfn : Semisentence ℒₛₑₜ 2 := “u x. ∀ z, z ∈ u ↔ ∃ w ∈ x, z ∈ w”

lemma sUnion.defined : ℒₛₑₜ-function₁[V] sUnion via sUnion.dfn := by
  intro v; simp [sUnion.dfn, mem_sUnion_iff, mem_ext_iff]

instance sUnion.definable : ℒₛₑₜ-function₁[V] sUnion := sUnion.defined.to_definable

@[simp] lemma sUnion_emptyset_eq_emptyset : ⋃ˢ (∅ : V) = ∅ := by ext; simp

@[simp] lemma sUnion_singleton_eq (x : V) : ⋃ˢ ({x} : V) = x := by ext; simp

/-! ### Union of two sets -/

noncomputable def union (x y : V) : V := ⋃ˢ (doubleton x y)

noncomputable scoped instance : Union V := ⟨union⟩

lemma union_def (x y : V) : x ∪ y = ⋃ˢ (doubleton x y) := rfl

def union.dfn : Semisentence ℒₛₑₜ 3 := “u x y. ∀ d, !doubleton.dfn d x y → !sUnion.dfn u d”

lemma union.defined : ℒₛₑₜ-function₂[V] Union.union via union.dfn := by
  intro v; simp [union.dfn, doubleton.defined.iff, sUnion.defined.iff, union_def]

instance union.definable : ℒₛₑₜ-function₂[V] Union.union := union.defined.to_definable

@[simp] lemma mem_union_iff {x y z : V} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by simp [union_def]

@[simp] lemma union_self_eq (x : V) : x ∪ x = x := by ext; simp

lemma union_comm (x y : V) : x ∪ y = y ∪ x := by ext; simp; tauto

lemma union_assoc (x y z : V) : (x ∪ y) ∪ z = x ∪ (y ∪ z) := by ext; simp; tauto

@[simp] lemma union_empty (x : V) : x ∪ ∅ = x := by ext; simp

@[simp] lemma empty_union (x : V) : ∅ ∪ x = x := by ext; simp

/-! ### Insert -/

noncomputable def insert (x y : V) : V := {x} ∪ y

noncomputable scoped instance : Insert V V := ⟨insert⟩

lemma insert_def (x y : V) : Insert.insert x y = {x} ∪ y := rfl

def insert.dfn : Semisentence ℒₛₑₜ 3 := “u x y. ∀ s, !singleton.dfn s x → !union.dfn u s y”

lemma insert.defined : ℒₛₑₜ-function₂[V] Insert.insert via insert.dfn := by
  intro v; simp [insert.dfn, singleton.defined.iff, union.defined.iff, insert_def]

instance insert.definable : ℒₛₑₜ-function₂[V] Insert.insert := insert.defined.to_definable

@[simp] lemma mem_insert {x y z : V} : z ∈ Insert.insert x y ↔ z = x ∨ z ∈ y := by simp [insert_def]

@[simp] lemma insert_empty_eq (x : V) : (Insert.insert x ∅ : V) = {x} := by ext; simp

lemma union_insert (x y : V) : x ∪ Insert.insert y z = Insert.insert y (x ∪ z) := by ext; simp; tauto

lemma unordered_pair_eq_doubleton (x y : V) : {x, y} = doubleton x y := by ext; simp

@[simp] lemma sUnion_insert (x y : V) : ⋃ˢ Insert.insert x y = x ∪ ⋃ˢ y := by ext; simp

/-! ## Aussonderungsaxiom -/

lemma separation_exists_eval (x : V) (φ : Semiformula ℒₛₑₜ V 1) : ∃ y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ Semiformula.Evalm V ![z] id φ := by
  have : Inhabited V := inhabited_of_nonempty inferInstance
  let f := φ.enumarateFVar
  let ψ := (Rew.rewriteMap φ.idxOfFVar) ▹ φ
  have := by simpa [models_iff, Semiformula.eval_close₀, Axiom.separationSchema] using ModelsTheory.models V (Zermelo.axiom_of_separation ψ)
  simpa [ψ, f, Semiformula.eval_rewriteMap, Matrix.constant_eq_singleton] using this f x

lemma separation_exists (x : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P) : ∃ y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ P z := by
  rcases hP with ⟨φ, hP⟩
  simpa [hP.iff] using separation_exists_eval x φ

lemma separation_existsUnique (x : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P) : ∃! y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ P z := by
  rcases separation_exists x P hP with ⟨s, hs⟩
  apply ExistsUnique.intro s hs
  intro u hu
  ext; simp_all

noncomputable def sep (x : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P) : V := Classical.choose! (separation_existsUnique x P hP)

@[simp] lemma mem_sep_iff {P : V → Prop} {hP : ℒₛₑₜ-predicate P} {z x : V} :
    z ∈ sep x P hP ↔ z ∈ x ∧ P z := Classical.choose!_spec (separation_existsUnique x P hP) z

@[simp] lemma sep_subset {P : V → Prop} {hP : ℒₛₑₜ-predicate P} {x : V} :
    sep x P hP ⊆ x := by intro z; simp; tauto

section set_notation

open Lean Elab Term Meta

syntax (name := internalSetBuilder) "{" binderIdent " ∈ " term " ; " term "}" : term

@[term_elab internalSetBuilder]
def elabInternalSetBuilder : TermElab
  | `({ $x:ident ∈ $s ; $p }), expectedType? => do
    elabTerm (← `(sep $s (fun $x:ident ↦ $p) (by definability))) expectedType?
  | _, _ => throwUnsupportedSyntax

@[app_unexpander sep]
def sep.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $s $P $_) =>
    match P with
    | `(fun $x:ident ↦ $p) => `({ $x:ident ∈ $s ; $p })
    | _ => throw ()
  | _ => throw ()

end set_notation

/-! ### Intersection -/

noncomputable def sInter (x : V) : V := {z ∈ ⋃ˢ x ; ∀ y ∈ x, z ∈ y}

prefix:110 "⋂ˢ " => sInter

lemma mem_sInter_iff {x : V} : z ∈ ⋂ˢ x ↔ z ∈ ⋃ˢ x ∧ ∀ y ∈ x, z ∈ y := by simp [sInter]

lemma IsNenempty.mem_sInter_iff {x : V} (hx : IsNonempty x) : z ∈ ⋂ˢ x ↔ ∀ y ∈ x, z ∈ y := by
  simp only [Zermelo.mem_sInter_iff, mem_sUnion_iff, and_iff_right_iff_imp]
  rcases hx with ⟨v, hv⟩
  grind only

@[simp] lemma sInter_empty_eq : ⋂ˢ (∅ : V) = ∅ := by ext; simp [mem_sInter_iff]

end Zermelo

end LO
