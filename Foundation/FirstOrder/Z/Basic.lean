import Foundation.FirstOrder.SetTheory.Axioms
import Foundation.Vorspiel.ExistsUnique

/-!
# Zermelo set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth"
-/

namespace LO

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

instance Subset.defined_isSubsetOf : ℒₛₑₜ-relation[V] Subset via isSubsetOf :=
  ⟨fun v ↦ by simp [isSubsetOf, subset_def]⟩

instance Subset.definable : ℒₛₑₜ-relation[V] Subset := defined_isSubsetOf.to_definable

@[simp, refl] lemma subset_refl (x : V) : x ⊆ x := by simp [subset_def]

@[simp, trans] lemma subset_trans {x y z : V} : x ⊆ y → y ⊆ z → x ⊆ z := fun hxy hyz v hv ↦ hyz v (hxy v hv)

instance : IsRefl V Subset := ⟨subset_refl⟩

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

def SSubset.dfn : Semisentence ℒₛₑₜ 2 := “x y. x ⊆ y ∧ x ≠ y”

instance SSubset.defined : ℒₛₑₜ-relation[V] SSubset via SSubset.dfn := ⟨fun v ↦ by simp [ssubset_def, SSubset.dfn]⟩

instance SSubset.definable : ℒₛₑₜ-relation[V] SSubset := SSubset.defined.to_definable

@[simp] lemma SSubset.irrefl (x : V) : ¬x ⊊ x := by simp [ssubset_def]

lemma SSubset.subset {x y : V} : x ⊊ y → x ⊆ y := fun h ↦ h.1

variable [Nonempty V] [V ⊧ₘ* 𝗭]

/-! ## Axiom of extentionality -/

lemma mem_ext_iff {x y : V} : x = y ↔ ∀ z, z ∈ x ↔ z ∈ y  := by
  have := by simpa [models_iff, Axiom.extentionality] using ModelsTheory.models V Zermelo.axiom_of_extentionality
  exact this x y

alias ⟨_, mem_ext⟩ := mem_ext_iff

attribute [ext] mem_ext

@[grind] lemma subset_antisymm {x y : V} (hxy : x ⊆ y) (hyx : y ⊆ x) : x = y := by
  ext z; constructor
  · exact hxy z
  · exact hyx z

lemma SSubset.iff {x y : V} : x ⊊ y ↔ x ⊆ y ∧ ∃ z ∈ y, z ∉ x := by
  constructor
  · rintro ⟨ss, eq⟩
    refine ⟨ss, ?_⟩
    contrapose eq
    push_neg at *
    apply subset_antisymm ss eq
  · rintro ⟨ss, ⟨z, hzy, hzx⟩⟩
    refine ⟨ss, ?_⟩
    rintro rfl
    contradiction

lemma SSubset.exists_not_mem {x y : V} (hxy : x ⊊ y) : ∃ z ∈ y, z ∉ x := (SSubset.iff.mp hxy).2

lemma SSubset.of_subset_of_not_mem_of_mem {x y z : V} (ss : x ⊆ y) (hzx : z ∉ x) (hzy : z ∈ y) : x ⊊ y :=
  SSubset.iff.mpr ⟨ss, z, hzy, hzx⟩

/-! ## Axiom of empty set -/

lemma empty_exists : ∃ e : V, IsEmpty e := by simpa [models_iff] using ModelsTheory.models V Zermelo.axiom_of_empty_set

lemma empty_existsUnique : ∃! e : V, IsEmpty e := by
  rcases empty_exists (V := V) with ⟨e, he⟩
  apply ExistsUnique.intro e he
  intro x hx
  ext y
  simp [hx.not_mem, he.not_mem]

open Classical

noncomputable scoped instance : EmptyCollection V := ⟨Classical.choose! empty_existsUnique⟩

@[simp] lemma IsEmpty.empty : IsEmpty (∅ : V) := Classical.choose!_spec empty_existsUnique

@[simp] lemma not_mem_empty {x} : x ∉ (∅ : V) := IsEmpty.empty.not_mem

@[simp] lemma isEmpty_iff_eq_empty {x : V} :
    IsEmpty x ↔ x = ∅ := ⟨by intro h; ext; simp[h.not_mem], by rintro rfl; simp⟩

@[simp] lemma ne_empty_iff_isNonempty {x : V} :
    x ≠ ∅ ↔ IsNonempty x := by simp [←isEmpty_iff_eq_empty]

lemma eq_empty_or_isNonempty (x : V) : x = ∅ ∨ IsNonempty x := by
  by_cases hx : x = ∅
  · simp_all
  · right; exact ne_empty_iff_isNonempty.mp hx

@[simp] lemma empty_subset (x : V) : ∅ ⊆ x := by simp [subset_def]

@[simp] lemma subset_empty_iff_eq_empty {x : V} : x ⊆ ∅ ↔ x = ∅ := by simp [mem_ext_iff, subset_def]

/-! ## Axiom of pairing -/

lemma pairing_exists : ∀ x y : V, ∃ z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  simpa [models_iff, Axiom.pairing] using ModelsTheory.models V Zermelo.axiom_of_pairing

lemma pairing_existsUnique (x y : V) : ∃! z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  rcases pairing_exists x y with ⟨p, hp⟩
  apply ExistsUnique.intro p hp
  intro q hq
  ext z; simp_all

noncomputable def doubleton (x y : V) : V := Classical.choose! (pairing_existsUnique x y)

@[simp] lemma mem_doubleton_iff {x y z : V} : z ∈ doubleton x y ↔ z = x ∨ z = y := Classical.choose!_spec (pairing_existsUnique x y) z

def doubleton.dfn : Semisentence ℒₛₑₜ 3 := “p x y. ∀ z, z ∈ p ↔ z = x ∨ z = y”

instance doubleton.defined : ℒₛₑₜ-function₂[V] doubleton via doubleton.dfn :=
  ⟨by intro v; simp [doubleton.dfn, doubleton]⟩

instance doubleton.definable : ℒₛₑₜ-function₂[V] doubleton := doubleton.defined.to_definable

@[simp] instance doubleton_isNonempty (x y : V) : IsNonempty (doubleton x y) := ⟨x, by simp⟩

noncomputable def singleton (x : V) : V := doubleton x x

noncomputable scoped instance : Singleton V V := ⟨singleton⟩

lemma singleton_def (x : V) : ({x} : V) = doubleton x x := rfl

@[simp] lemma mem_singleton_iff {x z : V} : z ∈ ({x} : V) ↔ z = x := by simp [singleton_def]

def singleton.dfn : Semisentence ℒₛₑₜ 2 := “p x. !doubleton.dfn p x x”

instance singleton.defined : ℒₛₑₜ-function₁[V] Singleton.singleton via singleton.dfn :=
  ⟨by intro v; simp [singleton.dfn]; rfl⟩

instance singleton.definable : ℒₛₑₜ-function₁[V] Singleton.singleton := singleton.defined.to_definable

@[simp] instance singleton_isNonempty (x : V) : IsNonempty ({x} : V) := ⟨x, by simp⟩

@[simp] lemma singleton_subset_iff_mem {x y : V} : {x} ⊆ y ↔ x ∈ y := by simp [subset_def]

@[simp] lemma singleton_ext_iff {x y : V} : ({x} : V) = {y} ↔ x = y := by
  simp [mem_ext_iff (x := {x})]

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

lemma mem_sUnion_iff {x z : V} : z ∈ ⋃ˢ x ↔ ∃ y ∈ x, z ∈ y := Classical.choose!_spec (union_existsUnique x) z

def sUnion.dfn : Semisentence ℒₛₑₜ 2 := “u x. ∀ z, z ∈ u ↔ ∃ w ∈ x, z ∈ w”

instance sUnion.defined : ℒₛₑₜ-function₁[V] sUnion via sUnion.dfn :=
  ⟨by intro v; simp [sUnion.dfn, mem_sUnion_iff, mem_ext_iff]⟩

instance sUnion.definable : ℒₛₑₜ-function₁[V] sUnion := sUnion.defined.to_definable

@[simp] lemma sUnion_empty_eq_empty : ⋃ˢ (∅ : V) = ∅ := by ext; simp [mem_sUnion_iff]

@[simp] lemma sUnion_singleton_eq (x : V) : ⋃ˢ ({x} : V) = x := by ext; simp [mem_sUnion_iff]

@[simp] lemma IsNonempty_sUnion_iff {x : V} : IsNonempty (⋃ˢ x) ↔ ∃ y ∈ x, IsNonempty y := by
  simp only [isNonempty_def, mem_sUnion_iff]
  grind

lemma subset_sUnion_of_mem {x y : V} (h : x ∈ y) : x ⊆ ⋃ˢ y := fun z hz ↦ by
  simp only [mem_sUnion_iff]; grind

/-! ### Union of two sets -/

noncomputable def union (x y : V) : V := ⋃ˢ (doubleton x y)

noncomputable scoped instance : Union V := ⟨union⟩

lemma union_def (x y : V) : x ∪ y = ⋃ˢ (doubleton x y) := rfl

def union.dfn : Semisentence ℒₛₑₜ 3 := “u x y. ∀ d, !doubleton.dfn d x y → !sUnion.dfn u d”

instance union.defined : ℒₛₑₜ-function₂[V] Union.union via union.dfn :=
  ⟨by intro v; simp [union.dfn, union_def]⟩

instance union.definable : ℒₛₑₜ-function₂[V] Union.union := union.defined.to_definable

@[simp] lemma mem_union_iff {x y z : V} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by simp [union_def, mem_sUnion_iff]

@[simp] lemma union_self_eq (x : V) : x ∪ x = x := by ext; simp

lemma union_comm (x y : V) : x ∪ y = y ∪ x := by ext; simp; tauto

lemma union_assoc (x y z : V) : (x ∪ y) ∪ z = x ∪ (y ∪ z) := by ext; simp; tauto

@[simp] lemma union_empty (x : V) : x ∪ ∅ = x := by ext; simp

@[simp] lemma empty_union (x : V) : ∅ ∪ x = x := by ext; simp

@[simp] lemma IsNonempty_union_iff {x y : V} : IsNonempty (x ∪ y) ↔ IsNonempty x ∨ IsNonempty y := by
  simp only [isNonempty_def, mem_union_iff]; grind

@[simp] lemma subset_union_left (x y : V) : x ⊆ x ∪ y := fun z hz ↦ by simp [hz]

@[simp] lemma subset_union_right (x y : V) : y ⊆ x ∪ y := fun z hz ↦ by simp [hz]

@[simp] lemma union_eq_iff_right {x y : V} : x ∪ y = x ↔ y ⊆ x := by simp [mem_ext_iff, subset_def]

@[simp] lemma union_eq_iff_left {x y : V} : x ∪ y = y ↔ x ⊆ y := by simp [mem_ext_iff, subset_def]

/-! ### Insert -/

protected noncomputable def insert (x y : V) : V := {x} ∪ y

noncomputable scoped instance : Insert V V := ⟨Zermelo.insert⟩

lemma insert_def (x y : V) : insert x y = {x} ∪ y := rfl

def insert.dfn : Semisentence ℒₛₑₜ 3 := “u x y. ∀ s, !singleton.dfn s x → !union.dfn u s y”

instance insert.defined : ℒₛₑₜ-function₂[V] insert via insert.dfn :=
  ⟨by intro v; simp [insert.dfn, insert_def]⟩

instance insert.definable : ℒₛₑₜ-function₂[V] insert := insert.defined.to_definable

@[simp] lemma mem_insert {x y z : V} : z ∈ insert x y ↔ z = x ∨ z ∈ y := by simp [insert_def]

@[simp] lemma insert_empty_eq (x : V) : (insert x ∅ : V) = {x} := by ext; simp

lemma union_insert (x y : V) : x ∪ insert y z = insert y (x ∪ z) := by ext; simp; tauto

lemma pair_eq_doubleton (x y : V) : {x, y} = doubleton x y := by ext; simp

@[simp] lemma sUnion_insert (x y : V) : ⋃ˢ insert x y = x ∪ ⋃ˢ y := by ext; simp [mem_sUnion_iff]

@[simp] lemma subset_insert (x y : V) : y ⊆ insert x y := by simp [insert_def]

@[simp] instance insert_isNonempty (x y : V) : IsNonempty (insert x y) := ⟨x, by simp⟩

@[simp] lemma intsert_union (x y z : V) :
    insert x y ∪ z = insert x (y ∪ z) := by
  ext; simp only [mem_union_iff, mem_insert]; grind

@[simp] lemma singleton_inter (x y : V) :
    {x} ∪ y = insert x y := by
  ext; simp

@[simp, grind] lemma insert_eq_self_of_mem {x y : V} (hx : x ∈ y) : insert x y = y := by
  ext; simp only [mem_insert, or_iff_right_iff_imp]; grind

/-! ## Axiom of power set -/

lemma power_exists : ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ z ⊆ x := by
  simpa [models_iff, Axiom.power] using ModelsTheory.models V Zermelo.axiom_of_power_set

lemma power_existsUnique (x : V) : ∃! y : V, ∀ z, z ∈ y ↔ z ⊆ x := by
  rcases power_exists x with ⟨p, hp⟩
  apply ExistsUnique.intro p hp
  intro q hq
  ext; simp_all

noncomputable def power (x : V) : V := Classical.choose! (power_existsUnique x)

prefix:110 "℘ " => power

@[simp] lemma mem_power_iff {x z : V} : z ∈ ℘ x ↔ z ⊆ x := Classical.choose!_spec (power_existsUnique x) z

def power.dfn : Semisentence ℒₛₑₜ 2 := “p x. ∀ z, z ∈ p ↔ z ⊆ x”

instance power.defined : ℒₛₑₜ-function₁[V] power via power.dfn :=
  ⟨by intro v; simp [power.dfn, power]⟩

instance power.definable : ℒₛₑₜ-function₁[V] power := power.defined.to_definable

@[simp] lemma empty_mem_power (x : V) : ∅ ∈ ℘ x := by simp [mem_power_iff]

@[simp] lemma self_mem_power (x : V) : x ∈ ℘ x := by simp [mem_power_iff]

@[simp] lemma power_empty : ℘ (∅ : V) = {∅} := by ext; simp [mem_power_iff]

@[simp] instance power_nonempty (x : V) : IsNonempty (℘ x) := ⟨x, by simp⟩

/-! ## Aussonderungsaxiom -/

lemma separation_exists_eval (x : V) (φ : Semiformula ℒₛₑₜ V 1) : ∃ y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ Semiformula.Evalm V ![z] id φ := by
  have : Inhabited V := inhabited_of_nonempty inferInstance
  let f := φ.enumarateFVar
  let ψ := (Rew.rewriteMap φ.idxOfFVar) ▹ φ
  have := by simpa [models_iff, Semiformula.eval_univCl, Axiom.separationSchema] using ModelsTheory.models V (Zermelo.axiom_of_separation ψ)
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

@[simp] lemma sep_empty_eq (P : V → Prop) (hP : ℒₛₑₜ-predicate P) :
    sep ∅ P hP = ∅ := by ext; simp

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

lemma mem_sInter_iff {x : V} : z ∈ ⋂ˢ x ↔ IsNonempty x ∧ ∀ y ∈ x, z ∈ y := by
  simp only [sInter, mem_sep_iff, mem_sUnion_iff, and_congr_left_iff, isNonempty_def]
  grind

def sInter.dfn : Semisentence ℒₛₑₜ 2 := “u x. ∀ z, z ∈ u ↔ !isNonempty x ∧ ∀ y ∈ x, z ∈ y”

instance sInter.defined : ℒₛₑₜ-function₁[V] sInter via sInter.dfn :=
  ⟨by intro v; simp [sInter.dfn, mem_ext_iff, mem_sInter_iff]⟩

instance sInter.definable : ℒₛₑₜ-function₁[V] sInter := sInter.defined.to_definable

@[simp] lemma mem_sInter_iff_of_nonempty {x : V} [hx : IsNonempty x] :
    z ∈ ⋂ˢ x ↔ ∀ y ∈ x, z ∈ y := by
  simp [Zermelo.mem_sInter_iff, hx]

@[simp] lemma sInter_empty_eq : ⋂ˢ (∅ : V) = ∅ := by ext; simp [mem_sInter_iff]

@[simp] lemma sInter_singleton (x : V) : ⋂ˢ {x} = x := by ext; simp [mem_sInter_iff_of_nonempty]

lemma sInter_subset_of_mem_of_nonempty {x y : V} [IsNonempty y] (h : x ∈ y) : ⋂ˢ y ⊆ x := by
  intro z hz
  simp only [mem_sInter_iff_of_nonempty] at hz
  grind

@[simp] lemma subset_sInter_iff_of_nonempty {x y : V} [IsNonempty y] : x ⊆ ⋂ˢ y ↔ ∀ z ∈ y, x ⊆ z := by
  constructor
  · intro h z hzy
    exact subset_trans h (sInter_subset_of_mem_of_nonempty hzy)
  · intro h z hz
    simp only [mem_sInter_iff_of_nonempty]
    intro v hvy
    exact h v hvy z hz

/-! #### Intersection of two sets -/

noncomputable def inter (x y : V) : V := ⋂ˢ {x, y}

noncomputable instance : Inter V := ⟨inter⟩

lemma inter_def (x y : V) : x ∩ y = ⋂ˢ {x, y} := rfl

@[simp] lemma mem_inter_iff {x y z : V} : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := by
  simp [inter_def, mem_sInter_iff_of_nonempty]

def inter.dfn : Semisentence ℒₛₑₜ 3 := “u x y. ∀ z, z ∈ u ↔ z ∈ x ∧ z ∈ y”

instance inter.defined : ℒₛₑₜ-function₂[V] Inter.inter via inter.dfn := ⟨by intro v; simp [inter.dfn, mem_ext_iff]⟩

instance inter.definable : ℒₛₑₜ-function₂[V] Inter.inter := inter.defined.to_definable

@[simp] lemma inter_self (x : V) : x ∩ x = x := by ext; simp

lemma inter_comm (x y : V) : x ∩ y = y ∩ x := by ext; simp; tauto

lemma inter_assoc (x y z : V) : (x ∩ y) ∩ z = x ∩ (y ∩ z) := by ext; simp; tauto

@[simp] lemma inter_empty (x : V) : x ∩ ∅ = ∅ := by ext; simp

@[simp] lemma empty_inter (x : V) : ∅ ∩ x = ∅ := by ext; simp

@[simp] lemma sInter_insert (x y : V) [hy : IsNonempty y] : ⋂ˢ insert x y = x ∩ ⋂ˢ y := by
  ext; simp [*, mem_sInter_iff_of_nonempty]

@[simp, grind] lemma intsert_inter_of_mem (x y z : V) (hx : x ∈ z) :
    insert x y ∩ z = insert x (y ∩ z) := by
  ext; simp only [inter_comm, mem_inter_iff, mem_insert]; grind

@[simp, grind] lemma intsert_inter_of_not_mem (x y z : V) (hx : x ∉ z) :
    insert x y ∩ z = y ∩ z := by
  ext; simp only [inter_comm, mem_inter_iff, mem_insert]; grind

@[simp, grind] lemma singleton_inter_of_mem {x y : V} (hx : x ∈ y) :
    {x} ∩ y = {x} := by
  ext
  simp only [inter_comm, mem_inter_iff, mem_singleton_iff,
    and_iff_right_iff_imp]; grind

@[simp, grind] lemma singleton_inter_of_not_mem {x y : V} (hx : x ∉ y) :
    {x} ∩ y = ∅ := by
  ext; simp only [inter_comm, mem_inter_iff, mem_singleton_iff, not_mem_empty, iff_false, not_and]
  grind

/-! ### Set difference -/

noncomputable def sdiff (x y : V) : V := {z ∈ x ; z ∉ y}

noncomputable instance : SDiff V := ⟨sdiff⟩

lemma sdiff_def (x y : V) : x \ y = {z ∈ x ; z ∉ y} := rfl

@[simp] lemma mem_sdiff_iff {x y z : V} : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y := by simp [sdiff_def]

def sdiff.dfn : Semisentence ℒₛₑₜ 3 := “d x y. ∀ z, z ∈ d ↔ z ∈ x ∧ z ∉ y”

instance sdiff.defined : ℒₛₑₜ-function₂[V] SDiff.sdiff via sdiff.dfn := ⟨by intro v; simp [sdiff.dfn, mem_ext_iff]⟩

instance sdiff.definable : ℒₛₑₜ-function₂[V] SDiff.sdiff := sdiff.defined.to_definable

@[simp] lemma sdiff_empty (x : V) : x \ ∅ = x := by ext; simp

@[simp] lemma empty_sdiff (x : V) : ∅ \ x = ∅ := by ext; simp

@[simp, grind] lemma singleton_sdiff_of_mem {x z : V} (hx : x ∈ z) :
    {x} \ z = ∅ := by
  ext
  simp only [mem_sdiff_iff, mem_singleton_iff, not_mem_empty,
    iff_false, not_and, Decidable.not_not]; grind

@[simp, grind] lemma singleton_sdiff_of_not_mem {x z : V} (hx : x ∉ z) :
    {x} \ z = {x} := by
  ext; simp only [mem_sdiff_iff, mem_singleton_iff, and_iff_left_iff_imp]; grind

@[simp, grind] lemma insert_sdiff_of_mem {x y z : V} (hx : x ∈ z) :
    insert x y \ z = y \ z := by
  ext; simp only [mem_sdiff_iff, mem_insert, and_congr_left_iff, or_iff_right_iff_imp]; grind

@[simp, grind] lemma insert_sdiff_of_not_mem {x y z : V} (hx : x ∉ z) :
    insert x y \ z = insert x (y \ z) := by
  ext; simp only [mem_sdiff_iff, mem_insert]; grind

lemma isNonempty_sdiff_of_ssubset {x y : V} : x ⊊ y → IsNonempty (y \ x) := by
  intro h
  rcases h.exists_not_mem with ⟨z, hzy, hzx⟩
  exact ⟨z, by simp_all⟩

/-! ### Kuratowski's ordered pair -/

noncomputable def kpair (x y : V) : V := {{x}, {x, y}}

/-- `⟨x, y, z, ...⟩ₖ` notation for `kpair` -/
syntax "⟨" term,* "⟩ₖ" : term

macro_rules
  | `(⟨$term:term, $terms:term,*⟩ₖ) => `(kpair $term ⟨$terms,*⟩ₖ)
  | `(⟨$term:term⟩ₖ) => `($term)

@[app_unexpander kpair]
def pairUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term $term2) => `(⟨$term, $term2⟩ₖ)
  | _ => throw ()


noncomputable def kpair.π₁ (z : V) : V := ⋃ˢ ⋂ˢ z

noncomputable def kpair.π₂ (z : V) : V := ⋃ˢ {x ∈ ⋃ˢ z; x ∈ ⋂ˢ z → ⋃ˢ z = ⋂ˢ z}

def kpair.dfn : Semisentence ℒₛₑₜ 3 :=
  “k x y. ∀ x', !singleton.dfn x' x → ∀ z, !doubleton.dfn z x y → !doubleton.dfn k x' z”

instance kpair.defined : ℒₛₑₜ-function₂[V] kpair via kpair.dfn :=
  ⟨by intro v; simp [kpair.dfn, kpair, ←pair_eq_doubleton]⟩

instance kpair.definable : ℒₛₑₜ-function₂[V] kpair := kpair.defined.to_definable

def kpair.π₁.dfn : Semisentence ℒₛₑₜ 2 := “p₁ x. ∀ i, !sInter.dfn i x → !sUnion.dfn p₁ i”

instance kpair.π₁.defined : ℒₛₑₜ-function₁[V] kpair.π₁ via kpair.π₁.dfn :=
  ⟨by intro v; simp [kpair.π₁.dfn, π₁]⟩

instance kpair.π₁.definable : ℒₛₑₜ-function₁[V] kpair.π₁ := kpair.π₁.defined.to_definable

def kpair.π₂.dfn : Semisentence ℒₛₑₜ 2 :=
  “p₂ x. ∀ u, !sUnion.dfn u x → ∀ i, !sInter.dfn i x → ∀ s, (∀ z, z ∈ s ↔ (z ∈ u ∧ (z ∈ i → u = i))) → !sUnion.dfn p₂ s”

instance kpair.π₂.defined : ℒₛₑₜ-function₁[V] kpair.π₂ via kpair.π₂.dfn :=
  ⟨by intro v
      let u := ⋃ˢ v 1
      let i := ⋂ˢ v 1
      suffices (∀ s, (∀ z, z ∈ s ↔ z ∈ u ∧ (z ∈ i → u = i)) → v 0 = ⋃ˢ s) ↔ v 0 = ⋃ˢ {x ∈ u ; x ∈ i → u = i} by
        simpa [kpair.π₂.dfn, π₂] using this
      constructor
      · intro h
        apply h
        intro z; simp
      · intro e s hs; rw [e]
        congr; ext
        simp only [mem_sep_iff]; grind⟩

instance kpair.π₂.definable : ℒₛₑₜ-function₁[V] kpair.π₂ := kpair.π₂.defined.to_definable

@[grind, simp] lemma kpair.π₁_kpair (x y : V) :
    π₁ ⟨x, y⟩ₖ = x := by simp [π₁, kpair]

@[grind, simp] lemma kpair.π₂_kpair (x y : V) :
    π₂ ⟨x, y⟩ₖ = y := calc
  π₂ ⟨x, y⟩ₖ = ⋃ˢ {z ∈ {x, y} ; z = x → ({x, y} : V) = {x}} := by simp [π₂, kpair]
  _              = ⋃ˢ {y} := by
    congr; ext z
    suffices (z = x ∨ z = y) ∧ (z = x → y = x) ↔ z = y by simpa [mem_ext_iff (x := {x, y})]
    grind
  _              = y := by simp

lemma kpair_inj {x₁ x₂ y₁ y₂ : V} :
    ⟨x₁, y₁⟩ₖ = ⟨x₂, y₂⟩ₖ → x₁ = x₂ ∧ y₁ = y₂ := by
  intro h
  constructor
  · calc x₁ = kpair.π₁ ⟨x₁, y₁⟩ₖ := by simp
    _       = kpair.π₁ ⟨x₂, y₂⟩ₖ := by rw [h]
    _       = x₂                 := by simp
  · calc y₁ = kpair.π₂ ⟨x₁, y₁⟩ₖ := by simp
    _       = kpair.π₂ ⟨x₂, y₂⟩ₖ := by rw [h]
    _       = y₂                 := by simp

@[simp, grind =] lemma kpair_iff {x₁ x₂ y₁ y₂ : V} :
    ⟨x₁, y₁⟩ₖ = ⟨x₂, y₂⟩ₖ ↔ x₁ = x₂ ∧ y₁ = y₂ :=
  ⟨kpair_inj, by rintro ⟨rfl, rfl⟩; rfl⟩

/-! ### Product -/

noncomputable def prod (X Y : V) : V := {z ∈ ℘ ℘ (X ∪ Y) ; ∃ x ∈ X, ∃ y ∈ Y, z = ⟨x, y⟩ₖ}

infix:60 " ×ˢ " => prod

lemma mem_prod_iff {X Y z : V} : z ∈ X ×ˢ Y ↔ ∃ x ∈ X, ∃ y ∈ Y, z = ⟨x, y⟩ₖ := by
  suffices ∀ x ∈ X, ∀ y ∈ Y, z = ⟨x, y⟩ₖ → z ∈ ℘ ℘ (X ∪ Y) by simpa [prod]
  rintro x hx y hy rfl
  simp_all [mem_power_iff, subset_def, kpair]

def prod.dfn : Semisentence ℒₛₑₜ 3 := “p X Y. ∀ z, z ∈ p ↔ ∃ x ∈ X, ∃ y ∈ Y, !kpair.dfn z x y”

instance prod.defined : ℒₛₑₜ-function₂[V] prod via prod.dfn :=
  ⟨by intro v; simp [prod.dfn, mem_ext_iff, mem_prod_iff]⟩

instance prod.definable : ℒₛₑₜ-function₂[V] prod := prod.defined.to_definable

@[simp] lemma prod_empty (x : V) : x ×ˢ ∅ = ∅ := by ext; simp [mem_prod_iff]

@[simp] lemma empty_prod (x : V) : ∅ ×ˢ x = ∅ := by ext; simp [mem_prod_iff]

@[simp] lemma kpair_mem_iff {x y X Y : V} : ⟨x, y⟩ₖ ∈ X ×ˢ Y ↔ x ∈ X ∧ y ∈ Y := by
  simp [mem_prod_iff]

lemma prod_subset_prod_of_subset {X₁ X₂ Y₁ Y₂ : V} (hX : X₁ ⊆ X₂) (hY : Y₁ ⊆ Y₂) : X₁ ×ˢ Y₁ ⊆ X₂ ×ˢ Y₂ := by
  intro p hp
  have : ∃ x ∈ X₁, ∃ y ∈ Y₁, p = ⟨x, y⟩ₖ := by simpa [mem_prod_iff] using hp
  rcases this with ⟨x, hx, y, hy, rfl⟩
  simp [hX _ hx, hY _ hy]

lemma union_prod (x y z : V) : (x ∪ y) ×ˢ z = (x ×ˢ z) ∪ (y ×ˢ z) := by
  ext v; simp only [mem_prod_iff, mem_union_iff]; grind

@[simp] lemma singleton_prod_singleton (x y : V) : ({x} ×ˢ {y} : V) = {⟨x, y⟩ₖ} := by
  ext z; simp [mem_prod_iff]

lemma insert_kpair_subset_insert_prod_insert_of_subset_prod {R X Y : V} (h : R ⊆ X ×ˢ Y) (x y : V) :
    insert ⟨x, y⟩ₖ R ⊆ insert x X ×ˢ insert y Y := by
  intro z hz
  rcases show z = ⟨x, y⟩ₖ ∨ z ∈ R by simpa using hz with (rfl | hz)
  · simp
  · exact prod_subset_prod_of_subset
      (show X ⊆ insert x X by simp) (show Y ⊆ insert y Y by simp) z (h z hz)

/-! ## Axiom of infinity -/

noncomputable def succ (x : V) : V := insert x x

lemma mem_succ_iff {x y : V} : y ∈ succ x ↔ y = x ∨ y ∈ x := by simp [succ]

abbrev succ.dfn := isSucc

instance succ.defined : ℒₛₑₜ-function₁[V] succ via succ.dfn :=
  ⟨fun v ↦ by simp [mem_succ_iff, succ.dfn, isSucc, mem_ext_iff (x := v 0)]⟩

instance succ.definable : ℒₛₑₜ-function₁[V] succ := succ.defined.to_definable

@[simp] lemma mem_succ_self (x : V) : x ∈ succ x := by simp [mem_succ_iff]

@[simp] lemma mem_subset_refl (x : V) : x ⊆ succ x := by simp [succ]

def IsInductive (x : V) : Prop := ∅ ∈ x ∧ ∀ y ∈ x, succ y ∈ x

def IsInductive.dfn : Semisentence ℒₛₑₜ 1 :=
  “x. (∀ e, !isEmpty e → e ∈ x) ∧ (∀ y ∈ x, ∀ y', !succ.dfn y' y → y' ∈ x)”

instance IsInductive.defined : ℒₛₑₜ-predicate[V] IsInductive via IsInductive.dfn :=
  ⟨fun v ↦ by simp [IsInductive, IsInductive.dfn]⟩

instance IsInductive.definable : ℒₛₑₜ-predicate[V] IsInductive := IsInductive.defined.to_definable

lemma IsInductive.zero {I : V} (hI : IsInductive I) : ∅ ∈ I := hI.1

lemma IsInductive.succ {I : V} (hI : IsInductive I) {x : V} (hx : x ∈ I) : succ x ∈ I := hI.2 x hx

lemma isInductive_exists : ∃ I : V, IsInductive I := by
  simpa [models_iff, Axiom.infinity] using ModelsTheory.models V Zermelo.axiom_of_infinity

lemma omega_existsUnique : ∃! ω : V, ∀ x, x ∈ ω ↔ ∀ I : V, IsInductive I → x ∈ I := by
  rcases isInductive_exists (V := V) with ⟨I, hI⟩
  let ω : V := {x ∈ I ; ∀ J : V, IsInductive J → x ∈ J}
  have : ∀ x, x ∈ ω ↔ ∀ I : V, IsInductive I → x ∈ I := by
    intro x; constructor
    · intro hx J hJ
      have hx : x ∈ I ∧ ∀ J : V, IsInductive J → x ∈ J := by simpa [ω] using hx
      exact hx.2 J hJ
    · intro h
      suffices x ∈ I ∧ ∀ J : V, IsInductive J → x ∈ J by simpa [ω]
      exact ⟨h I hI, h⟩
  apply ExistsUnique.intro ω this
  intros; ext; simp_all

noncomputable def ω : V := Classical.choose! (omega_existsUnique)

lemma mem_ω_iff_mem_all_inductive {x : V} :
  x ∈ (ω : V) ↔ ∀ I : V, IsInductive I → x ∈ I := Classical.choose!_spec (omega_existsUnique) x

def isω : Semisentence ℒₛₑₜ 1 := “ω. ∀ x, x ∈ ω ↔ ∀ I, !IsInductive.dfn I → x ∈ I”

instance ω.defined : ℒₛₑₜ-function₀[V] ω via isω := ⟨fun v ↦ by simp [isω, ω]⟩

@[simp] lemma empty_mem_ω : ∅ ∈ (ω : V) := mem_ω_iff_mem_all_inductive.mpr <| fun _ hI ↦ hI.zero

@[simp] instance ω_nonempty : IsNonempty (ω : V) := ⟨⟨∅, by simp⟩⟩

@[simp] lemma ω_succ_closed {x : V} : x ∈ (ω : V) → succ x ∈ (ω : V) := by
  intro hx
  apply mem_ω_iff_mem_all_inductive.mpr
  intro I hI
  exact hI.succ (mem_ω_iff_mem_all_inductive.mp hx I hI)

@[simp] lemma ω_isInductive : IsInductive (ω : V) := ⟨empty_mem_ω, fun _ ↦ ω_succ_closed⟩

lemma IsInductive.ω_subset {I : V} (hI : IsInductive I) : (ω : V) ⊆ I :=
  fun _ hx ↦ mem_ω_iff_mem_all_inductive.mp hx I hI

noncomputable def ofNat : ℕ → V
  |     0 => ∅
  | n + 1 => succ (ofNat n)

noncomputable scoped instance (n) : OfNat V n := ⟨ofNat n⟩

noncomputable scoped instance : NatCast V := ⟨ofNat⟩

lemma zero_def : (0 : V) = ∅ := rfl

lemma num_succ_def (n : ℕ) : ((n + 1 : ℕ) : V) = succ ↑n := rfl

@[simp] lemma cast_zero_def : ((0 : ℕ) : V) = 0 := rfl

@[simp] lemma cast_one_def : ((1 : ℕ) : V) = 1 := rfl

lemma one_def : (1 : V) = {0} := calc
  (1 : V) = succ ∅ := rfl
  _       = {∅} := by simp [succ]

lemma one_def' : (1 : V) = {∅} := one_def

lemma two_def : (2 : V) = {0, 1} := calc
  (2 : V) = succ 1     := rfl
  _       = insert 1 1 := by rfl
  _       = {1, 0}     := by rw [←one_def]
  _       = {0, 1}     := by ext; simp; tauto

@[simp] lemma zero_ne_one : (0 : V) ≠ (1 : V) := by
  suffices ∅ ≠ {∅} by simpa [zero_def, one_def]
  intro e
  have := mem_ext_iff.mp e ∅
  simp at this

@[simp] lemma one_ne_zero : (1 : V) ≠ (0 : V) := Ne.symm zero_ne_one

@[simp] lemma mem_two_iff (x : V) : x ∈ (2 : V) ↔ x = 0 ∨ x = 1 := by simp [two_def]

@[simp] lemma zero_mem_one : 0 ∈ (1 : V) := by simp [zero_def, one_def]

@[simp] lemma ofNat_mem_ω (n : ℕ) : ↑n ∈ (ω : V) :=
  match n with
  |     0 => by simp [zero_def]
  | n + 1 => by simp [num_succ_def, ω_succ_closed (ofNat_mem_ω n)]

@[simp] lemma zero_mem_ω : 0 ∈ (ω : V) := ofNat_mem_ω 0

@[simp] lemma one_mem_ω : 1 ∈ (ω : V) := ofNat_mem_ω 1

@[simp] lemma two_mem_ω : 2 ∈ (ω : V) := ofNat_mem_ω 2

@[elab_as_elim]
lemma naturalNumber_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (zero : P 0) (succ : ∀ x ∈ (ω : V), P x → P (succ x)) : ∀ x ∈ (ω : V), P x := by
  let p : V := {x ∈ ω ; P x}
  have : IsInductive p := by
    constructor
    · simpa [p]
    · intro x hx
      have hx : x ∈ (ω : V) ∧ P x := by simpa [p] using hx
      suffices Zermelo.succ x ∈ ω ∧ P (Zermelo.succ x) by simpa [p]
      refine ⟨ω_succ_closed hx.1, succ x hx.1 hx.2⟩
  have : ω ⊆ p := this.ω_subset
  intro x hx
  have : x ∈ (ω : V) ∧ P x := by simpa [p] using this x hx
  exact this.2

/-! ## Axiom of foundation -/

lemma foundation : ∀ x : V, [IsNonempty x] → ∃ y ∈ x, ∀ z ∈ x, z ∉ y := by
  simpa [models_iff, Axiom.foundation] using ModelsTheory.models V Zermelo.axiom_of_foundation

lemma foundation' (x : V) [IsNonempty x] : ∃ y ∈ x, x ∩ y = ∅ := by
  rcases foundation x with ⟨y, hyx, H⟩
  exact ⟨y, hyx, by ext z; simpa using H z⟩

@[simp] lemma mem_irrefl (x : V) : x ∉ x := by
  simpa using foundation ({x} : V)

lemma ne_of_mem {x y : V} : x ∈ y → x ≠ y := by
  rintro h rfl; simp_all

lemma mem_asymm {x y : V} : x ∈ y → y ∉ x := by
  intro hxy hyx
  have : y ∉ x ∨ x ∉ y := by simpa using foundation ({x, y} : V)
  rcases this with (_ | _) <;> simp_all

lemma mem_asymm₃ {x y z : V} : x ∈ y → y ∈ z → z ∉ x := by
  intro hxy hyz
  have : y ∉ x ∧ z ∉ x := by simpa [hxy, hyz] using foundation ({x, y, z} : V)
  exact this.2

@[simp] lemma ne_succ (x : V) : x ≠ succ x := by
  intro h
  have : x ∈ succ x := mem_succ_self x
  simp [←h] at this

end LO.Zermelo
