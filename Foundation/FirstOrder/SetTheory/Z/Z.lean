module

public import Foundation.FirstOrder.SetTheory.BST.BST
public import Foundation.FirstOrder.SetTheory.Z.Model

/-!
# Zermelo set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth" [Sch14]
-/

@[expose] public section

namespace FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]

instance : V↓[ℒₛₑₜ] ⊧* 𝗕𝗦𝗧 := models_of_subtheory (U := 𝗭) inferInstance

instance : V↓[ℒₛₑₜ] ⊧* 𝗦𝗘𝗣 := models_of_subtheory (U := 𝗭) inferInstance

noncomputable instance : Inhabited V := Inhabited.mk ∅

/-! ## Aussonderungsaxiom -/

lemma separation_exists_eval (x : V) (φ : SetTheorySemiformula V 1) :
    ∃ y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ φ.Eval ![z] id := by
  classical
  let f := φ.enumerateFVar
  let ψ := (Rew.rewriteMap φ.idxOfFVar) ▹ φ
  have := by
    simpa [models_iff, Semiformula.eval_univCl, Axiom.separationSchema]
      using Theory.models V 𝗦𝗘𝗣 (Separation.separation ψ)
  simpa [ψ, f, Semiformula.eval_rewriteMap, Matrix.constant_eq_singleton] using this f x

lemma separation_exists (x : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P) :
    ∃ y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ P z := by
  rcases hP with ⟨φ, hP⟩
  simpa [hP.iff] using separation_exists_eval x φ

lemma separation_existsUnique (x : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P) :
    ∃! y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ P z := by
  rcases separation_exists x P hP with ⟨s, hs⟩
  apply ExistsUnique.intro s hs
  intro u hu
  ext; simp_all

noncomputable def sep (x : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P := by definability) : V :=
  Classical.choose! (separation_existsUnique x P hP)

@[simp] lemma mem_sep_iff {P : V → Prop} {hP : ℒₛₑₜ-predicate P} {z x : V} :
    z ∈ sep x P (hP := hP) ↔ z ∈ x ∧ P z :=
  Classical.choose!_spec (separation_existsUnique x P hP) z

@[simp] lemma sep_empty_eq (P : V → Prop) {hP : ℒₛₑₜ-predicate P} :
    sep ∅ P (hP := hP) = ∅ := by ext; simp

@[simp] lemma sep_subset {P : V → Prop} {hP : ℒₛₑₜ-predicate P} {x : V} :
    sep x P (hP := hP) ⊆ x := by intro z; simp; tauto

section set_notation

open Lean Elab Term Meta

/--
Set-builder notation.
-/
syntax (name := internalSetBuilder) "{" binderIdent " ∈ " term " ; " term "}" : term

@[term_elab internalSetBuilder]
meta def elabInternalSetBuilder : TermElab
  | `({ $x:ident ∈ $s ; $p }), expectedType? => do
    elabTerm (← `(sep $s (fun $x:ident ↦ $p))) expectedType?
  | _, _ => throwUnsupportedSyntax

@[app_unexpander sep]
meta def sep.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $s $P $_) =>
    match P with
    | `(fun $x:ident ↦ $p) => `({ $x:ident ∈ $s ; $p })
    | _ => throw ()
  | _ => throw ()

end set_notation

/-! ### Intersection -/

noncomputable def sInter (x : V) : V := {z ∈ ⋃ˢ x ; ∀ y ∈ x, z ∈ y}

prefix:110 "⋂ˢ " => sInter

lemma mem_sInter_iff {x z : V} : z ∈ ⋂ˢ x ↔ IsNonempty x ∧ ∀ y ∈ x, z ∈ y := by
  simp only [sInter, mem_sep_iff, mem_sUnion_iff, and_congr_left_iff, isNonempty_def]
  grind

def sInter.dfn : SetTheorySemisentence 2 := “u x. ∀ z, z ∈ u ↔ !isNonempty x ∧ ∀ y ∈ x, z ∈ y”

instance sInter.defined : ℒₛₑₜ-function₁[V] sInter via sInter.dfn :=
  ⟨by intro v; simp [sInter.dfn, mem_ext_iff, mem_sInter_iff]⟩

instance sInter.definable : ℒₛₑₜ-function₁[V] sInter := sInter.defined.to_definable

@[simp] lemma mem_sInter_iff_of_nonempty {x z : V} [hx : IsNonempty x] :
    z ∈ ⋂ˢ x ↔ ∀ y ∈ x, z ∈ y := by
  simp [SetTheory.mem_sInter_iff, hx]

@[simp] lemma sInter_empty_eq : ⋂ˢ (∅ : V) = ∅ := by ext; simp [mem_sInter_iff]

@[simp] lemma sInter_singleton (x : V) : ⋂ˢ {x} = x := by ext; simp [mem_sInter_iff_of_nonempty]

lemma sInter_subset_of_mem_of_nonempty {x y : V} [IsNonempty y] (h : x ∈ y) : ⋂ˢ y ⊆ x := by
  intro z hz
  simp only [mem_sInter_iff_of_nonempty] at hz
  grind

@[simp] lemma subset_sInter_iff_of_nonempty {x y : V} [IsNonempty y] :
    x ⊆ ⋂ˢ y ↔ ∀ z ∈ y, x ⊆ z := by
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

def inter.dfn : SetTheorySemisentence 3 := “u x y. ∀ z, z ∈ u ↔ z ∈ x ∧ z ∈ y”

instance inter.defined : ℒₛₑₜ-function₂[V] Inter.inter via inter.dfn :=
  ⟨by intro v; simp [inter.dfn, mem_ext_iff]⟩

instance inter.definable : ℒₛₑₜ-function₂[V] Inter.inter := inter.defined.to_definable

@[simp] lemma inter_self (x : V) : x ∩ x = x := by ext; simp

lemma inter_comm (x y : V) : x ∩ y = y ∩ x := by ext; simp; tauto

lemma inter_assoc (x y z : V) : (x ∩ y) ∩ z = x ∩ (y ∩ z) := by ext; simp; tauto

@[simp] lemma inter_empty (x : V) : x ∩ ∅ = ∅ := by ext; simp

@[simp] lemma empty_inter (x : V) : ∅ ∩ x = ∅ := by ext; simp

@[simp] lemma inter_eq_left_of_subset {x y : V} (h : x ⊆ y) : x ∩ y = x := by ext z; simpa using h z

@[simp] lemma inter_eq_right_of_subset {x y : V} (h : y ⊆ x) : x ∩ y = y := by
  ext z; simpa using h z

@[simp] lemma sInter_insert (x y : V) [hy : IsNonempty y] : ⋂ˢ insert x y = x ∩ ⋂ˢ y := by
  ext; simp [*, mem_sInter_iff_of_nonempty]

@[simp, grind =] lemma intsert_inter_of_mem (x y z : V) (hx : x ∈ z) :
    insert x y ∩ z = insert x (y ∩ z) := by
  ext; simp only [inter_comm, mem_inter_iff, mem_insert]; grind

@[simp, grind =] lemma intsert_inter_of_not_mem (x y z : V) (hx : x ∉ z) :
    insert x y ∩ z = y ∩ z := by
  ext; simp only [inter_comm, mem_inter_iff, mem_insert]; grind

@[simp, grind =] lemma singleton_inter_of_mem {x y : V} (hx : x ∈ y) :
    {x} ∩ y = {x} := by
  ext
  simp only [inter_comm, mem_inter_iff, mem_singleton_iff,
    and_iff_right_iff_imp]; grind

@[simp, grind =] lemma singleton_inter_of_not_mem {x y : V} (hx : x ∉ y) :
    {x} ∩ y = ∅ := by
  ext; simp only [inter_comm, mem_inter_iff, mem_singleton_iff, not_mem_empty, iff_false, not_and]
  grind

/-! ### Set difference -/

noncomputable def sdiff (x y : V) : V := {z ∈ x ; z ∉ y}

noncomputable instance : SDiff V := ⟨sdiff⟩

lemma sdiff_def (x y : V) : x \ y = {z ∈ x ; z ∉ y} := rfl

@[simp] lemma mem_sdiff_iff {x y z : V} : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y := by simp [sdiff_def]

def sdiff.dfn : SetTheorySemisentence 3 := “d x y. ∀ z, z ∈ d ↔ z ∈ x ∧ z ∉ y”

instance sdiff.defined : ℒₛₑₜ-function₂[V] SDiff.sdiff via sdiff.dfn :=
  ⟨by intro v; simp [sdiff.dfn, mem_ext_iff]⟩

instance sdiff.definable : ℒₛₑₜ-function₂[V] SDiff.sdiff := sdiff.defined.to_definable

@[simp] lemma sdiff_empty (x : V) : x \ ∅ = x := by ext; simp

@[simp] lemma empty_sdiff (x : V) : ∅ \ x = ∅ := by ext; simp

@[simp, grind =] lemma singleton_sdiff_of_mem {x z : V} (hx : x ∈ z) :
    {x} \ z = ∅ := by
  ext
  simp only [mem_sdiff_iff, mem_singleton_iff, not_mem_empty,
    iff_false, not_and]; grind

@[simp, grind =] lemma singleton_sdiff_of_not_mem {x z : V} (hx : x ∉ z) :
    {x} \ z = {x} := by
  ext; simp only [mem_sdiff_iff, mem_singleton_iff, and_iff_left_iff_imp]; grind

@[simp, grind =] lemma insert_sdiff_of_mem {x y z : V} (hx : x ∈ z) :
    insert x y \ z = y \ z := by
  ext; simp only [mem_sdiff_iff, mem_insert, and_congr_left_iff, or_iff_right_iff_imp]; grind

@[simp, grind =] lemma insert_sdiff_of_not_mem {x y z : V} (hx : x ∉ z) :
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
meta def pairUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term $term2) => `(⟨$term, $term2⟩ₖ)
  | _ => throw ()


noncomputable def kpair.π₁ (z : V) : V := ⋃ˢ ⋂ˢ z

noncomputable def kpair.π₂ (z : V) : V := ⋃ˢ {x ∈ ⋃ˢ z; x ∈ ⋂ˢ z → ⋃ˢ z = ⋂ˢ z}

def kpair.dfn : SetTheorySemisentence 3 :=
  “k x y. ∀ x', !singleton.dfn x' x → ∀ z, !doubleton.dfn z x y → !doubleton.dfn k x' z”

instance kpair.defined : ℒₛₑₜ-function₂[V] kpair via kpair.dfn :=
  ⟨by intro v; simp [kpair.dfn, kpair, ←pair_eq_doubleton]⟩

instance kpair.definable : ℒₛₑₜ-function₂[V] kpair := kpair.defined.to_definable

def kpair.π₁.dfn : SetTheorySemisentence 2 := “p₁ x. ∀ i, !sInter.dfn i x → !sUnion.dfn p₁ i”

instance kpair.π₁.defined : ℒₛₑₜ-function₁[V] kpair.π₁ via kpair.π₁.dfn :=
  ⟨by intro v; simp [kpair.π₁.dfn, π₁]⟩

instance kpair.π₁.definable : ℒₛₑₜ-function₁[V] kpair.π₁ := kpair.π₁.defined.to_definable

def kpair.π₂.dfn : SetTheorySemisentence 2 :=
  “p₂ x. ∀ u, !sUnion.dfn u x → ∀ i, !sInter.dfn i x →
    ∀ s, (∀ z, z ∈ s ↔ (z ∈ u ∧ (z ∈ i → u = i))) → !sUnion.dfn p₂ s”

instance kpair.π₂.defined : ℒₛₑₜ-function₁[V] kpair.π₂ via kpair.π₂.dfn :=
  ⟨by intro v
      let u := ⋃ˢ v 1
      let i := ⋂ˢ v 1
      suffices (∀ s, (∀ z, z ∈ s ↔ z ∈ u ∧ (z ∈ i → u = i)) → v 0 = ⋃ˢ s) ↔
          v 0 = ⋃ˢ {x ∈ u ; x ∈ i → u = i} by
        simpa [kpair.π₂.dfn, π₂] using this
      constructor
      · intro h
        apply h
        intro z; simp
      · intro e s hs; rw [e]
        congr; ext
        simp only [mem_sep_iff]; grind⟩

instance kpair.π₂.definable : ℒₛₑₜ-function₁[V] kpair.π₂ := kpair.π₂.defined.to_definable

@[grind =, simp] lemma kpair.π₁_kpair (x y : V) :
    π₁ ⟨x, y⟩ₖ = x := by simp [π₁, kpair]

@[grind =, simp] lemma kpair.π₂_kpair (x y : V) :
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

def prod.dfn : SetTheorySemisentence 3 := “p X Y. ∀ z, z ∈ p ↔ ∃ x ∈ X, ∃ y ∈ Y, !kpair.dfn z x y”

instance prod.defined : ℒₛₑₜ-function₂[V] prod via prod.dfn :=
  ⟨by intro v; simp [prod.dfn, mem_ext_iff, mem_prod_iff]⟩

instance prod.definable : ℒₛₑₜ-function₂[V] prod := prod.defined.to_definable

@[simp] lemma prod_empty (x : V) : x ×ˢ ∅ = ∅ := by ext; simp [mem_prod_iff]

@[simp] lemma empty_prod (x : V) : ∅ ×ˢ x = ∅ := by ext; simp [mem_prod_iff]

@[simp] lemma kpair_mem_iff {x y X Y : V} : ⟨x, y⟩ₖ ∈ X ×ˢ Y ↔ x ∈ X ∧ y ∈ Y := by
  simp [mem_prod_iff]

lemma prod_subset_prod_of_subset {X₁ X₂ Y₁ Y₂ : V} (hX : X₁ ⊆ X₂) (hY : Y₁ ⊆ Y₂) :
    X₁ ×ˢ Y₁ ⊆ X₂ ×ˢ Y₂ := by
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

def IsInductive.dfn : SetTheorySemisentence 1 :=
  “x. (∀ e, !isEmpty e → e ∈ x) ∧ (∀ y ∈ x, ∀ y', !succ.dfn y' y → y' ∈ x)”

instance IsInductive.defined : ℒₛₑₜ-predicate[V] IsInductive via IsInductive.dfn :=
  ⟨fun v ↦ by simp [IsInductive, IsInductive.dfn]⟩

instance IsInductive.definable : ℒₛₑₜ-predicate[V] IsInductive := IsInductive.defined.to_definable

lemma IsInductive.zero {I : V} (hI : IsInductive I) : ∅ ∈ I := hI.1

lemma IsInductive.succ {I : V} (hI : IsInductive I) {x : V} (hx : x ∈ I) : succ x ∈ I := hI.2 x hx

lemma isInductive_exists : ∃ I : V, IsInductive I := by
  simpa [models_iff, BasicSetTheory.infinity] using! Theory.models V 𝗕𝗦𝗧 BasicSetTheory.infinity

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

def isω : SetTheorySemisentence 1 := “ω. ∀ x, x ∈ ω ↔ ∀ I, !IsInductive.dfn I → x ∈ I”

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
      suffices SetTheory.succ x ∈ ω ∧ P (SetTheory.succ x) by simpa [p]
      refine ⟨ω_succ_closed hx.1, succ x hx.1 hx.2⟩
  have : ω ⊆ p := this.ω_subset
  intro x hx
  have : x ∈ (ω : V) ∧ P x := by simpa [p] using this x hx
  exact this.2

/-! ## Axiom of foundation -/

lemma foundation : ∀ x : V, [IsNonempty x] → ∃ y ∈ x, ∀ z ∈ x, z ∉ y := by
  simpa [models_iff, BasicSetTheory.foundation] using Theory.models V 𝗕𝗦𝗧 BasicSetTheory.foundation

lemma foundation' (x : V) [IsNonempty x] : ∃ y ∈ x, x ∩ y = ∅ := by
  rcases foundation x with ⟨y, hyx, H⟩
  exact ⟨y, hyx, by ext z; simpa using H z⟩

@[simp] lemma mem_irrefl (x : V) : x ∉ x := by
  simpa using foundation ({x} : V)

lemma ne_of_mem {x y : V} : x ∈ y → x ≠ y := by
  rintro h rfl; simp_all

-- TODO: I don't know how `aesop` modifiers work, so I don't know if `norm` is the right choice.
@[aesop norm] lemma mem_asymm {x y : V} : x ∈ y → y ∉ x := by
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

-- This lemma requires `foundation`
lemma subset_of_succ_subset {x y : V} (h : succ x ⊆ succ y) : x ⊆ y := by
  intro z hz
  have hzy : z = y ∨ z ∈ y := mem_insert.mp (h z (mem_insert (x := x).mpr (Or.inr hz)))
  have hxy : x = y ∨ x ∈ y := mem_insert.mp (h x (mem_succ_self x))
  have : (z = y ∨ z ∈ y) ∧ (x = y ∨ x ∈ y) := by
    exact And.intro hzy hxy
  aesop

@[simp] lemma succ_inj {x y : V} : succ x = succ y ↔ x = y := by
  constructor <;> intro h
  · ext z
    exact Iff.intro (subset_of_succ_subset (subset_of_eq h) z)
      (subset_of_succ_subset (subset_of_eq h.symm) z)
  · simp only [h]

end FFL.FirstOrder.SetTheory
