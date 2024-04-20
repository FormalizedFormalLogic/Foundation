import Logic.Logic.Semantics
import Logic.Logic.Deduction

/-!
# Basic definitions and properties of proof-related notions

This file defines a characterization of the proof/provability/calculus of formulas.
Also defines soundness and completeness.

## Main Definitions
* `LO.System`: Proof system of logic.
* `LO.Sound`: Soundness of the proof system.
* `LO.Complete`: Completeness of the proof system.

-/

namespace LO

variable {F : Type*} [LogicalConnective F]

/-- Deduction System -/

class System (F : Type*) extends HasTurnstile F Type*, Deduction (· ⊢ · : Set F → F → Type _)

namespace System

variable [𝓑 : System F]

open Deduction

abbrev Provable (T : Set F) (f : F) : Prop := Deduction.Deducible (· ⊢ ·) T f

infix:45 " ⊢! " => System.Provable

open Deduction


noncomputable def Provable.toProof {T : Set F} {f : F} (h : T ⊢! f) : T ⊢ f := Classical.choice h

abbrev Unprovable (T : Set F) (f : F) : Prop := Deduction.Undeducible (· ⊢ ·) T f

infix:45 " ⊬ " => System.Unprovable

lemma unprovable_iff_not_provable {T : Set F} {f : F} : T ⊬ f ↔ ¬T ⊢! f := by simp [System.Unprovable, Undeducible]

lemma not_unprovable_iff_provable {T : Set F} {f : F} : ¬T ⊬ f ↔ T ⊢! f := by simp [System.Unprovable, Undeducible]

def BewTheory (T U : Set F) : Type _ := {f : F} → f ∈ U → T ⊢ f

infix:45 " ⊢* " => System.BewTheory

abbrev ProvableTheory (T U : Set F) : Prop := Nonempty (T ⊢* U)

infix:45 " ⊢*! " => System.ProvableTheory

def BewTheoryEmpty (T : Set F) : T ⊢* ∅ := fun h => by contradiction

def BewTheory.ofSubset {T U : Set F} (h : U ⊆ T) : T ⊢* U := fun hf => axm (h hf)

def BewTheory.refl (T : Set F) : T ⊢* T := axm

abbrev Consistent (T : Set F) : Prop := Deduction.Consistent (· ⊢ ·) T

def weakening {T U : Set F} {f : F} (b : T ⊢ f) (ss : T ⊆ U) : U ⊢ f := weakening' ss b

lemma weakening! {T U : Set F} {f : F} (b : T ⊢! f) (ss : T ⊆ U) : U ⊢! f := by
  rcases b with ⟨b⟩; exact ⟨weakening b ss⟩

lemma Consistent.of_subset {T U : Set F} (h : Consistent U) (ss : T ⊆ U) : Consistent T := fun b ↦ h (weakening! b ss)

lemma inconsistent_of_proof {T : Set F} (b : T ⊢ ⊥) : ¬Consistent T := by simp [Consistent, Deduction.Consistent, Deduction.Undeducible]; exact ⟨b⟩

lemma inconsistent_of_provable {T : Set F} (b : T ⊢! ⊥) : ¬Consistent T := by simpa [Consistent, Deduction.Consistent, Deduction.Undeducible] using b

lemma consistent_iff_unprovable {T : Set F} : Consistent T ↔ T ⊬ ⊥ := by rfl

lemma inconsistent_iff_provable_falsum {T : Set F} : ¬Consistent T ↔ T ⊢! ⊥ := by
  simp [Consistent, Deduction.Consistent, Deduction.Undeducible]

lemma Consistent.falsum_not_mem {T : Set F} (h : Consistent T) : ⊥ ∉ T := fun b ↦
    System.unprovable_iff_not_provable.mp (System.consistent_iff_unprovable.mp h) ⟨LO.Deduction.axm b⟩

protected def Complete (T : Set F) : Prop := ∀ f, (T ⊢! f) ∨ (T ⊢! ~f)

def Independent (T : Set F) (f : F) : Prop := T ⊬ f ∧ T ⊬ ~f

lemma incomplete_iff_exists_independent {T : Set F} :
    ¬System.Complete T ↔ ∃ f, Independent T f := by simp [System.Complete, not_or, Independent, Unprovable, Undeducible]

def theory (T : Set F) : Set F := {p | T ⊢! p}

@[simp] lemma subset_theory {T : Set F} : T ⊆ theory T := fun _ h ↦ ⟨axm h⟩

noncomputable def provableTheory_theory {T : Set F} : T ⊢* theory T := λ b ↦ b.toProof

class Subtheory (T U : Set F) where
  sub : {f : F} → T ⊢ f → U ⊢ f

infix:50 " ≾ " => Subtheory

class Equivalent (T U : Set F) where
  ofLeft : {f : F} → T ⊢ f → U ⊢ f
  ofRight : {f : F} → U ⊢ f → T ⊢ f

namespace Subtheory

variable (T U T₁ T₂ T₃ : Set F)

@[refl] instance : T ≾ T := ⟨id⟩

@[trans] protected def trans [T₁ ≾ T₂] [T₂ ≾ T₃] : T₁ ≾ T₃ :=
  ⟨fun {f} b => sub (sub b : T₂ ⊢ f)⟩

variable {T U}

def ofSubset (h : T ⊆ U) : T ≾ U := ⟨fun b => weakening b h⟩

def bewTheory [T ≾ U] : U ⊢* T := λ hp ↦ sub (axm hp)

end Subtheory

namespace Equivalent

variable (T U T₁ T₂ T₃ : Set F)

@[refl] instance : Equivalent T T := ⟨id, id⟩

@[symm] instance [Equivalent T U] : Equivalent U T := ⟨ofRight, ofLeft⟩

@[trans] protected def trans [Equivalent T₁ T₂] [Equivalent T₂ T₃] : Equivalent T₁ T₃ :=
  ⟨fun {f} b => ofLeft (ofLeft b : T₂ ⊢ f), fun {f} b => ofRight (ofRight b : T₂ ⊢ f)⟩

end Equivalent

end System

def System.hom [System F] {G : Type*} [LogicalConnective G] (φ : G →ˡᶜ F) : System G where
  turnstile := fun T g ↦ φ '' T ⊢ φ g
  axm := fun h ↦ Deduction.axm (Bew := (· ⊢ · : Set F → F → Type _)) (Set.mem_image_of_mem φ h)
  weakening' := fun h ↦ by simpa using Deduction.weakening' (Set.image_subset φ h)

variable (F)
variable [LogicalConnective F] [𝓑 : System F] {α: Type*} [𝓢 : Semantics F α]

class Sound where
  sound : ∀ {T : Set F} {p : F}, T ⊢ p → T ⊨ p

class SoundOn (M : Type w) (a : α) (H : Set F) where
  sound : ∀ {T : Set F} {p : F}, p ∈ H → T ⊢ p → a ⊧ p

class Complete extends Sound F where
  complete : ∀ {T : Set F} {p : F}, T ⊨ p → T ⊢ p

variable {F}

namespace Sound

variable [Sound F]
variable {a : α}

lemma sound! {T : Set F} {f : F} : T ⊢! f → T ⊨ f := by rintro ⟨b⟩; exact sound b

lemma not_provable_of_countermodel {T : Set F} {p : F}
  (hT : a ⊧* T) (hp : ¬a ⊧ p) : T ⊬ p := fun b ↦ hp (Sound.sound! b hT)

lemma consistent_of_model {T : Set F}
  (hT : a ⊧* T) : System.Consistent T :=
  not_provable_of_countermodel (p := ⊥) hT (by simp)

lemma consistent_of_satisfiable {T : Set F} : Semantics.SatisfiableSet T → System.Consistent T := by
  rintro ⟨_, h⟩; exact consistent_of_model h

lemma realize_of_proof {T : Set F} {f} (h : a ⊧* T) (b : T ⊢ f) : a ⊧ f :=
  Sound.sound b h

lemma RealizeSet_of_proofTheory {T U : Set F} (h : a ⊧* T) (b : T ⊢* U) : a ⊧* U :=
  ⟨fun _ hf => realize_of_proof h (b hf)⟩

lemma modelsTheory_of_subtheory {T U : Set F} [U ≾ T] (h : a ⊧* T) : a ⊧* U :=
  RealizeSet_of_proofTheory h System.Subtheory.bewTheory

end Sound

namespace Complete

noncomputable def of! [Sound F] (H : ∀ {T : Set F} {p : F}, T ⊨ p → T ⊢! p) : Complete F where
  complete := fun h ↦ (H h).toProof

variable [Complete F]

lemma satisfiableTheory_iff_consistent {T : Set F} : Semantics.SatisfiableSet T ↔ System.Consistent T :=
  ⟨Sound.consistent_of_satisfiable,
   by contrapose; intro h
      have : T ⊨ ⊥ := by intro a hM; have : Semantics.SatisfiableSet T := ⟨a, hM⟩; contradiction
      have : T ⊢ ⊥ := complete this
      exact System.inconsistent_of_proof this⟩

lemma not_satisfiable_iff_inconsistent {T : Set F} : ¬Semantics.SatisfiableSet T ↔ T ⊢! ⊥ := by
  simp [satisfiableTheory_iff_consistent, System.Consistent, Deduction.Consistent, Deduction.Undeducible]

lemma consequence_iff_provable {T : Set F} {f : F} : T ⊨ f ↔ T ⊢! f :=
⟨fun h => ⟨complete h⟩, by rintro ⟨b⟩; exact Sound.sound b⟩

alias ⟨complete!, _⟩ := consequence_iff_provable

end Complete

namespace System

variable [LO.Complete F]

def ofSemanticsSubtheory {T₁ T₂ : Set F} (h : Semantics.Subtheory T₁ T₂) : System.Subtheory T₁ T₂ :=
  ⟨fun hf => Complete.complete (h (Sound.sound hf))⟩

end System

namespace Semantics

variable [LO.Complete F]

lemma ofSystemSubtheory (T₁ T₂ : Set F) [System.Subtheory T₁ T₂] : Semantics.Subtheory T₁ T₂ :=
  fun hf => (Sound.sound $ System.Subtheory.sub $ Complete.complete hf)

end Semantics

end LO
