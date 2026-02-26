module

public import Foundation.Modal.Logic.Basic
public import Foundation.Vorspiel.Rel.Basic
public import Foundation.Logic.ForcingRelation

@[expose] public section

variable {κ α : Type*} [Nonempty κ]

namespace LO.Modal

open Entailment

structure KripkeModel (κ : Type*) [Nonempty κ] (α : Type*) where
  frame : Rel κ κ
  val : α → κ → Prop

namespace KripkeModel

abbrev world (_ : KripkeModel κ α) := κ

variable {M : KripkeModel κ α} {x y z : M.world} {a : α} {φ ψ χ : Formula α} {n m : ℕ}


abbrev rel : Rel M.world M.world := M.frame
infix:45 " ≺ " => rel

abbrev relInv (x y : M.world) := M.frame y x
infix:45 " ≻ " => relInv

abbrev relItr (n : ℕ) : Rel M.world M.world := M.frame.Iterate n
notation x:45 " ≺^[" n:0 "] " y:46 => relItr n x y

-- instance : CoeSort (KripkeModel κ α) (Type*) := ⟨λ M => M.world⟩
instance : CoeFun (KripkeModel κ α) (λ _ => α → κ → Prop) := ⟨fun M => M.val⟩

abbrev replaceVal (M : KripkeModel κ α) (V : α → M.world → Prop) : KripkeModel κ α where
  frame := M.frame
  val := V

@[simp]
lemma replaceVal_comp {V₁ V₂ : α → M.world → Prop}
  : (M.replaceVal V₁ |>.replaceVal V₂) = M.replaceVal V₂ := by tauto;

section Forces

@[grind]
def Forces (M : KripkeModel κ α) (x : M.world) : Formula α → Prop
  | .atom a  => M a x
  | ⊥  => False
  | φ ➝ ψ => (M.Forces x φ) ➝ (M.Forces x ψ)
  | □φ   => ∀ y, x ≺ y → (M.Forces y φ)

instance : ForcingRelation M.world (Formula α) where
  Forces := Forces M

@[grind =] lemma forces_atom : x ⊩ (.atom a) ↔ M a x := by tauto
@[simp, grind .] lemma forces_falsum : x ⊮ ⊥ := by tauto;
@[simp, grind .] lemma forces_verum : x ⊩ ⊤ := by tauto;
@[grind =] lemma forces_imp : x ⊩ (φ ➝ ψ) ↔ (x ⊩ φ) ➝ (x ⊩ ψ) := by tauto;
@[grind =] lemma forces_neg : x ⊩ ∼φ ↔ x ⊮ φ := by tauto;
@[grind =] lemma forces_and : x ⊩ (φ ⋏ ψ) ↔ (x ⊩ φ) ∧ (x ⊩ ψ) := by grind;
@[grind =] lemma forces_or : x ⊩ (φ ⋎ ψ) ↔ (x ⊩ φ) ∨ (x ⊩ ψ) := by grind;
@[grind =] lemma forces_iff : x ⊩ (φ ⭤ ψ) ↔ ((x ⊩ φ) ↔ (x ⊩ ψ)) := by grind [LogicalConnective.iff];
@[grind =] lemma forces_box : x ⊩ □φ ↔ ∀ y, x ≺ y → (y ⊩ φ) := by tauto;

@[grind =] lemma iff_forces_dn : x ⊩ ∼∼φ ↔ x ⊩ φ := by simp [forces_neg, forces_neg.not];

@[grind =]
lemma forces_dia : x ⊩ ◇φ ↔ ∃ y, x ≺ y ∧ (y ⊩ φ) := calc
  _ ↔ x ⊩ ∼□(∼φ) := by rw [DiaByBox.dia_by_box]
  _ ↔ x ⊮ □(∼φ)  := by grind;
  _ ↔ ¬x ⊩ □(∼φ) := by grind;
  _ ↔ ¬(∀ y, x ≺ y → y ⊩ ∼φ) := by grind;
  _ ↔ ∃ y, x ≺ y ∧ y ⊮ ∼φ := by grind;
  _ ↔ ∃ y, x ≺ y ∧ y ⊩ (∼∼φ) := by simp [forces_neg];
  _ ↔ _ := by simp [iff_forces_dn];

instance : ForcingRelation.BasicSemantics M.world where
  verum {_} := forces_verum
  falsum {_} := forces_falsum
  and {_ _ _} := forces_and
  or {_ _ _} := forces_or


@[grind =]
lemma forces_boxItr : x ⊩ □^[n]φ ↔ ∀ y, x ≺^[n] y → y ⊩ φ := by
  induction n generalizing x <;> grind [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ];

@[grind =]
lemma forces_diaItr : x ⊩ ◇^[n]φ ↔ ∃ y, x ≺^[n] y ∧ (y ⊩ φ) := by
  induction n generalizing x <;> grind [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ];


@[grind =]
lemma forces_lconj {l : List _} : x ⊩ l.conj ↔ ∀ φ ∈ l, x ⊩ φ := by
  induction l <;>
  grind [List.conj_cons, List.conj_nil];

@[grind =]
lemma forces_lconj₂ {l : List _} : x ⊩ ⋀l ↔ ∀ φ ∈ l, x ⊩ φ := by
  induction l using List.induction_with_singleton <;>
  grind [List.conj₂_nil, List.conj₂_cons_nonempty, List.conj₂_singleton]

@[grind =]
lemma forces_lconj' {l : List β} {ι : β → Formula α} : x ⊩ l.conj' ι ↔ ∀ i ∈ l, x ⊩ (ι i) := by
  grind [List.conj'];

@[grind =]
lemma forces_fconj {s : Finset _} : x ⊩ s.conj ↔ ∀ φ ∈ s, x ⊩ φ := by
  apply Iff.trans forces_lconj₂;
  simp;

@[grind =]
lemma forces_fconj' {s : Finset β} {ι : β → Formula α} : x ⊩ s.conj' ι ↔ ∀ i ∈ s, x ⊩ (ι i) := by
  apply Iff.trans forces_lconj';
  simp;


@[grind =]
lemma forces_ldisj {l : List _} : x ⊩ l.disj ↔ ∃ φ ∈ l, x ⊩ φ := by
  induction l <;>
  grind [List.disj_cons, List.disj_nil];

@[grind =]
lemma forces_ldisj₂ {l : List _} : x ⊩ ⋁l ↔ ∃ φ ∈ l, x ⊩ φ := by
  induction l using List.induction_with_singleton <;>
  grind [List.disj₂_nil, List.disj₂_cons_nonempty, List.disj₂_singleton]

@[grind =]
lemma forces_ldisj' {l : List β} {ι : β → Formula α} : x ⊩ l.disj' ι ↔ ∃ i ∈ l, x ⊩ (ι i) := by
  grind [List.disj']

@[grind =]
lemma forces_fdisj {s : Finset _} : x ⊩ s.disj ↔ ∃ φ ∈ s, x ⊩ φ := by
  apply Iff.trans forces_ldisj₂;
  simp;

@[grind =]
lemma forces_fdisj' {s : Finset β} {ι : β → Formula α} : x ⊩ s.disj' ι ↔ ∃ i ∈ s, x ⊩ (ι i) := by
  apply Iff.trans forces_ldisj';
  simp;


/-
lemma iff_forces_diaItr_dual : (x ⊩ ◇^[n]φ) ↔ (x ⊩ ∼□^[n](∼φ)) := calc
  _ ↔ ∃ y, x ≺^[n] y ∧ (y ⊩ φ) := forces_diaItr
  _ ↔ ¬(∀ y, x ≺^[n] y → ¬y ⊩ φ) := by push_neg; rfl;
  _ ↔ _ := by sorry;
-/

lemma iff_dia_dual : (x ⊩ ◇φ) ↔ (x ⊩ ∼□(∼φ)) := by
  grind [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ];


abbrev replaceSubstVal (M : KripkeModel κ α) (s : Substitution α) : KripkeModel κ α
  := M.replaceVal (λ a x => x ⊩ (s a))

lemma iff_forces_replaceSubstVal (s : Substitution α) :
  (M.replaceSubstVal s).Forces x φ ↔ x ⊩ (φ⟦s⟧) := by
  induction φ generalizing x <;> . dsimp [Forces]; grind;

end Forces


section Models

def Models (M : KripkeModel κ α) (φ) := M.world ∀⊩ φ
infix:45 " ⊧ " => Models

abbrev NotModels (M : KripkeModel κ α) (φ) := ¬M ⊧ φ
infix:45 " ⊭ " => NotModels

@[simp, grind .]
lemma models_verum : M ⊧ ⊤ := ForcingRelation.AllForces.verum

@[simp, grind .]
lemma models_falsum : M ⊭ ⊥ := by simp [NotModels, Models]

@[grind =]
lemma models_and : M ⊧ (φ ⋏ ψ) ↔ M ⊧ φ ∧ M ⊧ ψ := ForcingRelation.AllForces.and

@[grind =]
lemma iff_notModels_exists_world_notForces : M ⊭ φ ↔ ∃ x : M.world, x ⊮ φ := by
  simp [NotModels, Models];
alias ⟨exists_world_notForces_of_notModels, notModels_of_exists_world_notForces⟩ := iff_notModels_exists_world_notForces

@[grind <=]
lemma models_mdp (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := fun x ↦ hpq x (hp x)

@[grind <=]
lemma models_nec (hp : M ⊧ φ) : M ⊧ □φ := fun _ y _ ↦ hp y

@[grind <=]
lemma models_multinec (hp : M ⊧ φ) : M ⊧ □^[n]φ := by induction n <;> grind;

lemma models_implyK : M ⊧ (Axioms.ImplyK φ ψ) := by intro x; grind;
lemma models_implyS : M ⊧ (Axioms.ImplyS φ ψ χ) := by intro x; grind;
lemma models_elimContra : M ⊧ (Axioms.ElimContra φ ψ) := by intro x; grind;
lemma models_axiomK : M ⊧ (Axioms.K φ ψ) := by tauto;

attribute [simp, grind .]
  models_implyK
  models_implyS
  models_elimContra
  models_axiomK

end Models


def logic (M : KripkeModel κ α) : Logic α := { φ | M ⊧ φ }

end KripkeModel



end LO.Modal
