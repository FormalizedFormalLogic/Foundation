module

public import Foundation.Modal.Logic.Basic
public import Foundation.Vorspiel.Rel.Basic
public import Foundation.Logic.ForcingRelation

@[expose] public section

variable {α β : Type*}

namespace LO.Modal

open Entailment

structure KripkeModel (α : Type*) where
  World : Type*
  Rel : Rel World World
  [world_nonempty : Nonempty World]
  Val : α → World → Prop

namespace KripkeModel

variable {M : KripkeModel α} {x y z : M.World} {a : α} {φ ψ χ : Formula α} {n m : ℕ}


abbrev Rel' (x y : M.World) := M.Rel x y
infix:45 " ≺ " => Rel'

abbrev InvRel (x y : M.World) := M.Rel y x
infix:45 " ≻ " => InvRel

abbrev RelItr' (n : ℕ) := M.Rel.Iterate n
notation x:45 " ≺^[" n:0 "] " y:46 => RelItr' n x y

instance : Nonempty M.World := M.world_nonempty
instance : CoeSort (KripkeModel α) (Type*) := ⟨λ M => M.World⟩
instance : CoeFun (KripkeModel α) (λ M => α → M → Prop) := ⟨fun M => M.Val⟩

abbrev replacingVal (M : KripkeModel α) (V : α → M.World → Prop) : KripkeModel α where
  World := M.World
  Rel := M.Rel
  Val := V


section Forces

@[grind]
def Forces {M : KripkeModel α} (x : M.World) : Formula α → Prop
  | .atom a  => M a x
  | ⊥  => False
  | φ ➝ ψ => (M.Forces x φ) ➝ (M.Forces x ψ)
  | □φ   => ∀ y, x ≺ y → (M.Forces y φ)

instance : ForcingRelation M.World (Formula α) where
  Forces := Forces

@[grind =] lemma forces_atom : x ⊩ (.atom a) ↔ M a x := by tauto
@[simp, grind .] lemma forces_falsum : x ⊮ ⊥ := by tauto;
@[simp, grind .] lemma forces_verum : x ⊩ ⊤ := by tauto;
@[grind =] lemma forces_imp : x ⊩ (φ ➝ ψ) ↔ (x ⊩ φ) ➝ (x ⊩ ψ) := by tauto;
@[grind =] lemma forces_neg : x ⊩ ∼φ ↔ x ⊮ φ := by tauto;
@[grind =] lemma forces_and : x ⊩ (φ ⋏ ψ) ↔ (x ⊩ φ) ∧ (x ⊩ ψ) := by grind;
@[grind =] lemma forces_or : x ⊩ (φ ⋎ ψ) ↔ (x ⊩ φ) ∨ (x ⊩ ψ) := by grind;
@[grind =] lemma forces_iff : x ⊩ (φ ⭤ ψ) ↔ ((x ⊩ φ) ↔ (x ⊩ ψ)) := by grind [LogicalConnective.iff];
@[grind =] lemma forces_box : x ⊩ □φ ↔ ∀ y, x ≺ y → (y ⊩ φ) := by tauto;
@[grind =] lemma forces_dia : x ⊩ ◇φ ↔ ∃ y, x ≺ y ∧ (y ⊩ φ) := by grind;

instance : ForcingRelation.BasicSemantics M where
  verum {_} := forces_verum
  falsum {_} := forces_falsum
  and {_ _ _} := forces_and
  or {_ _ _} := forces_or


@[grind =]
lemma forces_boxItr : x ⊩ □^[n]φ ↔ ∀ {y}, x ≺^[n] y → y ⊩ φ := by
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


lemma iff_forces_diaItr_dual : (x ⊩ ◇^[n]φ) ↔ (x ⊩ ∼□^[n](∼φ)) := by
  induction n generalizing x <;> grind [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ];

lemma iff_dia_dual : (x ⊩ ◇φ) ↔ (x ⊩ ∼□(∼φ)) := by
  grind [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ];

lemma iff_forces_replaceSubstVal (s : Substitution α) :
  letI M' : KripkeModel _ := M.replacingVal (λ a x => x ⊩ (s a));
  Forces (M := M') x φ ↔ x ⊩ (φ⟦s⟧) := by
  induction φ generalizing x <;> . dsimp [Forces]; grind;

end Forces


section Models

def Models (M : KripkeModel α) (φ) := M ∀⊩ φ
infix:45 " ⊧ " => Models

abbrev NotModels (M : KripkeModel α) (φ) := ¬M ⊧ φ
infix:45 " ⊭ " => NotModels

@[simp, grind .]
lemma models_verum : M ∀⊩ ⊤ := ForcingRelation.AllForces.verum

@[simp, grind .]
lemma models_falsum : M ⊭ ⊥ := by simp [NotModels, Models]

@[grind =]
lemma models_and : M ⊧ (φ ⋏ ψ) ↔ M ⊧ φ ∧ M ⊧ ψ := ForcingRelation.AllForces.and

@[grind =]
lemma iff_notModels_exists_world_notForces : M ⊭ φ ↔ ∃ x : M, x ⊮ φ := by
  simp [NotModels, Models];
alias ⟨exists_world_notForces_of_notModels, notModels_of_exists_world_notForces⟩ := iff_notModels_exists_world_notForces

@[grind =>]
lemma models_mdp (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := fun x ↦ hpq x (hp x)

@[grind =>]
lemma models_nec (hp : M ⊧ φ) : M ⊧ □φ := fun _ y _ ↦ hp y

@[grind =>]
lemma models_multinec (hp : M ⊧ φ) : M ⊧ □^[n]φ := by
  induction n <;> grind;

lemma models_implyK : M ⊧ (Axioms.ImplyK φ ψ) := by tauto;
lemma models_implyS : M ⊧ (Axioms.ImplyS φ ψ χ) := by tauto;
lemma models_elimContra : M ⊧ (Axioms.ElimContra φ ψ) := by
  grind only [iff_notModels_exists_world_notForces, forces_imp, forces_neg];
lemma models_axiomK : M ⊧ (Axioms.K φ ψ) := by tauto;

attribute [simp, grind .]
  models_implyK
  models_implyS
  models_elimContra
  models_axiomK

end Models


def logic (M : KripkeModel α) : Logic α := { φ | M ⊧ φ }


end KripkeModel


abbrev KripkeModelClass (α) := Set (KripkeModel α)



end LO.Modal
