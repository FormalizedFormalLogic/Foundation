module

public import Foundation.ProvabilityLogic.Formula
public import Foundation.Logic.Semantics
public import Foundation.Vorspiel.Rel.WCWF

/-!
# Kripke semantics
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace Kripke

structure Model (κ : Type*) [Nonempty κ] (α : Type*) where
  Rel' : κ → κ → Prop
  Val' : κ → α → Prop

namespace Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

abbrev World (_ : Model κ α) := κ

abbrev Rel {M : Model κ α} : M.World → M.World → Prop := M.Rel'

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

scoped infix:60 " ≺ " => Rel

@[grind]
def RelItr : ℕ → M.World → M.World → Prop
  |     0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, x ≺ z ∧ RelItr n z y

scoped notation x:45 " ≺^[" n:0 "] " y:46 => RelItr n x y

section RelItr

variable {x y : M.World} {n : ℕ}

@[simp, grind =]
lemma relItr_zero : x ≺^[0] y ↔ x = y := Iff.rfl

@[simp, grind =]
lemma relItr_one : x ≺^[1] y ↔ x ≺ y := by simp [RelItr];

@[grind =]
lemma relItr_succ : x ≺^[n + 1] y ↔ ∃ z, x ≺ z ∧ z ≺^[n] y := Iff.rfl

abbrev NotRel {M : Model κ α} : M.World → M.World → Prop := λ x y => ¬(x ≺ y)
scoped infix:60 " ⊀ " => NotRel

abbrev NotRelItr {M : Model κ α} (n : ℕ) : M.World → M.World → Prop := λ x y => ¬(x ≺^[n] y)
scoped notation x:45 " ⊀^[" n:0 "] " y:46 => NotRelItr n x y

@[simp, grind =]
lemma notRelItr_iff : x ⊀^[n] y ↔ ¬x ≺^[n] y := Iff.rfl

end RelItr

class IsGL (M : Model κ α) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel

class IsFiniteGL (M : Model κ α) extends IsTrans _ M.Rel, Std.Irrefl M.Rel where
  [finite : Finite M.World]

instance [M.IsFiniteGL] : Finite M.World := IsFiniteGL.finite

instance [M.IsFiniteGL] : M.IsGL where

instance [M.IsGL] : Std.Irrefl M.Rel := ConverseWellFounded.irrefl

class IsGrz (M : Model κ α) extends Std.Refl M.Rel, IsTrans _ M.Rel, IsWeaklyConverseWellFounded _ M.Rel

class IsFiniteGrz (M : Model κ α) extends Std.Refl M.Rel, IsTrans _ M.Rel, Std.Antisymm M.Rel where
  [finite : Finite M.World]

instance [M.IsFiniteGrz] : Finite M.World := IsFiniteGrz.finite

instance [M.IsFiniteGrz] : M.IsGrz where

abbrev pointModel (v : α → Prop) : Model (Fin 1) α where
  Rel' _ _ := False
  Val' _ := v

instance (v : α → Prop) : (pointModel v).IsFiniteGL where
  trans := by tauto;
  irrefl := by tauto;

noncomputable def terminalOf (M : Model κ α) [IsConverseWellFounded _ M.Rel] (X : Set M.World)
    (hX : X.Nonempty) :
    { t // t ∈ X ∧ ∀ x ∈ X, t ⊀ x } :=
  have h := ConverseWellFounded.iff_has_max.mp IsConverseWellFounded.cwf X hX;
  ⟨h.choose, h.choose_spec⟩

end Model

namespace Model.World

open Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {x : M.World} {A B : Formula α} {n : ℕ}

@[grind]
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
  | #a    => M.Val x a
  | ⊥     => False
  | A 🡒 B => Forces M x A → Forces M x B
  | □A    => ∀ y, x ≺ y → Forces M y A

scoped notation:55 x:56 " ⊩[" M "] " A:56 => Forces M x A

scoped notation:55 x:56 " ⊮[" M "] " A:56 => ¬Forces M x A

@[simp, grind =] lemma forces_atom {a : α} : x ⊩[M] #a ↔ M.Val x a := Iff.rfl
@[simp, grind .] lemma not_forces_bot : x ⊮[M] ⊥ := id
@[simp, grind .] lemma forces_top : x ⊩[M] ⊤ := id
@[grind =] lemma forces_imp : x ⊩[M] A 🡒 B ↔ x ⊮[M] A ∨ x ⊩[M] B := imp_iff_not_or
@[grind =] lemma forces_and : x ⊩[M] A ⋏ B ↔ x ⊩[M] A ∧ x ⊩[M] B := by
  change ((_ → _ → False) → False) ↔ _; tauto;
@[grind =] lemma forces_or : x ⊩[M] A ⋎ B ↔ x ⊩[M] A ∨ x ⊩[M] B := by
  change ((_ → False) → _) ↔ _; tauto;
@[grind =] lemma forces_neg : x ⊩[M] ∼A ↔ x ⊮[M] A := Iff.rfl
@[grind =] lemma forces_box : x ⊩[M] □A ↔ ∀ y, x ≺ y → y ⊩[M] A := Iff.rfl
@[grind =] lemma forces_dia : x ⊩[M] ◇A ↔ ∃ y, x ≺ y ∧ y ⊩[M] A := by
  change ((∀ y, x ≺ y → y ⊩[M] A → False) → False) ↔ _; grind;

@[grind =] lemma not_forces_imp : x ⊮[M] A 🡒 B ↔ x ⊩[M] A ∧ x ⊮[M] B := by grind;
@[grind =] lemma not_forces_box : x ⊮[M] □A ↔ ∃ y, x ≺ y ∧ y ⊮[M] A := by grind;

@[grind =]
lemma forces_boxItr : x ⊩[M] □^[n]A ↔ ∀ y, x ≺^[n] y → y ⊩[M] A := by
  induction n generalizing x <;> grind;

end Model.World

namespace Model

variable {κ α : Type*} [Nonempty κ]

instance : Semantics (Model κ α) (Formula α) := ⟨fun M A ↦ ∀ x : M.World, World.Forces M x A⟩

lemma models_iff {M : Model κ α} {A : Formula α} : M ⊧ A ↔ ∀ x : M.World, World.Forces M x A :=
  Iff.rfl

end Model

end Kripke

end FFL.ProvabilityLogic

end
