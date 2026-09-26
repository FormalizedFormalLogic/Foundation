module

public import Foundation.ProvabilityLogic.Kripke.Basic

/-!
# Bisimulations and pseudo-epimorphisms

Pseudo-epimorphisms are the p-morphisms of modal logic.

## References

- [Bek90, §4]
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model.World

namespace Model

variable {κ₁ κ₂ α : Type*} [Nonempty κ₁] [Nonempty κ₂] {M₁ : Model κ₁ α} {M₂ : Model κ₂ α}

/-- A bisimulation matching the valuation only on the atoms in `P`.

- [Bek90, §4]
-/
structure BisimulationUnder (P : Finset α) (M₁ : Model κ₁ α) (M₂ : Model κ₂ α) where
  toRel : M₁.World → M₂.World → Prop
  atomic {x₁ x₂ a} : a ∈ P → toRel x₁ x₂ → (M₁.Val x₁ a ↔ M₂.Val x₂ a)
  forth {x₁ y₁ x₂} : toRel x₁ x₂ → x₁ ≺ y₁ → ∃ y₂, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ x₂ y₂} : toRel x₁ x₂ → x₂ ≺ y₂ → ∃ y₁, toRel y₁ y₂ ∧ x₁ ≺ y₁

@[inherit_doc]
scoped notation:50 M₁ " ⇄[" P "] " M₂ => BisimulationUnder P M₁ M₂

instance {P : Finset α} : CoeFun (M₁ ⇄[P] M₂) fun _ ↦ M₁.World → M₂.World → Prop :=
  ⟨BisimulationUnder.toRel⟩

lemma BisimulationUnder.forces_iff [DecidableEq α] {P : Finset α} (Z : M₁ ⇄[P] M₂)
    {x₁ : M₁.World} {x₂ : M₂.World} (h : Z x₁ x₂) {A : Formula α} (hA : A.atoms ⊆ P) :
    x₁ ⊩[M₁] A ↔ x₂ ⊩[M₂] A := by
  induction A generalizing x₁ x₂ with
  | atom a => exact Z.atomic (hA (by simp)) h;
  | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr (ihA h (by grind)) (ihB h (by grind));
  | box A ih =>
    constructor;
    · intro hx y₂ R;
      obtain ⟨y₁, hy, R'⟩ := Z.back h R;
      exact (ih hy hA).mp (hx y₁ R');
    · intro hx y₁ R;
      obtain ⟨y₂, hy, R'⟩ := Z.forth h R;
      exact (ih hy hA).mpr (hx y₂ R');

structure PseudoEpimorphism (M₁ : Model κ₁ α) (M₂ : Model κ₂ α) where
  toFun : M₁.World → M₂.World
  forth {x y} : x ≺ y → toFun x ≺ toFun y
  back {x v} : toFun x ≺ v → ∃ y, toFun y = v ∧ x ≺ y
  atomic {x a} : M₁.Val x a ↔ M₂.Val (toFun x) a

scoped infix:80 " →ₚ " => PseudoEpimorphism

instance : CoeFun (M₁ →ₚ M₂) fun _ ↦ M₁.World → M₂.World := ⟨PseudoEpimorphism.toFun⟩

lemma PseudoEpimorphism.forces_iff (f : M₁ →ₚ M₂) {x : M₁.World} {A : Formula α} :
    x ⊩[M₁] A ↔ f x ⊩[M₂] A := by
  induction A generalizing x with
  | atom => exact f.atomic;
  | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ih =>
    constructor;
    · intro h v R;
      obtain ⟨y, rfl, R'⟩ := f.back R;
      exact ih.mp (h y R');
    · exact fun h y R ↦ ih.mpr (h (f y) (f.forth R));

end Model

end FFL.ProvabilityLogic.Kripke

end
