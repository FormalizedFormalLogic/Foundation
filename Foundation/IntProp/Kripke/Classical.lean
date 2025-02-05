import Foundation.IntProp.Kripke.Basic

namespace LO.IntProp


namespace Kripke

abbrev ClassicalValuation := ℕ → Prop

end Kripke


namespace Formula.Kripke

open IntProp.Kripke

abbrev ClassicalSatisfies (V : ClassicalValuation) (φ : Formula ℕ) : Prop := Satisfies (⟨Kripke.pointFrame, ⟨λ _ => V, by tauto⟩⟩) () φ

namespace ClassicalSatisfies

instance : Semantics (Formula ℕ) (ClassicalValuation) := ⟨ClassicalSatisfies⟩

variable {V : ClassicalValuation} {a : ℕ}

@[simp] lemma atom_def : V ⊧ atom a ↔ V a := by simp only [Semantics.Realize, Satisfies]

instance : Semantics.Tarski (ClassicalValuation) where
  realize_top := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_bot := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_or  := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_and := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_imp := by simp [Semantics.Realize, Satisfies]; tauto;
  realize_not := by simp [Semantics.Realize, Satisfies]; tauto;

end ClassicalSatisfies

end Formula.Kripke


open IntProp.Kripke
open Formula.Kripke (ClassicalSatisfies)

namespace Hilbert.Cl

lemma classical_sound : (Hilbert.Cl ℕ) ⊢! φ → (∀ V : ClassicalValuation, V ⊧ φ) := by
  intro h V;
  apply Hilbert.Cl.Kripke.sound.sound h Kripke.pointFrame;
  simp [Euclidean];

lemma unprovable_of_exists_classicalValuation : (∃ V : ClassicalValuation, ¬(V ⊧ φ)) → (Hilbert.Cl ℕ) ⊬ φ := by
  contrapose;
  simp;
  apply classical_sound;

end Hilbert.Cl

end LO.IntProp
