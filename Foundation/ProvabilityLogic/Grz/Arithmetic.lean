module

public import Foundation.ProvabilityLogic.Grz.Boxdot
public import Foundation.ProvabilityLogic.S.Arithmetic
public import Foundation.ProvabilityLogic.Arithmetic.StrongInterpret

/-!
# Arithmetical completeness of `Grz`

## References

- [Gol78]
- [Boo80]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction

namespace Logic.Grz

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α} {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

theorem arithmetical_completeness_iff_of_height_eq_top (height : T.height = ⊤) :
    A ∈ 𝐆𝐫𝐳 ↔ ∀ f : Realization α ℒₒᵣ, T ⊢ A.strongInterpret f T.standardProvability := by
  rw [iff_boxdotTranslate_mem_GL];
  constructor;
  . intro h f;
    exact Formula.provable_interpret_boxdotTranslate_iff.mp
      (WeakerThan.pbl (GL.arithmetical_soundness h));
  . intro h;
    exact GL.arithmetical_completeness_of_height_eq_top height fun f ↦
      Formula.provable_interpret_boxdotTranslate_iff.mpr (h f);

theorem arithmetical_completeness_iff [T.SoundOnHierarchy 𝚺 1] :
    A ∈ 𝐆𝐫𝐳 ↔ ∀ f : Realization α ℒₒᵣ, T ⊢ A.strongInterpret f T.standardProvability :=
  arithmetical_completeness_iff_of_height_eq_top (Arithmetic.height_eq_top_of_sigma1_sound T)

theorem arithmetical_completeness_models_iff [ℕ↓[ℒₒᵣ] ⊧* T] :
    A ∈ 𝐆𝐫𝐳 ↔ ∀ f : Realization α ℒₒᵣ, ℕ↓[ℒₒᵣ] ⊧ A.strongInterpret f T.standardProvability := by
  rw [iff_boxdotTranslate_mem_S, S.arithmetical_completeness_iff (T := T)];
  exact forall_congr' fun _ ↦ Formula.models_interpret_boxdotTranslate_iff;

end Logic.Grz

end FFL.ProvabilityLogic

end
