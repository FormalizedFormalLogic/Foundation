module

public import Foundation.ProvabilityLogic.GLPlusBoxBot.Basic
public import Foundation.ProvabilityLogic.GL.Arithmetic

/-!
# Arithmetical completeness of `GL + □^n⊥`

The provability logic of a theory of height `n` is `GL + □^n⊥`.

## References

- [AB05, Corollary 42]
- [Vis84]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction

namespace Logic.GLPlusBoxBot

section

variable {α : Type*} {L : Language} [L.ReferenceableBy L] [L.DecidableEq]
         {T U : Theory L} [Diagonalization T] [T ⪯ U]
         {𝔅 : Provability T U} [𝔅.HBL] {f : Realization α L} {A : Formula α}

theorem arithmetical_soundness (h : GLPlusBoxBot 𝔅.height ⊢ A) : U ⊢ A.interpret f 𝔅 := by
  cases hn : 𝔅.height using ENat.recTopCoe with
  | top => exact WeakerThan.pbl <| GL.arithmetical_soundness (by simpa [hn] using h);
  | coe n =>
    have := GL.arithmetical_soundness (f := f) (𝔅 := 𝔅) <| iff_provable_GL.mp (hn ▸ h);
    simp only [Formula.interpret, Formula.interpret_boxItr] at this;
    exact WeakerThan.pbl this ⨀ Provability.height_le_iff_boxBot.mp hn.le;

end

universe u

variable {α : Type u} {A : Formula α}
         {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

theorem arithmetical_completeness {n : ℕ∞} (hn : n ≤ T.height)
    (h : ∀ f : Realization α ℒₒᵣ, T ⊢ f T A) : GLPlusBoxBot n ⊢ A := by
  cases n using ENat.recTopCoe with
  | top => exact GL.arithmetical_completeness_of_height_eq_top (top_le_iff.mp hn) h;
  | coe n => exact iff_provable_GL.mpr <| GL.arithmetical_completeness_of_le_height hn h;

/-- - [AB05, Corollary 42] -/
theorem arithmetical_completeness_iff :
    GLPlusBoxBot T.height ⊢ A ↔ ∀ f : Realization α ℒₒᵣ, T ⊢ f T A :=
  ⟨fun h _ ↦ arithmetical_soundness h, arithmetical_completeness le_rfl⟩

/-- - [AB05, Corollary 42]
- [Vis84]
-/
theorem eq_provabilityLogic : GLPlusBoxBot T.height = T.provabilityLogic (α := α) := by
  ext A;
  exact arithmetical_completeness_iff;

lemma equiv_provabilityLogic : GLPlusBoxBot T.height ≊ T.provabilityLogic (α := α) :=
  equiv_iff.mpr eq_provabilityLogic

end Logic.GLPlusBoxBot

end FFL.ProvabilityLogic

end
