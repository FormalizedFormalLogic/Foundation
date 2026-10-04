module

public import Foundation.ProvabilityLogic.GLPlusBoxBot.Basic
public import Foundation.ProvabilityLogic.GL.Arithmetic

/-!
# Arithmetical completeness of `GL + □^n⊥`

The provability logic of a theory of height `n` is `GL + □^n⊥`. In particular, the provability
logic of `T` relative to `T + ¬Con(T)` is `GL + □⊥`.

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

variable {α : Type*} {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

open FirstOrder.Arithmetic Formula ProvabilityAbstraction.Provability in
/-- `T + ¬Con(T)` proves every `□`-formula under both `T` and its own provability, so both
interpretations agree. -/
lemma provabilityLogicRelativeTo_add_incon_eq :
    T.provabilityLogicRelativeTo (T ∪ T.Incon) = (T ∪ T.Incon).provabilityLogic (α := α) := by
  have h₁ : T ∪ T.Incon ⊢ T.standardProvability ⊥ :=
    of_NN (by_axm (by simp) : T ∪ T.Incon ⊢ ∼T.consistent.val)
  have h₂ : T ∪ T.Incon ⊢ (T ∪ T.Incon).standardProvability ⊥ :=
    WeakerThan.pbl (provable_standardProvability_imp_of_Δ₁Class_subset
      (fun _ _ _ _ hp ↦ Theory.Δ₁Class.mem_union.mpr (.inl hp)) ⊥) ⨀ h₁
  have key (f : Realization α ℒₒᵣ) (A : Formula α) : T ∪ T.Incon ⊢ f T A 🡘 f (T ∪ T.Incon) A := by
    induction A with
    | atom | falsum => simp only [standardInterpret, interpret]; exact E_id
    | imp A B ihA ihB =>
      simp only [standardInterpret, interpret] at *; exact ECC_of_E_of_E ihA ihB
    | box A =>
      have hT : T ∪ T.Incon ⊢ T.standardProvability (f T A) := WeakerThan.pbl (mono efq) ⨀ h₁
      have hU : T ∪ T.Incon ⊢ (T ∪ T.Incon).standardProvability (f (T ∪ T.Incon) A) :=
        WeakerThan.pbl (mono efq) ⨀ h₂
      simp only [standardInterpret, interpret] at *
      exact E_intro (C_of_conseq hU) (C_of_conseq hT)
  ext A
  exact forall_congr' fun f ↦ ⟨fun h ↦ K_left (key f A) ⨀ h, fun h ↦ K_right (key f A) ⨀ h⟩

open FirstOrder.Arithmetic in
/-- The provability logic of `T` relative to `T + ¬Con(T)` is `GL + □⊥`. -/
theorem Logic.GLPlusBoxBot.eq_provabilityLogicRelativeTo_add_incon [Consistent T] :
    GLPlusBoxBot 1 = T.provabilityLogicRelativeTo (T ∪ T.Incon) (α := α) := by
  rw [provabilityLogicRelativeTo_add_incon_eq, ← eq_provabilityLogic, height_union_incon_eq_one]

end FFL.ProvabilityLogic

end
