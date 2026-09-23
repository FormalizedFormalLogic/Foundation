module

public import Foundation.ProvabilityLogic.Logic.Basic
public import Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
# Arithmetical interpretations

Realizations of the modal atoms by sentences, and the interpretation of modal formulas that
reads `□` as a provability predicate.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open FirstOrder FirstOrder.ProvabilityAbstraction

variable {α : Type*} {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}

/-- A realization maps modal atoms to sentences. -/
structure Realization (α : Type*) (L : Language) where
  val : α → Sentence L

namespace Formula

/-- The interpretation of a modal formula under a realization `f`, reading `□` as `𝔅`. -/
@[grind]
def interpret (f : Realization α L) (𝔅 : Provability T₀ T) : Formula α → Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => A.interpret f 𝔅 🡒 B.interpret f 𝔅
  | □A    => 𝔅 (A.interpret f 𝔅)

-- `T` and `[T.Δ₁]` are bound after `f` so that the coercion below can be `standardInterpret`
-- itself: routing it through a lambda leaves a beta-redex in every statement written as `f T A`.
/-- The interpretation reading `□` as the standard provability predicate of `T`. -/
noncomputable abbrev standardInterpret (f : Realization α ℒₒᵣ) (T : ArithmeticTheory) [T.Δ₁] :
    Formula α → Sentence ℒₒᵣ :=
  interpret f T.standardProvability

/-- `f T A` is the standard interpretation `A.standardInterpret f T`. -/
noncomputable instance : CoeFun (Realization α ℒₒᵣ)
    (fun _ ↦ (T : ArithmeticTheory) → [T.Δ₁] → Formula α → Sentence ℒₒᵣ) :=
  ⟨standardInterpret⟩

variable {f : Realization α L} {𝔅 : Provability T₀ T} {A : Formula α}

@[simp, grind =]
lemma interpret_boxItr {n : ℕ} : (□^[n]A).interpret f 𝔅 = 𝔅^[n] (A.interpret f 𝔅) := by
  induction n with
  | zero => rfl;
  | succ n ih => simp [interpret, ih, Function.iterate_succ_apply'];

end Formula

/-- The provability logic of `T` relative to `U`: the modal formulas whose standard
interpretations over `T` are all provable in `U`. -/
def _root_.FFL.FirstOrder.ArithmeticTheory.provabilityLogicRelativeTo (T U : ArithmeticTheory) [T.Δ₁] :
    Logic α :=
  { A | ∀ f : Realization α ℒₒᵣ, U ⊢ f T A }

/-- The provability logic of `T`. -/
abbrev _root_.FFL.FirstOrder.ArithmeticTheory.provabilityLogic (T : ArithmeticTheory) [T.Δ₁] :
    Logic α :=
  T.provabilityLogicRelativeTo T

end FFL.ProvabilityLogic

end
