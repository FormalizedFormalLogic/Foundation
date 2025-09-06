import Foundation.ProvabilityLogic.Provability
import Foundation.FirstOrder.Internal.DerivabilityCondition
import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.Logic.HilbertStyle.Cl
import Foundation.Modal.Hilbert.Normal.Basic

namespace LO

open Entailment FiniteContext
open FirstOrder ProvabilityLogic
open Modal Modal.Hilbert

variable {L : Language} [L.ReferenceableBy L] {T₀ T U : Theory L}

namespace ProvabilityLogic

/-- Mapping modal prop vars to first-order sentence -/
structure Realization (𝔅 : Provability T₀ T) where
  val : ℕ → FirstOrder.Sentence L

abbrev _root_.LO.FirstOrder.ArithmeticTheory.StandardRealization (T : ArithmeticTheory) [T.Δ₁] := Realization T.standardProvability

namespace Realization

/-- Mapping modal formulae to first-order sentence -/
@[coe] def interpret {𝔅 : Provability T₀ T} (f : Realization 𝔅) : Formula ℕ → FirstOrder.Sentence L
  | .atom a => f.val a
  |      □φ => 𝔅 (f.interpret φ)
  |       ⊥ => ⊥
  |   φ ➝ ψ => (f.interpret φ) ➝ (f.interpret ψ)

instance {𝔅 : Provability T₀ T} :
    CoeFun (Realization 𝔅) (fun _ ↦ Formula ℕ → FirstOrder.Sentence L) := ⟨interpret⟩

section

variable {𝔅 : Provability T₀ T} {f : Realization 𝔅} {A B : Modal.Formula _}

lemma interpret_atom_def : f (.atom a) = f.val a := rfl

lemma interpret_imp_def : f (A ➝ B) = (f A) ➝ (f B) := rfl

@[simp] lemma interpret_bot_def : f ⊥ = ⊥ := rfl

lemma interpret_box_def : f (□A) = 𝔅 (f A) := rfl

lemma interpret_boxItr_def (n : ℕ) : f (□^[n] A) = 𝔅^[n] (f A) := by
  induction n <;> simp [interpret_box_def, -Function.iterate_succ, Function.iterate_succ', *]

variable [DecidableEq (Sentence L)]

lemma iff_interpret_neg_inside : U ⊢!. f (∼A) ⭤ ∼(f A) := by
  dsimp [Realization.interpret];
  cl_prover;

lemma iff_interpret_or_inside : U ⊢!. f (A ⋎ B) ⭤ (f A) ⋎ (f B) := by
  dsimp [Realization.interpret];
  cl_prover;

lemma iff_interpret_and_inside : U ⊢!. f (A ⋏ B) ⭤ (f A) ⋏ (f B) := by
  dsimp [Realization.interpret];
  cl_prover;

lemma iff_interpret_neg : U ⊢!. f (∼A) ↔ U ⊢!. ∼(f A) := by
  dsimp [Realization.interpret];
  constructor <;> . intro h; cl_prover [h];

lemma iff_interpret_or : U ⊢!. f (A ⋎ B) ↔ U ⊢!. (f A) ⋎ (f B) := by
  dsimp [Realization.interpret];
  constructor <;> . intro h; cl_prover [h];

lemma iff_interpret_and : U ⊢!. f (A ⋏ B) ↔ U ⊢!. (f A) ⋏ (f B) := by
  dsimp [Realization.interpret];
  constructor <;> . intro h; cl_prover [h];

@[grind]
lemma iff_interpret_and' : U ⊢!. f (A ⋏ B) ↔ U ⊢!. (f A) ∧ U ⊢!. (f B) := by
  dsimp [Realization.interpret];
  constructor;
  . intro h; constructor <;> cl_prover [h];
  . rintro ⟨hA, hB⟩; cl_prover [hA, hB];

@[simp, grind]
lemma iff_interpret_lconj₂ {l : List (Formula _)} : U ⊢!. f (l.conj₂) ↔ ∀ A ∈ l, U ⊢!. f A := by
  induction l using List.induction_with_singleton with
  | hcons a l h ih =>
    rw [List.conj₂_cons_nonempty h (a := a)];
    grind;
  | _ => simp [Realization.interpret];

end

lemma letterless_interpret {𝔅 : Provability T₀ T}
    {f₁ f₂ : Realization 𝔅} (A_letterless : A.letterless) : f₁ A = f₂ A := by
  induction A with
  | hatom a => simp at A_letterless;
  | hfalsum => simp_all [Realization.interpret];
  | himp A B ihA ihB =>
    replace ihA := ihA $ Modal.Formula.letterless.def_imp₁ A_letterless;
    replace ihB := ihB $ Modal.Formula.letterless.def_imp₂ A_letterless;
    simp_all [Realization.interpret];
  | hbox A ihA =>
    replace ihA := ihA $ Modal.Formula.letterless.def_box A_letterless;
    simp_all [Realization.interpret];


end Realization

end LO.ProvabilityLogic
