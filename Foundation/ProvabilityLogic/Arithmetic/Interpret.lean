module

public import Foundation.ProvabilityLogic.Logic
public import Foundation.ProvabilityLogic.Letterless
public import Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
# Arithmetical interpretations
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open FirstOrder FirstOrder.ProvabilityAbstraction Formula

variable {α : Type*} {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}

structure Realization (α : Type*) (L : Language) where
  val : α → Sentence L

namespace Formula

@[grind]
def interpret (f : Realization α L) (𝔅 : Provability T₀ T) : Formula α → Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => A.interpret f 𝔅 🡒 B.interpret f 𝔅
  | □A    => 𝔅 (A.interpret f 𝔅)

-- `T` and `[T.Δ₁]` are bound after `f` so that the coercion below can be `standardInterpret`
-- itself: routing it through a lambda leaves a beta-redex in every statement written as `f T A`.
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

lemma interpret_subst {β : Type*} {s : Substitution β α} {A : Formula β} :
    (A⟦s⟧).interpret f 𝔅 = A.interpret ⟨fun a ↦ (s a).interpret f 𝔅⟩ 𝔅 := by
  induction A <;> simp_all [interpret];

lemma interpret_congr_atoms [DecidableEq α] {f₁ f₂ : Realization α L}
    (h : ∀ a ∈ A.atoms, f₁.val a = f₂.val a) : A.interpret f₁ 𝔅 = A.interpret f₂ 𝔅 := by
  induction A with
  | atom a => exact h a (by simp);
  | falsum => rfl;
  | imp A B ihA ihB =>
    simp only [interpret];
    rw [ihA fun a ha ↦ h a (by simp [ha]), ihB fun a ha ↦ h a (by simp [ha])];
  | box A ih => simp only [interpret]; rw [ih fun a ha ↦ h a (by simpa using ha)];

end Formula

namespace LetterlessFormula

variable {A : LetterlessFormula} {f : Realization α L} {𝔅 : Provability T₀ T}

lemma interpret_lift :
    (A.lift : Formula α).interpret f 𝔅 = A.interpret (⟨Empty.elim⟩ : Realization Empty L) 𝔅 := by
  induction A with
  | atom a => exact a.elim;
  | falsum => rfl;
  | imp A B ihA ihB => simp_all [lift, Formula.interpret];
  | box A ih => simp_all [lift, Formula.interpret];

end LetterlessFormula

def _root_.FFL.FirstOrder.ArithmeticTheory.provabilityLogicRelativeTo
    (T U : ArithmeticTheory) [T.Δ₁] : Logic α :=
  { A | ∀ f : Realization α ℒₒᵣ, U ⊢ f T A }

abbrev _root_.FFL.FirstOrder.ArithmeticTheory.provabilityLogic (T : ArithmeticTheory) [T.Δ₁] :
    Logic α :=
  T.provabilityLogicRelativeTo T

section

variable {T U : ArithmeticTheory} [T.Δ₁] {A B : Formula α}

lemma provabilityLogic_mdp
    (h₁ : (A 🡒 B) ∈ (T.provabilityLogicRelativeTo U : Logic α))
    (h₂ : A ∈ (T.provabilityLogicRelativeTo U : Logic α)) :
    B ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  fun f ↦ (h₁ f) ⨀ (h₂ f)

lemma provabilityLogic_subst {s : Substitution α α}
    (h : A ∈ (T.provabilityLogicRelativeTo U : Logic α)) :
    (A⟦s⟧) ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  fun f ↦ by simpa [Formula.interpret_subst] using h ⟨fun a ↦ f T (s a)⟩

end

end FFL.ProvabilityLogic

end
