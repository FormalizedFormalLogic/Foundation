module

public import Foundation.ProvabilityLogic.GLAlpha.Basic
public import Foundation.ProvabilityLogic.GLBetaMinus.Basic
public import Foundation.ProvabilityLogic.GL.Arithmetic

/-!
# Classification of letterless extensions of `GL`

A quasi-normal extension of `GL` by letterless formulas is `GLα` or `GLβ⁻` of its trace,
according as all of its axioms are true in `ℕ` or not.

## References

- [Art86]
- [Bek90]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open FirstOrder FirstOrder.ProvabilityAbstraction LetterlessFormula

namespace Logic.GL

variable {α : Type*} {X : LetterlessFormulaSet}

lemma sumQuasiNormal_eq_GLAlpha (h : ∀ A ∈ X, (trace A).Finite) :
    (𝐆𝐋 +ᴸ X.lift (α := α)) = 𝐆𝐋α X.trace := by
  rw [GLAlpha.eq_sumQuasiNormal_lift,
    sumQuasiNormal_eq_iff (.inr ⟨h, by rintro _ ⟨n, -, rfl⟩; simp⟩)];
  simp [LetterlessFormulaSet.trace];

/-- - [Bek90] -/
theorem sumQuasiNormal_eq_GLAlpha_or_GLBetaMinus :
    ((∀ A ∈ X, (trace A).Finite) ∧ (𝐆𝐋 +ᴸ X.lift (α := α)) = 𝐆𝐋α X.trace) ∨
    ∃ hX : X.traceᶜ.Finite, (𝐆𝐋 +ᴸ X.lift (α := α)) = 𝐆𝐋β⁻ X.trace hX := by
  by_cases h : ∀ A ∈ X, (trace A).Finite;
  · exact .inl ⟨h, sumQuasiNormal_eq_GLAlpha h⟩;
  · push Not at h;
    obtain ⟨B, hB, hinf⟩ := h;
    have hfin := spectrum_finite_or_cofinite.resolve_right hinf;
    have hX : X.traceᶜ.Finite := hfin.subset fun n hn ↦
      LetterlessFormulaSet.mem_spectrum.mp (by simpa [LetterlessFormulaSet.trace] using hn) B hB;
    right;
    use hX;
    rw [GLBetaMinus.eq_sumQuasiNormal_lift,
      sumQuasiNormal_eq_iff (.inl ⟨⟨B, hB, hfin⟩, ⟨_, Set.mem_singleton _, by simpa using hX⟩⟩)];
    simp [LetterlessFormulaSet.trace];

end Logic.GL

/-! ### Regular letterless formulas -/

namespace LetterlessFormula

variable {T : ArithmeticTheory} [T.Δ₁] {A B : LetterlessFormula} {n : ℕ}

/-- A letterless formula is regular if its arithmetical interpretation is true. -/
def Regular (T : ArithmeticTheory) [T.Δ₁] (A : LetterlessFormula) : Prop :=
  ℕ↓[ℒₒᵣ] ⊧ A.interpret ⟨Empty.elim⟩ T.standardProvability

lemma regular_neg : (∼A).Regular T ↔ ¬A.Regular T := by
  simp [Regular, Formula.interpret];

lemma Regular.of_imp [𝗜𝚺₁ ⪯ T] (h : A 🡒 B ∈ 𝐆𝐋) (hA : A.Regular T) :
    B.Regular T := by
  have : ℕ↓[ℒₒᵣ] ⊧ (A 🡒 B).interpret ⟨Empty.elim⟩ T.standardProvability :=
    models_of_provable inferInstance (Logic.GL.arithmetical_soundness h);
  simp_all [Regular, Formula.interpret];

variable [ℕ↓[ℒₒᵣ] ⊧* T]

lemma not_regular_boxItr_bot : ¬Regular T (□^[n]⊥) := by
  induction n with
  | zero => simp [Regular, Formula.interpret];
  | succ n ih =>
    by_contra h;
    exact ih <| models_of_provable inferInstance <|
      T.standardProvability.sound_on (by simpa [Regular, Formula.interpret] using h);

lemma regular_iff_trace_finite [𝗜𝚺₁ ⪯ T] : A.Regular T ↔ (trace A).Finite := by
  constructor;
  · intro h;
    by_contra hinf;
    obtain ⟨m, hm⟩ := (spectrum_finite_or_cofinite.resolve_right hinf).bddAbove;
    exact not_regular_boxItr_bot (T := T) (n := m + 1) <| h.of_imp <|
      Logic.GL.mem_iff_spectrum_eq_univ.mpr <| Set.ext fun k ↦ by
        grind [@hm k, spectrum_imp, spectrum_boxItr_bot];
  · intro h;
    obtain ⟨m, hm⟩ := h.bddAbove;
    exact Regular.of_imp (A := ∼□^[m + 1]⊥)
      (Logic.GL.mem_iff_spectrum_eq_univ.mpr <| Set.ext fun k ↦ by
        grind [@hm k, spectrum_imp, spectrum_neg, spectrum_boxItr_bot])
      (regular_neg.mpr not_regular_boxItr_bot);

end LetterlessFormula

namespace LetterlessFormulaSet

def Regular (T : ArithmeticTheory) [T.Δ₁] (X : LetterlessFormulaSet) : Prop :=
  ∀ A ∈ X, A.Regular T

end LetterlessFormulaSet

namespace Logic.GL

variable {α : Type*} {X : LetterlessFormulaSet}
         {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]

/-- - [Bek90] -/
theorem sumQuasiNormal_classification :
    (X.Regular T ∧ (𝐆𝐋 +ᴸ X.lift (α := α)) = 𝐆𝐋α X.trace) ∨
    (¬X.Regular T ∧ ∃ hX : X.traceᶜ.Finite, (𝐆𝐋 +ᴸ X.lift (α := α)) = 𝐆𝐋β⁻ X.trace hX) := by
  have e : X.Regular T ↔ ∀ A ∈ X, (trace A).Finite := by
    simp [LetterlessFormulaSet.Regular, regular_iff_trace_finite];
  by_cases h : X.Regular T;
  · exact .inl ⟨h, sumQuasiNormal_eq_GLAlpha (e.mp h)⟩;
  · rcases sumQuasiNormal_eq_GLAlpha_or_GLBetaMinus (α := α) (X := X) with h' | h';
    · exact absurd (e.mpr h'.1) h;
    · exact .inr ⟨h, h'⟩;

end Logic.GL

end FFL.ProvabilityLogic

end
