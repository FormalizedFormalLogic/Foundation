module

public import Foundation.FirstOrder.Incompleteness.Reflection.Unboundedness

/-!
# A prenex $\Pi_{n+1}$ axiomatization of local $\Sigma_n$ reflection

If `T` contains `𝗜𝚺₁` and `𝗕𝚺 n`, the extension of `T` by local $\Sigma_n$ reflection is
equivalent to an extension of `T` by a $\Delta_1$-definable set of prenex $\Pi_{n+1}$ sentences.

## References

- [AB05, Section 4.2]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping

variable (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) [NeZero n]

private noncomputable def sigmaReflectionPremise : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “x. !(isSemiformula ℒₒᵣ).sigma 0 x ∧ !(shiftGraph ℒₒᵣ) x x ∧
    (∃ θ <⁺ x, !(qqToPrenexDef 𝚺 n) x θ ∧ !isBounded.sigma θ) ∧ !(provable T) x”

private noncomputable def sigmaReflectionFormula : ArithmeticSemisentence 1 :=
  (sigmaReflectionPremise T n).val 🡒 (partialTruth 𝚺 n).val

variable {T n}

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma exists_prenex_of_quote_eq_qqToPrenex :
    ∀ {Γ : Polarity} {s k : ℕ} {σ : ArithmeticSemisentence k} {θ : V},
      (⌜σ⌝ : V) = qqToPrenex Γ s θ → IsBounded θ → ∃ φ : Prenex Γ s Empty k, σ = φ.val
  | _, 0, _, σ, _, h, hb => ⟨⟨⟨σ, (isBounded_quote_iff σ).mp (by rwa [h, qqToPrenex_zero])⟩⟩, rfl⟩
  | 𝚺, s + 1, k, σ, θ, h, hb => by
    cases σ using Semiformula.cases' with
    | hexs ψ =>
      obtain ⟨φ, rfl⟩ := exists_prenex_of_quote_eq_qqToPrenex (Γ := 𝚷) (by simpa using h) hb;
      exact ⟨φ.sigma, Prenex.val_sigma.symm⟩;
    | _ => simp [Sentence.quote_def, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll,
        qqExs] at h;
  | 𝚷, s + 1, k, σ, θ, h, hb => by
    cases σ using Semiformula.cases' with
    | hall ψ =>
      obtain ⟨φ, rfl⟩ := exists_prenex_of_quote_eq_qqToPrenex (Γ := 𝚺) (by simpa using h) hb;
      exact ⟨φ.pi, Prenex.val_pi.symm⟩;
    | _ => simp [Sentence.quote_def, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll,
        qqExs] at h;

private lemma eval_sigmaReflectionPremise (x : V) :
    V ⊧/![x] (sigmaReflectionPremise T n).val ↔
      IsSemiformula ℒₒᵣ (0 : V) x ∧ shift ℒₒᵣ x = x ∧
        (∃ θ ≤ x, x = qqToPrenex 𝚺 n θ ∧ IsBounded θ) ∧ Provable T x := by
  sorry

private lemma eval_sigmaReflectionFormula (x : V) :
    V ⊧/![x] (sigmaReflectionFormula T n) ↔
      (IsSemiformula ℒₒᵣ (0 : V) x ∧ shift ℒₒᵣ x = x ∧
        (∃ θ ≤ x, x = qqToPrenex 𝚺 n θ ∧ IsBounded θ) ∧ Provable T x → PartialTruth 𝚺 n x) := by
  sorry

private lemma exists_prenex_eq_quote {m : ℕ} (hsemi : IsSemiformula ℒₒᵣ (0 : V) (m : V))
    (hshift : shift ℒₒᵣ (m : V) = m)
    (hpre : ∃ θ ≤ (m : V), (m : V) = qqToPrenex 𝚺 n θ ∧ IsBounded θ) :
    ∃ φ : Prenex 𝚺 n Empty 0, m = ⌜φ.val⌝ := by
  sorry

end

private lemma provable_sigmaReflectionFormula_of_not_code {m : ℕ}
    (h : ∀ φ : Prenex 𝚺 n Empty 0, m ≠ ⌜φ.val⌝) :
    𝗜𝚺₁ ⊢ (sigmaReflectionFormula T n)/[↑m] := by
  sorry

private lemma provable_sigmaReflectionFormula_iff (φ : Prenex 𝚺 n Empty 0) :
    𝗜𝚺₁ ⊢ (sigmaReflectionFormula T n)/[↑(⌜φ.val⌝ : ℕ)] 🡘
      (T.standardProvability φ.val 🡒 φ.val) := by
  sorry

variable (T n) in
private lemma exists_matrix_sigmaReflectionPremise :
    ∃ θ : ℬ[<, ℒₒᵣ].Semisentence 2,
      𝗜𝚺₁ ⊢ ∀¹* ((sigmaReflectionPremise T n).val 🡘 ∃¹ θ.val) :=
  ISigma1.exists_matrix_provable (by simp)

variable (T n) in
private noncomputable def sigmaReflectionPremiseMatrix : ℬ[<, ℒₒᵣ].Semisentence 2 :=
  (exists_matrix_sigmaReflectionPremise T n).choose

variable (T n) in
private noncomputable def sigmaReflectionBody : ArithmeticSemisentence 2 :=
  “u x. ¬!(sigmaReflectionPremiseMatrix T n).val u x ∨ !(partialTruth 𝚺 n).val x”

variable (T n) in
private lemma exists_prenex_sigmaReflectionBody :
    ∃ φ : Prenex 𝚺 n Empty 2, 𝗕𝚺 n ⊢ ∀¹* (sigmaReflectionBody T n 🡘 φ.val) :=
  exists_prenex_of_hierarchy (𝗕𝚺 n) <| by
    sorry

-- The vacuous disjunct `x ≠ x` makes the free variable occur in every numeral instance.
variable (T n) in
private noncomputable def sigmaReflectionFormulaPrenex : Prenex 𝚷 (n + 1) Empty 1 :=
  ⟨⟨“!!(#⟨n + 1, by omega⟩) ≠ !!(#⟨n + 1, by omega⟩)” ⋎
      (exists_prenex_sigmaReflectionBody T n).choose.pi.matrix.val,
    by sorry⟩⟩

private lemma le_quote_sigmaReflectionFormulaPrenex (m : ℕ) :
    m ≤ (⌜((sigmaReflectionFormulaPrenex T n).val/[↑m] : ArithmeticSentence)⌝ : ℕ) := by
  sorry

private lemma eval_sigmaReflectionFormulaPrenex {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗕𝚺 n] (x : V) :
    V ⊧/![x] (sigmaReflectionFormulaPrenex T n).val ↔
      V ⊧/![x] (sigmaReflectionFormula T n) := by
  sorry

variable (T n) in
private noncomputable def sigmaReflectionTheory : ArithmeticTheory :=
  Set.range fun m : ℕ ↦ ((sigmaReflectionFormulaPrenex T n).val/[↑m] : ArithmeticSentence)

variable [𝗜𝚺₁ ⪯ T] [𝗕𝚺 n ⪯ T]

private lemma provable_sigmaReflectionFormulaPrenex_iff (m : ℕ) :
    T ⊢ (sigmaReflectionFormulaPrenex T n).val/[↑m] 🡘 (sigmaReflectionFormula T n)/[↑m] := by
  sorry

private lemma localReflectionOn_Sigma_equiv_union_range :
    T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] T ≊
      T ∪ Set.range fun m : ℕ ↦ ((sigmaReflectionFormula T n)/[↑m] : ArithmeticSentence) := by
  sorry

private lemma localReflectionOn_Sigma_equiv_union_sigmaReflectionTheory :
    T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] T ≊ T ∪ sigmaReflectionTheory T n := by
  sorry

theorem exists_prenex_axiomatization_localReflectionOn_Sigma :
    ∃ (U : ArithmeticTheory) (_ : U.Δ₁), (∀ σ ∈ U, ∃ φ : Prenex 𝚷 (n + 1) Empty 0, φ.val = σ) ∧
      T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] T ≊ T ∪ U := by
  use sigmaReflectionTheory T n,
    Theory.Δ₁.numeralInstances _ le_quote_sigmaReflectionFormulaPrenex;
  and_intros;
  · rintro _ ⟨m, rfl⟩;
    exact ⟨(sigmaReflectionFormulaPrenex T n).rew (Rew.subst ![↑m]), Prenex.val_rew _ _⟩;
  · exact localReflectionOn_Sigma_equiv_union_sigmaReflectionTheory;

end FFL.FirstOrder.Arithmetic
