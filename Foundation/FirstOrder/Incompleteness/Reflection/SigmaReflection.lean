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
  simp [sigmaReflectionPremise, eq_comm];

private lemma eval_sigmaReflectionFormula (x : V) :
    V ⊧/![x] (sigmaReflectionFormula T n) ↔
      (IsSemiformula ℒₒᵣ (0 : V) x ∧ shift ℒₒᵣ x = x ∧
        (∃ θ ≤ x, x = qqToPrenex 𝚺 n θ ∧ IsBounded θ) ∧ Provable T x → PartialTruth 𝚺 n x) := by
  simp [sigmaReflectionFormula, eval_sigmaReflectionPremise,
    (PartialTruth.sigma_defined (V := V) n).df];

private lemma exists_prenex_eq_quote {m : ℕ} (hsemi : IsSemiformula ℒₒᵣ (0 : V) (m : V))
    (hshift : shift ℒₒᵣ (m : V) = m)
    (hpre : ∃ θ ≤ (m : V), (m : V) = qqToPrenex 𝚺 n θ ∧ IsBounded θ) :
    ∃ φ : Prenex 𝚺 n Empty 0, m = ⌜φ.val⌝ := by
  obtain ⟨F, hF⟩ :=
    IsSemiformula.sound (L := ℒₒᵣ) (isSemiformula_natCast_iff (V := V) |>.mpr hsemi);
  have hshiftN : shift ℒₒᵣ m = m := by
    have h := DefinedFunction.shigmaOne_absolute_func V
      (shift.defined (L := ℒₒᵣ) (V := ℕ)) (shift.defined (L := ℒₒᵣ) (V := V)) ![m];
    simp only [Matrix.cons_val_zero, Function.comp_apply] at h;
    exact_mod_cast h.trans hshift;
  have hF' : Rewriting.shift F = F := by
    apply (Semiformula.quote_inj_iff (V := ℕ)).mp;
    rw [Semiformula.quote_shift, hF, hshiftN];
  obtain ⟨σ, rfl⟩ : ∃ σ : ArithmeticSentence, ⌜σ⌝ = m :=
    ⟨F.toEmpty (Semiformula.freeVariables_eq_empty_of_shift_eq hF'),
      by simp [Sentence.quote_def, hF]⟩;
  obtain ⟨θ, -, hθ, hb⟩ := hpre;
  rw [Sentence.coe_quote_eq_quote] at hθ;
  obtain ⟨φ, rfl⟩ := exists_prenex_of_quote_eq_qqToPrenex hθ hb;
  exact ⟨φ, rfl⟩;

end

private lemma provable_sigmaReflectionFormula_of_not_code {m : ℕ}
    (h : ∀ φ : Prenex 𝚺 n Empty 0, m ≠ ⌜φ.val⌝) :
    𝗜𝚺₁ ⊢ (sigmaReflectionFormula T n)/[↑m] :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have hV : V ⊧/![(m : V)] (sigmaReflectionFormula T n) := by
      rw [eval_sigmaReflectionFormula];
      rintro ⟨hsemi, hshift, hpre, -⟩;
      obtain ⟨φ, hφ⟩ := exists_prenex_eq_quote hsemi hshift hpre;
      exact absurd hφ (h φ);
    simpa [models_iff, numeral_eq_natCast] using hV

private lemma provable_sigmaReflectionFormula_iff (φ : Prenex 𝚺 n Empty 0) :
    𝗜𝚺₁ ⊢ (sigmaReflectionFormula T n)/[↑(⌜φ.val⌝ : ℕ)] 🡘
      (T.standardProvability φ.val 🡒 φ.val) :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h : V ⊧/![(⌜φ.val⌝ : V)] (sigmaReflectionFormula T n) ↔
        (Provable T (⌜φ.val⌝ : V) → V↓[ℒₒᵣ] ⊧ φ.val) := by
      have hq : (⌜φ.val⌝ : V) = qqToPrenex 𝚺 n ⌜φ.matrix.val⌝ := quote_toPrenex φ.matrix.val;
      have hpre : ∃ θ ≤ (⌜φ.val⌝ : V), (⌜φ.val⌝ : V) = qqToPrenex 𝚺 n θ ∧ IsBounded θ :=
        ⟨⌜φ.matrix.val⌝, hq ▸ le_qqToPrenex, hq, (isBounded_quote_iff _).mpr φ.matrix.bounded⟩;
      rw [eval_sigmaReflectionFormula, ← partialTruth_quote_iff φ];
      simp only [Sentence.quote_isSemiformula₀, Sentence.shift_quote, hpre, true_and];
    simpa [models_iff, Arithmetic.standardProvability_def, numeral_eq_natCast] using h

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
    ∃ φ : Prenex 𝚺 n Empty 2, 𝗕𝚺n ⊢ ∀¹* (sigmaReflectionBody T n 🡘 φ.val) :=
  exists_prenex_of_hierarchy (𝗕𝚺 n) <| by simp [sigmaReflectionBody, (partialTruth 𝚺 n).sigma_prop]

private lemma eval_prenex_congr {V : Type*} [ORingStructure V] :
    ∀ {Γ : Polarity} {s k : ℕ} {φ ψ : Prenex Γ s Empty k},
      (∀ e : Fin (k + s) → V, V ⊧/e φ.matrix.val ↔ V ⊧/e ψ.matrix.val) →
        ∀ e : Fin k → V, V ⊧/e φ.val ↔ V ⊧/e ψ.val
  | _, 0, _, _, _, h, e => h e
  | 𝚺, s + 1, _, φ, ψ, h, e => by
    rw [Prenex.models_sigmaInv φ, Prenex.models_sigmaInv ψ];
    exact exists_congr fun x ↦ eval_prenex_congr (fun e ↦ by simp [Prenex.sigmaInv, h]) (x :> e)
  | 𝚷, s + 1, _, φ, ψ, h, e => by
    rw [Prenex.models_piInv φ, Prenex.models_piInv ψ];
    exact forall_congr' fun x ↦ eval_prenex_congr (fun e ↦ by simp [Prenex.piInv, h]) (x :> e)

-- The vacuous disjunct `x ≠ x` makes the free variable occur in every numeral instance.
variable (T n) in
private noncomputable def sigmaReflectionFormulaPrenex : Prenex 𝚷 (n + 1) Empty 1 :=
  ⟨⟨“!!(#⟨n + 1, by omega⟩) ≠ !!(#⟨n + 1, by omega⟩)” ⋎
      (exists_prenex_sigmaReflectionBody T n).choose.pi.matrix.val,
    by simp [(exists_prenex_sigmaReflectionBody T n).choose.pi.matrix.bounded,
      Semiformula.Operator.eq_def]⟩⟩

private lemma le_quote_sigmaReflectionFormulaPrenex (m : ℕ) :
    m ≤ (⌜((sigmaReflectionFormulaPrenex T n).val/[↑m] : ArithmeticSentence)⌝ : ℕ) := by
  sorry

private lemma eval_sigmaReflectionFormulaPrenex {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗕𝚺n] (x : V) :
    V ⊧/![x] (sigmaReflectionFormulaPrenex T n).val ↔
      V ⊧/![x] (sigmaReflectionFormula T n) := by
  set Q := (exists_prenex_sigmaReflectionBody T n).choose;
  have hA : ∀ e : Fin 1 → V, V ⊧/e (sigmaReflectionPremise T n).val ↔
      ∃ u, V ⊧/(u :> e) (sigmaReflectionPremiseMatrix T n).val := by
    have h := models_of_provable (M := V) inferInstance
      (exists_matrix_sigmaReflectionPremise T n).choose_spec;
    simp only [models_iff, Semiformula.eval_allClosure, LogicalConnective.HomClass.map_iff,
      Semiformula.eval_ex, LogicalConnective.Prop.iff_eq] at h;
    exact h;
  have hQ : ∀ e : Fin 2 → V, V ⊧/e (sigmaReflectionBody T n) ↔ V ⊧/e Q.val := by
    have h := models_of_provable (M := V) inferInstance
      (exists_prenex_sigmaReflectionBody T n).choose_spec;
    simp only [models_iff, Semiformula.eval_allClosure, LogicalConnective.HomClass.map_iff,
      LogicalConnective.Prop.iff_eq] at h;
    exact h;
  calc
    _ ↔ V ⊧/![x] Q.pi.val := eval_prenex_congr (fun e ↦ by simp [sigmaReflectionFormulaPrenex, Q]) _
    _ ↔ ∀ u, V ⊧/![u, x] Q.val := by simp [-Prenex.val_piInv]
    _ ↔ ∀ u, V ⊧/![u, x] (sigmaReflectionBody T n) := forall_congr' fun u ↦ (hQ _).symm
    _ ↔ _ := by
      simp [sigmaReflectionBody, sigmaReflectionFormula, hA, imp_iff_not_or, forall_or_right]

variable (T n) in
private noncomputable def sigmaReflectionTheory : ArithmeticTheory :=
  Set.range fun m : ℕ ↦ ((sigmaReflectionFormulaPrenex T n).val/[↑m] : ArithmeticSentence)

variable [𝗜𝚺₁ ⪯ T] [𝗕𝚺n ⪯ T]

private lemma provable_sigmaReflectionFormulaPrenex_iff (m : ℕ) :
    T ⊢ (sigmaReflectionFormulaPrenex T n).val/[↑m] 🡘 (sigmaReflectionFormula T n)/[↑m] :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := eq_weakerThan_of_BSigma (s := n);
  complete T _ fun (V : Type) _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* T);
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺n := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* T);
    simpa [models_iff, numeral_eq_natCast, -Prenex.val_piInv] using
      eval_sigmaReflectionFormulaPrenex (T := T) (n := n) (m : V)

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
