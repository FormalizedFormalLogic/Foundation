module

public import Foundation.FirstOrder.Incompleteness.Reflection.Unboundedness

/-!
# A prenex $\Pi_2$ axiomatization of local $\Sigma_1$ reflection

The extension of `T` by local $\Sigma_1$ reflection is equivalent to an extension of `T` by a
$\Delta_1$-definable set of prenex $\Pi_2$ sentences.

## References

- [AB05, Section 4.2]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping

variable (T : ArithmeticTheory) [T.Δ₁]

private noncomputable def sigma1ReflectionPremise : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “x. !(isSemiformula ℒₒᵣ).sigma 0 x ∧ !(shiftGraph ℒₒᵣ) x x ∧
    (∃ θ <⁺ x, !(qqToPrenexDef 𝚺 1) x θ ∧ !isBounded.sigma θ) ∧ !(provable T) x”

private noncomputable def sigma1ReflectionFormula : ArithmeticSemisentence 1 :=
  (sigma1ReflectionPremise T).val 🡒 (partialTruth 𝚺 1).val

variable {T}

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma eval_sigma1ReflectionPremise (x : V) :
    V ⊧/![x] (sigma1ReflectionPremise T).val ↔
      IsSemiformula ℒₒᵣ (0 : V) x ∧ shift ℒₒᵣ x = x ∧ (∃ θ ≤ x, x = ^∃ θ ∧ IsBounded θ) ∧
        Provable T x := by
  simp [sigma1ReflectionPremise, eq_comm];

private lemma eval_sigma1ReflectionFormula (x : V) :
    V ⊧/![x] (sigma1ReflectionFormula T) ↔
      (IsSemiformula ℒₒᵣ (0 : V) x ∧ shift ℒₒᵣ x = x ∧ (∃ θ ≤ x, x = ^∃ θ ∧ IsBounded θ) ∧
        Provable T x → PartialTruth 𝚺 1 x) := by
  simp [sigma1ReflectionFormula, eval_sigma1ReflectionPremise,
    (PartialTruth.sigma_defined (V := V) 1).df];

private lemma exists_prenex_eq_quote {m : ℕ} (hsemi : IsSemiformula ℒₒᵣ (0 : V) (m : V))
    (hshift : shift ℒₒᵣ (m : V) = m) (hpre : ∃ θ ≤ (m : V), (m : V) = ^∃ θ ∧ IsBounded θ) :
    ∃ φ : Prenex 𝚺 1 Empty 0, m = ⌜φ.val⌝ := by
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
  cases σ using Semiformula.cases' with
  | hexs ψ =>
    obtain rfl : ⌜ψ⌝ = θ := by simpa using hθ;
    exact ⟨⟨⟨ψ, (isBounded_quote_iff ψ).mp hb⟩⟩, rfl⟩;
  | _ => simp [Sentence.quote_def, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll,
      qqExs] at hθ;

end

private lemma provable_sigma1ReflectionFormula_of_not_code {n : ℕ}
    (h : ∀ φ : Prenex 𝚺 1 Empty 0, n ≠ ⌜φ.val⌝) :
    𝗜𝚺₁ ⊢ (sigma1ReflectionFormula T)/[↑n] :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have hV : V ⊧/![(n : V)] (sigma1ReflectionFormula T) := by
      rw [eval_sigma1ReflectionFormula];
      rintro ⟨hsemi, hshift, hpre, -⟩;
      obtain ⟨φ, hφ⟩ := exists_prenex_eq_quote hsemi hshift hpre;
      exact absurd hφ (h φ);
    simpa [models_iff, numeral_eq_natCast] using hV

private lemma provable_sigma1ReflectionFormula_iff (φ : Prenex 𝚺 1 Empty 0) :
    𝗜𝚺₁ ⊢ (sigma1ReflectionFormula T)/[↑(⌜φ.val⌝ : ℕ)] 🡘
      (T.standardProvability φ.val 🡒 φ.val) :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h : V ⊧/![(⌜φ.val⌝ : V)] (sigma1ReflectionFormula T) ↔
        (Provable T (⌜φ.val⌝ : V) → V↓[ℒₒᵣ] ⊧ φ.val) := by
      have hq : (⌜φ.val⌝ : V) = ^∃ ⌜φ.matrix.val⌝ := quote_toPrenex φ.matrix.val;
      have hpre : ∃ θ ≤ (⌜φ.val⌝ : V), (⌜φ.val⌝ : V) = ^∃ θ ∧ IsBounded θ :=
        ⟨⌜φ.matrix.val⌝, hq ▸ (lt_exists _).le, hq, (isBounded_quote_iff _).mpr φ.matrix.bounded⟩;
      rw [eval_sigma1ReflectionFormula, ← partialTruth_quote_iff φ];
      simp only [Sentence.quote_isSemiformula₀, Sentence.shift_quote, hpre, true_and];
    simpa [models_iff, Arithmetic.standardProvability_def, numeral_eq_natCast,
      -Prenex.val_sigmaInv] using h

variable (T) in
private lemma exists_matrix_sigma1ReflectionPremise :
    ∃ θ : ℬ[<, ℒₒᵣ].Semisentence 2, 𝗜𝚺₁ ⊢ ∀¹* ((sigma1ReflectionPremise T).val 🡘 ∃¹ θ.val) :=
  ISigma1.exists_matrix_provable (by simp)

private lemma exists_matrix_sigma1ReflectionConclusion :
    ∃ θ : ℬ[<, ℒₒᵣ].Semisentence 2, 𝗜𝚺₁ ⊢ ∀¹* ((partialTruth 𝚺 1).val 🡘 ∃¹ θ.val) :=
  ISigma1.exists_matrix_provable (partialTruth 𝚺 1).sigma_prop

variable (T) in
private noncomputable def sigma1ReflectionPremiseMatrix : ℬ[<, ℒₒᵣ].Semisentence 2 :=
  (exists_matrix_sigma1ReflectionPremise T).choose

private noncomputable def sigma1ReflectionConclusionMatrix : ℬ[<, ℒₒᵣ].Semisentence 2 :=
  exists_matrix_sigma1ReflectionConclusion.choose

-- The vacuous disjunct `x ≠ x` makes the free variable occur in every numeral instance.
variable (T) in
private noncomputable def sigma1ReflectionFormulaPrenex : Prenex 𝚷 2 Empty 1 :=
  ⟨⟨“w u x. x ≠ x ∨ ¬!(sigma1ReflectionPremiseMatrix T).val u x ∨
      !sigma1ReflectionConclusionMatrix.val w x”,
    by simp [(sigma1ReflectionPremiseMatrix T).bounded.rew,
      sigma1ReflectionConclusionMatrix.bounded.rew, Semiformula.Operator.eq_def]⟩⟩

private lemma val_sigma1ReflectionFormulaPrenex :
    (sigma1ReflectionFormulaPrenex T).val =
      “x. ∀ u, ∃ w, x ≠ x ∨ ¬!(sigma1ReflectionPremiseMatrix T).val u x ∨
        !sigma1ReflectionConclusionMatrix.val w x” :=
  rfl

private lemma le_quote_sigma1ReflectionFormulaPrenex (n : ℕ) :
    n ≤ (⌜((sigma1ReflectionFormulaPrenex T).val/[↑n] : ArithmeticSentence)⌝ : ℕ) := by
  simp only [val_sigma1ReflectionFormulaPrenex, Rewriting.app_all, Rewriting.app_exs,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, Rew.hom_finitary2,
    Sentence.quote_def, Rew.q_emb, Semiformula.quote_all, Semiformula.quote_ex,
    Semiformula.quote_or];
  apply LE.le.trans' <| le_of_lt <|
    lt_trans (lt_or_left _ _) (lt_trans (lt_exists _) (lt_forall _));
  have : (2 : Fin 3) = (0 : Fin 1).succ.succ := rfl;
  rw [this, Rew.q_bvar_succ, Rew.q_bvar_succ];
  simp only [Semiformula.quote_def, Rew.subst_bvar, Matrix.cons_val_fin_one, Rew.finitary0,
    LCWQIsoGödelQuote.neg, Semiformula.typed_quote_eq, Semiterm.typed_quote_numeral_eq_numeral,
    natCast_nat, Arithmetic.neg_equals, Arithmetic.val_notEquals,
    Bootstrapping.Arithmetic.val_numeral];
  have h := Arithmetic.lt_qqNEQ_left (V := ℕ) (Arithmetic.numeral n) (Arithmetic.numeral n);
  rcases Arithmetic.le_numeral_self (V := ℕ) n with e | e;
  · exact e ▸ h.le;
  · exact (e.trans h).le;

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma eval_sigma1ReflectionFormulaPrenex (x : V) :
    V ⊧/![x] (sigma1ReflectionFormulaPrenex T).val ↔ V ⊧/![x] (sigma1ReflectionFormula T) := by
  have hA := models_of_provable (M := V) inferInstance
    (exists_matrix_sigma1ReflectionPremise T).choose_spec;
  have hB := models_of_provable (M := V) inferInstance
    exists_matrix_sigma1ReflectionConclusion.choose_spec;
  simp [models_iff] at hA hB;
  rw [val_sigma1ReflectionFormulaPrenex];
  simp [sigma1ReflectionFormula, hA, hB, sigma1ReflectionPremiseMatrix,
    sigma1ReflectionConclusionMatrix, exists_or, imp_iff_not_or, forall_or_right];

end

private lemma provable_sigma1ReflectionFormulaPrenex_iff (n : ℕ) :
    𝗜𝚺₁ ⊢ (sigma1ReflectionFormulaPrenex T).val/[↑n] 🡘 (sigma1ReflectionFormula T)/[↑n] :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, numeral_eq_natCast, -Prenex.val_piInv] using
      eval_sigma1ReflectionFormulaPrenex (T := T) (n : V)

variable (T) in
private noncomputable def sigma1ReflectionTheory : ArithmeticTheory :=
  Set.range fun n : ℕ ↦ ((sigma1ReflectionFormulaPrenex T).val/[↑n] : ArithmeticSentence)

variable [𝗜𝚺₁ ⪯ T]

private lemma localReflectionOn_Sigma1_equiv_union_range :
    T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T ≊
      T ∪ Set.range fun n : ℕ ↦ ((sigma1ReflectionFormula T)/[↑n] : ArithmeticSentence) := by
  set R := Set.range fun n : ℕ ↦ ((sigma1ReflectionFormula T)/[↑n] : ArithmeticSentence);
  have hR : 𝗜𝚺₁ ⪯ T ∪ R :=
    WeakerThan.trans (𝓣 := T) inferInstance (WeakerThan.ofSubset Set.subset_union_left);
  have hRfn : 𝗜𝚺₁ ⪯ T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T :=
    WeakerThan.trans (𝓣 := T) inferInstance (WeakerThan.ofSubset Set.subset_union_left);
  have hbroad : T ∪ R ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T := by
    rintro _ ⟨σ, hσ, rfl⟩;
    obtain ⟨φ, hφ⟩ := exists_prenex_of_hierarchy 𝗜𝚺₁ hσ;
    have he : 𝗜𝚺₁ ⊢ σ 🡘 φ.val := by simpa using hφ;
    have h₁ : T ∪ R ⊢ (sigma1ReflectionFormula T)/[↑(⌜φ.val⌝ : ℕ)] :=
      by_axm <| Set.mem_union_right _ ⟨⌜φ.val⌝, rfl⟩;
    have h₂ := hR.pbl (provable_sigma1ReflectionFormula_iff (T := T) φ);
    have h₃ : T ∪ R ⊢ T.standardProvability σ 🡘 T.standardProvability φ.val :=
      hR.pbl <| T.standardProvability.ext' he;
    have h₄ : T ∪ R ⊢ σ 🡘 φ.val := hR.pbl he;
    cl_prover [h₁, h₂, h₃, h₄];
  apply Equiv.antisymm;
  constructor;
  · apply WeakerThan.ofAxm!;
    rintro φ (hφ | hφ);
    · exact by_axm <| Set.mem_union_left _ hφ;
    · exact hbroad hφ;
  · apply WeakerThan.ofAxm!;
    rintro φ (hφ | ⟨n, rfl⟩);
    · exact by_axm <| Set.mem_union_left _ hφ;
    · by_cases hn : ∃ φ : Prenex 𝚺 1 Empty 0, n = ⌜φ.val⌝;
      · obtain ⟨φ, rfl⟩ := hn;
        have h₁ : T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T ⊢ T.standardProvability φ.val 🡒 φ.val :=
          by_axm <| Set.mem_union_right _ ⟨φ.val, Prenex.val_hierarchy, rfl⟩;
        have h₂ := hRfn.pbl (provable_sigma1ReflectionFormula_iff (T := T) φ);
        cl_prover [h₁, h₂];
      · exact hRfn.pbl <|
          provable_sigma1ReflectionFormula_of_not_code fun φ e ↦ hn ⟨φ, e⟩;

private lemma localReflectionOn_Sigma1_equiv_union_sigma1ReflectionTheory :
    T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T ≊ T ∪ sigma1ReflectionTheory T := by
  apply localReflectionOn_Sigma1_equiv_union_range.trans;
  have hR : 𝗜𝚺₁ ⪯ T ∪ Set.range fun n : ℕ ↦
      ((sigma1ReflectionFormula T)/[↑n] : ArithmeticSentence) :=
    WeakerThan.trans (𝓣 := T) inferInstance (WeakerThan.ofSubset Set.subset_union_left);
  have hS : 𝗜𝚺₁ ⪯ T ∪ sigma1ReflectionTheory T :=
    WeakerThan.trans (𝓣 := T) inferInstance (WeakerThan.ofSubset Set.subset_union_left);
  apply Equiv.antisymm;
  constructor;
  · apply WeakerThan.ofAxm!;
    rintro φ (hφ | ⟨n, rfl⟩);
    · exact by_axm <| Set.mem_union_left _ hφ;
    · have h₁ : T ∪ sigma1ReflectionTheory T ⊢ (sigma1ReflectionFormulaPrenex T).val/[↑n] :=
        by_axm <| Set.mem_union_right _ ⟨n, rfl⟩;
      have h₂ := hS.pbl (provable_sigma1ReflectionFormulaPrenex_iff (T := T) n);
      cl_prover [h₁, h₂];
  · apply WeakerThan.ofAxm!;
    rintro φ (hφ | ⟨n, rfl⟩);
    · exact by_axm <| Set.mem_union_left _ hφ;
    · have h₁ : T ∪ (Set.range fun n : ℕ ↦ ((sigma1ReflectionFormula T)/[↑n] : ArithmeticSentence))
          ⊢ (sigma1ReflectionFormula T)/[↑n] :=
        by_axm <| Set.mem_union_right _ ⟨n, rfl⟩;
      have h₂ := hR.pbl (provable_sigma1ReflectionFormulaPrenex_iff (T := T) n);
      cl_prover [h₁, h₂];

theorem exists_prenex_axiomatization_localReflectionOn_Sigma1 :
    ∃ (U : ArithmeticTheory) (_ : U.Δ₁), (∀ σ ∈ U, ∃ φ : Prenex 𝚷 2 Empty 0, φ.val = σ) ∧
      T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T ≊ T ∪ U := by
  use sigma1ReflectionTheory T,
    Theory.Δ₁.numeralInstances _ le_quote_sigma1ReflectionFormulaPrenex;
  and_intros;
  · rintro _ ⟨n, rfl⟩;
    exact ⟨(sigma1ReflectionFormulaPrenex T).rew (Rew.subst ![↑n]), Prenex.val_rew _ _⟩;
  · exact localReflectionOn_Sigma1_equiv_union_sigma1ReflectionTheory;

end FFL.FirstOrder.Arithmetic
