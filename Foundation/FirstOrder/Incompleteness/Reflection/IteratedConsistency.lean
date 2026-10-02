module

public import Foundation.FirstOrder.Incompleteness.Reflection.Local
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Height

/-!
# A prenex $\Pi_1$ axiomatization of $T_\omega$

The extension $T_\omega$ of `T` by all iterated consistency statements $\neg\Box_T^n\bot$ is
equivalent to an extension of `T` by a $\Delta_1$-definable set of prenex $\Pi_1$ sentences.

## References

- [AB05, Section 4.1]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping Bootstrapping.Arithmetic

variable (T : ArithmeticTheory) [T.Δ₁]

private noncomputable def notProvableIterateBot : 𝚷ᴬ₁.Semisentence 1 := .mkPi
  “x. ∀ y, !substNumeralItrDef y !!(⌜(provable T).val⌝) !!(⌜(⊥ : ArithmeticSentence)⌝) x →
    ¬!(provable T) y”

variable {T}

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma eval_notProvableIterateBot (x : V) :
    V ⊧/![x] (notProvableIterateBot T).val ↔
      ¬Provable T (substNumeralItr ⌜(provable T).val⌝ ⌜(⊥ : ArithmeticSentence)⌝ x) := by
  simp [notProvableIterateBot];

private lemma substNumeralItr_provable_bot (n : ℕ) :
    substNumeralItr (⌜(provable T).val⌝ : V) ⌜(⊥ : ArithmeticSentence)⌝ (n : V) =
      ⌜T.standardProvability^[n] ⊥⌝ :=
  substNumeralItr_quote _ _ n

end

variable (T) in
private lemma exists_matrix_notProvableIterateBot :
    ∃ θ : ℬ[<, ℒₒᵣ].Semisentence 2, 𝗜𝚺₁ ⊢ ∀¹* ((notProvableIterateBot T).val 🡘 ∀¹ θ.val) :=
  ISigma1.exists_matrix_provable_pi (by simp)

variable (T) in
private noncomputable def notProvableIterateBotMatrix : ℬ[<, ℒₒᵣ].Semisentence 2 :=
  (exists_matrix_notProvableIterateBot T).choose

-- The vacuous disjunct `x ≠ x` makes the free variable occur in every numeral instance.
variable (T) in
private noncomputable def notProvableIterateBotPrenex : Prenex 𝚷 1 Empty 1 :=
  ⟨⟨“y x. x ≠ x ∨ !(notProvableIterateBotMatrix T).val y x”,
    by simp [(notProvableIterateBotMatrix T).bounded.rew, Semiformula.Operator.eq_def]⟩⟩

private lemma val_notProvableIterateBotPrenex :
    (notProvableIterateBotPrenex T).val =
      “x. ∀ y, x ≠ x ∨ !(notProvableIterateBotMatrix T).val y x” :=
  rfl

private lemma le_quote_notProvableIterateBotPrenex (n : ℕ) :
    n ≤ (⌜((notProvableIterateBotPrenex T).val/[↑n] : ArithmeticSentence)⌝ : ℕ) := by
  simp only [val_notProvableIterateBotPrenex, Rewriting.app_all,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, Rew.hom_finitary2,
    Sentence.quote_def, Rew.q_emb, Semiformula.quote_all, Semiformula.quote_or];
  apply LE.le.trans' (le_of_lt <| lt_trans (lt_or_left _ _) (lt_forall _));
  have : (1 : Fin 2) = (0 : Fin 1).succ := rfl;
  rw [this, Rew.q_bvar_succ];
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

private lemma eval_notProvableIterateBotPrenex (x : V) :
    V ⊧/![x] (notProvableIterateBotPrenex T).val ↔ V ⊧/![x] (notProvableIterateBot T).val := by
  have h := models_of_provable (M := V) inferInstance
    (exists_matrix_notProvableIterateBot T).choose_spec;
  simp [models_iff] at h;
  rw [val_notProvableIterateBotPrenex];
  simp [h, notProvableIterateBotMatrix];

end

private lemma provable_notProvableIterateBotPrenex_iff (n : ℕ) :
    𝗜𝚺₁ ⊢ (notProvableIterateBotPrenex T).val/[↑n] 🡘 T.standardProvability.conItr (n + 1) :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h : V ⊧/![(n : V)] (notProvableIterateBotPrenex T).val ↔
        ¬Provable T (⌜T.standardProvability^[n] ⊥⌝ : V) := by
      rw [eval_notProvableIterateBotPrenex, eval_notProvableIterateBot,
        substNumeralItr_provable_bot];
    simpa [models_iff, ProvabilityAbstraction.Provability.conItr, Function.iterate_succ_apply',
      Arithmetic.standardProvability_def, numeral_eq_natCast, -Prenex.val_piInv] using h

variable (T) in
private noncomputable def notProvableIterateBotTheory : ArithmeticTheory :=
  Set.range fun n : ℕ ↦ ((notProvableIterateBotPrenex T).val/[↑n] : ArithmeticSentence)

variable [𝗜𝚺₁ ⪯ T]

private lemma turingOmega_equiv_union_notProvableIterateBotTheory :
    T ∪ Set.range T.standardProvability.conItr ≊ T ∪ notProvableIterateBotTheory T := by
  apply Equiv.antisymm;
  constructor;
  · apply WeakerThan.ofAxm!;
    rintro σ (hσ | ⟨_ | n, rfl⟩);
    · exact by_axm <| Set.mem_union_left _ hσ;
    · simp [ProvabilityAbstraction.Provability.conItr];
    · have h₁ : T ∪ notProvableIterateBotTheory T ⊢ (notProvableIterateBotPrenex T).val/[↑n] :=
        by_axm <| Set.mem_union_right _ ⟨n, rfl⟩;
      exact (K_left <| WeakerThan.pbl <| provable_notProvableIterateBotPrenex_iff n) ⨀ h₁;
  · apply WeakerThan.ofAxm!;
    rintro σ (hσ | ⟨n, rfl⟩);
    · exact by_axm <| Set.mem_union_left _ hσ;
    · have h₁ : T ∪ Set.range T.standardProvability.conItr ⊢
          T.standardProvability.conItr (n + 1) :=
        by_axm <| Set.mem_union_right _ ⟨n + 1, rfl⟩;
      exact (K_right <| WeakerThan.pbl <| provable_notProvableIterateBotPrenex_iff n) ⨀ h₁;

theorem exists_prenex_axiomatization_turingOmega :
    ∃ (U : ArithmeticTheory) (_ : U.Δ₁), (∀ σ ∈ U, ∃ φ : Prenex 𝚷 1 Empty 0, φ.val = σ) ∧
      T ∪ Set.range T.standardProvability.conItr ≊ T ∪ U := by
  use notProvableIterateBotTheory T,
    Theory.Δ₁.numeralInstances _ le_quote_notProvableIterateBotPrenex;
  and_intros;
  · rintro _ ⟨n, rfl⟩;
    exact ⟨(notProvableIterateBotPrenex T).rew (Rew.subst ![↑n]), Prenex.val_rew _ _⟩;
  · exact turingOmega_equiv_union_notProvableIterateBotTheory;

end FFL.FirstOrder.Arithmetic
