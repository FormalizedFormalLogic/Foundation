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

variable (T : ArithmeticTheory) [T.Δ₁] (n : ℕ)

private noncomputable def sigmaReflectionPremise : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “x. !(isSemiformula ℒₒᵣ).sigma 0 x ∧ !(shiftGraph ℒₒᵣ) x x ∧
    !(isPrenexHierarchy 𝚺 n).sigma x ∧ !(provable T) x”

variable {T n}

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma eval_sigmaReflectionPremise (x : V) :
    V ⊧/![x] (sigmaReflectionPremise T n).val ↔
      IsSemiformula ℒₒᵣ (0 : V) x ∧ shift ℒₒᵣ x = x ∧ IsPrenexHierarchy 𝚺 n x ∧ Provable T x := by
  simp [sigmaReflectionPremise, eq_comm];

private lemma exists_prenex_eq_quote {m : ℕ}
    (hsemi : IsSemiformula ℒₒᵣ (0 : V) (m : V))
    (hshift : shift ℒₒᵣ (m : V) = m)
    (hpre : IsPrenexHierarchy 𝚺 n (m : V)) :
    ∃ φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 n Empty 0, m = ⌜φ.val⌝ := by
  obtain ⟨F, hF⟩ := IsSemiformula.sound <| isSemiformula_natCast_iff.mpr hsemi;
  have hshiftN : shift ℒₒᵣ m = m := by
    have h := DefinedFunction.shigmaOne_absolute_func V
      shift.defined (shift.defined (L := ℒₒᵣ) (V := V)) ![m];
    simp only [Matrix.cons_val_zero, Function.comp_apply] at h;
    exact_mod_cast h.trans hshift;
  have hF' : Rewriting.shift F = F := by
    apply (Semiformula.quote_inj_iff (V := ℕ)).mp;
    rw [Semiformula.quote_shift, hF, hshiftN];
  obtain ⟨σ, rfl⟩ : ∃ σ : ArithmeticSentence, ⌜σ⌝ = m :=
    ⟨F.toEmpty (Semiformula.freeVariables_eq_empty_of_shift_eq hF'),
      by simp [Sentence.quote_def, hF]⟩;
  rw [Sentence.coe_quote_eq_quote] at hpre;
  obtain ⟨φ, rfl⟩ := (isPrenexHierarchy_quote_iff σ).mp hpre;
  exact ⟨φ, rfl⟩;

end

variable (T n) in
private lemma exists_matrix_sigmaReflectionPremise :
    ∃ θ : ℬ[<, ℒₒᵣ].Semisentence 2,
      𝗜𝚺₁ ⊢ ∀¹* ((sigmaReflectionPremise T n).val 🡘 ∃¹ θ.val) :=
  ISigma1.exists_matrix_provable (by simp)

variable (T n) in
private noncomputable def sigmaReflectionPremiseMatrix : ℬ[<, ℒₒᵣ].Semisentence 2 :=
  (exists_matrix_sigmaReflectionPremise T n).choose

private lemma eval_prenex_congr {V : Type*} [ORingStructure V] :
    ∀ {Γ : Polarity} {s k : ℕ} {φ ψ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty k},
      (∀ e : Fin (k + s) → V, V ⊧/e φ.matrix.val ↔ V ⊧/e ψ.matrix.val) →
        ∀ e : Fin k → V, V ⊧/e φ.val ↔ V ⊧/e ψ.val
  | _, 0, _, _, _, h, e => h e
  | 𝚺, s + 1, _, φ, ψ, h, e => by
    rw [φ.models_sigmaInv, ψ.models_sigmaInv];
    exact exists_congr fun x ↦
      eval_prenex_congr (fun e ↦ by simp [Bounding.Prenex.sigmaInv, h]) (x :> e)
  | 𝚷, s + 1, _, φ, ψ, h, e => by
    rw [φ.models_piInv, ψ.models_piInv];
    exact forall_congr' fun x ↦
      eval_prenex_congr (fun e ↦ by simp [Bounding.Prenex.piInv, h]) (x :> e)

variable [NeZero n]

variable (T n) in
private noncomputable def sigmaReflectionFormula : ArithmeticSemisentence 1 :=
  (sigmaReflectionPremise T n).val 🡒 (partialTrue 𝚺 n).val

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma eval_sigmaReflectionFormula (x : V) :
    V ⊧/![x] (sigmaReflectionFormula T n) ↔
      (IsSemiformula ℒₒᵣ (0 : V) x ∧ shift ℒₒᵣ x = x ∧
        IsPrenexHierarchy 𝚺 n x ∧ Provable T x → PartialTrue 𝚺 n x) := by
  simp [sigmaReflectionFormula, eval_sigmaReflectionPremise,
    (PartialTrue.sigma_defined (V := V) n).df];

private lemma provable_sigmaReflectionFormula_of_not_code {m : ℕ}
    (h : ∀ φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 n Empty 0, m ≠ ⌜φ.val⌝) :
    𝗜𝚺₁ ⊢ (sigmaReflectionFormula T n)/[↑m] :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have hV : V ⊧/![(m : V)] (sigmaReflectionFormula T n) := by
      rw [eval_sigmaReflectionFormula];
      rintro ⟨hsemi, hshift, hpre, -⟩;
      obtain ⟨φ, hφ⟩ := exists_prenex_eq_quote hsemi hshift hpre;
      exact absurd hφ (h φ);
    simpa [models_iff, numeral_eq_natCast] using hV

private lemma provable_sigmaReflectionFormula_iff (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 n Empty 0) :
    𝗜𝚺₁ ⊢ (sigmaReflectionFormula T n)/[↑(⌜φ.val⌝ : ℕ)] 🡘
      (T.standardProvability φ.val 🡒 φ.val) :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h : V ⊧/![(⌜φ.val⌝ : V)] (sigmaReflectionFormula T n) ↔
        (Provable T (⌜φ.val⌝ : V) → V↓[ℒₒᵣ] ⊧ φ.val) := by
      rw [eval_sigmaReflectionFormula, ← partialTrue_quote_iff φ];
      simp [isPrenexHierarchy_quote_iff];
    simpa [models_iff, Arithmetic.standardProvability_def, numeral_eq_natCast] using h

variable (T n) in
private noncomputable def sigmaReflectionBody : ArithmeticSemisentence 2 :=
  “u x. ¬!(sigmaReflectionPremiseMatrix T n).val u x ∨ !(partialTrue 𝚺 n).val x”

variable (T n) in
private lemma hierarchy_sigmaReflectionBody :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n (sigmaReflectionBody T n) := by
  simp [sigmaReflectionBody, (partialTrue 𝚺 n).sigma_prop]

-- The vacuous disjunct `x ≠ x` makes the free variable occur in every numeral instance.
variable (T n) in
private noncomputable def sigmaReflectionFormulaPrenex : ℬ[<, ℒₒᵣ].Prenex 𝚷 (n + 1) Empty 1 :=
  ⟨⟨“!!(#⟨n + 1, by omega⟩) ≠ !!(#⟨n + 1, by omega⟩)” ⋎
      (hierarchy_sigmaReflectionBody T n).prenex.pi.matrix.val,
    by simp [(hierarchy_sigmaReflectionBody T n).prenex.pi.matrix.bounded,
      Semiformula.Operator.eq_def]⟩⟩

private lemma le_quote_sigmaReflectionFormulaPrenex (m : ℕ) :
    m ≤ (⌜((sigmaReflectionFormulaPrenex T n).val/[↑m] : ArithmeticSentence)⌝ : ℕ) := by
  have hb : ∀ k (h : k < 1 + k),
      (Rew.subst ![(↑m : ArithmeticSemiterm Empty 0)]).qpow k #⟨k, h⟩ =
        (↑m : ArithmeticSemiterm Empty (0 + k)) := by
    intro k;
    induction k with
    | zero => simp
    | succ k ih =>
      exact fun _ ↦ (Rew.q_bvar_succ
        ((Rew.subst ![(↑m : ArithmeticSemiterm Empty 0)]).qpow k) ⟨k, by omega⟩).trans <|
          (congrArg Rew.bShift (ih (by omega))).trans (by simp)
  set R : ℬ[<, ℒₒᵣ].Prenex 𝚷 (n + 1) Empty 0 :=
    (sigmaReflectionFormulaPrenex T n).rew (Rew.subst ![↑m]) with hR;
  have e : ((sigmaReflectionFormulaPrenex T n).val/[↑m] : ArithmeticSentence) = R.val :=
    (Bounding.Prenex.val_rew _ _).symm;
  have h₁ : m < (⌜R.matrix.val⌝ : ℕ) := by
    simp only [hR, sigmaReflectionFormulaPrenex, Bounding.Prenex.rew, Bounding.Semiformula.val_rew,
      LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, Sentence.quote_or];
    apply lt_trans' (lt_or_left _ _);
    simp only [Semiformula.Operator.eq_def, Semiformula.rew_rel_eq_comp, Matrix.comp₂, hb,
      Semiformula.neg_rel, Sentence.quote_notEquals];
    apply lt_of_le_of_lt ?_ (Arithmetic.lt_qqNEQ_left (V := ℕ) _ _);
    simp only [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_numeral_eq_numeral,
      natCast_nat, Bootstrapping.Arithmetic.val_numeral];
    exact (Arithmetic.le_numeral_self (V := ℕ) m).elim (·.le) (·.le);
  rw [e, Bounding.Prenex.val, quote_toPrenex];
  rcases le_qqToPrenex (V := ℕ) (Γ := 𝚷) (s := n + 1) (θ := ⌜R.matrix.val⌝) with e | e;
  · exact e ▸ h₁.le;
  · exact (h₁.trans e).le;

private lemma eval_sigmaReflectionFormulaPrenex {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗕𝚺n] (x : V) :
    V ⊧/![x] (sigmaReflectionFormulaPrenex T n).val ↔
      V ⊧/![x] (sigmaReflectionFormula T n) := by
  set Q := (hierarchy_sigmaReflectionBody T n).prenex;
  have hA : ∀ e : Fin 1 → V, V ⊧/e (sigmaReflectionPremise T n).val ↔
      ∃ u, V ⊧/(u :> e) (sigmaReflectionPremiseMatrix T n).val := by
    have h := models_of_provable (M := V) inferInstance
      (exists_matrix_sigmaReflectionPremise T n).choose_spec;
    simp only [models_iff, Semiformula.eval_allClosure, LogicalConnective.HomClass.map_iff,
      Semiformula.eval_ex, LogicalConnective.Prop.iff_eq] at h;
    exact h;
  calc
    _ ↔ V ⊧/![x] Q.pi.val := eval_prenex_congr (fun e ↦ by simp [sigmaReflectionFormulaPrenex, Q]) _
    _ ↔ ∀ u, V ⊧/![u, x] Q.val := by simp [-Bounding.Prenex.val_piInv]
    _ ↔ ∀ u, V ⊧/![u, x] (sigmaReflectionBody T n) := by
      apply forall_congr';
      intro u;
      symm;
      have h := models_of_provable (M := V) inferInstance
        ((hierarchy_sigmaReflectionBody T n).provable_prenex (𝗕𝚺 n));
      simp only [models_iff, Semiformula.eval_allClosure, LogicalConnective.HomClass.map_iff,
        LogicalConnective.Prop.iff_eq] at h;
      apply h;
    _ ↔ _ := by
      simp [sigmaReflectionBody, sigmaReflectionFormula, hA, imp_iff_not_or, forall_or_right]

variable (T n) in
private noncomputable def sigmaReflectionTheory : ArithmeticTheory :=
  Set.range fun m : ℕ ↦ ((sigmaReflectionFormulaPrenex T n).val/[↑m] : ArithmeticSentence)

variable [𝗜𝚺₁ ⪯ T] [𝗕𝚺n ⪯ T]

private lemma provable_sigmaReflectionFormulaPrenex_iff (m : ℕ) :
    T ⊢ (sigmaReflectionFormulaPrenex T n).val/[↑m] 🡘 (sigmaReflectionFormula T n)/[↑m] :=
  complete.{0} T _ fun V _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* T);
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺n := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* T);
    simpa [models_iff, numeral_eq_natCast, -Bounding.Prenex.val_piInv] using
      eval_sigmaReflectionFormulaPrenex (T := T) (n := n) (m : V)

private lemma localReflectionOn_Sigma_equiv_union_sigmaReflectionTheory :
    T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] T ≊ T ∪ sigmaReflectionTheory T n := by
  set U := sigmaReflectionTheory T n;
  set R := 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] T;
  have hU  : T ⪯ T ∪ U := WeakerThan.ofSubset Set.subset_union_left;
  have hU' : 𝗜𝚺₁ ⪯ T ∪ U := WeakerThan.trans inferInstance hU;
  have hR  : T ⪯ T ∪ R := WeakerThan.ofSubset Set.subset_union_left;
  have hR' : 𝗜𝚺₁ ⪯ T ∪ R := WeakerThan.trans inferInstance hR;
  apply Equiv.antisymm;
  constructor;
  · apply WeakerThan.ofAxm!;
    rintro φ (hφ | ⟨σ, hσ, rfl⟩);
    · exact by_axm <| Set.mem_union_left _ hφ;
    · set φ := Bounding.Hierarchy.prenex hσ;
      have he : T ⊢ σ 🡘 φ.val := by simpa using Bounding.Hierarchy.provable_prenex T hσ;
      have h₁ : T ∪ U ⊢ (sigmaReflectionFormulaPrenex T n).val/[↑(⌜φ.val⌝ : ℕ)] :=
        by_axm <| Set.mem_union_right _ ⟨⌜φ.val⌝, rfl⟩;
      have h₂ := hU.pbl (provable_sigmaReflectionFormulaPrenex_iff (T := T) (n := n) ⌜φ.val⌝);
      have h₃ := hU'.pbl (provable_sigmaReflectionFormula_iff (T := T) φ);
      have h₄ : T ∪ U ⊢ T.standardProvability σ 🡘 T.standardProvability φ.val :=
        hU'.pbl <| T.standardProvability.ext he;
      have h₅ : T ∪ U ⊢ σ 🡘 φ.val := hU.pbl he;
      cl_prover [h₁, h₂, h₃, h₄, h₅];
  · apply WeakerThan.ofAxm!;
    rintro φ (hφ | ⟨m, rfl⟩);
    · exact by_axm <| Set.mem_union_left _ hφ;
    · have h₁ := hR.pbl (provable_sigmaReflectionFormulaPrenex_iff (T := T) (n := n) m);
      have h₂ : T ∪ R ⊢ (sigmaReflectionFormula T n)/[↑m] := by
        by_cases hm : ∃ φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 n Empty 0, m = ⌜φ.val⌝;
        · obtain ⟨φ, rfl⟩ := hm;
          have h₃ : T ∪ R ⊢ T.standardProvability φ.val 🡒 φ.val :=
            by_axm <| Set.mem_union_right _ ⟨φ.val, Bounding.Prenex.val_hierarchy, rfl⟩;
          have h₄ := hR'.pbl (provable_sigmaReflectionFormula_iff (T := T) φ);
          cl_prover [h₃, h₄];
        · exact hR'.pbl <| provable_sigmaReflectionFormula_of_not_code fun φ e ↦ hm ⟨φ, e⟩;
      cl_prover [h₁, h₂];

theorem exists_prenex_axiomatization_localReflectionOn_Sigma :
    ∃ (U : ArithmeticTheory) (_ : U.Δ₁), (∀ σ ∈ U, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 1) σ) ∧
      T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] T ≊ T ∪ U := by
  use sigmaReflectionTheory T n, Theory.Δ₁.numeralInstances _ le_quote_sigmaReflectionFormulaPrenex;
  and_intros;
  · rintro _ ⟨m, rfl⟩;
    exact ⟨
      (sigmaReflectionFormulaPrenex T n).rew (Rew.subst ![↑m]),
      (Bounding.Prenex.val_rew _ _).symm
    ⟩;
  · exact localReflectionOn_Sigma_equiv_union_sigmaReflectionTheory;

end FFL.FirstOrder.Arithmetic
