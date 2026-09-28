module

public import Foundation.FirstOrder.Incompleteness.BoundedDefinability

/-!
# Internal strict prenex classes

The coded blocks of existential quantifiers `qqExss` and the internal predicates `IsStrictSigma`
and `IsStrictPi` on codes of strict prenex formulas: they are `𝚫ᴬ₁`-definable and agree with
`StrictHierarchy` on quoted formulas. Consequently the induction schemata over strict prenex
classes, and hence the theories `𝗜𝗡𝗗 Γ s` (in particular `𝗜𝚺 s`), are `Δ₁`.

## References

- [HP98, Lemma I.1.69]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Iterated existential quantification -/

section qqExss

def qqExss.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !qqExsDef y ih”

noncomputable def qqExss.construction : PR.Construction V qqExss.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ ^∃ ih
  zero_defined := .mk fun v ↦ by simp [qqExss.blueprint]
  succ_defined := .mk fun v ↦ by simp [qqExss.blueprint, qqExs]

noncomputable def qqExss (p k : V) : V := qqExss.construction.result ![p] k

@[simp] lemma qqExss_zero (p : V) : qqExss p 0 = p := by
  simp [qqExss, qqExss.construction];

@[simp] lemma qqExss_succ (p k : V) : qqExss p (k + 1) = ^∃ (qqExss p k) := by
  simp [qqExss, qqExss.construction];

def _root_.FFL.FirstOrder.Arithmetic.qqExssDef : 𝚺ᴬ₁.Semisentence 3 :=
  qqExss.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qqExss_defined : 𝚺ᴬ₁-Function₂ (qqExss : V → V → V) via qqExssDef := .mk
  fun v ↦ by simp [qqExss.construction.result_defined_iff, qqExssDef]; rfl

instance qqExss_definable : 𝚺ᴬ₁-Function₂ (qqExss : V → V → V) :=
  qqExss_defined.to_definable

instance qqExss_definable' {m : ℕ} (Γ) : Γᴬ-[m + 1]-Function₂ (qqExss : V → V → V) :=
  qqExss_definable.of_sigmaOne

lemma le_qqExs (p : V) : p ≤ ^∃ p := (lt_exists p).le

lemma succ_le_qqExs (p : V) : p + 1 ≤ ^∃ p := add_le_add_left (le_pair_right _ _) 1

@[simp] lemma le_qqExss (p k : V) : p ≤ qqExss p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih =>
    rw [qqExss_succ];
    exact ih.trans (le_qqExs _);

@[simp] lemma index_le_qqExss (p k : V) : k ≤ qqExss p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih =>
    rw [qqExss_succ];
    exact (add_le_add_left ih 1).trans (succ_le_qqExs _);

variable {L : Language} [L.Encodable] [L.LORDefinable] in
@[simp] lemma isUFormula_qqExss {p k : V} : IsUFormula L (qqExss p k) ↔ IsUFormula L p := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih => rw [qqExss_succ, IsUFormula.ex, ih];

variable {p k : V}

lemma neg_qqExss (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqExss p k) = qqAlls (neg ℒₒᵣ p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih =>
    rw [qqExss_succ, neg_ex (isUFormula_qqExss.mpr hp), ih, qqAlls_succ];

lemma neg_qqAlls (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqAlls p k) = qqExss (neg ℒₒᵣ p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih =>
    rw [qqAlls_succ, neg_all (isUFormula_qqAlls.mpr hp), ih, qqExss_succ];

end qqExss

/-! ## Internal strict prenex classes -/

section isStrict

mutual
  def IsStrictSigma : ℕ → V → Prop
    | 0 => IsBounded
    | n + 1 => fun p ↦ ∃ k q, p = qqExss q k ∧ IsStrictPi n q

  def IsStrictPi : ℕ → V → Prop
    | 0 => IsBounded
    | n + 1 => fun p ↦ ∃ k q, p = qqAlls q k ∧ IsStrictSigma n q
end

mutual
  noncomputable def isStrictSigma : ℕ → 𝚫ᴬ₁.Semisentence 1
    | 0 => isBounded
    | n + 1 => .mkDelta
        (.mkSigma “p. ∃ k < p + 1, ∃ q < p + 1, !qqExssDef p q k ∧ !(isStrictPi n).sigma q”)
        (.mkPi “p. ∃ k < p + 1, ∃ q < p + 1, (∀ y, !qqExssDef y q k → y = p) ∧
          !(isStrictPi n).pi q”)

  noncomputable def isStrictPi : ℕ → 𝚫ᴬ₁.Semisentence 1
    | 0 => isBounded
    | n + 1 => .mkDelta
        (.mkSigma “p. ∃ k < p + 1, ∃ q < p + 1, !qqAllsDef p q k ∧ !(isStrictSigma n).sigma q”)
        (.mkPi “p. ∃ k < p + 1, ∃ q < p + 1, (∀ y, !qqAllsDef y q k → y = p) ∧
          !(isStrictSigma n).pi q”)
end

mutual
  instance IsStrictSigma.defined :
      ∀ n : ℕ, 𝚫ᴬ₁-Predicate (IsStrictSigma n : V → Prop) via isStrictSigma n
    | 0 => IsBounded.defined
    | n + 1 =>
      have : 𝚫ᴬ₁-Predicate (IsStrictPi n : V → Prop) via isStrictPi n := IsStrictPi.defined n
      .mk ⟨fun v ↦ by
          simp [isStrictSigma, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm],
        fun v ↦ by
          simp [isStrictSigma, IsStrictSigma, lt_succ_iff_le];
          grind [le_qqExss, index_le_qqExss]⟩

  instance IsStrictPi.defined :
      ∀ n : ℕ, 𝚫ᴬ₁-Predicate (IsStrictPi n : V → Prop) via isStrictPi n
    | 0 => IsBounded.defined
    | n + 1 =>
      have : 𝚫ᴬ₁-Predicate (IsStrictSigma n : V → Prop) via isStrictSigma n :=
        IsStrictSigma.defined n
      .mk ⟨fun v ↦ by
          simp [isStrictPi, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm],
        fun v ↦ by
          simp [isStrictPi, IsStrictPi, lt_succ_iff_le];
          grind [le_qqAlls, index_le_qqAlls]⟩
end

instance IsStrictSigma.definable (n : ℕ) : 𝚫ᴬ₁-Predicate (IsStrictSigma n : V → Prop) :=
  (IsStrictSigma.defined n).to_definable

instance IsStrictPi.definable (n : ℕ) : 𝚫ᴬ₁-Predicate (IsStrictPi n : V → Prop) :=
  (IsStrictPi.defined n).to_definable

variable {n : ℕ} {p : V}

lemma IsStrictSigma.of_pi (h : IsStrictPi n p) : IsStrictSigma (n + 1) p :=
  ⟨0, p, (qqExss_zero p).symm, h⟩

lemma IsStrictPi.of_sigma (h : IsStrictSigma n p) : IsStrictPi (n + 1) p :=
  ⟨0, p, (qqAlls_zero p).symm, h⟩

lemma IsStrictSigma.exs (h : IsStrictSigma (n + 1) p) : IsStrictSigma (n + 1) (^∃ p) := by
  obtain ⟨k, q, rfl, hq⟩ := h;
  exact ⟨k + 1, q, (qqExss_succ q k).symm, hq⟩;

lemma IsStrictPi.all (h : IsStrictPi (n + 1) p) : IsStrictPi (n + 1) (^∀ p) := by
  obtain ⟨k, q, rfl, hq⟩ := h;
  exact ⟨k + 1, q, (qqAlls_succ q k).symm, hq⟩;

mutual
  lemma IsStrictSigma.of_bounded : ∀ {n : ℕ} {p : V}, IsBounded p → IsStrictSigma n p
    | 0,     _, h => h
    | _ + 1, _, h => IsStrictSigma.of_pi (IsStrictPi.of_bounded h)

  lemma IsStrictPi.of_bounded : ∀ {n : ℕ} {p : V}, IsBounded p → IsStrictPi n p
    | 0,     _, h => h
    | _ + 1, _, h => IsStrictPi.of_sigma (IsStrictSigma.of_bounded h)
end

mutual
  lemma IsStrictSigma.mono :
      ∀ {m n : ℕ}, m ≤ n → ∀ {p : V}, IsStrictSigma m p → IsStrictSigma n p
    | 0,     _,     _,  _, h => IsStrictSigma.of_bounded h
    | _ + 1, 0,     hn, _, _ => absurd hn (by omega)
    | _ + 1, _ + 1, hn, _, h => by
      obtain ⟨k, q, rfl, hq⟩ := h;
      exact ⟨k, q, rfl, IsStrictPi.mono (by omega) hq⟩;

  lemma IsStrictPi.mono : ∀ {m n : ℕ}, m ≤ n → ∀ {p : V}, IsStrictPi m p → IsStrictPi n p
    | 0,     _,     _,  _, h => IsStrictPi.of_bounded h
    | _ + 1, 0,     hn, _, _ => absurd hn (by omega)
    | _ + 1, _ + 1, hn, _, h => by
      obtain ⟨k, q, rfl, hq⟩ := h;
      exact ⟨k, q, rfl, IsStrictSigma.mono (by omega) hq⟩;
end

lemma IsStrictSigma.of_isBounded_exs (h : IsBounded (^∃ p)) : IsStrictSigma 1 p := by
  obtain ⟨_, q, ⟨t, -, rfl⟩, hq, rfl⟩ := IsBounded.of_ex h;
  exact IsStrictSigma.of_pi <| IsBounded.and_iff.mpr ⟨by simp [Arithmetic.qqLT], hq⟩;

lemma IsStrictPi.of_isBounded_all (h : IsBounded (^∀ p)) : IsStrictPi 1 p := by
  obtain ⟨_, q, ⟨t, -, rfl⟩, hq, rfl⟩ := IsBounded.of_all h;
  exact IsStrictPi.of_sigma <| IsBounded.or_iff.mpr ⟨by simp [Arithmetic.qqNLT], hq⟩;

mutual
  private lemma IsStrictPi.of_exs_aux :
      ∀ {n : ℕ} {p : V}, IsStrictPi n (^∃ p) → IsStrictSigma (n + 1) p
    | 0,     _, h => IsStrictSigma.of_isBounded_exs h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
      · rw [qqAlls_zero] at heq; subst heq;
        exact IsStrictSigma.mono (by omega) (IsStrictSigma.of_exs_aux hq);
      · rw [qqAlls_succ] at heq; simp [qqExs, qqAll, pair_ext_iff] at heq;

  private lemma IsStrictSigma.of_exs_aux :
      ∀ {n : ℕ} {p : V}, IsStrictSigma n (^∃ p) → IsStrictSigma (n + 1) p
    | 0,     _, h => IsStrictSigma.of_isBounded_exs h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
      · rw [qqExss_zero] at heq; subst heq;
        exact IsStrictSigma.mono (by omega) (IsStrictPi.of_exs_aux hq);
      · exact ⟨k, q, by simpa using heq, IsStrictPi.mono (by omega) hq⟩;
end

mutual
  private lemma IsStrictSigma.of_all_aux :
      ∀ {n : ℕ} {p : V}, IsStrictSigma n (^∀ p) → IsStrictPi (n + 1) p
    | 0,     _, h => IsStrictPi.of_isBounded_all h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
      · rw [qqExss_zero] at heq; subst heq;
        exact IsStrictPi.mono (by omega) (IsStrictPi.of_all_aux hq);
      · rw [qqExss_succ] at heq; simp [qqExs, qqAll, pair_ext_iff] at heq;

  private lemma IsStrictPi.of_all_aux :
      ∀ {n : ℕ} {p : V}, IsStrictPi n (^∀ p) → IsStrictPi (n + 1) p
    | 0,     _, h => IsStrictPi.of_isBounded_all h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
      · rw [qqAlls_zero] at heq; subst heq;
        exact IsStrictPi.mono (by omega) (IsStrictSigma.of_all_aux hq);
      · exact ⟨k, q, by simpa using heq, IsStrictSigma.mono (by omega) hq⟩;
end

lemma IsStrictSigma.of_exs (h : IsStrictSigma (n + 1) (^∃ p)) : IsStrictSigma (n + 1) p := by
  obtain ⟨k, q, heq, hq⟩ := h;
  rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
  · rw [qqExss_zero] at heq; subst heq;
    exact IsStrictPi.of_exs_aux hq;
  · exact ⟨k, q, by simpa using heq, hq⟩;

lemma IsStrictPi.of_all (h : IsStrictPi (n + 1) (^∀ p)) : IsStrictPi (n + 1) p := by
  obtain ⟨k, q, heq, hq⟩ := h;
  rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
  · rw [qqAlls_zero] at heq; subst heq;
    exact IsStrictSigma.of_all_aux hq;
  · exact ⟨k, q, by simpa using heq, hq⟩;

mutual
  lemma IsStrictSigma.neg :
      ∀ {n : ℕ} {p : V}, IsUFormula ℒₒᵣ p → IsStrictSigma n p → IsStrictPi n (neg ℒₒᵣ p)
    | 0,     _, hp, h => IsBounded.neg hp h
    | _ + 1, _, hp, h => by
      obtain ⟨k, q, rfl, hq⟩ := h;
      have hq' : IsUFormula ℒₒᵣ q := isUFormula_qqExss.mp hp;
      exact ⟨k, neg ℒₒᵣ q, neg_qqExss hq', IsStrictPi.neg hq' hq⟩;

  lemma IsStrictPi.neg :
      ∀ {n : ℕ} {p : V}, IsUFormula ℒₒᵣ p → IsStrictPi n p → IsStrictSigma n (neg ℒₒᵣ p)
    | 0,     _, hp, h => IsBounded.neg hp h
    | _ + 1, _, hp, h => by
      obtain ⟨k, q, rfl, hq⟩ := h;
      have hq' : IsUFormula ℒₒᵣ q := isUFormula_qqAlls.mp hp;
      exact ⟨k, neg ℒₒᵣ q, neg_qqAlls hq', IsStrictSigma.neg hq' hq⟩;
end

end isStrict

/-! ## Agreement with `StrictHierarchy` on quoted formulas -/

section quote

-- Indexed by polarity so a single induction on a `StrictHierarchy` derivation proves the `Σ`
-- and `Π` cases at once.
private def IsStrictClass : Polarity → ℕ → V → Prop
  | 𝚺, s, p => IsStrictSigma s p
  | 𝚷, s, p => IsStrictPi s p

private lemma isStrictClass_quote {Γ : Polarity} {s n : ℕ} {ψ : ArithmeticSemiproposition n}
    (h : StrictHierarchy Γ s ψ) : IsStrictClass Γ s (⌜ψ⌝ : V) := by
  induction h with
  | @zero Γ _ φ hφ => cases Γ <;> exact (isBounded_quote_iff_s φ).mpr hφ;
  | @ofAlt Γ _ _ _ _ ih =>
    cases Γ;
    · exact IsStrictSigma.of_pi ih;
    · exact IsStrictPi.of_sigma ih;
  | exs _ ih => simpa [IsStrictClass] using IsStrictSigma.exs ih;
  | all _ ih => simpa [IsStrictClass] using IsStrictPi.all ih;

mutual
  private lemma strictHierarchy_sigma_of_isStrictSigma_aux :
      ∀ (s : ℕ) {n : ℕ} (ψ : ArithmeticSemiproposition n),
        IsStrictSigma s (⌜ψ⌝ : ℕ) → StrictHierarchy 𝚺 s ψ
    | 0,     _, ψ, h => .zero ((isBounded_quote_iff_s ψ).mp h)
    | s + 1, n, ψ, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      induction k generalizing n ψ with
      | zero =>
        exact .ofAlt <| strictHierarchy_pi_of_isStrictPi_aux s ψ <| by simpa [heq] using hq;
      | succ k ih =>
        induction ψ using Semiformula.rec' with
        | hexs φ _ => exact .exs <| ih _ φ <| by simpa using heq;
        | _ => simp [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs] at heq;

  private lemma strictHierarchy_pi_of_isStrictPi_aux :
      ∀ (s : ℕ) {n : ℕ} (ψ : ArithmeticSemiproposition n),
        IsStrictPi s (⌜ψ⌝ : ℕ) → StrictHierarchy 𝚷 s ψ
    | 0,     _, ψ, h => .zero ((isBounded_quote_iff_s ψ).mp h)
    | s + 1, n, ψ, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      induction k generalizing n ψ with
      | zero =>
        exact .ofAlt <| strictHierarchy_sigma_of_isStrictSigma_aux s ψ <| by simpa [heq] using hq;
      | succ k ih =>
        induction ψ using Semiformula.rec' with
        | hall φ _ => exact .all <| ih _ φ <| by simpa using heq;
        | _ => simp [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs] at heq;
end

variable {s n : ℕ}

lemma isStrictSigma_quote_iff_s (ψ : ArithmeticSemiproposition n) :
    IsStrictSigma s (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚺 s ψ := by
  have h : IsStrictSigma s (⌜ψ⌝ : V) ↔ IsStrictSigma s (⌜ψ⌝ : ℕ) := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton,
      (IsStrictSigma.defined (V := V) s).df, (IsStrictSigma.defined (V := ℕ) s).df]
      using models_iff_of_Delta1 (V := V) (IsStrictSigma.defined s).proper
        (IsStrictSigma.defined s).proper (e := ![⌜ψ⌝]);
  exact h.trans ⟨strictHierarchy_sigma_of_isStrictSigma_aux s ψ, isStrictClass_quote⟩;

lemma isStrictPi_quote_iff_s (ψ : ArithmeticSemiproposition n) :
    IsStrictPi s (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚷 s ψ := by
  have h : IsStrictPi s (⌜ψ⌝ : V) ↔ IsStrictPi s (⌜ψ⌝ : ℕ) := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton,
      (IsStrictPi.defined (V := V) s).df, (IsStrictPi.defined (V := ℕ) s).df]
      using models_iff_of_Delta1 (V := V) (IsStrictPi.defined s).proper
        (IsStrictPi.defined s).proper (e := ![⌜ψ⌝]);
  exact h.trans ⟨strictHierarchy_pi_of_isStrictPi_aux s ψ, isStrictClass_quote⟩;

theorem isStrictSigma_quote_iff (ψ : ArithmeticSemisentence n) :
    IsStrictSigma s (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚺 s ψ := by
  simp [Sentence.quote_def, isStrictSigma_quote_iff_s];

theorem isStrictPi_quote_iff (ψ : ArithmeticSemisentence n) :
    IsStrictPi s (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚷 s ψ := by
  simp [Sentence.quote_def, isStrictPi_quote_iff_s];

end quote

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Arithmetic

/-! ## The strict induction theories are `Δ₁` -/

open FFL.FirstOrder.Theory Bootstrapping

noncomputable instance InductionScheme.delta1_strictHierarchy :
    (Γ : Polarity) → (s : ℕ) → (InductionScheme ℒₒᵣ (StrictHierarchy Γ s)).Δ₁
  | 𝚺, s =>
    { ch := chInd (isStrictSigma s)
      mem_iff φ := by
        simpa using
          (inductionR_quote_iff isStrictSigma_quote_iff_s φ).trans (mem_inductionScheme_iff φ).symm;
      isDelta1 :=
        Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
          fun _ _ _ ↦ by simp }
  | 𝚷, s =>
    { ch := chInd (isStrictPi s)
      mem_iff φ := by
        simpa using
          (inductionR_quote_iff isStrictPi_quote_iff_s φ).trans (mem_inductionScheme_iff φ).symm;
      isDelta1 :=
        Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
          fun _ _ _ ↦ by simp }

noncomputable instance InductionOnHierarchy.delta1 (Γ : Polarity) (s : ℕ) : (𝗜𝗡𝗗 Γ s).Δ₁ :=
  Δ₁.add PeanoMinus.delta1 inferInstance

end FFL.FirstOrder.Arithmetic
