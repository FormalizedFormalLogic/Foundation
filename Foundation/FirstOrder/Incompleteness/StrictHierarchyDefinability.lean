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

lemma le_qqExs (p : V) : p ≤ ^∃ p := le_of_lt (lt_exists p)

lemma succ_le_qqExs (p : V) : p + 1 ≤ ^∃ p := by
  simp only [qqExs]; exact add_le_add (le_pair_right _ _) (le_refl 1);

@[simp] lemma le_qqExss (p k : V) : p ≤ qqExss p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih =>
    apply le_trans ih;
    rw [qqExss_succ];
    exact le_qqExs _;

@[simp] lemma index_le_qqExss (p k : V) : k ≤ qqExss p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih =>
    rw [qqExss_succ];
    exact le_trans (add_le_add ih (le_refl 1)) (succ_le_qqExs _);

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

/-! ## Vector append -/

section vecAppend

namespace VecAppend

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y w. y = w”
  adjoin := .mkSigma “y x xs ih w. !adjoinDef y x ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil param := param 0
  adjoin (_ x _ ih) := x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end VecAppend

noncomputable def vecAppend (v w : V) : V := VecAppend.construction.result ![w] v

@[simp] lemma vecAppend_nil (w : V) : vecAppend 0 w = w := by
  simp [vecAppend, VecAppend.construction];

@[simp] lemma vecAppend_adjoin (x v w : V) : vecAppend (x ∷ v) w = x ∷ vecAppend v w := by
  simp [vecAppend, VecAppend.construction];

def _root_.FFL.FirstOrder.Arithmetic.vecAppendDef : 𝚺ᴬ₁.Semisentence 3 :=
  VecAppend.blueprint.resultDef

instance vecAppend_defined : 𝚺ᴬ₁-Function₂ (vecAppend : V → V → V) via vecAppendDef :=
  VecAppend.construction.result_defined

instance vecAppend_definable : 𝚺ᴬ₁-Function₂ (vecAppend : V → V → V) :=
  vecAppend_defined.to_definable

instance vecAppend_definable' (Γ m) : Γᴬ-[m + 1]-Function₂ (vecAppend : V → V → V) :=
  vecAppend_definable.of_sigmaOne

@[simp] lemma len_vecAppend (v w : V) : len (vecAppend v w) = len v + len w := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability;
  case nil => simp;
  case adjoin x v ih => simp [vecAppend_adjoin, ih, add_right_comm];

variable {v w i : V}

lemma nth_vecAppend_of_lt (hi : i < len v) : (vecAppend v w).[i] = v.[i] := by
  induction v using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability;
  case nil => simp at hi;
  case adjoin x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩);
    · simp;
    · simp only [vecAppend_adjoin, nth_adjoin_succ];
      exact ih (by simpa using hi);

lemma nth_vecAppend_of_le (hi : len v ≤ i) :
    (vecAppend v w).[i] = w.[i - len v] := by
  induction v using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability;
  case nil => simp;
  case adjoin x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩);
    · simp at hi;
    · simp only [vecAppend_adjoin, nth_adjoin_succ, len_adjoin];
      rw [ih (by simpa using hi), add_tsub_add_eq_tsub_right];

end vecAppend

/-! ## Internal prenex classes -/

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

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma exists_block_iff {f : V → V → V} (hmatrix : ∀ q k : V, q ≤ f q k)
    (hlength : ∀ q k : V, k ≤ f q k) (P : V → Prop) (p : V) :
    (∃ k ≤ p, ∃ q ≤ p, p = f q k ∧ P q) ↔ ∃ k q, p = f q k ∧ P q :=
  ⟨fun ⟨k, _, q, _, h⟩ ↦ ⟨k, q, h⟩,
    fun ⟨k, q, heq, hq⟩ ↦ ⟨k, heq ▸ hlength q k, q, heq ▸ hmatrix q k, heq, hq⟩⟩

mutual
  instance IsStrictSigma.defined :
      ∀ n : ℕ, 𝚫ᴬ₁-Predicate (IsStrictSigma n : V → Prop) via isStrictSigma n
    | 0 => IsBounded.defined
    | n + 1 =>
      have : 𝚫ᴬ₁-Predicate (IsStrictPi n : V → Prop) via isStrictPi n := IsStrictPi.defined n
      .mk ⟨fun v ↦ by
          simp [isStrictSigma, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm],
        fun v ↦ by
          simpa [isStrictSigma, IsStrictSigma, lt_succ_iff_le] using
            exists_block_iff le_qqExss index_le_qqExss (IsStrictPi n) (v 0)⟩

  instance IsStrictPi.defined :
      ∀ n : ℕ, 𝚫ᴬ₁-Predicate (IsStrictPi n : V → Prop) via isStrictPi n
    | 0 => IsBounded.defined
    | n + 1 =>
      have : 𝚫ᴬ₁-Predicate (IsStrictSigma n : V → Prop) via isStrictSigma n :=
        IsStrictSigma.defined n
      .mk ⟨fun v ↦ by
          simp [isStrictPi, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm],
        fun v ↦ by
          simpa [isStrictPi, IsStrictPi, lt_succ_iff_le] using
            exists_block_iff le_qqAlls index_le_qqAlls (IsStrictSigma n) (v 0)⟩
end

instance IsStrictSigma.definable (n : ℕ) : 𝚫ᴬ₁-Predicate (IsStrictSigma n : V → Prop) :=
  (IsStrictSigma.defined n).to_definable

instance IsStrictPi.definable (n : ℕ) : 𝚫ᴬ₁-Predicate (IsStrictPi n : V → Prop) :=
  (IsStrictPi.defined n).to_definable

section

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

end

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

section

variable {p : V}

private lemma isStrictSigma1_of_isBounded_exs (h : IsBounded (^∃ p)) : IsStrictSigma 1 p := by
  obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsBounded.of_ex h;
  have h₁ : IsBounded (Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) := by
    rw [Arithmetic.qqLT]; exact IsBounded.rel;
  exact IsStrictSigma.of_pi (IsBounded.and_iff.mpr ⟨h₁, hq⟩);

private lemma isStrictPi1_of_isBounded_alls (h : IsBounded (^∀ p)) : IsStrictPi 1 p := by
  obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsBounded.of_all h;
  have h₁ : IsBounded (Arithmetic.qqNLT (qqBvar 0) (termBShift ℒₒᵣ t)) := by
    rw [Arithmetic.qqNLT]; exact IsBounded.nrel;
  exact IsStrictPi.of_sigma (IsBounded.or_iff.mpr ⟨h₁, hq⟩);

end

mutual
  private lemma IsStrictPi.of_exs_aux :
      ∀ {n : ℕ} {p : V}, IsStrictPi n (^∃ p) → IsStrictSigma (n + 1) p
    | 0,     _, h => isStrictSigma1_of_isBounded_exs h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
      · rw [qqAlls_zero] at heq; subst heq;
        exact IsStrictSigma.mono (by omega) (IsStrictSigma.of_exs_aux hq);
      · rw [qqAlls_succ] at heq; simp [qqExs, qqAll, pair_ext_iff] at heq;

  private lemma IsStrictSigma.of_exs_aux :
      ∀ {n : ℕ} {p : V}, IsStrictSigma n (^∃ p) → IsStrictSigma (n + 1) p
    | 0,     _, h => isStrictSigma1_of_isBounded_exs h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
      · rw [qqExss_zero] at heq; subst heq;
        exact IsStrictSigma.mono (by omega) (IsStrictPi.of_exs_aux hq);
      · rw [qqExss_succ] at heq;
        simp only [qqExs_inj] at heq;
        exact ⟨k, q, heq, IsStrictPi.mono (by omega) hq⟩;
end

mutual
  private lemma IsStrictSigma.of_all_aux :
      ∀ {n : ℕ} {p : V}, IsStrictSigma n (^∀ p) → IsStrictPi (n + 1) p
    | 0,     _, h => isStrictPi1_of_isBounded_alls h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
      · rw [qqExss_zero] at heq; subst heq;
        exact IsStrictPi.mono (by omega) (IsStrictPi.of_all_aux hq);
      · rw [qqExss_succ] at heq; simp [qqExs, qqAll, pair_ext_iff] at heq;

  private lemma IsStrictPi.of_all_aux :
      ∀ {n : ℕ} {p : V}, IsStrictPi n (^∀ p) → IsStrictPi (n + 1) p
    | 0,     _, h => isStrictPi1_of_isBounded_alls h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
      · rw [qqAlls_zero] at heq; subst heq;
        exact IsStrictPi.mono (by omega) (IsStrictSigma.of_all_aux hq);
      · rw [qqAlls_succ] at heq;
        simp only [qqAll_inj] at heq;
        exact ⟨k, q, heq, IsStrictSigma.mono (by omega) hq⟩;
end

section

variable {n : ℕ} {p : V}

lemma IsStrictSigma.of_exs (h : IsStrictSigma (n + 1) (^∃ p)) : IsStrictSigma (n + 1) p := by
  obtain ⟨k, q, heq, hq⟩ := h;
  rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
  · rw [qqExss_zero] at heq; subst heq;
    exact IsStrictPi.of_exs_aux hq;
  · rw [qqExss_succ] at heq;
    simp only [qqExs_inj] at heq;
    exact ⟨k, q, heq, hq⟩;

lemma IsStrictPi.of_all (h : IsStrictPi (n + 1) (^∀ p)) : IsStrictPi (n + 1) p := by
  obtain ⟨k, q, heq, hq⟩ := h;
  rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
  · rw [qqAlls_zero] at heq; subst heq;
    exact IsStrictSigma.of_all_aux hq;
  · rw [qqAlls_succ] at heq;
    simp only [qqAll_inj] at heq;
    exact ⟨k, q, heq, hq⟩;

end

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

/-! ## Agreement with the external strict hierarchy on quoted formulas -/

-- Indexed by polarity so a single induction on a `StrictHierarchy` derivation proves the `Σ`
-- and `Π` cases at once.
private def IsStrictClass : Polarity → ℕ → V → Prop
  | .sigma, s, p => IsStrictSigma s p
  | .pi, s, p => IsStrictPi s p

private lemma isStrictClass_quote {Γ : Polarity} {s n : ℕ} {ψ : ArithmeticSemiproposition n}
    (h : StrictHierarchy Γ s ψ) : IsStrictClass Γ s (⌜ψ⌝ : V) := by
  induction h with
  | @zero Γ₀ n₀ φ₀ hφ₀ =>
    rcases Γ₀ with _ | _;
    · exact (isBounded_quote_iff_s φ₀).mpr hφ₀;
    · exact (isBounded_quote_iff_s φ₀).mpr hφ₀;
  | @ofAlt Γ₀ s₀ n₀ φ₀ _ ih =>
    rcases Γ₀ with _ | _;
    · exact IsStrictSigma.of_pi ih;
    · exact IsStrictPi.of_sigma ih;
  | exs _ ih =>
    change IsStrictSigma _ _;
    rw [Semiformula.quote_ex];
    exact IsStrictSigma.exs ih;
  | all _ ih =>
    change IsStrictPi _ _;
    rw [Semiformula.quote_all];
    exact IsStrictPi.all ih;

section

variable {n : ℕ} (ψ : ArithmeticSemiproposition n) {p : ℕ}

private lemma exists_ex_of_quote_eq_qqExs (h : (⌜ψ⌝ : ℕ) = ^∃ p) :
    ∃ ψ' : ArithmeticSemiproposition (n + 1), ψ = ∃¹ ψ' ∧ (⌜ψ'⌝ : ℕ) = p := by
  induction ψ using Semiformula.rec' with
  | hexs φ _ => exact ⟨φ, rfl, by simpa using h⟩;
  | _ => simp [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs] at h;

private lemma exists_all_of_quote_eq_qqAll (h : (⌜ψ⌝ : ℕ) = ^∀ p) :
    ∃ ψ' : ArithmeticSemiproposition (n + 1), ψ = ∀¹ ψ' ∧ (⌜ψ'⌝ : ℕ) = p := by
  induction ψ using Semiformula.rec' with
  | hall φ _ => exact ⟨φ, rfl, by simpa using h⟩;
  | _ => simp [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqExs, qqAll] at h;

end

private lemma strictHierarchy_sigma_of_quote_eq_qqExss {s : ℕ}
    (ih : ∀ {n : ℕ} (ψ : ArithmeticSemiproposition n),
      IsStrictPi s (⌜ψ⌝ : ℕ) → StrictHierarchy 𝚷 s ψ) :
    ∀ (k : ℕ) {n : ℕ} (ψ : ArithmeticSemiproposition n) (q : ℕ),
      (⌜ψ⌝ : ℕ) = qqExss q k → IsStrictPi s q → StrictHierarchy 𝚺 (s + 1) ψ
  | 0,     _, ψ, _, heq, hq => by
    rw [qqExss_zero] at heq; subst heq;
    exact .ofAlt (ih ψ hq);
  | k + 1, _, ψ, q, heq, hq => by
    rw [qqExss_succ] at heq;
    obtain ⟨ψ', rfl, heq'⟩ := exists_ex_of_quote_eq_qqExs ψ heq;
    exact .exs (strictHierarchy_sigma_of_quote_eq_qqExss ih k ψ' q heq' hq);

private lemma strictHierarchy_pi_of_quote_eq_qqAlls {s : ℕ}
    (ih : ∀ {n : ℕ} (ψ : ArithmeticSemiproposition n),
      IsStrictSigma s (⌜ψ⌝ : ℕ) → StrictHierarchy 𝚺 s ψ) :
    ∀ (k : ℕ) {n : ℕ} (ψ : ArithmeticSemiproposition n) (q : ℕ),
      (⌜ψ⌝ : ℕ) = qqAlls q k → IsStrictSigma s q → StrictHierarchy 𝚷 (s + 1) ψ
  | 0,     _, ψ, _, heq, hq => by
    rw [qqAlls_zero] at heq; subst heq;
    exact .ofAlt (ih ψ hq);
  | k + 1, _, ψ, q, heq, hq => by
    rw [qqAlls_succ] at heq;
    obtain ⟨ψ', rfl, heq'⟩ := exists_all_of_quote_eq_qqAll ψ heq;
    exact .all (strictHierarchy_pi_of_quote_eq_qqAlls ih k ψ' q heq' hq);

mutual
  private lemma strictHierarchy_sigma_of_isStrictSigma_nat :
      ∀ (s : ℕ) {n : ℕ} (ψ : ArithmeticSemiproposition n),
        IsStrictSigma s (⌜ψ⌝ : ℕ) → StrictHierarchy 𝚺 s ψ
    | 0,     _, ψ, h => .zero ((isBounded_quote_iff_s ψ).mp h)
    | s + 1, _, ψ, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      exact strictHierarchy_sigma_of_quote_eq_qqExss
        (strictHierarchy_pi_of_isStrictPi_nat s) k ψ q heq hq;

  private lemma strictHierarchy_pi_of_isStrictPi_nat :
      ∀ (s : ℕ) {n : ℕ} (ψ : ArithmeticSemiproposition n),
        IsStrictPi s (⌜ψ⌝ : ℕ) → StrictHierarchy 𝚷 s ψ
    | 0,     _, ψ, h => .zero ((isBounded_quote_iff_s ψ).mp h)
    | s + 1, _, ψ, h => by
      obtain ⟨k, q, heq, hq⟩ := h;
      exact strictHierarchy_pi_of_quote_eq_qqAlls
        (strictHierarchy_sigma_of_isStrictSigma_nat s) k ψ q heq hq;
end

section

variable {s n : ℕ} (ψ : ArithmeticSemiproposition n)

private lemma isStrictSigma_quote_iff_nat :
    IsStrictSigma s (⌜ψ⌝ : ℕ) ↔ StrictHierarchy 𝚺 s ψ :=
  ⟨strictHierarchy_sigma_of_isStrictSigma_nat s ψ, fun h ↦ isStrictClass_quote h⟩

private lemma isStrictPi_quote_iff_nat :
    IsStrictPi s (⌜ψ⌝ : ℕ) ↔ StrictHierarchy 𝚷 s ψ :=
  ⟨strictHierarchy_pi_of_isStrictPi_nat s ψ, fun h ↦ isStrictClass_quote h⟩

lemma isStrictSigma_quote_iff_s : IsStrictSigma s (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚺 s ψ :=
  have h : V ⊧/![(⌜ψ⌝ : V)] (isStrictSigma s).val ↔ ℕ ⊧/![(⌜ψ⌝ : ℕ)] (isStrictSigma s).val := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton]
      using models_iff_of_Delta1 (V := V) (σ := isStrictSigma s)
        (IsStrictSigma.defined (V := ℕ) s).proper (IsStrictSigma.defined (V := V) s).proper
        (e := ![⌜ψ⌝])
  by simpa [(IsStrictSigma.defined (V := V) s).df, (IsStrictSigma.defined (V := ℕ) s).df,
    isStrictSigma_quote_iff_nat] using h

lemma isStrictPi_quote_iff_s : IsStrictPi s (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚷 s ψ :=
  have h : V ⊧/![(⌜ψ⌝ : V)] (isStrictPi s).val ↔ ℕ ⊧/![(⌜ψ⌝ : ℕ)] (isStrictPi s).val := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton]
      using models_iff_of_Delta1 (V := V) (σ := isStrictPi s)
        (IsStrictPi.defined (V := ℕ) s).proper (IsStrictPi.defined (V := V) s).proper
        (e := ![⌜ψ⌝])
  by simpa [(IsStrictPi.defined (V := V) s).df, (IsStrictPi.defined (V := ℕ) s).df,
    isStrictPi_quote_iff_nat] using h

end

section

variable {n k : ℕ} (ψ : ArithmeticSemisentence k)

lemma isStrictSigma_quote_iff : IsStrictSigma n (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚺 n ψ := by
  simp [Sentence.quote_def, isStrictSigma_quote_iff_s];

lemma isStrictPi_quote_iff : IsStrictPi n (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚷 n ψ := by
  simp [Sentence.quote_def, isStrictPi_quote_iff_s];

end

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Arithmetic

/-! ## The strict induction theories are `Δ₁` -/

open FFL.FirstOrder.Theory Bootstrapping

noncomputable instance InductionScheme.delta1_strictHierarchy :
    (Γ : Polarity) → (s : ℕ) → (InductionScheme ℒₒᵣ (StrictHierarchy Γ s)).Δ₁
  | 𝚺, s =>
    { ch := chInd (isStrictSigma s)
      mem_iff φ := by
        have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] (chInd (isStrictSigma s)).val)
            ↔ InductionR (IsStrictSigma s) (⌜φ⌝ : ℕ) := by
          simp;
        rw [h];
        exact (inductionR_quote_iff isStrictSigma_quote_iff_s φ).trans
          (mem_inductionScheme_iff φ).symm;
      isDelta1 :=
        Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
          fun _ _ _ ↦ by simp }
  | 𝚷, s =>
    { ch := chInd (isStrictPi s)
      mem_iff φ := by
        have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] (chInd (isStrictPi s)).val)
            ↔ InductionR (IsStrictPi s) (⌜φ⌝ : ℕ) := by
          simp;
        rw [h];
        exact (inductionR_quote_iff isStrictPi_quote_iff_s φ).trans
          (mem_inductionScheme_iff φ).symm;
      isDelta1 :=
        Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
          fun _ _ _ ↦ by simp }

noncomputable instance InductionOnHierarchy.delta1 (Γ : Polarity) (s : ℕ) : (𝗜𝗡𝗗 Γ s).Δ₁ :=
  Theory.Δ₁.add PeanoMinus.delta1 inferInstance

end FFL.FirstOrder.Arithmetic
