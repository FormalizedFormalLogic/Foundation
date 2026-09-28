module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Bounded

/-!
# Internal arithmetical hierarchy

The internal predicates `IsHierarchy Γ n` and `IsStrictHierarchy Γ n` on codes of formulas: they
are `𝚫ᴬ₁`-definable and agree with `ℬ[<, ℒₒᵣ].Hierarchy` and `ℬ[<, ℒₒᵣ].StrictHierarchy` on quoted
formulas. Both are `IsBounded` at level `0`; only `IsHierarchy` admits bounded quantifiers above.

## References

- [HP98, Lemma I.1.69]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Unbounded quantifier of a given polarity -/

section qqQuant

noncomputable def qqQuant : Polarity → V → V
  | 𝚺, p => ^∃ p
  | 𝚷, p => ^∀ p

@[simp] lemma qqQuant_sigma (p : V) : qqQuant 𝚺 p = ^∃ p := rfl

@[simp] lemma qqQuant_pi (p : V) : qqQuant 𝚷 p = ^∀ p := rfl

def _root_.FFL.FirstOrder.Arithmetic.qqQuantDef : Polarity → 𝚺ᴬ₀.Semisentence 2
  | 𝚺 => qqExsDef
  | 𝚷 => qqAllDef

instance qqQuant_defined (Γ : Polarity) :
    𝚺ᴬ₀-Function₁ (qqQuant Γ : V → V) via qqQuantDef Γ := by
  cases Γ;
  · exact qqExsists_defined;
  · exact qqForall_defined;

@[simp] lemma lt_qqQuant (Γ : Polarity) (p : V) : p < qqQuant Γ p := by
  cases Γ <;> simp [lt_exists, lt_forall];

variable {Γ Γ' : Polarity} {p q : V}

@[simp] lemma qqQuant_inj : qqQuant Γ p = qqQuant Γ' q ↔ Γ = Γ' ∧ p = q := by
  cases Γ <;> cases Γ' <;> simp [qqExs, qqAll];

@[simp] lemma isUFormula_qqQuant {L : Language} [L.Encodable] [L.LORDefinable] :
    IsUFormula L (qqQuant Γ p) ↔ IsUFormula L p := by
  cases Γ <;> simp;

lemma neg_qqQuant (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqQuant Γ p) = qqQuant Γ.alt (neg ℒₒᵣ p) := by
  cases Γ <;> simp [hp];

end qqQuant

/-! ## Internal hierarchy predicates

`IsHierarchyOf bq Γ n` is generated from `IsBounded` by `⋏`, `⋎` and unbounded quantifiers, and
also by bounded quantifiers when `bq` holds. -/

section isHierarchy

namespace IsHierarchyF

variable (bq : Bool)

def Phi (Γ : Polarity) (P : V → Prop) (C : Set V) (p : V) : Prop :=
  P p ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (bq ∧ ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBall u q) ∨
  (bq ∧ ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBex u q) ∨
  (∃ q, q ∈ C ∧ p = qqQuant Γ q)

private lemma phi_iff (Γ : Polarity) (P : V → Prop) (C p : V) :
    Phi bq Γ P {x | x ∈ C} p ↔
    P p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
    (bq ∧ ∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBall u q) ∨
    (bq ∧ ∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBex u q) ∨
    (∃ q < p, q ∈ C ∧ p = qqQuant Γ q) := by
  constructor;
  · rintro (hp | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨hb, u, q, ⟨t, ht, rfl⟩, hq, rfl⟩
      | ⟨hb, u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨q, hq, rfl⟩);
    · disj 1; exact hp;
    · disj 2; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩;
    · disj 3; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩;
    · disj 4;
      exact ⟨hb, termBShift ℒₒᵣ t, by simp, q, by simp,
        ⟨t, lt_of_le_of_lt (le_termBShift ht) (by simp), ht, rfl⟩, hq, rfl⟩;
    · disj 5;
      exact ⟨hb, termBShift ℒₒᵣ t, by simp, q, by simp,
        ⟨t, lt_of_le_of_lt (le_termBShift ht) (by simp), ht, rfl⟩, hq, rfl⟩;
    · disj 6; exact ⟨q, by simp, hq, rfl⟩;
  · unfold Phi;
    rintro (hp | ⟨p₁, _, p₂, _, hp, hq, rfl⟩ | ⟨p₁, _, p₂, _, hp, hq, rfl⟩
      | ⟨hb, u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩ | ⟨hb, u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩
      | ⟨q, _, hq, rfl⟩) <;> grind;

/-- The bounded-quantifier clauses of `blueprint`, present only when `bq`. -/
noncomputable def bqDef : Bool → 𝚫ᴬ₁.Semisentence 2
  | false => .mkDelta (.mkSigma “p C. ⊥”) (.mkPi “p C. ⊥”)
  | true => .mkDelta
    (.mkSigma “p C.
      (∃ u < p, ∃ q < p, (∃ t < p, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ q ∈ C
         ∧ !qqBallDef p u q) ∨
      (∃ u < p, ∃ q < p, (∃ t < p, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ q ∈ C
         ∧ !qqBexDef p u q)”)
    (.mkPi “p C.
      (∃ u < p, ∃ q < p,
        (∃ t < p, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧
        q ∈ C ∧ ∀ p', !qqBallDef p' u q → p = p') ∨
      (∃ u < p, ∃ q < p,
        (∃ t < p, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧
        q ∈ C ∧ ∀ p', !qqBexDef p' u q → p = p')”)

noncomputable def blueprint (Γ : Polarity) (θ : 𝚫ᴬ₁.Semisentence 1) :
    Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “p C.
    !θ.sigma p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    !(bqDef bq).sigma p C ∨
    (∃ q < p, q ∈ C ∧ !(qqQuantDef Γ) p q)”)
  (.mkPi “p C.
    !θ.pi p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    !(bqDef bq).pi p C ∨
    (∃ q < p, q ∈ C ∧ !(qqQuantDef Γ) p q)”)⟩

def construction (Γ : Polarity) {P : V → Prop} {θ : 𝚫ᴬ₁.Semisentence 1}
    (hP : 𝚫ᴬ₁-Predicate P via θ) : Fixpoint.Construction V (blueprint bq Γ θ) where
  Φ := fun _ ↦ Phi bq Γ P
  defined := .mk <| by
    have := hP;
    constructor;
    · intro v;
      cases bq <;>
        simp [blueprint, bqDef, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
          (termBShift.defined (L := ℒₒᵣ)).df, qqBall_defined.df, qqBex_defined.df,
          (qqQuant_defined Γ).df];
    · intro v;
      have h := phi_iff bq Γ P (v 1) (v 0);
      cases bq <;>
        simpa [blueprint, bqDef, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
          (termBShift.defined (L := ℒₒᵣ)).df, qqBall_defined.df, qqBex_defined.df,
          (qqQuant_defined Γ).df, or_assoc] using h.symm;
  monotone := by
    unfold Phi;
    intro C C' hC _ x;
    grind;

instance (Γ : Polarity) {P : V → Prop} {θ : 𝚫ᴬ₁.Semisentence 1}
    (hP : 𝚫ᴬ₁-Predicate P via θ) : (construction bq Γ hP).StrongFinite V where
  strong_finite := by
    unfold construction Phi;
    rintro C _ x (h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨_, u, q, ht, hq, rfl⟩
      | ⟨_, u, q, ht, hq, rfl⟩ | ⟨q, hq, rfl⟩) <;>
      grind [lt_K!_left, lt_K!_right, lt_or_left, lt_or_right, lt_q_qqBall, lt_q_qqBex, lt_qqQuant];

end IsHierarchyF

noncomputable def isHierarchyOf (bq : Bool) : Polarity → ℕ → 𝚫ᴬ₁.Semisentence 1
  | _, 0 => isBounded
  | Γ, n + 1 => (IsHierarchyF.blueprint bq Γ (isHierarchyOf bq Γ.alt n)).fixpointDefΔ₁

namespace IsHierarchyF

-- The predicate of each level is bundled with its definability, which the construction of the
-- next level depends on.
noncomputable def pred (bq : Bool) :
    (Γ : Polarity) → (n : ℕ) → {P : V → Prop // 𝚫ᴬ₁-Predicate P via isHierarchyOf bq Γ n}
  | _, 0 => ⟨IsBounded, IsBounded.defined⟩
  | Γ, n + 1 =>
    ⟨(construction bq Γ (pred bq Γ.alt n).2).Fixpoint ![],
      (construction bq Γ (pred bq Γ.alt n).2).fixpoint_definedΔ₁⟩

end IsHierarchyF

def IsHierarchyOf (bq : Bool) (Γ : Polarity) (n : ℕ) (p : V) : Prop :=
  (IsHierarchyF.pred bq Γ n).1 p

abbrev IsHierarchy (Γ : Polarity) (n : ℕ) (p : V) : Prop := IsHierarchyOf true Γ n p

abbrev IsStrictHierarchy (Γ : Polarity) (n : ℕ) (p : V) : Prop := IsHierarchyOf false Γ n p

abbrev IsSigma (n : ℕ) (p : V) : Prop := IsHierarchy 𝚺 n p

abbrev IsPi (n : ℕ) (p : V) : Prop := IsHierarchy 𝚷 n p

abbrev IsStrictSigma (n : ℕ) (p : V) : Prop := IsStrictHierarchy 𝚺 n p

abbrev IsStrictPi (n : ℕ) (p : V) : Prop := IsStrictHierarchy 𝚷 n p

noncomputable abbrev isHierarchy : Polarity → ℕ → 𝚫ᴬ₁.Semisentence 1 := isHierarchyOf true

noncomputable abbrev isStrictHierarchy : Polarity → ℕ → 𝚫ᴬ₁.Semisentence 1 :=
  isHierarchyOf false

noncomputable abbrev isSigma (n : ℕ) : 𝚫ᴬ₁.Semisentence 1 := isHierarchy 𝚺 n

noncomputable abbrev isPi (n : ℕ) : 𝚫ᴬ₁.Semisentence 1 := isHierarchy 𝚷 n

instance IsHierarchyOf.defined (bq : Bool) (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsHierarchyOf (V := V) bq Γ n) via isHierarchyOf bq Γ n :=
  (IsHierarchyF.pred bq Γ n).2

instance IsHierarchyOf.definable (bq : Bool) (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsHierarchyOf (V := V) bq Γ n) :=
  (IsHierarchyOf.defined bq Γ n).to_definable

lemma IsHierarchy.defined (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsHierarchy (V := V) Γ n) via isHierarchy Γ n :=
  IsHierarchyOf.defined true Γ n

lemma IsStrictHierarchy.defined (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsStrictHierarchy (V := V) Γ n) via isStrictHierarchy Γ n :=
  IsHierarchyOf.defined false Γ n

variable {bq : Bool} {Γ : Polarity} {n : ℕ} {p q : V}

lemma IsHierarchyOf.zero_iff : IsHierarchyOf bq Γ 0 p ↔ IsBounded p := by rfl

lemma IsHierarchyOf.succ_iff :
    IsHierarchyOf bq Γ (n + 1) p ↔
    IsHierarchyOf bq Γ.alt n p ∨
    (∃ p₁ p₂, IsHierarchyOf bq Γ (n + 1) p₁ ∧ IsHierarchyOf bq Γ (n + 1) p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsHierarchyOf bq Γ (n + 1) p₁ ∧ IsHierarchyOf bq Γ (n + 1) p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (bq ∧ ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsHierarchyOf bq Γ (n + 1) q
      ∧ p = qqBall u q) ∨
    (bq ∧ ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsHierarchyOf bq Γ (n + 1) q
      ∧ p = qqBex u q) ∨
    (∃ q, IsHierarchyOf bq Γ (n + 1) q ∧ p = qqQuant Γ q) :=
  (IsHierarchyF.construction bq Γ (IsHierarchyF.pred bq Γ.alt n).2).case

alias ⟨IsHierarchyOf.succ_case, IsHierarchyOf.succ_mk⟩ := IsHierarchyOf.succ_iff

lemma IsStrictHierarchy.succ_iff :
    IsStrictHierarchy Γ (n + 1) p ↔
    IsStrictHierarchy Γ.alt n p ∨
    (∃ p₁ p₂, IsStrictHierarchy Γ (n + 1) p₁ ∧ IsStrictHierarchy Γ (n + 1) p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsStrictHierarchy Γ (n + 1) p₁ ∧ IsStrictHierarchy Γ (n + 1) p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ q, IsStrictHierarchy Γ (n + 1) q ∧ p = qqQuant Γ q) := by
  simpa using IsHierarchyOf.succ_iff (bq := false);

lemma IsHierarchyOf.succ_induction (Γ' : Polarity) {P : V → Prop} (hP : Γ'ᴬ-[1]-Predicate P)
    (hbase : ∀ p, IsHierarchyOf bq Γ.alt n p → P p)
    (hand : ∀ p q, IsHierarchyOf bq Γ (n + 1) p → IsHierarchyOf bq Γ (n + 1) q → P p → P q →
      P (p ^⋏ q))
    (hor : ∀ p q, IsHierarchyOf bq Γ (n + 1) p → IsHierarchyOf bq Γ (n + 1) q → P p → P q →
      P (p ^⋎ q))
    (hball : ∀ t q, bq → IsUTerm ℒₒᵣ t → IsHierarchyOf bq Γ (n + 1) q → P q →
      P (qqBall (termBShift ℒₒᵣ t) q))
    (hbex : ∀ t q, bq → IsUTerm ℒₒᵣ t → IsHierarchyOf bq Γ (n + 1) q → P q →
      P (qqBex (termBShift ℒₒᵣ t) q))
    (hquant : ∀ q, IsHierarchyOf bq Γ (n + 1) q → P q → P (qqQuant Γ q)) :
    ∀ p, IsHierarchyOf bq Γ (n + 1) p → P p :=
  (IsHierarchyF.construction bq Γ (IsHierarchyF.pred bq Γ.alt n).2).induction (v := ![]) hP (by
    rintro C hC x (hx | ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩
      | ⟨hb, u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨hb, u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨q, hq, rfl⟩);
    · exact hbase x hx;
    · exact hand p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2;
    · exact hor p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2;
    · exact hball t q hb ht (hC q hq).1 (hC q hq).2;
    · exact hbex t q hb ht (hC q hq).1 (hC q hq).2;
    · exact hquant q (hC q hq).1 (hC q hq).2)

/-! ### Closure properties -/

lemma IsHierarchyOf.of_alt (h : IsHierarchyOf bq Γ.alt n p) : IsHierarchyOf bq Γ (n + 1) p :=
  IsHierarchyOf.succ_mk <| by left; exact h

lemma IsHierarchyOf.of_bounded (h : IsBounded p) : IsHierarchyOf bq Γ n p := by
  induction n generalizing Γ with
  | zero => exact IsHierarchyOf.zero_iff.mpr h;
  | succ n ih => exact IsHierarchyOf.of_alt ih;

@[simp] lemma IsHierarchyOf.verum : IsHierarchyOf bq Γ n (^⊤ : V) :=
  IsHierarchyOf.of_bounded (by simp)

@[simp] lemma IsHierarchyOf.falsum : IsHierarchyOf bq Γ n (^⊥ : V) :=
  IsHierarchyOf.of_bounded (by simp)

@[simp] lemma IsHierarchyOf.rel {k r v : V} : IsHierarchyOf bq Γ n (^rel k r v) :=
  IsHierarchyOf.of_bounded (by simp)

@[simp] lemma IsHierarchyOf.nrel {k r v : V} : IsHierarchyOf bq Γ n (^nrel k r v) :=
  IsHierarchyOf.of_bounded (by simp)

@[simp] lemma IsHierarchyOf.and_iff :
    IsHierarchyOf bq Γ n (p ^⋏ q) ↔ IsHierarchyOf bq Γ n p ∧ IsHierarchyOf bq Γ n q := by
  induction n generalizing Γ with
  | zero => exact IsBounded.and_iff;
  | succ n ih =>
    constructor;
    · intro h;
      rcases h.succ_case with (h | h | h | h | h | h);
      · exact ⟨(ih.mp h).1.of_alt, (ih.mp h).2.of_alt⟩;
      all_goals cases Γ <;> simp_all [qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex];
    · rintro ⟨hp, hq⟩;
      exact IsHierarchyOf.succ_mk <| by disj 2; exact ⟨p, q, hp, hq, rfl⟩;

@[simp] lemma IsHierarchyOf.or_iff :
    IsHierarchyOf bq Γ n (p ^⋎ q) ↔ IsHierarchyOf bq Γ n p ∧ IsHierarchyOf bq Γ n q := by
  induction n generalizing Γ with
  | zero => exact IsBounded.or_iff;
  | succ n ih =>
    constructor;
    · intro h;
      rcases h.succ_case with (h | h | h | h | h | h);
      · exact ⟨(ih.mp h).1.of_alt, (ih.mp h).2.of_alt⟩;
      all_goals cases Γ <;> simp_all [qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex];
    · rintro ⟨hp, hq⟩;
      exact IsHierarchyOf.succ_mk <| by disj 3; exact ⟨p, q, hp, hq, rfl⟩;

lemma IsHierarchyOf.ball {t : V} (hb : bq) (ht : IsUTerm ℒₒᵣ t) (hq : IsHierarchyOf bq Γ n q) :
    IsHierarchyOf bq Γ n (qqBall (termBShift ℒₒᵣ t) q) := by
  cases n with
  | zero => exact IsBounded.ball ht hq;
  | succ n => exact IsHierarchyOf.succ_mk <| by disj 4; exact ⟨hb, _, q, ⟨t, ht, rfl⟩, hq, rfl⟩;

lemma IsHierarchyOf.bex {t : V} (hb : bq) (ht : IsUTerm ℒₒᵣ t) (hq : IsHierarchyOf bq Γ n q) :
    IsHierarchyOf bq Γ n (qqBex (termBShift ℒₒᵣ t) q) := by
  cases n with
  | zero => exact IsBounded.bex ht hq;
  | succ n => exact IsHierarchyOf.succ_mk <| by disj 5; exact ⟨hb, _, q, ⟨t, ht, rfl⟩, hq, rfl⟩;

lemma IsHierarchyOf.quant (h : IsHierarchyOf bq Γ (n + 1) p) :
    IsHierarchyOf bq Γ (n + 1) (qqQuant Γ p) :=
  IsHierarchyOf.succ_mk <| by disj 6; exact ⟨p, h, rfl⟩

lemma IsHierarchyOf.ex (h : IsHierarchyOf bq 𝚺 (n + 1) p) : IsHierarchyOf bq 𝚺 (n + 1) (^∃ p) :=
  IsHierarchyOf.quant h

lemma IsHierarchyOf.all (h : IsHierarchyOf bq 𝚷 (n + 1) p) : IsHierarchyOf bq 𝚷 (n + 1) (^∀ p) :=
  IsHierarchyOf.quant h

lemma IsHierarchyOf.sigma (h : IsHierarchyOf bq 𝚷 n p) : IsHierarchyOf bq 𝚺 (n + 1) (^∃ p) :=
  IsHierarchyOf.ex (IsHierarchyOf.of_alt (Γ := 𝚺) h)

lemma IsHierarchyOf.pi (h : IsHierarchyOf bq 𝚺 n p) : IsHierarchyOf bq 𝚷 (n + 1) (^∀ p) :=
  IsHierarchyOf.all (IsHierarchyOf.of_alt (Γ := 𝚷) h)

lemma IsHierarchyOf.succ (h : IsHierarchyOf bq Γ n p) : IsHierarchyOf bq Γ (n + 1) p := by
  induction n generalizing Γ p with
  | zero => exact IsHierarchyOf.of_bounded h;
  | succ n ih =>
    apply IsHierarchyOf.succ_induction 𝚺 (P := IsHierarchyOf bq Γ (n + 1 + 1)) (by definability)
      (fun p hp ↦ (ih hp).of_alt) (fun p q _ _ hp hq ↦ IsHierarchyOf.and_iff.mpr ⟨hp, hq⟩)
      (fun p q _ _ hp hq ↦ IsHierarchyOf.or_iff.mpr ⟨hp, hq⟩)
      (fun t q hb ht _ hq ↦ IsHierarchyOf.ball hb ht hq)
      (fun t q hb ht _ hq ↦ IsHierarchyOf.bex hb ht hq) (fun q _ hq ↦ IsHierarchyOf.quant hq) p h;

lemma IsHierarchyOf.accum (Γ' : Polarity) (h : IsHierarchyOf bq Γ n p) :
    IsHierarchyOf bq Γ' (n + 1) p := by
  cases Γ <;> cases Γ';
  · exact h.succ;
  · exact IsHierarchyOf.of_alt (Γ := 𝚷) h;
  · exact IsHierarchyOf.of_alt (Γ := 𝚺) h;
  · exact h.succ;

lemma IsHierarchyOf.mono {m : ℕ} (hmn : m ≤ n) (h : IsHierarchyOf bq Γ m p) :
    IsHierarchyOf bq Γ n p := by
  induction hmn with
  | refl => exact h;
  | step _ ih => exact ih.succ;

/-! ### Inversion of unbounded quantifiers -/

lemma IsHierarchyOf.of_all (h : IsHierarchyOf bq Γ (n + 1) (^∀ p)) :
    IsHierarchyOf bq Γ.alt n (^∀ p) ∨
    IsHierarchyOf bq Γ (n + 1) p ∧
      (Γ = 𝚷 ∨ bq ∧ ∃ t q, IsUTerm ℒₒᵣ t ∧ p = (^#0 ^≮ termBShift ℒₒᵣ t) ^⋎ q) := by
  rcases h.succ_case with (h | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
    | ⟨hb, _, q, ⟨t, ht, rfl⟩, hq, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨q, hq, h⟩);
  · left; exact h;
  · simp [qqAll, qqAnd] at h;
  · simp [qqAll, qqOr] at h;
  · obtain rfl := (qqAll_inj _ _).mp h;
    right;
    exact ⟨IsHierarchyOf.or_iff.mpr ⟨by simp [Arithmetic.qqNLT], hq⟩,
      by right; exact ⟨hb, t, q, ht, rfl⟩⟩;
  · simp [qqAll, qqBex, qqExs] at h;
  · cases Γ;
    · simp [qqAll, qqExs] at h;
    · right;
      obtain rfl : p = q := (qqAll_inj _ _).mp h;
      exact ⟨hq, by left; rfl⟩;

lemma IsHierarchyOf.of_ex (h : IsHierarchyOf bq Γ (n + 1) (^∃ p)) :
    IsHierarchyOf bq Γ.alt n (^∃ p) ∨
    IsHierarchyOf bq Γ (n + 1) p ∧
      (Γ = 𝚺 ∨ bq ∧ ∃ t q, IsUTerm ℒₒᵣ t ∧ p = (^#0 ^< termBShift ℒₒᵣ t) ^⋏ q) := by
  rcases h.succ_case with (h | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
    | ⟨hb, _, q, ⟨t, ht, rfl⟩, hq, h⟩ | ⟨q, hq, h⟩);
  · left; exact h;
  · simp [qqExs, qqAnd] at h;
  · simp [qqExs, qqOr] at h;
  · simp [qqExs, qqBall, qqAll] at h;
  · obtain rfl := (qqExs_inj _ _).mp h;
    right;
    exact ⟨IsHierarchyOf.and_iff.mpr ⟨by simp [Arithmetic.qqLT], hq⟩,
      by right; exact ⟨hb, t, q, ht, rfl⟩⟩;
  · cases Γ;
    · right;
      obtain rfl : p = q := (qqExs_inj _ _).mp h;
      exact ⟨hq, by left; rfl⟩;
    · simp [qqAll, qqExs] at h;

/-! ### Negation -/

lemma IsHierarchyOf.neg (hp : IsUFormula ℒₒᵣ p) (h : IsHierarchyOf bq Γ n p) :
    IsHierarchyOf bq Γ.alt n (neg ℒₒᵣ p) := by
  induction n generalizing Γ p with
  | zero => exact IsBounded.neg hp h;
  | succ n ih =>
    suffices ∀ p : V, IsHierarchyOf bq Γ (n + 1) p →
        IsUFormula ℒₒᵣ p → IsHierarchyOf bq Γ.alt (n + 1) (neg ℒₒᵣ p) from this p h hp;
    apply IsHierarchyOf.succ_induction 𝚺
      (P := fun p ↦ IsUFormula ℒₒᵣ p → IsHierarchyOf bq Γ.alt (n + 1) (neg ℒₒᵣ p))
      (by definability);
    · intro p h hp;
      exact IsHierarchyOf.of_alt (Γ := Γ.alt) (by simpa using ih hp h);
    · simp +contextual;
    · simp +contextual;
    · intro t q hb ht _ ih h;
      have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBall];
      simpa [neg_qqBall ht.termBShift hq] using IsHierarchyOf.bex hb ht (ih hq);
    · intro t q hb ht _ ih h;
      have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBex];
      simpa [neg_qqBex ht.termBShift hq] using IsHierarchyOf.ball hb ht (ih hq);
    · intro q _ ih h;
      have hq : IsUFormula ℒₒᵣ q := isUFormula_qqQuant.mp h;
      simpa [neg_qqQuant hq] using IsHierarchyOf.quant (ih hq);

end isHierarchy

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Arithmetic

/-! ## Agreement on quoted formulas -/

section quote

open Bootstrapping

variable {bq : Bool} {Γ : Polarity} {s n : ℕ}

private abbrev bounding (bq : Bool) : Bounding ℒₒᵣ := bif bq then ℬ[<, ℒₒᵣ] else ℬ[ℒₒᵣ]

private lemma isHierarchyOf_of_hierarchyOn {ψ : ArithmeticSemiproposition n}
    (h : (bounding bq).HierarchyOn ℬ[<, ℒₒᵣ].Closure Γ s ψ) :
    IsHierarchyOf bq Γ s (⌜ψ⌝ : ℕ) := by
  induction h with
  | initial _ _ _ h => exact IsHierarchyOf.of_bounded ((isBounded_quote_iff_s _).mpr h);
  | and _ _ ihφ ihψ => simpa [Semiformula.quote_and] using ⟨ihφ, ihψ⟩;
  | or _ _ ihφ ihψ => simpa [Semiformula.quote_or] using ⟨ihφ, ihψ⟩;
  | ball hR ht _ ih =>
    cases bq;
    · exact absurd hR Bounding.not_mem_strict;
    obtain rfl := Set.mem_singleton_iff.mp hR;
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
    change IsHierarchy _ _ (⌜(∀¹[“#0 < !!(Rew.bShift t)”] _ : ArithmeticSemiproposition _)⌝ : ℕ);
    rw [quote_ball];
    exact IsHierarchyOf.ball rfl (by simp [Semiterm.quote_def]) ih;
  | bexs hR ht _ ih =>
    cases bq;
    · exact absurd hR Bounding.not_mem_strict;
    obtain rfl := Set.mem_singleton_iff.mp hR;
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
    change IsHierarchy _ _ (⌜(∃¹[“#0 < !!(Rew.bShift t)”] _ : ArithmeticSemiproposition _)⌝ : ℕ);
    rw [quote_bex];
    exact IsHierarchyOf.bex rfl (by simp [Semiterm.quote_def]) ih;
  | exs _ ih => simpa [Semiformula.quote_ex] using ih.ex;
  | all _ ih => simpa [Semiformula.quote_all] using ih.all;
  | sigma _ ih => simpa [Semiformula.quote_ex] using ih.sigma;
  | pi _ ih => simpa [Semiformula.quote_all] using ih.pi;
  | dummy_sigma _ ih => simpa [Semiformula.quote_all] using IsHierarchyOf.of_alt (Γ := 𝚺) ih.all;
  | dummy_pi _ ih => simpa [Semiformula.quote_ex] using IsHierarchyOf.of_alt (Γ := 𝚷) ih.ex;

private lemma hierarchyOn_of_isHierarchyOf (ψ : ArithmeticSemiproposition n) :
    IsHierarchyOf bq Γ s (⌜ψ⌝ : ℕ) → (bounding bq).HierarchyOn ℬ[<, ℒₒᵣ].Closure Γ s ψ := by
  induction s generalizing Γ n ψ with
  | zero => exact fun h ↦ .initial _ _ _ ((isBounded_quote_iff_s ψ).mp h);
  | succ s ihs =>
    induction ψ using Semiformula.rec' with
    | hverum => simp;
    | hfalsum => simp;
    | hrel => simp;
    | hnrel => simp;
    | hand φ ψ ihφ ihψ =>
      intro h;
      rw [Semiformula.quote_and] at h;
      exact (ihφ (IsHierarchyOf.and_iff.mp h).1).and (ihψ (IsHierarchyOf.and_iff.mp h).2);
    | hor φ ψ ihφ ihψ =>
      intro h;
      rw [Semiformula.quote_or] at h;
      exact (ihφ (IsHierarchyOf.or_iff.mp h).1).or (ihψ (IsHierarchyOf.or_iff.mp h).2);
    | hall φ ih =>
      intro h;
      rw [Semiformula.quote_all] at h;
      rcases IsHierarchyOf.of_all h with (h | ⟨hφ, rfl | ⟨rfl, t, q, ht, e⟩⟩);
      · exact (ihs (∀¹ φ) (by rwa [Semiformula.quote_all])).accum Γ;
      · exact (ih hφ).all;
      · obtain ⟨u, χ, rfl⟩ := exists_ball_of_quote_eq ht e;
        exact Bounding.Hierarchy.arithmetic_ball (Rew.positive_iff.mpr ⟨u, rfl⟩)
          (Bounding.HierarchyOn.imp_iff.mp (ih hφ)).2;
    | hexs φ ih =>
      intro h;
      rw [Semiformula.quote_ex] at h;
      rcases IsHierarchyOf.of_ex h with (h | ⟨hφ, rfl | ⟨rfl, t, q, ht, e⟩⟩);
      · exact (ihs (∃¹ φ) (by rwa [Semiformula.quote_ex])).accum Γ;
      · exact (ih hφ).exs;
      · obtain ⟨u, χ, rfl⟩ := exists_bex_of_quote_eq ht e;
        exact Bounding.Hierarchy.arithmetic_bexs (Rew.positive_iff.mpr ⟨u, rfl⟩)
          (Bounding.HierarchyOn.and_iff.mp (ih hφ)).2;

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma isHierarchyOf_quote_iff_s (ψ : ArithmeticSemiproposition n) :
    IsHierarchyOf bq Γ s (⌜ψ⌝ : V) ↔ (bounding bq).HierarchyOn ℬ[<, ℒₒᵣ].Closure Γ s ψ := by
  simpa [Semiformula.coe_quote_eq_quote] using
    (Defined.shigmaOne_absolute V (IsHierarchyOf.defined bq Γ s)
      (IsHierarchyOf.defined bq Γ s) ![⌜ψ⌝]).symm.trans
      ⟨hierarchyOn_of_isHierarchyOf ψ, isHierarchyOf_of_hierarchyOn⟩;

/-! ### `IsHierarchy` and `ℬ[<, ℒₒᵣ].Hierarchy` -/

lemma isHierarchy_quote_iff_s (ψ : ArithmeticSemiproposition n) :
    IsHierarchy Γ s (⌜ψ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy Γ s ψ :=
  isHierarchyOf_quote_iff_s ψ

theorem isHierarchy_quote_iff (σ : ArithmeticSemisentence n) :
    IsHierarchy Γ s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy Γ s σ := by
  simp [Sentence.quote_def, isHierarchy_quote_iff_s];

theorem isSigma_quote_iff (σ : ArithmeticSemisentence n) :
    IsSigma s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s σ := isHierarchy_quote_iff σ

theorem isPi_quote_iff (σ : ArithmeticSemisentence n) :
    IsPi s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy 𝚷 s σ := isHierarchy_quote_iff σ

/-! ### `IsStrictHierarchy` and `ℬ[<, ℒₒᵣ].StrictHierarchy` -/

lemma isStrictHierarchy_quote_iff_s (ψ : ArithmeticSemiproposition n) :
    IsStrictHierarchy Γ s (⌜ψ⌝ : V) ↔ ℬ[<, ℒₒᵣ].StrictHierarchy Γ s ψ :=
  isHierarchyOf_quote_iff_s ψ

theorem isStrictHierarchy_quote_iff (σ : ArithmeticSemisentence n) :
    IsStrictHierarchy Γ s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].StrictHierarchy Γ s σ := by
  simp [Sentence.quote_def, isStrictHierarchy_quote_iff_s];

theorem isStrictSigma_quote_iff (σ : ArithmeticSemisentence n) :
    IsStrictSigma s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].StrictHierarchy 𝚺 s σ := isStrictHierarchy_quote_iff σ

theorem isStrictPi_quote_iff (σ : ArithmeticSemisentence n) :
    IsStrictPi s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].StrictHierarchy 𝚷 s σ := isStrictHierarchy_quote_iff σ

end quote

end FFL.FirstOrder.Arithmetic
