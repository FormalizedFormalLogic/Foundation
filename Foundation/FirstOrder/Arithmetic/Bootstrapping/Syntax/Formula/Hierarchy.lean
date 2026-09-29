module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Bounded

/-!
# Internal arithmetical hierarchy

The internal predicates `IsHierarchy Γ n` on codes of formulas of the (non-strict) bounded
arithmetical hierarchy, and `IsStrictHierarchy Γ n` on codes of strict prenex formulas: they are
`𝚫ᴬ₁`-definable and agree with `ℬ[<, ℒₒᵣ].Hierarchy` and `StrictHierarchy` on quoted formulas.
Both are `IsBounded` at level `0`.

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

/-! ## Internal hierarchy predicate `IsHierarchy` -/

section isHierarchy

namespace IsHierarchyF

def Phi (Γ : Polarity) (P : V → Prop) (C : Set V) (p : V) : Prop :=
  P p ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBall u q) ∨
  (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBex u q) ∨
  (∃ q, q ∈ C ∧ p = qqQuant Γ q)

private lemma phi_iff (Γ : Polarity) (P : V → Prop) (C p : V) :
    Phi Γ P {x | x ∈ C} p ↔
    P p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBall u q) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBex u q) ∨
    (∃ q < p, q ∈ C ∧ p = qqQuant Γ q) := by
  constructor;
  · rintro (hp | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩
      | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨q, hq, rfl⟩);
    · disj 1; exact hp;
    · disj 2; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩;
    · disj 3; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩;
    · disj 4;
      exact ⟨termBShift ℒₒᵣ t, by simp, q, by simp,
        ⟨t, lt_of_le_of_lt (le_termBShift ht) (by simp), ht, rfl⟩, hq, rfl⟩;
    · disj 5;
      exact ⟨termBShift ℒₒᵣ t, by simp, q, by simp,
        ⟨t, lt_of_le_of_lt (le_termBShift ht) (by simp), ht, rfl⟩, hq, rfl⟩;
    · disj 6; exact ⟨q, by simp, hq, rfl⟩;
  · unfold Phi;
    rintro (hp | ⟨p₁, _, p₂, _, hp, hq, rfl⟩ | ⟨p₁, _, p₂, _, hp, hq, rfl⟩
      | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩ | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩
      | ⟨q, _, hq, rfl⟩) <;> grind;

noncomputable def blueprint (Γ : Polarity) (θ : 𝚫ᴬ₁.Semisentence 1) :
    Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “p C.
    !θ.sigma p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ q ∈ C
       ∧ !qqBallDef p u q) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ q ∈ C
       ∧ !qqBexDef p u q) ∨
    (∃ q < p, q ∈ C ∧ !(qqQuantDef Γ) p q)”)
  (.mkPi “p C.
    !θ.pi p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ u < p, ∃ q < p,
      (∃ t < p, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧
      q ∈ C ∧ ∀ p', !qqBallDef p' u q → p = p') ∨
    (∃ u < p, ∃ q < p,
      (∃ t < p, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧
      q ∈ C ∧ ∀ p', !qqBexDef p' u q → p = p') ∨
    (∃ q < p, q ∈ C ∧ !(qqQuantDef Γ) p q)”)⟩

def construction (Γ : Polarity) {P : V → Prop} {θ : 𝚫ᴬ₁.Semisentence 1}
    (hP : 𝚫ᴬ₁-Predicate P via θ) : Fixpoint.Construction V (blueprint Γ θ) where
  Φ := fun _ ↦ Phi Γ P
  defined := .mk <| by
    have := hP;
    constructor;
    · intro v;
      simp [blueprint, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ)).df, qqBall_defined.df, qqBex_defined.df,
        (qqQuant_defined Γ).df];
    · intro v;
      simpa [blueprint, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ)).df, qqBall_defined.df, qqBex_defined.df,
        (qqQuant_defined Γ).df] using (phi_iff Γ P _ _).symm;
  monotone := by
    unfold Phi;
    intro C C' hC _ x;
    grind;

instance (Γ : Polarity) {P : V → Prop} {θ : 𝚫ᴬ₁.Semisentence 1}
    (hP : 𝚫ᴬ₁-Predicate P via θ) : (construction Γ hP).StrongFinite V where
  strong_finite := by
    unfold construction Phi;
    rintro C _ x (h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨u, q, ht, hq, rfl⟩
      | ⟨u, q, ht, hq, rfl⟩ | ⟨q, hq, rfl⟩) <;>
      grind [lt_K!_left, lt_K!_right, lt_or_left, lt_or_right, lt_q_qqBall, lt_q_qqBex, lt_qqQuant];

end IsHierarchyF

noncomputable def isHierarchy : Polarity → ℕ → 𝚫ᴬ₁.Semisentence 1
  | _, 0 => isBounded
  | Γ, n + 1 => (IsHierarchyF.blueprint Γ (isHierarchy Γ.alt n)).fixpointDefΔ₁

namespace IsHierarchyF

-- The predicate of each level is bundled with its definability, which the construction of the
-- next level depends on.
noncomputable def pred :
    (Γ : Polarity) → (n : ℕ) → {P : V → Prop // 𝚫ᴬ₁-Predicate P via isHierarchy Γ n}
  | _, 0 => ⟨IsBounded, IsBounded.defined⟩
  | Γ, n + 1 =>
    ⟨(construction Γ (pred Γ.alt n).2).Fixpoint ![],
      (construction Γ (pred Γ.alt n).2).fixpoint_definedΔ₁⟩

end IsHierarchyF

def IsHierarchy (Γ : Polarity) (n : ℕ) (p : V) : Prop := (IsHierarchyF.pred Γ n).1 p

abbrev IsSigma (n : ℕ) (p : V) : Prop := IsHierarchy 𝚺 n p

abbrev IsPi (n : ℕ) (p : V) : Prop := IsHierarchy 𝚷 n p

noncomputable abbrev isSigma (n : ℕ) : 𝚫ᴬ₁.Semisentence 1 := isHierarchy 𝚺 n

noncomputable abbrev isPi (n : ℕ) : 𝚫ᴬ₁.Semisentence 1 := isHierarchy 𝚷 n

instance IsHierarchy.defined (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsHierarchy (V := V) Γ n) via isHierarchy Γ n :=
  (IsHierarchyF.pred Γ n).2

instance IsHierarchy.definable (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsHierarchy (V := V) Γ n) :=
  (IsHierarchy.defined Γ n).to_definable

variable {Γ : Polarity} {n : ℕ} {p q : V}

lemma IsHierarchy.zero_iff : IsHierarchy Γ 0 p ↔ IsBounded p := by rfl

lemma IsHierarchy.succ_iff :
    IsHierarchy Γ (n + 1) p ↔
    IsHierarchy Γ.alt n p ∨
    (∃ p₁ p₂, IsHierarchy Γ (n + 1) p₁ ∧ IsHierarchy Γ (n + 1) p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsHierarchy Γ (n + 1) p₁ ∧ IsHierarchy Γ (n + 1) p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsHierarchy Γ (n + 1) q
      ∧ p = qqBall u q) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsHierarchy Γ (n + 1) q
      ∧ p = qqBex u q) ∨
    (∃ q, IsHierarchy Γ (n + 1) q ∧ p = qqQuant Γ q) :=
  (IsHierarchyF.construction Γ (IsHierarchyF.pred Γ.alt n).2).case

alias ⟨IsHierarchy.succ_case, IsHierarchy.succ_mk⟩ := IsHierarchy.succ_iff

lemma IsHierarchy.succ_induction (Γ' : Polarity) {P : V → Prop} (hP : Γ'ᴬ-[1]-Predicate P)
    (hbase : ∀ p, IsHierarchy Γ.alt n p → P p)
    (hand : ∀ p q, IsHierarchy Γ (n + 1) p → IsHierarchy Γ (n + 1) q → P p → P q →
      P (p ^⋏ q))
    (hor : ∀ p q, IsHierarchy Γ (n + 1) p → IsHierarchy Γ (n + 1) q → P p → P q →
      P (p ^⋎ q))
    (hball : ∀ t q, IsUTerm ℒₒᵣ t → IsHierarchy Γ (n + 1) q → P q →
      P (qqBall (termBShift ℒₒᵣ t) q))
    (hbex : ∀ t q, IsUTerm ℒₒᵣ t → IsHierarchy Γ (n + 1) q → P q →
      P (qqBex (termBShift ℒₒᵣ t) q))
    (hquant : ∀ q, IsHierarchy Γ (n + 1) q → P q → P (qqQuant Γ q)) :
    ∀ p, IsHierarchy Γ (n + 1) p → P p :=
  (IsHierarchyF.construction Γ (IsHierarchyF.pred Γ.alt n).2).induction (v := ![]) hP (by
    rintro C hC x (hx | ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩
      | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨q, hq, rfl⟩);
    · exact hbase x hx;
    · exact hand p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2;
    · exact hor p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2;
    · exact hball t q ht (hC q hq).1 (hC q hq).2;
    · exact hbex t q ht (hC q hq).1 (hC q hq).2;
    · exact hquant q (hC q hq).1 (hC q hq).2)

/-! ### Closure properties -/

lemma IsHierarchy.of_alt (h : IsHierarchy Γ.alt n p) : IsHierarchy Γ (n + 1) p :=
  IsHierarchy.succ_mk <| by left; exact h

lemma IsHierarchy.of_bounded (h : IsBounded p) : IsHierarchy Γ n p := by
  induction n generalizing Γ with
  | zero => exact IsHierarchy.zero_iff.mpr h;
  | succ n ih => exact IsHierarchy.of_alt ih;

@[simp] lemma IsHierarchy.verum : IsHierarchy Γ n (^⊤ : V) :=
  IsHierarchy.of_bounded (by simp)

@[simp] lemma IsHierarchy.falsum : IsHierarchy Γ n (^⊥ : V) :=
  IsHierarchy.of_bounded (by simp)

@[simp] lemma IsHierarchy.rel {k r v : V} : IsHierarchy Γ n (^rel k r v) :=
  IsHierarchy.of_bounded (by simp)

@[simp] lemma IsHierarchy.nrel {k r v : V} : IsHierarchy Γ n (^nrel k r v) :=
  IsHierarchy.of_bounded (by simp)

@[simp] lemma IsHierarchy.and_iff :
    IsHierarchy Γ n (p ^⋏ q) ↔ IsHierarchy Γ n p ∧ IsHierarchy Γ n q := by
  induction n generalizing Γ with
  | zero => exact IsBounded.and_iff;
  | succ n ih =>
    constructor;
    · intro h;
      rcases h.succ_case with (h | h | h | h | h | h);
      · exact ⟨(ih.mp h).1.of_alt, (ih.mp h).2.of_alt⟩;
      all_goals cases Γ <;> simp_all [qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex];
    · rintro ⟨hp, hq⟩;
      exact IsHierarchy.succ_mk <| by disj 2; exact ⟨p, q, hp, hq, rfl⟩;

@[simp] lemma IsHierarchy.or_iff :
    IsHierarchy Γ n (p ^⋎ q) ↔ IsHierarchy Γ n p ∧ IsHierarchy Γ n q := by
  induction n generalizing Γ with
  | zero => exact IsBounded.or_iff;
  | succ n ih =>
    constructor;
    · intro h;
      rcases h.succ_case with (h | h | h | h | h | h);
      · exact ⟨(ih.mp h).1.of_alt, (ih.mp h).2.of_alt⟩;
      all_goals cases Γ <;> simp_all [qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex];
    · rintro ⟨hp, hq⟩;
      exact IsHierarchy.succ_mk <| by disj 3; exact ⟨p, q, hp, hq, rfl⟩;

lemma IsHierarchy.ball {t : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsHierarchy Γ n q) :
    IsHierarchy Γ n (qqBall (termBShift ℒₒᵣ t) q) := by
  cases n with
  | zero => exact IsBounded.ball ht hq;
  | succ n => exact IsHierarchy.succ_mk <| by disj 4; exact ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩;

lemma IsHierarchy.bex {t : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsHierarchy Γ n q) :
    IsHierarchy Γ n (qqBex (termBShift ℒₒᵣ t) q) := by
  cases n with
  | zero => exact IsBounded.bex ht hq;
  | succ n => exact IsHierarchy.succ_mk <| by disj 5; exact ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩;

lemma IsHierarchy.quant (h : IsHierarchy Γ (n + 1) p) : IsHierarchy Γ (n + 1) (qqQuant Γ p) :=
  IsHierarchy.succ_mk <| by disj 6; exact ⟨p, h, rfl⟩

lemma IsSigma.ex (h : IsSigma (n + 1) p) : IsSigma (n + 1) (^∃ p) := IsHierarchy.quant h

lemma IsPi.all (h : IsPi (n + 1) p) : IsPi (n + 1) (^∀ p) := IsHierarchy.quant h

lemma IsSigma.sigma (h : IsPi n p) : IsSigma (n + 1) (^∃ p) :=
  IsSigma.ex (IsHierarchy.of_alt (Γ := 𝚺) h)

lemma IsPi.pi (h : IsSigma n p) : IsPi (n + 1) (^∀ p) :=
  IsPi.all (IsHierarchy.of_alt (Γ := 𝚷) h)

lemma IsHierarchy.succ (h : IsHierarchy Γ n p) : IsHierarchy Γ (n + 1) p := by
  induction n generalizing Γ p with
  | zero => exact IsHierarchy.of_bounded h;
  | succ n ih =>
    apply IsHierarchy.succ_induction 𝚺 (P := IsHierarchy Γ (n + 1 + 1)) (by definability)
      (fun p hp ↦ (ih hp).of_alt) (fun p q _ _ hp hq ↦ IsHierarchy.and_iff.mpr ⟨hp, hq⟩)
      (fun p q _ _ hp hq ↦ IsHierarchy.or_iff.mpr ⟨hp, hq⟩)
      (fun t q ht _ hq ↦ IsHierarchy.ball ht hq) (fun t q ht _ hq ↦ IsHierarchy.bex ht hq)
      (fun q _ hq ↦ IsHierarchy.quant hq) p h;

lemma IsHierarchy.accum (Γ' : Polarity) (h : IsHierarchy Γ n p) : IsHierarchy Γ' (n + 1) p := by
  cases Γ <;> cases Γ';
  · exact h.succ;
  · exact IsHierarchy.of_alt (Γ := 𝚷) h;
  · exact IsHierarchy.of_alt (Γ := 𝚺) h;
  · exact h.succ;

lemma IsHierarchy.mono {m : ℕ} (hmn : m ≤ n) (h : IsHierarchy Γ m p) : IsHierarchy Γ n p := by
  induction hmn with
  | refl => exact h;
  | step _ ih => exact ih.succ;

/-! ### Inversion of unbounded quantifiers -/

lemma IsHierarchy.of_all (h : IsHierarchy Γ (n + 1) (^∀ p)) :
    IsHierarchy Γ.alt n (^∀ p) ∨
    IsHierarchy Γ (n + 1) p ∧
      (Γ = 𝚷 ∨ ∃ t q, IsUTerm ℒₒᵣ t ∧ p = (^#0 ^≮ termBShift ℒₒᵣ t) ^⋎ q) := by
  rcases h.succ_case with (h | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, q, ⟨t, ht, rfl⟩, hq, h⟩
    | ⟨_, _, _, _, h⟩ | ⟨q, hq, h⟩);
  · left; exact h;
  · simp [qqAll, qqAnd] at h;
  · simp [qqAll, qqOr] at h;
  · obtain rfl := (qqAll_inj _ _).mp h;
    right;
    exact ⟨IsHierarchy.or_iff.mpr ⟨by simp [Arithmetic.qqNLT], hq⟩,
      by right; exact ⟨t, q, ht, rfl⟩⟩;
  · simp [qqAll, qqBex, qqExs] at h;
  · cases Γ;
    · simp [qqAll, qqExs] at h;
    · right;
      obtain rfl : p = q := (qqAll_inj _ _).mp h;
      exact ⟨hq, by left; rfl⟩;

lemma IsHierarchy.of_ex (h : IsHierarchy Γ (n + 1) (^∃ p)) :
    IsHierarchy Γ.alt n (^∃ p) ∨
    IsHierarchy Γ (n + 1) p ∧
      (Γ = 𝚺 ∨ ∃ t q, IsUTerm ℒₒᵣ t ∧ p = (^#0 ^< termBShift ℒₒᵣ t) ^⋏ q) := by
  rcases h.succ_case with (h | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
    | ⟨_, q, ⟨t, ht, rfl⟩, hq, h⟩ | ⟨q, hq, h⟩);
  · left; exact h;
  · simp [qqExs, qqAnd] at h;
  · simp [qqExs, qqOr] at h;
  · simp [qqExs, qqBall, qqAll] at h;
  · obtain rfl := (qqExs_inj _ _).mp h;
    right;
    exact ⟨IsHierarchy.and_iff.mpr ⟨by simp [Arithmetic.qqLT], hq⟩,
      by right; exact ⟨t, q, ht, rfl⟩⟩;
  · cases Γ;
    · right;
      obtain rfl : p = q := (qqExs_inj _ _).mp h;
      exact ⟨hq, by left; rfl⟩;
    · simp [qqAll, qqExs] at h;

/-! ### Negation -/

lemma IsHierarchy.neg (hp : IsUFormula ℒₒᵣ p) (h : IsHierarchy Γ n p) :
    IsHierarchy Γ.alt n (neg ℒₒᵣ p) := by
  induction n generalizing Γ p with
  | zero => exact IsBounded.neg hp h;
  | succ n ih =>
    suffices ∀ p : V, IsHierarchy Γ (n + 1) p →
        IsUFormula ℒₒᵣ p → IsHierarchy Γ.alt (n + 1) (neg ℒₒᵣ p) from this p h hp;
    apply IsHierarchy.succ_induction 𝚺
      (P := fun p ↦ IsUFormula ℒₒᵣ p → IsHierarchy Γ.alt (n + 1) (neg ℒₒᵣ p)) (by definability);
    · intro p h hp;
      exact IsHierarchy.of_alt (Γ := Γ.alt) (by simpa using ih hp h);
    · simp +contextual;
    · simp +contextual;
    · intro t q ht _ ih h;
      have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBall];
      simpa [neg_qqBall ht.termBShift hq] using IsHierarchy.bex ht (ih hq);
    · intro t q ht _ ih h;
      have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBex];
      simpa [neg_qqBex ht.termBShift hq] using IsHierarchy.ball ht (ih hq);
    · intro q _ ih h;
      have hq : IsUFormula ℒₒᵣ q := isUFormula_qqQuant.mp h;
      simpa [neg_qqQuant hq] using IsHierarchy.quant (ih hq);

end isHierarchy

/-! ## Strict prenex classes

### Iterated unbounded quantifier of a given polarity -/

section qqQuants

def qqQuants.blueprint (Γ : Polarity) : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !(qqQuantDef Γ) y ih”

noncomputable def qqQuants.construction (Γ : Polarity) :
    PR.Construction V (qqQuants.blueprint Γ) where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ qqQuant Γ ih
  zero_defined := .mk fun v ↦ by simp [qqQuants.blueprint]
  succ_defined := .mk fun v ↦ by simp [qqQuants.blueprint, (qqQuant_defined Γ).df]

noncomputable def qqQuants (Γ : Polarity) (p k : V) : V := (qqQuants.construction Γ).result ![p] k

def _root_.FFL.FirstOrder.Arithmetic.qqQuantsDef (Γ : Polarity) : 𝚺ᴬ₁.Semisentence 3 :=
  (qqQuants.blueprint Γ).resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qqQuants_defined (Γ : Polarity) :
    𝚺ᴬ₁-Function₂ (qqQuants Γ : V → V → V) via qqQuantsDef Γ := .mk
  fun v ↦ by simp [(qqQuants.construction Γ).result_defined_iff, qqQuantsDef]; rfl

instance qqQuants_definable (Γ : Polarity) : 𝚺ᴬ₁-Function₂ (qqQuants Γ : V → V → V) :=
  (qqQuants_defined Γ).to_definable

instance qqQuants_definable' (Γ Γ' : Polarity) {m : ℕ} :
    Γ'ᴬ-[m + 1]-Function₂ (qqQuants Γ : V → V → V) :=
  (qqQuants_definable Γ).of_sigmaOne

variable {Γ : Polarity} {p k : V}

@[simp] lemma qqQuants_zero : qqQuants Γ p 0 = p := by
  simp [qqQuants, qqQuants.construction];

@[simp] lemma qqQuants_succ : qqQuants Γ p (k + 1) = qqQuant Γ (qqQuants Γ p k) := by
  simp [qqQuants, qqQuants.construction];

@[simp] lemma le_qqQuants : p ≤ qqQuants Γ p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih => simpa using ih.trans (lt_qqQuant Γ _).le;

@[simp] lemma index_le_qqQuants : k ≤ qqQuants Γ p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih => simpa [← lt_iff_succ_le] using ih.trans_lt (lt_qqQuant Γ _);

@[simp] lemma isUFormula_qqQuants {L : Language} [L.Encodable] [L.LORDefinable] :
    IsUFormula L (qqQuants Γ p k) ↔ IsUFormula L p := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih => simpa using ih;

lemma neg_qqQuants (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqQuants Γ p k) = qqQuants Γ.alt (neg ℒₒᵣ p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih => simp [neg_qqQuant (isUFormula_qqQuants.mpr hp), ih];

end qqQuants

/-! ### Internal strict prenex classes -/

section isStrictHierarchy

def IsStrictHierarchy : Polarity → ℕ → V → Prop
  | _, 0 => IsBounded
  | Γ, n + 1 => fun p ↦ ∃ k q, p = qqQuants Γ q k ∧ IsStrictHierarchy Γ.alt n q

abbrev IsStrictSigma (n : ℕ) (p : V) : Prop := IsStrictHierarchy 𝚺 n p

abbrev IsStrictPi (n : ℕ) (p : V) : Prop := IsStrictHierarchy 𝚷 n p

noncomputable def isStrictHierarchy : Polarity → ℕ → 𝚫ᴬ₁.Semisentence 1
  | _, 0 => isBounded
  | Γ, n + 1 => .mkDelta
      (.mkSigma “p. ∃ k < p + 1, ∃ q < p + 1, !(qqQuantsDef Γ) p q k ∧
        !(isStrictHierarchy Γ.alt n).sigma q”)
      (.mkPi “p. ∃ k < p + 1, ∃ q < p + 1, (∀ y, !(qqQuantsDef Γ) y q k → y = p) ∧
        !(isStrictHierarchy Γ.alt n).pi q”)

instance IsStrictHierarchy.defined : (Γ : Polarity) → (n : ℕ) →
    𝚫ᴬ₁-Predicate (IsStrictHierarchy (V := V) Γ n) via isStrictHierarchy Γ n
  | _, 0 => IsBounded.defined
  | Γ, n + 1 =>
    have : 𝚫ᴬ₁-Predicate (IsStrictHierarchy (V := V) Γ.alt n) via isStrictHierarchy Γ.alt n :=
      IsStrictHierarchy.defined Γ.alt n
    .mk ⟨fun v ↦ by
        simp [isStrictHierarchy, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm],
      fun v ↦ by
        simp [isStrictHierarchy, IsStrictHierarchy, lt_succ_iff_le];
        grind [le_qqQuants, index_le_qqQuants]⟩

instance IsStrictHierarchy.definable (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsStrictHierarchy (V := V) Γ n) :=
  (IsStrictHierarchy.defined Γ n).to_definable

variable {Γ : Polarity} {n : ℕ} {p : V}

lemma IsStrictHierarchy.of_alt (h : IsStrictHierarchy Γ.alt n p) :
    IsStrictHierarchy Γ (n + 1) p :=
  ⟨0, p, qqQuants_zero.symm, h⟩

lemma IsStrictHierarchy.quant (h : IsStrictHierarchy Γ (n + 1) p) :
    IsStrictHierarchy Γ (n + 1) (qqQuant Γ p) := by
  obtain ⟨k, q, rfl, hq⟩ := h;
  exact ⟨k + 1, q, qqQuants_succ.symm, hq⟩;

lemma IsStrictHierarchy.of_bounded (h : IsBounded p) : IsStrictHierarchy Γ n p := by
  induction n generalizing Γ with
  | zero => exact h;
  | succ n ih => exact IsStrictHierarchy.of_alt ih;

lemma IsStrictHierarchy.succ (h : IsStrictHierarchy Γ n p) : IsStrictHierarchy Γ (n + 1) p := by
  induction n generalizing Γ p with
  | zero => exact IsStrictHierarchy.of_bounded h;
  | succ n ih =>
    obtain ⟨k, q, rfl, hq⟩ := h;
    exact ⟨k, q, rfl, ih hq⟩;

lemma IsStrictHierarchy.mono {m : ℕ} (hmn : m ≤ n) (h : IsStrictHierarchy Γ m p) :
    IsStrictHierarchy Γ n p := by
  induction hmn with
  | refl => exact h;
  | step _ ih => exact ih.succ;

lemma IsStrictHierarchy.of_quant (h : IsStrictHierarchy Γ (n + 1) (qqQuant Γ p)) :
    IsStrictHierarchy Γ (n + 1) p := by
  have H : ∀ {Γ' n} {p : V},
      IsStrictHierarchy Γ' n (qqQuant Γ p) → IsStrictHierarchy Γ (n + 1) p := by
    intro Γ' n;
    induction n generalizing Γ' with
    | zero =>
      intro p h;
      cases Γ;
      · obtain ⟨_, q, ⟨t, -, rfl⟩, hq, rfl⟩ := IsBounded.of_ex h;
        exact IsStrictHierarchy.of_alt <| IsBounded.and_iff.mpr ⟨by simp [Arithmetic.qqLT], hq⟩;
      · obtain ⟨_, q, ⟨t, -, rfl⟩, hq, rfl⟩ := IsBounded.of_all h;
        exact IsStrictHierarchy.of_alt <| IsBounded.or_iff.mpr ⟨by simp [Arithmetic.qqNLT], hq⟩;
    | succ n ih =>
      rintro p ⟨k, q, heq, hq⟩;
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
      · obtain rfl : qqQuant Γ p = q := by simpa using heq;
        exact (ih hq).succ;
      · obtain ⟨rfl, rfl⟩ : Γ = Γ' ∧ p = qqQuants Γ' q k := by simpa using heq;
        exact ⟨k, q, rfl, hq.succ⟩;
  obtain ⟨k, q, heq, hq⟩ := h;
  rcases zero_or_succ k with (rfl | ⟨k, rfl⟩);
  · obtain rfl : qqQuant Γ p = q := by simpa using heq;
    exact H hq;
  · exact ⟨k, q, by simpa using heq, hq⟩;

lemma IsStrictHierarchy.neg (hp : IsUFormula ℒₒᵣ p) (h : IsStrictHierarchy Γ n p) :
    IsStrictHierarchy Γ.alt n (neg ℒₒᵣ p) := by
  induction n generalizing Γ p with
  | zero => exact IsBounded.neg hp h;
  | succ n ih =>
    obtain ⟨k, q, rfl, hq⟩ := h;
    have hq' : IsUFormula ℒₒᵣ q := isUFormula_qqQuants.mp hp;
    exact ⟨k, neg ℒₒᵣ q, neg_qqQuants hq', ih hq' hq⟩;

end isStrictHierarchy

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Arithmetic

/-! ## Agreement on quoted formulas -/

section quote

open Bootstrapping

variable {Γ : Polarity} {s n : ℕ}

/-! ### `IsHierarchy` and `ℬ[<, ℒₒᵣ].Hierarchy` -/

private lemma isHierarchy_of_hierarchy {ψ : ArithmeticSemiproposition n}
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s ψ) : IsHierarchy Γ s (⌜ψ⌝ : ℕ) := by
  induction h with
  | bounded _ _ _ h => exact IsHierarchy.of_bounded ((isBounded_quote_iff_s _).mpr h);
  | and _ _ ihφ ihψ => simpa [Semiformula.quote_and] using ⟨ihφ, ihψ⟩;
  | or _ _ ihφ ihψ => simpa [Semiformula.quote_or] using ⟨ihφ, ihψ⟩;
  | ball hR ht _ ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR;
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
    change IsHierarchy _ _ (⌜(∀¹[“#0 < !!(Rew.bShift t)”] _ : ArithmeticSemiproposition _)⌝ : ℕ);
    rw [quote_ball];
    exact IsHierarchy.ball (by simp [Semiterm.quote_def]) ih;
  | bexs hR ht _ ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR;
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
    change IsHierarchy _ _ (⌜(∃¹[“#0 < !!(Rew.bShift t)”] _ : ArithmeticSemiproposition _)⌝ : ℕ);
    rw [quote_bex];
    exact IsHierarchy.bex (by simp [Semiterm.quote_def]) ih;
  | exs _ ih => simpa [Semiformula.quote_ex] using IsSigma.ex ih;
  | all _ ih => simpa [Semiformula.quote_all] using IsPi.all ih;
  | sigma _ ih => simpa [Semiformula.quote_ex] using IsSigma.sigma ih;
  | pi _ ih => simpa [Semiformula.quote_all] using IsPi.pi ih;
  | dummy_sigma _ ih =>
    simpa [Semiformula.quote_all] using IsHierarchy.of_alt (Γ := 𝚺) (IsPi.all ih);
  | dummy_pi _ ih =>
    simpa [Semiformula.quote_ex] using IsHierarchy.of_alt (Γ := 𝚷) (IsSigma.ex ih);

private lemma hierarchy_of_isHierarchy (ψ : ArithmeticSemiproposition n) :
    IsHierarchy Γ s (⌜ψ⌝ : ℕ) → ℬ[<, ℒₒᵣ].Hierarchy Γ s ψ := by
  induction s generalizing Γ n ψ with
  | zero => exact fun h ↦ .bounded _ _ _ ((isBounded_quote_iff_s ψ).mp h);
  | succ s ihs =>
    induction ψ using Semiformula.rec' with
    | hverum => simp;
    | hfalsum => simp;
    | hrel => simp;
    | hnrel => simp;
    | hand φ ψ ihφ ihψ =>
      intro h;
      rw [Semiformula.quote_and] at h;
      exact (ihφ (IsHierarchy.and_iff.mp h).1).and (ihψ (IsHierarchy.and_iff.mp h).2);
    | hor φ ψ ihφ ihψ =>
      intro h;
      rw [Semiformula.quote_or] at h;
      exact (ihφ (IsHierarchy.or_iff.mp h).1).or (ihψ (IsHierarchy.or_iff.mp h).2);
    | hall φ ih =>
      intro h;
      rw [Semiformula.quote_all] at h;
      rcases IsHierarchy.of_all h with (h | ⟨hφ, rfl | ⟨t, q, ht, e⟩⟩);
      · exact (ihs (∀¹ φ) (by rwa [Semiformula.quote_all])).accum Γ;
      · exact (ih hφ).all;
      · obtain ⟨u, χ, rfl⟩ := exists_ball_of_quote_eq ht e;
        exact Bounding.Hierarchy.arithmetic_ball (Rew.positive_iff.mpr ⟨u, rfl⟩)
          (Bounding.Hierarchy.imp_iff.mp (ih hφ)).2;
    | hexs φ ih =>
      intro h;
      rw [Semiformula.quote_ex] at h;
      rcases IsHierarchy.of_ex h with (h | ⟨hφ, rfl | ⟨t, q, ht, e⟩⟩);
      · exact (ihs (∃¹ φ) (by rwa [Semiformula.quote_ex])).accum Γ;
      · exact (ih hφ).exs;
      · obtain ⟨u, χ, rfl⟩ := exists_bex_of_quote_eq ht e;
        exact Bounding.Hierarchy.arithmetic_bexs (Rew.positive_iff.mpr ⟨u, rfl⟩)
          (Bounding.Hierarchy.and_iff.mp (ih hφ)).2;

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma isHierarchy_quote_iff_s (ψ : ArithmeticSemiproposition n) :
    IsHierarchy Γ s (⌜ψ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy Γ s ψ := by
  simpa [Semiformula.coe_quote_eq_quote] using
    (Defined.shigmaOne_absolute V (IsHierarchy.defined Γ s)
      (IsHierarchy.defined Γ s) ![⌜ψ⌝]).symm.trans
      ⟨hierarchy_of_isHierarchy ψ, isHierarchy_of_hierarchy⟩;

theorem isHierarchy_quote_iff (σ : ArithmeticSemisentence n) :
    IsHierarchy Γ s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy Γ s σ := by
  simp [Sentence.quote_def, isHierarchy_quote_iff_s];

theorem isSigma_quote_iff (σ : ArithmeticSemisentence n) :
    IsSigma s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s σ := isHierarchy_quote_iff σ

theorem isPi_quote_iff (σ : ArithmeticSemisentence n) :
    IsPi s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy 𝚷 s σ := isHierarchy_quote_iff σ

/-! ### `IsStrictHierarchy` and `StrictHierarchy` -/

private lemma isStrictHierarchy_of_strictHierarchy {ψ : ArithmeticSemiproposition n}
    (h : StrictHierarchy Γ s ψ) : IsStrictHierarchy Γ s (⌜ψ⌝ : V) := by
  induction h with
  | zero hφ => exact (isBounded_quote_iff_s _).mpr hφ;
  | ofAlt _ ih => exact ih.of_alt;
  | exs _ ih => simpa [Semiformula.quote_ex] using IsStrictHierarchy.quant (Γ := 𝚺) ih;
  | all _ ih => simpa [Semiformula.quote_all] using IsStrictHierarchy.quant (Γ := 𝚷) ih;

private lemma strictHierarchy_of_isStrictHierarchy (ψ : ArithmeticSemiproposition n) :
    IsStrictHierarchy Γ s (⌜ψ⌝ : ℕ) → StrictHierarchy Γ s ψ := by
  induction s generalizing Γ n ψ with
  | zero => exact fun h ↦ .zero ((isBounded_quote_iff_s ψ).mp h);
  | succ s ihs =>
    rintro ⟨k, q, heq, hq⟩;
    induction k generalizing n ψ with
    | zero => exact .ofAlt <| ihs ψ <| by simpa [heq] using hq;
    | succ k ih =>
      cases Γ;
      · induction ψ using Semiformula.rec' with
        | hexs φ _ => exact .exs <| ih φ <| by simpa using heq;
        | _ => simp [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs] at heq;
      · induction ψ using Semiformula.rec' with
        | hall φ _ => exact .all <| ih φ <| by simpa using heq;
        | _ => simp [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs] at heq;

lemma isStrictHierarchy_quote_iff_s (ψ : ArithmeticSemiproposition n) :
    IsStrictHierarchy Γ s (⌜ψ⌝ : V) ↔ StrictHierarchy Γ s ψ := by
  simpa [Semiformula.coe_quote_eq_quote] using
    (Defined.shigmaOne_absolute V (IsStrictHierarchy.defined Γ s)
      (IsStrictHierarchy.defined Γ s) ![⌜ψ⌝]).symm.trans
      ⟨strictHierarchy_of_isStrictHierarchy ψ, isStrictHierarchy_of_strictHierarchy⟩;

theorem isStrictHierarchy_quote_iff (σ : ArithmeticSemisentence n) :
    IsStrictHierarchy Γ s (⌜σ⌝ : V) ↔ StrictHierarchy Γ s σ := by
  simp [Sentence.quote_def, isStrictHierarchy_quote_iff_s];

theorem isStrictSigma_quote_iff (σ : ArithmeticSemisentence n) :
    IsStrictSigma s (⌜σ⌝ : V) ↔ StrictHierarchy 𝚺 s σ := isStrictHierarchy_quote_iff σ

theorem isStrictPi_quote_iff (σ : ArithmeticSemisentence n) :
    IsStrictPi s (⌜σ⌝ : V) ↔ StrictHierarchy 𝚷 s σ := isStrictHierarchy_quote_iff σ

end quote

end FFL.FirstOrder.Arithmetic
