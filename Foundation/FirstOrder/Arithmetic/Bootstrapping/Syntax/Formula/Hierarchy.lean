module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Bounded

/-!
# Internal arithmetical hierarchy

The internal predicates `IsSigma n` and `IsPi n` on codes of formulas of the (non-strict) bounded
arithmetical hierarchy, and `IsStrictSigma n` and `IsStrictPi n` on codes of strict prenex
formulas: they are `𝚫ᴬ₁`-definable and agree with `ℬ[<, ℒₒᵣ].Hierarchy` and `StrictHierarchy`
on quoted formulas. In particular `IsSigma 0` is `IsBounded`.

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
      have hq : IsUFormula ℒₒᵣ q := by cases Γ <;> simpa using h;
      cases Γ;
      · simpa [neg_ex hq] using IsHierarchy.quant (ih hq);
      · simpa [neg_all hq] using IsHierarchy.quant (ih hq);

end isHierarchy

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Arithmetic

/-! ## Agreement with `ℬ[<, ℒₒᵣ].Hierarchy` on quoted formulas -/

section quote

open Bootstrapping

variable {Γ : Polarity} {s n : ℕ}

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
  | zero =>
    intro h;
    exact .bounded _ _ _ ((isBounded_quote_iff_s ψ).mp h);
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
  have h : IsHierarchy Γ s (⌜ψ⌝ : V) ↔ IsHierarchy Γ s (⌜ψ⌝ : ℕ) := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton,
      (IsHierarchy.defined (V := V) Γ s).df, (IsHierarchy.defined (V := ℕ) Γ s).df]
      using models_iff_of_Delta1 (V := V) (IsHierarchy.defined Γ s).proper
        (IsHierarchy.defined Γ s).proper (e := ![⌜ψ⌝]);
  exact h.trans ⟨hierarchy_of_isHierarchy ψ, isHierarchy_of_hierarchy⟩;

theorem isHierarchy_quote_iff (σ : ArithmeticSemisentence n) :
    IsHierarchy Γ s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy Γ s σ := by
  simp [Sentence.quote_def, isHierarchy_quote_iff_s];

theorem isSigma_quote_iff (σ : ArithmeticSemisentence n) :
    IsSigma s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s σ := isHierarchy_quote_iff σ

theorem isPi_quote_iff (σ : ArithmeticSemisentence n) :
    IsPi s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy 𝚷 s σ := isHierarchy_quote_iff σ

end quote

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Strict prenex classes

### Iterated existential quantification -/

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

@[simp] lemma le_qqExss (p k : V) : p ≤ qqExss p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih =>
    rw [qqExss_succ];
    exact ih.trans (lt_exists _).le;

@[simp] lemma index_le_qqExss (p k : V) : k ≤ qqExss p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih =>
    rw [qqExss_succ];
    exact (add_le_add_left ih 1).trans (add_le_add_left (le_pair_right _ _) 1);

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

/-! ### Internal strict prenex classes -/

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

/-! ### Agreement with `StrictHierarchy` on quoted formulas -/

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
