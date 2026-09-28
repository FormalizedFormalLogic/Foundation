module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Bounded

/-!
# Internal arithmetical hierarchy

The internal predicates `IsSigma n` and `IsPi n` on codes of formulas of the (non-strict) bounded
arithmetical hierarchy: they are `𝚫ᴬ₁`-definable and agree with `ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n` and
`ℬ[<, ℒₒᵣ].Hierarchy 𝚷 n` on quoted formulas. In particular `IsSigma 0` is `IsBounded` and
`IsSigma 1` is `IsSigma1`.

## References

- [HP98]
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
        (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBall_defined (V := V)).df,
        (qqBex_defined (V := V)).df, (qqQuant_defined (V := V) Γ).df];
    · intro v;
      symm;
      simpa [blueprint, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBall_defined (V := V)).df,
        (qqBex_defined (V := V)).df, (qqQuant_defined (V := V) Γ).df]
        using phi_iff (V := V) Γ P _ _;
  monotone := by
    unfold Phi;
    rintro C C' hC _ x (h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨u, q, ht, hq, rfl⟩
      | ⟨u, q, ht, hq, rfl⟩ | ⟨q, hq, rfl⟩) <;> grind;

instance (Γ : Polarity) {P : V → Prop} {θ : 𝚫ᴬ₁.Semisentence 1}
    (hP : 𝚫ᴬ₁-Predicate P via θ) : (construction Γ hP).StrongFinite V where
  strong_finite := by
    unfold construction Phi;
    rintro C _ x (h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨u, q, ht, hq, rfl⟩
      | ⟨u, q, ht, hq, rfl⟩ | ⟨q, hq, rfl⟩);
    · disj 1; exact h;
    · disj 2; exact ⟨p₁, p₂, ⟨hp, by simp⟩, ⟨hq, by simp⟩, rfl⟩;
    · disj 3; exact ⟨p₁, p₂, ⟨hp, by simp⟩, ⟨hq, by simp⟩, rfl⟩;
    · disj 4; exact ⟨u, q, ht, ⟨hq, by simp⟩, rfl⟩;
    · disj 5; exact ⟨u, q, ht, ⟨hq, by simp⟩, rfl⟩;
    · disj 6; exact ⟨q, ⟨hq, by simp⟩, rfl⟩;

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
  · right;
    rw [qqBall, qqAll_inj] at h;
    subst h;
    constructor;
    · exact IsHierarchy.or_iff.mpr ⟨by simp [Arithmetic.qqNLT], hq⟩;
    · right; exact ⟨t, q, ht, rfl⟩;
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
  · right;
    rw [qqBex, qqExs_inj] at h;
    subst h;
    constructor;
    · exact IsHierarchy.and_iff.mpr ⟨by simp [Arithmetic.qqLT], hq⟩;
    · right; exact ⟨t, q, ht, rfl⟩;
  · cases Γ;
    · right;
      obtain rfl : p = q := (qqExs_inj _ _).mp h;
      exact ⟨hq, by left; rfl⟩;
    · simp [qqAll, qqExs] at h;

/-! ### Negation -/

lemma neg_qqQuant (Γ : Polarity) (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqQuant Γ p) = qqQuant Γ.alt (neg ℒₒᵣ p) := by
  cases Γ;
  · exact neg_ex hp;
  · exact neg_all hp;

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
      rw [neg_qqQuant Γ hq];
      exact IsHierarchy.quant (ih hq);

/-! ### Comparison with `IsSigma1` -/

theorem isSigma_one_iff_isSigma1 : IsSigma 1 p ↔ IsSigma1 p := by
  have : 𝚫ᴬ₁-Predicate (IsSigma1 : V → Prop) := IsSigma1.defined.to_definable;
  constructor;
  · revert p;
    apply IsHierarchy.succ_induction 𝚺 (P := IsSigma1) (by definability);
    · intro p h;
      exact IsBounded.isSigma1 h;
    · intro p q _ _ hp hq;
      exact IsSigma1.and_iff.mpr ⟨hp, hq⟩;
    · intro p q _ _ hp hq;
      exact IsSigma1.or_iff.mpr ⟨hp, hq⟩;
    · intro t q ht _ hq;
      exact IsSigma1.mk <| by disj 8; exact ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩;
    · intro t q _ _ hq;
      simp [qqBex, Arithmetic.qqLT, hq];
    · intro q _ hq;
      exact IsSigma1.ex_iff.mpr hq;
  · revert p;
    apply IsSigma1F.construction.induction (v := ![]) (Γ := 𝚺) (P := IsSigma 1) (by definability);
    rintro C hC x (rfl | rfl | ⟨k, r, v, rfl⟩ | ⟨k, r, v, rfl⟩ | ⟨p, q, hp, hq, rfl⟩
      | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩);
    · exact IsHierarchy.verum;
    · exact IsHierarchy.falsum;
    · exact IsHierarchy.rel;
    · exact IsHierarchy.nrel;
    · exact IsHierarchy.and_iff.mpr ⟨(hC p hp).2, (hC q hq).2⟩;
    · exact IsHierarchy.or_iff.mpr ⟨(hC p hp).2, (hC q hq).2⟩;
    · exact IsSigma.ex (hC p hp).2;
    · exact IsHierarchy.ball ht (hC q hq).2;

end isHierarchy

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Arithmetic

/-! ## Agreement with `ℬ[<, ℒₒᵣ].Hierarchy` on quoted formulas -/

section quote

open Bootstrapping

lemma exists_ball_of_quote_eq {n : ℕ} {φ : ArithmeticSemiproposition (n + 1)} {t q : ℕ}
    (ht : IsUTerm ℒₒᵣ t) (h : (⌜φ⌝ : ℕ) = (^#0 ^≮ termBShift ℒₒᵣ t) ^⋎ q) :
    ∃ (s : SyntacticSemiterm ℒₒᵣ n) (ψ : ArithmeticSemiproposition (n + 1)),
      φ = “#0 < !!(Rew.bShift s)” 🡒 ψ := by
  have hsf : IsSemiformula ℒₒᵣ (n + 1) ((^#0 ^≮ termBShift ℒₒᵣ t) ^⋎ q) := by
    simpa [h] using Semiformula.quote_isSemiformula (V := ℕ) φ;
  obtain ⟨h₁, hq⟩ := IsSemiformula.or.mp hsf;
  obtain ⟨ψ, rfl⟩ := IsSemiformula.sound hq;
  have ht' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) := by
    simpa using (IsSemiformula.nrel.mp h₁).2.nth (i := 1) (by simp);
  obtain ⟨s, rfl⟩ := IsSemiterm.sound <| IsSemiterm.def.mpr
    ⟨ht, (termBV_termBShift_le ht _).mp (IsSemiterm.def.mp ht').2⟩;
  have e : (∀¹ φ) = ∀¹[“#0 < !!(Rew.bShift s)”] ψ := by
    apply Semiformula.quote_inj_iff (V := ℕ) |>.mp;
    rw [Semiformula.quote_all, h, quote_ball];
    rfl;
  exact ⟨s, ψ, (Semiformula.all_inj _ _).mp e⟩;

lemma exists_bex_of_quote_eq {n : ℕ} {φ : ArithmeticSemiproposition (n + 1)} {t q : ℕ}
    (ht : IsUTerm ℒₒᵣ t) (h : (⌜φ⌝ : ℕ) = (^#0 ^< termBShift ℒₒᵣ t) ^⋏ q) :
    ∃ (s : SyntacticSemiterm ℒₒᵣ n) (ψ : ArithmeticSemiproposition (n + 1)),
      φ = “#0 < !!(Rew.bShift s)” ⋏ ψ := by
  have hsf : IsSemiformula ℒₒᵣ (n + 1) ((^#0 ^< termBShift ℒₒᵣ t) ^⋏ q) := by
    simpa [h] using Semiformula.quote_isSemiformula (V := ℕ) φ;
  obtain ⟨h₁, hq⟩ := IsSemiformula.and.mp hsf;
  obtain ⟨ψ, rfl⟩ := IsSemiformula.sound hq;
  have ht' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) := by
    simpa using (IsSemiformula.rel.mp h₁).2.nth (i := 1) (by simp);
  obtain ⟨s, rfl⟩ := IsSemiterm.sound <| IsSemiterm.def.mpr
    ⟨ht, (termBV_termBShift_le ht _).mp (IsSemiterm.def.mp ht').2⟩;
  have e : (∃¹ φ) = ∃¹[“#0 < !!(Rew.bShift s)”] ψ := by
    apply Semiformula.quote_inj_iff (V := ℕ) |>.mp;
    rw [Semiformula.quote_ex, h, quote_bex];
    rfl;
  exact ⟨s, ψ, (Semiformula.exs_inj _ _).mp e⟩;

variable {Γ : Polarity} {s n : ℕ}

lemma isHierarchy_of_hierarchy {ψ : ArithmeticSemiproposition n}
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

lemma hierarchy_of_isHierarchy (ψ : ArithmeticSemiproposition n) :
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
      rw [Semiformula.quote_and, IsHierarchy.and_iff] at h;
      exact (ihφ h.1).and (ihψ h.2);
    | hor φ ψ ihφ ihψ =>
      intro h;
      rw [Semiformula.quote_or, IsHierarchy.or_iff] at h;
      exact (ihφ h.1).or (ihψ h.2);
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
  sorry

theorem isHierarchy_quote_iff (σ : ArithmeticSemisentence n) :
    IsHierarchy Γ s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy Γ s σ := by
  sorry

theorem isSigma_quote_iff (σ : ArithmeticSemisentence n) :
    IsSigma s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s σ := isHierarchy_quote_iff σ

theorem isPi_quote_iff (σ : ArithmeticSemisentence n) :
    IsPi s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Hierarchy 𝚷 s σ := isHierarchy_quote_iff σ

end quote

end FFL.FirstOrder.Arithmetic
