module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Bounded

/-!
# Internal arithmetical hierarchy

The internal predicates `IsHierarchy Γ n` and `IsPrenexHierarchy Γ n` on codes of formulas: they
are `𝚫ᴬ₁`-definable and agree with `ℬ[<, ℒₒᵣ].Hierarchy` and `ℬ[<, ℒₒᵣ].PrenexHierarchy` on
quoted formulas.

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

section qqToPrenex

noncomputable def qqToPrenex : Polarity → ℕ → V → V
  | _, 0, θ => θ
  | Γ, s + 1, θ => qqQuant Γ (qqToPrenex Γ.alt s θ)

def _root_.FFL.FirstOrder.Arithmetic.qqToPrenexDef : Polarity → ℕ → 𝚺ᴬ₀.Semisentence 2
  | _, 0 => .mkSigma “y θ. y = θ”
  | Γ, s + 1 => .mkSigma “y θ. ∃ z < y, !(qqQuantDef Γ) y z ∧ !(qqToPrenexDef Γ.alt s) z θ”

variable {Γ : Polarity} {s : ℕ} {θ θ' : V}

@[simp] lemma qqToPrenex_zero : qqToPrenex Γ 0 θ = θ := rfl

@[simp] lemma qqToPrenex_succ : qqToPrenex Γ (s + 1) θ = qqQuant Γ (qqToPrenex Γ.alt s θ) := rfl

@[simp] lemma qqToPrenex_inj : qqToPrenex Γ s θ = qqToPrenex Γ s θ' ↔ θ = θ' := by
  induction s generalizing Γ <;> simp [*];

@[simp] lemma le_qqToPrenex : θ ≤ qqToPrenex Γ s θ := by
  induction s generalizing Γ with
  | zero => simp;
  | succ s ih => exact ih.trans (lt_qqQuant _ _).le;

instance qqToPrenex_defined : (Γ : Polarity) → (s : ℕ) →
    𝚺ᴬ₀-Function₁ (qqToPrenex Γ s : V → V) via qqToPrenexDef Γ s
  | _, 0 => .mk fun v ↦ by simp [qqToPrenexDef]
  | Γ, s + 1 => .mk fun v ↦ by
    simp +contextual [qqToPrenexDef, (qqToPrenex_defined Γ.alt s).df, (qqQuant_defined Γ).df]

end qqToPrenex

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

lemma IsHierarchy.succ_induction (Γ' : Polarity) {P : V → Prop} (hP : Γ'ᴬ_[1]-Predicate P)
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

/-! ## Internal prenex classes -/

section isPrenexHierarchy

def IsPrenexHierarchy : Polarity → ℕ → V → Prop
  | _, 0 => IsBounded
  | Γ, n + 1 => fun p ↦ ∃ q, p = qqQuant Γ q ∧ IsPrenexHierarchy Γ.alt n q

noncomputable def isPrenexHierarchy : Polarity → ℕ → 𝚫ᴬ₁.Semisentence 1
  | _, 0 => isBounded
  | Γ, n + 1 => .mkDelta
      (.mkSigma “p. ∃ q < p, !(qqQuantDef Γ) p q ∧ !(isPrenexHierarchy Γ.alt n).sigma q”)
      (.mkPi “p. ∃ q < p, !(qqQuantDef Γ) p q ∧ !(isPrenexHierarchy Γ.alt n).pi q”)

instance IsPrenexHierarchy.defined : (Γ : Polarity) → (n : ℕ) →
    𝚫ᴬ₁-Predicate (IsPrenexHierarchy (V := V) Γ n) via isPrenexHierarchy Γ n
  | _, 0 => IsBounded.defined
  | Γ, n + 1 =>
    have : 𝚫ᴬ₁-Predicate (IsPrenexHierarchy (V := V) Γ.alt n) via isPrenexHierarchy Γ.alt n :=
      IsPrenexHierarchy.defined Γ.alt n
    .mk ⟨fun v ↦ by
        simp [isPrenexHierarchy, Bounding.HierarchySymbol.Semiformula.val_sigma],
      fun v ↦ by
        simp [isPrenexHierarchy, IsPrenexHierarchy, (qqQuant_defined Γ).df];
        grind [lt_qqQuant]⟩

instance IsPrenexHierarchy.definable (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsPrenexHierarchy (V := V) Γ n) :=
  (IsPrenexHierarchy.defined Γ n).to_definable

variable {Γ : Polarity} {n : ℕ} {p : V}

@[simp] lemma IsPrenexHierarchy.quant_iff :
    IsPrenexHierarchy Γ (n + 1) (qqQuant Γ p) ↔ IsPrenexHierarchy Γ.alt n p := by
  simp [IsPrenexHierarchy];

lemma isPrenexHierarchy_iff_exists_qqToPrenex :
    IsPrenexHierarchy Γ n p ↔ ∃ θ, p = qqToPrenex Γ n θ ∧ IsBounded θ := by
  induction n generalizing Γ p <;> simp [IsPrenexHierarchy, *];

lemma IsPrenexHierarchy.neg (hp : IsUFormula ℒₒᵣ p) (h : IsPrenexHierarchy Γ n p) :
    IsPrenexHierarchy Γ.alt n (neg ℒₒᵣ p) := by
  induction n generalizing Γ p with
  | zero => exact IsBounded.neg hp h;
  | succ n ih =>
    obtain ⟨q, rfl, hq⟩ := h;
    have hq' : IsUFormula ℒₒᵣ q := isUFormula_qqQuant.mp hp;
    exact ⟨neg ℒₒᵣ q, neg_qqQuant hq', ih hq' hq⟩;

end isPrenexHierarchy

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
  | initial _ _ _ h => exact IsHierarchy.of_bounded ((isBounded_quote_iff_s _).mpr h);
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
          (Bounding.HierarchyOn.imp_iff.mp (ih hφ)).2;
    | hexs φ ih =>
      intro h;
      rw [Semiformula.quote_ex] at h;
      rcases IsHierarchy.of_ex h with (h | ⟨hφ, rfl | ⟨t, q, ht, e⟩⟩);
      · exact (ihs (∃¹ φ) (by rwa [Semiformula.quote_ex])).accum Γ;
      · exact (ih hφ).exs;
      · obtain ⟨u, χ, rfl⟩ := exists_bex_of_quote_eq ht e;
        exact Bounding.Hierarchy.arithmetic_bexs (Rew.positive_iff.mpr ⟨u, rfl⟩)
          (Bounding.HierarchyOn.and_iff.mp (ih hφ)).2;

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

/-! ### `IsPrenexHierarchy` and `ℬ[<, ℒₒᵣ].PrenexHierarchy` -/

lemma isPrenexHierarchy_quote_iff_s (ψ : ArithmeticSemiproposition n) :
    IsPrenexHierarchy Γ s (⌜ψ⌝ : V) ↔ ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s ψ := by
  induction s generalizing Γ n with
  | zero => exact (isBounded_quote_iff_s ψ).trans Bounding.PrenexHierarchy.zero_iff_bounded.symm;
  | succ s ih =>
    cases Γ;
    · constructor;
      · rintro ⟨q, heq, hq⟩;
        cases ψ using Semiformula.cases' with
        | hexs φ =>
          obtain rfl : ⌜φ⌝ = q := by simpa [Semiformula.quote_ex] using heq;
          exact ((ih φ).mp hq).exs;
        | _ => simp [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs] at heq;
      · intro h;
        obtain ⟨φ, hφ, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp h;
        exact ⟨⌜φ⌝, by simp [Semiformula.quote_ex], (ih φ).mpr hφ⟩;
    · constructor;
      · rintro ⟨q, heq, hq⟩;
        cases ψ using Semiformula.cases' with
        | hall φ =>
          obtain rfl : ⌜φ⌝ = q := by simpa [Semiformula.quote_all] using heq;
          exact ((ih φ).mp hq).all;
        | _ => simp [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs] at heq;
      · intro h;
        obtain ⟨φ, hφ, rfl⟩ := Bounding.PrenexHierarchy.pi_succ_iff.mp h;
        exact ⟨⌜φ⌝, by simp [Semiformula.quote_all], (ih φ).mpr hφ⟩;

theorem isPrenexHierarchy_quote_iff (σ : ArithmeticSemisentence n) :
    IsPrenexHierarchy Γ s (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s σ := by
  simp [Sentence.quote_def, isPrenexHierarchy_quote_iff_s];

end quote

end FFL.FirstOrder.Arithmetic
