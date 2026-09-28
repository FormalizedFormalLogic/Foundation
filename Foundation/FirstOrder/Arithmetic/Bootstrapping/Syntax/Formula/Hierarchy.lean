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

lemma IsHierarchy.zero_iff : IsHierarchy Γ 0 p ↔ IsBounded p := by
  sorry

lemma IsHierarchy.succ_iff :
    IsHierarchy Γ (n + 1) p ↔
    IsHierarchy Γ.alt n p ∨
    (∃ p₁ p₂, IsHierarchy Γ (n + 1) p₁ ∧ IsHierarchy Γ (n + 1) p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsHierarchy Γ (n + 1) p₁ ∧ IsHierarchy Γ (n + 1) p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsHierarchy Γ (n + 1) q
      ∧ p = qqBall u q) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsHierarchy Γ (n + 1) q
      ∧ p = qqBex u q) ∨
    (∃ q, IsHierarchy Γ (n + 1) q ∧ p = qqQuant Γ q) := by
  sorry

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
    ∀ p, IsHierarchy Γ (n + 1) p → P p := by
  sorry

/-! ### Closure properties -/

lemma IsHierarchy.of_alt (h : IsHierarchy Γ.alt n p) : IsHierarchy Γ (n + 1) p := by
  sorry

lemma IsHierarchy.of_bounded (h : IsBounded p) : IsHierarchy Γ n p := by
  sorry

@[simp] lemma IsHierarchy.verum : IsHierarchy Γ n (^⊤ : V) := by
  sorry

@[simp] lemma IsHierarchy.falsum : IsHierarchy Γ n (^⊥ : V) := by
  sorry

@[simp] lemma IsHierarchy.rel {k r v : V} : IsHierarchy Γ n (^rel k r v) := by
  sorry

@[simp] lemma IsHierarchy.nrel {k r v : V} : IsHierarchy Γ n (^nrel k r v) := by
  sorry

@[simp] lemma IsHierarchy.and_iff :
    IsHierarchy Γ n (p ^⋏ q) ↔ IsHierarchy Γ n p ∧ IsHierarchy Γ n q := by
  sorry

@[simp] lemma IsHierarchy.or_iff :
    IsHierarchy Γ n (p ^⋎ q) ↔ IsHierarchy Γ n p ∧ IsHierarchy Γ n q := by
  sorry

lemma IsHierarchy.ball {t : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsHierarchy Γ n q) :
    IsHierarchy Γ n (qqBall (termBShift ℒₒᵣ t) q) := by
  sorry

lemma IsHierarchy.bex {t : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsHierarchy Γ n q) :
    IsHierarchy Γ n (qqBex (termBShift ℒₒᵣ t) q) := by
  sorry

lemma IsHierarchy.quant (h : IsHierarchy Γ (n + 1) p) : IsHierarchy Γ (n + 1) (qqQuant Γ p) := by
  sorry

lemma IsSigma.ex (h : IsSigma (n + 1) p) : IsSigma (n + 1) (^∃ p) := by
  sorry

lemma IsPi.all (h : IsPi (n + 1) p) : IsPi (n + 1) (^∀ p) := by
  sorry

lemma IsSigma.sigma (h : IsPi n p) : IsSigma (n + 1) (^∃ p) := by
  sorry

lemma IsPi.pi (h : IsSigma n p) : IsPi (n + 1) (^∀ p) := by
  sorry

lemma IsHierarchy.succ (h : IsHierarchy Γ n p) : IsHierarchy Γ (n + 1) p := by
  sorry

lemma IsHierarchy.accum (Γ' : Polarity) (h : IsHierarchy Γ n p) : IsHierarchy Γ' (n + 1) p := by
  sorry

lemma IsHierarchy.mono {m : ℕ} (hmn : m ≤ n) (h : IsHierarchy Γ m p) : IsHierarchy Γ n p := by
  sorry

/-! ### Inversion of unbounded quantifiers -/

lemma IsHierarchy.of_all (h : IsHierarchy Γ (n + 1) (^∀ p)) :
    IsHierarchy Γ.alt n (^∀ p) ∨
    IsHierarchy Γ (n + 1) p ∧
      (Γ = 𝚷 ∨ ∃ t q, IsUTerm ℒₒᵣ t ∧ p = (^#0 ^≮ termBShift ℒₒᵣ t) ^⋎ q) := by
  sorry

lemma IsHierarchy.of_ex (h : IsHierarchy Γ (n + 1) (^∃ p)) :
    IsHierarchy Γ.alt n (^∃ p) ∨
    IsHierarchy Γ (n + 1) p ∧
      (Γ = 𝚺 ∨ ∃ t q, IsUTerm ℒₒᵣ t ∧ p = (^#0 ^< termBShift ℒₒᵣ t) ^⋏ q) := by
  sorry

/-! ### Negation -/

lemma neg_qqQuant (Γ : Polarity) (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqQuant Γ p) = qqQuant Γ.alt (neg ℒₒᵣ p) := by
  sorry

lemma IsHierarchy.neg (hp : IsUFormula ℒₒᵣ p) (h : IsHierarchy Γ n p) :
    IsHierarchy Γ.alt n (neg ℒₒᵣ p) := by
  sorry

/-! ### Comparison with `IsSigma1` -/

theorem isSigma_one_iff_isSigma1 : IsSigma 1 p ↔ IsSigma1 p := by
  sorry

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
  sorry

lemma exists_bex_of_quote_eq {n : ℕ} {φ : ArithmeticSemiproposition (n + 1)} {t q : ℕ}
    (ht : IsUTerm ℒₒᵣ t) (h : (⌜φ⌝ : ℕ) = (^#0 ^< termBShift ℒₒᵣ t) ^⋏ q) :
    ∃ (s : SyntacticSemiterm ℒₒᵣ n) (ψ : ArithmeticSemiproposition (n + 1)),
      φ = “#0 < !!(Rew.bShift s)” ⋏ ψ := by
  sorry

variable {Γ : Polarity} {s n : ℕ}

lemma isHierarchy_of_hierarchy {ψ : ArithmeticSemiproposition n}
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s ψ) : IsHierarchy Γ s (⌜ψ⌝ : ℕ) := by
  sorry

lemma hierarchy_of_isHierarchy (ψ : ArithmeticSemiproposition n) :
    IsHierarchy Γ s (⌜ψ⌝ : ℕ) → ℬ[<, ℒₒᵣ].Hierarchy Γ s ψ := by
  sorry

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
