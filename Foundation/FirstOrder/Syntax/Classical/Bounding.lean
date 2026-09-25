module

public import Foundation.FirstOrder.Syntax.Classical.Operator
public import Foundation.FirstOrder.Syntax.Classical.BinderNotation

/-!
Bounded formulas with bounds supplied by a set of operators; this set-parametric presentation
and its rewriting lemmas are specific to this formalization.
-/

@[expose] public section

namespace FFL.FirstOrder

structure Bounding (L : Language) where
  set : Set (Semiformula.Operator L 2)

namespace Bounding

def strict (L : Language) : Bounding L := ⟨∅⟩

def lt (L : Language) [L.LT] : Bounding L :=
  ⟨{Semiformula.Operator.LT.lt}⟩

def mem (L : Language) [L.Mem] : Bounding L :=
  ⟨{Semiformula.Operator.Mem.mem}⟩

notation "ℬ[" L "]" => strict L
notation "ℬ[<, " L "]" => lt L
notation "ℬ[∈, " L "]" => mem L

variable {L : Language}

instance : SetLike (Bounding L) (Semiformula.Operator L 2) where
  coe ℬ := ℬ.set
  coe_injective := by rintro ⟨s⟩ ⟨t⟩; simp

open Semiformula

variable {ξ ξ₁ ξ₂ : Type*} {n : ℕ} (ℬ : Bounding L)

class SymbolLike (ξ₁ ξ₂ : Type*) : Prop where
  symbolLike {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) : R.SymbolLike ξ₁ ξ₂

instance lt.symbolLike [L.LT] : ℬ[<, L].SymbolLike ξ₁ ξ₂ where
  symbolLike hR := by
    simpa only [Bounding.lt, Set.mem_singleton_iff] using hR ▸ inferInstance

instance mem.symbolLike [L.Mem] : ℬ[∈, L].SymbolLike ξ₁ ξ₂ where
  symbolLike hR := by
    simpa only [Bounding.mem, Set.mem_singleton_iff] using hR ▸ inferInstance

inductive Closure (ℬ : Bounding L) : {n : ℕ} → Semiformula L ξ n → Prop
  | verum (n : ℕ) : ℬ.Closure (⊤ : Semiformula L ξ n)
  | falsum (n : ℕ) : ℬ.Closure (⊥ : Semiformula L ξ n)
  | rel {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ℬ.Closure (.rel r v)
  | nrel {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ℬ.Closure (.nrel r v)
  | and {n : ℕ} {φ ψ : Semiformula L ξ n} : ℬ.Closure φ → ℬ.Closure ψ → ℬ.Closure (φ ⋏ ψ)
  | or {n : ℕ} {φ ψ : Semiformula L ξ n} : ℬ.Closure φ → ℬ.Closure ψ → ℬ.Closure (φ ⋎ ψ)
  | ball {n : ℕ} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    R ∈ ℬ → t.Positive → ℬ.Closure φ → ℬ.Closure (∀¹[R.operator ![#0, t]] φ)
  | bexs {n : ℕ} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    R ∈ ℬ → t.Positive → ℬ.Closure φ → ℬ.Closure (∃¹[R.operator ![#0, t]] φ)

variable {ℬ}

namespace Closure

attribute [simp] verum falsum rel nrel

variable {R : Semiformula.Operator L 2} {n n₁ n₂ : ℕ}

@[simp] lemma and_iff {φ ψ : Semiformula L ξ n} :
    ℬ.Closure (φ ⋏ ψ) ↔ ℬ.Closure φ ∧ ℬ.Closure ψ :=
  ⟨fun | .and hp hq => ⟨hp, hq⟩, fun ⟨hp, hq⟩ => .and hp hq⟩

@[simp] lemma or_iff {φ ψ : Semiformula L ξ n} :
    ℬ.Closure (φ ⋎ ψ) ↔ ℬ.Closure φ ∧ ℬ.Closure ψ :=
  ⟨fun | .or hp hq => ⟨hp, hq⟩, fun ⟨hp, hq⟩ => .or hp hq⟩

lemma neg {φ : Semiformula L ξ n} : ℬ.Closure φ → ℬ.Closure (∼φ) := by
  intro h;
  induction h <;> try (solve | simp [*]);
  case ball hR ht _ ih => simpa only [neg_ball] using bexs hR ht ih;
  case bexs hR ht _ ih => simpa only [neg_bexs] using ball hR ht ih;

@[simp] lemma neg_iff {φ : Semiformula L ξ n} : ℬ.Closure (∼φ) ↔ ℬ.Closure φ :=
  ⟨fun h ↦ by simpa using h.neg, neg (ℬ := ℬ)⟩

@[simp] lemma ball_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (hR : R ∈ ℬ) (ht : t.Positive) : ℬ.Closure (∀¹[R.operator ![#0, t]] φ) ↔ ℬ.Closure φ := by
  constructor;
  . generalize hq : (∀¹[R.operator ![#0, t]] φ) = ψ;
    intro h;
    cases h <;> simp only [FFL.FirstOrder.ball, FFL.FirstOrder.bexs,
      all_inj, imp_inj, reduceCtorEq] at hq;
    case ball hR' ht h =>
      rcases hq with ⟨_, rfl⟩;
      exact h;
  . exact ball hR ht;

@[simp] lemma bexs_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (hR : R ∈ ℬ) (ht : t.Positive) : ℬ.Closure (∃¹[R.operator ![#0, t]] φ) ↔ ℬ.Closure φ := by
  constructor;
  . generalize hq : (∃¹[R.operator ![#0, t]] φ) = ψ;
    intro h;
    cases h <;> simp only [FFL.FirstOrder.ball, FFL.FirstOrder.bexs,
      exs_inj, Semiformula.and_inj, reduceCtorEq] at hq;
    case bexs hR' ht h =>
      rcases hq with ⟨_, rfl⟩;
      exact h;
  . exact bexs hR ht;

lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} :
    ℬ.Closure φ → ℬ.Closure (ω ▹ φ) := by
  intro h;
  induction h generalizing n₂ <;> simp [*];

lemma operator_preimage [SymbolLike ℬ ξ₁ ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {χ : Semiformula L ξ₁ (n₁ + 1)} {t : Semiterm L ξ₂ (n₂ + 1)}
    (hR : R ∈ ℬ) (hχ : ω.q ▹ χ = R.operator ![#0, t]) (ht : t.Positive) :
    ∃ u : Semiterm L ξ₁ (n₁ + 1), χ = R.operator ![#0, u] ∧ u.Positive := by
  obtain ⟨v, hχ, hv⟩ := ((inferInstance : SymbolLike ℬ ξ₁ ξ₂).symbolLike hR).symbolLike ω.q hχ;
  have hv0 : v 0 = #0 :=
    (Rew.q_eq_zero_iff (ω := ω) (t := v 0)).mp (by simpa using hv 0);
  have hv1 : ω.q (v 1) = t := by simpa using hv 1;
  use v 1;
  and_intros;
  . calc
      χ = R.operator v := hχ
      _ = R.operator ![#0, v 1] := by
        rw [Matrix.fun_eq_vec_two v, hv0];
        simp;
  . rw [← Rew.q_positive_iff (ω := ω) (t := v 1), hv1];
    exact ht;

@[simp] lemma rew_iff [SymbolLike ℬ ξ₁ ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    ℬ.Closure (ω ▹ φ) ↔ ℬ.Closure φ := by
  constructor;
  . generalize eq : ω ▹ φ = ψ;
    intro h;
    induction h generalizing φ n₁
      <;> simp only [Semiformula.eq_top_iff, Semiformula.eq_bot_iff, Semiformula.eq_rel_iff,
        Semiformula.eq_nrel_iff, Semiformula.eq_ball_iff, Semiformula.eq_bexs_iff,
        Semiformula.eq_and_iff, Semiformula.eq_or_iff, exists_and_left] at eq;
    case verum => rcases eq with rfl; simp;
    case falsum => rcases eq with rfl; simp;
    case rel => rcases eq with ⟨v, rfl, rfl⟩; simp;
    case nrel => rcases eq with ⟨v, rfl, rfl⟩; simp;
    case and ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩;
      exact .and (ihp rfl) (ihq rfl);
    case or ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩;
      exact .or (ihp rfl) (ihq rfl);
    case ball t hR ht _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩;
      obtain ⟨u, rfl, hu⟩ := operator_preimage (ℬ := ℬ) hR hχ ht;
      exact .ball hR hu (ih hφ);
    case bexs t hR ht _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩;
      obtain ⟨u, rfl, hu⟩ := operator_preimage (ℬ := ℬ) hR hχ ht;
      exact .bexs hR hu (ih hφ);
  . exact rew (ℬ := ℬ) _;

end Closure

@[simp] lemma strict_closure_iff_open {φ : Semiformula L ξ n} :
    ℬ[L].Closure φ ↔ φ.Open := by
  constructor
  · intro h
    induction h <;> try simp_all [Bounding.strict]
    case ball R φ t hR ht hp ih =>
      change R ∈ (∅ : Set (Semiformula.Operator L 2)) at hR
      simp at hR
    case bexs R φ t hR ht hp ih =>
      change R ∈ (∅ : Set (Semiformula.Operator L 2)) at hR
      simp at hR
  · intro h
    induction φ using Semiformula.rec' <;> simp_all [Semiformula.Open]

/-! The bounding principle for `R`. -/
def principle (R : Operator L 2) (φ : Semiformula L ξ 2) : Formula L ξ :=
  “∀ a, (∀ x, %R x a → ∃ y, !φ x y) → ∃ b, ∀ x, %R x a → ∃ y, %R y b ∧ !φ x y”

def schema (ℬ : Bounding L) (C : Semisentence L 2 → Prop) : Theory L :=
  Set.image2 principle {R | R ∈ ℬ} {φ | C φ}

def inductionPrinciple (R : Operator L 2) (φ : Semiformula L ξ 1) : Formula L ξ :=
  “(∀ x, (∀ y, %R y x → !φ y) → !φ x) → ∀ x, !φ x”

def inductionSchema (ℬ : Bounding L) (C : Semisentence L 1 → Prop) : Theory L :=
  Set.image2 inductionPrinciple {R | R ∈ ℬ} {φ | C φ}

end FFL.FirstOrder.Bounding
