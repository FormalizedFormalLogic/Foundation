module

public import Foundation.FirstOrder.Syntax.Classical.Operator

/-!
Bounded formulas with bounds supplied by an operator; this operator-parametric presentation
and its rewriting lemmas are specific to this formalization.
-/

@[expose] public section

namespace FFL.FirstOrder.Semiformula

variable {L : Language} {ξ ξ₁ ξ₂ : Type*}
variable (R : Operator L 2)

inductive Bounded : {n : ℕ} → Semiformula L ξ n → Prop
  | verum (n) : Bounded (⊤ : Semiformula L ξ n)
  | falsum (n) : Bounded (⊥ : Semiformula L ξ n)
  | rel {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : Bounded (.rel r v)
  | nrel {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : Bounded (.nrel r v)
  | and {n} {φ ψ : Semiformula L ξ n} : Bounded φ → Bounded ψ → Bounded (φ ⋏ ψ)
  | or {n} {φ ψ : Semiformula L ξ n} : Bounded φ → Bounded ψ → Bounded (φ ⋎ ψ)
  | ball {n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Bounded φ → Bounded (∀¹[R.operator ![#0, t]] φ)
  | bexs {n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Bounded φ → Bounded (∃¹[R.operator ![#0, t]] φ)

namespace Bounded

attribute [simp] verum falsum rel nrel

variable {R} {n n₁ n₂ : ℕ}

@[simp] lemma and_iff {φ ψ : Semiformula L ξ n} :
    Bounded R (φ ⋏ ψ) ↔ Bounded R φ ∧ Bounded R ψ :=
  ⟨fun | .and hp hq => ⟨hp, hq⟩, fun ⟨hp, hq⟩ => .and hp hq⟩

@[simp] lemma or_iff {φ ψ : Semiformula L ξ n} :
    Bounded R (φ ⋎ ψ) ↔ Bounded R φ ∧ Bounded R ψ :=
  ⟨fun | .or hp hq => ⟨hp, hq⟩, fun ⟨hp, hq⟩ => .or hp hq⟩

lemma neg {φ : Semiformula L ξ n} : Bounded R φ → Bounded R (∼φ) := by
  intro h;
  induction h <;> try (solve | simp [*]);
  case ball ht _ ih => simpa only [neg_ball] using bexs ht ih;
  case bexs ht _ ih => simpa only [neg_bexs] using ball ht ih;

@[simp] lemma neg_iff {φ : Semiformula L ξ n} : Bounded R (∼φ) ↔ Bounded R φ :=
  ⟨fun h => by simpa using h.neg, neg⟩

@[simp] lemma ball_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) : Bounded R (∀¹[R.operator ![#0, t]] φ) ↔ Bounded R φ := by
  constructor;
  . generalize hq : (∀¹[R.operator ![#0, t]] φ) = ψ;
    intro h;
    cases h <;> simp only [FFL.FirstOrder.ball, FFL.FirstOrder.bexs,
      all_inj, imp_inj, reduceCtorEq] at hq;
    case ball ht h =>
      rcases hq with ⟨_, rfl⟩;
      exact h;
  . exact ball ht;

@[simp] lemma bexs_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) : Bounded R (∃¹[R.operator ![#0, t]] φ) ↔ Bounded R φ := by
  constructor;
  . generalize hq : (∃¹[R.operator ![#0, t]] φ) = ψ;
    intro h;
    cases h <;> simp only [FFL.FirstOrder.ball, FFL.FirstOrder.bexs,
      exs_inj, Semiformula.and_inj, reduceCtorEq] at hq;
    case bexs ht h =>
      rcases hq with ⟨_, rfl⟩;
      exact h;
  . exact bexs ht;

lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} :
    Bounded R φ → Bounded R (ω ▹ φ) := by
  intro h;
  induction h generalizing n₂ <;> simp [*];

lemma operator_preimage [R.SymbolLike ξ₁ ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {χ : Semiformula L ξ₁ (n₁ + 1)} {t : Semiterm L ξ₂ (n₂ + 1)}
    (hχ : ω.q ▹ χ = R.operator ![#0, t]) (ht : t.Positive) :
    ∃ u : Semiterm L ξ₁ (n₁ + 1), χ = R.operator ![#0, u] ∧ u.Positive := by
  obtain ⟨v, hχ, hv⟩ := (inferInstance : R.SymbolLike ξ₁ ξ₂).symbolLike ω.q hχ;
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

@[simp] lemma rew_iff [R.SymbolLike ξ₁ ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    Bounded R (ω ▹ φ) ↔ Bounded R φ := by
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
    case ball t ht _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩;
      obtain ⟨u, rfl, hu⟩ := operator_preimage hχ ht;
      exact .ball hu (ih hφ);
    case bexs t ht _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩;
      obtain ⟨u, rfl, hu⟩ := operator_preimage hχ ht;
      exact .bexs hu (ih hφ);
  . exact rew _;

end Bounded

end FFL.FirstOrder.Semiformula

namespace FFL.FirstOrder

/-- A formula bundled with a proof that it is bounded with respect to `R`. -/
structure BoundedSemiformula (R : Semiformula.Operator L 2) (ξ : Type*) (n : ℕ) where
  val : Semiformula L ξ n
  bounded : Semiformula.Bounded R val

abbrev BoundedSemisentence (R : Semiformula.Operator L 2) (n : ℕ) := BoundedSemiformula R Empty n

namespace BoundedSemiformula

variable {L : Language} {R : Semiformula.Operator L 2} {ξ ξ₁ ξ₂ : Type*} {n n₁ n₂ : ℕ}

attribute [simp] bounded

instance : CoeTC (BoundedSemiformula R ξ n) (Semiformula L ξ n) := ⟨val⟩

@[ext] lemma ext {φ ψ : BoundedSemiformula R ξ n} (h : φ.val = ψ.val) : φ = ψ := by
  cases φ; cases ψ; simpa using h

def rew (φ : BoundedSemiformula R ξ₁ n₁) (ω : Rew L ξ₁ n₁ ξ₂ n₂) : BoundedSemiformula R ξ₂ n₂ :=
  ⟨ω ▹ φ.val, φ.bounded.rew ω⟩

@[simp] lemma val_rew (φ : BoundedSemiformula R ξ₁ n₁) (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    (φ.rew ω).val = ω ▹ φ.val := rfl

end BoundedSemiformula

end FFL.FirstOrder
