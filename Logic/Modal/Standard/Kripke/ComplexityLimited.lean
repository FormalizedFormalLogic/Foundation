import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard.Kripke

def ComplexityLimitedFrame (F : Kripke.Frame) (r : F.World) (p : Formula α) : Kripke.Frame where
  World := { x | ∃ n ≤ p.complexity, r ≺^[n] x }
  World_nonempty := ⟨r, by use 0; simp⟩
  Rel x y := x.1 ≺ y.1

def ComplexityLimitedModel (M : Kripke.Model α) (w : M.World) (p : Formula α) : Kripke.Model α where
  Frame := ComplexityLimitedFrame M.Frame w p
  Valuation x a := M.Valuation x.1 a

variable [DecidableEq α]
         {M : Kripke.Model α} {r x : M.World} {p q : Formula α}

open Formula.Kripke
open Formula.Subformulas

lemma iff_satisfy_complexity_limit_modelAux
  (hq : q ∈ 𝒮 p)
  (hx : ∃ n ≤ p.complexity - q.complexity, r ≺^[n] x)
  : x ⊧ q ↔ Satisfies (ComplexityLimitedModel M r p) ⟨x, (by obtain ⟨n, _, _⟩ := hx; use n; exact ⟨by omega, by assumption⟩)⟩ q := by
  induction q using Formula.rec' generalizing x p with
  | hbox q ihq =>
    obtain ⟨n, hn, hx⟩ := hx;
    simp [Formula.complexity] at hn;
    have : n + 1 ≤ p.complexity - q.complexity := by
      have : q.complexity + 1 ≤ p.complexity := by simpa using complexity_lower hq;
      omega;
    constructor;
    . rintro h ⟨y, hy⟩ Rxy;
      apply ihq (mem_box (by assumption)) ?_ |>.mp;
      . exact h _ Rxy;
      . use (n + 1);
        constructor;
        . assumption;
        . apply Kripke.Frame.RelItr'.forward.mpr;
          use x; constructor; assumption; exact Rxy;
    . rintro h y Rxy;
      apply ihq (mem_box (by assumption)) ?_ |>.mpr;
      . exact h _ Rxy;
      . use (n + 1);
        constructor;
        . assumption;
        . apply Kripke.Frame.RelItr'.forward.mpr;
          use x;
  | himp q₁ q₂ ihq₁ ihq₂ =>
    obtain ⟨n, hn, hx⟩ := hx;
    simp [Formula.complexity] at hn;
    constructor;
    . rintro hq₁ hq₂;
      apply ihq₂ (mem_imp (by assumption) |>.2) ?_ |>.mp;
      apply hq₁;
      apply ihq₁ (mem_imp (by assumption) |>.1) ?_ |>.mpr hq₂;
      use n; constructor; omega; assumption;
      use n; constructor; omega; assumption;
    . rintro hq₁ hq₂;
      apply ihq₂ (mem_imp (by assumption) |>.2) ?_ |>.mpr;
      apply hq₁;
      apply ihq₁ (mem_imp (by assumption) |>.1) ?_ |>.mp hq₂;
      use n; constructor; omega; assumption;
      use n; constructor; omega; assumption;
  | _ => simp [Satisfies, ComplexityLimitedModel];

lemma iff_satisfy_complexity_limit_model : r ⊧ p ↔ Satisfies (ComplexityLimitedModel M r p) ⟨r, (by use 0; simp)⟩ p := by
  apply iff_satisfy_complexity_limit_modelAux (show p ∈ 𝒮 p by simp);
  use 0; simp;

lemma complexity_limit_model_subformula_closedAux {q₁ q₂ : Formula α} (hq₁ : p ∈ 𝒮 q₁) (hq₂ : p ∈ 𝒮 q₂)
  : Satisfies (ComplexityLimitedModel M r q₁) ⟨r, (by use 0; simp)⟩ p → Satisfies (ComplexityLimitedModel M r q₂) ⟨r, (by use 0; simp)⟩ p := by
  intro h;
  apply @iff_satisfy_complexity_limit_modelAux α _ M r r q₂ p (by assumption) ?_ |>.mp;
  apply @iff_satisfy_complexity_limit_modelAux α _ M r r q₁ p (by assumption) ?_ |>.mpr h;
  use 0; simp;
  use 0; simp;

lemma complexity_limit_model_subformula_closed (hq : p ∈ 𝒮 q)
  : Satisfies (ComplexityLimitedModel M r p) ⟨r, (by use 0; simp)⟩ p ↔ Satisfies (ComplexityLimitedModel M r q) ⟨r, (by use 0; simp)⟩ p := by
  constructor;
  . apply complexity_limit_model_subformula_closedAux <;> simp_all;
  . apply complexity_limit_model_subformula_closedAux <;> simp_all;

end LO.Modal.Standard.Kripke
