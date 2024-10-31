import Foundation.Modal.Kripke.Semantics

namespace LO.Modal.Kripke

def ComplexityLimitedFrame (F : Kripke.Frame) (r : F.World) (φ : Formula α) : Kripke.Frame where
  World := { x | ∃ n ≤ φ.complexity, r ≺^[n] x }
  World_nonempty := ⟨r, by use 0; simp⟩
  Rel x y := x.1 ≺ y.1

def ComplexityLimitedModel (M : Kripke.Model α) (w : M.World) (φ : Formula α) : Kripke.Model α where
  Frame := ComplexityLimitedFrame M.Frame w φ
  Valuation x a := M.Valuation x.1 a

variable [DecidableEq α]
         {M : Kripke.Model α} {r x : M.World} {φ ψ : Formula α}

open Formula.Kripke
open Formula.subformulae

lemma iff_satisfy_complexity_limit_modelAux
  (hq : ψ ∈ φ.subformulae)
  (hx : ∃ n ≤ φ.complexity - ψ.complexity, r ≺^[n] x)
  : x ⊧ ψ ↔ Satisfies (ComplexityLimitedModel M r φ) ⟨x, (by obtain ⟨n, _, _⟩ := hx; use n; exact ⟨by omega, by assumption⟩)⟩ ψ := by
  induction ψ using Formula.rec' generalizing x φ with
  | hbox ψ ihq =>
    obtain ⟨n, hn, hx⟩ := hx;
    simp [Formula.complexity] at hn;
    have : n + 1 ≤ φ.complexity - ψ.complexity := by
      have : ψ.complexity + 1 ≤ φ.complexity := by simpa using complexity_lower hq;
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
  | himp ψ₁ ψ₂ ihq₁ ihq₂ =>
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

lemma iff_satisfy_complexity_limit_model : r ⊧ φ ↔ Satisfies (ComplexityLimitedModel M r φ) ⟨r, (by use 0; simp)⟩ φ := by
  apply iff_satisfy_complexity_limit_modelAux (show φ ∈ φ.subformulae by simp);
  use 0; simp;

lemma complexity_limit_model_subformula_closedAux {ψ₁ ψ₂ : Formula α} (hq₁ : φ ∈ ψ₁.subformulae) (hq₂ : φ ∈ ψ₂.subformulae)
  : Satisfies (ComplexityLimitedModel M r ψ₁) ⟨r, (by use 0; simp)⟩ φ → Satisfies (ComplexityLimitedModel M r ψ₂) ⟨r, (by use 0; simp)⟩ φ := by
  intro h;
  apply @iff_satisfy_complexity_limit_modelAux α _ M r r ψ₂ φ (by assumption) ?_ |>.mp;
  apply @iff_satisfy_complexity_limit_modelAux α _ M r r ψ₁ φ (by assumption) ?_ |>.mpr h;
  use 0; simp;
  use 0; simp;

lemma complexity_limit_model_subformula_closed (hq : φ ∈ ψ.subformulae)
  : Satisfies (ComplexityLimitedModel M r φ) ⟨r, (by use 0; simp)⟩ φ ↔ Satisfies (ComplexityLimitedModel M r ψ) ⟨r, (by use 0; simp)⟩ φ := by
  constructor;
  . apply complexity_limit_model_subformula_closedAux <;> simp_all;
  . apply complexity_limit_model_subformula_closedAux <;> simp_all;

end LO.Modal.Kripke
