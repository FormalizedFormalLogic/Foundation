import Foundation.Modal.Hilbert.Basic
import Foundation.Modal.Kripke.Closure

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment
open Formula
open Hilbert.Deduction

variable [DecidableEq α]
variable {φ : Formula α}

def Formula.boxdotTranslate : Formula α → Formula α
  | atom a => .atom a
  | ⊥ => ⊥
  | φ ➝ ψ => (boxdotTranslate φ) ➝ (boxdotTranslate ψ)
  | □φ => ⊡(boxdotTranslate φ)
postfix:90 "ᵇ" => Formula.boxdotTranslate

class BoxdotProperty (L₁ L₂ : Logic) where
  bdp {φ : _} : φᵇ ∈ L₁ ↔ φ ∈ L₂


theorem Hilbert.boxdotTranslated_of_dominate {H₁ H₂ : Hilbert α} [Entailment.K H₂]
  (h : ∀ φ ∈ H₁.axiomInstances, H₂ ⊢! φᵇ) : H₁ ⊢! φ → H₂ ⊢! φᵇ := by
  intro d;
  induction d using Hilbert.Deduction.rec! with
  | maxm hs => exact h _ hs;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | nec ihp => exact boxdot_nec! $ ihp;
  | imply₂ => exact imply₂!;
  | imply₁ => exact imply₁!;
  | ec => exact elim_contra!;


namespace Kripke

open Relation (ReflGen)
open Formula.Kripke

variable {F : Frame} {φ : Formula _}

lemma iff_boxdot_reflexive_closure : (Satisfies ⟨F, V⟩ x (φᵇ)) ↔ (Satisfies ⟨F^=, V⟩ x φ) := by
  induction φ generalizing x with
  | himp φ ψ ihp ihq =>
    constructor;
    . intro h hp;
      apply ihq.mp;
      exact h $ ihp.mpr hp;
    . intro h hp;
      apply ihq.mpr;
      exact h $ ihp.mp hp;
  | hbox φ ih =>
    simp [Formula.boxdotTranslate, Box.boxdot, Satisfies];
    constructor;
    . rintro ⟨h₁, h₂⟩;
      intro y Rxy;
      rcases (Relation.reflGen_iff _ _ _ |>.mp Rxy) with (rfl | Rxy);
      . apply ih.mp h₁;
      . exact ih.mp $ h₂ y Rxy;
    . rintro h;
      constructor;
      . exact ih.mpr $ @h x ReflGen.refl;
      . intro y Rxy;
        apply ih.mpr;
        exact @h y (ReflGen.single Rxy);
  | _ => rfl;

lemma iff_frame_boxdot_reflexive_closure : (F ⊧ (φᵇ)) ↔ ((F^=) ⊧ φ) := by
  constructor;
  . intro h V x; apply iff_boxdot_reflexive_closure.mp; exact h V x;
  . intro h V x; apply iff_boxdot_reflexive_closure.mpr; exact h V x;

lemma iff_reflexivize_irreflexivize [F.IsReflexive] {x : F.World} {V} : (Satisfies ⟨F, V⟩ x φ) ↔ (Satisfies ⟨F^≠^=, V⟩ x φ) := by
  induction φ generalizing x with
  | hatom φ => rfl;
  | hfalsum => rfl;
  | himp φ ψ ihp ihq =>
    constructor;
    . intro h hp;
      apply ihq.mp;
      exact h $ ihp.mpr hp;
    . intro h hp;
      apply ihq.mpr;
      exact h $ ihp.mp hp;
  | hbox φ ihp =>
    constructor;
    . intro h y Rxy;
      apply ihp (x := y) |>.mp;
      exact h y $ by
        induction Rxy with
        | refl => apply IsRefl.refl;
        | single h => exact h.2;
    . intro h y Rxy;
      by_cases e : x = y;
      . subst e;
        apply ihp.mpr;
        exact h x ReflGen.refl;
      . apply ihp (x := y) |>.mpr;
        exact h y $ by
          exact ReflGen.single ⟨(by simpa), Rxy⟩;

lemma iff_reflexivize_irreflexivize' [F.IsReflexive] : (F ⊧ φ) ↔ ((F^≠^=) ⊧ φ) := by
  constructor;
  . intro h V x; apply iff_reflexivize_irreflexivize.mp; exact h V x;
  . intro h V x; apply iff_reflexivize_irreflexivize.mpr; exact h V x;

end Kripke

end LO.Modal
