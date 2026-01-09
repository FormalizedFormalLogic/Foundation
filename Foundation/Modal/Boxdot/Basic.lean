module
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Closure
import Foundation.Modal.Kripke.Irreflexivize

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment
open Formula

variable {φ : Formula α} {Ax Ax₁ Ax₂ : Axiom α}

def Formula.boxdotTranslate : Formula α → Formula α
  | atom a => .atom a
  | ⊥ => ⊥
  | φ ➝ ψ => (boxdotTranslate φ) ➝ (boxdotTranslate ψ)
  | □φ => ⊡(boxdotTranslate φ)
postfix:90 "ᵇ" => Formula.boxdotTranslate


theorem Hilbert.Normal.of_provable_boxdotTranslated_axiomInstances [Entailment.K (Hilbert.Normal Ax₂)]
  (h : ∀ φ ∈ Ax₁.instances, Hilbert.Normal Ax₂ ⊢ φᵇ) : Hilbert.Normal Ax₁ ⊢ φ → Hilbert.Normal Ax₂ ⊢ φᵇ := by
  intro d;
  induction d using Hilbert.Normal.rec! with
  | @axm φ s hs => apply h; use φ; tauto;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | nec ihp => exact boxdot_nec! $ ihp;
  | implyS => exact implyS!;
  | implyK => exact implyK!;
  | ec => exact elim_contra!;


namespace Formula.Kripke.Satisfies

open Kripke

variable {M : Kripke.Model} {x : M} {φ ψ : Formula _}

lemma iff_boxdotboxdot : x ⊧ φᵇᵇ ↔ x ⊧ φᵇ := by
  induction φ generalizing x with
  | hbox φ ih =>
    suffices x ⊧ (φᵇ) → (x ⊧ (□φᵇᵇ) ↔ x ⊧ (□φᵇ)) by simpa [Formula.boxdotTranslate, Box.boxdot, ih];
    intro h₁;
    constructor;
    . intro h₂ y Rxy; exact ih.mp $ @h₂ y Rxy;
    . intro h₂ y Rxy; exact ih.mpr $ @h₂ y Rxy;
  | _ => simp_all [Formula.boxdotTranslate];

lemma boxdot_and : x ⊧ (φ ⋏ ψ)ᵇ ↔ x ⊧ φᵇ ⋏ ψᵇ := by simp [boxdotTranslate];

lemma boxdotTranslate_lconj {l : List _} : x ⊧ l.conjᵇ ↔ x ⊧ (l.map (·ᵇ)).conj := by
  induction l with
  | nil => simp [Formula.boxdotTranslate];
  | cons φ l ih =>
    apply Iff.trans boxdot_and;
    apply Iff.trans Satisfies.and_def;
    suffices x ⊧ φᵇ → (x ⊧ (l.conjᵇ) ↔ ∀ ψ ∈ l, x ⊧ (ψᵇ)) by simpa;
    intro hφ;
    constructor;
    . intro hl ψ hψ;
      have := ih.mp hl;
      apply Satisfies.conj₁_def.mp this;
      simp;
      tauto;
    . intro h;
      apply ih.mpr;
      apply Satisfies.conj₁_def.mpr;
      simpa;

lemma boxdotTranslate_lconj₂ {l : List _} : x ⊧ (⋀l)ᵇ ↔ x ⊧ ⋀(l.map (·ᵇ)) := by
  induction l using List.induction_with_singleton with
  | hnil => simp [Formula.boxdotTranslate];
  | hsingle φ => simp;
  | hcons φ l hl ih =>
    suffices x ⊧ ((φ ⋏ ⋀l)ᵇ) ↔ x ⊧ (φᵇ) ∧ ∀ a ∈ l, x ⊧ (aᵇ) by simpa [hl, boxdot_and];
    apply Iff.trans boxdot_and;
    apply Iff.trans Satisfies.and_def;
    suffices x ⊧ φᵇ → (x ⊧ (⋀l)ᵇ ↔ ∀ ψ ∈ l, x ⊧ (ψᵇ)) by simpa;
    intro hφ;
    constructor;
    . intro hl ψ hψ;
      have := ih.mp hl;
      apply Satisfies.conj_def.mp this;
      simp;
      tauto;
    . intro h;
      apply ih.mpr;
      apply Satisfies.conj_def.mpr;
      simpa;

lemma boxdotTranslate_fconj₂ {Γ : Finset _} : x ⊧ Γ.conjᵇ ↔ x ⊧ (Γ.image (·ᵇ)).conj := by
  obtain ⟨l, rfl⟩ : ∃ l : List _, l.toFinset = Γ := ⟨Γ.toList, by simp⟩
  induction l with
  | nil => simp [Formula.boxdotTranslate];
  | cons φ l ih =>
    apply Iff.trans boxdotTranslate_lconj₂;
    suffices (∀ ψ, (φᵇ = ψ ∨ ∃ ξ ∈ l, ξᵇ = ψ) → x ⊧ ψ) ↔ x ⊧ (φᵇ) ∧ ∀ ξ ∈ l, x ⊧ (ξᵇ) by simpa;
    constructor;
    . intro h;
      constructor;
      . apply h;
        tauto;
      . intro ψ hψ;
        apply h;
        right;
        use ψ;
    . rintro ⟨h₁, h₂⟩ _ (rfl | ⟨ψ, hψ, rfl⟩);
      . assumption;
      . apply h₂;
        assumption;

lemma iff_boxdotTranslateMultibox_boxdotTranslateBoxlt : x ⊧ (□^[n]φ)ᵇ ↔ x ⊧ □^≤[n] φᵇ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    suffices (∀ k < n + 1, x ⊧ (□^[k]φᵇ)) ∧ x ⊧ (□(□^[n]φ)ᵇ) ↔ (∀ k < n + 2, x ⊧ (□^[k]φᵇ)) by
      simpa [Box.boxdot, boxdotTranslate, ih, Box.boxLe];
    constructor;
    . rintro ⟨h₁, h₂⟩ k hk;
      apply Satisfies.boxItr_def.mpr;
      intro y Rxy;
      by_cases ek : k = n + 1;
      . subst ek;
        obtain ⟨u, Ryu, Ruy⟩ := Rxy;
        apply Satisfies.boxItr_def.mp (Satisfies.fconj_def.mp (ih.mp $ h₂ u Ryu) _ ?_) Ruy;
        . simp;
          tauto;
      . exact Satisfies.boxItr_def.mp (h₁ k (by omega)) Rxy;
    . intro h;
      constructor;
      . intro k hk;
        apply Satisfies.boxItr_def.mpr;
        intro y Rxy;
        apply Satisfies.boxItr_def.mp (@h k (by omega)) Rxy;
      . intro y Rxy;
        apply ih.mpr;
        apply Satisfies.fconj_def.mpr;
        simp only [Finset.mem_image, Finset.mem_range, Satisfies.iff_models, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂];
        intro k hk;
        apply Satisfies.boxItr_def.mpr;
        intro u Ryu;
        apply Satisfies.boxItr_def.mp $ @h (k + 1) (by omega);
        use y;

end Formula.Kripke.Satisfies


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
        | single h => exact h.1;
    . intro h y Rxy;
      by_cases e : x = y;
      . subst e;
        apply ihp.mpr;
        exact h x ReflGen.refl;
      . apply ihp (x := y) |>.mpr;
        exact h y $ by
          exact ReflGen.single ⟨Rxy, (by simpa)⟩;

lemma iff_reflexivize_irreflexivize' [F.IsReflexive] : (F ⊧ φ) ↔ ((F^≠^=) ⊧ φ) := by
  constructor;
  . intro h V x; apply iff_reflexivize_irreflexivize.mp; exact h V x;
  . intro h V x; apply iff_reflexivize_irreflexivize.mpr; exact h V x;

end Kripke

end LO.Modal
