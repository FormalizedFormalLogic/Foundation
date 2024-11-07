import Foundation.Logic.Disjunctive
import Foundation.IntProp.Kripke.Completeness

namespace LO.IntProp

open System
open Formula Formula.Kripke

namespace Kripke

variable {α}
variable {φ ψ : Formula α}

abbrev IntDPCounterexampleFrame (F₁ : Kripke.Frame) (F₂ : Kripke.Frame) (w₁ : F₁.World) (w₂ : F₂.World) : Kripke.Frame where
  World := Unit ⊕ F₁.World ⊕ F₂.World;
  Rel x y :=
    match x, y with
    | (Sum.inl _), (Sum.inl _) => True
    | (Sum.inl _), (Sum.inr $ Sum.inl y) => F₁.Rel w₁ y
    | (Sum.inl _), (Sum.inr $ Sum.inr y) => F₂.Rel w₂ y
    | (Sum.inr $ Sum.inl x), (Sum.inr $ Sum.inl y) => F₁.Rel x y
    | (Sum.inr $ Sum.inr x), (Sum.inr $ Sum.inr y) => F₂.Rel x y
    | _, _ => False

lemma IntDPCounterexampleFrame.reflexive
  {F₁ : Kripke.Frame} {F₂ : Kripke.Frame}
  {w₁ : F₁.World} {w₂ : F₂.World}
  (F₁_refl : Reflexive F₁.Rel) (F₂_refl : Reflexive F₂.Rel)
  : Reflexive (IntDPCounterexampleFrame F₁ F₂ w₁ w₂).Rel := by
  simp only [Reflexive, Sum.forall, forall_const, true_and];
  constructor;
  . exact F₁_refl;
  . exact F₂_refl;

lemma IntDPCounterexampleFrame.transitive
  {F₁ : Kripke.Frame} {F₂ : Kripke.Frame}
  {w₁ : F₁.World} {w₂ : F₂.World}
  (F₁_trans : Transitive F₁.Rel) (F₂_trans : Transitive F₂.Rel)
  : Transitive (IntDPCounterexampleFrame F₁ F₂ w₁ w₂).Rel := by
  simp only [Transitive, Sum.forall, forall_true_left, imp_self, forall_const, true_and, IsEmpty.forall_iff, implies_true, and_true, and_self, imp_false];
  constructor;
  . constructor;
    . intro _ _; apply F₁_trans;
    . intro _ _; apply F₂_trans;
  . constructor;
    . intro _ _; apply F₁_trans;
    . intro _ _; apply F₂_trans;

lemma IntDPCounterexampleFrame.antisymmetric
  {F₁ : Kripke.Frame} {F₂ : Kripke.Frame}
  {w₁ : F₁.World} {w₂ : F₂.World}
  (F₁_antisymm : Antisymmetric F₁.Rel) (F₂_antisymm : Antisymmetric F₂.Rel)
  : Antisymmetric (IntDPCounterexampleFrame F₁ F₂ w₁ w₂).Rel := by
  simp only [Antisymmetric, Sum.forall, forall_true_left, forall_const, IsEmpty.forall_iff, implies_true, and_self, imp_false, Sum.inr.injEq, true_and, Sum.inl.injEq, and_true];
  constructor;
  . exact F₁_antisymm;
  . exact F₂_antisymm;

abbrev IntDPCounterexampleModel (M₁ : Kripke.Model α) (M₂ : Kripke.Model α) (w₁ : M₁.World) (w₂ : M₂.World) : Kripke.Model α where
  Frame := IntDPCounterexampleFrame M₁.Frame M₂.Frame w₁ w₂;
  Valuation w a :=
    match w with
    | Sum.inr $ Sum.inl w => M₁.Valuation w a
    | Sum.inr $ Sum.inr w => M₂.Valuation w a
    | _ => False

lemma IntDPCounterexampleModel.atomic_hereditary
  {M₁ : Kripke.Model α} {M₂ : Kripke.Model α}
  {w₁ : M₁.World} {w₂ : M₂.World}
  (M₁_hered : M₁.Valuation.atomic_hereditary) (M₂_hered : M₂.Valuation.atomic_hereditary)
  : (IntDPCounterexampleModel M₁ M₂ w₁ w₂).Valuation.atomic_hereditary := by
  simp;
  constructor;
  . apply M₁_hered;
  . apply M₂_hered;

variable {M₁ : Kripke.Model α} {M₂ : Kripke.Model α}

lemma satisfies_left_on_IntDPCounterexampleModel :
  (Satisfies M₁ w φ) ↔ (Satisfies (IntDPCounterexampleModel M₁ M₂ w₁ w₂) (Sum.inr $ Sum.inl w) φ) := by
  induction φ using rec' generalizing w with
  | himp φ ψ ihp ihq =>
    constructor;
    . intro hpq X hWX hp;
      obtain ⟨x, hx, ex⟩ : ∃ x, (M₁.Frame.Rel w x) ∧ (Sum.inr $ Sum.inl x) = X := by
        replace hWX : (IntDPCounterexampleModel M₁ M₂ w₁ w₂).Frame.Rel _ X := hWX;
        simp [IntDPCounterexampleFrame] at hWX;
        split at hWX;
        all_goals simp_all;
      subst ex;
      exact ihq.mp $ hpq hx $ ihp.mpr hp;
    . intro h v Rwv hp;
      apply @ihq v |>.mpr $ h (by simpa) $ ihp.mp hp;
  | _ => simp_all [IntDPCounterexampleModel, Satisfies.iff_models, Satisfies];

lemma satisfies_right_on_IntDPCounterexampleModel :
  (Satisfies M₂ w φ) ↔ (Satisfies (IntDPCounterexampleModel M₁ M₂ w₁ w₂) (Sum.inr $ Sum.inr w) φ) := by
  induction φ using rec' generalizing w with
  | himp φ ψ ihp ihq =>
    constructor;
    . intro h X hWX hp;
      obtain ⟨x, hx, ex⟩ : ∃ x, (M₂.Frame.Rel w x) ∧ (Sum.inr $ Sum.inr x) = X := by
        replace hWX : (IntDPCounterexampleModel M₁ M₂ w₁ w₂).Frame.Rel _ X := hWX;
        simp [IntDPCounterexampleFrame] at hWX;
        split at hWX;
        all_goals simp_all;
      subst ex;
      exact ihq.mp $ h hx $ ihp.mpr hp;
    . intro h v Rwv hp;
      exact ihq.mpr $ h (by simpa) $ ihp.mp hp;
  | _ => simp_all [IntDPCounterexampleModel, Satisfies.iff_models, Satisfies];

theorem disjunctive_int [Inhabited α] [DecidableEq α] [Encodable α] : (Hilbert.Int α) ⊢! φ ⋎ ψ → (Hilbert.Int α) ⊢! φ ∨ (Hilbert.Int α) ⊢! ψ := by
  contrapose;
  intro hC; push_neg at hC;
  have ⟨hnp, hnq⟩ := hC;
  obtain ⟨Fp, Fp_refl, Fp_trans, Vp, Vp_hered, wp, hp⟩ := by simpa [Semantics.Realize, ValidOnFrame, ValidOnModel] using not_imp_not.mpr Int_complete.complete hnp;
  obtain ⟨Fq, Fq_refl, Fq_trans, Vq, Vq_hered, wq, hq⟩ := by simpa [Semantics.Realize, ValidOnFrame, ValidOnModel] using not_imp_not.mpr Int_complete.complete hnq;
  apply (not_imp_not.mpr Int_sound.sound);
  simp [Semantics.Realize, ValidOnFrame, ValidOnModel, Satisfies];
  use (IntDPCounterexampleFrame Fp Fq wp wq);
  refine ⟨IntDPCounterexampleFrame.reflexive Fp_refl Fq_refl, IntDPCounterexampleFrame.transitive Fp_trans Fq_trans, ?_⟩;
  use (IntDPCounterexampleModel ⟨Fp, Vp⟩ ⟨Fq, Vq⟩ wp wq).Valuation;
  constructor;
  . exact IntDPCounterexampleModel.atomic_hereditary (M₁ := ⟨Fp, Vp⟩) (M₂ := ⟨Fq, Vq⟩) Vp_hered Vq_hered;
  . use (Sum.inl ());
    constructor;
    . exact not_imp_not.mpr
        (Satisfies.formula_hereditary
          (M := IntDPCounterexampleModel ⟨Fp, Vp⟩ ⟨Fq, Vq⟩ wp wq)
          (IntDPCounterexampleModel.atomic_hereditary Vp_hered Vq_hered)
          (IntDPCounterexampleFrame.transitive Fp_trans Fq_trans)
          (w := Sum.inl ()) (w' := Sum.inr $ Sum.inl wp) (by aesop))
        $ satisfies_left_on_IntDPCounterexampleModel |>.not.mp hp;
    . exact not_imp_not.mpr
        (Satisfies.formula_hereditary
          (M := IntDPCounterexampleModel ⟨Fp, Vp⟩ ⟨Fq, Vq⟩ wp wq)
          (IntDPCounterexampleModel.atomic_hereditary Vp_hered Vq_hered)
          (IntDPCounterexampleFrame.transitive Fp_trans Fq_trans)
          (w := Sum.inl ()) (w' := Sum.inr $ Sum.inr wq) (by aesop))
        $ satisfies_right_on_IntDPCounterexampleModel |>.not.mp hq;

instance [DecidableEq α] [Inhabited α] [Encodable α] : Disjunctive (Hilbert.Int α) := ⟨disjunctive_int⟩

end Kripke

end LO.IntProp
