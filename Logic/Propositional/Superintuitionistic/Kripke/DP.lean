import Logic.Propositional.Superintuitionistic.Kripke.Soundness
import Logic.Propositional.Superintuitionistic.Kripke.Completeness

namespace LO.System

variable {F : Type*} [LogicalConnective F]
variable {S : Type*} [System F S]

class Disjunctive (𝓢 : S) : Prop where
  disjunctive : ∀ {p q}, 𝓢 ⊢! p ⋎ q → 𝓢 ⊢! p ∨ 𝓢 ⊢! q

end LO.System


namespace LO.Propositional.Superintuitionistic

open System
open Formula Formula.Kripke

namespace Kripke

variable {α} [Inhabited α] [DecidableEq α] [Encodable α]
variable {p q : Formula α}

abbrev IntDPCounterexampleFrame (F₁ : Frame.{u}) (F₂ : Frame.{u}) (w₁ : F₁.World) (w₂ : F₂.World) : Frame where
  World := Unit ⊕ F₁.World ⊕ F₂.World;
  Rel w v :=
    match w, v with
    | (Sum.inl _), (Sum.inl _) => True
    | (Sum.inl _), (Sum.inr $ Sum.inl v) => w₁ ≺ v
    | (Sum.inl _), (Sum.inr $ Sum.inr v) => w₂ ≺ v
    | (Sum.inr $ Sum.inl w), (Sum.inr $ Sum.inl v) => w ≺ v
    | (Sum.inr $ Sum.inr w), (Sum.inr $ Sum.inr v) => w ≺ v
    | _, _ => False
  Rel_refl := by
    simp only [Reflexive, Sum.forall, forall_const, true_and];
    constructor;
    . exact F₁.Rel_refl;
    . exact F₂.Rel_refl;
  Rel_trans := by
    simp only [Transitive, Sum.forall, forall_true_left, imp_self, forall_const, true_and, IsEmpty.forall_iff, implies_true, and_true, and_self, imp_false];
    constructor;
    . constructor;
      . intro _ _; apply F₁.Rel_trans;
      . intro _ _; apply F₂.Rel_trans;
    . constructor;
      . intro _ _; apply F₁.Rel_trans;
      . intro _ _; apply F₂.Rel_trans;
  Rel_antisymm := by
    simp only [Antisymmetric, Sum.forall, forall_true_left, forall_const, IsEmpty.forall_iff, implies_true, and_self, imp_false, Sum.inr.injEq, true_and, Sum.inl.injEq, and_true];
    constructor;
    . exact F₁.Rel_antisymm;
    . exact F₂.Rel_antisymm;

abbrev IntDPCounterexampleModel (M₁ : Model α) (M₂ : Model α) (w₁ : M₁.World) (w₂ : M₂.World) : Model α where
  Frame := IntDPCounterexampleFrame M₁.Frame M₂.Frame w₁ w₂;
  Valuation w a :=
    match w with
    | Sum.inr $ Sum.inl w => M₁.Valuation w a
    | Sum.inr $ Sum.inr w => M₂.Valuation w a
    | _ => False
  hereditary := by
    simp only [Sum.forall, imp_false, not_false_eq_true, implies_true, forall_true_left, forall_const, IsEmpty.forall_iff, and_self, and_true, true_and];
    constructor;
    . intro _ _; apply M₁.hereditary;
    . intro _ _; apply M₂.hereditary;

variable {M₁ : Model α} {M₂ : Model α}

lemma satisfies_left_on_IntDPCounterexampleModel :
  (Satisfies M₁ w p) ↔ (Satisfies (IntDPCounterexampleModel M₁ M₂ w₁ w₂) (Sum.inr $ Sum.inl w) p) := by
  -- ((M₁, w) ⊧ p) ↔ ((IntDPCounterexampleModel M₁ M₂ w₁ w₂, (Sum.inr $ Sum.inl w : (Unit ⊕ W₁ ⊕ W₂))) ⊧ p) := by
  induction p using rec' generalizing w with
  | himp p q ihp ihq =>
    constructor;
    . simp only [Satisfies.imp_def];
      intro h X hWX hp;
      obtain ⟨x, hx, ex⟩ : ∃ x, w ≺ x ∧ (Sum.inr $ Sum.inl x) = X := by
        replace hWX : (IntDPCounterexampleModel M₁ M₂ w₁ w₂).Frame.Rel _ X := hWX;
        simp [IntDPCounterexampleFrame] at hWX;
        split at hWX;
        all_goals simp_all;
      subst ex;
      exact ihq.mp $ h hx $ ihp.mpr hp;
    . simp only [Satisfies.imp_def];
      intro h v hv hp;
      exact ihq.mpr $ h (by simpa [IntDPCounterexampleModel]) $ ihp.mp hp;
  | _ => simp_all [IntDPCounterexampleModel, Satisfies.iff_models, Satisfies];

lemma satisfies_right_on_IntDPCounterexampleModel :
  (Satisfies M₂ w p) ↔ (Satisfies (IntDPCounterexampleModel M₁ M₂ w₁ w₂) (Sum.inr $ Sum.inr w) p) := by
  -- : ((M₂, w) ⊧ p) ↔ ((IntDPCounterexampleModel M₁ M₂ w₁ w₂, (Sum.inr $ Sum.inr w : (Unit ⊕ W₁ ⊕ W₂))) ⊧ p) := by
  induction p using rec' generalizing w with
  | himp p q ihp ihq =>
    constructor;
    . simp only [Satisfies.imp_def];
      intro h X hWX hp;
      obtain ⟨x, hx, ex⟩ : ∃ x, w ≺ x ∧ (Sum.inr $ Sum.inr x) = X := by
        replace hWX : (IntDPCounterexampleModel M₁ M₂ w₁ w₂).Frame.Rel _ X := hWX;
        simp [IntDPCounterexampleFrame] at hWX;
        split at hWX;
        all_goals simp_all;
      subst ex;
      exact ihq.mp $ h hx $ ihp.mpr hp;
    . simp only [Satisfies.imp_def];
      intro h v hv hp;
      exact ihq.mpr $ h (by simpa [IntDPCounterexampleModel]) $ ihp.mp hp;
  | _ => simp_all [IntDPCounterexampleModel, Satisfies.iff_models, Satisfies];

theorem disjunctive_int : 𝐈𝐧𝐭 ⊢! p ⋎ q → 𝐈𝐧𝐭 ⊢! p ∨ 𝐈𝐧𝐭 ⊢! q := by
  contrapose;
  intro hC; push_neg at hC;
  have ⟨hnp, hnq⟩ := hC;
  obtain ⟨Fp, _, Vp, hVp, wp, hp⟩ := by simpa [ValidOnFrameClass, ValidOnFrame, ValidOnModel] using not_imp_not.mpr complete! hnp;
  obtain ⟨Fq, _, Vq, hVq, wq, hq⟩ := by simpa [ValidOnFrameClass, ValidOnFrame, ValidOnModel] using not_imp_not.mpr complete! hnq;
  apply (not_imp_not.mpr sound!);

  simp [ValidOnFrameClass, ValidOnFrame, ValidOnModel];
  let M : Model α := IntDPCounterexampleModel ⟨Fp, Vp, hVp⟩ ⟨Fq, Vq, hVq⟩ wp wq;
  existsi M.Frame;
  constructor;
  . apply iff_definability_memAxiomSetFrameClass AxiomSet.EFQ.definability |>.mpr;
    trivial;
  . existsi M.Valuation, M.hereditary, Sum.inl ();
    push_neg;
    constructor;
    . exact not_imp_not.mpr (Satisfies.formula_hereditary (by apply Fp.Rel_refl)) $ satisfies_left_on_IntDPCounterexampleModel.not.mp hp;
    . exact not_imp_not.mpr (Satisfies.formula_hereditary (by apply Fq.Rel_refl)) $ satisfies_right_on_IntDPCounterexampleModel.not.mp hq;

instance : Disjunctive (𝐈𝐧𝐭 : DeductionParameter α) := ⟨disjunctive_int⟩

end Kripke

end LO.Propositional.Superintuitionistic
