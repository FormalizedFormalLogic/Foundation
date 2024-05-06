import Logic.Propositional.Superintuitionistic.Kripke.Soundness
import Logic.Propositional.Superintuitionistic.Kripke.Completeness

namespace LO.System

variable {F : Type*} [Vee F]
variable {S : Type*} [System F S]

class Disjunctive (𝓢 : S) : Prop where
  disjunctive : ∀ {p q}, 𝓢 ⊢! p ⋎ q → 𝓢 ⊢! p ∨ 𝓢 ⊢! q

end LO.System


namespace LO.Propositional.Superintuitionistic

open System
open Formula Formula.Kripke

namespace Kripke

variable {α} [DecidableEq α]
variable {p q : Formula α}

def IntDPCounterexampleModel (M₁ : Model (𝐈𝐧𝐭 W₁ α)) (M₂ : Model (𝐈𝐧𝐭 W₂ α)) (w₁ : W₁) (w₂ : W₂) : Model (𝐈𝐧𝐭 (Unit ⊕ W₁ ⊕ W₂) α) where
  frame w v :=
    match w, v with
    | (Sum.inl _), (Sum.inl _) => True
    | (Sum.inl _), (Sum.inr $ Sum.inl v) => M₁.frame w₁ v
    | (Sum.inl _), (Sum.inr $ Sum.inr v) => M₂.frame w₂ v
    | (Sum.inr $ Sum.inl w), (Sum.inr $ Sum.inl v) => M₁.frame w v
    | (Sum.inr $ Sum.inr w), (Sum.inr $ Sum.inr v) => M₂.frame w v
    | _, _ => False
  valuation w a :=
    match w with
    | Sum.inr $ Sum.inl w => M₁.valuation w a
    | Sum.inr $ Sum.inr w => M₂.valuation w a
    | _ => False
  hereditary := by
    simp only [Sum.forall, imp_false, not_false_eq_true, implies_true, forall_true_left, forall_const, IsEmpty.forall_iff, and_self, true_and, and_true];
    constructor;
    . intro _ _; apply M₁.hereditary;
    . intro _ _; apply M₂.hereditary;
  frame_prop := by
    constructor;
    . simp only [Transitive, Sum.forall, forall_true_left, imp_self, forall_const, true_and, IsEmpty.forall_iff, implies_true, and_true, and_self, imp_false];
      constructor;
      . constructor;
        . intro _ _; apply M₁.frame_prop.1;
        . intro _ _; apply M₂.frame_prop.1;
      . constructor;
        . intro _ _; apply M₁.frame_prop.1;
        . intro _ _; apply M₂.frame_prop.1;
    . simp only [Reflexive, Sum.forall, forall_const, true_and];
      constructor;
      . intros; apply M₁.frame_prop.2;
      . intros; apply M₂.frame_prop.2;

variable {M₁ : Model (𝐈𝐧𝐭 W₁ α)} {M₂ : Model (𝐈𝐧𝐭 W₂ α)}

lemma satisfies_left_on_IntDPCounterexampleModel : ((M₁, w) ⊧ p) ↔ ((IntDPCounterexampleModel M₁ M₂ w₁ w₂, (Sum.inr $ Sum.inl w : (Unit ⊕ W₁ ⊕ W₂))) ⊧ p) := by
  induction p using rec' generalizing w with
  | himp p q ihp ihq =>
    constructor;
    . simp only [Satisfies.imp_def];
      intro h v hv hp;
      replace ⟨v, hv, hv'⟩ : ∃ v', M₁.frame w v' ∧ v = (Sum.inr (Sum.inl v')) := by
        simp [IntDPCounterexampleModel] at hv;
        split at hv;
        all_goals simp_all;
      subst hv';
      exact ihq.mp $ h hv $ ihp.mpr hp;
    . simp only [Satisfies.imp_def];
      intro h v hv hp;
      exact ihq.mpr $ h (by simpa [IntDPCounterexampleModel]) $ ihp.mp hp;
  | _ => simp_all [IntDPCounterexampleModel, Satisfies.iff_models, Satisfies];

lemma satisfies_right_on_IntDPCounterexampleModel : ((M₂, w) ⊧ p) ↔ ((IntDPCounterexampleModel M₁ M₂ w₁ w₂, (Sum.inr $ Sum.inr w : (Unit ⊕ W₁ ⊕ W₂))) ⊧ p) := by
  induction p using rec' generalizing w with
  | himp p q ihp ihq =>
    constructor;
    . simp only [Satisfies.imp_def];
      intro h v hv hp;
      replace ⟨v, hv, hv'⟩ : ∃ v', M₂.frame w v' ∧ v = (Sum.inr (Sum.inr v')) := by
        simp [IntDPCounterexampleModel] at hv;
        split at hv;
        all_goals simp_all;
      subst hv';
      exact ihq.mp $ h hv $ ihp.mpr hp;
    . simp only [Satisfies.imp_def];
      intro h v hv hp;
      exact ihq.mpr $ h (by simpa [IntDPCounterexampleModel]) $ ihp.mp hp;
  | _ => simp_all [IntDPCounterexampleModel, Satisfies.iff_models, Satisfies];


theorem disjunctive_int : 𝐄𝐅𝐐 ⊢! p ⋎ q → (𝐄𝐅𝐐 ⊢! p ∨ 𝐄𝐅𝐐 ⊢! q) := by
  contrapose;
  intro hC; simp [not_or] at hC;
  have ⟨hnp, hnq⟩ := hC;
  obtain ⟨Mp, wp, hp⟩ := by simpa [ValidOnFrameClass.iff_models, ValidOnFrameClass, ValidOnModel.iff_models, ValidOnModel] using (not_imp_not.mpr complete!) hnp;
  obtain ⟨Mq, wq, hq⟩ := by simpa [ValidOnFrameClass.iff_models, ValidOnFrameClass, ValidOnModel.iff_models, ValidOnModel] using (not_imp_not.mpr complete!) hnq;
  apply (not_imp_not.mpr sound!);
  simp [ValidOnFrameClass.iff_models, ValidOnFrameClass, ValidOnModel.iff_models, ValidOnModel];

  let M := IntDPCounterexampleModel Mp Mq wp wq;
  existsi M, Sum.inl ();

  have hup : M.frame (Sum.inl ()) (Sum.inr $ Sum.inl wp) := by
    simp [M, IntDPCounterexampleModel];
    apply Mp.frame_prop.2;

  have huq : M.frame (Sum.inl ()) (Sum.inr $ Sum.inr wq) := by
    simp [M, IntDPCounterexampleModel];
    apply Mq.frame_prop.2;

  have : ¬(M, Sum.inl ()) ⊧ p := not_imp_not.mpr (Satisfies.hereditary (by simp_all) hup) $ satisfies_left_on_IntDPCounterexampleModel.not.mp hp;
  have : ¬(M, Sum.inl ()) ⊧ q := not_imp_not.mpr (Satisfies.hereditary (by simp_all) huq) $ satisfies_right_on_IntDPCounterexampleModel.not.mp hq;

  simp_all;

instance : Disjunctive (𝐄𝐅𝐐 : AxiomSet α) := ⟨disjunctive_int⟩

end Kripke

end LO.Propositional.Superintuitionistic
