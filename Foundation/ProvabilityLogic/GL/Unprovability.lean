import Foundation.Modal.Hilbert.GL.Independency
import Foundation.ProvabilityLogic.GL.Completeness

namespace LO

namespace FirstOrder.DerivabilityCondition

namespace ProvabilityPredicate

open LO.Entailment

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] [DecidableEq (Sentence L)]
         {T₀ T : Theory L} [T₀ ⪯ T]
         {𝔅 : ProvabilityPredicate T₀ T}
         {σ π : Sentence L}

def indep (𝔅 : ProvabilityPredicate T₀ T) (σ : Sentence L) : Sentence L := ∼(𝔅 σ) ⋏ ∼(𝔅 (∼σ))

lemma indep_distribute [𝔅.HBL2] (h : T ⊢!. σ ⭤ π) :
  T ⊢!. 𝔅.indep σ ➝ 𝔅.indep π := by
  apply and_replace!;
  . apply contra₀'!;
    apply WeakerThan.pbl (𝓢 := T₀.alt);
    apply 𝔅.prov_distribute_imply;
    exact and₂'! h;
  . apply contra₀'!;
    apply WeakerThan.pbl (𝓢 := T₀.alt);
    apply 𝔅.prov_distribute_imply;
    apply contra₀'!;
    exact and₁'! h;

lemma indep_iff_distribute_inside [𝔅.HBL2] (h : T ⊢!. σ ⭤ π) :
  T ⊢!. 𝔅.indep σ ⭤ 𝔅.indep π := by
  apply and₃'!
  . exact indep_distribute $ h;
  . apply indep_distribute;
    exact iff_comm'! h;

lemma indep_iff_distribute [𝔅.HBL2] (h : T ⊢!. σ ⭤ π) :
  T ⊢!. 𝔅.indep σ ↔ T ⊢!. 𝔅.indep π := by
  constructor;
  . intro H; exact and₁'! (indep_iff_distribute_inside h) ⨀ H;
  . intro H; exact and₂'! (indep_iff_distribute_inside h) ⨀ H;

end ProvabilityPredicate

end FirstOrder.DerivabilityCondition


namespace ProvabilityLogic

open FirstOrder FirstOrder.Arith FirstOrder.DerivabilityCondition
open Entailment

variable {T : Theory ℒₒᵣ} [T.Delta1Definable]
         {f : Realization ℒₒᵣ}
         {A B : Modal.Formula _}


section Corollary

/-- Gödel's Second Incompleteness Theorem -/
example [𝐈𝚺₁ ⪯ T] [SoundOn T (Hierarchy 𝚷 2)] : T ⊬. ((𝐈𝚺₁).standardDP T).con := by
  have h := GL.arithmetical_completeness_iff (T := T) |>.not.mpr $ Modal.Hilbert.GL.unprovable_notbox (φ := ⊥);
  push_neg at h;
  obtain ⟨f, h⟩ := h;
  exact Realization.iff_interpret_neg.not.mp h;

end Corollary


section Independency

lemma iff_modalConsis_bewConsis_inside
  : T ⊢!. f.interpret (𝐈𝚺₁.standardDP T) (∼□⊥) ⭤ (𝐈𝚺₁.standardDP T).con := by
  apply and₃'!;
  . refine imp_trans''! (and₁'! Realization.iff_interpret_neg_inside) ?_;
    apply contra₀'!;
    simp [Realization.interpret];
  . refine imp_trans''! ?_ (and₂'! Realization.iff_interpret_neg_inside)
    apply contra₀'!;
    simp [Realization.interpret];

variable [𝐈𝚺₁ ⪯ T]

lemma iff_modalIndep_bewIndep_inside :
  T ⊢!. f.interpret ((𝐈𝚺₁).standardDP T) (Modal.independency A) ⭤ ((𝐈𝚺₁).standardDP T).indep (f.interpret ((𝐈𝚺₁).standardDP T) A)
  := by
  apply and₃'!;
  . refine imp_trans''! (and₁'! $ Realization.iff_interpret_and_inside) ?_;
    apply and_replace!;
    . apply and₁'! Realization.iff_interpret_neg_inside;
    . apply imp_trans''! (and₁'! $ Realization.iff_interpret_neg_inside (A := □(∼A))) ?_;
      apply contra₀'!;
      apply WeakerThan.pbl (𝓢 := 𝐈𝚺₁.alt);
      apply ((𝐈𝚺₁).standardDP T).prov_distribute_imply;
      apply and₂'! $ Realization.iff_interpret_neg_inside;
  . refine imp_trans''! ?_ (and₂'! $ Realization.iff_interpret_and_inside);
    apply and_replace!;
    . exact imp_trans''! (and₂'! $ Realization.iff_interpret_neg_inside (A := □A)) imp_id!;
    . apply imp_trans''! ?_ (and₂'! $ Realization.iff_interpret_neg_inside (A := □(∼A)));
      apply contra₀'!;
      apply WeakerThan.pbl (𝓢 := 𝐈𝚺₁.alt);
      apply ((𝐈𝚺₁).standardDP T).prov_distribute_imply;
      apply and₁'! $ Realization.iff_interpret_neg_inside;

lemma iff_modalIndep_bewIndep :
  T ⊢!. f.interpret ((𝐈𝚺₁).standardDP T) (Modal.independency A) ↔ T ⊢!. ((𝐈𝚺₁).standardDP T).indep (f.interpret ((𝐈𝚺₁).standardDP T) A)
  := by
  constructor;
  . intro h; exact (and₁'! iff_modalIndep_bewIndep_inside) ⨀ h;
  . intro h; exact (and₂'! iff_modalIndep_bewIndep_inside) ⨀ h;

lemma iff_not_modalIndep_not_bewIndep_inside :
  T ⊢!. ∼f.interpret ((𝐈𝚺₁).standardDP T) (Modal.independency A) ⭤ ∼((𝐈𝚺₁).standardDP T).indep (f.interpret ((𝐈𝚺₁).standardDP T) A)
  := neg_replace_iff'! iff_modalIndep_bewIndep_inside

lemma iff_not_modalIndep_not_bewIndep :
  T ⊢!. ∼f.interpret ((𝐈𝚺₁).standardDP T) (Modal.independency A) ↔ T ⊢!. ∼((𝐈𝚺₁).standardDP T).indep (f.interpret ((𝐈𝚺₁).standardDP T) A)
  := by
  constructor;
  . intro h; exact (and₁'! iff_not_modalIndep_not_bewIndep_inside) ⨀ h;
  . intro h; exact (and₂'! iff_not_modalIndep_not_bewIndep_inside) ⨀ h;

variable [SoundOn T (Hierarchy 𝚷 2)]

lemma unprovable_independency_of_consistency :
  T ⊬. ((𝐈𝚺₁).standardDP T).indep (((𝐈𝚺₁).standardDP T).con) := by
  let g : Realization ℒₒᵣ := λ _ => ⊥;
  suffices T ⊬. g.interpret (𝐈𝚺₁.standardDP T) (Modal.independency (∼□⊥)) by
    have H₁ := iff_modalIndep_bewIndep (f := g) (T := T) (A := ∼□⊥);
    have H₂ := ((𝐈𝚺₁).standardDP T).indep_iff_distribute (T := T)
      (σ := g.interpret (𝐈𝚺₁.standardDP T) (∼□⊥))
      (π := (𝐈𝚺₁.standardDP T).con)
      iff_modalConsis_bewConsis_inside;
    exact Iff.trans H₁ H₂ |>.not.mp this;
  have h := Modal.Hilbert.GL.unprovable_independency (φ := ∼□⊥);
  replace h := GL.arithmetical_completeness_iff (T := T) |>.not.mpr h;
  push_neg at h;
  obtain ⟨f, h⟩ := h;
  congr;

lemma unrefutable_independency_of_consistency :
  T ⊬. ∼((𝐈𝚺₁).standardDP T).indep (((𝐈𝚺₁).standardDP T).con) := by
  let g : Realization ℒₒᵣ := λ _ => ⊥;
  suffices T ⊬. ∼g.interpret (𝐈𝚺₁.standardDP T) (Modal.independency (∼□⊥)) by
    have H₁ := iff_not_modalIndep_not_bewIndep (f := g) (T := T) (A := ∼□⊥);
    have H₂ : T ⊢!.
      ∼(𝐈𝚺₁.standardDP T).indep (g.interpret (𝐈𝚺₁.standardDP T) (∼□⊥)) ⭤
      ∼(𝐈𝚺₁.standardDP T).indep (𝐈𝚺₁.standardDP T).con
      := neg_replace_iff'! $ ((𝐈𝚺₁).standardDP T).indep_iff_distribute_inside (T := T)
      (σ := g.interpret (𝐈𝚺₁.standardDP T) (∼□⊥))
      (π := (𝐈𝚺₁.standardDP T).con)
      iff_modalConsis_bewConsis_inside;
    replace H₂ :
      T ⊢!. ∼(𝐈𝚺₁.standardDP T).indep (g.interpret (𝐈𝚺₁.standardDP T) (∼□⊥)) ↔
      T ⊢!. ∼(𝐈𝚺₁.standardDP T).indep (𝐈𝚺₁.standardDP T).con
      := by
      constructor;
      . intro H; exact and₁'! H₂ ⨀ H;
      . intro H; exact and₂'! H₂ ⨀ H;
    apply Iff.trans H₁ H₂ |>.not.mp this;
  have h := Modal.Hilbert.GL.unprovable_not_independency_of_consistency;
  replace h := GL.arithmetical_completeness_iff (T := T) |>.not.mpr h;
  push_neg at h;
  obtain ⟨f, h⟩ := h;
  replace h := Realization.iff_interpret_neg.not.mp h;
  congr;

theorem undecidable_independency_of_consistency :
  Undecidable T.alt (((𝐈𝚺₁).standardDP T).indep (((𝐈𝚺₁).standardDP T).con)) := by
  constructor;
  . exact unprovable_independency_of_consistency;
  . exact unrefutable_independency_of_consistency;

end Independency


end LO.ProvabilityLogic
