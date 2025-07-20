import Foundation.Modal.Logic.GL.Independency
import Foundation.ProvabilityLogic.GL.Completeness

namespace LO.ProvabilityLogic

open Modal.Logic FirstOrder

namespace Provability

open LO.Entailment

variable {L : Language} [L.DecidableEq] [L.ReferenceableBy L] [DecidableEq (Sentence L)]
         {T₀ T : Theory L} [T₀ ⪯ T]
         {𝔅 : Provability T₀ T}
         {σ π : Sentence L}

def indep (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L := ∼(𝔅 σ) ⋏ ∼(𝔅 (∼σ))

lemma indep_distribute [𝔅.HBL2] (h : T ⊢!. σ ⭤ π) :
    T ⊢!. 𝔅.indep σ ➝ 𝔅.indep π := by
  apply CKK!_of_C!_of_C!;
  . apply contra!;
    apply WeakerThan.pbl (𝓢 := T₀.toAxiom);
    apply 𝔅.prov_distribute_imply;
    exact K!_right h;
  . apply contra!;
    apply WeakerThan.pbl (𝓢 := T₀.toAxiom);
    apply 𝔅.prov_distribute_imply;
    apply contra!;
    exact K!_left h;

lemma indep_iff_distribute_inside [𝔅.HBL2] (h : T ⊢!. σ ⭤ π) :
    T ⊢!. 𝔅.indep σ ⭤ 𝔅.indep π := by
  apply K!_intro
  . exact indep_distribute $ h;
  . apply indep_distribute;
    exact E!_symm h;

lemma indep_iff_distribute [𝔅.HBL2] (h : T ⊢!. σ ⭤ π) :
    T ⊢!. 𝔅.indep σ ↔ T ⊢!. 𝔅.indep π := by
  constructor;
  . intro H; exact K!_left (indep_iff_distribute_inside h) ⨀ H;
  . intro H; exact K!_right (indep_iff_distribute_inside h) ⨀ H;

end Provability

end ProvabilityLogic


namespace ProvabilityLogic

open FirstOrder FirstOrder.Arithmetic
open Modal Logic
open Entailment

variable {T : ArithmeticTheory} [T.Δ₁]
         {f : Realization ℒₒᵣ}
         {A B : Modal.Formula _}


section Corollary

/-- Gödel's Second Incompleteness Theorem -/
example [𝐈𝚺₁ ⪯ T] [T.SoundOn (Hierarchy 𝚷 2)] : T ⊬. T.standardProvability.con := by
  have h := GL.arithmetical_completeness_iff (T := T) |>.not.mpr $ GL.unprovable_notbox (φ := ⊥);
  push_neg at h;
  obtain ⟨f, h⟩ := h;
  exact Realization.iff_interpret_neg.not.mp h;

end Corollary

section Independency

lemma iff_modalConsis_bewConsis_inside :
    T ⊢!. f.interpret T.standardProvability (∼□⊥) ⭤ T.standardProvability.con := by
  apply K!_intro;
  . refine C!_trans (K!_left Realization.iff_interpret_neg_inside) ?_;
    apply contra!;
    simp [Realization.interpret];
  . refine C!_trans ?_ (K!_right Realization.iff_interpret_neg_inside)
    apply contra!;
    simp [Realization.interpret];

variable [𝐈𝚺₁ ⪯ T]

lemma iff_modalIndep_bewIndep_inside :
    T ⊢!. f.interpret T.standardProvability (Modal.independency A) ⭤ T.standardProvability.indep (f.interpret T.standardProvability A) := by
  apply K!_intro;
  . refine C!_trans (K!_left $ Realization.iff_interpret_and_inside) ?_;
    apply CKK!_of_C!_of_C!;
    . apply K!_left Realization.iff_interpret_neg_inside;
    . apply C!_trans (K!_left $ Realization.iff_interpret_neg_inside (A := □(∼A))) ?_;
      apply contra!;
      apply WeakerThan.pbl (𝓢 := 𝐈𝚺₁.toAxiom);
      apply T.standardProvability.prov_distribute_imply;
      apply K!_right $ Realization.iff_interpret_neg_inside;
  . refine C!_trans ?_ (K!_right $ Realization.iff_interpret_and_inside);
    apply CKK!_of_C!_of_C!;
    . exact C!_trans (K!_right $ Realization.iff_interpret_neg_inside (A := □A)) C!_id;
    . apply C!_trans ?_ (K!_right $ Realization.iff_interpret_neg_inside (A := □(∼A)));
      apply contra!;
      apply WeakerThan.pbl (𝓢 := 𝐈𝚺₁.toAxiom);
      apply T.standardProvability.prov_distribute_imply;
      apply K!_left $ Realization.iff_interpret_neg_inside;

lemma iff_modalIndep_bewIndep :
    T ⊢!. f.interpret T.standardProvability (Modal.independency A) ↔ T ⊢!. T.standardProvability.indep (f.interpret T.standardProvability A) := by
  constructor;
  . intro h; exact (K!_left iff_modalIndep_bewIndep_inside) ⨀ h;
  . intro h; exact (K!_right iff_modalIndep_bewIndep_inside) ⨀ h;

lemma iff_not_modalIndep_not_bewIndep_inside :
    T ⊢!. ∼f.interpret T.standardProvability (Modal.independency A) ⭤ ∼T.standardProvability.indep (f.interpret T.standardProvability A) :=
  ENN!_of_E! iff_modalIndep_bewIndep_inside

lemma iff_not_modalIndep_not_bewIndep :
    T ⊢!. ∼f.interpret T.standardProvability (Modal.independency A) ↔ T ⊢!. ∼T.standardProvability.indep (f.interpret T.standardProvability A) := by
  constructor;
  . intro h; exact (K!_left iff_not_modalIndep_not_bewIndep_inside) ⨀ h;
  . intro h; exact (K!_right iff_not_modalIndep_not_bewIndep_inside) ⨀ h;

variable [T.SoundOn (Hierarchy 𝚷 2)]

lemma unprovable_independency_of_consistency :
    T ⊬. T.standardProvability.indep (T.standardProvability.con) := by
  let g : Realization ℒₒᵣ := λ _ => ⊥;
  suffices T ⊬. g.interpret T.standardProvability (Modal.independency (∼□⊥)) by
    have H₁ := iff_modalIndep_bewIndep (f := g) (T := T) (A := ∼□⊥);
    have H₂ := T.standardProvability.indep_iff_distribute (T := T)
      (σ := g.interpret T.standardProvability (∼□⊥))
      (π := T.standardProvability.con)
      iff_modalConsis_bewConsis_inside;
    exact Iff.trans H₁ H₂ |>.not.mp this;
  have h := GL.arithmetical_completeness_iff (T := T) |>.not.mpr $ GL.unprovable_independency (φ := ∼□⊥);
  push_neg at h;
  obtain ⟨f, h⟩ := h;
  congr;

lemma unrefutable_independency_of_consistency :
    T ⊬. ∼T.standardProvability.indep (T.standardProvability.con) := by
  let g : Realization ℒₒᵣ := λ _ => ⊥;
  suffices T ⊬. ∼g.interpret T.standardProvability (Modal.independency (∼□⊥)) by
    have H₁ := iff_not_modalIndep_not_bewIndep (f := g) (T := T) (A := ∼□⊥);
    have H₂ : T ⊢!.
      ∼T.standardProvability.indep (g.interpret T.standardProvability (∼□⊥)) ⭤
      ∼T.standardProvability.indep T.standardProvability.con
      := ENN!_of_E! $ T.standardProvability.indep_iff_distribute_inside (T := T)
      (σ := g.interpret T.standardProvability (∼□⊥))
      (π := T.standardProvability.con)
      iff_modalConsis_bewConsis_inside;
    replace H₂ :
      T ⊢!. ∼T.standardProvability.indep (g.interpret T.standardProvability (∼□⊥)) ↔
      T ⊢!. ∼T.standardProvability.indep T.standardProvability.con
      := by
      constructor;
      . intro H; exact K!_left H₂ ⨀ H;
      . intro H; exact K!_right H₂ ⨀ H;
    apply Iff.trans H₁ H₂ |>.not.mp this;
  have h := GL.arithmetical_completeness_iff (T := T) |>.not.mpr $ GL.unprovable_not_independency_of_consistency;
  push_neg at h;
  obtain ⟨f, h⟩ := h;
  replace h := Realization.iff_interpret_neg.not.mp h;
  congr;

theorem undecidable_independency_of_consistency :
    Independent T.toAxiom (T.standardProvability.indep (T.standardProvability.con)) := by
  constructor;
  . exact unprovable_independency_of_consistency;
  . exact unrefutable_independency_of_consistency;

end Independency


end LO.ProvabilityLogic
