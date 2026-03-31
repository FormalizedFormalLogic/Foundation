module

public import Foundation.Modal.Logic.GL.Independency
public import Foundation.ProvabilityLogic.GL.Completeness

@[expose] public section
namespace LO.FirstOrder

open LO.Entailment

namespace ProvabilityAbstraction

variable {L : Language} [L.ReferenceableBy L] [DecidableEq (Sentence L)]
         {T₀ T : Theory L} [T₀ ⪯ T]
         {𝔅 : Provability T₀ T}
         {σ π : Sentence L}

def Provability.indep (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L := ∼(𝔅 σ) ⋏ ∼(𝔅 (∼σ))

lemma indep_distribute [𝔅.HBL2] (h : T ⊢ σ 🡘 π) : T ⊢ 𝔅.indep σ 🡒 𝔅.indep π := by
  apply CKK!_of_C!_of_C!;
  . apply contra!;
    apply WeakerThan.pbl (𝓢 := T₀);
    apply 𝔅.mono;
    cl_prover [h];
  . apply contra!;
    apply WeakerThan.pbl (𝓢 := T₀);
    apply 𝔅.mono;
    cl_prover [h];

lemma indep_iff_distribute_inside [𝔅.HBL2] (h : T ⊢ σ 🡘 π) :
    T ⊢ 𝔅.indep σ 🡘 𝔅.indep π := by
  apply K!_intro
  . exact indep_distribute $ h;
  . apply indep_distribute;
    cl_prover [h];

lemma indep_iff_distribute [𝔅.HBL2] (h : T ⊢ σ 🡘 π) :
    T ⊢ 𝔅.indep σ ↔ T ⊢ 𝔅.indep π := by
  constructor;
  . intro H; exact K!_left (indep_iff_distribute_inside h) ⨀ H;
  . intro H; exact K!_right (indep_iff_distribute_inside h) ⨀ H;

end ProvabilityAbstraction


namespace Arithmetic

open Modal ProvabilityLogic
open ProvabilityAbstraction

variable {T : ArithmeticTheory} [T.Δ₁]
         {σ π : Sentence L}
         {f : T.StandardRealization}
         {A B : Modal.Formula _}

example [𝗜𝚺₁ ⪯ T] (height : T.height = ⊤) : T ⊬ T.standardProvability.con := by
  have h := ProvabilityLogic.GL.arithmetical_completeness_iff height (T := T) |>.not.mpr $ GL.unprovable_notbox (φ := ⊥);
  push_neg at h;
  obtain ⟨f, h⟩ := h;
  exact Realization.interpret.iff_provable_neg (f := f) |>.not.mp h;

lemma iff_modalConsis_bewConsis_inside : T ⊢ f (∼□⊥) 🡘 T.standardProvability.con := by
  apply K!_intro;
  . refine C!_trans (K!_left Realization.interpret.iff_provable_neg_inside) ?_;
    apply contra!;
    simp [Realization.interpret];
  . refine C!_trans ?_ (K!_right Realization.interpret.iff_provable_neg_inside)
    apply contra!;
    simp [Realization.interpret];

variable [𝗜𝚺₁ ⪯ T]

lemma iff_modalIndep_bewIndep_inside :
    T ⊢ f (Modal.independency A) 🡘 T.standardProvability.indep (f A) := by
  apply K!_intro;
  . refine C!_trans (K!_left $ Realization.interpret.iff_provable_and_inside) ?_;
    apply CKK!_of_C!_of_C!;
    . apply K!_left $ Realization.interpret.iff_provable_neg_inside (L := ℒₒᵣ);
    . apply C!_trans (K!_left $ Realization.interpret.iff_provable_neg_inside (L := ℒₒᵣ) (A := □(∼A))) ?_;
      apply contra!;
      apply WeakerThan.pbl (𝓢 := 𝗜𝚺₁);
      apply T.standardProvability.mono;
      apply K!_right $ Realization.interpret.iff_provable_neg_inside (L := ℒₒᵣ) ;
  . refine C!_trans ?_ (K!_right $ Realization.interpret.iff_provable_and_inside);
    apply CKK!_of_C!_of_C!;
    . exact C!_trans (K!_right $ Realization.interpret.iff_provable_neg_inside (A := □A)) C!_id;
    . apply C!_trans ?_ (K!_right $ Realization.interpret.iff_provable_neg_inside (L := ℒₒᵣ) (A := □(∼A)));
      apply contra!;
      apply WeakerThan.pbl (𝓢 := 𝗜𝚺₁);
      apply T.standardProvability.mono;
      apply K!_left $ Realization.interpret.iff_provable_neg_inside (L := ℒₒᵣ);

lemma iff_modalIndep_bewIndep :
    T ⊢ f (Modal.independency A) ↔ T ⊢ T.standardProvability.indep (f A) := by
  constructor;
  . intro h; exact (K!_left iff_modalIndep_bewIndep_inside) ⨀ h;
  . intro h; exact (K!_right iff_modalIndep_bewIndep_inside) ⨀ h;

lemma iff_not_modalIndep_not_bewIndep_inside :
    T ⊢ ∼f (Modal.independency A) 🡘 ∼T.standardProvability.indep (f A) :=
  ENN!_of_E! iff_modalIndep_bewIndep_inside

lemma iff_not_modalIndep_not_bewIndep :
    T ⊢ ∼f (Modal.independency A) ↔ T ⊢ ∼T.standardProvability.indep (f A) := by
  constructor;
  . intro h; exact (K!_left iff_not_modalIndep_not_bewIndep_inside) ⨀ h;
  . intro h; exact (K!_right iff_not_modalIndep_not_bewIndep_inside) ⨀ h;

lemma unprovable_independency_of_consistency (height : T.height = ⊤) :
    T ⊬ T.standardProvability.indep (T.standardProvability.con) := by
  let g : T.StandardRealization := ⟨λ _ => ⊥⟩
  suffices T ⊬ g (Modal.independency (∼□⊥)) by
    have H₁ := iff_modalIndep_bewIndep (f := g) (T := T) (A := ∼□⊥);
    have H₂ := indep_iff_distribute (𝔅 := T.standardProvability) (T := T)
      (σ := g (∼□⊥))
      (π := T.standardProvability.con)
      iff_modalConsis_bewConsis_inside;
    exact Iff.trans H₁ H₂ |>.not.mp this;
  have h := GL.arithmetical_completeness_iff height |>.not.mpr $ GL.unprovable_independency (φ := ∼□⊥);
  push_neg at h;
  obtain ⟨f, h⟩ := h;
  congr;

lemma unrefutable_independency_of_consistency (height : T.height = ⊤):
    T ⊬ ∼T.standardProvability.indep (T.standardProvability.con) := by
  let g : T.StandardRealization := ⟨λ _ => ⊥⟩
  suffices T ⊬ ∼g (Modal.independency (∼□⊥)) by
    have H₁ := iff_not_modalIndep_not_bewIndep (f := g) (T := T) (A := ∼□⊥);
    have H₂ : T ⊢
      ∼T.standardProvability.indep (g (∼□⊥)) 🡘
      ∼T.standardProvability.indep T.standardProvability.con
      := ENN!_of_E! $ indep_iff_distribute_inside (T := T)
      (σ := g (∼□⊥))
      (π := T.standardProvability.con)
      iff_modalConsis_bewConsis_inside;
    replace H₂ :
      T ⊢ ∼T.standardProvability.indep (g (∼□⊥)) ↔
      T ⊢ ∼T.standardProvability.indep T.standardProvability.con
      := by
      constructor;
      . intro H; exact K!_left H₂ ⨀ H;
      . intro H; exact K!_right H₂ ⨀ H;
    apply Iff.trans H₁ H₂ |>.not.mp this;
  have h := GL.arithmetical_completeness_iff height |>.not.mpr $ GL.unprovable_not_independency_of_consistency;
  push_neg at h;
  obtain ⟨f, h⟩ := h;
  replace h := Realization.interpret.iff_provable_neg (L := ℒₒᵣ) |>.not.mp h;
  congr;

theorem undecidable_independency_of_consistency (height : T.height = ⊤) :
    Independent T (T.standardProvability.indep T.standardProvability.con) := by
  constructor;
  . exact unprovable_independency_of_consistency height;
  . exact unrefutable_independency_of_consistency height;

end Arithmetic

end LO.FirstOrder
