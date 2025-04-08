import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.ProvabilityLogic.Grz.Completeness
import Foundation.Modal.Hilbert.GL.Independency

namespace LO


namespace Entailment

open Entailment
open FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Classical 𝓢]
         {φ ψ χ ξ : F}

lemma IIIpIqbb_Apq (h : 𝓢 ⊢! ((φ ➝ (ψ ➝ ⊥)) ➝ ⊥)) : 𝓢 ⊢! (φ ⋏ ψ) := IIIpIqbbApq ⨀ h

end Entailment


namespace FirstOrder.DerivabilityCondition

namespace ProvabilityPredicate

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] -- [DecidableEq (Sentence L)]
         {T₀ T : Theory L} -- [T₀ ⪯ T]

def indep (𝔅 : ProvabilityPredicate T₀ T) (σ : Sentence L) : Sentence L := ∼(𝔅 σ) ⋏ ∼(𝔅 (∼σ))

end ProvabilityPredicate

end FirstOrder.DerivabilityCondition


namespace ProvabilityLogic

namespace Realization

open FirstOrder FirstOrder.DerivabilityCondition
open Modal
open Modal.Hilbert
open FirstOrder
open Entailment FiniteContext

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] -- [DecidableEq (Sentence L)]
         {T₀ T : Theory L} -- [T₀ ⪯ T]
         {𝔅 : ProvabilityPredicate T₀ T} {f : Realization L} {A B : Modal.Formula _}

lemma iff_interpret_atom : T ⊢!. f.interpret 𝔅 (.atom a) ↔ T ⊢!. f a := by  simp [Realization.interpret];
lemma iff_interpret_imp : T ⊢!. f.interpret 𝔅 (A ➝ B) ↔ T ⊢!. (f.interpret 𝔅 A) ➝ (f.interpret 𝔅 B) := by simp [Realization.interpret];
lemma iff_interpret_bot : T ⊢!. f.interpret 𝔅 ⊥ ↔ T ⊢!. ⊥ := by simp [Realization.interpret];
lemma iff_interpret_box : T ⊢!. f.interpret 𝔅 (□A) ↔ T ⊢!. 𝔅 (f.interpret 𝔅 A) := by simp [Realization.interpret];
lemma iff_interpret_neg : T ⊢!. f.interpret 𝔅 (∼A) ↔ T ⊢!. ∼(f.interpret 𝔅 A) := by
  dsimp [Realization.interpret];
  apply neg_equiv'!.symm;

lemma iff_interpret_neg_inside : T ⊢!. f.interpret 𝔅 (∼A) ⭤ ∼(f.interpret 𝔅 A) := by
  dsimp [Realization.interpret];
  apply and₃'!;
  . apply and₂'! $ neg_equiv!
  . apply and₁'! $ neg_equiv!

variable [DecidableEq (Sentence L)]

lemma iff_interpret_or : T ⊢!. f.interpret 𝔅 (A ⋎ B) ↔ T ⊢!. (f.interpret 𝔅 A) ⋎ (f.interpret 𝔅 B) := by
  constructor;
  . intro h;
    sorry;
  . intro h;
    sorry;

lemma iff_interpret_and : T ⊢!. f.interpret 𝔅 (A ⋏ B) ↔ T ⊢!. (f.interpret 𝔅 A) ⋏ (f.interpret 𝔅 B) := by
  constructor;
  . intro h; apply IIIpIqbb_Apq h;
  . intro h; apply Apq_IIpIqbb h;

lemma iff_interpret_and' : T ⊢!. f.interpret 𝔅 (A ⋏ B) ↔ T ⊢!. (f.interpret 𝔅 A) ∧ T ⊢!. (f.interpret 𝔅 B) := by
  apply Iff.trans iff_interpret_and;
  constructor;
  . intro h;
    constructor;
    . apply and₁'! h;
    . apply and₂'! h;
  . rintro ⟨_, _⟩;
    apply and₃'! <;> assumption;

-- def letterless_interpret (𝔅 : ProvabilityPredicate T₀ T) (A : Modal.Formula ℕ) : Sentence L := Realization.interpret (λ _ => ⊥) 𝔅 A

omit [DecidableEq (Sentence L)] in
lemma letterless_interpret
  {f₁ f₂ : Realization L} (A_letterless : A.letterless)
  : (f₁.interpret 𝔅 A) = (f₂.interpret 𝔅 A) := by
  induction A using Formula.rec' with
  | hatom a => simp at A_letterless;
  | hfalsum => simp_all [Realization.interpret];
  | himp A B ihA ihB =>
    replace ihA := ihA $ Modal.Formula.letterless.def_imp₁ A_letterless;
    replace ihB := ihB $ Modal.Formula.letterless.def_imp₂ A_letterless;
    simp_all [Realization.interpret];
  | hbox A ihA =>
    replace ihA := ihA $ Modal.Formula.letterless.def_box A_letterless;
    simp_all [Realization.interpret];

end Realization



open FirstOrder FirstOrder.Arith FirstOrder.DerivabilityCondition
open Entailment

variable {T : Theory ℒₒᵣ} [T.Delta1Definable] [𝐈𝚺₁ ⪯ T] [SoundOn T (Hierarchy 𝚷 2)]
         {f : Realization ℒₒᵣ} {σ π : Sentence ℒₒᵣ}
         {A B : Modal.Formula _}

lemma second :
  letI 𝔅 := (𝐈𝚺₁).standardDP T
  T ⊬. 𝔅.con := by
  have h := arithmetical_completeness_GL_iff (T := T) |>.not.mpr $ Modal.Hilbert.GL.unprovable_notbox (φ := ⊥);
  push_neg at h;
  obtain ⟨f, h⟩ := h;
  exact Realization.iff_interpret_neg.not.mp h;

omit [SoundOn T (Hierarchy 𝚷 2)] in
lemma iff_modalIndep_bewIndep :
  letI 𝔅 := (𝐈𝚺₁).standardDP T
  T ⊢!. f.interpret 𝔅 (Modal.independency A) ↔ T ⊢!. 𝔅.indep (f.interpret 𝔅 A) := by
  have H : T ⊢!. ∼((𝐈𝚺₁).standardDP T) (∼f.interpret ((𝐈𝚺₁).standardDP T) A) ⭤ ∼f.interpret ((𝐈𝚺₁).standardDP T) (□(∼A)) := by
    apply neg_replace_iff'!;
    apply WeakerThan.pbl (𝓢 := 𝐈𝚺₁.alt);
    apply ((𝐈𝚺₁).standardDP T).prov_distribute_iff;
    apply iff_comm'!;
    apply Realization.iff_interpret_neg_inside;
  constructor;
  . intro h;
    replace h := Realization.iff_interpret_and (L := ℒₒᵣ).mp h;
    apply and₃'!;
    . replace h := and₁'! h;
      exact Realization.iff_interpret_neg.mp h;
    . replace h := and₂'! h;
      have := Realization.iff_interpret_neg.mp h;
      exact (and₂'! H) ⨀ this;
  . intro h;
    apply Realization.iff_interpret_and (L := ℒₒᵣ).mpr;
    apply and₃'!;
    . apply Realization.iff_interpret_neg.mpr; exact and₁'! h;
    . apply Realization.iff_interpret_neg.mpr;
      exact (and₁'! H) ⨀ (and₂'! h);

omit [SoundOn T (Hierarchy 𝚷 2)] in
lemma indep_distribute (h : T ⊢!. σ ⭤ π) :
  letI 𝔅 := (𝐈𝚺₁).standardDP T
  T ⊢!. 𝔅.indep σ ➝ 𝔅.indep π := by
  apply and_replace!;
  . apply contra₀'!;
    apply WeakerThan.pbl (𝓢 := 𝐈𝚺₁.alt);
    apply ((𝐈𝚺₁).standardDP T).prov_distribute_imply;
    exact and₂'! h;
  . apply contra₀'!;
    apply WeakerThan.pbl (𝓢 := 𝐈𝚺₁.alt);
    apply ((𝐈𝚺₁).standardDP T).prov_distribute_imply;
    apply contra₀'!;
    exact and₁'! h;

omit [SoundOn T (Hierarchy 𝚷 2)] in
lemma indep_iff_distribute_inside (h : T ⊢!. σ ⭤ π) :
  letI 𝔅 := (𝐈𝚺₁).standardDP T
  T ⊢!. 𝔅.indep σ ⭤ 𝔅.indep π := by
  apply and₃'!
  . exact indep_distribute $ h;
  . apply indep_distribute;
    exact iff_comm'! h;

omit [SoundOn T (Hierarchy 𝚷 2)] in
lemma indep_iff_distribute (h : T ⊢!. σ ⭤ π) :
  letI 𝔅 := (𝐈𝚺₁).standardDP T
  T ⊢!. 𝔅.indep σ ↔ T ⊢!. 𝔅.indep π := by
  constructor;
  . intro H; exact and₁'! (indep_iff_distribute_inside h) ⨀ H;
  . intro H; exact and₂'! (indep_iff_distribute_inside h) ⨀ H;

omit [𝐈𝚺₁ ⪯ T] [SoundOn T (Hierarchy 𝚷 2)] in
lemma iff_modalConsis_bewConsis_inside : T ⊢!. f.interpret (𝐈𝚺₁.standardDP T) (∼□⊥) ⭤ (𝐈𝚺₁.standardDP T).con := by
  dsimp [ProvabilityPredicate.con];
  apply and₃'!;
  . refine imp_trans''! (and₁'! Realization.iff_interpret_neg_inside) ?_;
    apply contra₀'!;
    simp [Realization.interpret];
  . refine imp_trans''! ?_ (and₂'! Realization.iff_interpret_neg_inside)
    apply contra₀'!;
    simp [Realization.interpret];

lemma unprovable_independency_of_consistency :
  letI 𝔅 := (𝐈𝚺₁).standardDP T
  T ⊬. 𝔅.indep (𝔅.con) := by
  let g : Realization ℒₒᵣ := λ _ => ⊥;
  have H₁ := iff_modalIndep_bewIndep (f := g) (T := T) (A := ∼□⊥);
  have H₂ := (indep_iff_distribute (T := T) (σ := g.interpret (𝐈𝚺₁.standardDP T) (∼□⊥)) (π := (𝐈𝚺₁.standardDP T).con) ?_);
  apply Iff.trans H₁ H₂ |>.not.mp;
  . have h := Modal.Hilbert.GL.unprovable_independency (φ := ∼□⊥);
    replace h := arithmetical_completeness_GL_iff (T := T) |>.not.mpr h;
    push_neg at h;
    obtain ⟨f, h⟩ := h;
    congr;
  . exact iff_modalConsis_bewConsis_inside;

lemma unrefutable_independency_of_consistency :
  letI 𝔅 := (𝐈𝚺₁).standardDP T
  T ⊬. ∼𝔅.indep (𝔅.con) := by
  sorry;

theorem independent_independency_of_consistency :
  letI 𝔅 := (𝐈𝚺₁).standardDP T
  Undecidable T.alt (𝔅.indep (𝔅.con)) := by
  constructor;
  . exact unprovable_independency_of_consistency;
  . exact unrefutable_independency_of_consistency;

end LO.ProvabilityLogic
