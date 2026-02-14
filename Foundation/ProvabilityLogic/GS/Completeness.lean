import Foundation.ProvabilityLogic.Grz.Completeness
import Foundation.Modal.Hilbert.GS

namespace LO.ProvabilityLogic

open FirstOrder FirstOrder.DerivabilityCondition
open Modal
open Modal.Hilbert
open FirstOrder
open Entailment FiniteContext

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] [DecidableEq (Sentence L)]
         {T₀ T : Theory L} [T₀ ⪯ T] {A : Modal.Formula ℕ}

namespace Realization

variable {𝔅 : ProvabilityPredicate T₀ T} {f : Realization L} {A B : Modal.Formula _}

/-- Interpret `□` as _"True but Unprovable"_ -/
def gsInterpret (f : Realization L) (𝔅 : ProvabilityPredicate T₀ T) : Formula ℕ → Sentence L
  | .atom a => f a
  | ⊥ => ⊥
  | φ ➝ ψ => (f.gsInterpret 𝔅 φ) ➝ (f.gsInterpret 𝔅 ψ)
  | □φ => (f.gsInterpret 𝔅 φ) ⋏ ∼𝔅 (f.gsInterpret 𝔅 φ)

lemma iff_interpret_gsTranslate_gsInterpret_inside [𝔅.HBL2] : T ⊢!. f.interpret 𝔅 (Aᴾ) ⭤ f.gsInterpret 𝔅 A := by
  induction A using Formula.rec' with
  | hatom φ => simp [Realization.interpret, gsInterpret, Formula.gsTranslate];
  | hfalsum => simp [Realization.interpret, gsInterpret, Formula.gsTranslate];
  | himp A B ihA ihB => exact Epq_Ers_EIprIqs! ihA ihB;
  | hbox A ih =>
    apply and₃'!;
    . apply imp_trans''! IIIpIqbbApq! ?_;
      apply and_replace!;
      . exact and₁'! ih;
      . apply imp_trans''! (and₁'! iff_interpret_neg_inside) ?_;
        apply contra₀'!;
        apply 𝔅.prov_distribute_imply'';
        apply and₂'! ih;
    . apply imp_trans''! ?_ ApqIIpIqbb!;
      apply and_replace!;
      . exact and₂'! ih;
      . apply imp_trans''! ?_ (and₂'! iff_interpret_neg_inside);
        apply contra₀'!;
        apply 𝔅.prov_distribute_imply'';
        apply and₁'! ih;

lemma iff_interpret_gsTranslate_gsInterpret [𝔅.HBL2] : T ⊢!. f.interpret 𝔅 (Aᴾ) ↔ T ⊢!. f.gsInterpret 𝔅 A := by
  constructor;
  . intro h; exact (and₁'! iff_interpret_gsTranslate_gsInterpret_inside) ⨀ h;
  . intro h; exact (and₂'! iff_interpret_gsTranslate_gsInterpret_inside) ⨀ h;

end Realization

variable {T : Theory ℒₒᵣ} [T.Delta1Definable] [𝐈𝚺₁ ⪯ T] [Arith.SoundOn T (Arith.Hierarchy 𝚷 2)]

theorem GS.arithmetical_completeness_iff :
  (∀ {f : Realization ℒₒᵣ}, T ⊢!. f.gsInterpret ((𝐈𝚺₁).standardDP T) A) ↔ A ∈ Logic.GS := by
  apply Iff.trans ?_ iff_provable_GS_provable_boxdot_GL.symm;
  apply Iff.trans ?_ (GL.arithmetical_completeness_iff (T := T));
  constructor;
  . intro h f;
    apply Realization.iff_interpret_gsTranslate_gsInterpret (L := ℒₒᵣ) |>.mpr;
    apply h;
  . intro h f;
    apply Realization.iff_interpret_gsTranslate_gsInterpret (L := ℒₒᵣ) |>.mp;
    apply h;

end LO.ProvabilityLogic
