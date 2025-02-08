import Foundation.Modal.Hilbert.K
import Foundation.Modal.Kripke.Hilbert.K


namespace LO.Modal

abbrev Logic := Set (Modal.Formula ℕ)


abbrev Hilbert.logic (H : Hilbert ℕ) : Logic := { φ | H ⊢! φ }

protected abbrev Logic.K : Logic := Hilbert.K.logic


class Logic.QuasiNormal (L : Logic) where
  subset_K : Logic.K ⊆ L
  mdp_closed {φ ψ} : (φ ➝ ψ) ∈ L → φ ∈ L → ψ ∈ L
  subst_closed {φ} : φ ∈ L → (∀ s, φ⟦s⟧ ∈ L)

class Logic.Normal (L : Logic) extends QuasiNormal L where
  nec_closed {φ} : φ ∈ L → □φ ∈ L


namespace Hilbert

open System

instance normal {H : Hilbert ℕ} [H.HasK] : (H.logic).Normal where
  subset_K := by
    intro φ hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with ⟨s, rfl⟩; simp;
    | mdp ihφψ ihφ => exact mdp! ihφψ ihφ;
    | nec ih => exact nec! ih;
    | _ => simp;
  mdp_closed := by
    intro φ ψ hφψ hφ;
    exact hφψ ⨀ hφ;
  subst_closed := by
    intro φ hφ s;
    exact Hilbert.Deduction.subst! s hφ;
  nec_closed := by
    intro φ hφ;
    exact System.nec! hφ;

end Hilbert

instance : (Logic.K).Normal := Hilbert.normal



section

open Kripke

abbrev Kripke.FrameClass.logic (C : FrameClass) : Logic := { φ | C ⊧ φ }

abbrev Kripke.FiniteFrameClass.logic (C : FiniteFrameClass) : Logic := { φ | C ⊧ φ }

lemma Logic.eq_Hilbert_Logic_KripkeFrameClass_Logic
  {H : Hilbert ℕ} {C : FrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  . exact sound.sound;
  . exact complete.complete;

lemma Logic.eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic
  {H : Hilbert ℕ} {C : FiniteFrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  . exact sound.sound;
  . exact complete.complete;

lemma Logic.K.eq_AllKripkeFrameClass_Logic : Logic.K = AllFrameClass.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

lemma Logic.K.eq_AllKripkeFiniteFrameClass_Logic : Logic.K = AllFiniteFrameClass.logic := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic

end


end LO.Modal
