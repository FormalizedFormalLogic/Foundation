import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Kripke.Logic.Triv
import Foundation.Modal.Kripke.Logic.Ver

namespace LO.Modal

namespace Hilbert

open Kripke
open Formula.Kripke
open Formula (BoxdotTranslation)
open Modal.Kripke
open Entailment Entailment.FiniteContext

lemma provable_boxdotTranslated_Ver_of_Triv : (Hilbert.Triv) ⊢! φ → (Hilbert.Ver) ⊢! φᵇ := boxdotTranslated_of_dominate $ by
  intro φ hp;
  rcases (by simpa using hp) with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . exact boxdot_axiomK!;
  . simp only [BoxdotTranslation, axiomVer!, and₁!];
  . apply deduct'!;
    apply K!_intro <;> simp;

lemma provable_Triv_of_boxdotTranslated_Ver : (Hilbert.Ver) ⊢! φᵇ → (Hilbert.Triv) ⊢! φ := by
  contrapose;
  intro h;
  obtain ⟨F, F_eq, h⟩ := iff_not_validOnFrameClass_exists_frame.mp $ (not_imp_not.mpr $ Hilbert.Triv.Kripke.complete_equality |>.complete) h;
  replace F_eq := Set.mem_setOf_eq.mp F_eq;
  apply not_imp_not.mpr $ Hilbert.Ver.Kripke.sound.sound;
  apply iff_not_validOnFrameClass_exists_frame.mpr;
  use F^≠;
  constructor;
  . apply isIsolated_iff _ _ |>.mpr
    intro x y;
    by_contra hC;
    obtain ⟨nxy, Rxy⟩ := hC;
    exact nxy $ F_eq.equality.mp Rxy;
  . apply Kripke.iff_frame_boxdot_reflexive_closure.not.mpr;
    apply iff_reflexivize_irreflexivize'.not.mp;
    exact h;

theorem iff_boxdotTranslated_Ver_Triv : (Hilbert.Ver) ⊢! φᵇ ↔ (Hilbert.Triv) ⊢! φ := ⟨
  provable_Triv_of_boxdotTranslated_Ver,
  provable_boxdotTranslated_Ver_of_Triv
⟩

end Hilbert

instance : BoxdotProperty (Logic.Ver) (Logic.Triv) := ⟨Hilbert.iff_boxdotTranslated_Ver_Triv⟩

end LO.Modal
