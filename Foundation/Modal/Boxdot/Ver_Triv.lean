import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Kripke.Logic.Triv
import Foundation.Modal.Kripke.Logic.Ver

namespace LO.Modal

namespace Logic

open Kripke
open Formula.Kripke
open Formula (boxdotTranslate)
open Modal.Kripke
open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

variable {φ : Formula ℕ}

lemma provable_boxdotTranslated_Ver_of_Triv : φ ∈ Logic.Triv → φᵇ ∈ Logic.Ver := Hilbert.boxdotTranslated_of_dominate $ by
  rintro φ hp;
  rcases (by simpa using hp) with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . exact boxdot_axiomK!;
  . simp only [boxdotTranslate, axiomVer!, and₁!];
  . apply deduct'!;
    apply K!_intro <;> simp;

lemma provable_Triv_of_boxdotTranslated_Ver : φᵇ ∈ Logic.Ver → φ ∈ Logic.Triv := by
  contrapose;
  rw [Logic.Triv.Kripke.equality, Logic.Ver.Kripke.isolated];
  intro h;
  obtain ⟨F, F_eq, h⟩ := iff_not_validOnFrameClass_exists_frame.mp $ h;
  replace F_eq := Set.mem_setOf_eq.mp F_eq;
  apply iff_not_validOnFrameClass_exists_frame.mpr;
  use F^≠;
  constructor;
  . exact {
      isolated := by
        intro x y;
        by_contra! hC;
        obtain ⟨Rxy, nxy⟩ := hC;
        apply nxy;
        simpa using Rxy;
    }
  . apply Kripke.iff_frame_boxdot_reflexive_closure.not.mpr;
    apply iff_reflexivize_irreflexivize'.not.mp;
    exact h;

theorem iff_boxdotTranslated_Ver_Triv : (Hilbert.Ver) ⊢! φᵇ ↔ (Hilbert.Triv) ⊢! φ := ⟨
  provable_Triv_of_boxdotTranslated_Ver,
  provable_boxdotTranslated_Ver_of_Triv
⟩

instance : BoxdotProperty (Logic.Ver) (Logic.Triv) := ⟨iff_boxdotTranslated_Ver_Triv⟩

end Logic


end LO.Modal
