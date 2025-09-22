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

lemma provable_boxdotTranslated_Ver_of_Triv : Modal.Triv ⊢! φ → Modal.Ver ⊢! φᵇ := Hilbert.Normal.of_provable_boxdotTranslated_axiomInstances $ by
  rintro φ hp;
  rcases (by simpa [Axiom.instances] using hp) with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . exact boxdot_axiomK!;
  . simp only [boxdotTranslate, and₁!];
  . apply deduct'!;
    apply K!_intro <;> simp;

lemma provable_Triv_of_boxdotTranslated_Ver : Modal.Ver ⊢! φᵇ → Modal.Triv ⊢! φ := by
  intro h;
  replace h := Sound.sound (𝓢 := Modal.Ver) (𝓜 := FrameClass.Ver) h;
  apply Complete.complete (𝓢 := Modal.Triv) (𝓜 := FrameClass.Triv);
  contrapose! h;
  obtain ⟨F, hF, h⟩ := iff_not_validOnFrameClass_exists_frame.mp $ h;
  replace hF := Set.mem_setOf_eq.mp hF;
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

theorem iff_boxdotTranslated_Ver_Triv' : Modal.Ver ⊢! φᵇ ↔ Modal.Triv ⊢! φ := ⟨
  provable_Triv_of_boxdotTranslated_Ver,
  provable_boxdotTranslated_Ver_of_Triv
⟩

theorem iff_boxdotTranslated_Ver_Triv : Modal.Ver ⊢! φᵇ ↔ Modal.Triv ⊢! φ := by
  grind [iff_boxdotTranslated_Ver_Triv'];

end Logic


end LO.Modal
