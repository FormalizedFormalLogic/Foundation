import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Semantics

namespace LO.Propositional.Superintuitionistic.Kripke

variable {W α : Type*}

open Formula.Kripke.ValidOnFrameClass
open FrameClass

-- TODO: Expand 𝐄𝐅𝐐-𝐈𝐧𝐭
lemma sound (d : 𝐄𝐅𝐐 ⊢ p) : (𝐈𝐧𝐭 W α) ⊧ p := by
  induction d with
  | eaxm h =>
    obtain ⟨q, hq⟩ := by simpa [axiomEFQ] using h;
    subst hq;
    simp;
  | mdp _ _ ihpq ihp => exact mdp (by simp_all [Intuitionistic]) ihpq ihp;
  | conj₃ => apply conj₃; simp_all [Intuitionistic];
  | disj₃ => apply disj₃; simp_all [Intuitionistic];
  | imply₁ => apply imply₁; simp_all [Intuitionistic];
  | imply₂ => apply imply₂ <;> simp_all [Intuitionistic];
  | _ => simp_all;

lemma sound! : (𝐄𝐅𝐐 ⊢! p) → (𝐈𝐧𝐭 W α) ⊧ p := λ ⟨d⟩ => sound d

instance : Sound (𝐄𝐅𝐐 : AxiomSet α) (𝐈𝐧𝐭 W α) := ⟨sound!⟩

end LO.Propositional.Superintuitionistic.Kripke
