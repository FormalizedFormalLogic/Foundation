import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Semantics

namespace LO.Propositional.Superintuitionistic.Kripke

variable {α : Type*} [Inhabited α]

variable {𝓓 : DeductionParameter α}

open Formula Formula.Kripke
open Formula.Kripke.ValidOnFrame
open FrameClass

lemma sound (d : 𝓓 ⊢ p) : 𝔽(Ax(𝓓)) ⊧ p := by
  simp [-ValidOnFrame.models_iff];
  intro F hF;
  induction d with
  | eaxm h => exact validOnAxiomSetFrameClass_axiom h hF;
  | mdp _ _ ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | _ =>
    intros;
    first
    | apply ValidOnFrame.verum
    | apply ValidOnFrame.imply₁
    | apply ValidOnFrame.imply₂
    | apply ValidOnFrame.or₁
    | apply ValidOnFrame.or₂
    | apply ValidOnFrame.or₃
    | apply ValidOnFrame.and₁
    | apply ValidOnFrame.and₂
    | apply ValidOnFrame.and₃
    | apply ValidOnFrame.neg_equiv

lemma sound! : (𝓓 ⊢! p) → 𝔽(Ax(𝓓)) ⊧ p := λ ⟨d⟩ => sound d

instance : Sound 𝓓 𝔽(Ax(𝓓)) := ⟨sound!⟩

lemma unprovable_bot [ne : FrameClass.IsNonempty 𝔽(Ax(𝓓))] : 𝓓 ⊬! ⊥ := by
  intro h;
  obtain ⟨F, hF⟩ := ne;
  simpa using sound! h hF;

instance [FrameClass.IsNonempty 𝔽(Ax(𝓓))] : System.Consistent 𝓓 := System.Consistent.of_unprovable $ unprovable_bot

instance : System.Consistent (𝐈𝐧𝐭 : DeductionParameter α) := inferInstance


end LO.Propositional.Superintuitionistic.Kripke
