import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard.Kripke

variable {W α : Type*}
variable {Λ : AxiomSet α}

open Deduction
open Formula Formula.Kripke

lemma sound (d : Λ ⊢ p) : (𝔽 : AxiomSetFrameClass W Λ) ⊧ p := by
  induction d with
  | maxm h => exact validOnAxiomSetFrameClass_axiom h;
  | mdp _ _ ihpq ihp =>
    intro F hF V w;
    have := ihpq F hF V w;
    have := ihp F hF V w;
    simp_all;
  | nec _ ih =>
    intro F hF V w w' _;
    exact ih F hF V w';
  | disj₃ =>
    simp_all [ValidOnAxiomSetFrameClass, ValidOnFrameClass, ValidOnFrame, ValidOnModel];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [ValidOnAxiomSetFrameClass, ValidOnFrameClass, ValidOnFrame, ValidOnModel];

lemma sound! : Λ ⊢! p → (𝔽Λ : AxiomSetFrameClass W Λ) ⊧ p := λ ⟨d⟩ => sound d

instance : Sound Λ (𝔽Λ : AxiomSetFrameClass W Λ) := ⟨sound!⟩

/-
theorem soundness {T : Theory α} {p : Formula α} : T ⊢[Λ] p → T ⊨[AxiomSetFrameClass W Λ] p := by
  intro ⟨Γ, hΓ, d⟩ 𝔽 h𝔽;
  by_contra hC;
  simp [ValidOnAxiomSetFrameClass, ValidOnFrameClass] at hC;
  obtain ⟨F, ⟨hF, V⟩⟩ := hC;
  simp [Semantics.models] at h𝔽;
  intro F hF V w;
  have := 𝔽.spec.mp hF;

theorem soundness! {T : Theory α} {p} : T ⊢! p → T ⊨[AxiomSetFrameClass W Λ] p := λ ⟨d⟩ => soundness d
-/

end LO.Modal.Standard.Kripke
