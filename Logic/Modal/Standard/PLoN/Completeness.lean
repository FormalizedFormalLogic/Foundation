import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.PLoN.Soundness

namespace LO.Modal.Standard

namespace PLoN

variable {α : Type*} [DecidableEq α]
variable {Λ : DeductionParameter α}

open Formula
open Theory
open MaximalConsistentTheory

abbrev CanonicalFrame (Λ : DeductionParameter α) [Inhabited (Λ)-MCT] : PLoN.Frame α where
  World := (Λ)-MCT
  Rel := λ p Ω₁ Ω₂ => ~(□p) ∈ Ω₁.theory ∧ ~p ∈ Ω₂.theory

abbrev CanonicalModel (Λ : DeductionParameter α) [Inhabited (Λ)-MCT] : PLoN.Model α where
  Frame := CanonicalFrame Λ
  Valuation Ω a := (atom a) ∈ Ω.theory

instance CanonicalModel.instSatisfies [Inhabited (Λ)-MCT] : Semantics (Formula α) ((CanonicalModel Λ).World) := Formula.PLoN.Satisfies.semantics (CanonicalModel Λ)

variable {Λ : DeductionParameter α} [Inhabited (Λ)-MCT] [Λ.HasNec]
         {p : Formula α}

lemma truthlemma : ∀ {Ω : (CanonicalModel Λ).World}, Ω ⊧ p ↔ (p ∈ Ω.theory) := by
  induction p using Formula.rec' with
  | hbox p ih =>
    intro Ω;
    constructor;
    . intro h;
      by_contra hC;
      suffices ¬Ω ⊧ □p by contradiction; done;
      simp [PLoN.Satisfies];
      constructor;
      . assumption;
      . obtain ⟨Ω', hΩ'⟩ := lindenbaum (𝓓 := Λ) (T := {~p}) (not_singleton_consistent Ω.consistent (iff_mem_neg.mpr hC));
        use Ω';
        constructor;
        . apply iff_mem_neg.mp;
          simp_all;
        . apply ih.not.mpr;
          apply iff_mem_neg.mp;
          simp_all;
    . intro h;
      by_contra hC;
      simp [PLoN.Satisfies] at hC;
      simp_all only [PLoN.Satisfies.iff_models];
  | _ => simp_all [PLoN.Satisfies];

lemma complete_of_mem_canonicalFrame {𝔽 : FrameClass α} (hFC : CanonicalFrame Λ ∈ 𝔽) : 𝔽 ⊧ p → Λ ⊢! p:= by
  simp [PLoN.ValidOnFrameClass, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  contrapose; push_neg;
  intro h;
  use (CanonicalFrame Λ);
  constructor;
  . exact hFC;
  . use (CanonicalModel Λ).Valuation;
    obtain ⟨Ω, hΩ⟩ := lindenbaum (𝓓 := Λ) (T := {~p}) (by
      apply unprovable_iff_singleton_neg_Consistent.mp;
      exact h;
    );
    use Ω;
    apply truthlemma.not.mpr;
    apply iff_mem_neg.mp;
    simp_all;

lemma instComplete_of_mem_canonicalFrame {𝔽 : FrameClass α} (hFC : CanonicalFrame Λ ∈ 𝔽) : Complete Λ 𝔽 := ⟨complete_of_mem_canonicalFrame hFC⟩

instance : Complete 𝐍 (AllFrameClass α) := instComplete_of_mem_canonicalFrame trivial

end PLoN

end LO.Modal.Standard
