import Foundation.Modal.ConsistentTheory
import Foundation.Modal.PLoN.Soundness

namespace LO.Modal

namespace PLoN

variable {α : Type u} [DecidableEq α]
variable {Λ : Hilbert α}

open Formula
open Theory
open MaximalConsistentTheory

abbrev CanonicalFrame (Λ : Hilbert α) [Nonempty (MCT Λ)] : PLoN.Frame α where
  World := (MCT Λ)
  Rel := λ φ Ω₁ Ω₂ => ∼(□φ) ∈ Ω₁.theory ∧ ∼φ ∈ Ω₂.theory

abbrev CanonicalModel (Λ : Hilbert α) [Nonempty (MCT Λ)] : PLoN.Model α where
  Frame := CanonicalFrame Λ
  Valuation Ω a := (atom a) ∈ Ω.theory

instance CanonicalModel.instSatisfies [Nonempty (MCT Λ)] : Semantics (Formula α) ((CanonicalModel Λ).World) := Formula.PLoN.Satisfies.semantics (CanonicalModel Λ)

variable {Λ : Hilbert α} [Nonempty (MCT Λ)] [Λ.HasNecessitation]
         {φ : Formula α}

lemma truthlemma : ∀ {Ω : (CanonicalModel Λ).World}, Ω ⊧ φ ↔ (φ ∈ Ω.theory) := by
  induction φ using Formula.rec' with
  | hbox φ ih =>
    intro Ω;
    constructor;
    . intro h;
      by_contra hC;
      suffices ¬Ω ⊧ □φ by contradiction;
      simp [PLoN.Satisfies];
      constructor;
      . assumption;
      . obtain ⟨Ω', hΩ'⟩ := lindenbaum (Λ := Λ) (T := {∼φ}) (not_singleton_consistent Ω.consistent (iff_mem_neg.mpr hC));
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

lemma complete_of_mem_canonicalFrame {𝔽 : FrameClass α} (hFC : CanonicalFrame Λ ∈ 𝔽) : 𝔽 ⊧ φ → Λ ⊢! φ:= by
  simp [PLoN.ValidOnFrameClass, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  contrapose; push_neg;
  intro h;
  use (CanonicalFrame Λ);
  constructor;
  . exact hFC;
  . use (CanonicalModel Λ).Valuation;
    obtain ⟨Ω, hΩ⟩ := lindenbaum (Λ := Λ) (T := {∼φ}) (by
      apply unprovable_iff_singleton_neg_consistent.mp;
      exact h;
    );
    use Ω;
    apply truthlemma.not.mpr;
    apply iff_mem_neg.mp;
    simp_all;

lemma instComplete_of_mem_canonicalFrame {𝔽 : FrameClass α} (hFC : CanonicalFrame Λ ∈ 𝔽) : Complete Λ 𝔽 := ⟨complete_of_mem_canonicalFrame hFC⟩

instance : Complete (Hilbert.N α) (AllFrameClass.{u, u} α) := instComplete_of_mem_canonicalFrame (by simp)

end PLoN

end LO.Modal
