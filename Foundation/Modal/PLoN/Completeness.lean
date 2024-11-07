import Foundation.Modal.ConsistentTheory
import Foundation.Modal.PLoN.Soundness

namespace LO.Modal

namespace PLoN

variable {α : Type u} [DecidableEq α]
variable {H : Hilbert α}

open Formula
open Theory
open MaximalConsistentTheory

abbrev CanonicalFrame (H : Hilbert α) [Nonempty (MCT H)] : PLoN.Frame α where
  World := (MCT H)
  Rel := λ φ Ω₁ Ω₂ => ∼(□φ) ∈ Ω₁.theory ∧ ∼φ ∈ Ω₂.theory

abbrev CanonicalModel (H : Hilbert α) [Nonempty (MCT H)] : PLoN.Model α where
  Frame := CanonicalFrame H
  Valuation Ω a := (atom a) ∈ Ω.theory

instance CanonicalModel.instSatisfies [Nonempty (MCT H)] : Semantics (Formula α) ((CanonicalModel H).World) := Formula.PLoN.Satisfies.semantics (CanonicalModel H)

variable {H : Hilbert α} [Nonempty (MCT H)] [H.HasNecessitation]
         {φ : Formula α}

lemma truthlemma : ∀ {Ω : (CanonicalModel H).World}, Ω ⊧ φ ↔ (φ ∈ Ω.theory) := by
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
      . obtain ⟨Ω', hΩ'⟩ := lindenbaum (H := H) (T := {∼φ}) (not_singleton_consistent Ω.consistent (iff_mem_neg.mpr hC));
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

lemma complete_of_mem_canonicalFrame {𝔽 : FrameClass α} (hFC : CanonicalFrame H ∈ 𝔽) : 𝔽 ⊧ φ → H ⊢! φ:= by
  simp [PLoN.ValidOnFrameClass, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  contrapose; push_neg;
  intro h;
  use (CanonicalFrame H);
  constructor;
  . exact hFC;
  . use (CanonicalModel H).Valuation;
    obtain ⟨Ω, hΩ⟩ := lindenbaum (H := H) (T := {∼φ}) (by
      apply unprovable_iff_singleton_neg_consistent.mp;
      exact h;
    );
    use Ω;
    apply truthlemma.not.mpr;
    apply iff_mem_neg.mp;
    simp_all;

lemma instComplete_of_mem_canonicalFrame {𝔽 : FrameClass α} (hFC : CanonicalFrame H ∈ 𝔽) : Complete H 𝔽 := ⟨complete_of_mem_canonicalFrame hFC⟩

instance : Complete (Hilbert.N α) (AllFrameClass.{u, u} α) := instComplete_of_mem_canonicalFrame (by simp)

end PLoN

end LO.Modal
