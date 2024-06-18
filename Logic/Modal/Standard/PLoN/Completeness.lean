import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.PLoN.Soundness

namespace LO.Modal.Standard

namespace PLoN

variable [DecidableEq α]

open Formula
open Theory
open MaximalConsistentTheory

abbrev CanonicalFrameN : PLoN.Frame α where
  World := (𝐍)-MCT
  Rel :=  λ p Ω₁ Ω₂ => ~(□p) ∈ Ω₁.theory ∧ ~p ∈ Ω₂.theory

abbrev CanonicalModelN : PLoN.Model α where
  Frame := CanonicalFrameN
  Valuation Ω a := (atom a) ∈ Ω.theory

@[reducible]
instance : Semantics (Formula α) (CanonicalModelN (α := α)).World := Formula.plon_satisfies.instSemantics (CanonicalModelN)

lemma truthlemma {p : Formula α} : ∀ {Ω : (CanonicalModelN).World}, Ω ⊧ p ↔ (p ∈ Ω.theory) := by
  induction p using Formula.rec' with
  | hbox p ih =>
    intro Ω;
    constructor;
    . intro h;
      by_contra hC;
      suffices ¬Ω ⊧ □p by contradiction; done;
      simp [plon_satisfies];
      constructor;
      . assumption;
      . obtain ⟨Ω', hΩ'⟩ := lindenbaum (𝓓 := 𝐍) (T := {~p}) (not_singleton_consistent Ω.consistent (iff_mem_neg.mpr hC));
        use Ω';
        constructor;
        . apply iff_mem_neg.mp;
          simp_all;
        . apply ih.not.mpr;
          apply iff_mem_neg.mp;
          simp_all;
    . intro h;
      by_contra hC;
      simp [plon_satisfies] at hC;
      simp_all only [plon_satisfies.iff_models];
  | _ => simp_all [plon_satisfies];

lemma complete!_on_N {p : Formula α} : ℕ𝔽(𝐍) ⊧ p → 𝐍 ⊢! p:= by
  simp [valid_on_PLoNFrameClass, valid_on_PLoNFrame, valid_on_PLoNModel];
  contrapose;
  push_neg;
  intro h;
  use CanonicalModelN.Frame;
  constructor;
  . apply Definability.defines' Definability.N |>.mpr; trivial;
  . use CanonicalModelN.Valuation;
    obtain ⟨Ω, hΩ⟩ := lindenbaum (𝓓 := 𝐍) (T := {~p}) (by
      apply unprovable_iff_singleton_neg_Consistent.mp;
      exact h;
    );
    use Ω;
    apply truthlemma.not.mpr;
    apply iff_mem_neg.mp;
    simp_all;

instance : Complete (𝐍 : DeductionParameter α) ℕ𝔽(𝐍) := ⟨complete!_on_N⟩

end PLoN

end LO.Modal.Standard
