import Foundation.Propositional.Kripke.Completeness
import Foundation.Propositional.Entailment.LC
import Foundation.Vorspiel.HRel.Connected

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Kripke

protected abbrev Frame.IsPiecewiseStronglyConnected (F : Frame) := _root_.IsPiecewiseStronglyConnected F.Rel
lemma Frame.ps_connected {F : Frame} [F.IsPiecewiseStronglyConnected] : ∀ ⦃x y z : F⦄, x ≺ y → x ≺ z → y ≺ z ∨ z ≺ y := by
  apply IsPiecewiseStronglyConnected.ps_connected


section definability

variable {F : Kripke.Frame}

lemma validate_axiomDummett_of_isPiecewiseStronglyConnected [F.IsPiecewiseStronglyConnected] : F ⊧ (Axioms.Dummett (.atom 0) (.atom 1)) := by
  have := F.ps_connected;
  revert this;
  contrapose!;
  intro h;
  obtain ⟨V, x, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;
  unfold Satisfies at h;
  push_neg at h;

  rcases h with ⟨h₁, h₂⟩;

  replace h₁ := Satisfies.imp_def.not.mp h₁;
  push_neg at h₁;
  obtain ⟨y, Rxy, ⟨hy0, nhy1⟩⟩ := h₁;

  replace h₂ := Satisfies.imp_def.not.mp h₂;
  push_neg at h₂;
  obtain ⟨z, Rxz, ⟨hz1, nhz0⟩⟩ := h₂;

  use x, y, z;
  refine ⟨Rxy, Rxz, ?_⟩;
  . by_contra hC;
    replace hC := not_and_or.mp hC;
    push_neg at hC;
    rcases hC with (Ryz | Rzy);
    . exact nhz0 $ Satisfies.formula_hereditary Ryz hy0;
    . exact nhy1 $ Satisfies.formula_hereditary Rzy hz1;

lemma isPiecewiseStronglyConnected_of_validate_axiomDummett (h : F ⊧ (Axioms.Dummett (.atom 0) (.atom 1))) : F.IsPiecewiseStronglyConnected := ⟨by
  rintro x y z Rxy Ryz;
  let V : Kripke.Valuation F := ⟨λ {v a} => match a with | 0 => y ≺ v | 1 => z ≺ v | _ => True, by
    intro w v Rwv a ha;
    split at ha;
    . apply F.trans ha Rwv
    . apply F.trans ha Rwv
    . tauto;
  ⟩;
  replace h : F ⊧ (Axioms.Dummett (.atom 0) (.atom 1)) := by simpa using h;
  rcases Formula.Kripke.Satisfies.or_def.mp $ @h V x with (hi | hi);
  . right;
    apply hi Rxy;
    apply F.refl;
  . left;
    apply hi Ryz;
    apply F.refl;
⟩

end definability


section canonicality

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]

open Formula.Kripke
open Entailment
     Entailment.FiniteContext
open canonicalModel
open SaturatedConsistentTableau
open Classical

instance [Entailment.HasAxiomDummett 𝓢] : (canonicalFrame 𝓢).IsPiecewiseStronglyConnected := ⟨by
  rintro x y z Rxy Ryz;
  apply or_iff_not_imp_left.mpr;
  intro nRyz;
  obtain ⟨φ, hyp, nhzp⟩ := Set.not_subset.mp nRyz;
  intro ψ hqz;
  have : ψ ➝ φ ∉ x.1.1 := by
    by_contra hqpx;
    have hqpz : ψ ➝ φ ∈ z.1.1 := by aesop;
    have : φ ∈ z.1.1 := mdp₁_mem hqz hqpz;
    contradiction;
  have := iff_mem₁_or.mp $ mem₁_of_provable (t := x) (φ := (φ ➝ ψ) ⋎ (ψ ➝ φ)) dummett!;
  have hpqx : φ ➝ ψ ∈ x.1.1 := by aesop;
  have hpqy : φ ➝ ψ ∈ y.1.1 := Rxy hpqx;
  have : ψ ∈ y.1.1 := mdp₁_mem hyp hpqy;
  exact this;
⟩

end canonicality

end Kripke

end LO.Propositional
