import Foundation.Modal.Hilbert.Geach
import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Kripke.Hilbert.Soundness

namespace LO.Modal

open Formula.Kripke

namespace Kripke

abbrev MultiGeacheanConfluentFrameClass (G : Set Geachean.Taple) : FrameClass := { F | (MultiGeachean G) F.Rel }

instance : (MultiGeacheanConfluentFrameClass G).IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  intros t ht x y z h;
  use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }

instance MultiGeacheanFrameClass.isDefinedByGeachAxioms (G) : (MultiGeacheanConfluentFrameClass G).DefinedBy (G.image (λ t => Axioms.Geach t (.atom 0))) := by
  unfold MultiGeacheanConfluentFrameClass MultiGeachean Axioms.Geach;
  constructor;
  intro F;
  constructor;
  . rintro hF φ ⟨g, ⟨hg, rfl⟩⟩ V x h;
    obtain ⟨y, Rxy, hbp⟩ := Satisfies.multidia_def.mp h;
    apply Satisfies.multibox_def.mpr;
    intro z Rxz;
    apply Satisfies.multidia_def.mpr;
    obtain ⟨u, Ryu, Rzu⟩ := hF g hg ⟨Rxy, Rxz⟩;
    use u;
    constructor;
    . assumption;
    . exact (Satisfies.multibox_def.mp hbp) Ryu;
  . rintro h g hg x y z ⟨Rxy, Rxz⟩;
    let V : Kripke.Valuation F := λ v _ => y ≺^[g.m] v;
    have : Satisfies ⟨F, V⟩ x (◇^[g.i](□^[g.m](.atom 0))) := by
      apply Satisfies.multidia_def.mpr;
      use y;
      constructor;
      . assumption;
      . apply Satisfies.multibox_def.mpr;
        aesop;
    have : Satisfies ⟨F, V⟩ x (□^[g.j](◇^[g.n]Formula.atom 0)) := h (Axioms.Geach g (.atom 0)) (by tauto) V x this;
    have : Satisfies ⟨F, V⟩ z (◇^[g.n]Formula.atom 0) := Satisfies.multibox_def.mp this Rxz;
    obtain ⟨u, Rzu, Ryu⟩ := Satisfies.multidia_def.mp this;
    exact ⟨u, Ryu, Rzu⟩;

instance MultiGeacheanFrameClass.isDefinedByGeachHilbertAxioms (ts)
  : (MultiGeacheanConfluentFrameClass ts).DefinedBy (Hilbert.Geach ts).axioms :=
  FrameClass.definedBy_with_axiomK (MultiGeacheanFrameClass.isDefinedByGeachAxioms ts)


section

abbrev ReflexiveFrameClass : FrameClass := { F | Reflexive F }
instance ReflexiveFrameClass.definedByAxiomT : ReflexiveFrameClass.DefinedBy {Axioms.T (.atom 0)} := ⟨by
  convert MultiGeacheanFrameClass.isDefinedByGeachAxioms {⟨0, 0, 1, 0⟩} |>.defines;
  . ext F; simp [Axioms.Geach, MultiGeachean, ←Geachean.reflexive_def];
  . simp;
⟩

abbrev TransitiveFrameClass : FrameClass := { F | Transitive F }
instance TransitiveFrameClass.definedByAxiomFour : TransitiveFrameClass.DefinedBy {Axioms.Four (.atom 0)} := ⟨by
  convert MultiGeacheanFrameClass.isDefinedByGeachAxioms {⟨0, 2, 1, 0⟩} |>.defines;
  . ext F; simp [Axioms.Geach, MultiGeachean, ←Geachean.transitive_def];
  . simp;
⟩

variable {F : Frame}

lemma iff_reflexive_validate_AxiomT : Reflexive F.Rel ↔ F ⊧ (Axioms.T (.atom 0)) := by
  simpa using ReflexiveFrameClass.definedByAxiomT.defines F;

alias ⟨_, reflexive_of_validate_AxiomT⟩ := iff_reflexive_validate_AxiomT


lemma iff_transitive_validate_AxiomFour : Transitive F.Rel ↔ F ⊧ (Axioms.Four (.atom 0)) := by
  simpa using TransitiveFrameClass.definedByAxiomFour.defines F;

alias ⟨_, transitive_of_validate_AxiomFour⟩ := iff_transitive_validate_AxiomFour

end

end Kripke



namespace Kripke

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Entailment
open FormulaSet
open canonicalFrame
open MaximalConsistentSet

lemma canonicalFrame.multigeachean_of_provable_geach
  (hG : ∀ g ∈ G, ∀ φ, 𝓢 ⊢! ◇^[g.i](□^[g.m]φ) ➝ □^[g.j](◇^[g.n]φ))
  : MultiGeachean G (canonicalFrame 𝓢).Rel := by
  intro t ht;
  rintro X Y Z ⟨RXY, RXZ⟩;
  have ⟨U, hU⟩ := lindenbaum (𝓢 := 𝓢) (T := □''⁻¹^[t.m]Y.1 ∪ □''⁻¹^[t.n]Z.1) $ by
    apply intro_union_consistent;
    rintro Γ Δ ⟨hΓ, hΔ⟩ hC;

    replace hΓ : ∀ φ ∈ Γ, □^[t.m]φ ∈ Y := by simpa using hΓ;
    have hΓconj : □^[t.m]⋀Γ ∈ Y := iff_mem_multibox_conj.mpr hΓ;

    replace hΔ : ∀ φ ∈ Δ, □^[t.n]φ ∈ Z := by simpa using hΔ;
    have hZ₁ : □^[t.n]⋀Δ ∈ Z := iff_mem_multibox_conj.mpr hΔ;

    have : □^[t.j](◇^[t.n]⋀Γ) ∈ X := MaximalConsistentSet.mdp
      (membership_iff.mpr $ Context.of! (hG t ht _))
      (multirel_def_multidia.mp RXY hΓconj)
    have hZ₂ : ◇^[t.n]⋀Γ ∈ Z := multirel_def_multibox.mp RXZ this;

    have : 𝓢 ⊢! □^[t.n]⋀Δ ⋏ ◇^[t.n]⋀Γ ➝ ⊥ := by {
      apply and_imply_iff_imply_imply'!.mpr;
      exact imp_trans''!
        (show _ ⊢! □^[t.n]⋀Δ ➝ □^[t.n](∼⋀Γ) by exact imply_multibox_distribute'! $ contra₁'! $ imp_trans''! (and_imply_iff_imply_imply'!.mp hC) (and₂'! neg_equiv!))
        (show _ ⊢! □^[t.n](∼⋀Γ) ➝ (◇^[t.n]⋀Γ) ➝ ⊥ by exact imp_trans''! (contra₁'! $ and₁'! $ multidia_duality!) (and₁'! neg_equiv!));
    }
    have : 𝓢 ⊬ □^[t.n]⋀Δ ⋏ ◇^[t.n]⋀Γ ➝ ⊥ := (def_consistent.mp (Z.consistent)) (Γ := [□^[t.n]⋀Δ, ◇^[t.n]⋀Γ]) $ by
      suffices □^[t.n]⋀Δ ∈ ↑Z ∧ ◇^[t.n]⋀Γ ∈ ↑Z by simpa;
      constructor <;> assumption;
    contradiction;
  use U;
  simp only [Set.union_subset_iff] at hU;
  constructor;
  . apply multirel_def_multibox.mpr; apply hU.1;
  . apply multirel_def_multibox.mpr; apply hU.2;

end Kripke


namespace Hilbert.Geach

open Kripke

instance Kripke.sound : Sound (Hilbert.Geach G) (MultiGeacheanConfluentFrameClass G) := inferInstance

instance Kripke.Consistent : Entailment.Consistent (Hilbert.Geach G) := Kripke.Hilbert.consistent_of_FrameClass (Kripke.MultiGeacheanConfluentFrameClass G)

instance Kripke.Canonical : Canonical (Hilbert.Geach G) (MultiGeacheanConfluentFrameClass G) := ⟨by
  apply canonicalFrame.multigeachean_of_provable_geach;
  intro t ht φ;
  apply Hilbert.Deduction.maxm!;
  unfold Hilbert.axiomInstances;
  use Axioms.Geach t (.atom 0);
  constructor;
  . simp only [Hilbert.axioms];
    right;
    aesop;
  . use (λ _ => φ); simp;
⟩

instance Kripke.Complete : Complete (Hilbert.Geach G) (MultiGeacheanConfluentFrameClass G) := inferInstance

end Hilbert.Geach


end LO.Modal
