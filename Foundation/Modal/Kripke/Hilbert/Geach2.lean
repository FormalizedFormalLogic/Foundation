import Foundation.Modal.Hilbert.Geach
import Foundation.Modal.Kripke.Completeness2
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

namespace Kripke

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Entailment
open canonicalFrame
open SaturatedConsistentTableau

lemma canonicalFrame.multigeachean_of_provable_geach
  (hG : ∀ g ∈ G, ∀ φ, 𝓢 ⊢! ◇^[g.i](□^[g.m]φ) ➝ □^[g.j](◇^[g.n]φ))
  : MultiGeachean G (canonicalFrame 𝓢).Rel := by
  rintro g hg t₁ t₂ t₃ ⟨ht₁₂, ht₁₃⟩;
  let t : Tableau ℕ := ⟨□''⁻¹^[g.m]t₁.1.1, ◇''⁻¹^[g.n]t₂.1.2⟩;
  obtain ⟨t', ht'⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := t) (by sorry);
  use t';
  constructor;
  . apply multirel_def_multibox.mpr;
    intro φ hφ;
    have := @multirel_def_multibox (t₁ := t₁) (t₂ := t₂) (n := g.i) |>.mp;
    have := @this ht₁₂ φ ?_;
    . sorry;
    . sorry;
  . apply multirel_def_multibox.mpr;
    intro φ hφ;
    have := @multirel_def_multibox (t₁ := t₁) (t₂ := t₃) (n := g.j) |>.mp;
    have := @this ht₁₃ φ ?_;
    . sorry;
    . sorry;

end Kripke

end Kripke

end LO.Modal
