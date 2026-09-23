module

public import Foundation.ProvabilityLogic.Hilbert.GL.Basic
public import Foundation.ProvabilityLogic.Kripke.Cone

/-!
# The logic `GL`
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Kripke Kripke.Model Kripke.Model.World

namespace Logic.GL

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

lemma iff_gentzen : 𝐆𝐋 ⊢ A ↔ ⊢ᴳ[GL] ∅ ⟹ {A} := by
  constructor;
  . intro h;
    apply GL.Gentzen.complete;
    intro _ _ M _ x _;
    exact ⟨A, by simp, sound M h x⟩;
  . intro h;
    have : 𝐆𝐋 ⊢ (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    simpa using of_gentzen h ⨀ this;

theorem iff_valid_finite : 𝐆𝐋 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGL] → M ⊧ A := by
  constructor;
  . intro h _ _ M _;
    exact sound M h;
  . intro h;
    apply iff_gentzen.mpr;
    apply GL.Gentzen.complete;
    intro _ _ M _ x _;
    exact ⟨A, by simp, h M x⟩;

theorem iff_root_forces : 𝐆𝐋 ⊢ A ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGL] → M.root ⊩[M.toModel] A := by
  constructor;
  . intro h _ _ M _;
    exact sound M.toModel h M.root;
  . intro h;
    apply iff_valid_finite.mpr;
    intro _ _ M _ x;
    exact Model.forces_cone.mp <| h (M.cone x);

theorem provability_TFAE : [
    𝐆𝐋 ⊢ A,
    ⊢ᴳ[GL] ∅ ⟹ {A},
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGL] → M ⊧ A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGL] → M.root ⊩[M.toModel] A
  ].TFAE := by
  tfae_have 1 ↔ 2 := iff_gentzen;
  tfae_have 1 ↔ 3 := iff_valid_finite;
  tfae_have 1 ↔ 4 := iff_root_forces;
  tfae_finish;

end Logic.GL

end FFL.ProvabilityLogic

end
