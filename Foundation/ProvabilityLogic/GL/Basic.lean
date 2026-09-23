module

public import Foundation.ProvabilityLogic.Logic
public import Foundation.ProvabilityLogic.GL.Hilbert.Basic

/-!
# The logic `GL`
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke Kripke.Model Kripke.Model.World

abbrev Logic.GL {α : Type*} : Logic α := { A | ⊢ᴴ[GL] A }

notation "𝐆𝐋" => Logic.GL

namespace Logic.GL

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

theorem provability_TFAE : [
    A ∈ 𝐆𝐋,
    ⊢ᴴ[GL] A,
    ⊢ᴳ[GL] ∅ ⟹ {A},
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGL] → M ⊧ A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGL] → M.root ⊩[M.toModel] A
  ].TFAE := by
  tfae_have 1 ↔ 2 := Iff.rfl;
  tfae_have 2 ↔ 3 := GL.Hilbert.iff_gentzen;
  tfae_have 2 ↔ 4 := GL.Hilbert.iff_valid_finite;
  tfae_have 2 ↔ 5 := GL.Hilbert.iff_root_forces;
  tfae_finish;

lemma iff_provable_gentzen : A ∈ 𝐆𝐋 ↔ ⊢ᴳ[GL] ∅ ⟹ {A} := provability_TFAE.out 1 3

omit [DecidableEq α] in
lemma iff_valid_finite : A ∈ 𝐆𝐋 ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGL] → M ⊧ A :=
  by classical exact provability_TFAE.out 1 4

omit [DecidableEq α] in
lemma iff_root_forces : A ∈ 𝐆𝐋 ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGL] → M.root ⊩[M.toModel] A :=
  by classical exact provability_TFAE.out 1 5

end Logic.GL

end FFL.ProvabilityLogic

end
