module

public import Foundation.ProvabilityLogic.Logic
public import Foundation.ProvabilityLogic.Grz.Hilbert.Basic

/-!
# The logic `Grz`
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke Kripke.Model Kripke.Model.World

abbrev Logic.Grz {α : Type*} : Logic α := { A | ⊢ᴴ[Grz] A }

notation "𝐆𝐫𝐳" => Logic.Grz

namespace Logic.Grz

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

theorem provability_TFAE : [
    A ∈ 𝐆𝐫𝐳,
    ⊢ᴴ[Grz] A,
    ⊢ᴳ[Grz] ∅ ⟹ {A},
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGrz] → M ⊧ A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGrz] → M.root ⊩[M.toModel] A
  ].TFAE := by
  tfae_have 1 ↔ 2 := Iff.rfl;
  tfae_have 2 ↔ 3 := Grz.Hilbert.iff_gentzen;
  tfae_have 2 ↔ 4 := Grz.Hilbert.iff_valid_finite;
  tfae_have 2 ↔ 5 := Grz.Hilbert.iff_root_forces;
  tfae_finish;

lemma iff_provable_gentzen : A ∈ 𝐆𝐫𝐳 ↔ ⊢ᴳ[Grz] ∅ ⟹ {A} := provability_TFAE.out 1 3

lemma iff_valid_finite : A ∈ 𝐆𝐫𝐳 ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGrz] → M ⊧ A :=
  provability_TFAE.out 1 4

lemma iff_root_forces : A ∈ 𝐆𝐫𝐳 ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGrz] → M.root ⊩[M.toModel] A :=
  provability_TFAE.out 1 5

end Logic.Grz

end FFL.ProvabilityLogic

end
