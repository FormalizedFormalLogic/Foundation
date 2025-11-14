import Foundation.Vorspiel.Vorspiel
import Mathlib.Logic.Small.Basic

section Small

variable {α : Type uα} {β : Type uβ}

def small_preimage_of_injective (f : α → β) (h : Function.Injective f) (s : Set β) [Small.{u} s] :
    Small.{u} (f ⁻¹' s) := small_of_injective (β := s) (f := fun x ↦ ⟨f x, x.prop⟩) fun x y ↦ by
  simp [Function.Injective.eq_iff h, SetCoe.ext_iff]

end Small
