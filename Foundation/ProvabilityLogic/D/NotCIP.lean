module

public import Foundation.ProvabilityLogic.D.Basic
public import Foundation.ProvabilityLogic.GL.Fixedpoint

/-!
# `D` does not have the Craig interpolation property

`𝐃 ⊢ ∼(□(□b ⋎ a) 🡒 □b) 🡒 □(a 🡒 □c) 🡒 □c`, but no formula in the sole shared atom `a`
interpolates it.

## References

- [Bek89, Section 8]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Formula Kripke Kripke.Model Kripke.Model.World

namespace Logic.D

universe u

variable {α : Type u} {a b c : α} {C : Formula α}

lemma provable_counterexample : 𝐃 ⊢ ∼(□(□#b ⋎ #a) 🡒 □#b) 🡒 □(#a 🡒 □#c) 🡒 □#c := by
  sorry

variable [DecidableEq α]

lemma forces_pseudoTail_interpolant_iff (hab : a ≠ b) (hac : a ≠ c)
    (h₁ : 𝐃 ⊢ ∼(□(□#b ⋎ #a) 🡒 □#b) 🡒 C) (h₂ : 𝐃 ⊢ C 🡒 □(#a 🡒 □#c) 🡒 □#c) (hC : C.atoms ⊆ {a})
    {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (o : α → Prop) :
    Sum.inr ⊤ ⊩[(M.toPseudoTail o).toModel] C ↔ M.Val M.root a := by
  sorry

lemma S_modalize_iff_of_interpolant (hab : a ≠ b) (hac : a ≠ c)
    (h₁ : 𝐃 ⊢ ∼(□(□#b ⋎ #a) 🡒 □#b) 🡒 C) (h₂ : 𝐃 ⊢ C 🡒 □(#a 🡒 □#c) 🡒 □#c) (hC : C.atoms ⊆ {a}) :
    𝐒 ⊢ C.modalize 🡘 #a := by
  sorry

lemma _root_.FFL.ProvabilityLogic.Logic.S.not_iff_atom (hab : a ≠ b) (hC : C.ModalizedIn a)
    (hb : b ∉ C.atoms) : 𝐒 ⊬ C 🡘 #a := by
  sorry

/-- **`𝐃` does not have the Craig interpolation property.**

- [Bek89, Theorem 2] -/
theorem not_CIP (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬∀ A B : Formula α, 𝐃 ⊢ A 🡒 B →
      ∃ C, 𝐃 ⊢ A 🡒 C ∧ 𝐃 ⊢ C 🡒 B ∧ C.atoms ⊆ A.atoms ∩ B.atoms := by
  intro h;
  obtain ⟨C, h₁, h₂, hC⟩ := h _ _ (provable_counterexample (a := a) (b := b) (c := c));
  have hC : C.atoms ⊆ {a} := hC.trans (by intro; simp; grind);
  exact S.not_iff_atom hab modalizedIn_modalize
    (fun h ↦ hab (Finset.mem_singleton.mp (hC (atoms_modalize_subset h))).symm)
    (S_modalize_iff_of_interpolant hab hac h₁ h₂ hC);

end Logic.D

end FFL.ProvabilityLogic

end
