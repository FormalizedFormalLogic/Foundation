module

public import Foundation.ProvabilityLogic.GL.Basic
public import Mathlib.Data.ENat.Basic

/-!
# The logics `GL + □^n⊥`

## References

- [AB05, Corollary 42]
- [Vis84]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Formula Kripke Kripke.Model Kripke.Model.World

/-- `𝐆𝐋` extended by `□^[n]⊥` for finite `n`, and `𝐆𝐋` itself for `n = ⊤`.

- [AB05, Corollary 42]
-/
def Logic.GLPlusBoxBot {α : Type*} : ℕ∞ → Logic α
  | .some n => 𝐆𝐋 +ᴸ {□^[n]⊥}
  | .none => 𝐆𝐋

namespace Logic.GLPlusBoxBot

variable {α : Type*} {A : Formula α} {n : ℕ}

@[simp] lemma top_eq_GL : GLPlusBoxBot (α := α) ⊤ = 𝐆𝐋 := rfl

lemma iff_provable_GL : GLPlusBoxBot n ⊢ A ↔ 𝐆𝐋 ⊢ □^[n]⊥ 🡒 A := by
  constructor;
  · intro h;
    suffices ∀ {κ : Type _} [Nonempty κ] (M : Model κ α) [M.IsGL] (x : M.World),
        x ⊩ □^[n]⊥ → x ⊩ A from
      GL.iff_valid_finite.mpr fun M _ x ↦ this M x;
    induction h with
    | mem₁ h => exact fun M _ x _ ↦ GL.sound M h x;
    | mem₂ h => exact h ▸ fun _ _ _ ↦ id;
    | mdp _ _ ih₁ ih₂ => exact fun M _ x hx ↦ ih₁ M x hx (ih₂ M x hx);
    | subst _ ih =>
      exact fun M _ x hx ↦ forces_subst.mp <| ih (M.subst _) x <| by
        simpa [forces_subst] using hx;
  · exact fun h ↦ .mdp (.mem₁ h) (.mem₂ rfl);

end Logic.GLPlusBoxBot

end FFL.ProvabilityLogic

end
