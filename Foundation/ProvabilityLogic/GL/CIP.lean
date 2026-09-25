module

public import Foundation.ProvabilityLogic.GL.Basic
public import Foundation.ProvabilityLogic.GL.Gentzen.Maehara

/-!
# Craig interpolation property of `GL`

## References

- [SV82]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open GL

namespace Logic.GL

universe u

variable {α : Type u} [DecidableEq α] {A B : Formula α}

lemma imp_iff_provable_gentzen : 𝐆𝐋 ⊢ A 🡒 B ↔ ⊢ᴳ[𝐆𝐋] {A} ⟹ {B} := by
  constructor;
  · intro h;
    have h₁ : ⊢ᴳ[𝐆𝐋] insert (A 🡒 B) {A} ⟹ {B} := Gentzen.impL (Gentzen.union A) (Gentzen.union B);
    simpa using Gentzen.cut (Γ₁ := ∅) (Δ₁ := ∅) (by simpa using iff_provable_gentzen.mp h) h₁;
  · intro h;
    simpa using iff_provable_gentzen.mpr <| Gentzen.impR (Γ := ∅) (Δ := ∅) (by simpa using h);

/-- **Craig interpolation property** of `GL`.

- [SV82] -/
theorem CIP (h : 𝐆𝐋 ⊢ A 🡒 B) :
    ∃ C, 𝐆𝐋 ⊢ A 🡒 C ∧ 𝐆𝐋 ⊢ C 🡒 B ∧ C.atoms ⊆ A.atoms ∩ B.atoms := by
  obtain ⟨C, hC⟩ := Gentzen.exists_interpolant (Γ₁ := {A}) (Γ₂ := ∅) (Δ₁ := ∅) (Δ₂ := {B})
    (imp_iff_provable_gentzen.mp h) (by simp) (by simp);
  exact ⟨C, imp_iff_provable_gentzen.mpr (by simpa using hC.left),
    imp_iff_provable_gentzen.mpr (by simpa using hC.right), by simpa using hC.atoms⟩;

end Logic.GL

end FFL.ProvabilityLogic

end
