module

public import Foundation.ProvabilityLogic.GL.CIP

/-!
# The de Jongh–Sambin fixed point theorem for `GL`

## References

- [SV82, Lemma 4.3, Theorem 4.4]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Formula GL Kripke Kripke.Model Kripke.Model.World

namespace Logic.GL

universe u

variable {α : Type u} [DecidableEq α] {p q : α} {A D E : Formula α}

/-- - [SV82, Lemma 4.3] -/
theorem fixpoint_unique (hA : A.ModalizedIn p) (hD : 𝐆𝐋 ⊢ A⟦p ↦ D⟧ 🡘 D)
    (hE : 𝐆𝐋 ⊢ A⟦p ↦ E⟧ 🡘 E) : 𝐆𝐋 ⊢ D 🡘 E := by
  apply iff_valid_finite.mpr;
  intro _ _ M _ x;
  induction x using (IsConverseWellFounded.cwf (rel := M.Rel)).induction with
  | _ x ih =>
    have := forces_subst_single_congr_of_modalizedIn (x := x) (B := D) (C := E) hA
      fun y Rxy ↦ forces_iff.mp (ih y Rxy);
    have := iff_valid_finite.mp hD M x;
    have := iff_valid_finite.mp hE M x;
    grind;

/-- - [SV82, Theorem 4.4] -/
theorem exists_fixpoint (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ∃ D, D.atoms ⊆ A.atoms.erase p ∧ 𝐆𝐋 ⊢ A⟦p ↦ D⟧ 🡘 D := by
  have h₀ : ⊢ᴳ[𝐆𝐋] {A, □(A 🡘 #p), □(A⟦p ↦ #q⟧ 🡘 #q)} ⟹ {A⟦p ↦ #q⟧} := by
    apply Gentzen.complete;
    intro _ _ M _ x hx;
    have h₁ : x ⊩ □(A 🡘 #p) := hx _ (by simp);
    have h₂ : x ⊩ □(A⟦p ↦ #q⟧ 🡘 #q) := hx _ (by simp);
    have h₃ : ∀ y, x ≺ y → (y ⊩ #p ↔ y ⊩ #q) := by
      intro y;
      induction y using (IsConverseWellFounded.cwf (rel := M.Rel)).induction with
      | _ y ih =>
        intro Rxy;
        have := forces_subst_single_congr_of_modalizedIn (x := y) (B := #p) (C := #q) hA
          fun z Ryz ↦ ih z Ryz (IsTrans.trans _ _ _ Rxy Ryz);
        have := h₁ y Rxy;
        have := h₂ y Rxy;
        simp_all [forces_iff];
    have := forces_subst_single_congr_of_modalizedIn (B := #p) (C := #q) hA h₃;
    exact ⟨A⟦p ↦ #q⟧, by simp, by simp_all [hx A (by simp)]⟩;
  obtain ⟨D, hD⟩ := Gentzen.exists_interpolant (Γ₁ := {A, □(A 🡘 #p)})
    (Γ₂ := {□(A⟦p ↦ #q⟧ 🡘 #q)}) (Δ₁ := ∅) (Δ₂ := {A⟦p ↦ #q⟧}) h₀ (by intro; simp) (by simp);
  have hD' : D.atoms ⊆ A.atoms.erase p := by
    have := hD.atoms;
    have := atoms_subst_single (A := A) (p := p) (B := #q);
    simp [Finset.subset_iff] at *;
    grind;
  have h₁ : ⊢ᴳ[𝐆𝐋] {A⟦p ↦ D⟧, □(A⟦p ↦ D⟧ 🡘 D)} ⟹ {D} := by
    simpa [subst_single_of_not_mem (show p ∉ D.atoms by grind)]
      using Gentzen.subst (Substitution.single p D) hD.left;
  have h₂ : ⊢ᴳ[𝐆𝐋] {D, □(A⟦p ↦ D⟧ 🡘 D)} ⟹ {A⟦p ↦ D⟧} := by
    simpa [subst_single_of_not_mem (show p ∉ D.atoms by grind),
      subst_single_of_not_mem (show q ∉ D.atoms by grind), subst_single_subst_single hq, hpq]
      using Gentzen.subst (Substitution.single p D) <|
        Gentzen.subst (Substitution.single q #p) hD.right;
  use D, hD';
  apply iff_valid_finite.mpr;
  intro _ _ M _ x;
  induction x using (IsConverseWellFounded.cwf (rel := M.Rel)).induction with
  | _ x ih =>
    have h₃ : x ⊩ □(A⟦p ↦ D⟧ 🡘 D) := ih;
    have h₄ := Gentzen.sound M h₁ x;
    have h₅ := Gentzen.sound M h₂ x;
    simp only [ForcesSequent, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      exists_eq_left] at h₄ h₅;
    exact forces_iff.mpr ⟨fun h ↦ h₄ ⟨h, h₃⟩, fun h ↦ h₅ ⟨h, h₃⟩⟩;

/-- The de Jongh–Sambin fixed point theorem for `GL`.

- [SV82, Lemma 4.3, Theorem 4.4] -/
theorem fixpoint_theorem (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ∃ D, D.atoms ⊆ A.atoms.erase p ∧ 𝐆𝐋 ⊢ A⟦p ↦ D⟧ 🡘 D ∧
      ∀ E, 𝐆𝐋 ⊢ A⟦p ↦ E⟧ 🡘 E → 𝐆𝐋 ⊢ D 🡘 E := by
  obtain ⟨D, hD₁, hD₂⟩ := exists_fixpoint hpq hA hq;
  exact ⟨D, hD₁, hD₂, fun _ hE ↦ fixpoint_unique hA hD₂ hE⟩;

end Logic.GL

end FFL.ProvabilityLogic

end
