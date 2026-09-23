module

public import Foundation.ProvabilityLogic.GL.CIP
public import Foundation.ProvabilityLogic.Kripke.Overwrite

/-!
# The de Jongh–Sambin fixed point theorem for `GL`

## References

- [SV82, Lemma 4.3, Theorem 4.4]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Formula Kripke Kripke.Model Kripke.Model.World

namespace Kripke.Model.World

variable {κ α : Type*} [Nonempty κ] [DecidableEq α] {M : Model κ α} [IsTrans _ M.Rel]
  {x : M.World} {p : α} {A B C : Formula α}

lemma forces_subst_single_congr (h : ∀ y, (y = x ∨ x ≺ y) → (y ⊩[M] B ↔ y ⊩[M] C)) :
    x ⊩[M] A⟦p ↦ B⟧ ↔ x ⊩[M] A⟦p ↦ C⟧ := by
  induction A generalizing x with
  | atom a => by_cases a = p <;> simp_all;
  | falsum => rfl;
  | imp _ _ ihA ihB => exact imp_congr (ihA h) (ihB h);
  | box A ih =>
    exact forall_congr' fun y ↦ imp_congr_right fun Rxy ↦ ih fun z hz ↦ h z <| .inr <| by
      rcases hz with rfl | hz;
      · exact Rxy;
      · exact IsTrans.trans _ _ _ Rxy hz;

lemma forces_subst_single_congr_of_modalizedIn (hA : A.ModalizedIn p)
    (h : ∀ y, x ≺ y → (y ⊩[M] B ↔ y ⊩[M] C)) : x ⊩[M] A⟦p ↦ B⟧ ↔ x ⊩[M] A⟦p ↦ C⟧ := by
  induction A with
  | atom a => simp [show a ≠ p from hA];
  | falsum => rfl;
  | imp _ _ ihA ihB => exact imp_congr (ihA hA.1) (ihB hA.2);
  | box A =>
    exact forall_congr' fun y ↦ imp_congr_right fun Rxy ↦ forces_subst_single_congr fun z hz ↦ by
      rcases hz with rfl | hz;
      · exact h z Rxy;
      · exact h z (IsTrans.trans _ _ _ Rxy hz);

end Kripke.Model.World

namespace GL.Gentzen

universe u

variable {α : Type u} [DecidableEq α] {Γ Δ : FormulaFinset α}

lemma subst (s : Substitution α α) (h : ⊢ᴳ[GL] Γ ⟹ Δ) :
    ⊢ᴳ[GL] Γ.image (·⟦s⟧) ⟹ Δ.image (·⟦s⟧) := by
  apply complete;
  intro _ _ M _ x hx;
  obtain ⟨D, hD, hxD⟩ := sound (M.overwrite fun y a ↦ y ⊩[M] s a) h x
    fun C hC ↦ forces_overwrite_subst.mpr (hx _ (Finset.mem_image_of_mem _ hC));
  exact ⟨_, Finset.mem_image_of_mem _ hD, forces_overwrite_subst.mp hxD⟩;

end GL.Gentzen

open GL

namespace Logic.GL

universe u

variable {α : Type u} [DecidableEq α] {p q : α} {A D E : Formula α}

/-- - [SV82, Lemma 4.3] -/
theorem fixpoint_unique (hA : A.ModalizedIn p) (hD : A⟦p ↦ D⟧ 🡘 D ∈ 𝐆𝐋)
    (hE : A⟦p ↦ E⟧ 🡘 E ∈ 𝐆𝐋) : D 🡘 E ∈ 𝐆𝐋 := by
  apply iff_valid_finite.mpr;
  intro _ _ M _ x;
  induction x using (IsConverseWellFounded.cwf (rel := M.Rel)).induction with
  | _ x ih =>
    have := forces_subst_single_congr_of_modalizedIn (x := x) (B := D) (C := E) hA
      fun y Rxy ↦ forces_iff.mp (ih y Rxy);
    have := iff_valid_finite.mp hD M x;
    have := iff_valid_finite.mp hE M x;
    grind;

private lemma fixpoint_premise (hA : A.ModalizedIn p) :
    ⊢ᴳ[GL] {A, □(A 🡘 #p), □(A⟦p ↦ #q⟧ 🡘 #q)} ⟹ {A⟦p ↦ #q⟧} := by
  apply Gentzen.complete;
  intro _ _ M _ x hx;
  have h₁ : x ⊩[M] □(A 🡘 #p) := hx _ (by simp);
  have h₂ : x ⊩[M] □(A⟦p ↦ #q⟧ 🡘 #q) := hx _ (by simp);
  have h₃ : ∀ y, x ≺ y → (y ⊩[M] #p ↔ y ⊩[M] #q) := by
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

/-- - [SV82, Theorem 4.4] -/
theorem exists_fixpoint (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ∃ D, D.atoms ⊆ A.atoms.erase p ∧ A⟦p ↦ D⟧ 🡘 D ∈ 𝐆𝐋 := by
  have h₀ := fixpoint_premise (q := q) hA;
  obtain ⟨D, hD⟩ := Gentzen.exists_interpolant (Γ₁ := {A, □(A 🡘 #p)})
    (Γ₂ := {□(A⟦p ↦ #q⟧ 🡘 #q)}) (Δ₁ := ∅) (Δ₂ := {A⟦p ↦ #q⟧}) h₀ (by intro; simp) (by simp);
  have hD' : D.atoms ⊆ A.atoms.erase p := by
    have := hD.atoms;
    have := atoms_subst_single (A := A) (p := p) (B := #q);
    simp [Finset.subset_iff] at *;
    grind;
  have h₁ : ⊢ᴳ[GL] {A⟦p ↦ D⟧, □(A⟦p ↦ D⟧ 🡘 D)} ⟹ {D} := by
    simpa [subst_single_of_not_mem (show p ∉ D.atoms by grind)]
      using Gentzen.subst (Substitution.single p D) hD.left;
  have h₂ : ⊢ᴳ[GL] {D, □(A⟦p ↦ D⟧ 🡘 D)} ⟹ {A⟦p ↦ D⟧} := by
    simpa [subst_single_of_not_mem (show p ∉ D.atoms by grind),
      subst_single_of_not_mem (show q ∉ D.atoms by grind), subst_single_subst_single hq, hpq]
      using Gentzen.subst (Substitution.single p D) <|
        Gentzen.subst (Substitution.single q #p) hD.right;
  use D, hD';
  apply iff_valid_finite.mpr;
  intro _ _ M _ x;
  induction x using (IsConverseWellFounded.cwf (rel := M.Rel)).induction with
  | _ x ih =>
    have h₃ : x ⊩[M] □(A⟦p ↦ D⟧ 🡘 D) := ih;
    have h₄ := Gentzen.sound M h₁ x;
    have h₅ := Gentzen.sound M h₂ x;
    simp only [ForcesSequent, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      exists_eq_left] at h₄ h₅;
    exact forces_iff.mpr ⟨fun h ↦ h₄ ⟨h, h₃⟩, fun h ↦ h₅ ⟨h, h₃⟩⟩;

/-- The de Jongh–Sambin fixed point theorem for `GL`.

- [SV82, Lemma 4.3, Theorem 4.4] -/
theorem fixpoint_theorem (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ∃ D, D.atoms ⊆ A.atoms.erase p ∧ A⟦p ↦ D⟧ 🡘 D ∈ 𝐆𝐋 ∧
      ∀ E, A⟦p ↦ E⟧ 🡘 E ∈ 𝐆𝐋 → D 🡘 E ∈ 𝐆𝐋 := by
  obtain ⟨D, hD₁, hD₂⟩ := exists_fixpoint hpq hA hq;
  exact ⟨D, hD₁, hD₂, fun _ hE ↦ fixpoint_unique hA hD₂ hE⟩;

end Logic.GL

end FFL.ProvabilityLogic

end
