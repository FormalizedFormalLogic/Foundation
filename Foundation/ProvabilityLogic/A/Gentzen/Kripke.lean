module

public import Foundation.ProvabilityLogic.A.Gentzen.Basic
public import Foundation.ProvabilityLogic.GL.Gentzen.Kripke
public import Foundation.ProvabilityLogic.Kripke.Cone
public import Foundation.ProvabilityLogic.Kripke.Graft

/-!
# Kripke completeness of the sequent calculus of `A`

## References

- [AB05, Lemma 51]
- [Bek90, Lemma 5]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke Kripke.Model Kripke.Model.World Kripke.RootedModel

namespace A.Gentzen

variable {α : Type*} [DecidableEq α] {Γ Δ : FormulaFinset α}

/-- - [Bek90, Lemma 5] -/
theorem sound {T : LayeredSequent 2 α} (h : ⊢ᴳ[A] T) {κ : Type*} [Nonempty κ]
    (M : RootedModel κ α) [M.IsGL] (a : M.NonRoot) :
    (M.graft a ℕ).root ⊩[(M.graft a ℕ).toModel] T.toSequent := by
  induction h with
  | liftUp h => exact GL.Gentzen.sound _ (h.toGL rfl) _;
  | boxGL h => exact GL.Gentzen.sound _ ((boxGL h).toGL rfl) _;
  | boxGP _ ih =>
    intro hΓ;
    obtain ⟨D, hD, hrD⟩ := ih hΓ;
    grind [graft.not_forces_boxItr_bot];
  | _ => grind;

universe u

variable {α : Type u} [DecidableEq α] {Γ Δ : FormulaFinset α}

/-- - [Bek90, Lemma 5] -/
theorem GL_of_forces_graft
    (h : ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (a : M.NonRoot),
      (M.graft a ℕ).root ⊩[(M.graft a ℕ).toModel] (Γ ⟹ Δ)) :
    ⊢ᴳ[GL] Γ ⟹ insert (□^[(Γ ⟹ Δ).subfmls.prebox.card + 1]⊥) Δ := by
  apply GL.Gentzen.complete;
  intro κ _ M _ x hΓ;
  by_contra! hx;
  have : Fintype M.World := Fintype.ofFinite _;
  have hr : (Γ ⟹ Δ).subfmls.prebox.card < x.rank := by
    have := hx _ (Finset.mem_insert_self _ _);
    rw [forces_boxItr_bot_iff] at this;
    omega;
  obtain ⟨z, Rxz, hz⟩ := exists_isReflexiveOf_of_card_lt_rank hr;
  have hzx : z ≠ x := fun h ↦ Std.Irrefl.irrefl (r := M.Rel) x (h ▸ Rxz);
  let a : (M.cone x).NonRoot := ⟨⟨z, .inr Rxz⟩, fun h ↦ hzx (congrArg Subtype.val h)⟩;
  have key := fun {C} (hC : C ∈ (Γ ⟹ Δ).subfmls) ↦
    (graft.forces_iff (a := a) (ι := ℕ) (fun _ hB _ ↦ Sequent.mem_subfmls_subfmls hB)
      (fun B hB ↦ forces_cone.mpr (hz B (FormulaFinset.mem_prebox.mpr hB))) hC).1 (M.cone x).root;
  obtain ⟨D, hD, hrD⟩ := h (M.cone x) a fun C hC ↦
    (key (Sequent.subset_subfmls (by simp [hC]))).mpr (forces_cone.mpr (hΓ C hC));
  exact hx D (Finset.mem_insert_of_mem hD)
    (forces_cone.mp ((key (Sequent.subset_subfmls (by simp [hD]))).mp hrD));

/-- - [Bek90, Lemma 5] -/
theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (a : M.NonRoot),
      (M.graft a ℕ).root ⊩[(M.graft a ℕ).toModel] (Γ ⟹ Δ)) :
    ⊢ᴳ[A] Γ ⟹[1] Δ :=
  of_GL_boxItr_bot (GL_of_forces_graft h)

/-- - [AB05, Lemma 51]
- [Bek90, Lemma 5]
-/
theorem TFAE : [
    ⊢ᴳ[A] Γ ⟹[1] Δ,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsGL] (a : M.NonRoot),
      (M.graft a ℕ).root ⊩[(M.graft a ℕ).toModel] (Γ ⟹ Δ),
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (a : M.NonRoot),
      (M.graft a ℕ).root ⊩[(M.graft a ℕ).toModel] (Γ ⟹ Δ),
    ∃ n : ℕ, ⊢ᴳ[GL] Γ ⟹ insert (□^[n]⊥) Δ
  ].TFAE := by
  tfae_have 1 → 2 := fun h _ _ M _ a ↦ sound h M a;
  tfae_have 2 → 3 := fun h _ _ M _ a ↦ h M a;
  tfae_have 3 → 4 := fun h ↦ ⟨_, GL_of_forces_graft h⟩;
  tfae_have 4 → 1 := fun ⟨_, h⟩ ↦ of_GL_boxItr_bot h;
  tfae_finish;

variable {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A : Formula α}

/-- Cut is admissible. -/
theorem cut : {ℓ : Fin 2} → ⊢ᴳ[A] Γ₁ ⟹[ℓ] insert A Δ₁ → ⊢ᴳ[A] insert A Γ₂ ⟹[ℓ] Δ₂ →
    ⊢ᴳ[A] Γ₁ ∪ Γ₂ ⟹[ℓ] Δ₁ ∪ Δ₂
  | 0, h₁, h₂ => iff_GL.mpr (GL.Gentzen.cut (iff_GL.mp h₁) (iff_GL.mp h₂))
  | 1, h₁, h₂ => complete fun M _ a ↦ forcesSequent_cut (sound h₁ M a) (sound h₂ M a)

end A.Gentzen

end FFL.ProvabilityLogic

end
