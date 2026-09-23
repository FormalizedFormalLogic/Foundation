module

public import Foundation.ProvabilityLogic.D.Gentzen.Basic
public import Foundation.ProvabilityLogic.S.Gentzen.Kripke

/-!
# Kripke completeness of the sequent calculus of `D`

## References

- [KKIM25]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke Kripke.Model Kripke.Model.World

namespace D.Gentzen

variable {α : Type*} [DecidableEq α] {Γ Δ : FormulaFinset α}

theorem sound_aux {T : LayeredSequent 3 α} (h : ⊢ᴳ[D] T) : T.level = 2 →
    ∀ {κ : Type*} [Nonempty κ] (M : Model κ α) [M.IsGL] (V : ℕ∞ → α → Prop),
      Sum.inr ⊤ ⊩[(M.toFreeTail V).toModel] T.toSequent := by
  induction h with
  | axm | botL | wkL | wkR | impL | impR => intro hl _ _ M _ V; grind;
  | boxGL | liftUp₀₁ | boxL => nofun;
  | @liftUp₁₂ Γ Δ h _ =>
    intro _ κ _ M _ V hΓ;
    obtain ⟨X, hX⟩ := S.Gentzen.sound (h.toS rfl);
    obtain ⟨i, hi⟩ := eventually_isReflexiveOf (M := (M.toFreeTail V).toModel)
      (w := fun n : ℕ ↦ Sum.inr (n : ℕ∞))
      (fun n ↦ toFreeTail.rel_inr_inr.mpr (by exact_mod_cast n.lt_succ_self)) X;
    by_contra hΔ;
    have : ∀ D ∈ Δ, ∃ k : ℕ, ∀ n ≥ k, ¬Sum.inr (n : ℕ∞) ⊩[(M.toFreeTail V).toModel] □D := by
      intro D hD;
      obtain ⟨y, Rry, hy⟩ := not_forces_box.mp fun h ↦ hΔ ⟨□D, Finset.mem_image_of_mem _ hD, h⟩;
      obtain ⟨k, hk⟩ := toFreeTail.eventually_rel Rry;
      exact ⟨k, fun n hn h ↦ hy (h y (hk n hn))⟩;
    choose! k hk using this;
    obtain ⟨E, hE, hnE⟩ := hX _ _ (hi (max i (Δ.sup k)) (le_max_left _ _)) fun C hC ↦ by
      obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hC;
      exact toFreeTail.forces_box_of_root (hΓ _ hC) _;
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hE;
    exact hk D hD _ ((Finset.le_sup hD).trans (le_max_right _ _)) hnE;

/-- - [KKIM25, Theorem 5.8] -/
theorem sound (h : ⊢ᴳ[D] Γ ⟹[2] Δ) {κ : Type*} [Nonempty κ] (M : Model κ α) [M.IsGL]
    (V : ℕ∞ → α → Prop) : Sum.inr ⊤ ⊩[(M.toFreeTail V).toModel] (Γ ⟹ Δ) :=
  sound_aux h rfl M V

universe u

variable {α : Type u} [DecidableEq α] {Γ Δ : FormulaFinset α}

/-- - [KKIM25, Lemma 5.3, Theorem 5.8] -/
theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (o : α → Prop),
      Sum.inr ⊤ ⊩[(M.toPseudoTail o).toModel] (Γ ⟹ Δ)) :
    ⊢ᴳ[D] Γ ⟹[2] Δ := by
  by_contra hD;
  have : Fact (⊬ᴳ[GL] Γ ⟹ Δ) := ⟨fun h ↦ hD (liftUp₀₂ h)⟩;
  obtain ⟨U, hsubU, hU, hsatU, hsubfU, -⟩ :=
    Sequent.exists_saturated (isPropClosed.isImpClosed 2) (BS := Γ ⟹ Δ) (S₀ := Γ ⟹ Δ) hD (by grind);
  have hS₀ : ¬⊢ᴳ[D] U.ant.prebox.box ⟹[1] U.suc.prebox.box := fun h ↦
    hU (wkR (wkL (liftUp₁₂ h) FormulaFinset.box_prebox_subset) FormulaFinset.box_prebox_subset);
  obtain ⟨T, hsubT, hT, hsatT, hsubfT, hbox⟩ :=
    Sequent.exists_saturated (isPropClosed.isImpClosed 1) (BS := Γ ⟹ Δ)
      (S₀ := U.ant.prebox.box ⟹ U.suc.prebox.box) hS₀
      (Finset.union_subset_union FormulaFinset.box_prebox_subset FormulaFinset.box_prebox_subset
        |>.trans hsubfU);
  replace hbox : ∀ {A}, □A ∈ T.ant → A ∈ T.ant := hbox boxL;
  let t : GL.SaturatedSequent (Γ ⟹ Δ) := ⟨T, hsatT, hsubfT, fun h ↦ hT (liftUp₀₁ (iff_GL.mpr h))⟩;
  let N := ((GL.countermodel (Γ ⟹ Δ)).cone t).toPseudoTail fun a ↦ #a ∈ U.ant;
  have hchain := S.Gentzen.truthlemma_freeTail (t := t) hbox
    (V := fun i ↦ if i = ⊤ then fun a ↦ #a ∈ U.ant else fun a ↦ #a ∈ T.ant)
    (fun n ↦ by simp [t]);
  have hbox' : ∀ {A}, □A ∈ U.ant → □A ∈ T.ant := fun h ↦
    hsubT.ant (Finset.mem_image_of_mem _ (FormulaFinset.mem_prebox.mpr h));
  have key : ∀ A,
      (A ∈ U.ant → Sum.inr ⊤ ⊩[N.toModel] A) ∧ (A ∈ U.suc → ¬Sum.inr ⊤ ⊩[N.toModel] A) := by
    intro A;
    induction A with
    | atom a => exact ⟨id, fun h h' ↦ hU (isPropClosed.union _ h' h)⟩;
    | falsum => exact ⟨fun h ↦ hU (isPropClosed.botL_mem h), fun _ ↦ id⟩;
    | imp A B ihA ihB =>
      constructor;
      . intro h hA;
        rcases hsatU.impL h with h | h;
        . exact absurd hA (ihA.2 h);
        . exact ihB.1 h;
      . intro h hf;
        obtain ⟨hA, hB⟩ := hsatU.impR h;
        exact ihB.2 hB (hf (ihA.1 hA));
    | box A ih =>
      constructor;
      . rintro h (y | j) R;
        . exact (hchain (□A) 0).1 (hbox' h) (.inl y) trivial;
        . obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (toFreeTail.rel_inr_inr.mp R));
          exact (hchain A m).1 (hbox (hbox' h));
      . intro h hf;
        exact (hchain (□A) 0).2
          (hsubT.suc (Finset.mem_image_of_mem _ (FormulaFinset.mem_prebox.mpr h)))
          (toFreeTail.forces_box_of_root hf _);
  obtain ⟨D, hD, hD'⟩ := h _ (fun a ↦ #a ∈ U.ant) fun C hC ↦ (key C).1 (hsubU.ant hC);
  exact (key D).2 (hsubU.suc hD) hD';

/-- - [KKIM25, Theorem 5.8] -/
theorem TFAE : [
    ⊢ᴳ[D] Γ ⟹[2] Δ,
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (V : ℕ∞ → α → Prop),
      Sum.inr ⊤ ⊩[(M.toFreeTail V).toModel] (Γ ⟹ Δ),
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (o : α → Prop),
      Sum.inr ⊤ ⊩[(M.toPseudoTail o).toModel] (Γ ⟹ Δ)
  ].TFAE := by
  tfae_have 1 → 2 := fun h _ _ M _ V ↦ sound h M V;
  tfae_have 2 → 3 := fun h _ _ M _ _ ↦ h M.toModel _;
  tfae_have 3 → 1 := complete;
  tfae_finish;

variable {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A : Formula α}

/-- Cut is admissible.

- [KKIM25, Theorem 5.8]
-/
theorem cut : {ℓ : Fin 3} → ⊢ᴳ[D] Γ₁ ⟹[ℓ] insert A Δ₁ → ⊢ᴳ[D] insert A Γ₂ ⟹[ℓ] Δ₂ →
    ⊢ᴳ[D] Γ₁ ∪ Γ₂ ⟹[ℓ] Δ₁ ∪ Δ₂
  | 0, h₁, h₂ => iff_GL.mpr (GL.Gentzen.cut (iff_GL.mp h₁) (iff_GL.mp h₂))
  | 1, h₁, h₂ => iff_S.mpr (S.Gentzen.cut (iff_S.mp h₁) (iff_S.mp h₂))
  | 2, h₁, h₂ =>
    complete fun M _ _ ↦ forcesSequent_cut (sound h₁ M.toModel _) (sound h₂ M.toModel _)

end D.Gentzen

end FFL.ProvabilityLogic

end
