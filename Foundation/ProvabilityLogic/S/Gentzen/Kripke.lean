module

public import Foundation.ProvabilityLogic.S.Gentzen.Basic
public import Foundation.ProvabilityLogic.GL.Gentzen.Kripke
public import Foundation.ProvabilityLogic.Kripke.Cone
public import Foundation.ProvabilityLogic.Kripke.Tail
public import Foundation.ProvabilityLogic.Kripke.Rank

/-!
# Kripke completeness of the sequent calculus of `S`

## References

- [KK23]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke Kripke.Model Kripke.Model.World

namespace Kripke.Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

/-- - [KK23, Lemma 3.2] -/
lemma eventually_isReflexiveOf [M.IsGL] {w : ℕ → M.World} (hw : ∀ n, w (n + 1) ≺ w n)
    (X : FormulaFinset α) : ∃ i, ∀ j ≥ i, (w j).IsReflexiveOf X := by
  have : IsTrans _ fun x y : M.World ↦ y ≺ x := ⟨fun _ _ _ h₁ h₂ ↦ IsTrans.trans _ _ _ h₂ h₁⟩;
  have h : ∀ A, ∃ i, ∀ j ≥ i, w j ⊩[M] □A 🡒 A := by
    intro A;
    by_cases h : ∀ n, w n ⊩[M] A;
    · exact ⟨0, fun j _ _ ↦ h j⟩;
    · push Not at h;
      obtain ⟨n, hn⟩ := h;
      exact ⟨n + 1, fun j hj h ↦ absurd
        (h _ (Nat.rel_of_forall_rel_succ_of_lt (fun x y : M.World ↦ y ≺ x) hw (by omega))) hn⟩;
  choose i hi using h;
  exact ⟨X.sup i, fun j hj A hA ↦ hi A j ((Finset.le_sup hA).trans hj)⟩;

end Kripke.Model

namespace S.Gentzen

variable {α : Type*} [DecidableEq α] {Γ Δ : FormulaFinset α}

/-- - [KK23, Theorem 3.1] -/
theorem sound_aux {T : LayeredSequent 2 α} (h : ⊢ᴳ[S] T) :
    ∃ X : FormulaFinset α, ∀ {κ : Type*} [Nonempty κ] (M : Model κ α) [M.IsGL] (x : M.World),
      (T.level = 1 → x.IsReflexiveOf X) → x ⊩[M] T.toSequent := by
  induction h with
  | axm | botL => exact ⟨∅, by intros; grind⟩;
  | wkL _ _ ih | wkR _ _ ih | impR _ ih =>
    obtain ⟨X, h⟩ := ih;
    exact ⟨X, fun M _ x hx ↦ by have := h M x hx; grind⟩;
  | impL _ _ ih₁ ih₂ =>
    obtain ⟨X₁, h₁⟩ := ih₁;
    obtain ⟨X₂, h₂⟩ := ih₂;
    use X₁ ∪ X₂;
    intro _ _ M _ x hx;
    have := h₁ M x fun hl A hA ↦ hx hl A (by simp [hA]);
    have := h₂ M x fun hl A hA ↦ hx hl A (by simp [hA]);
    grind;
  | liftUp _ ih =>
    obtain ⟨X, h⟩ := ih;
    exact ⟨∅, fun M _ x _ ↦ h M x nofun⟩;
  | boxGL _ ih =>
    obtain ⟨X, h⟩ := ih;
    exact ⟨∅, fun M _ x _ ↦ validateSequent_boxGL (fun y ↦ h M y nofun) x⟩;
  | @boxL Γ Δ A _ ih =>
    obtain ⟨X, h⟩ := ih;
    use insert A X;
    intro _ _ M _ x hx hΓ;
    have hx := hx rfl;
    apply h M x (fun _ B hB ↦ hx B (by simp [hB]));
    intro C hC;
    rcases Finset.mem_insert.mp hC with rfl | hC;
    · exact hx C (by simp) (hΓ _ (by simp));
    · exact hΓ C (by simp [hC]);

/-- - [KK23, Theorem 3.1] -/
theorem sound (h : ⊢ᴳ[S] Γ ⟹[1] Δ) :
    ∃ X : FormulaFinset α, ∀ {κ : Type*} [Nonempty κ] (M : Model κ α) [M.IsGL] (x : M.World),
      x.IsReflexiveOf X → x ⊩[M] (Γ ⟹ Δ) := by
  obtain ⟨X, hX⟩ := sound_aux h;
  exact ⟨X, fun M _ x hx ↦ hX M x fun _ ↦ hx⟩;

universe u

variable {α : Type u} [DecidableEq α] {Γ Δ : FormulaFinset α}

/-- A saturated sequent `t` closed under `□A ↦ A` on the left is true at the finite points of a
tail below the cone of `t` in the countermodel. -/
lemma truthlemma_freeTail {BS : Sequent α} [Fact (⊬ᴳ[GL] BS)] {t : GL.SaturatedSequent BS}
    (hbox : ∀ {A}, □A ∈ t.ant → A ∈ t.ant) {V : ℕ∞ → α → Prop}
    (hV : ∀ n : ℕ, V n = fun a ↦ #a ∈ t.ant) (A : Formula α) (n : ℕ) :
    let N := ((GL.countermodel BS).cone t).toModel.toFreeTail V;
    (A ∈ t.ant → Sum.inr (n : ℕ∞) ⊩[N.toModel] A) ∧
      (A ∈ t.suc → ¬Sum.inr (n : ℕ∞) ⊩[N.toModel] A) := by
  induction A generalizing n with
  | atom a =>
    have := iff_of_eq (congrFun (hV n) a);
    exact ⟨this.mpr, fun h h' ↦ GL.SaturatedSequent.not_mem_both ⟨this.mp h', h⟩⟩;
  | falsum => exact ⟨fun h ↦ absurd h GL.SaturatedSequent.bot_not_mem_ant, fun _ ↦ id⟩;
  | imp A B ihA ihB =>
    constructor;
    · intro h hA;
      rcases t.saturated.impL h with h | h;
      · exact absurd hA ((ihA n).2 h);
      · exact (ihB n).1 h;
    · intro h hf;
      obtain ⟨hA, hB⟩ := t.saturated.impR h;
      exact (ihB n).2 hB (hf ((ihA n).1 hA));
  | box A ih =>
    constructor;
    · rintro h (⟨y, rfl | Rty⟩ | j) Rnj;
      · exact Model.toFreeTail.forces_inl.mpr <| forces_cone.mpr <|
          GL.countermodel.truthlemma.1 (hbox h);
      · exact Model.toFreeTail.forces_inl.mpr <| forces_cone.mpr <|
          GL.countermodel.truthlemma.1 (Rty.2 (by simpa using h));
      · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp
          (ne_top_of_lt (Model.toFreeTail.rel_inr_inr.mp Rnj));
        exact (ih m).1 (hbox h);
    · intro h hf;
      obtain ⟨y, Rty, hy⟩ := not_forces_box.mp ((GL.countermodel.truthlemma (x := t)).2 h);
      exact hy <| forces_cone.mp <| Model.toFreeTail.forces_inl.mp <|
        hf (.inl ⟨y, .inr Rty⟩) trivial;

/-- - [KK23, Theorem 3.1] -/
theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, w i ⊩[M] (Γ ⟹ Δ)) :
    ⊢ᴳ[S] Γ ⟹[1] Δ := by
  by_contra hS;
  have hGL : ∀ {S : Sequent α}, ⊢ᴳ[GL] S → ⊢ᴳ[S] S.ant ⟹[1] S.suc := fun h ↦ .liftUp (of_GL h);
  have : Fact (⊬ᴳ[GL] Γ ⟹ Δ) := ⟨fun h ↦ hS (hGL h)⟩;
  obtain ⟨T, hsub, hT, hsat, hsubf, hbox⟩ :=
    Sequent.exists_saturated (isPropClosed.isImpClosed 1) (BS := Γ ⟹ Δ) (S₀ := Γ ⟹ Δ) hS (by grind);
  let t : GL.SaturatedSequent (Γ ⟹ Δ) := ⟨T, hsat, hsubf, fun h ↦ hT (hGL h)⟩;
  have key := truthlemma_freeTail (t := t) (hbox boxL) (V := fun _ a ↦ #a ∈ T.ant) (fun _ ↦ rfl);
  obtain ⟨i, hi⟩ :=
    h (((GL.countermodel (Γ ⟹ Δ)).cone t).toModel.toFreeTail fun _ a ↦ #a ∈ T.ant).toModel
    (fun n ↦ .inr n)
    (fun n ↦ Model.toFreeTail.rel_inr_inr.mpr (by exact_mod_cast n.lt_succ_self));
  obtain ⟨D, hD, hiD⟩ := hi fun C hC ↦ (key C i).1 (hsub.ant hC);
  exact (key D i).2 (hsub.suc hD) hiD;

/-- - [KK23, Theorem 3.1] -/
theorem TFAE : [
    ⊢ᴳ[S] Γ ⟹[1] Δ,
    ∃ X : FormulaFinset α, ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (x : M.World),
      x.IsReflexiveOf X → x ⊩[M] (Γ ⟹ Δ),
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, ∀ j ≥ i, w j ⊩[M] (Γ ⟹ Δ),
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, w i ⊩[M] (Γ ⟹ Δ)
  ].TFAE := by
  tfae_have 1 → 2 := fun h ↦ by
    obtain ⟨X, hX⟩ := sound h;
    exact ⟨X, fun M _ ↦ hX M⟩;
  tfae_have 2 → 3 := by
    rintro ⟨X, hX⟩ _ _ M _ w hw;
    obtain ⟨i, hi⟩ := eventually_isReflexiveOf hw X;
    exact ⟨i, fun j hj ↦ hX M (w j) (hi j hj)⟩;
  tfae_have 3 → 4 := fun h _ _ M _ w hw ↦ (h M w hw).imp fun i hi ↦ hi i le_rfl;
  tfae_have 4 → 1 := complete;
  tfae_finish;

lemma iff_eventually_forces : ⊢ᴳ[S] Γ ⟹[1] Δ ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, ∀ j ≥ i, w j ⊩[M] (Γ ⟹ Δ) :=
  TFAE.out 1 3

variable {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A : Formula α}

/-- Cut is admissible.

- [KK23, Theorem 3.1]
-/
theorem cut : {ℓ : Fin 2} → ⊢ᴳ[S] Γ₁ ⟹[ℓ] insert A Δ₁ → ⊢ᴳ[S] insert A Γ₂ ⟹[ℓ] Δ₂ →
    ⊢ᴳ[S] Γ₁ ∪ Γ₂ ⟹[ℓ] Δ₁ ∪ Δ₂
  | 0, h₁, h₂ => iff_GL.mpr (GL.Gentzen.cut (iff_GL.mp h₁) (iff_GL.mp h₂))
  | 1, h₁, h₂ => by
    apply iff_eventually_forces.mpr;
    intro _ _ M _ w hw;
    obtain ⟨i₁, hi₁⟩ := iff_eventually_forces.mp h₁ M w hw;
    obtain ⟨i₂, hi₂⟩ := iff_eventually_forces.mp h₂ M w hw;
    exact ⟨max i₁ i₂, fun j hj ↦ forcesSequent_cut (hi₁ j (by omega)) (hi₂ j (by omega))⟩

end S.Gentzen

end FFL.ProvabilityLogic

end
