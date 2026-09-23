module

public import Foundation.ProvabilityLogic.S.Gentzen.Basic
public import Foundation.ProvabilityLogic.GL.Gentzen.Kripke
public import Foundation.ProvabilityLogic.Kripke.Cone
public import Foundation.ProvabilityLogic.Kripke.Tail

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

/-- Called `Σ`-reflexivity in the source.

- [KK23]
-/
def World.IsReflexiveOf (X : FormulaFinset α) (x : M.World) : Prop := ∀ A ∈ X, x ⊩[M] □A 🡒 A

/-- - [KK23, Lemma 3.2] -/
lemma eventually_isReflexiveOf [M.IsGL] {w : ℕ → M.World} (hw : ∀ n, w (n + 1) ≺ w n)
    (X : FormulaFinset α) : ∃ i, ∀ j ≥ i, (w j).IsReflexiveOf X := by
  have : IsTrans _ fun x y : M.World ↦ y ≺ x := ⟨fun _ _ _ h₁ h₂ ↦ IsTrans.trans _ _ _ h₂ h₁⟩;
  have h : ∀ A, ∃ i, ∀ j ≥ i, w j ⊩[M] □A 🡒 A := by
    intro A;
    by_cases h : ∀ n, w n ⊩[M] A;
    . exact ⟨0, fun j _ _ ↦ h j⟩;
    . push Not at h;
      obtain ⟨n, hn⟩ := h;
      exact ⟨n + 1, fun j hj h ↦ absurd
        (h _ (Nat.rel_of_forall_rel_succ_of_lt (fun x y : M.World ↦ y ≺ x) hw (by omega))) hn⟩;
  choose i hi using h;
  exact ⟨X.sup i, fun j hj A hA ↦ hi A j ((Finset.le_sup hA).trans hj)⟩;

end Kripke.Model

namespace S.Gentzen

variable {α : Type*} [DecidableEq α] {S : Sequent α}

/-- - [KK23, Theorem 3.1] -/
theorem sound (h : ⊢ᴳ[S] S) :
    ∃ X : FormulaFinset α, ∀ {κ : Type*} [Nonempty κ] (M : Model κ α) [M.IsGL] (x : M.World),
      x.IsReflexiveOf X → x ⊩[M] S := by
  induction h with
  | ofGL h => exact ⟨∅, fun M _ x _ ↦ GL.Gentzen.sound M h x⟩;
  | impL _ _ ih₁ ih₂ =>
    obtain ⟨X₁, h₁⟩ := ih₁;
    obtain ⟨X₂, h₂⟩ := ih₂;
    exact ⟨X₁ ∪ X₂, fun M _ x hx ↦ forcesSequent_impL
      (h₁ M x fun A hA ↦ hx A (by simp [hA])) (h₂ M x fun A hA ↦ hx A (by simp [hA]))⟩;
  | impR _ ih =>
    obtain ⟨X, h⟩ := ih;
    exact ⟨X, fun M _ x hx ↦ forcesSequent_impR (h M x hx)⟩;
  | @boxL Γ Δ A _ ih =>
    obtain ⟨X, h⟩ := ih;
    use insert A X;
    intro _ _ M _ x hx hΓ;
    apply h M x (fun B hB ↦ hx B (by simp [hB]));
    intro C hC;
    rcases Finset.mem_insert.mp hC with rfl | hC;
    . exact hx C (by simp) (hΓ _ (by simp));
    . exact hΓ C (by simp [hC]);

universe u

variable {α : Type u} [DecidableEq α] {S : Sequent α}

/-- - [KK23, Theorem 3.1] -/
theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, w i ⊩[M] S) :
    ⊢ᴳ[S] S := by
  by_contra hS;
  have : Fact (⊬ᴳ[GL] S) := ⟨fun h ↦ hS (.ofGL h)⟩;
  obtain ⟨T, hsub, hT, hsat, hsubf, hbox⟩ :=
    Sequent.exists_saturated Gentzen.isImpClosed (BS := S) hS (by grind);
  replace hbox : ∀ {A}, □A ∈ T.ant → A ∈ T.ant := hbox Gentzen.boxL;
  let t : GL.SaturatedSequent S := ⟨T, hsat, hsubf, fun h ↦ hT (.ofGL h)⟩;
  let N := ((GL.countermodel S).cone t).toTail;
  have key : ∀ A (i : ℕ∞),
      (A ∈ T.ant → Sum.inr i ⊩[N.toModel] A) ∧ (A ∈ T.suc → ¬Sum.inr i ⊩[N.toModel] A) := by
    intro A;
    induction A with
    | atom a => exact fun _ ↦ ⟨id, fun h h' ↦ GL.SaturatedSequent.not_mem_both (S := t) ⟨h', h⟩⟩;
    | falsum =>
      exact fun _ ↦ ⟨fun h ↦ absurd h (GL.SaturatedSequent.bot_not_mem_ant (S := t)), fun _ ↦ id⟩;
    | imp A B ihA ihB =>
      intro i;
      constructor;
      . intro h hA;
        rcases hsat.impL h with h | h;
        . exact absurd hA ((ihA i).2 h);
        . exact (ihB i).1 h;
      . intro h hf;
        obtain ⟨hA, hB⟩ := hsat.impR h;
        exact (ihB i).2 hB (hf ((ihA i).1 hA));
    | box A ih =>
      intro i;
      constructor;
      . rintro h (⟨y, rfl | Rty⟩ | j) -;
        . exact RootedModel.toTail.forces_inl.mpr <| forces_cone.mpr <|
            (GL.countermodel.truthlemma (x := t)).1 (hbox h);
        . exact RootedModel.toTail.forces_inl.mpr <| forces_cone.mpr <|
            GL.countermodel.truthlemma.1 (Rty.2 (by simpa [t] using h));
        . exact (ih j).1 (hbox h);
      . intro h hf;
        obtain ⟨y, Rty, hy⟩ := not_forces_box.mp ((GL.countermodel.truthlemma (x := t)).2 h);
        exact hy <| forces_cone.mp <| RootedModel.toTail.forces_inl.mp <|
          hf (.inl ⟨y, .inr Rty⟩) trivial;
  obtain ⟨i, hi⟩ := h N.toModel (fun n ↦ .inr n)
    (fun n ↦ RootedModel.toTail.rel_inr_inr.mpr (by exact_mod_cast n.lt_succ_self));
  obtain ⟨D, hD, hiD⟩ := hi fun C hC ↦ (key C i).1 (hsub.ant hC);
  exact (key D i).2 (hsub.suc hD) hiD;

/-- - [KK23, Theorem 3.1] -/
theorem TFAE : [
    ⊢ᴳ[S] S,
    ∃ X : FormulaFinset α, ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (x : M.World),
      x.IsReflexiveOf X → x ⊩[M] S,
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, ∀ j ≥ i, w j ⊩[M] S,
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, w i ⊩[M] S
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

lemma iff_eventually_forces : ⊢ᴳ[S] S ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, ∀ j ≥ i, w j ⊩[M] S :=
  TFAE.out 1 3

variable {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A : Formula α}

/-- Cut is admissible.

- [KK23, Theorem 3.1]
-/
theorem cut (h₁ : ⊢ᴳ[S] Γ₁ ⟹ insert A Δ₁) (h₂ : ⊢ᴳ[S] insert A Γ₂ ⟹ Δ₂) :
    ⊢ᴳ[S] Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂ := by
  apply iff_eventually_forces.mpr;
  intro _ _ M _ w hw;
  obtain ⟨i₁, hi₁⟩ := iff_eventually_forces.mp h₁ M w hw;
  obtain ⟨i₂, hi₂⟩ := iff_eventually_forces.mp h₂ M w hw;
  exact ⟨max i₁ i₂, fun j hj ↦ forcesSequent_cut (hi₁ j (by omega)) (hi₂ j (by omega))⟩;

end S.Gentzen

end FFL.ProvabilityLogic

end
