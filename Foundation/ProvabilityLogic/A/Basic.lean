module

public import Foundation.ProvabilityLogic.A.Gentzen.Kripke
public import Foundation.ProvabilityLogic.D.Basic
public import Foundation.ProvabilityLogic.GLAlpha.Basic

/-!
# The logic `A`

## References

- [AB05, Lemma 51]
- [Art86]
- [Bek90, Lemma 5]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Formula Kripke Kripke.Model Kripke.Model.World Kripke.RootedModel

/-- Artemov's logic: `𝐆𝐋` extended by `TBB n` for every `n`.

- [Art86]
-/
abbrev Logic.A {α : Type*} : Logic α := 𝐆𝐋α Set.univ

notation "𝐀" => Logic.A

variable {α : Type*} {A : Formula α} {n : ℕ}

lemma Logic.S.provable_TBB : (𝐒 : Logic α) ⊢ TBB n := by
  simpa [TBB] using S.axiomT (A := □^[n]⊥);

lemma Logic.D.provable_TBB : (𝐃 : Logic α) ⊢ TBB n := by
  classical
  cases n with
  | zero => exact D.axiomP;
  | succ n => simpa [TBB] using D.axiomD_disj (Γ := {□^[n]⊥});

namespace Logic.A

lemma of_GL (h : 𝐆𝐋 ⊢ A) : 𝐀 ⊢ A := sumQuasiNormal.of_left h

lemma provable_TBB : (𝐀 : Logic α) ⊢ TBB n := sumQuasiNormal.mem₂ ⟨n, trivial, rfl⟩

lemma neg_boxItr_bot : (𝐀 : Logic α) ⊢ ∼□^[n]⊥ := by
  induction n with
  | zero => exact of_GL (by simp only [boxItr_zero]; cl_prover);
  | succ n ih => exact of_GL (by unfold TBB; cl_prover) ⨀ provable_TBB ⨀ ih;

lemma sound (h : 𝐀 ⊢ A) {κ : Type*} [Nonempty κ] (M : Model κ α) [M.IsGL] {x : M.World}
    (hx : ∀ n, x ⊮[M] □^[n]⊥) : x ⊩[M] A := by
  induction h generalizing M with
  | mem₁ h => exact GL.sound M h x;
  | mem₂ h =>
    obtain ⟨m, -, rfl⟩ := h;
    exact fun h ↦ absurd h (hx (m + 1));
  | mdp _ _ ih₁ ih₂ => exact ih₁ M hx (ih₂ M hx);
  | subst _ ih =>
    exact forces_subst.mp <| ih (M.subst _) fun n h ↦ hx n (by simpa using forces_subst.mp h);

universe u

variable {α : Type u} {A : Formula α}

/-- - [Bek90, Lemma 5] -/
theorem provability_TFAE [DecidableEq α] : [
    𝐀 ⊢ A,
    ⊢ᴳ[A] ∅ ⟹[1] {A},
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsGL] (a : M.NonRoot),
      (M.graft a ℕ).root ⊩[(M.graft a ℕ).toModel] A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (a : M.NonRoot),
      (M.graft a ℕ).root ⊩[(M.graft a ℕ).toModel] A,
    ∃ n : ℕ, 𝐆𝐋 ⊢ ∼□^[n]⊥ 🡒 A
  ].TFAE := by
  tfae_have 1 → 3 := fun h _ _ M _ a ↦ sound h _ (graft.not_forces_boxItr_bot (a := a));
  tfae_have 3 → 4 := fun h _ _ M _ a ↦ h M a;
  tfae_have 4 → 2 := fun h ↦ A.Gentzen.complete fun M _ a _ ↦ ⟨A, by simp, h M a⟩;
  tfae_have 2 → 5 := by
    intro h;
    obtain ⟨n, hn⟩ := (A.Gentzen.TFAE.out 1 4).mp h;
    use n;
    apply GL.iff_valid_finite.mpr;
    intro _ _ M _ x hx;
    obtain ⟨D, hD, hxD⟩ := GL.Gentzen.sound M hn x (by simp);
    grind;
  tfae_have 5 → 1 := fun ⟨_, h⟩ ↦ of_GL h ⨀ neg_boxItr_bot;
  tfae_finish;

lemma iff_provable_GL : 𝐀 ⊢ A ↔ ∃ n : ℕ, 𝐆𝐋 ⊢ ∼□^[n]⊥ 🡒 A := by
  classical
  exact provability_TFAE.out 1 5

lemma iff_forces_graft : 𝐀 ⊢ A ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (a : M.NonRoot),
      (M.graft a ℕ).root ⊩[(M.graft a ℕ).toModel] A := by
  classical
  exact provability_TFAE.out 1 4

/-- - [AB05, Lemma 51] -/
lemma exists_countermodel [DecidableEq α] (h : 𝐀 ⊬ A) :
    ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : M.IsFiniteGL) (u : M.World),
      M.root ⊮[M.toModel] A ∧ M.root ≺ u ∧ u.IsReflexiveOf A.subfmls.prebox := by
  sorry

lemma subset_D : (𝐀 : Logic α) ⊆ 𝐃 := by
  sorry

lemma not_axiomD {a : α} : 𝐀 ⊬ □(□#a ⋎ □#a) 🡒 □#a ⋎ □#a := by
  sorry

lemma GL_ssubset : (𝐆𝐋 : Logic α) ⊂ 𝐀 := by
  sorry

lemma ssubset_D [Inhabited α] : (𝐀 : Logic α) ⊂ 𝐃 :=
  ⟨subset_D, fun h ↦ not_axiomD (a := default) (h D.axiomD)⟩

end Logic.A

end FFL.ProvabilityLogic

end
