module

public import Foundation.ProvabilityLogic.Arithmetic.Interpret
public import Foundation.ProvabilityLogic.Kripke.RootExtension

/-!
# Modified Solovay sentences

Solovay sentences for the root extension of a strong reflexive countermodel of `A` whose limit
jumps from the old root to the reflexive world `u` once a witness of `σ` appears, and the
reflection principle for `σ` that they yield.

## References

- [Bek90, §6 Lemma 1, Lemma 1.7, Lemma 1.8, Lemma 2, Theorem 2]
- [AB05, Lemma 51, Lemma 53]
-/

@[expose] public section

open FFL.Entailment

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

/-- A rooted countermodel of `A` with an `A`-reflexive world `u` whose only predecessor is the
root.

- [Bek90, §6 Theorem 2]
-/
structure StrongReflexiveCountermodel (κ : Type*) [Nonempty κ] {α : Type*} [DecidableEq α]
    (A : Formula α) extends RootedModel κ α where
  root_not_forces : root ⊮[toModel] A
  u : κ
  root_rel_u : toModel.Rel root u
  isReflexiveOf_u : IsReflexiveOf (M := toModel) A.subfmls.prebox u
  eq_root_of_rel_u : ∀ z, toModel.Rel z u → z = root

end FFL.ProvabilityLogic.Kripke

namespace FFL.FirstOrder.ProvabilityAbstraction

open ProvabilityLogic Kripke Kripke.Model Kripke.Model.World Kripke.RootedModel

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} [T₀ ⪯ T]
         {𝔅 : Provability T₀ T} [𝔅.HBL]
         {κ α : Type*} [Nonempty κ] [DecidableEq α] {A : ProvabilityLogic.Formula α}

/-- The `n`-times iterated consistency `∼𝔅^[n] ⊥`. -/
def Provability.conItr (𝔅 : Provability T₀ T) (n : ℕ) : Sentence L := ∼𝔅^[n] ⊥

omit [T₀ ⪯ T] in
lemma Provability.provable_boxItr_bot_mono {n m : ℕ} (h : n ≤ m) : T₀ ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[m] ⊥ := by
  induction m, h using Nat.le_induction with
  | base => exact C_id
  | succ m _ ih =>
    suffices T₀ ⊢ 𝔅^[m] ⊥ 🡒 𝔅^[m + 1] ⊥ from C_trans ih this;
    rcases m with _ | m;
    · exact efq;
    · simpa only [Function.iterate_succ_apply'] using 𝔅.D3 (σ := 𝔅^[m] ⊥);

open Classical in
/-- Sentences indexed by the worlds of `X.extendRoot` satisfying the Solovay conditions of the
construction whose limit jumps from the old root to `u` once a witness of `σ` is found.

- [Bek90, §6 Lemma 1]
-/
structure Provability.ModifiedSolovaySentences
    (𝔅 : Provability T₀ T) (X : StrongReflexiveCountermodel κ A) [Fintype X.World]
    (σ : Sentence L) where
  Λ : X.extendRoot.World → Sentence L
  protected SC1 : ∀ i j, i ≠ j → T₀ ⊢ Λ i 🡒 ∼Λ j
  protected SC2 : ∀ i j : X.extendRoot.World, i ≺ j → j ≠ some X.u → T₀ ⊢ Λ i 🡒 𝔅.dia (Λ j)
  protected SC3 : ∀ i : X.extendRoot.World, i ≠ none → i ≠ some X.u →
    T₀ ⊢ Λ i 🡒 𝔅 (⩖ j ∈ { j : X.extendRoot.World | i ≺ j }, Λ j)
  protected SC3r : T₀ ⊢ Λ (some X.u) 🡒
    𝔅 (Λ (some X.u) ⋎ ⩖ j ∈ { j : X.extendRoot.World | some X.u ≺ j }, Λ j)
  protected SC4 : T₀ ⊢ ⩖ j, Λ j
  protected SC5 : T₀ ⊢ 𝔅 σ 🡒 ∼Λ none
  protected SC6 : T₀ ⊢ ∼σ 🡒 ∼Λ (some X.u)

namespace Provability.ModifiedSolovaySentences

variable {X : StrongReflexiveCountermodel κ A} [Fintype X.World] [X.IsGL] {σ : Sentence L}
         {S : 𝔅.ModifiedSolovaySentences X σ} {i : X.extendRoot.World}

open Classical in
noncomputable def realization (S : 𝔅.ModifiedSolovaySentences X σ) : Realization α L :=
  ⟨fun a ↦ ⩖ i ∈ { i : X.extendRoot.World | i ⊩[X.extendRoot.toModel] #a }, S.Λ i⟩

private lemma mainlemma_aux (hi : i ≠ none) {B : ProvabilityLogic.Formula α}
    (hB : B ∈ A.subfmls) :
    (i ⊩[X.extendRoot.toModel] B → T₀ ⊢ S.Λ i 🡒 B.interpret S.realization 𝔅) ∧
    (i ⊮[X.extendRoot.toModel] B → T₀ ⊢ S.Λ i 🡒 ∼B.interpret S.realization 𝔅) := by
  classical
  induction B generalizing i with
  | falsum => simp [Formula.interpret];
  | atom a =>
    constructor;
    · intro h;
      apply right_Fdisj'_intro;
      simpa using h;
    · intro h;
      apply CN_of_CN_right;
      apply left_Fdisj'_intro;
      intro j hj;
      apply S.SC1;
      rintro rfl;
      exact h (by simpa using hj);
  | imp B C ihB ihC =>
    replace ihB := ihB hi (Formula.subfmls_trans hB (by grind));
    replace ihC := ihC hi (Formula.subfmls_trans hB (by grind));
    constructor;
    · intro h;
      rcases forces_imp.mp h with hB | hC;
      · exact C_trans (ihB.2 hB) CNC;
      · exact C_trans (ihC.1 hC) implyK;
    · intro h;
      obtain ⟨hB, hC⟩ := not_forces_imp.mp h;
      exact CNC_of_C_of_CN (ihB.1 hB) (ihC.2 hC);
  | box B ih =>
    replace ih := fun {j} (hj : j ≠ none) ↦ ih hj (Formula.subfmls_trans hB (by grind));
    have hne {j : X.extendRoot.World} (Rij : i ≺ j) : j ≠ none := by
      rintro rfl;
      exact extendRoot.not_rel_none Rij;
    have hu : some X.u ⊩[X.extendRoot.toModel] □B → some X.u ⊩[X.extendRoot.toModel] B :=
      fun h ↦ extendRoot.forces_some.mpr <|
        X.isReflexiveOf_u B (FormulaFinset.mem_prebox.mpr hB) (extendRoot.forces_some.mp h);
    constructor;
    · intro h;
      have h₁ : T₀ ⊢ (⩖ j ∈ { j : X.extendRoot.World | i ≺ j }, S.Λ j) 🡒
          B.interpret S.realization 𝔅 :=
        left_Fdisj'_intro _ _ fun j hj ↦ (ih (hne (by simpa using hj))).1 (h j (by simpa using hj));
      by_cases hiu : i = some X.u;
      · subst hiu;
        exact C_trans S.SC3r <| 𝔅.mono' <| left_A_intro ((ih hi).1 (hu h)) h₁;
      · exact C_trans (S.SC3 i hi hiu) <| 𝔅.mono' h₁;
    · intro h;
      obtain ⟨j, Rij, hj⟩ := not_forces_box.mp h;
      obtain ⟨y, ⟨Riy, hy⟩, hymax⟩ :=
        X.extendRoot.terminalOf { y | i ≺ y ∧ y ⊮[X.extendRoot.toModel] B } ⟨j, Rij, hj⟩;
      have hyu : y ≠ some X.u := by
        rintro rfl;
        apply hy <| hu _;
        intro z Ryz;
        by_contra hz;
        exact hymax z ⟨IsTrans.trans _ _ _ Riy Ryz, hz⟩ Ryz;
      exact C_trans (S.SC2 i y Riy hyu) <| contra <| 𝔅.mono' <| CN_of_CN_right <|
        (ih (hne Riy)).2 hy;

/-- - [Bek90, §6 Lemma 2]
- [AB05, Lemma 53]
-/
theorem mainlemma (hi : i ≠ none) {B : ProvabilityLogic.Formula α} (hB : B ∈ A.subfmls) :
    i ⊩[X.extendRoot.toModel] B → T₀ ⊢ S.Λ i 🡒 B.interpret S.realization 𝔅 :=
  (mainlemma_aux hi hB).1

/-- - [Bek90, §6 Lemma 2]
- [AB05, Lemma 53]
-/
theorem mainlemma_neg (hi : i ≠ none) {B : ProvabilityLogic.Formula α} (hB : B ∈ A.subfmls) :
    i ⊮[X.extendRoot.toModel] B → T₀ ⊢ S.Λ i 🡒 ∼B.interpret S.realization 𝔅 :=
  (mainlemma_aux hi hB).2

lemma provable_boxItr_bot_of_ne (S : 𝔅.ModifiedSolovaySentences X σ) {z : X.World}
    (hr : z ≠ X.root) (hu : z ≠ X.u) :
    T₀ ⊢ S.Λ (some z) 🡒 𝔅^[Model.World.rank (M := X.toModel) z + 1] ⊥ := by
  classical
  induction z using WellFounded.induction IsConverseWellFounded.cwf (r := flip X.Rel) with
  | h z ih =>
    suffices T₀ ⊢ (⩖ j ∈ { j : X.extendRoot.World | some z ≺ j }, S.Λ j) 🡒
        𝔅^[Model.World.rank (M := X.toModel) z] ⊥ by
      simpa only [Function.iterate_succ_apply'] using
        C_trans (S.SC3 (some z) (by simp) (by simpa using hu)) (𝔅.mono' this);
    apply left_Fdisj'_intro;
    rintro (_ | y) hy;
    · simp at hy;
    · replace hy : z ≺ y := by simpa using hy;
      exact C_trans (ih y hy (by rintro rfl; exact not_rel_root hy)
        (by rintro rfl; exact hr <| X.eq_root_of_rel_u z hy)) <|
        𝔅.provable_boxItr_bot_mono <| Model.rank_lt_of_rel hy;

lemma provable_b (S : 𝔅.ModifiedSolovaySentences X σ) :
    T₀ ⊢ 𝔅.conItr X.height 🡒 𝔅 σ 🡒 ∼σ 🡒 S.Λ (some X.root) := by
  classical
  suffices T₀ ⊢ (⩖ j, S.Λ j) 🡒 ∼𝔅^[X.height] ⊥ 🡒 𝔅 σ 🡒 ∼σ 🡒 S.Λ (some X.root) from
    this ⨀ S.SC4;
  apply left_Udisj_intro;
  rintro (_ | z);
  · cl_prover [S.SC5];
  · by_cases hr : z = X.root;
    · subst hr;
      cl_prover;
    by_cases hu : z = X.u;
    · subst hu;
      cl_prover [S.SC6];
    cl_prover [C_trans (S.provable_boxItr_bot_of_ne hr hu) <|
      𝔅.provable_boxItr_bot_mono <| rank_lt_height <| X.root_rel z hr];

/-- Provably in `T₀`, the `X.height`-times iterated consistency and the realization of `A` yield
the reflection instance `𝔅 σ 🡒 σ`.

- [Bek90, §6 Theorem 2]
- [AB05, Lemma 51]
-/
theorem reflection (S : 𝔅.ModifiedSolovaySentences X σ) :
    T₀ ⊢ 𝔅.conItr X.height 🡒 A.interpret S.realization 𝔅 🡒 𝔅 σ 🡒 σ := by
  cl_prover [S.provable_b, S.mainlemma_neg (Option.some_ne_none X.root) Formula.mem_subfmls_self <|
    extendRoot.forces_some.not.mpr X.root_not_forces];

end Provability.ModifiedSolovaySentences

end FFL.FirstOrder.ProvabilityAbstraction

end
