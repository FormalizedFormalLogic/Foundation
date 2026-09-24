module

public import Foundation.ProvabilityLogic.Arithmetic.Interpret
public import Foundation.ProvabilityLogic.Kripke.RootExtension

/-!
# Modified Solovay sentences

Solovay sentences for the root extension of a strong reflexive countermodel of `A` whose limit
jumps from the old root to the reflexive world `u` once a witness of `σ` appears, and the
reflection principle for `σ` that they yield.

## References

- [Bek90, §6]
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

open ProvabilityLogic Kripke Kripke.Model Kripke.Model.World

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
    𝔅 (Λ (some X.u) ⋎ ⩖ j ∈ { j : X.extendRoot.World | (some X.u : X.extendRoot.World) ≺ j }, Λ j)
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
  sorry

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
  sorry

lemma provable_b (S : 𝔅.ModifiedSolovaySentences X σ) :
    T₀ ⊢ 𝔅.conItr X.height 🡒 𝔅 σ 🡒 ∼σ 🡒 S.Λ (some X.root) := by
  sorry

/-- Provably in `T₀`, the `X.height`-times iterated consistency and the realization of `A` yield
the reflection instance `𝔅 σ 🡒 σ`.

- [Bek90, §6 Theorem 2]
- [AB05, Lemma 51]
-/
theorem reflection (S : 𝔅.ModifiedSolovaySentences X σ) :
    T₀ ⊢ 𝔅.conItr X.height 🡒 A.interpret S.realization 𝔅 🡒 𝔅 σ 🡒 σ := by
  sorry

end Provability.ModifiedSolovaySentences

end FFL.FirstOrder.ProvabilityAbstraction

end
