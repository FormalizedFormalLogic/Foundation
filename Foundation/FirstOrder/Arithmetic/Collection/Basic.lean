module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Collection in models, and `𝗕𝚺 (s + 1)` below `𝗜𝚺 (s + 1)`

Collection for a definable relation in a model of a collection scheme, the converse passage from
collection to a model of the scheme, and the collection available in a model of `𝗜𝚺 (s + 1)`.

## References

- [HP98]
- [Bus98]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {R : V → V → Prop}
         {Γ : Polarity} {s : ℕ}

namespace CollectionScheme

variable {C : ArithmeticSemiformula ℕ 2 → Prop} [V↓[ℒₒᵣ] ⊧* CollectionScheme C]

private lemma collection_eval {φ : ArithmeticSemiformula ℕ 2} (hφ : C φ) (e : ℕ → V) (a : V) :
    (∀ x < a, ∃ y, φ.Eval ![x, y] e) → ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] e := by
  have h : V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom φ) :=
    Theory.models (T := CollectionScheme C) V (by simpa using mem_CollectionScheme_of_mem hφ);
  revert e a;
  simpa [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
    Semiformula.eval_bexsLT, Semiformula.eval_substs] using h;

lemma collection {R : V → V → Prop}
    (hR : ∃ e : ℕ → V, ∃ φ : ArithmeticSemiformula ℕ 2, C φ ∧ ∀ x y, R x y ↔ φ.Eval ![x, y] e)
    (a : V) (h : ∀ x < a, ∃ y, R x y) : ∃ b, ∀ x < a, ∃ y < b, R x y := by
  obtain ⟨e, φ, hφ, hiff⟩ := hR;
  apply collection_eval hφ e a ?_ |>.imp;
  . grind;
  . grind;

end CollectionScheme

lemma CollectionScheme.models_of_collection
  (H : ∀ {R : V → V → Prop}, Γ-[s].DefinableRel R → ∀ a, (∀ x < a, ∃ y, R x y) → ∃ b, ∀ x < a, ∃ y < b, R x y) :
  V↓[ℒₒᵣ] ⊧* CollectionScheme (Hierarchy Γ s) := by
  apply Semantics.ModelsSet.setOf_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ e : ℕ → V, ∀ a : V,
      (∀ x < a, ∃ y, φ.Eval ![x, y] e) → ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] e by
    simpa [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
      Semiformula.eval_bexsLT, Semiformula.eval_substs] using this;
  intro e a;
  exact H (definableRel_of_hierarchy hφ e) a;

namespace CollectionOnHierarchy

variable (Γ : Polarity) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s]

instance models_CollectionScheme : V↓[ℒₒᵣ] ⊧* CollectionScheme (StrictHierarchy Γ s) :=
  models_of_subtheory ‹_›

lemma collection (hR : StrictDefinableRel Γ s R) (a : V)
    (h : ∀ x < a, ∃ y, R x y) : ∃ b, ∀ x < a, ∃ y < b, R x y := by
  obtain ⟨e, φ, hφ, hiff⟩ := hR.exists_eval_iff;
  apply CollectionScheme.collection ⟨e, φ, hφ, fun x y ↦ by simpa using hiff ![x, y]⟩ a h;

end CollectionOnHierarchy

section standardModel

/-! ### The standard model -/

instance models_CollectionOnHierarchy (Γ : Polarity) (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗕 Γ s := by
  apply Semantics.ModelsSet.union_iff.mpr;
  and_intros;
  . infer_instance;
  . apply models_of_ss
      (CollectionScheme.models_of_collection ?_)
      (CollectionScheme_subset (·.hierarchy));
    intro R _ a h;
    choose! g hg using h;
    use (Finset.range a).sup g + 1;
    intro x hx;
    use g x;
    and_intros;
    . exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_range.mpr hx));
    . exact hg x hx;

instance {Γ : Polarity} {s : ℕ} : Consistent (𝗕 Γ s) := (𝗕 Γ s).consistent_of_sound (Eq ⊥) rfl

end standardModel

section BSigma_ISigma

/-! ### `𝗕𝚺 (s + 1)` below `𝗜𝚺 (s + 1)` -/

variable {s : ℕ}

lemma ISigma.collection [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)] {R : V → V → Prop}
    (hR : 𝚺-[s + 1].DefinableRel R) (a : V) (h : ∀ x < a, ∃ y, R x y) :
    ∃ b, ∀ x < a, ∃ y < b, R x y := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := s + 1);
  have key : ∀ y : V, ∃ b, ∀ x < y, x < a → ∃ u < b, R x u := by
    apply InductionOnHierarchy.succ_induction_sigma 𝚺 (s + 1)
      (P := fun y ↦ ∃ b, ∀ x < y, x < a → ∃ u < b, R x u)
      (hP := by definability);
    . use 0;
      simp;
    . rintro y ⟨b, hb⟩;
      rcases lt_or_ge y a with hya | hya;
      . obtain ⟨u₀, hu₀⟩ := h y hya;
        use max b (u₀ + 1);
        intro x hx _;
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl;
        . obtain ⟨u, hu, hRu⟩ := hb x hx (lt_trans hx hya);
          exact ⟨u, lt_of_lt_of_le hu (le_max_left b (u₀ + 1)), hRu⟩;
        . exact ⟨u₀, lt_of_lt_of_le (lt_add_one u₀) (le_max_right b (u₀ + 1)), hu₀⟩;
      . use b;
        intro x hx hxa;
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl;
        . exact hb x hx hxa;
        . exact absurd hxa (not_lt.mpr hya);
  obtain ⟨b, hb⟩ := key (a + 1);
  use b;
  intro x hx;
  exact hb x (lt_trans hx (lt_add_one a)) hx;

instance ISigma.models_BSigma_succ [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)] : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 1) := by
  apply Semantics.ModelsSet.union_iff.mpr;
  and_intros;
  . exact mod_ISigma_of_le (Nat.zero_le (s + 1));
  . exact models_of_ss
      (CollectionScheme.models_of_collection (Γ := 𝚺) ISigma.collection)
      (CollectionScheme_subset (·.hierarchy));

@[instance]
theorem BSigma_weakerThan_ISigma : 𝗕𝚺 (s + 1) ⪯ 𝗜𝚺 (s + 1) :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance

@[instance]
theorem BSigma_weakerThan_ISigma_succ : 𝗕𝚺 s ⪯ 𝗜𝚺 (s + 1) :=
  WeakerThan.trans (CollectionOnHierarchy_weakerThan_of_le (by omega)) BSigma_weakerThan_ISigma

@[instance]
theorem BSigma_weakerThan_Peano : 𝗕𝚺 s ⪯ 𝗣𝗔 :=
  WeakerThan.trans BSigma_weakerThan_ISigma_succ (inferInstance : 𝗜𝚺 (s + 1) ⪯ 𝗣𝗔)

end BSigma_ISigma

end FFL.FirstOrder.Arithmetic
