module

public import Foundation.FirstOrder.Arithmetic.TA.Basic
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

@[expose] public section
namespace LO.FirstOrder.Arithmetic

abbrev withStar := Language.add ℒₒᵣ Language.unit

local notation "ℒₒᵣ⋆" => withStar

def starUnbounded (c : ℕ) : Theory ℒₒᵣ⋆ := Set.range fun n : Fin c ↦ “!!(Semiterm.Operator.numeral ℒₒᵣ⋆ n) < ⋆”

def trueArithWithStarUnbounded (n : ℕ) : Theory ℒₒᵣ⋆ :=
  𝗘𝗤 ℒₒᵣ⋆ ∪ (Semiformula.lMap (Language.Hom.add₁ _ _) '' 𝗧𝗔) ∪ starUnbounded n

lemma trueArithWithStarUnbounded.cumulative : Cumulative trueArithWithStarUnbounded := fun c =>
  Set.union_subset_union_right _ <|
    Set.range_subset_range_iff_exists_comp.mpr ⟨Fin.castSucc, by simp [Function.comp_def]⟩

abbrev modelStar (c : ℕ) : Structure Language.unit ℕ where
  func := fun _ ⟨⟨⟩⟩ _ ↦ c
  rel  := fun _ r _ ↦ PEmpty.elim r

lemma satisfiable_trueArithWithStarUnbounded (c : ℕ) : Satisfiable (trueArithWithStarUnbounded c) := by
  let : Structure Language.unit ℕ := modelStar c
  have : Structure.Zero ℒₒᵣ⋆ ℕ := ⟨rfl⟩
  have : Structure.One ℒₒᵣ⋆ ℕ := ⟨rfl⟩
  have : Structure.Add ℒₒᵣ⋆ ℕ := ⟨fun _ _ => rfl⟩
  have : Structure.Eq ℒₒᵣ⋆ ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  have : Structure.LT ℒₒᵣ⋆ ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  have : ℕ↓[ℒₒᵣ⋆] ⊧* starUnbounded c := by
    have : ∀ (i : Fin c), (↑i : ℕ) < Semiterm.Operator.Star.star.val (L := ℒₒᵣ⋆) ![] := Fin.prop
    simp [starUnbounded, models_iff, this]
  have : ℕ↓[ℒₒᵣ⋆] ⊧* trueArithWithStarUnbounded c := by
    simpa [trueArithWithStarUnbounded, models_iff] using this
  exact satisfiable_intro ℕ this

lemma satisfiable_union_trueArithWithStarUnbounded :
    Satisfiable (⋃ c, trueArithWithStarUnbounded c) :=
  (Compact.compact_cumulative trueArithWithStarUnbounded.cumulative).mpr
    satisfiable_trueArithWithStarUnbounded

instance trueArithWithStarUnbounded.eqTheory : 𝗘𝗤 ℒₒᵣ⋆ ⪯ (⋃ c, trueArithWithStarUnbounded c) :=
  Entailment.WeakerThan.ofSubset <|
    Set.subset_iUnion_of_subset 0 (Set.subset_union_of_subset_left (by simp) _)

abbrev Nonstandard : Type := ModelOfSatEq satisfiable_union_trueArithWithStarUnbounded

noncomputable section

namespace Nonstandard

notation "ℕ⋆" => Nonstandard

def star : ℕ⋆ := Semiterm.Operator.Star.star.val (L := ℒₒᵣ⋆) ![]

local notation "⋆" => star

lemma models_union_trueArithWithStarUnbounded : ℕ⋆↓[ℒₒᵣ⋆] ⊧* ⋃ c, trueArithWithStarUnbounded c := ModelOfSatEq.models _

instance : ℕ⋆↓[ℒₒᵣ] ⊧* 𝗧𝗔 := ⟨by
  have : ℕ⋆↓[ℒₒᵣ⋆] ⊧* Semiformula.lMap (Language.Hom.add₁ _ _) '' 𝗧𝗔 :=
    Semantics.ModelsSet.of_subset models_union_trueArithWithStarUnbounded
      (Set.subset_iUnion_of_subset 0 $ Set.subset_union_of_subset_left (by simp) _)
  intro σ hσ
  let s : Structure ℒₒᵣ ℕ⋆ := (ModelOfSatEq.struc satisfiable_union_trueArithWithStarUnbounded).lMap
    (Language.Hom.add₁ ℒₒᵣ Language.unit)
  have e : s = standardModel ℕ⋆ := by
    have : Structure.Zero ℒₒᵣ ℕ⋆ := ⟨rfl⟩
    have : Structure.One ℒₒᵣ ℕ⋆ := ⟨rfl⟩
    have : Structure.Add ℒₒᵣ ℕ⋆ := ⟨fun _ _ => rfl⟩
    have : Structure.Mul ℒₒᵣ ℕ⋆ := ⟨fun _ _ => rfl⟩
    have : Structure.Eq ℒₒᵣ ℕ⋆ := ⟨fun _ _ => by
      simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
        Matrix.fun_eq_vec_two]⟩
    have : Structure.LT ℒₒᵣ ℕ⋆ := ⟨fun _ _ => iff_of_eq rfl⟩
    exact standardModel_unique _ _
  have : s.toStruc ⊧ σ := Semiformula.models_lMap.mp (this.models _ (Set.mem_image_of_mem _ hσ))
  exact e ▸ this⟩

instance : ℕ⋆↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_ss (U := 𝗧𝗔) inferInstance (Structure.subset_of_models.mpr inferInstance)

lemma star_unbounded (n : ℕ) : n < ⋆ := by
  have : ℕ⋆↓[ℒₒᵣ⋆] ⊧ (“!!(Semiterm.Operator.numeral ℒₒᵣ⋆ n) < ⋆” : Sentence ℒₒᵣ⋆) :=
    models_union_trueArithWithStarUnbounded.models _
      <| Set.mem_iUnion_of_mem (n + 1)
      <| Set.mem_union_right _
      <| Set.mem_range_self (Fin.last n)
  simpa [models_iff, numeral_eq_natCast] using! this

end Nonstandard

end

end LO.FirstOrder.Arithmetic
