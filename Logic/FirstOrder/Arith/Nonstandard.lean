import Logic.FirstOrder.Arith.Model
import Logic.FirstOrder.Arith.PeanoMinus

namespace LO

namespace FirstOrder

namespace Arith

abbrev withStar := Language.add ℒₒᵣ Language.unit

local notation "ℒₒᵣ⋆" => withStar

def starUnbounded (c : ℕ) : Theory ℒₒᵣ⋆ := Set.range fun n : Fin c ↦ “!!(Semiterm.Operator.numeral ℒₒᵣ⋆ n) < ⋆”

def trueArithWithStarUnbounded (n : ℕ) : Theory ℒₒᵣ⋆ :=
  𝐄𝐐 ∪ (Semiformula.lMap (Language.Hom.add₁ _ _) '' 𝐓𝐀) ∪ starUnbounded n

lemma trueArithWithStarUnbounded.cumulative : Cumulative trueArithWithStarUnbounded := fun c =>
  Set.union_subset_union_right _ <|
    Set.range_subset_range_iff_exists_comp.mpr <| ⟨Fin.castSucc, by simp[Function.comp]⟩

def modelStar (c : ℕ) : Structure Language.unit ℕ where
  func := fun _ ⟨⟨⟩⟩ _ => c
  rel  := fun _ r _ => PEmpty.elim r

lemma satisfiable_trueArithWithStarUnbounded (c : ℕ) : Semantics.SatisfiableSet (trueArithWithStarUnbounded c) := by
  letI : Structure Language.unit ℕ := modelStar c
  haveI : Structure.Zero ℒₒᵣ⋆ ℕ := ⟨rfl⟩
  haveI : Structure.One ℒₒᵣ⋆ ℕ := ⟨rfl⟩
  haveI : Structure.Add ℒₒᵣ⋆ ℕ := ⟨fun _ _ => rfl⟩
  haveI : Structure.Eq ℒₒᵣ⋆ ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  haveI : Structure.LT ℒₒᵣ⋆ ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  have : ℕ ⊧ₘ* starUnbounded c := by
    simp [starUnbounded, models_iff]; exact Fin.prop
  have : ℕ ⊧ₘ* trueArithWithStarUnbounded c := by
    simp[trueArithWithStarUnbounded, models_iff]; exact this
  exact satisfiableTheory_intro ℕ this

lemma satisfiable_union_trueArithWithStarUnbounded :
    Semantics.SatisfiableSet (⋃ c, trueArithWithStarUnbounded c) :=
  (Compact.compact_cumulative trueArithWithStarUnbounded.cumulative).mpr
    satisfiable_trueArithWithStarUnbounded

instance trueArithWithStarUnbounded.eqTheory : 𝐄𝐐 ≾ (⋃ c, trueArithWithStarUnbounded c) :=
  System.Subtheory.ofSubset <|
    Set.subset_iUnion_of_subset 0 (Set.subset_union_of_subset_left (Set.subset_union_left _ _) _)

abbrev Nonstandard : Type := ModelOfSatEq satisfiable_union_trueArithWithStarUnbounded

noncomputable section

namespace Nonstandard

notation "ℕ⋆" => Nonstandard

def star : ℕ⋆ := Semiterm.Operator.val (L := ℒₒᵣ⋆) Semiterm.Operator.Star.star ![]

local notation "⋆" => star

lemma models_union_trueArithWithStarUnbounded : ℕ⋆ ⊧ₘ* ⋃ c, trueArithWithStarUnbounded c := ModelOfSatEq.models _

instance trueArith : ℕ⋆ ⊧ₘ* 𝐓𝐀 := ⟨by
  have : ℕ⋆ ⊧ₘ* Semiformula.lMap (Language.Hom.add₁ _ _) '' 𝐓𝐀 :=
    Semantics.RealizeSet.of_subset models_union_trueArithWithStarUnbounded
      (Set.subset_iUnion_of_subset 0 $ Set.subset_union_of_subset_left (Set.subset_union_right _ _ ) _)
  intro σ hσ
  let s : Structure ℒₒᵣ ℕ⋆ := (ModelOfSatEq.struc satisfiable_union_trueArithWithStarUnbounded).lMap
    (Language.Hom.add₁ ℒₒᵣ Language.unit)
  have e : s = standardModel ℕ⋆ := by
    haveI : Structure.Zero ℒₒᵣ ℕ⋆ := ⟨rfl⟩
    haveI : Structure.One ℒₒᵣ ℕ⋆ := ⟨rfl⟩
    haveI : Structure.Add ℒₒᵣ ℕ⋆ := ⟨fun _ _ => rfl⟩
    haveI : Structure.Mul ℒₒᵣ ℕ⋆ := ⟨fun _ _ => rfl⟩
    haveI : Structure.Eq ℒₒᵣ ℕ⋆ := ⟨fun _ _ => by
      simp[Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
        ←Semiformula.eval_lMap, Matrix.fun_eq_vec₂]⟩
    haveI : Structure.LT ℒₒᵣ ℕ⋆ := ⟨fun _ _ => iff_of_eq rfl⟩
    exact standardModel_unique _ _
  have : s.toStruc ⊧ σ := Semiformula.models_lMap.mp (this.realize (Set.mem_image_of_mem _ hσ))
  exact e ▸ this⟩

instance : ℕ⋆ ⊧ₘ* 𝐏𝐀⁻ :=
  ModelsTheory.of_ss (U := 𝐓𝐀) inferInstance (Structure.subset_of_models.mpr $ Arith.Standard.models_peanoMinus)

lemma star_unbounded (n : ℕ) : n < ⋆ := by
  have : ℕ⋆ ⊧ₘ (“!!(Semiterm.Operator.numeral ℒₒᵣ⋆ n) < ⋆” : Sentence ℒₒᵣ⋆) :=
    models_union_trueArithWithStarUnbounded.realize
      (Set.mem_iUnion_of_mem (n + 1) (Set.mem_union_right _ $ Set.mem_range_self $ Fin.last n))
  simpa [models_iff, Model.numeral_eq_natCast] using this

end Nonstandard

end

end Arith

end FirstOrder

end LO
