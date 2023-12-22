import Logic.FirstOrder.Arith.Model
import Logic.FirstOrder.Arith.PAminus

namespace LO

namespace FirstOrder

namespace Arith

abbrev withStar := Language.add ℒₒᵣ Language.unit

local notation "ℒₒᵣ⋆" => withStar

def starUnbounded (c : ℕ) : Theory ℒₒᵣ⋆ := Set.range fun n : Fin c ↦ “!!(Subterm.Operator.numeral ℒₒᵣ⋆ n) < ⋆”

def trueArithWithStarUnbounded (n : ℕ) : Theory ℒₒᵣ⋆ :=
  Theory.Eq ℒₒᵣ⋆ ∪ (Subformula.lMap (Language.Hom.add₁ _ _) '' 𝐓𝐀) ∪ starUnbounded n

lemma trueArithWithStarUnbounded.cumulative : Cumulative trueArithWithStarUnbounded := fun c =>
  Set.union_subset_union_right _ <|
    Set.range_subset_range_iff_exists_comp.mpr <| ⟨Fin.castSucc, by simp[Function.comp]⟩

def modelStar (c : ℕ) : Structure Language.unit ℕ where
  func := fun _ ⟨⟨⟩⟩ _ => c
  rel  := fun _ r _ => PEmpty.elim r

lemma satisfiable_trueArithWithStarUnbounded (c : ℕ) : Semantics.Satisfiableₛ (trueArithWithStarUnbounded c) := by
  letI : Structure Language.unit ℕ := modelStar c
  haveI : Structure.Zero ℒₒᵣ⋆ ℕ := ⟨rfl⟩
  haveI : Structure.One ℒₒᵣ⋆ ℕ := ⟨rfl⟩
  haveI : Structure.Add ℒₒᵣ⋆ ℕ := ⟨fun _ _ => rfl⟩
  haveI : Structure.Eq ℒₒᵣ⋆ ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  haveI : Structure.LT ℒₒᵣ⋆ ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  have : ℕ ⊧* starUnbounded c := by
    simp[starUnbounded, models_iff]; exact Fin.prop
  have : ℕ ⊧* trueArithWithStarUnbounded c := by
    simp[trueArithWithStarUnbounded, models_iff]; exact this
  exact satisfiableₛ_intro ℕ this

lemma satisfiable_union_trueArithWithStarUnbounded :
    Semantics.Satisfiableₛ (⋃ c, trueArithWithStarUnbounded c) :=
  (Compact.compact_cumulative trueArithWithStarUnbounded.cumulative).mpr
    satisfiable_trueArithWithStarUnbounded

instance trueArithWithStarUnbounded.eqTheory : EqTheory (⋃ c, trueArithWithStarUnbounded c) :=
  ⟨Set.subset_iUnion_of_subset 0 (Set.subset_union_of_subset_left (Set.subset_union_left _ _) _)⟩

abbrev Nonstandard : Type := ModelOfSatEq satisfiable_union_trueArithWithStarUnbounded

noncomputable section

namespace Nonstandard

notation "ℕ⋆" => Nonstandard

def star : ℕ⋆ := Subterm.Operator.val (L := ℒₒᵣ⋆) Subterm.Operator.Star.star ![]

local notation "∞" => star

lemma models_union_trueArithWithStarUnbounded : ℕ⋆ ⊧* ⋃ c, trueArithWithStarUnbounded c := ModelOfSatEq.models _

lemma trueArith : ℕ⋆ ⊧* 𝐓𝐀 := by
  have : ℕ⋆ ⊧* Subformula.lMap (Language.Hom.add₁ _ _) '' 𝐓𝐀 :=
    Semantics.modelsTheory_of_subset models_union_trueArithWithStarUnbounded
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
      simp[Subformula.Operator.val, Subformula.Operator.Eq.sentence_eq,
        ←Subformula.eval_lMap, Matrix.fun_eq_vec₂]⟩
    haveI : Structure.LT ℒₒᵣ ℕ⋆ := ⟨fun _ _ => iff_of_eq rfl⟩
    exact standardModel_unique _ _
  have : s ⊧ₛ σ := Subformula.models_lMap.mp (this (Set.mem_image_of_mem _ hσ))
  exact e ▸ this

instance : Theory.Mod ℕ⋆ 𝐓𝐀 := ⟨trueArith⟩

instance : Theory.Mod ℕ⋆ (Theory.PAminus ℒₒᵣ) :=
  Theory.Mod.of_ss (T₁ := 𝐓𝐀) _ (Structure.subset_of_models.mpr $ Arith.Standard.modelsTheoryPAminus)

lemma star_unbounded (n : ℕ) : n < ∞ := by
  have : ℕ⋆ ⊧ (“!!(Subterm.Operator.numeral ℒₒᵣ⋆ n) < ⋆” : Sentence ℒₒᵣ⋆) :=
    models_union_trueArithWithStarUnbounded
      (Set.mem_iUnion_of_mem (n + 1) (Set.mem_union_right _ $ Set.mem_range_self $ Fin.last n))
  simpa [models_iff] using this

end Nonstandard

end

end Arith

end FirstOrder

end LO
