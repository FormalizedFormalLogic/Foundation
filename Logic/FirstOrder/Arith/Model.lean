import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Arith.Theory

namespace LO

namespace FirstOrder

namespace Arith
open Language

section model

variable (M : Type*) [Zero M] [One M] [Add M] [Mul M] [LT M]

instance standardModel : Structure ℒₒᵣ M where
  func := fun _ f =>
    match f with
    | ORing.Func.zero => fun _ => 0
    | ORing.Func.one  => fun _ => 1
    | ORing.Func.add  => fun v => v 0 + v 1
    | ORing.Func.mul  => fun v => v 0 * v 1
  rel := fun _ r =>
    match r with
    | ORing.Rel.eq => fun v => v 0 = v 1
    | ORing.Rel.lt => fun v => v 0 < v 1

instance : Structure.Eq ℒₒᵣ M :=
  ⟨by intro a b; simp[standardModel, Subformula.Operator.val, Subformula.Operator.Eq.sentence_eq, Subformula.eval_rel]⟩

instance : Structure.Zero ℒₒᵣ M := ⟨rfl⟩

instance : Structure.One ℒₒᵣ M := ⟨rfl⟩

instance : Structure.Add ℒₒᵣ M := ⟨fun _ _ => rfl⟩

instance : Structure.Mul ℒₒᵣ M := ⟨fun _ _ => rfl⟩

instance : Structure.Eq ℒₒᵣ M := ⟨fun _ _ => iff_of_eq rfl⟩

instance : Structure.LT ℒₒᵣ M := ⟨fun _ _ => iff_of_eq rfl⟩

instance : ORing ℒₒᵣ := ORing.mk

lemma standardModel_unique (s : Structure ℒₒᵣ M)
    [Structure.Zero ℒₒᵣ M] [Structure.One ℒₒᵣ M] [Structure.Add ℒₒᵣ M] [Structure.Mul ℒₒᵣ M]
    [Structure.Eq ℒₒᵣ M] [Structure.LT ℒₒᵣ M] : s = standardModel M := Structure.ext _ _
  (funext₃ fun k f _ =>
    match k, f with
    | _, Language.Zero.zero => by simp[Matrix.empty_eq]; rfl
    | _, Language.One.one   => by simp[Matrix.empty_eq]; rfl
    | _, Language.Add.add   => by simp; rfl
    | _, Language.Mul.mul   => by simp; rfl)
  (funext₃ fun k r _ =>
    match k, r with
    | _, Language.Eq.eq => by simp; rfl
    | _, Language.LT.lt => by simp; rfl)

end model

namespace standardModel
variable {μ : Type v} (e : Fin n → ℕ) (ε : μ → ℕ)

lemma modelsTheoryPAminus : ℕ ⊧* Theory.PAminus ℒₒᵣ := by
  intro σ h
  rcases h <;> simp[models_def, ←le_iff_eq_or_lt]
  case addAssoc => intro l m n; exact add_assoc l m n
  case addComm  => intro m n; exact add_comm m n
  case mulAssoc => intro l m n; exact mul_assoc l m n
  case mulComm  => intro m n; exact mul_comm m n
  case addEqOfLt => intro m n h; exact ⟨n - m, Nat.add_sub_of_le (le_of_lt h)⟩
  case oneLeOfZeroLt => intro n hn; exact hn
  case mulLtMul => rintro l m n h hl; exact (mul_lt_mul_right hl).mpr h
  case distr => intro l m n; exact Nat.mul_add l m n
  case ltTrans => intro l m n; exact Nat.lt_trans
  case ltTri => intro n m; exact Nat.lt_trichotomy n m

lemma modelsSuccInd (σ : Subsentence ℒₒᵣ (k + 1)) : ℕ ⊧ (Arith.succInd σ) := by
  simp[succInd, models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons', Subformula.eval_substs]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih

lemma modelsPeano : ℕ ⊧* (Theory.IndScheme Set.univ ∪ Theory.PAminus ℒₒᵣ ∪ Theory.Eq ℒₒᵣ) :=
  by simp[Theory.IndScheme, modelsSuccInd, modelsTheoryPAminus]

end standardModel

theorem Peano.Consistent :
    System.Consistent (Theory.IndScheme Set.univ ∪ Theory.PAminus ℒₒᵣ ∪ Theory.Eq ℒₒᵣ) :=
  Sound.consistent_of_model standardModel.modelsPeano

variable (L : Language.{u}) [ORing L]

structure Cut (M : Type w) [s : Structure L M] where
  domain : Set M
  closedSucc : ∀ x ∈ domain, (ᵀ“#0 + 1”).bVal s ![x] ∈ domain
  closedLt : ∀ x y : M, Subformula.PVal s ![x, y] “#0 < #1” → y ∈ domain → x ∈ domain

structure ClosedCut (M : Type w) [s : Structure L M] extends Structure.ClosedSubset L M where
  closedLt : ∀ x y : M, Subformula.PVal s ![x, y] “#0 < #1” → y ∈ domain → x ∈ domain

end Arith

abbrev Theory.trueArith : Theory ℒₒᵣ := Structure.theory ℒₒᵣ ℕ

notation "𝐓𝐀" => Theory.trueArith

abbrev Language.oRingStar : Language := ℒₒᵣ + Language.unit

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

local notation "⋆" => star

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

lemma star_unbounded (n : ℕ) : ORingSymbol.numeral n < ⋆ := by
  have : ℕ⋆ ⊧ (“!!(Subterm.Operator.numeral ℒₒᵣ⋆ n) < ⋆” : Sentence ℒₒᵣ⋆) :=
    models_union_trueArithWithStarUnbounded
      (Set.mem_iUnion_of_mem (n + 1) (Set.mem_union_right _ $ Set.mem_range_self $ Fin.last n))
  simpa [models_iff] using this

end Nonstandard

end

end Arith

end FirstOrder

end LO
