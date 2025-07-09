import Foundation.FirstOrder.Incompleteness.StandardProvability.FormalizedArithmetic

/-!

# Formalized theory $\mathsf{R_0}$

-/

namespace LO.FirstOrder

variable {L : Language}

section

open Lean PrettyPrinter Delaborator

syntax:max "let " ident " := " term:max first_order_term:61* "; " first_order_formula:0 : first_order_formula
syntax:max "let' " ident " := " term:max first_order_term:61* "; " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula[$binders* | $fbinders* | let $x:ident := $f:term $vs:first_order_term* ; $φ:first_order_formula]) =>
    `(⤫formula[$binders* | $fbinders* | ∃ $x, !$f:term #0 $vs:first_order_term* ∧ $φ])
  | `(⤫formula[$binders* | $fbinders* | let' $x:ident := $f:term $vs:first_order_term* ; $φ:first_order_formula]) =>
    `(⤫formula[$binders* | $fbinders* | ∀ $x, !$f:term #0 $vs:first_order_term* → $φ])

end

namespace Theory

inductive R0' : ArithmeticTheory
  | eq_refl : R0' “∀ x, x = x”
  | replace (φ : SyntacticSemiformula ℒₒᵣ 1) : R0' “∀ x y, x = y → !φ x → !φ y”
  | Ω₁ (n m : ℕ)  : R0' “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ)  : R0' “↑n * ↑m = ↑(n * m)”
  | Ω₃ (n m : ℕ)  : n ≠ m → R0' “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : R0' “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”

notation "𝐑₀'" => R0'

abbrev addR0' (T : ArithmeticTheory) : ArithmeticTheory := T + 𝐑₀'

end Theory

namespace Arithmetic
/-


namespace R0'

variable {M : Type*} [Nonempty M] [s : Structure ℒₒᵣ M] [M ⊧ₘ* 𝐑₀'] {a b c : M}

abbrev eql (x y : M) : Prop := s.rel Language.Eq.eq ![x, y]

abbrev add (x y : M) : M := s.func Language.Add.add ![x, y]

abbrev mul (x y : M) : M := s.func Language.Mul.mul ![x, y]

lemma operator_eq_eq (v : Fin 2 → M) : (Semiformula.Operator.Eq.eq (L := ℒₒᵣ)).val v = eql (v 0) (v 1) := by
  rw [Matrix.fun_eq_vec_two (v := v)]; simp; rfl

lemma operator_lt_eq : (Semiformula.Operator.LT.lt (L := ℒₒᵣ)).val ![a, b] = s.rel Language.LT.lt ![a, b] := rfl

@[simp] lemma eq_refl (a : M) : eql a a := by
  have := by simpa using ModelsTheory.models M Theory.R0'.eq_refl (fun _ ↦ a)
  exact this a

lemma eq_symm {a b : M} : eql a b → eql b a := fun h ↦ by
  have : ∀ x y, eql x y → eql x a → eql y a := by
    simpa [operator_eq_eq] using ModelsTheory.models M (Theory.R0'.replace “x. x = &0”) (fun _ ↦ a)
  exact this a b h (by simp)

lemma eq_trans {a b c : M} : eql a b → eql b c → eql a c := fun hab hbc ↦ by
  have := by simpa [operator_eq_eq] using ModelsTheory.models M (Theory.R0'.replace “x. &0 = x”) (fun _ ↦ a)
  exact this b c hbc hab

lemma add_ext {a₁ a₂ b₁ b₂ : M} (ha : eql a₁ a₂) (hb : eql b₁ b₂) :
    eql (s.func Language.Add.add ![a₁, b₁]) (s.func Language.Add.add ![a₂, b₂]) := by
  have e : eql (s.func Language.Add.add ![a₁, b₁]) (s.func Language.Add.add ![a₂, b₁]) := by
    have := by simpa [operator_eq_eq] using ModelsTheory.models M (Theory.R0'.replace “x. &0 + &1 = x + &1”) (a₁ :>ₙ fun _ ↦ b₁)
    exact this a₁ a₂ ha (by simp)
  have := by simpa [operator_eq_eq] using ModelsTheory.models M (Theory.R0'.replace “x. &0 + &1 = &2 + x”) (a₁ :>ₙ b₁ :>ₙ fun _ ↦ a₂)
  exact this b₁ b₂ hb e

lemma mul_ext {a₁ a₂ b₁ b₂ : M} (ha : eql a₁ a₂) (hb : eql b₁ b₂) :
    eql (s.func Language.Mul.mul ![a₁, b₁]) (s.func Language.Mul.mul ![a₂, b₂]) := by
  have e : eql (s.func Language.Mul.mul ![a₁, b₁]) (s.func Language.Mul.mul ![a₂, b₁]) := by
    have := by simpa [operator_eq_eq] using ModelsTheory.models M (Theory.R0'.replace “x. &0 * &1 = x * &1”) (a₁ :>ₙ fun _ ↦ b₁)
    exact this a₁ a₂ ha (by simp)
  have := by simpa [operator_eq_eq] using ModelsTheory.models M (Theory.R0'.replace “x. &0 * &1 = &2 * x”) (a₁ :>ₙ b₁ :>ₙ fun _ ↦ a₂)
  exact this b₁ b₂ hb e

noncomputable instance : 𝐄𝐐 ⪯ 𝐑₀' := Entailment.WeakerThan.ofAxm! <| by {
  intro φ hp
  cases hp
  · apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
    simp [operator_eq_eq]
  · apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
    simp [operator_eq_eq]; exact eq_symm
  · apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
    simp [operator_eq_eq]; exact eq_trans
  case funcExt k f =>
    match k, f with
    | _, Language.Zero.zero =>
      apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
      simp [operator_eq_eq]
    | _, Language.One.one =>
      apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
      simp [operator_eq_eq]
    | _, Language.Add.add =>
      apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
      simp [operator_eq_eq, Semiterm.val_func]
      intro h; rw [Matrix.fun_eq_vec_two (v := fun i : Fin 2 ↦ f i), Matrix.fun_eq_vec_two (v := fun i : Fin 2 ↦ f (2 + i))]
      apply add_ext (by simpa using h 0) (by simpa using h 1)
    | _, Language.Mul.mul =>
      apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
      simp [operator_eq_eq, Semiterm.val_func]
      intro h; rw [Matrix.fun_eq_vec_two (v := fun i : Fin 2 ↦ f i), Matrix.fun_eq_vec_two (v := fun i : Fin 2 ↦ f (2 + i))]
      apply mul_ext (by simpa using h 0) (by simpa using h 1)
  case relExt k R =>
    match k, R with
    | _, Language.Eq.eq =>
      apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
      simp [operator_eq_eq, Semiterm.val_func, Semiformula.eval_rel]
      rw [Matrix.fun_eq_vec_two (v := fun i : Fin 2 ↦ f i), Matrix.fun_eq_vec_two (v := fun i : Fin 2 ↦ f (2 + i))]
      intro hs h;
      have e20 : eql (f 2) (f 0) := by simpa using eq_symm (hs 0)
      have e01 : eql (f 0) (f 1) := by simpa using h
      have e13 : eql (f 1) (f 3) := by simpa using (hs 1)
      simpa using eq_trans (eq_trans e20 e01) e13
    | _, Language.LT.lt =>
      apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
      simp [operator_eq_eq, Semiterm.val_func, Semiformula.eval_rel]
      rw [Matrix.fun_eq_vec_two (v := fun i : Fin 2 ↦ f i), Matrix.fun_eq_vec_two (v := fun i : Fin 2 ↦ f (2 + i))]
      intro hs h;



}

-/

open LO.ISigma1.Metamath

noncomputable instance R0'.subtheoryOfR0 : 𝐑₀' ⪯ 𝐑₀ := Entailment.WeakerThan.ofAxm! <| by
  intro φ hp
  rcases hp
  · apply complete <| oRing_consequence_of.{0} _ _ <| fun M _ _ => by simp [models_iff]
  · apply complete <| oRing_consequence_of.{0} _ _ <| fun M _ _ => by simp [models_iff]
  case Ω₁ n m => exact Entailment.by_axm _ (R0.Ω₁ n m)
  case Ω₂ n m => exact Entailment.by_axm _ (R0.Ω₂ n m)
  case Ω₃ n m h => exact Entailment.by_axm _ (R0.Ω₃ n m h)
  case Ω₄ n => exact Entailment.by_axm _ (R0.Ω₄ n)

variable {T : ArithmeticTheory} [𝐑₀ ⪯ T]

lemma add_cobhamR0' {φ} : T ⊢! φ ↔ T + 𝐑₀' ⊢! φ := by
  constructor
  · intro h; exact Entailment.wk! (by simp [Theory.add_def]) h
  · intro h
    exact Entailment.StrongCut.cut!
      (by
        rintro φ (hp | hp)
        · exact Entailment.by_axm _ hp
        · have : 𝐑₀' ⊢! φ := Entailment.by_axm _ hp
          have : 𝐑₀ ⊢! φ := Entailment.WeakerThan.pbl this
          exact Entailment.WeakerThan.pbl this) h

end Arithmetic

end LO.FirstOrder

section

open Classical

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

section

variable {L : Language} [L.Encodable] [L.LORDefinable]

def singleton (φ : SyntacticFormula L) :
    Theory.Delta1Definable {φ} where
  ch := .ofZero (.mkSigma “x. x = ↑⌜φ⌝” (by simp)) _
  mem_iff {ψ} := by simp
  isDelta1 := Arithmetic.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

@[simp] lemma singleton_toTDef_ch_val (φ : FirstOrder.SyntacticFormula L) :
    letI := singleton φ
    (Theory.Delta1Definable.toTDef {φ}).ch.val = “x. x = ↑⌜φ⌝” := rfl

end

namespace InternalArithmetic

namespace Theory.R0'

def eqRefl : FirstOrder.Theory.Delta1Definable {(“∀ x, x = x” : SyntacticFormula ℒₒᵣ)} := singleton _

def replace :
    FirstOrder.Theory.Delta1Definable {“∀ x y, x = y → !φ x → !φ y” | φ : SyntacticSemiformula ℒₒᵣ 1} where
  ch := .mkDelta
    (.mkSigma
      “p.
      ∃ q < p, !p⌜ℒₒᵣ⌝.isSemiformula.sigma 1 q ∧
      let x0 := qqBvarDef 0;
      let x1 := qqBvarDef 1;
      let eq := qqEQDef x1 x0;
      let v0 := mkVec₁Def x0;
      let v1 := mkVec₁Def x1;
      let q0 := psubsts ℒₒᵣDef v1 q;
      let q1 := psubsts ℒₒᵣDef v0 q;
      let imp0 := p⌜ℒₒᵣ⌝.impDef q0 q1;
      let imp1 := p⌜ℒₒᵣ⌝.impDef eq imp0;
      let all0 := qqAllDef imp1;
      !qqAllDef p all0” (by simp))
    (.mkPi
      “p.
      ∃ q < p, !p⌜ℒₒᵣ⌝.isSemiformula.pi 1 q ∧
      let' x0 := qqBvarDef 0;
      let' x1 := qqBvarDef 1;
      let' eq := qqEQDef x1 x0;
      let' v0 := mkVec₁Def x0;
      let' v1 := mkVec₁Def x1;
      let' q0 := psubsts ℒₒᵣDef v1 q;
      let' q1 := psubsts ℒₒᵣDef v0 q;
      let' imp0 := p⌜ℒₒᵣ⌝.impDef q0 q1;
      let' imp1 := p⌜ℒₒᵣ⌝.impDef eq imp0;
      let' all0 := qqAllDef imp1;
      !qqAllDef p all0” (by simp))
  mem_iff {φ} := by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma, (Language.isSemiformula_defined (LOR (V := ℕ))).df.iff,
      (Language.substs_defined (LOR (V := ℕ))).df.iff, (Language.imp_defined (LOR (V := ℕ))).df.iff]
    -/
    simp only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, Set.mem_setOf_eq,
      HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.val_mkDelta,
      HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT, Semiterm.val_bvar,
      Matrix.cons_val_fin_one, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
      Matrix.comp_vecCons', Semiterm.val_operator₀, Structure.numeral_eq_numeral,
      ORingStruc.one_eq_one, Matrix.cons_val_zero, Matrix.constant_eq_singleton,
      (Language.isSemiformula_defined (LOR (V := ℕ))).df.iff, Matrix.cons_val_one, Matrix.vecHead,
      Semiformula.eval_ex, ORingStruc.zero_eq_zero, eval_qqBvarDef, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, eval_qqEQDef,
      Matrix.cons_val_three, Fin.succ_one_eq_two, eval_mkVec₁Def, Matrix.cons_app_six,
      Matrix.cons_app_five, Matrix.cons_val_four, Matrix.cons_val_succ,
      (Language.substs_defined (LOR (V := ℕ))).df.iff, Matrix.cons_app_seven,
      (Language.imp_defined (LOR (V := ℕ))).df.iff, eval_qqAllDef,
      Language.TermRec.Construction.cons_app_11, Language.TermRec.Construction.cons_app_10,
      Language.TermRec.Construction.cons_app_9, Matrix.cons_app_eight,
      LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨x, _, hx, h⟩
      rcases hx.sound with ⟨q, rfl⟩
      exact ⟨q, by symm; apply (quote_inj_iff (V := ℕ)).mp; simpa using h⟩
    · rintro ⟨q, rfl⟩
      exact ⟨⌜q⌝, by
        suffices ⌜q⌝ < ^∀ ^∀ (^#1 ^= ^#0 ^→[(ℒₒᵣ).codeIn ℕ] ((ℒₒᵣ).codeIn ℕ).substs (^#1 ∷ 0) ⌜q⌝ ^→[(ℒₒᵣ).codeIn ℕ] ⌜q⌝) by
          simpa [subst_eq_self₁, Matrix.constant_eq_singleton]
        refine lt_trans ?_ (lt_forall _)
        refine lt_trans ?_ (lt_forall _)
        refine lt_trans ?_ (lt_or_right _ _)
        exact lt_or_right _ _, by simp [Matrix.constant_eq_singleton]⟩
  isDelta1 := Arithmetic.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V := V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff]
    -/
    simp only [Fin.isValue, Nat.reduceAdd, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.sigma_mkDelta,
      HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT, Semiterm.val_bvar,
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
      Semiterm.val_operator₀, Structure.numeral_eq_numeral, ORingStruc.one_eq_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.constant_eq_singleton,
      (Language.isSemiformula_defined (LOR (V := V))).df.iff, Matrix.cons_val_one, Matrix.vecHead,
      Semiformula.eval_ex, ORingStruc.zero_eq_zero, eval_qqBvarDef, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, eval_qqEQDef,
      Matrix.cons_val_three, Fin.succ_one_eq_two, eval_mkVec₁Def, Matrix.cons_app_six,
      Matrix.cons_app_five, Matrix.cons_val_four, Matrix.cons_val_succ,
      (Language.substs_defined (LOR (V := V))).df.iff, Matrix.cons_app_seven,
      (Language.imp_defined (LOR (V := V))).df.iff, eval_qqAllDef,
      Language.TermRec.Construction.cons_app_11, Language.TermRec.Construction.cons_app_10,
      Language.TermRec.Construction.cons_app_9, Matrix.cons_app_eight,
      LogicalConnective.Prop.and_eq, exists_eq_left, HierarchySymbol.Semiformula.pi_mkDelta,
      HierarchySymbol.Semiformula.val_mkPi,
      (Language.isSemiformula_defined (LOR (V := V))).proper.iff', Semiformula.eval_all,
      LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq, forall_eq]

def Ω₁ :
    FirstOrder.Theory.Delta1Definable {φ : SyntacticFormula ℒₒᵣ | ∃ n m : ℕ, φ = “↑n + ↑m = ↑(n + m)”} where
  ch := .mkDelta
    (.mkSigma “p.
      ∃ n < p, ∃ m < p,
      let numn := numeralGraph n;
      let numm := numeralGraph m;
      let lhd := qqAddGraph numn numm;
      let rhd := numeralGraph (n + m);
      !qqEQDef p lhd rhd” (by simp))
    (.mkPi “p.
      ∃ n < p, ∃ m < p,
      let' numn := numeralGraph n;
      let' numm := numeralGraph m;
      let' lhd := qqAddGraph numn numm;
      let' rhd := numeralGraph (n + m);
      ∀ p', !qqEQDef p' lhd rhd → p = p'” (by simp))
  mem_iff {φ} := by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma, (Language.isSemiformula_defined (LOR (V := ℕ))).df.iff,
      (Language.substs_defined (LOR (V := ℕ))).df.iff, (Language.imp_defined (LOR (V := ℕ))).df.iff]
    -/
    simp only [Set.mem_setOf_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.vecHead, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.constant_eq_singleton,
      eval_numeralGraph, eval_qqAddGraph, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Add.add,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨n, _, m, _, h⟩
      use n; use m
      exact (quote_inj_iff (V := ℕ)).mp (by simpa using h)
    · rintro ⟨n, m, rfl⟩
      refine ⟨n, by
          simpa using lt_trans
            (lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←PeanoMinus.le_def]) (lt_qqAdd_left _ _))
            (lt_qqEQ_left _ _),
        m, by
          simpa using lt_trans
            (lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←PeanoMinus.le_def]) (lt_qqAdd_right _ _))
            (lt_qqEQ_left _ _),
        by simp⟩
  isDelta1 := Arithmetic.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V := V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff]
    -/
    simp only [Fin.isValue, Nat.reduceAdd, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
      Semiformula.eval_ex, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.constant_eq_singleton,
      eval_numeralGraph, eval_qqAddGraph, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Add.add,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left,
      HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
      Semiformula.eval_all, LogicalConnective.HomClass.map_imply, Semiformula.eval_operator_two,
      Matrix.cons_app_seven, Structure.Eq.eq, LogicalConnective.Prop.arrow_eq, forall_eq]

def Ω₂ :
    FirstOrder.Theory.Delta1Definable {φ : SyntacticFormula ℒₒᵣ | ∃ n m : ℕ, φ = “↑n * ↑m = ↑(n * m)”} where
  ch := .mkDelta
    (.mkSigma “p.
      ∃ n < p, ∃ m < p,
      let numn := numeralGraph n;
      let numm := numeralGraph m;
      let lhd := qqMulGraph numn numm;
      let rhd := numeralGraph (n * m);
      !qqEQDef p lhd rhd” (by simp))
    (.mkPi “p.
      ∃ n < p, ∃ m < p,
      let' numn := numeralGraph n;
      let' numm := numeralGraph m;
      let' lhd := qqMulGraph numn numm;
      let' rhd := numeralGraph (n * m);
      ∀ p', !qqEQDef p' lhd rhd → p = p'” (by simp))
  mem_iff {φ} := by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma, (Language.isSemiformula_defined (LOR (V := ℕ))).df.iff,
      (Language.substs_defined (LOR (V := ℕ))).df.iff, (Language.imp_defined (LOR (V := ℕ))).df.iff]
    -/
    simp only [Set.mem_setOf_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.vecHead, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.constant_eq_singleton,
      eval_numeralGraph, eval_qqMulGraph, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Mul.mul,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨n, _, m, _, h⟩
      use n; use m
      exact (quote_inj_iff (V := ℕ)).mp (by simpa using h)
    · rintro ⟨n, m, rfl⟩
      refine ⟨n, by
          simpa using lt_trans
            (lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←PeanoMinus.le_def]) (lt_qqMul_left _ _))
            (lt_qqEQ_left _ _),
        m, by
          simpa using lt_trans
            (lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←PeanoMinus.le_def]) (lt_qqMul_right _ _))
            (lt_qqEQ_left _ _),
        by simp⟩
  isDelta1 := Arithmetic.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V := V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff]
    -/
    simp only [Fin.isValue, Nat.reduceAdd, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
      Semiformula.eval_ex, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.constant_eq_singleton,
      eval_numeralGraph, eval_qqMulGraph, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Mul.mul,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left,
      HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
      Semiformula.eval_all, LogicalConnective.HomClass.map_imply, Semiformula.eval_operator_two,
      Matrix.cons_app_seven, Structure.Eq.eq, LogicalConnective.Prop.arrow_eq, forall_eq]

def Ω₃ :
    FirstOrder.Theory.Delta1Definable {φ : SyntacticFormula ℒₒᵣ | ∃ n m : ℕ, n ≠ m ∧ φ = “↑n ≠ ↑m”} where
  ch := .mkDelta
    (.mkSigma “p. ∃ n < p, ∃ m < p, n ≠ m ∧
      let numn := numeralGraph n;
      let numm := numeralGraph m;
      !qqNEQDef p numn numm” (by simp))
    (.mkPi “p. ∃ n < p, ∃ m < p, n ≠ m ∧
      let' numn := numeralGraph n;
      let' numm := numeralGraph m;
      ∀ p', !qqNEQDef p' numn numm → p = p'” (by simp))
  mem_iff {φ} := by
    /-
    simp?
    -/
    simp only [ne_eq, Set.mem_setOf_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.vecHead, LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
      Semiformula.eval_operator_two, Matrix.cons_val_zero, Structure.Eq.eq,
      LogicalConnective.Prop.neg_eq, Semiformula.eval_ex, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, Matrix.constant_eq_singleton, eval_numeralGraph, Matrix.cons_val_four,
      Fin.succ_one_eq_two, Matrix.cons_val_succ, eval_qqNEQDef, LogicalConnective.Prop.and_eq,
      exists_eq_left]
    constructor
    · rintro ⟨n, _, m, _, ne, h⟩
      refine ⟨n, m, ne, ?_⟩
      exact (quote_inj_iff (V := ℕ)).mp
        (by simp only [quote_neg, Semiformula.quote_eq',
              quote_numeral_eq_numeral, natCast_nat]
            rw [neg_eq (by simp) (by simp)]; simpa using h)
    · rintro ⟨n, m, ne, rfl⟩
      refine ⟨n, by
          simp only [quote_neg, Semiformula.quote_eq', quote_numeral_eq_numeral, natCast_nat]
          rw [neg_eq (by simp) (by simp)]
          exact lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←PeanoMinus.le_def]) (lt_qqNEQ_left _ _),
        m, by
          simp only [quote_neg, Semiformula.quote_eq', quote_numeral_eq_numeral, natCast_nat]
          rw [neg_eq (by simp) (by simp)]
          exact lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←PeanoMinus.le_def]) (lt_qqNEQ_right _ _), ne, ?_⟩
      simp only [quote_neg, Semiformula.quote_eq', quote_numeral_eq_numeral, natCast_nat]
      rw [neg_eq (by simp) (by simp)]
  isDelta1 := Arithmetic.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by simp

private lemma quote_disjLt_eq (n : ℕ) :
    ⌜(disjLt (fun i ↦ “#0 = ↑i”) n : SyntacticSemiformula ℒₒᵣ 1)⌝ =
    ^⋁ substItr (^#0 ∷ 0) (^#1 ^= ^#0) n := by
  induction n
  case zero => simp
  case succ n ih =>
    suffices ^#0 ^= numeral n = substs ℒₒᵣ (numeral n ∷ ^#0 ∷ 0) (^#1 ^= ^#0) by simpa [ih]
    rw [substs_eq (by simp) (by simp)]; simp

def Ω₄ :
    FirstOrder.Theory.Delta1Definable {(“∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i” : SyntacticFormula ℒₒᵣ) | n} where
  ch := .mkDelta
    (.mkSigma “p. ∃ n < p,
      let numn := numeralGraph n;
      let x₀ := qqBvarDef 0;
      let x₁ := qqBvarDef 1;
      let lhd := qqLTDef x₀ numn;
      let v := consDef x₀ 0;
      let e := qqEQDef x₁ x₀;
      let ti := substItrDef v e n;
      let rhd := qqDisjDef ti;
      let iff := p⌜ℒₒᵣ⌝.qqIffDef lhd rhd;
      !qqAllDef p iff” (by simp))
    (.mkPi “p. ∃ n < p,
      let' numn := numeralGraph n;
      let' x₀ := qqBvarDef 0;
      let' x₁ := qqBvarDef 1;
      let' lhd := qqLTDef x₀ numn;
      let' v := consDef x₀ 0;
      let' e := qqEQDef x₁ x₀;
      let' ti := substItrDef v e n;
      let' rhd := qqDisjDef ti;
      let' iff := p⌜ℒₒᵣ⌝.qqIffDef lhd rhd;
      !qqAllDef p iff” (by simp))
  mem_iff {p} := by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma, (Language.isSemiformula_defined (LOR (V := ℕ))).df.iff,
      (Language.substs_defined (LOR (V := ℕ))).df.iff, (Language.imp_defined (LOR (V := ℕ))).df.iff,
      (iff_defined (LOR (V := ℕ))).df.iff]
    -/
    simp only [Nat.reduceAdd, Fin.isValue, Set.mem_setOf_eq, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_fin_one, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead, Matrix.constant_eq_singleton,
      eval_numeralGraph, Semiterm.val_operator₀, Structure.numeral_eq_numeral,
      ORingStruc.zero_eq_zero, eval_qqBvarDef, ORingStruc.one_eq_one, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_three,
      Fin.succ_one_eq_two, eval_qqLTDef, eval_cons, Matrix.cons_val_four, Matrix.cons_val_succ,
      eval_qqEQDef, Matrix.cons_app_seven, Matrix.cons_app_six, Matrix.cons_app_five,
      substItr_defined_iff, eval_qqDisj, (iff_defined (LOR (V := ℕ))).df.iff,
      Language.TermRec.Construction.cons_app_10, Language.TermRec.Construction.cons_app_9,
      Matrix.cons_app_eight, eval_qqAllDef, LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨n, _, h⟩
      use n
      symm;
      exact (quote_inj_iff (V := ℕ)).mp (by simpa [quote_disjLt_eq] using h)
    · rintro ⟨n, rfl⟩
      refine ⟨n, by
        simp only [Fin.isValue, Semiformula.quote_all, Nat.reduceAdd, quote_iff,
          Semiformula.quote_lt', Semiterm.quote_bvar, Fin.val_eq_zero, natCast_nat,
          quote_numeral_eq_numeral]
        apply lt_trans ?_ (lt_forall _)
        apply lt_trans ?_ (lt_iff_left _ _)
        apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←PeanoMinus.le_def]) (lt_qqLT_right _ _), ?_⟩
      simp [quote_disjLt_eq]
  isDelta1 := Arithmetic.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V := V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff,
      (iff_defined (LOR (V := V))).df.iff]
    -/
    simp only [Fin.isValue, Nat.reduceAdd, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.vecHead,
      Matrix.constant_eq_singleton, eval_numeralGraph, Semiterm.val_operator₀,
      Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero, eval_qqBvarDef, ORingStruc.one_eq_one,
      Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_three, Fin.succ_one_eq_two, eval_qqLTDef, eval_cons, Matrix.cons_val_four,
      Matrix.cons_val_succ, eval_qqEQDef, Matrix.cons_app_seven, Matrix.cons_app_six,
      Matrix.cons_app_five, substItr_defined_iff, eval_qqDisj,
      (iff_defined (LOR (V := V))).df.iff, Language.TermRec.Construction.cons_app_10,
      Language.TermRec.Construction.cons_app_9, Matrix.cons_app_eight, eval_qqAllDef,
      LogicalConnective.Prop.and_eq, exists_eq_left, HierarchySymbol.Semiformula.pi_mkDelta,
      HierarchySymbol.Semiformula.val_mkPi, Semiformula.eval_all,
      LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq, forall_eq]

end Theory.R0'

open Theory.R0'

instance Theory.R0'Delta1Definable : 𝐑₀'.Delta1Definable := (eqRefl.add <| replace.add <| Ω₁.add <| Ω₂.add <| Ω₃.add Ω₄).ofEq <| by
    ext φ; constructor
    · rintro (hφ | hφ | hφ | hφ | hφ | hφ)
      · rcases hφ; exact Theory.R0'.eq_refl
      · rcases hφ with ⟨φ, rfl⟩; exact FirstOrder.Theory.R0'.replace φ
      · rcases hφ with ⟨n, m, rfl⟩; exact FirstOrder.Theory.R0'.Ω₁ n m
      · rcases hφ with ⟨n, m, rfl⟩; exact FirstOrder.Theory.R0'.Ω₂ n m
      · rcases hφ with ⟨n, m, ne, rfl⟩; exact FirstOrder.Theory.R0'.Ω₃ n m ne
      · rcases hφ with ⟨n, rfl⟩; exact FirstOrder.Theory.R0'.Ω₄ n
    · intro hφ; cases hφ
      case eq_refl => left; simp
      case replace φ => right; left; exact ⟨φ, by simp⟩
      case Ω₁ n m => right; right; left; exact ⟨n, m, by simp⟩
      case Ω₂ n m => right; right; right; left; exact ⟨n, m, by simp⟩
      case Ω₃ n m ne => right; right; right; right; left; exact ⟨n, m, ne, by simp⟩
      case Ω₄ n => right; right; right; right; right; exact ⟨n, by simp⟩

abbrev Theory.R0' : ⌜ℒₒᵣ⌝[V].Theory := 𝐑₀'.codeIn V

abbrev TTheory.R0' : ⌜ℒₒᵣ⌝[V].TTheory := 𝐑₀'.tCodeIn V

notation "⌜𝐑₀'⌝" => TTheory.R0'
notation "⌜𝐑₀'⌝[" V "]" => TTheory.R0' (V := V)

namespace Theory.R0'

noncomputable def eqRefl.proof : ⌜𝐑₀'⌝[V] ⊢ (#'0 =' #'0).all := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_left
  unfold eqRefl
  simp [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve, numeral_eq_natCast]
  simp [qqAll, nat_cast_pair, qqEQ, qqRel, cons_absolute, qqBvar]

noncomputable def replace.proof (φ : ⌜ℒₒᵣ⌝[V].Semiformula (0 + 1)) :
    ⌜𝐑₀'⌝[V] ⊢ (#'1 =' #'0 ➝ φ^/[(#'1).sing] ➝ φ^/[(#'0).sing]).all.all := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold replace
  suffices
    ∃ x < ^∀ ^∀ (^#1 ^= ^#0 ^→[⌜ℒₒᵣ⌝] substs ℒₒᵣ (^#1 ∷ 0) φ.val ^→[⌜ℒₒᵣ⌝] substs ℒₒᵣ (^#0 ∷ 0) φ.val),
      IsSemiformula ℒₒᵣ 1 x ∧
        ^#1 ^= ^#0 ^→[⌜ℒₒᵣ⌝] substs ℒₒᵣ (^#1 ∷ 0) φ.val ^→[⌜ℒₒᵣ⌝] substs ℒₒᵣ (^#0 ∷ 0) φ.val =
          ^#1 ^= ^#0 ^→[⌜ℒₒᵣ⌝] substs ℒₒᵣ (^#1 ∷ 0) x ^→[⌜ℒₒᵣ⌝] substs ℒₒᵣ (^#0 ∷ 0) x by
    simpa [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve,
      (Language.isSemiformula_defined (LOR (V := V))).df.iff,
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff]
  refine ⟨φ.val, ?_, by simpa using φ.prop, rfl⟩
  · rw [subst_eq_self₁ (by simpa using φ.prop)]
    refine lt_trans ?_ (lt_forall _)
    refine lt_trans ?_ (lt_forall _)
    refine lt_trans ?_ (lt_or_right _ _)
    exact lt_or_right _ _

noncomputable def Ω₁.proof (n m : V) :
    ⌜𝐑₀'⌝[V] ⊢ (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m) := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold Ω₁
  suffices
    ∃ x < numeral n ^+ numeral m ^= numeral (n + m),
      ∃ y < numeral n ^+ numeral m ^= numeral (n + m),
        numeral n ^+ numeral m ^= numeral (n + m) = numeral x ^+ numeral y ^= numeral (x + y) by
    simpa [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve]
  refine ⟨n, ?_, m, ?_, rfl⟩
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqAdd_left _ _)
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqAdd_right _ _)

noncomputable def Ω₂.proof (n m : V) :
    ⌜𝐑₀'⌝[V] ⊢ (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m) := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold Ω₂
  suffices
    ∃ x < numeral n ^* numeral m ^= numeral (n * m),
      ∃ y < numeral n ^* numeral m ^= numeral (n * m),
        numeral n ^* numeral m ^= numeral (n * m) = numeral x ^* numeral y ^= numeral (x * y) by
    simpa [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve]
  refine ⟨n, ?_, m, ?_, rfl⟩
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqMul_left _ _)
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqMul_right _ _)

noncomputable def Ω₃.proof {n m : V} (ne : n ≠ m) : ⌜𝐑₀'⌝[V] ⊢ ↑n ≠' ↑m := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold Ω₃
  suffices
    ∃ x < numeral n ^≠ numeral m,
      ∃ y < numeral n ^≠ numeral m, ¬x = y ∧ numeral n ^≠ numeral m = numeral x ^≠ numeral y by
    simpa [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve]
  refine ⟨n, ?_, m, ?_, ne, rfl⟩
  · exact lt_of_le_of_lt (by simp) (lt_qqNEQ_left _ _)
  · exact lt_of_le_of_lt (by simp) (lt_qqNEQ_right _ _)

noncomputable def Ω₄.proof (n : V): ⌜𝐑₀'⌝[V] ⊢ (#'0 <' ↑n ⭤ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  unfold Ω₄
  suffices
    ∃ x < ^∀ ⌜ℒₒᵣ⌝.iff (^#0 ^< numeral n) (^⋁ substItr (^#0 ∷ 0) (^#1 ^= ^#0) n),
      ⌜ℒₒᵣ⌝.iff (^#0 ^< numeral n) (^⋁ substItr (^#0 ∷ 0) (^#1 ^= ^#0) n) =
        ⌜ℒₒᵣ⌝.iff (^#0 ^< numeral x) (^⋁ substItr (^#0 ∷ 0) (^#1 ^= ^#0) x) by
    simpa [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve,
      (iff_defined (LOR (V := V))).df.iff]
  refine ⟨n, ?_, rfl⟩
  apply lt_trans ?_ (lt_forall _)
  apply lt_trans ?_ (lt_iff_left _ _)
  apply lt_of_le_of_lt (by simp) (lt_qqLT_right _ _)

end Theory.R0'

instance Theory.addR0'Delta1Definable (T : ArithmeticTheory) [d : T.Delta1Definable] : (T + 𝐑₀').Delta1Definable :=
  d.add Theory.R0'Delta1Definable
section

abbrev _root_.LO.FirstOrder.ArithmeticTheory.AddR₀TTheory
    (T : ArithmeticTheory) [T.Delta1Definable] (V) [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁] : ⌜ℒₒᵣ⌝[V].TTheory := (T + 𝐑₀').tCodeIn V

scoped [LO.ISigma1.Metamath] infix:100 "†" => LO.FirstOrder.ArithmeticTheory.AddR₀TTheory

variable {T : ArithmeticTheory} [T.Delta1Definable]

@[simp] lemma R₀'_subset_AddR₀ : ⌜𝐑₀'⌝[V] ⊆ T†V := Set.subset_union_right

@[simp] lemma theory_subset_AddR₀ : T.tCodeIn V ⊆ T†V := FirstOrder.Theory.Delta1Definable.add_subset_left _ _

noncomputable instance : R₀Theory (T†V) where
  refl := Language.Theory.TProof.ofSubset (by simp) Theory.R0'.eqRefl.proof
  replace := fun φ ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.R0'.replace.proof φ)
  add := fun n m ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.R0'.Ω₁.proof n m)
  mul := fun n m ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.R0'.Ω₂.proof n m)
  ne := fun h ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.R0'.Ω₃.proof h)
  ltNumeral := fun n ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.R0'.Ω₄.proof n)

end

end InternalArithmetic

open InternalArithmetic

section

variable (T : ArithmeticTheory) [T.Delta1Definable]

/-- Provability predicate for arithmetic stronger than $\mathbf{R_0}$. -/
def _root_.LO.FirstOrder.ArithmeticTheory.Provable (φ : V) : Prop := ((T + 𝐑₀').codeIn V).Provable φ

variable {T}

lemma provable_iff {σ : Sentence ℒₒᵣ} : T.Provable (⌜σ⌝ : V) ↔ T†V ⊢! ⌜σ⌝ := by
  simp [Language.Theory.TProvable.iff_provable]; rfl

/-- TODO: refactor name-/
lemma provable_iff' {φ : SyntacticFormula ℒₒᵣ} : T.Provable (⌜φ⌝ : V) ↔ T†V ⊢! ⌜φ⌝ := by
  simp [Language.Theory.TProvable.iff_provable]; rfl

section

variable (T)

def _root_.LO.FirstOrder.ArithmeticTheory.provable : 𝚺₁.Semisentence 1 := .mkSigma
  “p. !(T + 𝐑₀').tDef.prv p” (by simp)

lemma provable_defined : 𝚺₁-Predicate (T.Provable : V → Prop) via T.provable := by
  intro v; simp [ArithmeticTheory.provable, ArithmeticTheory.Provable, ((T + 𝐑₀').codeIn V).provable_defined.df.iff]

@[simp] lemma eval_provable (v) :
    Semiformula.Evalbm V v T.provable.val ↔ T.Provable (v 0) := (provable_defined T).df.iff v

instance provable_definable : 𝚺₁-Predicate (T.Provable : V → Prop) := (provable_defined T).to_definable

/-- instance for definability tactic-/
instance provable_definable' : 𝚺-[0 + 1]-Predicate (T.Provable : V → Prop) := provable_definable T

end

end

end LO.ISigma1.Metamath
