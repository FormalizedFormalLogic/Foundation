import Incompleteness.Arith.FormalizedArithmetic

/-!

# Formalized $\Sigma_1$-Completeness

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

inductive CobhamR0' : Theory ℒₒᵣ
  | eq_refl : CobhamR0' “∀ x, x = x”
  | replace (φ : SyntacticSemiformula ℒₒᵣ 1) : CobhamR0' “∀ x y, x = y → !φ x → !φ y”
  | Ω₁ (n m : ℕ)  : CobhamR0' “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ)  : CobhamR0' “↑n * ↑m = ↑(n * m)”
  | Ω₃ (n m : ℕ)  : n ≠ m → CobhamR0' “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : CobhamR0' “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”

notation "𝐑₀'" => CobhamR0'

abbrev addCobhamR0' (T : Theory ℒₒᵣ) : Theory ℒₒᵣ := T + 𝐑₀'

end Theory

namespace Arith
/-


namespace CobhamR0'

variable {M : Type*} [Nonempty M] [s : Structure ℒₒᵣ M] [M ⊧ₘ* 𝐑₀'] {a b c : M}

abbrev eql (x y : M) : Prop := s.rel Language.Eq.eq ![x, y]

abbrev add (x y : M) : M := s.func Language.Add.add ![x, y]

abbrev mul (x y : M) : M := s.func Language.Mul.mul ![x, y]

lemma operator_eq_eq (v : Fin 2 → M) : (Semiformula.Operator.Eq.eq (L := ℒₒᵣ)).val v = eql (v 0) (v 1) := by
  rw [Matrix.fun_eq_vec₂ (v := v)]; simp; rfl

lemma operator_lt_eq : (Semiformula.Operator.LT.lt (L := ℒₒᵣ)).val ![a, b] = s.rel Language.LT.lt ![a, b] := rfl

@[simp] lemma eq_refl (a : M) : eql a a := by
  have := by simpa using ModelsTheory.models M Theory.CobhamR0'.eq_refl (fun _ ↦ a)
  exact this a

lemma eq_symm {a b : M} : eql a b → eql b a := fun h ↦ by
  have : ∀ x y, eql x y → eql x a → eql y a := by
    simpa [operator_eq_eq] using ModelsTheory.models M (Theory.CobhamR0'.replace “x. x = &0”) (fun _ ↦ a)
  exact this a b h (by simp)

lemma eq_trans {a b c : M} : eql a b → eql b c → eql a c := fun hab hbc ↦ by
  have := by simpa [operator_eq_eq] using ModelsTheory.models M (Theory.CobhamR0'.replace “x. &0 = x”) (fun _ ↦ a)
  exact this b c hbc hab

lemma add_ext {a₁ a₂ b₁ b₂ : M} (ha : eql a₁ a₂) (hb : eql b₁ b₂) :
    eql (s.func Language.Add.add ![a₁, b₁]) (s.func Language.Add.add ![a₂, b₂]) := by
  have e : eql (s.func Language.Add.add ![a₁, b₁]) (s.func Language.Add.add ![a₂, b₁]) := by
    have := by simpa [operator_eq_eq] using ModelsTheory.models M (Theory.CobhamR0'.replace “x. &0 + &1 = x + &1”) (a₁ :>ₙ fun _ ↦ b₁)
    exact this a₁ a₂ ha (by simp)
  have := by simpa [operator_eq_eq] using ModelsTheory.models M (Theory.CobhamR0'.replace “x. &0 + &1 = &2 + x”) (a₁ :>ₙ b₁ :>ₙ fun _ ↦ a₂)
  exact this b₁ b₂ hb e

lemma mul_ext {a₁ a₂ b₁ b₂ : M} (ha : eql a₁ a₂) (hb : eql b₁ b₂) :
    eql (s.func Language.Mul.mul ![a₁, b₁]) (s.func Language.Mul.mul ![a₂, b₂]) := by
  have e : eql (s.func Language.Mul.mul ![a₁, b₁]) (s.func Language.Mul.mul ![a₂, b₁]) := by
    have := by simpa [operator_eq_eq] using ModelsTheory.models M (Theory.CobhamR0'.replace “x. &0 * &1 = x * &1”) (a₁ :>ₙ fun _ ↦ b₁)
    exact this a₁ a₂ ha (by simp)
  have := by simpa [operator_eq_eq] using ModelsTheory.models M (Theory.CobhamR0'.replace “x. &0 * &1 = &2 * x”) (a₁ :>ₙ b₁ :>ₙ fun _ ↦ a₂)
  exact this b₁ b₂ hb e

noncomputable instance : 𝐄𝐐 ≼ 𝐑₀' := System.Subtheory.ofAxm! <| by {
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
      intro h; rw [Matrix.fun_eq_vec₂ (v := fun i : Fin 2 ↦ f i), Matrix.fun_eq_vec₂ (v := fun i : Fin 2 ↦ f (2 + i))]
      apply add_ext (by simpa using h 0) (by simpa using h 1)
    | _, Language.Mul.mul =>
      apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
      simp [operator_eq_eq, Semiterm.val_func]
      intro h; rw [Matrix.fun_eq_vec₂ (v := fun i : Fin 2 ↦ f i), Matrix.fun_eq_vec₂ (v := fun i : Fin 2 ↦ f (2 + i))]
      apply mul_ext (by simpa using h 0) (by simpa using h 1)
  case relExt k R =>
    match k, R with
    | _, Language.Eq.eq =>
      apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
      simp [operator_eq_eq, Semiterm.val_func, Semiformula.eval_rel]
      rw [Matrix.fun_eq_vec₂ (v := fun i : Fin 2 ↦ f i), Matrix.fun_eq_vec₂ (v := fun i : Fin 2 ↦ f (2 + i))]
      intro hs h;
      have e20 : eql (f 2) (f 0) := by simpa using eq_symm (hs 0)
      have e01 : eql (f 0) (f 1) := by simpa using h
      have e13 : eql (f 1) (f 3) := by simpa using (hs 1)
      simpa using eq_trans (eq_trans e20 e01) e13
    | _, Language.LT.lt =>
      apply complete (consequence_iff.mpr fun M _ _ s f ↦ ?_)
      simp [operator_eq_eq, Semiterm.val_func, Semiformula.eval_rel]
      rw [Matrix.fun_eq_vec₂ (v := fun i : Fin 2 ↦ f i), Matrix.fun_eq_vec₂ (v := fun i : Fin 2 ↦ f (2 + i))]
      intro hs h;



}

-/

open LO.Arith

noncomputable instance CobhamR0'.subtheoryOfCobhamR0 : 𝐑₀' ≼ 𝐑₀ := System.Subtheory.ofAxm! <| by
  intro φ hp
  rcases hp
  · apply complete <| oRing_consequence_of.{0} _ _ <| fun M _ _ => by simp [models_iff]
  · apply complete <| oRing_consequence_of.{0} _ _ <| fun M _ _ => by simp [models_iff]
  case Ω₁ n m => exact System.by_axm _ (Theory.CobhamR0.Ω₁ n m)
  case Ω₂ n m => exact System.by_axm _ (Theory.CobhamR0.Ω₂ n m)
  case Ω₃ n m h => exact System.by_axm _ (Theory.CobhamR0.Ω₃ n m h)
  case Ω₄ n => exact System.by_axm _ (Theory.CobhamR0.Ω₄ n)

variable {T : Theory ℒₒᵣ} [𝐑₀ ≼ T]

lemma add_cobhamR0' {φ} : T ⊢! φ ↔ T + 𝐑₀' ⊢! φ := by
  constructor
  · intro h; exact System.wk! (by simp [Theory.add_def]) h
  · intro h
    exact System.StrongCut.cut!
      (by
        rintro φ (hp | hp)
        · exact System.by_axm _ hp
        · have : 𝐑₀' ⊢! φ := System.by_axm _ hp
          have : 𝐑₀ ⊢! φ := System.Subtheory.prf! this
          exact System.Subtheory.prf! this) h

end Arith

end LO.FirstOrder

noncomputable section

open Classical

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

section

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

def singleton (φ : SyntacticFormula L) :
    Theory.Delta1Definable {φ} where
  ch := .ofZero (.mkSigma “x. x = ↑⌜φ⌝” (by simp)) _
  mem_iff {ψ} := by simp
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

@[simp] lemma singleton_toTDef_ch_val (φ : FirstOrder.SyntacticFormula L) :
    letI := singleton φ
    (Theory.Delta1Definable.toTDef {φ}).ch.val = “x. x = ↑⌜φ⌝” := rfl

end

namespace Formalized

namespace Theory.CobhamR0'

def eqRefl : FirstOrder.Theory.Delta1Definable {(“∀ x, x = x” : SyntacticFormula ℒₒᵣ)} := singleton _

def replace :
    FirstOrder.Theory.Delta1Definable {“∀ x y, x = y → !φ x → !φ y” | φ : SyntacticSemiformula ℒₒᵣ 1} where
  ch := .mkDelta
    (.mkSigma
      “p.
      ∃ q < p, !p⌜ℒₒᵣ⌝.isSemiformulaDef.sigma 1 q ∧
      let x0 := qqBvarDef 0;
      let x1 := qqBvarDef 1;
      let eq := qqEQDef x1 x0;
      let v0 := mkVec₁Def x0;
      let v1 := mkVec₁Def x1;
      let q0 := p⌜ℒₒᵣ⌝.substsDef v1 q;
      let q1 := p⌜ℒₒᵣ⌝.substsDef v0 q;
      let imp0 := p⌜ℒₒᵣ⌝.impDef q0 q1;
      let imp1 := p⌜ℒₒᵣ⌝.impDef eq imp0;
      let all0 := qqAllDef imp1;
      !qqAllDef p all0” (by simp))
    (.mkPi
      “p.
      ∃ q < p, !p⌜ℒₒᵣ⌝.isSemiformulaDef.pi 1 q ∧
      let' x0 := qqBvarDef 0;
      let' x1 := qqBvarDef 1;
      let' eq := qqEQDef x1 x0;
      let' v0 := mkVec₁Def x0;
      let' v1 := mkVec₁Def x1;
      let' q0 := p⌜ℒₒᵣ⌝.substsDef v1 q;
      let' q1 := p⌜ℒₒᵣ⌝.substsDef v0 q;
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
    · rintro ⟨q, rfl⟩
      exact ⟨⌜q⌝, by
        simp [subst_eq_self₁]
        refine lt_trans ?_ (lt_forall _)
        refine lt_trans ?_ (lt_forall _)
        refine lt_trans ?_ (lt_or_right _ _)
        exact lt_or_right _ _, by simp⟩
    · rintro ⟨x, _, hx, h⟩
      rcases hx.sound with ⟨q, rfl⟩
      exact ⟨q, by symm; apply (quote_inj_iff (V := ℕ)).mp; simpa using h⟩
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
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
      let numn := numeralDef n;
      let numm := numeralDef m;
      let lhd := qqAddDef numn numm;
      let rhd := numeralDef (n + m);
      !qqEQDef p lhd rhd” (by simp))
    (.mkPi “p.
      ∃ n < p, ∃ m < p,
      let' numn := numeralDef n;
      let' numm := numeralDef m;
      let' lhd := qqAddDef numn numm;
      let' rhd := numeralDef (n + m);
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
      eval_numeralDef, eval_qqAddDef, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Add.add,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨n, m, rfl⟩
      refine ⟨n, by
          simp
          apply lt_trans ?_ (lt_qqEQ_left _ _)
          apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqAdd_left _ _),
        m, by
          simp
          apply lt_trans ?_ (lt_qqEQ_left _ _)
          apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqAdd_right _ _), by simp⟩
    · rintro ⟨n, _, m, _, h⟩
      use n; use m
      exact (quote_inj_iff (V := ℕ)).mp (by simpa using h)
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
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
      eval_numeralDef, eval_qqAddDef, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Add.add,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left,
      HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
      Semiformula.eval_all, LogicalConnective.HomClass.map_imply, Semiformula.eval_operator₂,
      Matrix.cons_app_seven, Structure.Eq.eq, LogicalConnective.Prop.arrow_eq, forall_eq]

def Ω₂ :
    FirstOrder.Theory.Delta1Definable {φ : SyntacticFormula ℒₒᵣ | ∃ n m : ℕ, φ = “↑n * ↑m = ↑(n * m)”} where
  ch := .mkDelta
    (.mkSigma “p.
      ∃ n < p, ∃ m < p,
      let numn := numeralDef n;
      let numm := numeralDef m;
      let lhd := qqMulDef numn numm;
      let rhd := numeralDef (n * m);
      !qqEQDef p lhd rhd” (by simp))
    (.mkPi “p.
      ∃ n < p, ∃ m < p,
      let' numn := numeralDef n;
      let' numm := numeralDef m;
      let' lhd := qqMulDef numn numm;
      let' rhd := numeralDef (n * m);
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
      eval_numeralDef, eval_qqMulDef, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Mul.mul,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨n, m, rfl⟩
      refine ⟨n, by
          simp
          apply lt_trans ?_ (lt_qqEQ_left _ _)
          apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqMul_left _ _),
        m, by
          simp
          apply lt_trans ?_ (lt_qqEQ_left _ _)
          apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqMul_right _ _), by simp⟩
    · rintro ⟨n, _, m, _, h⟩
      use n; use m
      exact (quote_inj_iff (V := ℕ)).mp (by simpa using h)
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
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
      eval_numeralDef, eval_qqMulDef, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Mul.mul,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left,
      HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
      Semiformula.eval_all, LogicalConnective.HomClass.map_imply, Semiformula.eval_operator₂,
      Matrix.cons_app_seven, Structure.Eq.eq, LogicalConnective.Prop.arrow_eq, forall_eq]

def Ω₃ :
    FirstOrder.Theory.Delta1Definable {φ : SyntacticFormula ℒₒᵣ | ∃ n m : ℕ, n ≠ m ∧ φ = “↑n ≠ ↑m”} where
  ch := .mkDelta
    (.mkSigma “p. ∃ n < p, ∃ m < p, n ≠ m ∧
      let numn := numeralDef n;
      let numm := numeralDef m;
      !qqNEQDef p numn numm” (by simp))
    (.mkPi “p. ∃ n < p, ∃ m < p, n ≠ m ∧
      let' numn := numeralDef n;
      let' numm := numeralDef m;
      ∀ p', !qqNEQDef p' numn numm → p = p'” (by simp))
  mem_iff {φ} := by
    /-
    simp?
    -/
    simp only [ne_eq, Set.mem_setOf_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.vecHead, LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
      Semiformula.eval_operator₂, Matrix.cons_val_zero, Structure.Eq.eq,
      LogicalConnective.Prop.neg_eq, Semiformula.eval_ex, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, Matrix.constant_eq_singleton, eval_numeralDef, Matrix.cons_val_four,
      Fin.succ_one_eq_two, Matrix.cons_val_succ, eval_qqNEQDef, LogicalConnective.Prop.and_eq,
      exists_eq_left]
    constructor
    · rintro ⟨n, m, ne, rfl⟩
      refine ⟨n, by
          simp
          rw [neg_eq (by simp) (by simp)]
          exact lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqNEQ_left _ _),
        m, by
          simp
          rw [neg_eq (by simp) (by simp)]
          exact lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqNEQ_right _ _), ne, ?_⟩
      simp; rw [neg_eq (by simp) (by simp)]
    · rintro ⟨n, _, m, _, ne, h⟩
      refine ⟨n, m, ne, ?_⟩
      exact (quote_inj_iff (V := ℕ)).mp (by simp; rw [neg_eq (by simp) (by simp)]; simpa using h)
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by simp

private lemma quote_disjLt_eq (n : ℕ) :
    ⌜(disjLt (fun i ↦ “#0 = ↑i”) n : SyntacticSemiformula ℒₒᵣ 1)⌝ =
    ^⋁ substItr (^#0 ∷ 0) (^#1 ^= ^#0) n := by
  induction n
  case zero => simp
  case succ n ih =>
    simp [ih]; rw [substs_eq (by simp) (by simp)]; simp

def Ω₄ :
    FirstOrder.Theory.Delta1Definable {(“∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i” : SyntacticFormula ℒₒᵣ) | n} where
  ch := .mkDelta
    (.mkSigma “p. ∃ n < p,
      let numn := numeralDef n;
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
      let' numn := numeralDef n;
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
      (Language.iff_defined (LOR (V := ℕ))).df.iff]
    -/
    simp only [Nat.reduceAdd, Fin.isValue, Set.mem_setOf_eq, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_fin_one, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead, Matrix.constant_eq_singleton,
      eval_numeralDef, Semiterm.val_operator₀, Structure.numeral_eq_numeral,
      ORingStruc.zero_eq_zero, eval_qqBvarDef, ORingStruc.one_eq_one, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_three,
      Fin.succ_one_eq_two, eval_qqLTDef, eval_cons, Matrix.cons_val_four, Matrix.cons_val_succ,
      eval_qqEQDef, Matrix.cons_app_seven, Matrix.cons_app_six, Matrix.cons_app_five,
      substItr_defined_iff, eval_qqDisj, (Language.iff_defined (LOR (V := ℕ))).df.iff,
      Language.TermRec.Construction.cons_app_10, Language.TermRec.Construction.cons_app_9,
      Matrix.cons_app_eight, eval_qqAllDef, LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨n, by
        simp
        apply lt_trans ?_ (lt_forall _)
        apply lt_trans ?_ (lt_iff_left _ _)
        apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqLT_right _ _), ?_⟩
      simp [quote_disjLt_eq]
    · rintro ⟨n, _, h⟩
      use n
      symm;
      exact (quote_inj_iff (V := ℕ)).mp (by simpa [quote_disjLt_eq] using h)
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V := V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff,
      (Language.iff_defined (LOR (V := V))).df.iff]
    -/
    simp only [Fin.isValue, Nat.reduceAdd, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.vecHead,
      Matrix.constant_eq_singleton, eval_numeralDef, Semiterm.val_operator₀,
      Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero, eval_qqBvarDef, ORingStruc.one_eq_one,
      Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_three, Fin.succ_one_eq_two, eval_qqLTDef, eval_cons, Matrix.cons_val_four,
      Matrix.cons_val_succ, eval_qqEQDef, Matrix.cons_app_seven, Matrix.cons_app_six,
      Matrix.cons_app_five, substItr_defined_iff, eval_qqDisj,
      (Language.iff_defined (LOR (V := V))).df.iff, Language.TermRec.Construction.cons_app_10,
      Language.TermRec.Construction.cons_app_9, Matrix.cons_app_eight, eval_qqAllDef,
      LogicalConnective.Prop.and_eq, exists_eq_left, HierarchySymbol.Semiformula.pi_mkDelta,
      HierarchySymbol.Semiformula.val_mkPi, Semiformula.eval_all,
      LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq, forall_eq]

end Theory.CobhamR0'

open Theory.CobhamR0'

instance Theory.CobhamR0'Delta1Definable : 𝐑₀'.Delta1Definable := (eqRefl.add <| replace.add <| Ω₁.add <| Ω₂.add <| Ω₃.add Ω₄).ofEq <| by
    ext φ; constructor
    · rintro (hφ | hφ | hφ | hφ | hφ | hφ) <;> simp at hφ
      · rcases hφ; exact Theory.CobhamR0'.eq_refl
      · rcases hφ with ⟨φ, rfl⟩; exact FirstOrder.Theory.CobhamR0'.replace φ
      · rcases hφ with ⟨n, m, rfl⟩; exact FirstOrder.Theory.CobhamR0'.Ω₁ n m
      · rcases hφ with ⟨n, m, rfl⟩; exact FirstOrder.Theory.CobhamR0'.Ω₂ n m
      · rcases hφ with ⟨n, m, ne, rfl⟩; exact FirstOrder.Theory.CobhamR0'.Ω₃ n m ne
      · rcases hφ with ⟨n, rfl⟩; exact FirstOrder.Theory.CobhamR0'.Ω₄ n
    · intro hφ; cases hφ
      case eq_refl => left; simp
      case replace φ => right; left; exact ⟨φ, by simp⟩
      case Ω₁ n m => right; right; left; exact ⟨n, m, by simp⟩
      case Ω₂ n m => right; right; right; left; exact ⟨n, m, by simp⟩
      case Ω₃ n m ne => right; right; right; right; left; exact ⟨n, m, ne, by simp⟩
      case Ω₄ n => right; right; right; right; right; exact ⟨n, by simp⟩

abbrev Theory.CobhamR0' : ⌜ℒₒᵣ⌝[V].Theory := 𝐑₀'.codeIn V

abbrev TTheory.CobhamR0' : ⌜ℒₒᵣ⌝[V].TTheory := 𝐑₀'.tCodeIn V

notation "⌜𝐑₀'⌝" => TTheory.CobhamR0'
notation "⌜𝐑₀'⌝[" V "]" => TTheory.CobhamR0' (V := V)

namespace Theory.CobhamR0'

def eqRefl.proof : ⌜𝐑₀'⌝[V] ⊢ (#'0 =' #'0).all := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_left
  unfold eqRefl
  simp [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve, numeral_eq_natCast]
  simp [qqAll, nat_cast_pair, qqEQ, qqRel, cons_absolute, qqBvar]

def replace.proof (φ : ⌜ℒₒᵣ⌝[V].Semiformula (0 + 1)) :
    ⌜𝐑₀'⌝[V] ⊢ (#'1 =' #'0 ➝ φ^/[(#'1).sing] ➝ φ^/[(#'0).sing]).all.all := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold replace
  simp [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve,
    (Language.isSemiformula_defined (LOR (V := V))).df.iff,
    (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff]
  refine ⟨φ.val, ?_, by simpa using φ.prop, rfl⟩
  · rw [subst_eq_self₁ (by simpa using φ.prop)]
    refine lt_trans ?_ (lt_forall _)
    refine lt_trans ?_ (lt_forall _)
    refine lt_trans ?_ (lt_or_right _ _)
    exact lt_or_right _ _

def Ω₁.proof (n m : V) :
    ⌜𝐑₀'⌝[V] ⊢ (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m) := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold Ω₁
  simp [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve]
  refine ⟨n, ?_, m, ?_, rfl⟩
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqAdd_left _ _)
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqAdd_right _ _)

def Ω₂.proof (n m : V) :
    ⌜𝐑₀'⌝[V] ⊢ (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m) := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold Ω₂
  simp [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve]
  refine ⟨n, ?_, m, ?_, rfl⟩
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqMul_left _ _)
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqMul_right _ _)

def Ω₃.proof {n m : V} (ne : n ≠ m) : ⌜𝐑₀'⌝[V] ⊢ ↑n ≠' ↑m := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold Ω₃
  simp [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve]
  refine ⟨n, ?_, m, ?_, ne, rfl⟩
  · exact lt_of_le_of_lt (by simp) (lt_qqNEQ_left _ _)
  · exact lt_of_le_of_lt (by simp) (lt_qqNEQ_right _ _)

def Ω₄.proof (n : V): ⌜𝐑₀'⌝[V] ⊢ (#'0 <' ↑n ⭤ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  unfold Ω₄
  simp [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve,
      (Language.iff_defined (LOR (V := V))).df.iff]
  refine ⟨n, ?_, rfl⟩
  apply lt_trans ?_ (lt_forall _)
  apply lt_trans ?_ (lt_iff_left _ _)
  apply lt_of_le_of_lt (by simp) (lt_qqLT_right _ _)

end Theory.CobhamR0'

instance Theory.addCobhamR0'Delta1Definable (T : Theory ℒₒᵣ) [d : T.Delta1Definable] : (T + 𝐑₀').Delta1Definable :=
  d.add Theory.CobhamR0'Delta1Definable
section

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

abbrev _root_.LO.FirstOrder.Theory.AddR₀TTheory : ⌜ℒₒᵣ⌝[V].TTheory := (T + 𝐑₀').tCodeIn V

variable {T}

@[simp] lemma R₀'_subset_AddR₀ : ⌜𝐑₀'⌝[V] ⊆ T.AddR₀TTheory := Set.subset_union_right

@[simp] lemma theory_subset_AddR₀ : T.tCodeIn V ⊆ T.AddR₀TTheory := FirstOrder.Theory.Delta1Definable.add_subset_left _ _

instance : R₀Theory (T.AddR₀TTheory (V := V)) where
  refl := Language.Theory.TProof.ofSubset (by simp) Theory.CobhamR0'.eqRefl.proof
  replace := fun φ ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.CobhamR0'.replace.proof φ)
  add := fun n m ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.CobhamR0'.Ω₁.proof n m)
  mul := fun n m ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.CobhamR0'.Ω₂.proof n m)
  ne := fun h ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.CobhamR0'.Ω₃.proof h)
  ltNumeral := fun n ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.CobhamR0'.Ω₄.proof n)

end

end Formalized

open Formalized

section

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

/-- Provability predicate for arithmetic stronger than $\mathbf{R_0}$. -/
def _root_.LO.FirstOrder.Theory.Provableₐ (φ : V) : Prop := ((T + 𝐑₀').codeIn V).Provable φ

variable {T}

lemma provableₐ_iff {σ : Sentence ℒₒᵣ} : T.Provableₐ (⌜σ⌝ : V) ↔ (T + 𝐑₀').tCodeIn V ⊢! ⌜σ⌝ := by
  simp [Language.Theory.TProvable.iff_provable]; rfl

section

variable (T)

def _root_.LO.FirstOrder.Theory.provableₐ : 𝚺₁.Semisentence 1 := .mkSigma
  “p. !(T + 𝐑₀').tDef.prv p” (by simp)

lemma provableₐ_defined : 𝚺₁-Predicate (T.Provableₐ : V → Prop) via T.provableₐ := by
  intro v; simp [FirstOrder.Theory.provableₐ, FirstOrder.Theory.Provableₐ, ((T + 𝐑₀').codeIn V).provable_defined.df.iff]

@[simp] lemma eval_provableₐ (v) :
    Semiformula.Evalbm V v T.provableₐ.val ↔ T.Provableₐ (v 0) := (provableₐ_defined T).df.iff v

instance provableₐ_definable : 𝚺₁-Predicate (T.Provableₐ : V → Prop) := (provableₐ_defined T).to_definable

/-- instance for definability tactic-/
instance provableₐ_definable' : 𝚺-[0 + 1]-Predicate (T.Provableₐ : V → Prop) := provableₐ_definable T

end

end

end LO.Arith
