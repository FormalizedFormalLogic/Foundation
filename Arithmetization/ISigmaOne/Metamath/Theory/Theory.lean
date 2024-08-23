import Arithmetization.ISigmaOne.Metamath.Proof.Typed
import Arithmetization.ISigmaOne.Metamath.Theory.SigmaOneDefinable

/-!

# Formalized $\Sigma_1$-Completeness

-/

namespace LO.FirstOrder

variable {L : Language}

namespace Semiformula

def ifElse (c p q : Semiformula L ξ n) : Semiformula L ξ n := (c ⟶ p) ⋏ (~c ⟶ q)

variable {M : Type w} {s : Structure L M}

open Classical

@[simp] lemma val_ifElse {c p q : Semiformula L ξ n} : Eval s e ε (c.ifElse p q) ↔ if Eval s e ε c then Eval s e ε p else Eval s e ε q := by
  simp [ifElse]; by_cases h : Eval s e ε c <;> simp [h]

end Semiformula

section

open Lean PrettyPrinter Delaborator

syntax:max "let " ident " := " term:max first_order_term:61* "; " first_order_formula:0 : first_order_formula
syntax:max "let' " ident " := " term:max first_order_term:61* "; " first_order_formula:0 : first_order_formula
syntax:max "if " first_order_formula:0 " then " first_order_formula:0 " else " first_order_formula:0 : first_order_formula

macro_rules
  | `(“ $binders* | let $x:ident := $f:term $vs:first_order_term* ; $p:first_order_formula ”) =>
    `(“ $binders* | ∃ $x, !$f:term #0 $vs:first_order_term* ∧ $p ”)
  | `(“ $binders* | let' $x:ident := $f:term $vs:first_order_term* ; $p:first_order_formula ”) =>
    `(“ $binders* | ∀ $x, !$f:term #0 $vs:first_order_term* → $p ”)
  | `(“ $binders* | if $c:first_order_formula then $p:first_order_formula else $q:first_order_formula ”) =>
    `(Semiformula.ifElse “ $binders* | $c ” “ $binders* | $p ” “ $binders* | $q ”)

end

namespace Arith.Hierarchy

variable [L.LT]

lemma ifElse_iff {c p q : Semiformula L ξ n} :
    Hierarchy Γ s (c.ifElse p q) ↔ Hierarchy Γ s c ∧ Hierarchy Γ.alt s c ∧ Hierarchy Γ s p ∧ Hierarchy Γ s q := by
  simp [Semiformula.ifElse]; tauto

end Arith.Hierarchy

namespace Theory

variable (L : Language) [L.Eq]

inductive EQ₀ : Theory L
  | reflAx : EQ₀ “∀ x, x = x”
  | replaceAx (p : Semisentence L 1) : EQ₀ “∀ x y, x = y → !p x → !p y”

end Theory

namespace Arith

end Arith

end LO.FirstOrder

noncomputable section

open Classical

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

section

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (L V)

def Language.Theory.singleton (p : FirstOrder.SyntacticFormula L) : (L.codeIn V).Theory where
  set := {⌜p⌝}

@[simp] lemma Language.Theory.mem_singleton_iff (x : V) (p : FirstOrder.SyntacticFormula L) :
    x ∈ Language.Theory.singleton V L p ↔ x = ⌜p⌝ := by rfl

variable {L V}

@[simp] lemma Language.Theory.const_set_def (p : FirstOrder.SyntacticFormula L) :
    (Language.Theory.singleton V L p).set = {⌜p⌝} := rfl

def Language.Theory.singletonDef (p : FirstOrder.SyntacticFormula L) : L.lDef.TDef where
  ch := .ofZero (.mkSigma “x | x = ↑⌜p⌝” (by simp)) _

instance const_defined_const (p : FirstOrder.SyntacticFormula L) : (Language.Theory.singleton V L p).Defined (Language.Theory.singletonDef p) where
  defined := .of_zero (by intro v; simp [numeral_eq_natCast, coe_quote])

end

section scheme

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

structure Language.Scheme (L : Arith.Language V) {pL : LDef} [Arith.Language.Defined L pL] where
  scheme : V → V
  increasing : ∀ x, x ≤ scheme x

structure Language.Craig (L : Arith.Language V) {pL : LDef} [Arith.Language.Defined L pL] where
  core : V → V

structure _root_.LO.FirstOrder.Arith.LDef.SchemeDef (pL : LDef) where
core : 𝚺₁.Semisentence 2

class Language.Scheme.Defined (φ : L.Scheme) (ps : outParam pL.SchemeDef) : Prop where
  defined : 𝚺₁-Function₁ φ.scheme via ps.core

variable {φ : L.Scheme} {ps : pL.SchemeDef} [φ.Defined ps]

def Language.Scheme.toTheory (φ : L.Scheme) : L.Theory where
  set := Set.range φ.scheme

def _root_.LO.FirstOrder.Arith.LDef.SchemeDef.toTDef {pL : LDef} (ps : pL.SchemeDef) : pL.TDef where
  ch := .mkDelta
    (.mkSigma “p | ∃ x, !ps.core p x” (by simp))
    (.mkPi “p | ∃ x <⁺ p, ∀ y, !ps.core y x → p = y”  (by simp))

instance scheme_defined_scheme (φ : L.Scheme) {ps : pL.SchemeDef} [φ.Defined ps] : φ.toTheory.Defined ps.toTDef where
  defined := ⟨by
    intro v
    simp [Arith.LDef.SchemeDef.toTDef, (Language.Scheme.Defined.defined (V := V) (φ := φ)).df.iff]
    constructor
    · rintro ⟨x, h⟩; exact ⟨x, by simp [h, φ.increasing], h⟩
    · rintro ⟨x, _, h⟩; exact ⟨x, h⟩, by
    intro v
    simp [Language.Scheme.toTheory, Arith.LDef.SchemeDef.toTDef,
      (Language.Scheme.Defined.defined (V := V) (φ := φ)).df.iff, eq_comm]⟩

def Language.Craig.toScheme {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL] (c : L.Craig) : L.Scheme where
  scheme (x) := c.core x ^⋏ qqVerums x
  increasing (x) := le_trans (le_qqVerums x) (le_of_lt <| by simp)

structure _root_.LO.FirstOrder.Arith.LDef.CraigDef (pL : LDef) where
  core : 𝚺₁.Semisentence 2

class Language.Craig.Defined (φ : L.Craig) (ps : outParam pL.CraigDef) : Prop where
  defined : 𝚺₁-Function₁ φ.core via ps.core

def _root_.LO.FirstOrder.Arith.LDef.CraigDef.toSchemeDef {pL : LDef} (c : pL.CraigDef) : pL.SchemeDef where
  core := .mkSigma “p x | ∃ p', !c.core p' x ∧ ∃ vs, !qqVerumsDef vs x ∧ !qqAndDef p p' vs” (by simp)

instance (φ : L.Craig) (c : pL.CraigDef) [φ.Defined c] : φ.toScheme.Defined c.toSchemeDef where
  defined := by intro v; simp [Language.Craig.toScheme, Arith.LDef.CraigDef.toSchemeDef, (Language.Craig.Defined.defined (φ := φ)).df.iff]

end scheme

section union

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

def Language.Theory.union (T U : L.Theory) : L.Theory where
  set := T.set ∪ U.set

@[simp] lemma Language.Theory.mem_union_iff (x : V) (T U : L.Theory) : x ∈ T.union U ↔ x ∈ T ∨ x ∈ U := Set.mem_union _ _ _

def _root_.LO.FirstOrder.Arith.LDef.TDef.union {pL : LDef} (t u : pL.TDef) : pL.TDef where
  ch  := t.ch.or u.ch

instance union_Defined_union (T U : L.Theory) {t u : pL.TDef} [T.Defined t] [U.Defined u] : (T.union U).Defined (t.union u) where
  defined := ⟨by
    simp [Arith.LDef.TDef.union]
    apply HierarchySymbol.Semiformula.ProperOn.or
      (Language.Theory.Defined.defined (T := T)).proper
      (Language.Theory.Defined.defined (T := U)).proper, by
    intro v; simp [Arith.LDef.TDef.union, HierarchySymbol.Semiformula.or, Language.Theory.union,
      HierarchySymbol.Semiformula.val_sigma,
      (Language.Theory.Defined.defined (T := T)).df.iff,
      (Language.Theory.Defined.defined (T := U)).df.iff]⟩

end union

namespace Formalized

section thEQ

def eqRefl : ⌜ℒₒᵣ⌝[V].Theory := Language.Theory.singleton V ℒₒᵣ “∀ x, x = x”

def eqReplaceC : ⌜ℒₒᵣ⌝[V].Craig where
  core := fun p ↦ if ⌜ℒₒᵣ⌝.IsSemiformula 1 p then ^∀ ^∀ (^#1 ^= ^#0 ^→[⌜ℒₒᵣ⌝] ⌜ℒₒᵣ⌝.substs ?[^#1] p ^→[⌜ℒₒᵣ⌝] ⌜ℒₒᵣ⌝.substs ?[^#0] p) else 0

def eqReplaceCDef : p⌜ℒₒᵣ⌝.CraigDef where
  core := .mkSigma “σ p |
    ( !p⌜ℒₒᵣ⌝.isSemiformulaDef.pi 1 p →
      let x0 := qqBvarDef 0;
      let x1 := qqBvarDef 1;
      let eq := qqEQDef x1 x0;
      let v0 := mkVec₁Def x0;
      let v1 := mkVec₁Def x1;
      let p0 := p⌜ℒₒᵣ⌝.substsDef v1 p;
      let p1 := p⌜ℒₒᵣ⌝.substsDef v0 p;
      let imp0 := p⌜ℒₒᵣ⌝.impDef p0 p1;
      let imp1 := p⌜ℒₒᵣ⌝.impDef eq imp0;
      let all0 := qqAllDef imp1;
      !qqAllDef σ all0 ) ∧
    ( ¬!p⌜ℒₒᵣ⌝.isSemiformulaDef.sigma 1 p → σ = 0)” (by simp)

instance : (eqReplaceC (V := V)).Defined eqReplaceCDef where
  defined := by
    intro v
    simp [eqReplaceC, eqReplaceCDef,
      HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V := V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff]
    by_cases h : ⌜ℒₒᵣ⌝.IsSemiformula 1 (v 1) <;> simp [h]

variable (V)

def Theory.EQ : ⌜ℒₒᵣ⌝[V].Theory := (Language.Theory.singleton V ℒₒᵣ “∀ x, x = x”).union eqReplaceC.toScheme.toTheory

variable {V}

def Theory.eqDef : p⌜ℒₒᵣ⌝.TDef := (Language.Theory.singletonDef (L := ℒₒᵣ) “∀ x, x = x”).union eqReplaceCDef.toSchemeDef.toTDef

instance Theory.EQ_defined : (Theory.EQ V).Defined Theory.eqDef := by apply union_Defined_union

def TTheory.thEQ : ⌜ℒₒᵣ⌝[V].TTheory where
  thy := Theory.EQ V
  pthy := Theory.eqDef

notation "⌜𝐄𝐐'⌝" => TTheory.thEQ
notation "⌜𝐄𝐐'⌝[" V "]" => TTheory.thEQ (V := V)

def TTheory.thEQ.eqRefl : ⌜𝐄𝐐'⌝[V] ⊢ (#'0 =' #'0).all := Language.Theory.TProof.byAxm <| by
  simp [Language.Theory.tmem, TTheory.thEQ, Theory.EQ, FirstOrder.Semiformula.quote_all, FirstOrder.Semiformula.quote_eq,
    Semiformula.Operator.eq_def, Semiterm.quote_bvar]

end thEQ

/-
def thEQDef : (Language.lDef ℒₒᵣ).TDef where
  ch := .mkDelta
    (.mkSigma “σ |
      ( let v0 := qqBvarDef 0;
        ∃ eq, !qqEQDef eq 1 v0 v0 ∧
        !qqAllDef σ 0 eq ) ∨
      ( ∃ p, !p⌜ℒₒᵣ⌝.isSemiformulaDef.sigma 1 p ∧
        ∃ x0, !qqBvarDef x0 0 ∧
        ∃ x1, !qqBvarDef x1 1 ∧
        ∃ eq, !qqEQDef eq 2 x0 x1 ∧
        ∃ v0, !mkVec₁Def v0 x0 ∧
        ∃ v1, !mkVec₁Def v1 x1 ∧
        ∃ p0, !p⌜ℒₒᵣ⌝.substsDef p0 2 v0 p ∧
        ∃ p1, !p⌜ℒₒᵣ⌝.substsDef p0 2 v1 p ∧
        ∃ imp0, !p⌜ℒₒᵣ⌝.impDef imp0 2 p0 p1 ∧
        ∃ imp1, !p⌜ℒₒᵣ⌝.impDef imp1 2 eq imp0 ∧
        ∃ all0, !qqAllDef all0 1 imp1 ∧
        !qqAllDef σ 0all0)”
      (by simp))
    (.mkPi “σ |
      ( let' v0 := qqBvarDef 0;
        ∀ eq, !qqEQDef eq 1 v0 v0 →
        !qqAllDef σ 0 eq ) ∨
      ( ∀ p, !p⌜ℒₒᵣ⌝.isSemiformulaDef.sigma 1 p →
        ∀ x0, !qqBvarDef x0 0 →
        ∀ x1, !qqBvarDef x1 1 →
        ∀ eq, !qqEQDef eq 2 x0 x1 →
        ∀ v0, !mkVec₁Def v0 x0 →
        ∀ v1, !mkVec₁Def v1 x1 →
        ∀ p0, !p⌜ℒₒᵣ⌝.substsDef p0 2 v0 p →
        ∀ p1, !p⌜ℒₒᵣ⌝.substsDef p0 2 v1 p →
        ∀ imp0, !p⌜ℒₒᵣ⌝.impDef imp0 2 p0 p1 →
        ∀ imp1, !p⌜ℒₒᵣ⌝.impDef imp1 2 eq imp0 →
        ∀ all0, !qqAllDef all0 1 imp1 →
        !qqAllDef σ 0all0)”
      (by simp))

variable (V)

def thEQ : (Language.codeIn ℒₒᵣ V).Theory where
  set := { ^∀ (^#0 ^=[1] ^#0) } ∪ { ^∀[0] ^∀[1] (^#1 ^=[2] ^#0 ^→[⌜ℒₒᵣ⌝; 2] ⌜ℒₒᵣ⌝.substs 2 ?[^#0] p ^→[⌜ℒₒᵣ⌝; 2] ⌜ℒₒᵣ⌝.substs 2 ?[^#0] p) | p }

instance : (thEQ V).Defined thEQDef where
  defined := ⟨by {
    intro v
    simp [thEQDef,
      HierarchySymbol.Semiformula.val_sigma,
      (imp_defined (Language.codeIn ℒₒᵣ V)).df.iff,
      (substs_defined (Language.codeIn ℒₒᵣ V)).df.iff,
      (semiformula_defined (Language.codeIn ℒₒᵣ V)).df.iff]
   }, by {  }⟩

variable {V}
-/
