import Arithmetization.ISigmaOne.Metamath.Proof.Typed
import Arithmetization.ISigmaOne.Metamath.Theory.SigmaOneDefinable

/-!

# Formalized $\Sigma_1$-Completeness

-/

namespace LO.FirstOrder

section

open Lean PrettyPrinter Delaborator

syntax:max "let " ident " := " term:max first_order_term:61* "; " first_order_formula:0 : first_order_formula
syntax:max "let' " ident " := " term:max first_order_term:61* "; " first_order_formula:0 : first_order_formula

macro_rules
  | `(“ $binders* | let $x:ident := $f:term $vs:first_order_term* ; $p:first_order_formula ”) =>
    `(“ $binders* | ∃ $x, !$f:term #0 $vs:first_order_term* ∧ $p ”)
  | `(“ $binders* | let' $x:ident := $f:term $vs:first_order_term* ; $p:first_order_formula ”) =>
    `(“ $binders* | ∀ $x, !$f:term #0 $vs:first_order_term* → $p ”)
end

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

variable (V)

def Language.Theory.const (p : FirstOrder.SyntacticFormula L) : (L.codeIn V).Theory where
  set := {⌜p⌝}

@[simp] lemma Language.Theory.const_set_def (p : FirstOrder.SyntacticFormula L) :
    (Language.Theory.const V p).set = {⌜p⌝} := rfl

variable {V}

def Language.Theory.constDef (p : FirstOrder.SyntacticFormula L) : L.lDef.TDef where
  ch := .ofZero (.mkSigma “x | x = ↑⌜p⌝” (by simp)) _

instance const_defined_const (p : FirstOrder.SyntacticFormula L) : (Language.Theory.const V p).Defined (Language.Theory.constDef p) where
  defined := .of_zero (by intro v; simp [numeral_eq_natCast])

end

section scheme

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

variable (V)

structure Language.Scheme (L : Arith.Language V) {pL : LDef} [Arith.Language.Defined L pL] where
  scheme : V → V
  increasing : ∀ x, x ≤ scheme x

variable {V}

structure _root_.LO.FirstOrder.Arith.LDef.schemeDef (pL : LDef) where
  schemeDef : HSemisentence ℒₒᵣ 2 𝚺₁

class Language.Scheme.Defined (φ : L.Scheme V) (ps : outParam pL.schemeDef) : Prop where
  defined : 𝚺₁-Function₁ φ.scheme via ps.schemeDef

variable {φ : L.Scheme} {ps : pL.schemeDef} [φ.Defined ps]

def Language.Scheme.toTheory (φ : L.Scheme) : L.Theory where
  set := Set.range φ.scheme

def _root_.LO.FirstOrder.Arith.LDef.schemeDef.tDef {pL : LDef} (ps : pL.schemeDef) : pL.TDef where
  ch := .mkDelta
    (.mkSigma “p | ∃ x, !ps.schemeDef p x” (by simp))
    (.mkPi “p | ∃ x <⁺ p, ∀ y, !ps.schemeDef y x → p = y”  (by simp))

instance scheme_defined_scheme (φ : L.Scheme) {ps : pL.schemeDef} [φ.Defined ps] : φ.toTheory.Defined ps.tDef where
  defined := ⟨by
    intro v
    simp [Arith.LDef.schemeDef.tDef, (Language.Scheme.Defined.defined (V := V) (φ := φ)).df.iff]
    constructor
    · rintro ⟨x, h⟩; exact ⟨x, by simp [h, φ.increasing], h⟩
    · rintro ⟨x, _, h⟩; exact ⟨x, h⟩, by
    intro v
    simp [Language.Scheme.toTheory, Arith.LDef.schemeDef.tDef,
      (Language.Scheme.Defined.defined (V := V) (φ := φ)).df.iff, eq_comm]⟩

end scheme

section union

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

def Language.Theory.union (T U : L.Theory) : L.Theory where
  set := T.set ∪ U.set

def _root_.LO.FirstOrder.Arith.LDef.TDef.union {pL : LDef} (t u : pL.TDef) : pL.TDef where
  ch  := t.ch.or u.ch

instance union_Defined_union (T U : L.Theory) {t u : pL.TDef} [T.Defined t] [U.Defined u] : (T.union U).Defined (t.union u) where
  defined := ⟨by
    simp [Arith.LDef.TDef.union]
    apply HSemiformula.ProperOn.or
      (Language.Theory.Defined.defined (T := T)).proper
      (Language.Theory.Defined.defined (T := U)).proper, by
    intro v; simp [Arith.LDef.TDef.union, HSemiformula.or, Language.Theory.union,
      HSemiformula.val_sigma,
      (Language.Theory.Defined.defined (T := T)).df.iff,
      (Language.Theory.Defined.defined (T := U)).df.iff]⟩

end union
/-
namespace Formalized

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
      HSemiformula.val_sigma,
      (imp_defined (Language.codeIn ℒₒᵣ V)).df.iff,
      (substs_defined (Language.codeIn ℒₒᵣ V)).df.iff,
      (semiformula_defined (Language.codeIn ℒₒᵣ V)).df.iff]
   }, by {  }⟩

variable {V}
-/
