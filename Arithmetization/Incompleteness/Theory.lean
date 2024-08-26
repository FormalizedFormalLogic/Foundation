import Arithmetization.ISigmaOne.Metamath.CodedTheory
import Arithmetization.Incompleteness.FormalizedArithmetic

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

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

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
  scheme : V → L.Formula

structure _root_.LO.FirstOrder.Arith.LDef.SchemeDef (pL : LDef) where
core : 𝚺₁.Semisentence 2

class Language.Scheme.Defined (φ : L.Scheme) (ps : outParam pL.SchemeDef) : Prop where
  defined : 𝚺₁-Function₁ (fun x ↦ (φ.scheme x).val) via ps.core

variable {φ : L.Scheme} {ps : pL.SchemeDef} [φ.Defined ps]

def Language.Scheme.toTheory (φ : L.Scheme) : L.Theory where
  set := Set.range fun x ↦ (φ.scheme x).val ^⋏ qqVerums x

def _root_.LO.FirstOrder.Arith.LDef.SchemeDef.toTDef {pL : LDef} (ps : pL.SchemeDef) : pL.TDef where
  ch := .mkDelta
    (.mkSigma “p | ∃ x, ∃ p', !ps.core p' x ∧ ∃ vs, !qqVerumsDef vs x ∧ !qqAndDef p p' vs” (by simp))
    (.mkPi “p | ∃ x <⁺ p, ∀ p', !ps.core p' x → ∀ vs, !qqVerumsDef vs x → !qqAndDef p p' vs”  (by simp))

instance scheme_defined_scheme (φ : L.Scheme) {ps : pL.SchemeDef} [φ.Defined ps] : φ.toTheory.Defined ps.toTDef where
  defined := ⟨by
    intro v
    simp [Arith.LDef.SchemeDef.toTDef, (Language.Scheme.Defined.defined (V := V) (φ := φ)).df.iff]
    constructor
    · rintro ⟨x, h⟩; exact ⟨x, by rw [h]; apply le_trans (le_qqVerums x) (le_of_lt <| by simp), h⟩
    · rintro ⟨x, _, h⟩; exact ⟨x, h⟩,
  by intro v; simp [Language.Scheme.toTheory, Arith.LDef.SchemeDef.toTDef,
      (Language.Scheme.Defined.defined (V := V) (φ := φ)).df.iff, eq_comm]⟩

variable (φ : L.Scheme) (c : pL.SchemeDef) [φ.Defined c]

lemma Language.Scheme.mem_toTheory (x : V) :
    φ.scheme x ⋏ verums x ∈' φ.toTheory := Set.mem_range_self _

end scheme

section union

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

def Language.Theory.union (T U : L.Theory) : L.Theory where
  set := T.set ∪ U.set

@[simp] lemma Language.Theory.mem_union_iff (x : V) (T U : L.Theory) : x ∈ T.union U ↔ x ∈ T ∨ x ∈ U := Set.mem_union _ _ _

@[simp] lemma Language.TTheory.tmem_union_iff (x : L.Formula) (T U : L.Theory) : x ∈' T.union U ↔ x ∈' T ∨ x ∈' U := Set.mem_union _ _ _

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

namespace Theory.EQ

def eqRefl : ⌜ℒₒᵣ⌝[V].Theory := Language.Theory.singleton V ℒₒᵣ “∀ x, x = x”

def eqScheme : ⌜ℒₒᵣ⌝[V].Scheme where
  scheme := fun p ↦ if hp : ⌜ℒₒᵣ⌝.IsSemiformula 1 p then
    let p : ⌜ℒₒᵣ⌝[V].Semiformula (0 + 1) := ⟨p, by simp [hp]⟩
    (#'1 =' #'0 ⟶ p^/[(#'1).sing] ⟶ p^/[(#'0).sing]).all.all else ⊤

@[simp] lemma eqScheme_scheme (p : ⌜ℒₒᵣ⌝[V].Semiformula (0 + 1)) :
    eqScheme.scheme p.val = (#'1 =' #'0 ⟶ p^/[(#'1).sing] ⟶ p^/[(#'0).sing]).all.all := by
  simp [eqScheme, by simpa using p.prop]

def eqSchemeDef : p⌜ℒₒᵣ⌝.SchemeDef where
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
    ( ¬!p⌜ℒₒᵣ⌝.isSemiformulaDef.sigma 1 p → !qqVerumDef σ)” (by simp)

instance : (eqScheme (V := V)).Defined eqSchemeDef where
  defined := by
    intro v
    simp [eqScheme, eqSchemeDef,
      HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V := V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff]
    by_cases h : ⌜ℒₒᵣ⌝.IsSemiformula 1 (v 1) <;> simp [h]

end Theory.EQ

variable (V)

def Theory.EQ : ⌜ℒₒᵣ⌝[V].Theory := (Language.Theory.singleton V ℒₒᵣ “∀ x, x = x”).union Theory.EQ.eqScheme.toTheory

def Theory.Eq.def : p⌜ℒₒᵣ⌝.TDef := (Language.Theory.singletonDef (L := ℒₒᵣ) “∀ x, x = x”).union Theory.EQ.eqSchemeDef.toTDef

instance Theory.EQ.defined : (Theory.EQ V).Defined Theory.Eq.def := by apply union_Defined_union

variable {V}

def TTheory.EQ : ⌜ℒₒᵣ⌝[V].TTheory where
  thy := Theory.EQ V
  pthy := Theory.Eq.def

notation "⌜𝐄𝐐'⌝" => TTheory.EQ
notation "⌜𝐄𝐐'⌝[" V "]" => TTheory.EQ (V := V)

namespace TTheory.EQ

def eqRefl : ⌜𝐄𝐐'⌝[V] ⊢ (#'0 =' #'0).all := Language.Theory.TProof.byAxm <| by
  simp [Language.Theory.tmem, TTheory.EQ, Theory.EQ, FirstOrder.Semiformula.quote_all, FirstOrder.Semiformula.quote_eq,
    Semiformula.Operator.eq_def, Semiterm.quote_bvar]

def eqReplace (p : ⌜ℒₒᵣ⌝[V].Semiformula (0 + 1)) : ⌜𝐄𝐐'⌝[V] ⊢ (#'1 =' #'0 ⟶ p^/[(#'1).sing] ⟶ p^/[(#'0).sing]).all.all := by
  have : ⌜𝐄𝐐'⌝ ⊢ (#'1 =' #'0 ⟶ p^/[(#'1).sing] ⟶ p^/[(#'0).sing]).all.all ⋏ verums p.val :=
    Language.Theory.TProof.byAxm <| by
      right
      simpa using Theory.EQ.eqScheme.mem_toTheory p.val
  exact System.and₁' this

end TTheory.EQ

namespace Theory.R₀

def addScheme : ⌜ℒₒᵣ⌝[V].Scheme where
  scheme := fun x ↦
    let n := π₁ x
    let m := π₂ x
    (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m)

def addScheme.def : p⌜ℒₒᵣ⌝.SchemeDef where
  core := .mkSigma “σ x |
    let n := pi₁Def x;
    let m := pi₂Def x;
    let numn := numeralDef n;
    let numm := numeralDef m;
    let lhd := qqAddDef numn numm;
    let rhd := numeralDef (n + m);
    !qqEQDef σ lhd rhd” (by simp)

instance : (addScheme (V := V)).Defined addScheme.def where
  defined := by intro v; simp [Theory.R₀.addScheme, Theory.R₀.addScheme.def]

@[simp] lemma addScheme_scheme (n m : V) :
    addScheme.scheme ⟪n, m⟫ = (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m) := by
  simp [addScheme]

def mulScheme : ⌜ℒₒᵣ⌝[V].Scheme where
  scheme := fun x ↦
    let n := π₁ x
    let m := π₂ x
    (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m)

def mulScheme.def : p⌜ℒₒᵣ⌝.SchemeDef where
  core := .mkSigma “σ x |
    let n := pi₁Def x;
    let m := pi₂Def x;
    let numn := numeralDef n;
    let numm := numeralDef m;
    let lhd := qqMulDef numn numm;
    let rhd := numeralDef (n * m);
    !qqEQDef σ lhd rhd” (by simp)

instance : (mulScheme (V := V)).Defined mulScheme.def where
  defined := by intro v; simp [Theory.R₀.mulScheme, Theory.R₀.mulScheme.def]

@[simp] lemma mulScheme_scheme (n m : V) :
    mulScheme.scheme ⟪n, m⟫ = (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m) := by
  simp [mulScheme]

def neqScheme : ⌜ℒₒᵣ⌝[V].Scheme where
  scheme := fun x ↦
    let n := π₁ x
    let m := π₂ x
    if n ≠ m then ↑n ≠' ↑m else ⊤

def neqScheme.def : p⌜ℒₒᵣ⌝.SchemeDef where
  core := .mkSigma “σ x |
    let n := pi₁Def x;
    let m := pi₂Def x;
    ( n ≠ m →
      let numn := numeralDef n;
      let numm := numeralDef m;
      !qqNEQDef σ numn numm ) ∧
    ( n = m → !qqVerumDef σ )” (by simp)

instance : (Theory.R₀.neqScheme (V := V)).Defined Theory.R₀.neqScheme.def where
  defined := by
    intro v; simp [Theory.R₀.neqScheme, Theory.R₀.neqScheme.def]
    by_cases h : π₁ (v 1) = π₂ (v 1) <;> simp [h]

@[simp] lemma neqScheme_scheme {n m : V} (h : n ≠ m) :
    neqScheme.scheme ⟪n, m⟫ = ↑n ≠' ↑m := by
  simp [neqScheme, h]

def ltNumeralScheme : ⌜ℒₒᵣ⌝[V].Scheme where
  scheme := fun n ↦ (#'0 <' ↑n ⟷ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all

def ltNumeralScheme.def : p⌜ℒₒᵣ⌝.SchemeDef where
  core := .mkSigma “σ n |
    let numn := numeralDef n;
    let x₀ := qqBvarDef 0;
    let x₁ := qqBvarDef 1;
    let lhd := qqLTDef x₀ numn;
    let v := consDef x₀ 0;
    let e := qqEQDef x₁ x₀;
    let ti := substItrDef v e n;
    let rhd := qqDisjDef ti;
    let iff := p⌜ℒₒᵣ⌝.qqIffDef lhd rhd;
    !qqAllDef σ iff” (by simp)

instance : (ltNumeralScheme (V := V)).Defined Theory.R₀.ltNumeralScheme.def where
  defined := by
    intro v; simp [ltNumeralScheme, ltNumeralScheme.def,
      (Language.iff_defined (LOR (V := V))).df.iff]

end Theory.R₀

variable (V)

def Theory.R₀ : ⌜ℒₒᵣ⌝[V].Theory :=
  Theory.R₀.addScheme.toTheory
  |>.union Theory.R₀.mulScheme.toTheory
  |>.union Theory.R₀.neqScheme.toTheory
  |>.union Theory.R₀.ltNumeralScheme.toTheory

variable {V}

def Theory.R₀.def : p⌜ℒₒᵣ⌝.TDef :=
  Theory.R₀.addScheme.def.toTDef
  |>.union Theory.R₀.mulScheme.def.toTDef
  |>.union Theory.R₀.neqScheme.def.toTDef
  |>.union Theory.R₀.ltNumeralScheme.def.toTDef

instance Theory.R₀.defined : (Theory.R₀ V).Defined Theory.R₀.def := by apply union_Defined_union

def TTheory.R₀ : ⌜ℒₒᵣ⌝[V].TTheory where
  thy := Theory.R₀ V
  pthy := Theory.R₀.def

notation "⌜𝐑₀⌝" => TTheory.R₀
notation "⌜𝐑₀⌝[" V "]" => TTheory.R₀ (V := V)

namespace TTheory.R₀

def addEq (n m : V) : ⌜𝐑₀⌝[V] ⊢ (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m) := by
  have : ⌜𝐑₀⌝[V] ⊢ (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m) ⋏ verums ⟪n, m⟫ :=
    Language.Theory.TProof.byAxm <| by
      left; left; left
      simpa using Theory.R₀.addScheme.mem_toTheory ⟪n, m⟫
  exact System.and₁' this

def mulEq (n m : V) : ⌜𝐑₀⌝[V] ⊢ (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m) := by
  have : ⌜𝐑₀⌝[V] ⊢ (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m) ⋏ verums ⟪n, m⟫ :=
    Language.Theory.TProof.byAxm <| by
      left; left; right
      simpa using Theory.R₀.mulScheme.mem_toTheory ⟪n, m⟫
  exact System.and₁' this

def ne {n m : V} (h : n ≠ m) : ⌜𝐑₀⌝[V] ⊢ ↑n ≠' ↑m := by
  have : ⌜𝐑₀⌝[V] ⊢ ↑n ≠' ↑m ⋏ verums ⟪n, m⟫ :=
    Language.Theory.TProof.byAxm <| by
      left; right
      simpa [h] using Theory.R₀.neqScheme.mem_toTheory ⟪n, m⟫
  exact System.and₁' this

def ltNumeral (n : V): ⌜𝐑₀⌝[V] ⊢ (#'0 <' ↑n ⟷ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all := by
  have : ⌜𝐑₀⌝[V] ⊢ (#'0 <' ↑n ⟷ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all ⋏ verums n :=
    Language.Theory.TProof.byAxm <| by
      right
      simpa using Theory.R₀.ltNumeralScheme.mem_toTheory n
  exact System.and₁' this

end TTheory.R₀

def _root_.LO.Arith.Language.Theory.AddEqAddR₀ (T : ⌜ℒₒᵣ⌝[V].Theory) : ⌜ℒₒᵣ⌝[V].Theory := T |>.union (Theory.EQ V) |>.union (Theory.R₀ V)

def _root_.LO.FirstOrder.Arith.LDef.TDef.addEqAddR₀Def (pT : p⌜ℒₒᵣ⌝.TDef) : p⌜ℒₒᵣ⌝.TDef := pT |>.union Theory.Eq.def |>.union Theory.R₀.def

instance _root_.LO.Arith.Language.Theory.AddEqAddR₀.defined (T : ⌜ℒₒᵣ⌝[V].Theory) (pT : p⌜ℒₒᵣ⌝.TDef) [T.Defined pT] :
    T.AddEqAddR₀.Defined pT.addEqAddR₀Def := union_Defined_union _ _

def _root_.LO.Arith.Language.TTheory.AddEqAddR₀ (T : ⌜ℒₒᵣ⌝[V].TTheory) : ⌜ℒₒᵣ⌝[V].TTheory where
  thy := T.thy.AddEqAddR₀
  pthy := T.pthy.addEqAddR₀Def

@[simp] lemma Language.Theory.self_subset_AddEqAddR₀ (T : ⌜ℒₒᵣ⌝[V].Theory) : T ⊆ T.AddEqAddR₀ :=
  Set.subset_union_of_subset_left Set.subset_union_left _

section

variable {T : ⌜ℒₒᵣ⌝[V].TTheory}

@[simp] lemma R₀_subset_AddEqAddR₀ : ⌜𝐑₀⌝ ⊆ T.AddEqAddR₀ := Set.subset_union_right

@[simp] lemma EQ_subset_AddEqAddR₀ : ⌜𝐄𝐐'⌝ ⊆ T.AddEqAddR₀ := Set.subset_union_of_subset_left Set.subset_union_right _

@[simp] lemma self_subset_AddEqAddR₀ : T ⊆ T.AddEqAddR₀ := Set.subset_union_of_subset_left Set.subset_union_left _

instance : EQTheory T.AddEqAddR₀ where
  refl := Language.Theory.TProof.ofSubset (by simp) TTheory.EQ.eqRefl
  replace := fun p ↦ Language.Theory.TProof.ofSubset (by simp) (TTheory.EQ.eqReplace p)

instance : R₀Theory T.AddEqAddR₀ where
  add := fun n m ↦ Language.Theory.TProof.ofSubset (by simp) (TTheory.R₀.addEq n m)
  mul := fun n m ↦ Language.Theory.TProof.ofSubset (by simp) (TTheory.R₀.mulEq n m)
  ne := fun h ↦ Language.Theory.TProof.ofSubset (by simp) (TTheory.R₀.ne h)
  ltNumeral := fun h ↦ Language.Theory.TProof.ofSubset (by simp) (TTheory.R₀.ltNumeral h)

end

end Formalized

open Formalized

section

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

/-- Provability predicate for arithmetic stronger than $\mathbf{R_0}$. -/
def _root_.LO.FirstOrder.Theory.Provableₐ (p : V) : Prop := (T.codeIn V).AddEqAddR₀.Provable p

variable {T}

lemma provableₐ_iff {σ : Sentence ℒₒᵣ} : T.Provableₐ (⌜σ⌝ : V) ↔ (T.tCodeIn V).AddEqAddR₀ ⊢! ⌜σ⌝ := by
  simp [Language.Theory.TProvable.iff_provable]; rfl

section

variable (T)

def _root_.LO.FirstOrder.Theory.provableₐ : 𝚺₁.Semisentence 1 := .mkSigma
  “p | !T.tDef.addEqAddR₀Def.prv p” (by simp)

lemma provableₐ_defined : 𝚺₁-Predicate (T.Provableₐ : V → Prop) via T.provableₐ := by
  intro v; simp [FirstOrder.Theory.provableₐ, FirstOrder.Theory.Provableₐ, (T.codeIn V).AddEqAddR₀.provable_defined.df.iff]
  symm
  simpa using (T.codeIn V).AddEqAddR₀.provable_defined.df.iff _

@[simp] lemma eval_provableₐ (v) :
    Semiformula.Evalbm V v T.provableₐ.val ↔ T.Provableₐ (v 0) := (provableₐ_defined T).df.iff v

instance provableₐ_definable : 𝚺₁-Predicate (T.Provableₐ : V → Prop) := (provableₐ_defined T).to_definable

/-- instance for definability tactic-/
instance provableₐ_definable' : 𝚺-[0 + 1]-Predicate (T.Provableₐ : V → Prop) := provableₐ_definable T

end

end

end LO.Arith
