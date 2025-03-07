import Foundation.Arithmetization.ISigmaOne.HFS

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

section

variable {V : Type*} [ORingStruc V]

variable (V)

structure _root_.LO.FirstOrder.Arith.LDef where
  func : 𝚺₀.Semisentence 2
  rel : 𝚺₀.Semisentence 2

protected structure Language where
  Func (arity : V) : V → Prop
  Rel (arity : V) : V → Prop

variable {V}

namespace Language

protected class Defined (L : Arith.Language V) (pL : outParam LDef) where
  func : 𝚺₀-Relation L.Func via pL.func
  rel : 𝚺₀-Relation L.Rel via pL.rel

variable {L : Arith.Language V} {pL : LDef} [L.Defined pL]

@[simp] lemma Defined.eval_func (v) :
    Semiformula.Evalbm V v pL.func.val ↔ L.Func (v 0) (v 1) := Defined.func.df.iff v

@[simp] lemma Defined.eval_rel_iff (v) :
    Semiformula.Evalbm V v pL.rel.val ↔ L.Rel (v 0) (v 1) := Defined.rel.df.iff v

instance Defined.func_definable : 𝚺₀-Relation L.Func := Defined.func.to_definable

instance Defined.rel_definable : 𝚺₀-Relation L.Rel := Defined.rel.to_definable

@[simp, definability] instance Defined.func_definable' (ℌ) : ℌ-Relation L.Func :=
  HierarchySymbol.Boldface.of_zero Defined.func_definable

@[simp, definability] instance Defined.rel_definable' (ℌ) : ℌ-Relation L.Rel :=
  HierarchySymbol.Boldface.of_zero Defined.rel_definable

end Language

end

section

variable {L₀ : Language} [L₀.ORing]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

instance (k) : Semiterm.Operator.GoedelNumber L₀ (L.Func k) := ⟨fun f ↦ Semiterm.Operator.numeral L₀ (Encodable.encode f)⟩

instance (k) : Semiterm.Operator.GoedelNumber L₀ (L.Rel k) := ⟨fun r ↦ Semiterm.Operator.numeral L₀ (Encodable.encode r)⟩

variable (L)

class DefinableLanguage extends Arith.LDef where
  func_iff {k c : ℕ} :
    c ∈ Set.range (Encodable.encode : L.Func k → ℕ) ↔ ℕ ⊧/![k, c] func.val
  rel_iff {k c : ℕ} :
    c ∈ Set.range (Encodable.encode : L.Rel k → ℕ) ↔ ℕ ⊧/![k, c] rel.val

def _root_.LO.FirstOrder.Language.lDef [d : DefinableLanguage L] : LDef := d.toLDef

variable {L}

variable [DefinableLanguage L]

variable {V : Type*} [ORingStruc V]

variable (L V)

def _root_.LO.FirstOrder.Language.codeIn : Arith.Language V where
  Func := fun x y ↦ V ⊧/![x, y] L.lDef.func.val
  Rel := fun x y ↦ V ⊧/![x, y] L.lDef.rel.val

lemma _root_.LO.FirstOrder.Language.codeIn_func_def : (L.codeIn V).Func = fun x y ↦ V ⊧/![x, y] L.lDef.func.val := rfl

variable {L V}

variable [V ⊧ₘ* 𝐏𝐀⁻]

instance : (L.codeIn V).Defined L.lDef where
  func := by intro v; simp [Language.codeIn, ←Matrix.fun_eq_vec₂]
  rel := by intro v; simp [Language.codeIn, ←Matrix.fun_eq_vec₂]

instance : GoedelQuote (L.Func k) V := ⟨fun f ↦ ↑(Encodable.encode f)⟩

instance : GoedelQuote (L.Rel k) V := ⟨fun R ↦ ↑(Encodable.encode R)⟩

omit [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L] in
lemma quote_func_def (f : L.Func k) : (⌜f⌝ : V) = ↑(Encodable.encode f) := rfl

omit [(k : ℕ) → Encodable (L.Func k)] [DefinableLanguage L] in
lemma quote_rel_def (R : L.Rel k) : (⌜R⌝ : V) = ↑(Encodable.encode R) := rfl

lemma codeIn_func_quote_iff {k x : ℕ} : (L.codeIn V).Func k x ↔ ∃ f : L.Func k, Encodable.encode f = x :=
  have : V ⊧/![k, x] L.lDef.func.val ↔ ℕ ⊧/![k, x] L.lDef.func.val := by
    simpa using models_iff_of_Sigma0 (V := V) (σ := L.lDef.func.val) (by simp) (e := ![k, x])
  Iff.trans this <| Iff.trans (DefinableLanguage.func_iff.symm) <| (by simp)

lemma codeIn_rel_quote_iff {k x : ℕ} : (L.codeIn V).Rel k x ↔ ∃ R : L.Rel k, Encodable.encode R = x :=
  have : V ⊧/![k, x] L.lDef.rel.val ↔ ℕ ⊧/![k, x] L.lDef.rel.val := by
    simpa using models_iff_of_Sigma0 (V := V) (σ := L.lDef.rel.val) (by simp) (e := ![k, x])
  Iff.trans this <| Iff.trans (DefinableLanguage.rel_iff.symm) <| (by simp [quote_rel_def])

@[simp] lemma codeIn_func_quote {k : ℕ} (f : L.Func k) : (L.codeIn V).Func k ⌜f⌝ :=
  (codeIn_func_quote_iff (V := V)).mpr ⟨f, rfl⟩

@[simp] lemma codeIn_rel_quote {k : ℕ} (r : L.Rel k) : (L.codeIn V).Rel k ⌜r⌝ :=
  (codeIn_rel_quote_iff (V := V)).mpr ⟨r, rfl⟩

omit [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L] in
@[simp] lemma quote_func_inj (f₁ f₂ : L.Func k) : (⌜f₁⌝ : V) = (⌜f₂⌝ : V) ↔ f₁ = f₂ := by
  simp [quote_func_def]

omit [(k : ℕ) → Encodable (L.Func k)] [DefinableLanguage L] in
@[simp] lemma quote_rel_inj (R₁ R₂ : L.Rel k) : (⌜R₁⌝ : V) = (⌜R₂⌝ : V) ↔ R₁ = R₂ := by
  simp [quote_rel_def]

omit [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L] in
@[simp] lemma coe_quote_func_nat (f : L.Func k) : ((⌜f⌝ : ℕ) : V) = (⌜f⌝ : V) := by
  simp [quote_func_def]

omit [(k : ℕ) → Encodable (L.Func k)] [DefinableLanguage L] in
@[simp] lemma coe_quote_rel_nat (R : L.Rel k) : ((⌜R⌝ : ℕ) : V) = (⌜R⌝ : V) := by
  simp [quote_rel_def]

end

/-- TODO: move to Basic/Syntax/Language.lean-/
lemma _root_.LO.FirstOrder.Language.ORing.of_mem_range_encode_func {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : FirstOrder.Language.Func ℒₒᵣ k → ℕ) ↔
    (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) := by
  constructor
  · rintro ⟨f, rfl⟩
    match k, f with
    | 0, Language.ORing.Func.zero => simp; rfl
    | 0, Language.ORing.Func.one => simp; rfl
    | 2, Language.ORing.Func.add => simp; rfl
    | 2, Language.ORing.Func.mul => simp; rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Language.ORing.Func.zero, rfl⟩
    · exact ⟨Language.ORing.Func.one, rfl⟩
    · exact ⟨Language.ORing.Func.add, rfl⟩
    · exact ⟨Language.ORing.Func.mul, rfl⟩

/-- TODO: move to Basic/Syntax/Language.lean-/
lemma _root_.LO.FirstOrder.Language.ORing.of_mem_range_encode_rel {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : FirstOrder.Language.Rel ℒₒᵣ k → ℕ) ↔
    (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1) := by
  constructor
  · rintro ⟨r, rfl⟩
    match k, r with
    | 2, Language.ORing.Rel.eq => simp; rfl
    | 2, Language.ORing.Rel.lt => simp; rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Language.ORing.Rel.eq, rfl⟩
    · exact ⟨Language.ORing.Rel.lt, rfl⟩

instance : DefinableLanguage ℒₒᵣ where
  func := .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)” (by simp)
  rel  := .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” (by simp)
  func_iff {k c} := by
    simpa [models_iff] using Language.ORing.of_mem_range_encode_func
  rel_iff {k c} := by
    simpa [models_iff] using Language.ORing.of_mem_range_encode_rel

namespace Formalized

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

abbrev LOR : Arith.Language V := Language.codeIn ℒₒᵣ V

abbrev LOR.code : LDef := Language.lDef ℒₒᵣ

notation "⌜ℒₒᵣ⌝" => LOR

notation "⌜ℒₒᵣ⌝[" V "]" => LOR (V := V)

notation "p⌜ℒₒᵣ⌝" => LOR.code

variable (V)

instance LOR.defined : (⌜ℒₒᵣ⌝ : Arith.Language V).Defined (Language.lDef ℒₒᵣ) := inferInstance

variable {V}

def zeroIndex : ℕ := Encodable.encode (Language.Zero.zero : (ℒₒᵣ : FirstOrder.Language).Func 0)

def oneIndex : ℕ := Encodable.encode (Language.One.one : (ℒₒᵣ : FirstOrder.Language).Func 0)

def addIndex : ℕ := Encodable.encode (Language.Add.add : (ℒₒᵣ : FirstOrder.Language).Func 2)

def mulIndex : ℕ := Encodable.encode (Language.Mul.mul : (ℒₒᵣ : FirstOrder.Language).Func 2)

def eqIndex : ℕ := Encodable.encode (Language.Eq.eq : (ℒₒᵣ : FirstOrder.Language).Rel 2)

def ltIndex : ℕ := Encodable.encode (Language.LT.lt : (ℒₒᵣ : FirstOrder.Language).Rel 2)

@[simp] lemma LOR_func_zeroIndex : ⌜ℒₒᵣ⌝.Func 0 (zeroIndex : V) := by
  simpa using codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.Zero.zero

@[simp] lemma LOR_func_oneIndex : ⌜ℒₒᵣ⌝.Func 0 (oneIndex : V) := by
  simpa using codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.One.one

@[simp] lemma LOR_func_addIndex : ⌜ℒₒᵣ⌝.Func 2 (addIndex : V) := by
  simpa using codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.Add.add

@[simp] lemma LOR_func_mulIndex : ⌜ℒₒᵣ⌝.Func 2 (mulIndex : V) := by
  simpa using codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.Mul.mul

@[simp] lemma LOR_rel_eqIndex : ⌜ℒₒᵣ⌝.Rel 2 (eqIndex : V) := by
  simpa using codeIn_rel_quote (V := V) (L := ℒₒᵣ) Language.Eq.eq

@[simp] lemma LOR_rel_ltIndex : ⌜ℒₒᵣ⌝.Rel 2 (ltIndex : V) := by
  simpa using codeIn_rel_quote (V := V) (L := ℒₒᵣ) Language.LT.lt

lemma lDef.func_def : (ℒₒᵣ).lDef.func = .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)” (by simp) := rfl

lemma coe_zeroIndex_eq : (zeroIndex : V) = 0 := rfl

lemma coe_oneIndex_eq : (oneIndex : V) = 1 := by simp [oneIndex]; rfl

lemma coe_addIndex_eq : (addIndex : V) = 0 := rfl

lemma coe_mulIndex_eq : (mulIndex : V) = 1 := by simp [mulIndex]; rfl

lemma func_iff {k f : V} : ⌜ℒₒᵣ⌝.Func k f ↔ (k = 0 ∧ f = zeroIndex) ∨ (k = 0 ∧ f = oneIndex) ∨ (k = 2 ∧ f = addIndex) ∨ (k = 2 ∧ f = mulIndex) := by
  simp [FirstOrder.Language.codeIn_func_def, lDef.func_def,
    coe_zeroIndex_eq, coe_oneIndex_eq, coe_addIndex_eq, coe_mulIndex_eq]

end Formalized

end LO.Arith

end
