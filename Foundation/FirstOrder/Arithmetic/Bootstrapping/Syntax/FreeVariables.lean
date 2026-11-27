module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Coding

/-!
# Free variables of coded terms and formulas

The free variables of coded terms and formulas, and coded semisentences.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {Γ : Polarity} {m : ℕ} {f i k p q t v R : V}

/-! ## Terms -/

namespace TermFreeVariables

def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. y = 0”
  fvar := .mkSigma “y x. !insertDef y x 0”
  func := .mkSigma “y k f v v'. !listUnionDef y v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar _ _          := ∅
  fvar _ x          := {x}
  func _ _ _ _ v'   := listUnion v'
  bvar_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  fvar_defined := .mk fun v ↦ by simp [blueprint, singleton_eq_insert, emptyset_def]
  func_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]; simp

end TermFreeVariables

section termFreeVariables

open TermFreeVariables

variable (L)

noncomputable def termFreeVariables (t : V) : V := construction.result L ![] t

noncomputable def termFreeVariablesVec (k v : V) : V := construction.resultVec L ![] k v

noncomputable def termFreeVariablesGraph : 𝚺ᴬ₁.Semisentence 2 := blueprint.result L

noncomputable def termFreeVariablesVecGraph : 𝚺ᴬ₁.Semisentence 3 := blueprint.resultVec L

variable {L}

@[simp]
lemma termFreeVariables_bvar (z : V) :
    termFreeVariables L ^#z = ∅ := by simp [termFreeVariables, construction]

@[simp]
lemma termFreeVariables_fvar (x : V) :
    termFreeVariables L ^&x = {x} := by simp [termFreeVariables, construction]

@[simp]
lemma termFreeVariables_func (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termFreeVariables L (^func k f v) = listUnion (termFreeVariablesVec L k v) := by
  simp [termFreeVariables, construction, hkf, hv]; rfl

@[simp]
lemma len_termFreeVariablesVec (hv : IsUTermVec L k v) :
    len (termFreeVariablesVec L k v) = k := construction.resultVec_lh L _ hv

@[simp]
lemma nth_termFreeVariablesVec (hv : IsUTermVec L k v) (hi : i < k) :
    (termFreeVariablesVec L k v).[i] = termFreeVariables L v.[i] :=
  construction.nth_resultVec L _ hv hi

section

instance termFreeVariables.defined :
    𝚺ᴬ₁-Function₁ (termFreeVariables (V := V) L) via termFreeVariablesGraph L :=
  construction.result_defined

instance termFreeVariables.definable : 𝚺ᴬ₁-Function₁ (termFreeVariables (V := V) L) :=
  termFreeVariables.defined.to_definable

instance termFreeVariables.definable' : Γᴬ_[m + 1]-Function₁ (termFreeVariables (V := V) L) :=
  termFreeVariables.definable.of_sigmaOne

instance termFreeVariablesVec.defined :
    𝚺ᴬ₁-Function₂ (termFreeVariablesVec (V := V) L) via termFreeVariablesVecGraph L :=
  construction.resultVec_defined

instance termFreeVariablesVec.definable : 𝚺ᴬ₁-Function₂ (termFreeVariablesVec (V := V) L) :=
  termFreeVariablesVec.defined.to_definable

instance termFreeVariablesVec.definable' :
    Γᴬ_[m + 1]-Function₂ (termFreeVariablesVec (V := V) L) :=
  termFreeVariablesVec.definable.of_sigmaOne

end

lemma termFreeVariablesVec_eq_empty_iff (hv : IsUTermVec L k v) :
    listUnion (termFreeVariablesVec L k v) = ∅ ↔ ∀ i < k, termFreeVariables L v.[i] = ∅ := by
  rw [listUnion_eq_empty_iff, len_termFreeVariablesVec hv]
  exact forall₂_congr fun i hi ↦ by rw [nth_termFreeVariablesVec hv hi]

lemma termShiftVec_eq_self_iff_forall (hv : IsUTermVec L k v) :
    termShiftVec L k v = v ↔ ∀ i < k, termShift L v.[i] = v.[i] := by
  constructor
  · intro h i hi
    rw [← nth_termShiftVec hv hi, h]
  · intro h
    apply nth_ext' k (by simp [hv]) hv.lh.symm
    intro i hi
    rw [nth_termShiftVec hv hi]
    exact h i hi

lemma termShift_eq_self_iff (ht : IsUTerm L t) : termShift L t = t ↔ termFreeVariables L t = ∅ := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z
    simp
  · intro x
    rw [termShift_fvar, termFreeVariables_fvar]
    exact iff_of_false (by simp [qqFvar]) fun h ↦ by simpa using congrArg (x ∈ ·) h
  · intro k f v hf hv ih
    rw [termShift_func hf hv, termFreeVariables_func hf hv, qqFunc_inj,
      termShiftVec_eq_self_iff_forall hv, termFreeVariablesVec_eq_empty_iff hv]
    simpa using forall₂_congr ih

lemma termShiftVec_eq_self_iff (hv : IsUTermVec L k v) :
    termShiftVec L k v = v ↔ listUnion (termFreeVariablesVec L k v) = ∅ := by
  rw [termShiftVec_eq_self_iff_forall hv, termFreeVariablesVec_eq_empty_iff hv]
  exact forall₂_congr fun i hi ↦ termShift_eq_self_iff (hv.nth hi)

variable {n : V}

variable (L) in
def _root_.FFL.FirstOrder.Language.IsClosedSemiterm (n t : V) : Prop :=
  IsSemiterm L n t ∧ termFreeVariables L t = ∅

variable (L) in
abbrev _root_.FFL.FirstOrder.Language.IsClosedTerm (t : V) : Prop := L.IsClosedSemiterm 0 t

lemma _root_.FFL.FirstOrder.Language.IsClosedSemiterm.isSemiterm (h : L.IsClosedSemiterm n t) :
    IsSemiterm L n t := h.1

lemma _root_.FFL.FirstOrder.Language.IsClosedSemiterm.termFreeVariables_eq
    (h : L.IsClosedSemiterm n t) : termFreeVariables L t = ∅ := h.2

lemma _root_.FFL.FirstOrder.Language.IsClosedSemiterm.termShift_eq (h : L.IsClosedSemiterm n t) :
    termShift L t = t :=
  (termShift_eq_self_iff h.isSemiterm.isUTerm).mpr h.termFreeVariables_eq

lemma _root_.FFL.FirstOrder.Language.IsClosedSemiterm.of_termShift_eq
    (ht : IsSemiterm L n t) (h : termShift L t = t) : L.IsClosedSemiterm n t :=
  ⟨ht, (termShift_eq_self_iff ht.isUTerm).mp h⟩

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsClosedSemiterm.bvar_iff {z : V} :
    L.IsClosedSemiterm n ^#z ↔ z < n := by
  simp [Language.IsClosedSemiterm]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsClosedSemiterm.not_fvar (x : V) :
    ¬L.IsClosedSemiterm n ^&x := by
  intro h
  simpa using h.termShift_eq

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsClosedSemiterm.numeral (n x : V) :
    (ℒₒᵣ).IsClosedSemiterm n (Arithmetic.numeral x) :=
  .of_termShift_eq (Arithmetic.numeral_semiterm n x) (Arithmetic.numeral_shift x)

end termFreeVariables

/-! ## Formulas -/

namespace FreeVariables

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ M, !(termFreeVariablesVecGraph L) M k v ∧ !listUnionDef y M”
  nrel := .mkSigma “y param k R v. ∃ M, !(termFreeVariablesVecGraph L) M k v ∧ !listUnionDef y M”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !unionDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !unionDef y y₁ y₂”
  all := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ y = y₁”
  exs := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ y = y₁”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k _ v ↦ listUnion (termFreeVariablesVec L k v)
  nrel {_} := fun k _ v ↦ listUnion (termFreeVariablesVec L k v)
  verum {_} := ∅
  falsum {_} := ∅
  and {_} := fun _ _ y₁ y₂ ↦ y₁ ∪ y₂
  or {_} := fun _ _ y₁ y₂ ↦ y₁ ∪ y₂
  all {_} := fun _ ys ↦ ys.[0]
  exs {_} := fun _ ys ↦ ys.[0]
  rel_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]; simp
  nrel_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]; simp
  verum_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  falsum_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]

end FreeVariables

section freeVariables

open FreeVariables

variable (L)

noncomputable def freeVariables (p : V) : V := (construction L).result L 0 p

noncomputable def freeVariablesGraph : 𝚺ᴬ₁.Semisentence 2 :=
  (blueprint L).result L |>.rew (Rew.subst ![#0, ‘0’, #1])

variable {L}

section

instance freeVariables.defined : 𝚺ᴬ₁-Function₁[V] freeVariables L via freeVariablesGraph L :=
  .mk fun v ↦ by
    simpa [freeVariablesGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
      using! (construction L).result_defined.defined ![v 0, 0, v 1]

instance freeVariables.definable : 𝚺ᴬ₁-Function₁[V] freeVariables L :=
  freeVariables.defined.to_definable

instance freeVariables.definable' : Γᴬ_[m + 1]-Function₁[V] freeVariables L :=
  freeVariables.definable.of_sigmaOne

end

@[simp]
lemma freeVariables_rel (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    freeVariables L (^rel k R v) = listUnion (termFreeVariablesVec L k v) := by
  simp [freeVariables, hR, hv, construction]

@[simp]
lemma freeVariables_nrel (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    freeVariables L (^nrel k R v) = listUnion (termFreeVariablesVec L k v) := by
  simp [freeVariables, hR, hv, construction]

@[simp]
lemma freeVariables_verum : freeVariables L (^⊤ : V) = ∅ := by
  simp [freeVariables, construction]

@[simp]
lemma freeVariables_falsum : freeVariables L (^⊥ : V) = ∅ := by
  simp [freeVariables, construction]

@[simp]
lemma freeVariables_and (hp : IsUFormula L p) (hq : IsUFormula L q) :
    freeVariables L (p ^⋏ q) = freeVariables L p ∪ freeVariables L q := by
  simp [freeVariables, hp, hq, construction]

@[simp]
lemma freeVariables_or (hp : IsUFormula L p) (hq : IsUFormula L q) :
    freeVariables L (p ^⋎ q) = freeVariables L p ∪ freeVariables L q := by
  simp [freeVariables, hp, hq, construction]

@[simp]
lemma freeVariables_all (hp : IsUFormula L p) : freeVariables L (^∀ p) = freeVariables L p := by
  simp [freeVariables, hp, construction]

@[simp]
lemma freeVariables_exs (hp : IsUFormula L p) : freeVariables L (^∃ p) = freeVariables L p := by
  simp [freeVariables, hp, construction]

@[simp]
lemma freeVariables_neg (hp : IsUFormula L p) : freeVariables L (neg L p) = freeVariables L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    simp [hR, hv]
  · intro k R v hR hv
    simp [hR, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq
    simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ih
    simp [hp, hp.neg, ih]
  · intro p hp ih
    simp [hp, hp.neg, ih]

lemma shift_eq_self_iff (hp : IsUFormula L p) : shift L p = p ↔ freeVariables L p = ∅ := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [shift_rel hR hv, freeVariables_rel hR hv, qqRel_inj, termShiftVec_eq_self_iff hv]
    simp
  · intro k R v hR hv
    rw [shift_nrel hR hv, freeVariables_nrel hR hv, qqNRel_inj, termShiftVec_eq_self_iff hv]
    simp
  · simp
  · simp
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq, freeVariables_and hp hq, qqAnd_inj, ihp, ihq]
    simp [mem_ext_iff, forall_and]
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq, freeVariables_or hp hq, qqOr_inj, ihp, ihq]
    simp [mem_ext_iff, forall_and]
  · intro p hp ih
    rw [shift_all hp, freeVariables_all hp, qqAll_inj, ih]
  · intro p hp ih
    rw [shift_exs hp, freeVariables_exs hp, qqExs_inj, ih]

end freeVariables

section sentence

variable (L) {n : V}

def _root_.FFL.FirstOrder.Language.IsSemisentence (n p : V) : Prop :=
  IsSemiformula L n p ∧ freeVariables L p = ∅

abbrev _root_.FFL.FirstOrder.Language.IsSentence (p : V) : Prop := L.IsSemisentence 0 p

noncomputable def isSemisentence : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “n p. !(isSemiformula L).sigma n p ∧ !(freeVariablesGraph L) 0 p”)
  (.mkPi “n p. !(isSemiformula L).pi n p ∧ ∀ y, !(freeVariablesGraph L) y p → y = 0”)

instance _root_.FFL.FirstOrder.Language.IsSemisentence.defined :
    𝚫ᴬ₁-Relation (L.IsSemisentence (V := V)) via isSemisentence L := .mk <| by
  constructor
  · intro v
    simp [isSemisentence, Bounding.HierarchySymbol.Semiformula.val_sigma, IsSemiformula.defined.iff,
      freeVariables.defined.iff, eq_comm]
  · intro v
    simp [isSemisentence, Bounding.HierarchySymbol.Semiformula.val_sigma, IsSemiformula.defined.iff,
      freeVariables.defined.iff, Language.IsSemisentence, emptyset_def, eq_comm]

instance _root_.FFL.FirstOrder.Language.IsSemisentence.definable :
    𝚫ᴬ₁-Relation (L.IsSemisentence (V := V)) :=
  (Language.IsSemisentence.defined (L := L) (V := V)).to_definable

instance _root_.FFL.FirstOrder.Language.IsSemisentence.definable' {m : ℕ} {Γ : SigmaPiDelta} :
    Γᴬ_[m + 1]-Relation (L.IsSemisentence (V := V)) :=
  (Language.IsSemisentence.definable (L := L) (V := V)).of_deltaOne

noncomputable def isSentence : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “p. !(isSemisentence L).sigma 0 p”)
  (.mkPi “p. !(isSemisentence L).pi 0 p”)

variable {L}

instance _root_.FFL.FirstOrder.Language.IsSentence.defined :
    𝚫ᴬ₁-Predicate (L.IsSentence (V := V)) via isSentence L := .mk <| by
  constructor
  · intro v
    simp [isSentence, Bounding.HierarchySymbol.Semiformula.val_sigma]
  · intro v
    simp [isSentence, Bounding.HierarchySymbol.Semiformula.val_sigma]

lemma isSentence_sigma_iff (p : V) : V ⊧/![p] (isSentence L).sigma.val ↔ L.IsSentence p := by
  simp [isSentence, Bounding.HierarchySymbol.Semiformula.val_sigma]

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.isSemiformula
    (h : L.IsSemisentence n p) : IsSemiformula L n p := h.1

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.freeVariables_eq
    (h : L.IsSemisentence n p) : freeVariables L p = ∅ := h.2

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.shift_eq (h : L.IsSemisentence n p) :
    shift L p = p :=
  (shift_eq_self_iff h.isSemiformula.isUFormula).mpr h.freeVariables_eq

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.of_shift_eq
    (hp : IsSemiformula L n p) (h : shift L p = p) : L.IsSemisentence n p :=
  ⟨hp, (shift_eq_self_iff hp.isUFormula).mp h⟩

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.quote {n : ℕ} (σ : Semisentence L n) :
    L.IsSemisentence (n : V) ⌜σ⌝ :=
  .of_shift_eq (Sentence.quote_isSemiformula σ) (Semisentence.shift_quote σ)

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.sound {n p : ℕ} (h : L.IsSemisentence n p) :
    ∃ σ : Semisentence L n, ⌜σ⌝ = p := by
  obtain ⟨φ, rfl⟩ := IsSemiformula.sound h.isSemiformula
  have h₁ : Rewriting.shift φ = φ := by simpa [← Semiformula.quote_shift] using h.shift_eq
  use φ.toEmpty (Semiformula.freeVariables_eq_empty_of_shift_eq h₁)
  simp [Sentence.quote_def]

lemma _root_.FFL.FirstOrder.Language.IsSemisentence.sound_natCast {n p : ℕ}
    (h : L.IsSemisentence (n : V) p) : ∃ σ : Semisentence L n, ⌜σ⌝ = p :=
  Language.IsSemisentence.sound <| (Defined.shigmaOne_absolute V (Language.IsSemisentence.defined L)
    (Language.IsSemisentence.defined L) ![n, p]).mpr h

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSentence.quote (σ : Sentence L) :
    L.IsSentence (⌜σ⌝ : V) :=
  .of_shift_eq (Sentence.quote_isSemiformula₀ σ) (Semisentence.shift_quote σ)

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.verum (n : V) : L.IsSemisentence n ^⊤ := by
  simp [Language.IsSemisentence]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.falsum (n : V) : L.IsSemisentence n ^⊥ := by
  simp [Language.IsSemisentence]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.and_iff :
    L.IsSemisentence n (p ^⋏ q) ↔ L.IsSemisentence n p ∧ L.IsSemisentence n q := by
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := IsSemiformula.and.mp h.isSemiformula
    have hs := h.shift_eq
    rw [shift_and hp.isUFormula hq.isUFormula, qqAnd_inj] at hs
    exact ⟨.of_shift_eq hp hs.1, .of_shift_eq hq hs.2⟩
  · rintro ⟨hp, hq⟩
    apply Language.IsSemisentence.of_shift_eq
    · simp [hp.isSemiformula, hq.isSemiformula]
    · rw [shift_and hp.isSemiformula.isUFormula hq.isSemiformula.isUFormula,
        hp.shift_eq, hq.shift_eq]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.or_iff :
    L.IsSemisentence n (p ^⋎ q) ↔ L.IsSemisentence n p ∧ L.IsSemisentence n q := by
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := IsSemiformula.or.mp h.isSemiformula
    have hs := h.shift_eq
    rw [shift_or hp.isUFormula hq.isUFormula, qqOr_inj] at hs
    exact ⟨.of_shift_eq hp hs.1, .of_shift_eq hq hs.2⟩
  · rintro ⟨hp, hq⟩
    apply Language.IsSemisentence.of_shift_eq
    · simp [hp.isSemiformula, hq.isSemiformula]
    · rw [shift_or hp.isSemiformula.isUFormula hq.isSemiformula.isUFormula,
        hp.shift_eq, hq.shift_eq]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.all_iff :
    L.IsSemisentence n (^∀ p) ↔ L.IsSemisentence (n + 1) p := by
  simp only [Language.IsSemisentence, IsSemiformula.all]
  apply and_congr_right
  intro hp
  rw [freeVariables_all hp.isUFormula]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.exs_iff :
    L.IsSemisentence n (^∃ p) ↔ L.IsSemisentence (n + 1) p := by
  simp only [Language.IsSemisentence, IsSemiformula.exs]
  apply and_congr_right
  intro hp
  rw [freeVariables_exs hp.isUFormula]

@[simp]
lemma _root_.FFL.FirstOrder.Language.IsSemisentence.neg_iff :
    L.IsSemisentence n (neg L p) ↔ L.IsSemisentence n p := by
  constructor
  · intro h
    have hp : IsSemiformula L n p := IsSemiformula.neg_iff.mp h.isSemiformula
    exact ⟨hp, by rw [← freeVariables_neg hp.isUFormula]; exact h.freeVariables_eq⟩
  · intro h
    exact ⟨by simp [h.isSemiformula],
      by rw [freeVariables_neg h.isSemiformula.isUFormula]; exact h.freeVariables_eq⟩

end sentence

end Bootstrapping
end FFL.FirstOrder.Arithmetic
