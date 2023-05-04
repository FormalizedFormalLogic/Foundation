import Logic.Predicate.FirstOrder.Semantics



variable {L : Language.{u}} {μ : Type v} [L.Eq]
namespace SubTerm

def varSumInL {k} : Fin k → SubTerm L μ (k + k) := fun i => #(Fin.castLe (by simp) i)

def varSumInR {k} : Fin k → SubTerm L μ (k + k) := fun i => #(Fin.natAdd k i)

@[simp] lemma substs_varSumInL (w₁ w₂ : Fin k → SubTerm L μ n) (i) :
  substs (Matrix.vecAppend rfl w₁ w₂) (varSumInL i) = w₁ i := by simp[varSumInL, Matrix.vecAppend_eq_ite]

@[simp] lemma substs_varSumInR (w₁ w₂ : Fin k → SubTerm L μ n) (i) :
  substs (Matrix.vecAppend rfl w₁ w₂) (varSumInR i) = w₂ i := by simp[varSumInR, Matrix.vecAppend_eq_ite]

end SubTerm

namespace FirstOrder

namespace SubFormula

def vecEq {k} (v w : Fin k → SubTerm L μ n) : SubFormula L μ n := Matrix.conj (fun i => “ᵀ!(v i) = ᵀ!(w i)”)

end SubFormula

namespace Theory
open SubTerm

class Sub (T U : Theory L) where
  sub : T ⊆ U

section Eq

variable (L)

inductive Eq : Theory L
  | refl : Eq “∀ #0 = #0”
  | symm : Eq “∀ ∀ (#1 = #0 → #0 = #1)”
  | trans : Eq “∀ ∀ ∀ (#2 = #1 → #1 = #0 → #2 = #0)”  
  | funcExt {k} (f : L.func k) :
    Eq “∀* (!(SubFormula.vecEq varSumInL varSumInR) → ᵀ!(SubTerm.func f varSumInL) = ᵀ!(SubTerm.func f varSumInR))”
  | relExt {k} (r : L.rel k) :
    Eq “∀* (!(SubFormula.vecEq varSumInL varSumInR) → !(SubFormula.rel r varSumInL) → !(SubFormula.rel r varSumInR))”

end Eq

end Theory

abbrev EqTheory (T : Theory L) := SubTheory (Theory.Eq L) T

namespace EqTheory

variable (T : Theory L) [EqTheory T]

lemma subset : Theory.Eq L ⊆ T := SubTheory.sub 

end EqTheory

namespace Structure

namespace Eq

variable (L)

variable {M : Type u} [Structure L M]

def eqv (a b : M) : Prop := rel (L := L) Language.Eq.eq ![a, b]

variable {L}

variable (H : M ⊧₁* Theory.Eq L)

open SubTerm Theory SubFormula

lemma eqv_refl (a : M) : eqv L a a := by
  have : M ⊧₁ “∀ #0 = #0” := H (Theory.Eq.refl (L := L))
  simp[models_def] at this
  exact this a

lemma eqv_symm {a b : M} : eqv L a b → eqv L b a := by
  have : M ⊧₁ “∀ ∀ (#1 = #0 → #0 = #1)” := H (Theory.Eq.symm (L := L))
  simp[models_def] at this
  exact this a b

lemma eqv_trans {a b c : M} : eqv L a b → eqv L b c → eqv L a c := by
  have : M ⊧₁ “∀ ∀ ∀ (#2 = #1 → #1 = #0 → #2 = #0)” := H (Theory.Eq.trans (L := L))
  simp[models_def] at this
  exact this a b c

lemma eqv_funcExt {k} (f : L.func k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    eqv L (func f v) (func f w) := by
  have : M ⊧₁ “∀* (!(vecEq varSumInL varSumInR) → ᵀ!(SubTerm.func f varSumInL) = ᵀ!(SubTerm.func f varSumInR))” :=
    H (Eq.funcExt f (L := L))
  simp[varSumInL, varSumInR, models_def, vecEq, SubTerm.val_func] at this
  simpa[Matrix.vecAppend_eq_ite] using this (Matrix.vecAppend rfl v w) (fun i => by simpa[Matrix.vecAppend_eq_ite] using h i)

lemma eqv_relExt_aux {k} (r : L.rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v → rel r w := by
  have : M ⊧₁ “∀* (!(vecEq varSumInL varSumInR) → !(SubFormula.rel r varSumInL) → !(SubFormula.rel r varSumInR))” :=
    H (Eq.relExt r (L := L))
  simp[varSumInL, varSumInR, models_def, vecEq, SubTerm.val_func, eval_rel (r := r)] at this
  simpa[eval_rel, Matrix.vecAppend_eq_ite] using this (Matrix.vecAppend rfl v w) (fun i => by simpa[Matrix.vecAppend_eq_ite] using h i)

lemma eqv_relExt {k} (r : L.rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v = rel r w := by
  simp; constructor
  · exact eqv_relExt_aux H r h
  · exact eqv_relExt_aux H r (fun i => eqv_symm H (h i))

lemma eqv_equivalence : Equivalence (eqv L (M := M)) where
  refl := eqv_refl H
  symm := eqv_symm H
  trans := eqv_trans H

instance eqvSetoid : Setoid M := Setoid.mk (eqv L) (eqv_equivalence H)

def QuotEq := Quotient (eqvSetoid H)

instance [Inhabited M] : Inhabited (QuotEq H) := ⟨⟦default⟧⟩

lemma of_eq_of {a b : M} : (⟦a⟧ : QuotEq H) = ⟦b⟧ ↔ eqv L a b := Quotient.eq (r := eqvSetoid H)

namespace QuotEq

def func {k} (f : L.func k) (v : Fin k → QuotEq H) : QuotEq H :=
  Quotient.liftVec (s := eqvSetoid H) (⟦Structure.func f ·⟧) (fun _ _ hvw => (of_eq_of H).mpr (eqv_funcExt H f hvw)) v

def rel {k} (r : L.rel k) (v : Fin k → QuotEq H) : Prop :=
  Quotient.liftVec (s := eqvSetoid H) (Structure.rel r) (fun _ _ hvw => eqv_relExt H r hvw) v

variable {H}

instance QuotEqStruc : Structure L (QuotEq H) where
  func := QuotEq.func H
  rel := QuotEq.rel H

lemma funk_mk {k} (f : L.func k) (v : Fin k → M) : Structure.func (M := QuotEq H) f (fun i => ⟦v i⟧) = ⟦Structure.func f v⟧ :=
  Quotient.liftVec_mk (s := eqvSetoid H) _ _ _

lemma rel_mk {k} (r : L.rel k) (v : Fin k → M) : Structure.rel (M := QuotEq H) r (fun i => ⟦v i⟧) ↔ Structure.rel r v :=
  of_eq $ Quotient.liftVec_mk (s := eqvSetoid H) _ _ _

lemma val_mk {e} {ε} (t : SubTerm L μ n) : SubTerm.val! (QuotEq H) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) t = ⟦SubTerm.val! M e ε t⟧ :=
  by induction t <;> simp[*, funk_mk, SubTerm.val_func]

lemma eval_mk {e} {ε} {p : SubFormula L μ n} :
    SubFormula.Eval! (QuotEq H) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) p ↔ SubFormula.Eval! M e ε p := by
  induction p using SubFormula.rec' <;> simp[*, SubFormula.eval_rel, SubFormula.eval_nrel, val_mk, rel_mk]
  case hall n p ih =>
    constructor
    · intro h a; exact (ih (e := a :> e)).mp (by simpa[Matrix.comp_vecCons] using h ⟦a⟧)
    · intro h a;
      induction' a using Quotient.ind with a
      simpa[Matrix.comp_vecCons] using ih.mpr (h a)
  case hex n p ih =>
    constructor
    · intro ⟨a, h⟩
      induction' a using Quotient.ind with a
      exact ⟨a, (ih (e := a :> e)).mp (by simpa[Matrix.comp_vecCons] using h)⟩
    · intro ⟨a, h⟩; exact ⟨⟦a⟧, by simpa[Matrix.comp_vecCons] using ih.mpr h⟩

lemma models_iff {σ : Sentence L} : (QuotEq H) ⊧₁ σ ↔ M ⊧₁ σ := by
  simpa[models_def, SubFormula.Val, eq_finZeroElim, Empty.eq_elim] using
    eval_mk (H := H) (e := finZeroElim) (ε := Empty.elim) (p := σ)

variable (H)

lemma elementaryEquiv : QuotEq H ≃ₑ[L] M := fun _ => models_iff

variable {H}

lemma rel_eq (a b : QuotEq H) : Structure.rel (L := L) (M := QuotEq H) Language.Eq.eq ![a, b] ↔ (a = b) := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  simp[rel_mk]; rw[of_eq_of]; rfl

instance : Structure.Eq L (QuotEq H) := ⟨rel_eq⟩

end QuotEq

end Eq

end Structure

lemma consequence_iff_eq {T : Theory L} [EqTheory T] {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Inhabited M] [Structure L M] [Structure.Eq L M], M ⊧₁* T → M ⊧₁ σ) := by
  simp[consequence_iff]; constructor
  · intro h M i s _ hM; exact h M hM
  · intro h M i s hM
    have H : M ⊧₁* Theory.Eq L := Semantics.realizeTheory_of_subset hM (EqTheory.subset T)
    have e : Structure.Eq.QuotEq H ≃ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv H
    exact e.models.mp $ h (Structure.Eq.QuotEq H) (e.modelsₛ.mpr hM)

lemma satisfiableₛ_iff_eq {T : Theory L} [EqTheory T] :
    Semantics.Satisfiableₛ T ↔ (∃ (M : Type u) (_ : Inhabited M) (_ : Structure L M) (_ : Structure.Eq L M), M ⊧₁* T) := by
  simp[satisfiableₛ_iff]; constructor
  · intro ⟨M, i, s, hM⟩;
    have H : M ⊧₁* Theory.Eq L := Semantics.realizeTheory_of_subset hM (EqTheory.subset T)
    have e : Structure.Eq.QuotEq H ≃ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv H
    exact ⟨Structure.Eq.QuotEq H, inferInstance, inferInstance, inferInstance, e.modelsₛ.mpr hM⟩
  · intro ⟨M, i, s, _, hM⟩; exact ⟨M, i, s, hM⟩

end FirstOrder
