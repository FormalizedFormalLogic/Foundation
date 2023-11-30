import Logic.FirstOrder.Basic.Elab
import Logic.FirstOrder.Basic.Elementary

namespace LO

namespace FirstOrder

variable {L : Language.{u}} {μ : Type v} [Subformula.Operator.Eq L]
namespace Subterm

def varSumInL {k} : Fin k → Subterm L μ (k + k) := fun i => #(Fin.castLE (by simp) i)

def varSumInR {k} : Fin k → Subterm L μ (k + k) := fun i => #(Fin.natAdd k i)

@[simp] lemma substs_varSumInL (w₁ w₂ : Fin k → Subterm L μ n) (i) :
  Rew.substs (Matrix.vecAppend rfl w₁ w₂) (varSumInL i) = w₁ i := by simp[varSumInL, Matrix.vecAppend_eq_ite]

@[simp] lemma substs_varSumInR (w₁ w₂ : Fin k → Subterm L μ n) (i) :
  Rew.substs (Matrix.vecAppend rfl w₁ w₂) (varSumInR i) = w₂ i := by simp[varSumInR, Matrix.vecAppend_eq_ite]

@[simp] lemma emb_varSumInL {o} [IsEmpty o] (i : Fin k) :
  (Rew.emb (varSumInL (μ := o) i) : Subterm L μ (k + k)) = varSumInL i := by simp[varSumInL]

@[simp] lemma emb_varSumInR {o} [IsEmpty o] (i : Fin k) :
  (Rew.emb (varSumInR (μ := o) i) : Subterm L μ (k + k)) = varSumInR i := by simp[varSumInR]

end Subterm

namespace Subformula

def vecEq {k} (v w : Fin k → Subterm L μ n) : Subformula L μ n := Matrix.conj (fun i => “!!(v i) = !!(w i)”)

end Subformula

namespace Theory
open Subterm

class Sub (T U : Theory L) where
  sub : T ⊆ U

section Eq

variable (L)

inductive Eq : Theory L
  | refl : Eq “∀ #0 = #0”
  | symm : Eq “∀ ∀ (#1 = #0 → #0 = #1)”
  | trans : Eq “∀ ∀ ∀ (#2 = #1 → #1 = #0 → #2 = #0)”
  | funcExt {k} (f : L.func k) :
    Eq “∀* (!(Subformula.vecEq varSumInL varSumInR) → !!(Subterm.func f varSumInL) = !!(Subterm.func f varSumInR))”
  | relExt {k} (r : L.rel k) :
    Eq “∀* (!(Subformula.vecEq varSumInL varSumInR) → !(Subformula.rel r varSumInL) → !(Subformula.rel r varSumInR))”

end Eq

end Theory

class EqTheory (T : Theory L) where
  eq : Theory.Eq L ⊆ T

attribute [simp] EqTheory.eq

namespace Structure

namespace Eq

@[simp] lemma modelsEqTheory {M : Type u} [Structure L M] [Structure.Eq L M] : M ⊧* Theory.Eq L := by
  intro σ h
  cases h <;> simp[models_def, Subformula.vecEq, Subterm.val_func]
  · intro e h; congr; funext i; exact h i
  case relExt r =>
    simp[Subformula.eval_rel]; intro e h; simp[congr_arg (rel r) (funext h)]

variable (L)

variable {M : Type u} [Structure L M]

def eqv (a b : M) : Prop := (@Subformula.Operator.Eq.eq L _).val ![a, b]

variable {L}

variable (H : M ⊧* Theory.Eq L)

open Subterm Theory Subformula

lemma eqv_refl (a : M) : eqv L a a := by
  have : M ⊧ “∀ #0 = #0” := H (Theory.Eq.refl (L := L))
  simp[models_def] at this
  exact this a

lemma eqv_symm {a b : M} : eqv L a b → eqv L b a := by
  have : M ⊧ “∀ ∀ (#1 = #0 → #0 = #1)” := H (Theory.Eq.symm (L := L))
  simp[models_def] at this
  exact this a b

lemma eqv_trans {a b c : M} : eqv L a b → eqv L b c → eqv L a c := by
  have : M ⊧ “∀ ∀ ∀ (#2 = #1 → #1 = #0 → #2 = #0)” := H (Theory.Eq.trans (L := L))
  simp[models_def] at this
  exact this a b c

lemma eqv_funcExt {k} (f : L.func k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    eqv L (func f v) (func f w) := by
  have : M ⊧ “∀* (!(vecEq varSumInL varSumInR) → !!(Subterm.func f varSumInL) = !!(Subterm.func f varSumInR))” :=
    H (Eq.funcExt f (L := L))
  simp[varSumInL, varSumInR, models_def, vecEq, Subterm.val_func] at this
  simpa[Matrix.vecAppend_eq_ite] using this (Matrix.vecAppend rfl v w) (fun i => by simpa[Matrix.vecAppend_eq_ite] using h i)

lemma eqv_relExt_aux {k} (r : L.rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v → rel r w := by
  have : M ⊧ “∀* (!(vecEq varSumInL varSumInR) → !(Subformula.rel r varSumInL) → !(Subformula.rel r varSumInR))” :=
    H (Eq.relExt r (L := L))
  simp[varSumInL, varSumInR, models_def, vecEq, Subterm.val_func, eval_rel (r := r)] at this
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

def eqvSetoid (H : M ⊧* Theory.Eq L) : Setoid M := Setoid.mk (eqv L) (eqv_equivalence H)

def QuotEq := Quotient (eqvSetoid H)

instance [Inhabited M] : Inhabited (QuotEq H) := ⟨⟦default⟧⟩

lemma of_eq_of {a b : M} : (⟦a⟧ : QuotEq H) = ⟦b⟧ ↔ eqv L a b := Quotient.eq (r := eqvSetoid H)

namespace QuotEq

def func ⦃k⦄ (f : L.func k) (v : Fin k → QuotEq H) : QuotEq H :=
  Quotient.liftVec (s := eqvSetoid H) (⟦Structure.func f ·⟧) (fun _ _ hvw => (of_eq_of H).mpr (eqv_funcExt H f hvw)) v

def rel ⦃k⦄ (r : L.rel k) (v : Fin k → QuotEq H) : Prop :=
  Quotient.liftVec (s := eqvSetoid H) (Structure.rel r) (fun _ _ hvw => eqv_relExt H r hvw) v

variable {H}

instance QuotEqStruc : Structure L (QuotEq H) where
  func := QuotEq.func H
  rel := QuotEq.rel H

lemma funk_mk {k} (f : L.func k) (v : Fin k → M) : Structure.func (M := QuotEq H) f (fun i => ⟦v i⟧) = ⟦Structure.func f v⟧ :=
  Quotient.liftVec_mk (s := eqvSetoid H) _ _ _

lemma rel_mk {k} (r : L.rel k) (v : Fin k → M) : Structure.rel (M := QuotEq H) r (fun i => ⟦v i⟧) ↔ Structure.rel r v :=
  of_eq $ Quotient.liftVec_mk (s := eqvSetoid H) _ _ _

lemma val_mk {e} {ε} (t : Subterm L μ n) : Subterm.val! (QuotEq H) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) t = ⟦Subterm.val! M e ε t⟧ :=
  by induction t <;> simp[*, funk_mk, Subterm.val_func]

lemma eval_mk {e} {ε} {p : Subformula L μ n} :
    Subformula.Eval! (QuotEq H) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) p ↔ Subformula.Eval! M e ε p := by
  induction p using Subformula.rec' <;> simp[*, Subformula.eval_rel, Subformula.eval_nrel, val_mk, rel_mk]
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

lemma models_iff {σ : Sentence L} : (QuotEq H) ⊧ σ ↔ M ⊧ σ := by
  simpa[models_def, Subformula.Val, eq_finZeroElim, Empty.eq_elim] using
    eval_mk (H := H) (e := finZeroElim) (ε := Empty.elim) (p := σ)

variable (H)

lemma elementaryEquiv : QuotEq H ≡ₑ[L] M := fun _ => models_iff

variable {H}

lemma rel_eq (a b : QuotEq H) : (@Subformula.Operator.Eq.eq L _).val (M := QuotEq H) ![a, b] ↔ a = b := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  rw[of_eq_of]; simp[eqv, Subformula.Operator.val];
  simpa[Eval!, Matrix.fun_eq_vec₂, Matrix.empty_eq] using
    eval_mk (H := H) (e := ![]) (ε := ![a, b]) (p := Subformula.Operator.Eq.eq.sentence)

instance : Structure.Eq L (QuotEq H) := ⟨rel_eq⟩

end QuotEq

end Eq

end Structure

lemma consequence_iff_eq {T : Theory L} [EqTheory T] {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Inhabited M] [Structure L M] [Structure.Eq L M], M ⊧* T → M ⊧ σ) := by
  simp[consequence_iff]; constructor
  · intro h M i s _ hM; exact h M hM
  · intro h M i s hM
    have H : M ⊧* Theory.Eq L := Semantics.modelsTheory_of_subset hM EqTheory.eq
    have e : Structure.Eq.QuotEq H ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv H
    exact e.models.mp $ h (Structure.Eq.QuotEq H) (e.modelsTheory.mpr hM)

lemma consequence_iff_eq' {T : Theory L} [EqTheory T] {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Inhabited M] [Structure L M] [Structure.Eq L M] [Theory.Mod M T], M ⊧ σ) := by
  rw[consequence_iff_eq]
  exact ⟨fun h M _ _ _ hT => h M Semantics.Mod.modelsTheory, fun h M i s e hT => @h M i s e ⟨hT⟩⟩

lemma satisfiableₛ_iff_eq {T : Theory L} [EqTheory T] :
    Semantics.Satisfiableₛ T ↔ (∃ (M : Type u) (_ : Inhabited M) (_ : Structure L M) (_ : Structure.Eq L M), M ⊧* T) := by
  simp[satisfiableₛ_iff]; constructor
  · intro ⟨M, i, s, hM⟩;
    have H : M ⊧* Theory.Eq L := Semantics.modelsTheory_of_subset hM EqTheory.eq
    have e : Structure.Eq.QuotEq H ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv H
    exact ⟨Structure.Eq.QuotEq H, inferInstance, inferInstance, inferInstance, e.modelsTheory.mpr hM⟩
  · intro ⟨M, i, s, _, hM⟩; exact ⟨M, i, s, hM⟩

end FirstOrder

end LO
