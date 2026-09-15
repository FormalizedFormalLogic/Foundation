module
public import Foundation.FirstOrder.Syntax.Classical.Eq
public import Foundation.FirstOrder.Tarski.Operator
public import Foundation.FirstOrder.Tarski.Elementary
public import Foundation.Vorspiel.Quotient

@[expose] public section

namespace FFL

namespace FirstOrder

variable {L : Language} {ξ : Type*} [Semiformula.Operator.Eq L]

namespace Structure

namespace Eq

variable (L) (M : Type*) [Nonempty M] [Structure L M]

@[simp] instance models_eq [Structure.Eq L M] :
    M↓[L] ⊧* 𝗘𝗤 L := ⟨by
  intro φ h
  rcases h with (_ | _ | _ | _ | _) <;> simp [models_iff, Theory.Eq.funcExt, Theory.Eq.relExt]
  · simp [Function.comp_def]; grind
  · simp [Function.comp_def]; grind⟩

instance models_eqAxiom' [Structure.Eq L M] : M↓[L] ⊧* 𝗘𝗤 L := models_eq _ _

variable {M}

def eqv (a b : M) : Prop := (@Semiformula.Operator.Eq.eq L _).val ![a, b]

variable {L}

variable [H : M↓[L] ⊧* 𝗘𝗤 L]

open Semiterm Theory Semiformula

lemma eqv_refl (a : M) : eqv L a a := by
  have : M↓[L] ⊧ “∀ x, x = x” := H.models _ (Theory.eqAxiom.refl (L := L))
  have : ∀ x : M, op(=)[L].val ![x, x] := by simpa [models_iff] using this
  exact this a

lemma eqv_symm {a b : M} : eqv L a b → eqv L b a := by
  have : M↓[L] ⊧ “∀ x y, x = y → y = x” := H.models _ (Theory.eqAxiom.symm (L := L))
  have : ∀ x y : M, op(=)[L].val ![x, y] → op(=)[L].val ![y, x] := by simpa [models_iff] using this
  exact this a b

lemma eqv_trans {a b c : M} : eqv L a b → eqv L b c → eqv L a c := by
  have : M↓[L] ⊧ “∀ x y z, x = y → y = z → x = z” := H.models _ (Theory.eqAxiom.trans (L := L))
  have : ∀ x y z : M, op(=)[L].val ![x, y] → op(=)[L].val ![y, z] → op(=)[L].val ![x, z] := by simpa [models_iff] using this
  exact this a b c

lemma eqv_funcExt {k} (f : L.Func k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    eqv L (func f v) (func f w) := by
  have : M↓[L] ⊧ Eq.funcExt f := H.models _ (eqAxiom.funcExt f)
  have :
      ∀ m : Fin (k + k) → M,
      (∀ (i : Fin k), op(=)[L].val ![m (Fin.addCast k i), m (i.addNat k)]) →
        op(=)[L].val ![func f fun i ↦ m (Fin.addCast k i), func f fun i ↦ m (i.addNat k)] := by
    simpa [models_iff, Semiterm.val_func] using! this
  have := this (Matrix.vecAppend rfl v w) (fun i ↦ by simpa [Matrix.vecAppend_eq_ite, eqv] using h i)
  simpa [Semiterm.val_func, Matrix.vecAppend_eq_ite, eqv] using this

lemma eqv_relExt_aux {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v → rel r w := by
  have : M↓[L] ⊧ Eq.relExt r := H.models _ (eqAxiom.relExt r)
  have :
      ∀ m : Fin (k + k) → M,
      (∀ (i : Fin k), op(=)[L].val ![m (Fin.addCast k i), m (i.addNat k)]) →
        (rel r fun i ↦ m (Fin.addCast k i)) → rel r fun i ↦ m (i.addNat k) := by
    simpa [models_iff, Semiterm.val_func, eval_rel] using! this
  have := this (Matrix.vecAppend rfl v w) (fun i ↦ by simpa [Matrix.vecAppend_eq_ite, eqv] using h i)
  simpa [Semiterm.val_func, Matrix.vecAppend_eq_ite, eqv] using this

lemma eqv_relExt {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v ↔ rel r w := by
  constructor
  · exact eqv_relExt_aux r h
  · exact eqv_relExt_aux r (fun i => eqv_symm (h i))

lemma eqv_equivalence : Equivalence (eqv L (M := M)) where
  refl := eqv_refl
  symm := eqv_symm
  trans := eqv_trans

variable (L M)

def eqvSetoid : Setoid M := Setoid.mk (eqv L) eqv_equivalence

def QuotEq := Quotient (eqvSetoid L M)

variable {L M}

instance QuotEq.inhabited : Nonempty (QuotEq L M) := Nonempty.map (⟦·⟧) inferInstance

lemma of_eq_of {a b : M} : (⟦a⟧ : QuotEq L M) = ⟦b⟧ ↔ eqv L a b := Quotient.eq (r := eqvSetoid L M)

namespace QuotEq

def func ⦃k⦄ (f : L.Func k) (v : Fin k → QuotEq L M) : QuotEq L M :=
  Quotient.liftVec (s := eqvSetoid L M) (⟦Structure.func f ·⟧) (fun _ _ hvw ↦ of_eq_of.mpr (eqv_funcExt f hvw)) v

def Rel ⦃k⦄ (r : L.Rel k) (v : Fin k → QuotEq L M) : Prop :=
  Quotient.liftVec (s := eqvSetoid L M) (Structure.rel r) (fun _ _ hvw ↦ eq_iff_iff.mpr <| eqv_relExt r hvw) v

instance struc : Structure L (QuotEq L M) where
  func := QuotEq.func
  rel := QuotEq.Rel

lemma funk_mk {k} (f : L.Func k) (v : Fin k → M) : Structure.func (M := QuotEq L M) f (⟦v ·⟧) = ⟦Structure.func f v⟧ :=
  Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _

lemma rel_mk {k} (r : L.Rel k) (v : Fin k → M) : Structure.rel (M := QuotEq L M) r (⟦v ·⟧) ↔ Structure.rel r v :=
  of_eq <| Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _

lemma funk_mk_of_eq {k} (f : L.Func k) {w : Fin k → QuotEq L M} {v : Fin k → M}
    (h : ∀ i, w i = ⟦v i⟧) : Structure.func (M := QuotEq L M) f w = ⟦Structure.func f v⟧ :=
  funext h ▸ funk_mk f v

lemma rel_mk_of_eq {k} (r : L.Rel k) {w : Fin k → QuotEq L M} {v : Fin k → M}
    (h : ∀ i, w i = ⟦v i⟧) : Structure.rel (M := QuotEq L M) r w ↔ Structure.rel r v :=
  funext h ▸ rel_mk r v

lemma val_mk {bv fv} (t : Semiterm L ξ n) :
    t.val (M := QuotEq L M) (⟦bv ·⟧) (⟦fv ·⟧) = ⟦t.val bv fv⟧ := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih => exact funk_mk_of_eq f ih

lemma eval_mk {bv fv} {φ : Semiformula L ξ n} :
    φ.Eval (M := QuotEq L M) (⟦bv ·⟧) (⟦fv ·⟧) ↔ φ.Eval bv fv := by
  induction φ using Semiformula.rec'
  case hall n φ ih =>
    constructor
    · intro h a; exact (ih (bv := a :> bv)).mp (by simp only [Matrix.comp_vecCons]; exact h ⟦a⟧)
    · intro h a;
      induction' a using Quotient.ind with a
      have h2 := ih.mpr (h a); simp only [Matrix.comp_vecCons] at h2; exact h2
  case hexs n φ ih =>
    constructor
    · intro ⟨a, h⟩
      induction' a using Quotient.ind with a
      exact ⟨a, (ih (bv := a :> bv)).mp (by simp only [Matrix.comp_vecCons]; exact h)⟩
    · intro ⟨a, h⟩; refine ⟨⟦a⟧, ?_⟩
      have h2 := ih.mpr h; simp only [Matrix.comp_vecCons] at h2; exact h2
  case _ => simp [*]
  case _ => simp [*]
  case hrel r v => exact rel_mk_of_eq r fun i ↦ val_mk (v i)
  case hnrel r v => exact not_congr (rel_mk_of_eq r fun i ↦ val_mk (v i))
  case _ => simp [*]
  case _ => simp [*]

lemma evalf_mk {fv} {φ : Formula L ξ} :
    φ.Evalf (M := QuotEq L M) (⟦fv ·⟧) ↔ φ.Evalf fv := by
  have h := eval_mk (bv := ![]) (fv := fv) (φ := φ)
  simp only [Matrix.empty_eq] at h; exact h

lemma models_iff {σ : Sentence L} : (QuotEq L M)↓[L] ⊧ σ ↔ M↓[L] ⊧ σ := by
  have h := eval_mk (M := M) (ξ := Empty) (φ := σ) (bv := ![]) (fv := Empty.elim)
  simp only [Empty.eq_elim, Matrix.empty_eq] at h; exact h

variable (L M)

lemma elementaryEquiv : QuotEq L M ≡ₑ[L] M := ⟨models_iff⟩

variable {L M}

set_option backward.isDefEq.respectTransparency false in
lemma rel_eq (a b : QuotEq L M) : op(=)[L].val (M := QuotEq L M) ![a, b] ↔ a = b := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  rw [of_eq_of]; simp [eqv, Semiformula.Operator.val];
  simpa [Matrix.fun_eq_vec_two, Empty.eq_elim] using
    eval_mk (H := H) (bv := ![a, b]) (fv := Empty.elim) (φ := Semiformula.Operator.Eq.eq.sentence)

instance structureEq : Structure.Eq L (QuotEq L M) := ⟨rel_eq⟩

end QuotEq

end Eq

end Structure

/-- Consequence can be tested on equality structures when all models satisfy the equality axioms.
This is a routine consequence of the quotient-model construction. -/
lemma consequence_iff_eq_of_models_eq {T : Theory L}
    (hEq : ∀ (M : Type v) [Nonempty M] [Structure L M], M↓[L] ⊧* T → M↓[L] ⊧* 𝗘𝗤 L)
    {σ : Sentence L} :
    T ⊨[Struc.{v, u} L] σ ↔
      (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M], M↓[L] ⊧* T → M↓[L] ⊧ σ) := by
  simp only [consequence_iff, Nonempty.forall];
  constructor;
  . intro h M x s _ hM; exact h M x hM;
  . intro h M x s hM;
    have : Nonempty M := ⟨x⟩;
    have H : M↓[L] ⊧* 𝗘𝗤 L := hEq M hM;
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M;
    exact e.models.mp $ h (Structure.Eq.QuotEq L M) ⟦x⟧ (e.modelsTheory.mpr hM);

/-- Satisfiability has an equality-structure witness when all models satisfy the equality axioms.
This is a routine consequence of the quotient-model construction. -/
lemma satisfiable_iff_eq_of_models_eq {T : Theory L}
    (hEq : ∀ (M : Type v) [Nonempty M] [Structure L M], M↓[L] ⊧* T → M↓[L] ⊧* 𝗘𝗤 L) :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔
      (∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M) (_ : Structure.Eq L M), M↓[L] ⊧* T) := by
  simp only [satisfiable_iff, Nonempty.exists, exists_prop];
  constructor;
  . intro ⟨M, x, s, hM⟩;
    have : Nonempty M := ⟨x⟩;
    have H : M↓[L] ⊧* 𝗘𝗤 L := hEq M hM;
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M;
    exact ⟨Structure.Eq.QuotEq L M, ⟦x⟧, inferInstance, inferInstance, e.modelsTheory.mpr hM⟩;
  . intro ⟨M, i, s, _, hM⟩; exact ⟨M, i, s, hM⟩;

namespace Semiformula

variable {M : Type*} [s : Structure L M] [Structure.Eq L M]

@[simp] lemma eval_existsUnique {e ε} {φ : Semiformula L ξ (n + 1)} :
    Eval (M := M) e ε (∃¹! φ) ↔ ∃! x, Eval (M := M) (x :> e) ε φ := by
  simp [existsUnique, Semiformula.eval_substs, Matrix.comp_vecCons'', ExistsUnique]
  simp [Function.comp_def]

end Semiformula

end FirstOrder

end FFL

end
