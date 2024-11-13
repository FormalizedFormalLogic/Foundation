import Foundation.FirstOrder.Basic.BinderNotation
import Foundation.FirstOrder.Basic.Semantics.Elementary
import Foundation.FirstOrder.Basic.Soundness

namespace Matrix

variable {α : Type*}

def iget [Inhabited α] (v : Fin k → α) (x : ℕ) : α := if h : x < k then v ⟨x, h⟩ else default

end Matrix

namespace LO

namespace FirstOrder

variable {L : Language} {μ : Type*} [Semiformula.Operator.Eq L]

namespace Theory

class Sub (T U : Theory L) where
  sub : T ⊆ U

section Eq

inductive eqAxiom : Theory L
  | refl : eqAxiom “x | x = x”
  | symm : eqAxiom “x y | x = y → y = x”
  | trans : eqAxiom “x y z | x = y → y = z → x = z”
  | funcExt {k} (f : L.Func k) :
    eqAxiom ((Matrix.conj fun i : Fin k ↦ “&i = &(k + i)”) ➝ op(=).operator ![Semiterm.func f (fun i ↦ &i), Semiterm.func f (fun i ↦ &(k + i))])
  | relExt {k} (r : L.Rel k) :
    eqAxiom ((Matrix.conj fun i : Fin k ↦ “&i = &(k + i)”) ➝ Semiformula.rel r (fun i ↦ &i) ➝ Semiformula.rel r (fun i ↦ &(k + i)))

notation "𝐄𝐐" => eqAxiom

end Eq

end Theory

namespace Structure

namespace Eq

@[simp] lemma models_eqAxiom {M : Type u} [Nonempty M] [Structure L M] [Structure.Eq L M] : M ⊧ₘ* (𝐄𝐐 : Theory L) := ⟨by
  intro σ h
  cases h <;> simp [models_def, Semiterm.val_func, Semiformula.eval_rel]
  case symm => intros; simp_all
  case trans => intros; simp_all
  case funcExt f => intro m e; simp [e]
  case relExt r => intro m e; simp [e]⟩

variable (L)

instance models_eqAxiom' (M : Type u) [Nonempty M] [Structure L M] [Structure.Eq L M] : M ⊧ₘ* (𝐄𝐐 : Theory L) := Structure.Eq.models_eqAxiom

variable {M : Type u} [Nonempty M] [Structure L M]

def eqv (a b : M) : Prop := (@Semiformula.Operator.Eq.eq L _).val ![a, b]

variable {L}

variable [H : M ⊧ₘ* (𝐄𝐐 : Theory L)]

open Semiterm Theory Semiformula

lemma eqv_refl (a : M) : eqv L a a := by
  have : M ⊧ₘ “x | x = x” := H.realize _ (Theory.eqAxiom.refl (L := L))
  simpa [models_def] using this (fun _ ↦ a)

lemma eqv_symm {a b : M} : eqv L a b → eqv L b a := by
  have : M ⊧ₘ “x y | x = y → y = x” := H.realize _ (Theory.eqAxiom.symm (L := L))
  simpa [models_def] using this (a :>ₙ fun _ ↦ b)

lemma eqv_trans {a b c : M} : eqv L a b → eqv L b c → eqv L a c := by
  have : M ⊧ₘ “x y z | x = y → y = z → x = z” := H.realize _ (Theory.eqAxiom.trans (L := L))
  simpa [models_def] using  this (a :>ₙ b :>ₙ fun _ ↦ c)

lemma eqv_funcExt {k} (f : L.Func k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    eqv L (func f v) (func f w) := by
  haveI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  have := H.realize _ (eqAxiom.funcExt f (L := L)) (fun x ↦ Matrix.iget (Matrix.vecAppend rfl v w) x)
  have : (∀ i, op(=).val ![v i, w i]) → op(=).val ![func f v, func f w] := by {
    simpa [models_def, Matrix.vecAppend_eq_ite, Semiterm.val_func, Matrix.iget,
      show ∀ i : Fin k, i < k + k from fun i ↦ lt_of_lt_of_le i.prop (by simp)] using
      H.realize _ (eqAxiom.funcExt f (L := L)) (fun x ↦ Matrix.iget (Matrix.vecAppend rfl v w) x) }
  exact this h

lemma eqv_relExt_aux {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v → rel r w := by
  haveI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  have : (∀ i, op(=).val ![v i, w i]) → rel r v → rel r w := by {
    simpa [models_def, Matrix.vecAppend_eq_ite, Semiterm.val_func, eval_rel (r := r), Matrix.iget,
      show ∀ i : Fin k, i < k + k from fun i ↦ lt_of_lt_of_le i.prop (by simp)] using
      H.realize _ (eqAxiom.relExt r (L := L)) (fun x ↦ Matrix.iget (Matrix.vecAppend rfl v w) x) }
  exact this h

lemma eqv_relExt {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v = rel r w := by
  simp; constructor
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
  Quotient.liftVec (s := eqvSetoid L M) (⟦Structure.func f ·⟧) (fun _ _ hvw => of_eq_of.mpr (eqv_funcExt f hvw)) v

def rel ⦃k⦄ (r : L.Rel k) (v : Fin k → QuotEq L M) : Prop :=
  Quotient.liftVec (s := eqvSetoid L M) (Structure.rel r) (fun _ _ hvw => eqv_relExt r hvw) v

instance struc : Structure L (QuotEq L M) where
  func := QuotEq.func
  rel := QuotEq.rel

lemma funk_mk {k} (f : L.Func k) (v : Fin k → M) : Structure.func (M := QuotEq L M) f (fun i => ⟦v i⟧) = ⟦Structure.func f v⟧ :=
  Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _

lemma rel_mk {k} (r : L.Rel k) (v : Fin k → M) : Structure.rel (M := QuotEq L M) r (fun i => ⟦v i⟧) ↔ Structure.rel r v :=
  of_eq <| Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _

lemma val_mk {e} {ε} (t : Semiterm L μ n) : Semiterm.valm (QuotEq L M) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) t = ⟦Semiterm.valm M e ε t⟧ :=
  by induction t <;> simp [*, funk_mk, Semiterm.val_func]

lemma eval_mk {e} {ε} {φ : Semiformula L μ n} :
    Semiformula.Evalm (QuotEq L M) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) φ ↔ Semiformula.Evalm M e ε φ := by
  induction φ using Semiformula.rec' <;> simp [*, Semiformula.eval_rel, Semiformula.eval_nrel, val_mk, rel_mk]
  case hall n φ ih =>
    constructor
    · intro h a; exact (ih (e := a :> e)).mp (by simpa [Matrix.comp_vecCons] using h ⟦a⟧)
    · intro h a;
      induction' a using Quotient.ind with a
      simpa [Matrix.comp_vecCons] using ih.mpr (h a)
  case hex n φ ih =>
    constructor
    · intro ⟨a, h⟩
      induction' a using Quotient.ind with a
      exact ⟨a, (ih (e := a :> e)).mp (by simpa [Matrix.comp_vecCons] using h)⟩
    · intro ⟨a, h⟩; exact ⟨⟦a⟧, by simpa [Matrix.comp_vecCons] using ih.mpr h⟩

lemma eval_mk₀ {ε} {φ : Formula L ξ} :
    Semiformula.Evalfm (QuotEq L M) (fun i => ⟦ε i⟧) φ ↔ Semiformula.Evalfm (L := L) M ε φ := by
  simpa [Matrix.empty_eq] using eval_mk (H := H) (e := ![]) (ε := ε) (φ := φ)

lemma models_iff {φ : SyntacticFormula L} : QuotEq L M ⊧ₘ φ ↔ M ⊧ₘ φ := by
  constructor
  · intro h f; exact eval_mk₀.mp (h (fun x ↦ ⟦f x⟧))
  · intro h f
    induction' f using Quotient.induction_on_pi with f
    exact eval_mk₀.mpr (h f)

variable (L M)

lemma elementaryEquiv : QuotEq L M ≡ₑ[L] M := fun _ => models_iff

variable {L M}

lemma rel_eq (a b : QuotEq L M) : (@Semiformula.Operator.Eq.eq L _).val (M := QuotEq L M) ![a, b] ↔ a = b := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  rw[of_eq_of]; simp [eqv, Semiformula.Operator.val];
  simpa [Evalm, Matrix.fun_eq_vec₂, Empty.eq_elim] using
    eval_mk (H := H) (e := ![a, b]) (ε := Empty.elim) (φ := Semiformula.Operator.Eq.eq.sentence)

instance structureEq : Structure.Eq L (QuotEq L M) := ⟨rel_eq⟩

end QuotEq

end Eq

end Structure

lemma consequence_iff_eq {T : Theory L} [𝐄𝐐 ≼ T] {φ : SyntacticFormula L} :
    T ⊨[Struc.{v, u} L] φ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M], M ⊧ₘ* T → M ⊧ₘ φ) := by
  simp [consequence_iff]; constructor
  · intro h M x s _ hM; exact h M x hM
  · intro h M x s hM
    haveI : Nonempty M := ⟨x⟩
    have H : M ⊧ₘ* (𝐄𝐐 : Theory L) := models_of_subtheory hM
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M
    exact e.models.mp $ h (Structure.Eq.QuotEq L M) ⟦x⟧ (e.modelsTheory.mpr hM)

lemma consequence_iff_eq' {T : Theory L} [𝐄𝐐 ≼ T] {φ : SyntacticFormula L} :
    T ⊨[Struc.{v, u} L] φ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M] [M ⊧ₘ* T], M ⊧ₘ φ) := by
  rw [consequence_iff_eq]

lemma satisfiable_iff_eq {T : Theory L} [𝐄𝐐 ≼ T] :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔ (∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M) (_ : Structure.Eq L M), M ⊧ₘ* T) := by
  simp [satisfiable_iff]; constructor
  · intro ⟨M, x, s, hM⟩;
    haveI : Nonempty M := ⟨x⟩
    have H : M ⊧ₘ* (𝐄𝐐 : Theory L) := models_of_subtheory hM
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M
    exact ⟨Structure.Eq.QuotEq L M, ⟦x⟧, inferInstance, inferInstance, e.modelsTheory.mpr hM⟩
  · intro ⟨M, i, s, _, hM⟩; exact ⟨M, i, s, hM⟩

instance {T : Theory L} [𝐄𝐐 ≼ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T) :
    ModelOfSat sat ⊧ₘ* (𝐄𝐐 : Theory L) := models_of_subtheory (ModelOfSat.models sat)

def ModelOfSatEq {T : Theory L} [𝐄𝐐 ≼ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T) : Type _ :=
  Structure.Eq.QuotEq L (ModelOfSat sat)

namespace ModelOfSatEq

variable {T : Theory L} [𝐄𝐐 ≼ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T)

noncomputable instance : Nonempty (ModelOfSatEq sat) := Structure.Eq.QuotEq.inhabited

noncomputable instance struc : Structure L (ModelOfSatEq sat) := Structure.Eq.QuotEq.struc

noncomputable instance : Structure.Eq L (ModelOfSatEq sat) := Structure.Eq.QuotEq.structureEq

lemma models : ModelOfSatEq sat ⊧ₘ* T :=
  have e : ModelOfSatEq sat ≡ₑ[L] ModelOfSat sat := Structure.Eq.QuotEq.elementaryEquiv L (ModelOfSat sat)
  e.modelsTheory.mpr (ModelOfSat.models _)

instance mod : ModelOfSatEq sat ⊧ₘ* T := models sat

open Semiterm Semiformula

noncomputable instance [Operator.Zero L] : Zero (ModelOfSatEq sat) := ⟨(@Operator.Zero.zero L _).val ![]⟩

instance strucZero [Operator.Zero L] : Structure.Zero L (ModelOfSatEq sat) := ⟨rfl⟩

noncomputable instance [Operator.One L] : One (ModelOfSatEq sat) := ⟨(@Operator.One.one L _).val ![]⟩

instance [Operator.One L] : Structure.One L (ModelOfSatEq sat) := ⟨rfl⟩

noncomputable instance [Operator.Add L] : Add (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Add.add L _).val ![x, y]⟩

instance [Operator.Add L] : Structure.Add L (ModelOfSatEq sat) := ⟨fun _ _ => rfl⟩

noncomputable instance [Operator.Mul L] : Mul (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Mul.mul L _).val ![x, y]⟩

instance [Operator.Mul L] : Structure.Mul L (ModelOfSatEq sat) := ⟨fun _ _ => rfl⟩

instance [Operator.LT L] : LT (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.LT.lt L _).val ![x, y]⟩

instance [Operator.LT L] : Structure.LT L (ModelOfSatEq sat) := ⟨fun _ _ => iff_of_eq rfl⟩

instance [Operator.Mem L] : Membership (ModelOfSatEq sat) (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Mem.mem L _).val ![y, x]⟩

instance [Operator.Mem L] : Structure.Mem L (ModelOfSatEq sat) := ⟨fun _ _ => iff_of_eq rfl⟩

end ModelOfSatEq

namespace Semiformula

def existsUnique {ξ} (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  “∃ y, !φ y ⋯ ∧ ∀ z, !φ z ⋯ → z = y”

prefix:64 "∃'! " => existsUnique

variable {M : Type*} [s : Structure L M] [Structure.Eq L M]

@[simp] lemma eval_existsUnique {e ε} {φ : Semiformula L ξ (n + 1)} :
    Eval s e ε (∃'! φ) ↔ ∃! x, Eval s (x :> e) ε φ := by
  simp [existsUnique, Semiformula.eval_substs, Matrix.comp_vecCons', ExistsUnique]

end Semiformula

namespace BinderNotation

open Lean PrettyPrinter Delaborator SubExpr

syntax:max "∃! " first_order_formula:0 : first_order_formula
syntax:max "∃! " ident ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula[ $binders* | $fbinders* | ∃! $φ:first_order_formula ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertAt 0 v
    `(∃'! ⤫formula[ $binders'* | $fbinders* | $φ])
  | `(⤫formula[ $binders* | $fbinders* | ∃! $x, $φ ])                 => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(∃'! ⤫formula[ $binders'* | $fbinders* | $φ ])

end BinderNotation

end FirstOrder

end LO
