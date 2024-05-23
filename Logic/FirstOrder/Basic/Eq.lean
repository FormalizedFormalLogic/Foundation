import Logic.FirstOrder.Basic.Elab
import Logic.FirstOrder.Basic.Semantics.Elementary
import Logic.FirstOrder.Basic.Soundness

namespace LO

namespace FirstOrder

variable {L : Language} {μ : Type*} [Semiformula.Operator.Eq L]
namespace Semiterm

def varSumInL {k} : Fin k → Semiterm L μ (k + k) := fun i => #(Fin.castLE (by simp) i)

def varSumInR {k} : Fin k → Semiterm L μ (k + k) := fun i => #(Fin.natAdd k i)

@[simp] lemma substs_varSumInL (w₁ w₂ : Fin k → Semiterm L μ n) (i) :
  Rew.substs (Matrix.vecAppend rfl w₁ w₂) (varSumInL i) = w₁ i := by simp [varSumInL, Matrix.vecAppend_eq_ite]

@[simp] lemma substs_varSumInR (w₁ w₂ : Fin k → Semiterm L μ n) (i) :
  Rew.substs (Matrix.vecAppend rfl w₁ w₂) (varSumInR i) = w₂ i := by simp [varSumInR, Matrix.vecAppend_eq_ite]

@[simp] lemma emb_varSumInL {o} [IsEmpty o] (i : Fin k) :
  (Rew.emb (varSumInL (μ := o) i) : Semiterm L μ (k + k)) = varSumInL i := by simp [varSumInL]

@[simp] lemma emb_varSumInR {o} [IsEmpty o] (i : Fin k) :
  (Rew.emb (varSumInR (μ := o) i) : Semiterm L μ (k + k)) = varSumInR i := by simp [varSumInR]

end Semiterm

namespace Semiformula

def vecEq {k} (v w : Fin k → Semiterm L μ n) : Semiformula L μ n := Matrix.conj (fun i => “!!(v i) = !!(w i)”)

end Semiformula

namespace Theory
open Semiterm

class Sub (T U : Theory L) where
  sub : T ⊆ U

section Eq

inductive eqAxiom : Theory L
  | refl : eqAxiom “∀ #0 = #0”
  | symm : eqAxiom “∀ ∀ (#1 = #0 → #0 = #1)”
  | trans : eqAxiom “∀ ∀ ∀ (#2 = #1 → #1 = #0 → #2 = #0)”
  | funcExt {k} (f : L.Func k) :
    eqAxiom “∀* (!(Semiformula.vecEq varSumInL varSumInR) → !!(Semiterm.func f varSumInL) = !!(Semiterm.func f varSumInR))”
  | relExt {k} (r : L.Rel k) :
    eqAxiom “∀* (!(Semiformula.vecEq varSumInL varSumInR) → !(Semiformula.rel r varSumInL) → !(Semiformula.rel r varSumInR))”

notation "𝐄𝐐" => eqAxiom

end Eq

end Theory

abbrev Theory.addEqAxiom (T : Theory L) : Theory L := T + 𝐄𝐐

postfix:max "⁼" => Theory.addEqAxiom

abbrev ConsequenceWithEq (M : Type*) [Semantics (Sentence L) M] (T : Theory L) (σ : Sentence L) : Prop := T⁼ ⊨[M] σ

abbrev Consequence₀WithEq (T : Theory L) (σ : Sentence L) : Prop := T⁼ ⊨ σ

notation T:45 " ⊨₌[" M "] " σ:46 => ConsequenceWithEq M T σ

notation T:45 " ⊨₌ " σ:46 => Consequence₀WithEq T σ

abbrev ProofWithEq (T : Theory L) (σ : Sentence L) : Type _ := T⁼ ⊢ σ

abbrev ProvableWithEq (T : Theory L) (σ : Sentence L) : Prop := T⁼ ⊢! σ

infix:45 " ⊢₌ " => ProofWithEq

infix:45 " ⊢₌! " => ProvableWithEq

namespace Structure

namespace Eq

@[simp] lemma models_eqAxiom {M : Type u} [Nonempty M] [Structure L M] [Structure.Eq L M] : M ⊧ₘ* (𝐄𝐐 : Theory L) := ⟨by
  intro σ h
  cases h <;> simp [models_def, Semiformula.vecEq, Semiterm.val_func]
  · intro e h; congr; funext i; exact h i
  case relExt r =>
    simp [Semiformula.eval_rel]; intro e h; simp [congr_arg (rel r) (funext h)]⟩

variable (L)

instance models_eqAxiom' (M : Type u) [Nonempty M] [Structure L M] [Structure.Eq L M] : M ⊧ₘ* (𝐄𝐐 : Theory L) := Structure.Eq.models_eqAxiom

variable {M : Type u} [Nonempty M] [Structure L M]

def eqv (a b : M) : Prop := (@Semiformula.Operator.Eq.eq L _).val ![a, b]

variable {L}

variable (H : M ⊧ₘ* (𝐄𝐐 : Theory L))

open Semiterm Theory Semiformula

lemma eqv_refl (a : M) : eqv L a a := by
  have : M ⊧ₘ “∀ #0 = #0” := H.realize (Theory.eqAxiom.refl (L := L))
  simp [models_def] at this
  exact this a

lemma eqv_symm {a b : M} : eqv L a b → eqv L b a := by
  have : M ⊧ₘ “∀ ∀ (#1 = #0 → #0 = #1)” := H.realize (Theory.eqAxiom.symm (L := L))
  simp [models_def] at this
  exact this a b

lemma eqv_trans {a b c : M} : eqv L a b → eqv L b c → eqv L a c := by
  have : M ⊧ₘ “∀ ∀ ∀ (#2 = #1 → #1 = #0 → #2 = #0)” := H.realize (Theory.eqAxiom.trans (L := L))
  simp [models_def] at this
  exact this a b c

lemma eqv_funcExt {k} (f : L.Func k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    eqv L (func f v) (func f w) := by
  have : M ⊧ₘ “∀* (!(vecEq varSumInL varSumInR) → !!(Semiterm.func f varSumInL) = !!(Semiterm.func f varSumInR))” :=
    H.realize (eqAxiom.funcExt f (L := L))
  simp [varSumInL, varSumInR, models_def, vecEq, Semiterm.val_func] at this
  simpa [Matrix.vecAppend_eq_ite] using this (Matrix.vecAppend rfl v w) (fun i => by simpa [Matrix.vecAppend_eq_ite] using h i)

lemma eqv_relExt_aux {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v → rel r w := by
  have : M ⊧ₘ “∀* (!(vecEq varSumInL varSumInR) → !(Semiformula.rel r varSumInL) → !(Semiformula.rel r varSumInR))” :=
    H.realize (eqAxiom.relExt r (L := L))
  simp [varSumInL, varSumInR, models_def, vecEq, Semiterm.val_func, eval_rel (r := r)] at this
  simpa [eval_rel, Matrix.vecAppend_eq_ite] using this (Matrix.vecAppend rfl v w) (fun i => by simpa [Matrix.vecAppend_eq_ite] using h i)

lemma eqv_relExt {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v = rel r w := by
  simp; constructor
  · exact eqv_relExt_aux H r h
  · exact eqv_relExt_aux H r (fun i => eqv_symm H (h i))

lemma eqv_equivalence : Equivalence (eqv L (M := M)) where
  refl := eqv_refl H
  symm := eqv_symm H
  trans := eqv_trans H

def eqvSetoid (H : M ⊧ₘ* (𝐄𝐐 : Theory L)) : Setoid M := Setoid.mk (eqv L) (eqv_equivalence H)

def QuotEq := Quotient (eqvSetoid H)

instance QuotEq.inhabited : Nonempty (QuotEq H) := Nonempty.map (⟦·⟧) inferInstance

lemma of_eq_of {a b : M} : (⟦a⟧ : QuotEq H) = ⟦b⟧ ↔ eqv L a b := Quotient.eq (r := eqvSetoid H)

namespace QuotEq

def func ⦃k⦄ (f : L.Func k) (v : Fin k → QuotEq H) : QuotEq H :=
  Quotient.liftVec (s := eqvSetoid H) (⟦Structure.func f ·⟧) (fun _ _ hvw => (of_eq_of H).mpr (eqv_funcExt H f hvw)) v

def rel ⦃k⦄ (r : L.Rel k) (v : Fin k → QuotEq H) : Prop :=
  Quotient.liftVec (s := eqvSetoid H) (Structure.rel r) (fun _ _ hvw => eqv_relExt H r hvw) v

variable {H}

instance struc : Structure L (QuotEq H) where
  func := QuotEq.func H
  rel := QuotEq.rel H

lemma funk_mk {k} (f : L.Func k) (v : Fin k → M) : Structure.func (M := QuotEq H) f (fun i => ⟦v i⟧) = ⟦Structure.func f v⟧ :=
  Quotient.liftVec_mk (s := eqvSetoid H) _ _ _

lemma rel_mk {k} (r : L.Rel k) (v : Fin k → M) : Structure.rel (M := QuotEq H) r (fun i => ⟦v i⟧) ↔ Structure.rel r v :=
  of_eq <| Quotient.liftVec_mk (s := eqvSetoid H) _ _ _

lemma val_mk {e} {ε} (t : Semiterm L μ n) : Semiterm.valm (QuotEq H) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) t = ⟦Semiterm.valm M e ε t⟧ :=
  by induction t <;> simp [*, funk_mk, Semiterm.val_func]

lemma eval_mk {e} {ε} {p : Semiformula L μ n} :
    Semiformula.Evalm (QuotEq H) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) p ↔ Semiformula.Evalm M e ε p := by
  induction p using Semiformula.rec' <;> simp [*, Semiformula.eval_rel, Semiformula.eval_nrel, val_mk, rel_mk]
  case hall n p ih =>
    constructor
    · intro h a; exact (ih (e := a :> e)).mp (by simpa [Matrix.comp_vecCons] using h ⟦a⟧)
    · intro h a;
      induction' a using Quotient.ind with a
      simpa [Matrix.comp_vecCons] using ih.mpr (h a)
  case hex n p ih =>
    constructor
    · intro ⟨a, h⟩
      induction' a using Quotient.ind with a
      exact ⟨a, (ih (e := a :> e)).mp (by simpa [Matrix.comp_vecCons] using h)⟩
    · intro ⟨a, h⟩; exact ⟨⟦a⟧, by simpa [Matrix.comp_vecCons] using ih.mpr h⟩

lemma models_iff {σ : Sentence L} : (QuotEq H) ⊧ₘ σ ↔ M ⊧ₘ σ := by
  simpa [models_def, Semiformula.Evalf, eq_finZeroElim, Empty.eq_elim] using
    eval_mk (H := H) (e := finZeroElim) (ε := Empty.elim) (p := σ)

variable (H)

lemma elementaryEquiv : QuotEq H ≡ₑ[L] M := fun _ => models_iff

variable {H}

lemma rel_eq (a b : QuotEq H) : (@Semiformula.Operator.Eq.eq L _).val (M := QuotEq H) ![a, b] ↔ a = b := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  rw[of_eq_of]; simp [eqv, Semiformula.Operator.val];
  simpa [Evalm, Matrix.fun_eq_vec₂, Empty.eq_elim] using
    eval_mk (H := H) (e := ![a, b]) (ε := Empty.elim) (p := Semiformula.Operator.Eq.eq.sentence)

instance structureEq : Structure.Eq L (QuotEq H) := ⟨rel_eq⟩

end QuotEq

end Eq

end Structure

lemma consequence_iff_eq {T : Theory L} [𝐄𝐐 ≼ T] {σ : Sentence L} :
    T ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M], M ⊧ₘ* T → M ⊧ₘ σ) := by
  simp [consequence_iff]; constructor
  · intro h M x s _ hM; exact h M x hM
  · intro h M x s hM
    haveI : Nonempty M := ⟨x⟩
    have H : M ⊧ₘ* (𝐄𝐐 : Theory L) := models_of_subtheory hM
    have e : Structure.Eq.QuotEq H ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv H
    exact e.models.mp $ h (Structure.Eq.QuotEq H) ⟦x⟧ (e.modelsTheory.mpr hM)

lemma consequence_iff_eq' {T : Theory L} [𝐄𝐐 ≼ T] {σ : Sentence L} :
    T ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M] [M ⊧ₘ* T], M ⊧ₘ σ) := by
  rw [consequence_iff_eq]

lemma consequence_iff_add_eq {T : Theory L} {σ : Sentence L} :
    T ⊨₌[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M], M ⊧ₘ* T → M ⊧ₘ σ) :=
  Iff.trans consequence_iff_eq (forall₄_congr <| fun M _ _ _ ↦ by simp)

lemma satisfiable_iff_eq {T : Theory L} [𝐄𝐐 ≼ T] :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔ (∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M) (_ : Structure.Eq L M), M ⊧ₘ* T) := by
  simp [satisfiable_iff]; constructor
  · intro ⟨M, x, s, hM⟩;
    haveI : Nonempty M := ⟨x⟩
    have H : M ⊧ₘ* (𝐄𝐐 : Theory L) := models_of_subtheory hM
    have e : Structure.Eq.QuotEq H ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv H
    exact ⟨Structure.Eq.QuotEq H, ⟦x⟧, inferInstance, inferInstance, e.modelsTheory.mpr hM⟩
  · intro ⟨M, i, s, _, hM⟩; exact ⟨M, i, s, hM⟩

def ModelOfSatEq {T : Theory L} [𝐄𝐐 ≼ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T) : Type _ :=
  have H : ModelOfSat sat ⊧ₘ* (𝐄𝐐 : Theory L) := models_of_subtheory (ModelOfSat.models sat)
  Structure.Eq.QuotEq H

namespace ModelOfSatEq

variable {T : Theory L} [𝐄𝐐 ≼ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T)

noncomputable instance : Nonempty (ModelOfSatEq sat) := Structure.Eq.QuotEq.inhabited _

noncomputable instance struc : Structure L (ModelOfSatEq sat) := Structure.Eq.QuotEq.struc

noncomputable instance : Structure.Eq L (ModelOfSatEq sat) := Structure.Eq.QuotEq.structureEq

lemma models : ModelOfSatEq sat ⊧ₘ* T :=
  have e : ModelOfSatEq sat ≡ₑ[L] ModelOfSat sat :=
    Structure.Eq.QuotEq.elementaryEquiv (models_of_subtheory (ModelOfSat.models sat))
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
  ⟨fun x y => (@Operator.Mem.mem L _).val ![x, y]⟩

instance [Operator.Mem L] : Structure.Mem L (ModelOfSatEq sat) := ⟨fun _ _ => iff_of_eq rfl⟩

end ModelOfSatEq

namespace Semiformula

def existsUnique (p : Semiformula L μ (n + 1)) : Semiformula L μ n :=
  ∃' (p ⋏ (∀' ((Rew.substs (#0 :> (#·.succ.succ))).hom p ⟶ “#0 = #1”)))

prefix:64 "∃'! " => existsUnique

variable {M : Type*} [s : Structure L M] [Structure.Eq L M]

@[simp] lemma eval_existsUnique {e ε} {p : Semiformula L μ (n + 1)} :
    Eval s e ε (∃'! p) ↔ ∃! x, Eval s (x :> e) ε p := by
  simp [existsUnique, Semiformula.eval_substs, Matrix.comp_vecCons', ExistsUnique]

end Semiformula

end FirstOrder

end LO
