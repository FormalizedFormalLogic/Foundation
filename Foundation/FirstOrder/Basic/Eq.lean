module
public import Foundation.FirstOrder.Basic.BinderNotation
public import Foundation.FirstOrder.Basic.Semantics.Elementary
public import Foundation.FirstOrder.Basic.Soundness
public import Foundation.Vorspiel.Quotient
public import Foundation.Vorspiel.Finset.Card

@[expose] public section

namespace Matrix

variable {α : Type*}

def iget [Inhabited α] (v : Fin k → α) (x : ℕ) : α := if h : x < k then v ⟨x, h⟩ else default

end Matrix

namespace LO

namespace FirstOrder

variable {L : Language} {ξ  : Type*} [Semiformula.Operator.Eq L]

namespace Eq

protected abbrev refl (t : Term L ℕ) : Proposition L := op(=).operator ![t, t]

protected abbrev symm (t u : Term L ℕ) : Proposition L := op(=).operator ![t, u] ➝ op(=).operator ![u, t]

protected abbrev trans (t u v : Term L ℕ) : Proposition L := op(=).operator ![t, u] ➝ op(=).operator ![u, v] ➝ op(=).operator ![t, v]

def funcExt {k} (f : L.Func k) (v w : Fin k → Term L ℕ) : Proposition L :=
  (Matrix.conj fun i ↦ op(=).operator ![v i, w i]) ➝ op(=).operator ![Semiterm.func f v, Semiterm.func f w]

@[simp] lemma rew_funcExt (ω : Rew L ℕ 0 ℕ 0) {k} (f : L.Func k) (v w : Fin k → Term L ℕ) :
    ω ▹ funcExt f v w = funcExt f (ω ∘ v) (ω ∘ w) := by
  simp [funcExt, Function.comp_def]

def relExt {k} (r : L.Rel k) (v w : Fin k → Term L ℕ) : Proposition L :=
  (Matrix.conj fun i ↦ op(=).operator ![v i, w i]) 🡒 Semiformula.rel r v 🡒 Semiformula.rel r w

@[simp] lemma rew_relExt (ω : Rew L ℕ 0 ℕ 0) {k} (r : L.Rel k) (v w : Fin k → Term L ℕ) :
    ω ▹ relExt r v w = relExt r (ω ∘ v) (ω ∘ w) := by
  simp [relExt, Function.comp_def]

inductive EqSchema : Proposition L → Prop
  | refl (t : Term L ℕ) : EqSchema (Eq.refl t)
  | symm (t u : Term L ℕ) : EqSchema (Eq.symm t u)
  | trans (t u v : Term L ℕ) : EqSchema (Eq.trans t u v)
  | funcExt {k} (f : L.Func k) (v w : Fin k → Term L ℕ) : EqSchema (funcExt f v w)
  | relExt {k} (r : L.Rel k) (v w : Fin k → Term L ℕ) : EqSchema (relExt r v w)

attribute [simp] EqSchema.refl EqSchema.symm EqSchema.trans EqSchema.funcExt EqSchema.relExt

variable (L)

abbrev eqSchema : Schema L := {φ | EqSchema φ}

notation "𝗘𝗤" => eqSchema

instance : Schema.IsClosed (𝗘𝗤 L) := ⟨by rintro ω _ (_ | _ | _ | _ | _) <;> simp [eqSchema]⟩

end Eq

namespace Structure

namespace Eq

variable (L) (M : Type*) [Nonempty M] [Structure L M]

@[simp] instance models_eqSchema [Structure.Eq L M] :
    M↓[L] ⊧* ↑↑(𝗘𝗤 L) := ⟨by
  intro σ h
  have : ∃ φ, Eq.EqSchema φ ∧ Semiformula.univCl φ = σ := by simpa using h
  rcases this with ⟨φ, (_ | _ | _ | _ | _), rfl⟩ <;> simp [models_iff, Eq.funcExt, Eq.relExt]
  · simp at h; grind
  · grind
  · simp [Function.comp_def]; grind
  · simp [Function.comp_def]; grind⟩

variable {M}

def eqv (a b : M) : Prop := (@Semiformula.Operator.Eq.eq L _).val ![a, b]

variable {L}

variable [H : M↓[L] ⊧* 𝗘𝗤 L]

open Semiterm Theory Semiformula

lemma eqv_refl (a : M) : eqv L a a := by
  have : ∀ f : ℕ → M, op(=)[L].val ![f 0, f 0] := by
    simpa [models_iff] using modelsUnivCl_of_mem_schema (M := M) (𝔖 := 𝗘𝗤 L) (Eq.EqSchema.refl &0)
  simpa using this fun _ ↦ a

lemma eqv_symm {a b : M} : eqv L a b → eqv L b a := by
  have : ∀ f : ℕ → M, op(=)[L].val ![f 0, f 1] → op(=)[L].val ![f 1, f 0] := by
    simpa [models_iff] using modelsUnivCl_of_mem_schema (M := M) (𝔖 := 𝗘𝗤 L) (Eq.EqSchema.symm &0 &1)
  simpa using this (a :>ₙ fun _ ↦ b)

lemma eqv_trans {a b c : M} : eqv L a b → eqv L b c → eqv L a c := by
  have : ∀ f : ℕ → M, op(=)[L].val ![f 0, f 1] → op(=)[L].val ![f 1, f 2] → op(=)[L].val ![f 0, f 2] := by
    simpa [models_iff] using modelsUnivCl_of_mem_schema (M := M) (𝔖 := 𝗘𝗤 L) (Eq.EqSchema.trans &0 &1 &2)
  simpa using this (a :>ₙ b :>ₙ fun _ ↦ c)

lemma eqv_funcExt {k} (F : L.Func k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    eqv L (func F v) (func F w) := by
  have : ∀ f : ℕ → M,
  (∀ i : Fin k, op(=)[L].val ![f i, f (k + i)]) →
    op(=)[L].val ![func F fun x ↦ f x, func F fun x ↦ f (k + x)] := by
      have := by simpa [models_iff, Eq.funcExt,] using
        modelsUnivCl_of_mem_schema (M := M) (𝔖 := 𝗘𝗤 L) (Eq.EqSchema.funcExt F (fun i ↦ &i) (fun j ↦ &(k + j)))
      simpa [Function.comp_def] using this
  have : (∀ i : Fin k, op(=)[L].val ![v i, w i]) →
      op(=)[L].val ![func F fun x ↦ v x, func F fun x ↦ w x] := by
    simpa using this <| fun x ↦ if h : x < k then v ⟨x, h⟩ else if h : x < k + k then w ⟨x - k, by grind⟩ else Classical.ofNonempty
  exact this h

lemma eqv_relExt_aux {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v → rel r w := by
  have : ∀ f : ℕ → M,
  (∀ i : Fin k, op(=)[L].val ![f i, f (k + i)]) →
    (rel r fun x ↦ f x) → rel r fun x ↦ f (k + x) := by
      have := by simpa [models_iff, Eq.relExt] using
        modelsUnivCl_of_mem_schema (M := M) (𝔖 := 𝗘𝗤 L) (Eq.EqSchema.relExt r (fun i ↦ &i) (fun j ↦ &(k + j)))
      simpa [Function.comp_def] using this
  have : (∀ i : Fin k, op(=)[L].val ![v i, w i]) →
      (rel r fun x ↦ v x) → rel r fun x ↦ w x := by
    simpa using this <| fun x ↦ if h : x < k then v ⟨x, h⟩ else if h : x < k + k then w ⟨x - k, by grind⟩ else Classical.ofNonempty
  exact this h

lemma eqv_relExt {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v ↔ rel r w := by
  constructor
  · exact eqv_relExt_aux r h
  · exact eqv_relExt_aux r fun i ↦ eqv_symm (h i)

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

def Rel ⦃k⦄ (r : L.Rel k) (v : Fin k → QuotEq L M) : Prop :=
  Quotient.liftVec (s := eqvSetoid L M) (Structure.rel r) (fun _ _ hvw =>eq_iff_iff.mpr <| eqv_relExt r hvw) v

instance struc : Structure L (QuotEq L M) where
  func := QuotEq.func
  rel := QuotEq.Rel

lemma funk_mk {k} (f : L.Func k) (v : Fin k → M) : Structure.func (M := QuotEq L M) f (Quotient.mk _ ∘ v) = ⟦Structure.func f v⟧ :=
  Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _

lemma rel_mk {k} (r : L.Rel k) (v : Fin k → M) : Structure.rel (M := QuotEq L M) r (Quotient.mk _ ∘ v) ↔ Structure.rel r v :=
  of_eq <| Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _

lemma val_mk (e : Fin n → M) (ε : ξ → M) (t : Semiterm L ξ n) :
    t.val (M := QuotEq L M) (Quotient.mk _ ∘ e) (Quotient.mk _ ∘ ε) = ⟦t.val e ε⟧ := by
  match t with
  | #x | &x => simp
  | .func F v =>
    simp [←funk_mk, Function.comp_def (g := v), fun i ↦ val_mk e ε (v i)]; rfl

lemma eval_mk {e} {ε} {φ : Semiformula L ξ n} :
    φ.Eval (M := QuotEq L M) (Quotient.mk _ ∘ e) (Quotient.mk _ ∘ ε) ↔ φ.Eval e ε := by
  match φ with
  | .rel R v | .nrel R v => simp [←val_mk, ←rel_mk, Function.comp_def]
  | ⊤ | ⊥ => simp
  | φ ⋏ ψ | φ ⋎ ψ => simp [←eval_mk (φ := φ), ←eval_mk (φ := ψ)]
  | ∀⁰ φ => simpa [←eval_mk (φ := φ), Matrix.comp_vecCons'', ] using Quotient.forall
  | ∃⁰ φ => simpa [←eval_mk (φ := φ), Matrix.comp_vecCons'', ] using Quotient.exists

lemma models_iff {σ : Sentence L} : (QuotEq L M)↓[L] ⊧ σ ↔ M↓[L] ⊧ σ := by
  simpa [Empty.eq_elim] using eval_mk (M := M) (e := ![]) (ε := Empty.elim) (φ := σ)

variable (L M)

lemma elementaryEquiv : QuotEq L M ≡ₑ[L] M := ⟨models_iff⟩

variable {L M}

set_option backward.isDefEq.respectTransparency false in
lemma rel_eq (a b : QuotEq L M) : op(=)[L].val ![a, b] ↔ a = b := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  rw [of_eq_of]
  simpa [eqv, Semiformula.Operator.val, Empty.eq_elim] using
    eval_mk (H := H) (e := ![a, b]) (ε := Empty.elim) (φ := Semiformula.Operator.Eq.eq.sentence)

instance structureEq : Structure.Eq L (QuotEq L M) := ⟨rel_eq⟩

end QuotEq

end Eq

end Structure

lemma consequence_iff_eq {𝔖 : Schema L} [𝗘𝗤 L ⪯ 𝔖] {σ : Sentence L} :
    𝔖 ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M], M↓[L] ⊧* 𝔖 → M↓[L] ⊧ σ) := by
  simp only [consequence_iff, Nonempty.forall]
  constructor
  · intro h M x s _ hM; exact h M x hM
  · intro h M x s hM
    have : Nonempty M := ⟨x⟩
    have H : M↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory hM
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M
    exact e.models.mp <| h (Structure.Eq.QuotEq L M) ⟦x⟧ (e.modelsTheory.mpr hM)

lemma consequence_iff_eq' {𝔖 : Schema L} [𝗘𝗤 L ⪯ 𝔖] {σ : Sentence L} :
    𝔖 ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M] [M↓[L] ⊧* 𝔖], M↓[L] ⊧ σ) := by
  rw [consequence_iff_eq]

lemma satisfiable_iff_eq {𝔖 : Schema L} [𝗘𝗤 L ⪯ 𝔖] :
    Semantics.Satisfiable (Struc.{v, u} L) 𝔖 ↔ (∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M) (_ : Structure.Eq L M), M↓[L] ⊧* 𝔖) := by
  simp only [satisfiable_iff, Nonempty.exists, exists_prop]
  constructor
  · intro ⟨M, x, s, hM⟩;
    have : Nonempty M := ⟨x⟩
    have H : M↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory hM
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M
    exact ⟨Structure.Eq.QuotEq L M, ⟦x⟧, inferInstance, inferInstance, e.modelsTheory.mpr hM⟩
  · intro ⟨M, i, s, _, hM⟩; exact ⟨M, i, s, hM⟩

instance {𝔖 : Schema L} [𝗘𝗤 L ⪯ 𝔖] (sat : Semantics.Satisfiable (Struc.{v, u} L) 𝔖) :
    (ModelOfSat sat)↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory (ModelOfSat.models sat)

def ModelOfSatEq {𝔖 : Schema L} [𝗘𝗤 L ⪯ 𝔖] (sat : Semantics.Satisfiable (Struc.{v, u} L) 𝔖) : Type _ :=
  Structure.Eq.QuotEq L (ModelOfSat sat)

namespace ModelOfSatEq

variable {𝔖 : Schema L} [𝗘𝗤 L ⪯ 𝔖] (sat : Semantics.Satisfiable (Struc.{v, u} L) 𝔖)

noncomputable instance : Nonempty (ModelOfSatEq sat) := Structure.Eq.QuotEq.inhabited

noncomputable instance struc : Structure L (ModelOfSatEq sat) := Structure.Eq.QuotEq.struc

noncomputable instance : Structure.Eq L (ModelOfSatEq sat) := Structure.Eq.QuotEq.structureEq

lemma models : (ModelOfSatEq sat)↓[L] ⊧* 𝔖 :=
  have e : ModelOfSatEq sat ≡ₑ[L] ModelOfSat sat := Structure.Eq.QuotEq.elementaryEquiv L (ModelOfSat sat)
  e.modelsTheory.mpr (ModelOfSat.models _)

instance mod : (ModelOfSatEq sat)↓[L] ⊧* 𝔖 := models sat

open Semiterm Semiformula

noncomputable instance [Operator.Zero L] : Zero (ModelOfSatEq sat) := ⟨(@Operator.Zero.zero L _).val ![]⟩

instance strucZero [Operator.Zero L] : Structure.Zero L (ModelOfSatEq sat) := ⟨rfl⟩

noncomputable instance [Operator.One L] : One (ModelOfSatEq sat) := ⟨(@Operator.One.one L _).val ![]⟩

instance [Operator.One L] : Structure.One L (ModelOfSatEq sat) := ⟨rfl⟩

noncomputable instance [Operator.Add L] : Add (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Add.add L _).val ![x, y]⟩

instance [Operator.Add L] : Structure.Add L (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩

noncomputable instance [Operator.Mul L] : Mul (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Mul.mul L _).val ![x, y]⟩

instance [Operator.Mul L] : Structure.Mul L (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩

instance [Operator.LT L] : LT (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.LT.lt L _).val ![x, y]⟩

instance [Operator.LT L] : Structure.LT L (ModelOfSatEq sat) := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance [Operator.Mem L] : Membership (ModelOfSatEq sat) (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Mem.mem L _).val ![y, x]⟩

instance [Operator.Mem L] : Structure.Mem L (ModelOfSatEq sat) := ⟨fun _ _ ↦ iff_of_eq rfl⟩

end ModelOfSatEq

namespace Semiformula

def existsUnique {ξ} (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  “∃ y, !φ y ⋯ ∧ ∀ z, !φ z ⋯ → z = y”

prefix:64 "∃⁰! " => existsUnique

variable {M : Type*} [s : Structure L M] [Structure.Eq L M]

@[simp] lemma eval_existsUnique {e ε} {φ : Semiformula L ξ (n + 1)} :
    Eval e ε (∃⁰! φ) ↔ ∃! x : M, Eval (x :> e) ε φ := by
  simp [existsUnique, Semiformula.eval_substs, Matrix.comp_vecCons'', ExistsUnique]
  simp [Function.comp_def]

end Semiformula

namespace BinderNotation

open Lean PrettyPrinter Delaborator SubExpr

syntax:max "∃! " first_order_formula:0 : first_order_formula
syntax:max "∃! " ident ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃! $φ:first_order_formula ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃⁰! ⤫formula($type)[ $binders'* | $fbinders* | $φ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃! $x, $φ ])                 => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(∃⁰! ⤫formula($type)[ $binders'* | $fbinders* | $φ ])

end BinderNotation

end FirstOrder

end LO

end
