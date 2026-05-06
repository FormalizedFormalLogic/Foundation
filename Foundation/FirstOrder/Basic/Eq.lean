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

variable {L : Language} {ξ : Type*} [Semiformula.Operator.Eq L]

namespace Theory

section Eq

variable (L)

abbrev Eq.refl : Sentence L := “∀ x, x = x”

abbrev Eq.symm : Sentence L := “∀ x y, x = y → y = x”

abbrev Eq.trans : Sentence L := “∀ x y z, x = y → y = z → x = z”

variable {L}

abbrev Eq.funcExt {k} (f : L.Func k) : Sentence L :=
  let σ : Semisentence L (k + k) :=
    (Matrix.conj fun i : Fin k ↦ “#(i.addCast k) = #(i.addNat k)”) 🡒
      op(=).operator ![Semiterm.func f (fun i ↦ #(i.addCast k)), Semiterm.func f (fun i ↦ #(i.addNat k))]
  ∀⁰* σ

abbrev Eq.relExt {k} (r : L.Rel k) : Sentence L :=
  let σ : Semisentence L (k + k) :=
    (Matrix.conj fun i : Fin k ↦ “#(i.addCast k) = #(i.addNat k)”) 🡒
      Semiformula.rel r (fun i ↦ #(i.addCast k)) 🡒 Semiformula.rel r (fun i ↦ #(i.addNat k))
  ∀⁰* σ

variable (L)

inductive eqAxiom : Theory L
  | refl : eqAxiom (Eq.refl L)
  | symm : eqAxiom (Eq.symm L)
  | trans : eqAxiom (Eq.trans L)
  | funcExt {k} (f : L.Func k) : eqAxiom (Eq.funcExt f)
  | relExt {k} (r : L.Rel k) : eqAxiom (Eq.relExt r)

notation "𝗘𝗤" => eqAxiom

variable {L}

lemma Eq.defeq :
    𝗘𝗤 L = {Eq.refl L, Eq.symm L, Eq.trans L}
      ∪ Set.range (fun f : (k : ℕ) × L.Func k ↦ Eq.funcExt f.2)
      ∪ Set.range (fun f : (k : ℕ) × L.Rel k ↦ Eq.relExt f.2) := by
  ext φ; constructor
  · rintro ⟨⟩
    case refl => simp
    case symm => simp
    case trans => simp
    case funcExt k f =>
      left; right; exact ⟨⟨k, f⟩, rfl⟩
    case relExt k r =>
      right; exact ⟨⟨k, r⟩, rfl⟩
  · rintro (((rfl | rfl | rfl) | ⟨f, rfl⟩) | ⟨r, rfl⟩)
    · exact eqAxiom.refl
    · exact eqAxiom.symm
    · exact eqAxiom.trans
    · exact eqAxiom.funcExt _
    · exact eqAxiom.relExt _

@[simp] lemma EqAxiom.finite [L.Finite] : Set.Finite (𝗘𝗤 L) := by
  haveI : Fintype ((k : ℕ) × L.Func k) := Language.Finite.func
  haveI : Fintype ((k : ℕ) × L.Rel k) := Language.Finite.rel
  rw [Eq.defeq]
  simp [Set.finite_range]

end Eq

end Theory

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
  simpa using this a

lemma eqv_symm {a b : M} : eqv L a b → eqv L b a := by
  have : M↓[L] ⊧ “∀ x y, x = y → y = x” := H.models _ (Theory.eqAxiom.symm (L := L))
  have : ∀ x y : M, op(=)[L].val ![x, y] → op(=)[L].val ![y, x] := by simpa [models_iff] using this
  simpa using this a b

lemma eqv_trans {a b c : M} : eqv L a b → eqv L b c → eqv L a c := by
  have : M↓[L] ⊧ “∀ x y z, x = y → y = z → x = z” := H.models _ (Theory.eqAxiom.trans (L := L))
  have : ∀ x y z : M, op(=)[L].val ![x, y] → op(=)[L].val ![y, z] → op(=)[L].val ![x, z] := by simpa [models_iff] using this
  simpa using this a b c

lemma eqv_funcExt {k} (f : L.Func k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    eqv L (func f v) (func f w) := by
  have : M↓[L] ⊧ Eq.funcExt f := H.models _ (eqAxiom.funcExt f)
  have :
      ∀ m : Fin (k + k) → M,
      (∀ (i : Fin k), op(=)[L].val ![m (Fin.addCast k i), m (i.addNat k)]) →
        op(=)[L].val ![func f fun i ↦ m (Fin.addCast k i), func f fun i ↦ m (i.addNat k)] := by
    simpa [models_iff, Semiterm.val_func] using this
  have := this (Matrix.vecAppend rfl v w) (fun i ↦ by simpa [Matrix.vecAppend_eq_ite] using h i)
  simpa [Semiterm.val_func, Matrix.vecAppend_eq_ite] using this

lemma eqv_relExt_aux {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v → rel r w := by
  have : M↓[L] ⊧ Eq.relExt r := H.models _ (eqAxiom.relExt r)
  have :
      ∀ m : Fin (k + k) → M,
      (∀ (i : Fin k), op(=)[L].val ![m (Fin.addCast k i), m (i.addNat k)]) →
        (rel r fun i ↦ m (Fin.addCast k i)) → rel r fun i ↦ m (i.addNat k) := by
    simpa [models_iff, Semiterm.val_func] using this
  have := this (Matrix.vecAppend rfl v w) (fun i ↦ by simpa [Matrix.vecAppend_eq_ite] using h i)
  simpa [Semiterm.val_func, Matrix.vecAppend_eq_ite] using this

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

lemma val_mk {bv fv} (t : Semiterm L ξ n) :
    t.val (M := QuotEq L M) (⟦bv ·⟧) (⟦fv ·⟧) = ⟦t.val bv fv⟧ := by
  induction t <;> simp [*, funk_mk, Function.comp_def]

lemma eval_mk {bv fv} {φ : Semiformula L ξ n} :
    φ.Eval (M := QuotEq L M) (⟦bv ·⟧) (⟦fv ·⟧) ↔ φ.Eval bv fv := by
  induction φ using Semiformula.rec'
  case hall n φ ih =>
    constructor
    · intro h a; exact (ih (bv := a :> bv)).mp (by simpa [Matrix.comp_vecCons] using h ⟦a⟧)
    · intro h a;
      induction' a using Quotient.ind with a
      simpa [Matrix.comp_vecCons] using ih.mpr (h a)
  case hexs n φ ih =>
    constructor
    · intro ⟨a, h⟩
      induction' a using Quotient.ind with a
      exact ⟨a, (ih (bv := a :> bv)).mp (by simpa [Matrix.comp_vecCons] using h)⟩
    · intro ⟨a, h⟩; exact ⟨⟦a⟧, by simpa [Matrix.comp_vecCons] using ih.mpr h⟩
  case _ => simp [*]
  case _ => simp [*]
  case _ => simp [*, val_mk, rel_mk, Function.comp_def]
  case _ => simp [*, val_mk, rel_mk, Function.comp_def]
  case _ => simp [*]
  case _ => simp [*]

lemma evalf_mk {fv} {φ : Formula L ξ} :
    φ.Evalf (M := QuotEq L M) (⟦fv ·⟧) ↔ φ.Evalf fv := by
  simpa [Matrix.empty_eq] using eval_mk (bv := ![]) (fv := fv) (φ := φ)

lemma models_iff {σ : Sentence L} : (QuotEq L M)↓[L] ⊧ σ ↔ M↓[L] ⊧ σ := by
  simpa [Empty.eq_elim, Matrix.empty_eq] using
    eval_mk (M := M) (ξ := Empty) (φ := σ) (bv := ![]) (fv := Empty.elim)

variable (L M)

lemma elementaryEquiv : QuotEq L M ≡ₑ[L] M := ⟨models_iff⟩

variable {L M}

set_option backward.isDefEq.respectTransparency false in
lemma rel_eq (a b : QuotEq L M) : (@Semiformula.Operator.Eq.eq L _).val (M := QuotEq L M) ![a, b] ↔ a = b := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  rw [of_eq_of]; simp [eqv, Semiformula.Operator.val];
  simpa [Matrix.fun_eq_vec_two, Empty.eq_elim] using
    eval_mk (H := H) (bv := ![a, b]) (fv := Empty.elim) (φ := Semiformula.Operator.Eq.eq.sentence)

instance structureEq : Structure.Eq L (QuotEq L M) := ⟨rel_eq⟩

end QuotEq

end Eq

end Structure

lemma consequence_iff_eq {T : Theory L} [𝗘𝗤 L ⪯ T] {σ : Sentence L} :
    T ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M], M↓[L] ⊧* T → M↓[L] ⊧ σ) := by
  simp only [consequence_iff, Nonempty.forall]
  constructor
  · intro h M x s _ hM; exact h M x hM
  · intro h M x s hM
    haveI : Nonempty M := ⟨x⟩
    have H : M↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory hM
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M
    exact e.models.mp $ h (Structure.Eq.QuotEq L M) ⟦x⟧ (e.modelsTheory.mpr hM)

lemma consequence_iff_eq' {T : Theory L} [𝗘𝗤 L ⪯ T] {σ : Sentence L} :
    T ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M] [M↓[L] ⊧* T], M↓[L] ⊧ σ) := by
  rw [consequence_iff_eq]

lemma satisfiable_iff_eq {T : Theory L} [𝗘𝗤 L ⪯ T] :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔ (∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M) (_ : Structure.Eq L M), M↓[L] ⊧* T) := by
  simp only [satisfiable_iff, Nonempty.exists, exists_prop]
  constructor
  · intro ⟨M, x, s, hM⟩;
    haveI : Nonempty M := ⟨x⟩
    have H : M↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory hM
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M
    exact ⟨Structure.Eq.QuotEq L M, ⟦x⟧, inferInstance, inferInstance, e.modelsTheory.mpr hM⟩
  · intro ⟨M, i, s, _, hM⟩; exact ⟨M, i, s, hM⟩

instance {T : Theory L} [𝗘𝗤 L ⪯ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T) :
    (ModelOfSat sat)↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory (ModelOfSat.models sat)

def ModelOfSatEq {T : Theory L} [𝗘𝗤 L ⪯ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T) : Type _ :=
  Structure.Eq.QuotEq L (ModelOfSat sat)

namespace ModelOfSatEq

variable {T : Theory L} [𝗘𝗤 L ⪯ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T)

noncomputable instance : Nonempty (ModelOfSatEq sat) := Structure.Eq.QuotEq.inhabited

noncomputable instance struc : Structure L (ModelOfSatEq sat) := Structure.Eq.QuotEq.struc

noncomputable instance : Structure.Eq L (ModelOfSatEq sat) := Structure.Eq.QuotEq.structureEq

lemma models : (ModelOfSatEq sat)↓[L] ⊧* T :=
  have e : ModelOfSatEq sat ≡ₑ[L] ModelOfSat sat := Structure.Eq.QuotEq.elementaryEquiv L (ModelOfSat sat)
  e.modelsTheory.mpr (ModelOfSat.models _)

instance mod : (ModelOfSatEq sat)↓[L] ⊧* T := models sat

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

prefix:64 "∃⁰! " => existsUnique

variable {M : Type*} [s : Structure L M] [Structure.Eq L M]

@[simp] lemma eval_existsUnique {e ε} {φ : Semiformula L ξ (n + 1)} :
    Eval (M := M) e ε (∃⁰! φ) ↔ ∃! x, Eval (M := M) (x :> e) ε φ := by
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
