import Logic.Logic.Semantics
import Logic.FirstOrder.Basic.Formula

namespace LO

namespace FirstOrder

variable {L : Language.{u}} {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂}

@[ext] class Structure (L : Language.{u}) (M : Type w) where
  func : ⦃k : ℕ⦄ → L.Func k → (Fin k → M) → M
  rel : ⦃k : ℕ⦄ → L.Rel k → (Fin k → M) → Prop

namespace Structure

instance [Inhabited M] : Inhabited (Structure L M) := ⟨{ func := fun _ _ => default, rel := fun _ _ _ => True }⟩



protected def lMap (φ : L₁ →ᵥ L₂) {M : Type w} (S : Structure L₂ M) : Structure L₁ M where
  func := fun _ f => S.func (φ.func f)
  rel := fun _ r => S.rel (φ.rel r)

variable (φ : L₁ →ᵥ L₂) {M : Type w} (s₂ : Structure L₂ M)

@[simp] lemma lMap_func {k} {f : L₁.Func k} {v : Fin k → M} : (s₂.lMap φ).func f v = s₂.func (φ.func f) v := rfl

@[simp] lemma lMap_rel {k} {r : L₁.Rel k} {v : Fin k → M} : (s₂.lMap φ).rel r v ↔ s₂.rel (φ.rel r) v := of_eq rfl

def ofEquiv {M : Type w} [Structure L M] {N : Type w'} (φ : M ≃ N) : Structure L N where
  func := fun _ f v => φ (func f (φ.symm ∘ v))
  rel  := fun _ r v => rel r (φ.symm ∘ v)

protected abbrev Decidable (L : Language.{u}) (M : Type w) [s : Structure L M] :=
  {k : ℕ} → (r : L.Rel k) → (v : Fin k → M) → Decidable (s.rel r v)

noncomputable instance [Structure L M] : Structure.Decidable L M := fun r v => Classical.dec (rel r v)

end Structure

namespace Subterm

variable
  {M : Type w} {s : Structure L M}
  {e : Fin n → M} {e₁ : Fin n₁ → M} {e₂ : Fin n₂ → M}
  {ε : μ → M} {ε₁ : μ₁ → M} {ε₂ : μ₂ → M}

def val (s : Structure L M) (e : Fin n → M) (ε : μ → M) : Subterm L μ n → M
  | #x       => e x
  | &x       => ε x
  | func f v => s.func f (fun i => (v i).val s e ε)

abbrev bVal (s : Structure L M) (e : Fin n → M) (t : Subterm L Empty n) : M := t.val s e Empty.elim

abbrev val! (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : μ → M) : Subterm L μ n → M := val s e ε

abbrev bVal! (M : Type w) [s : Structure L M] {n} (e : Fin n → M) : Subterm L Empty n → M := bVal s e

abbrev realize (s : Structure L M) (t : Term L M) : M := t.val s ![] id

@[simp] lemma val_bvar (x) : val s e ε (#x : Subterm L μ n) = e x := rfl

@[simp] lemma val_fvar (x) : val s e ε (&x : Subterm L μ n) = ε x := rfl

lemma val_func {k} (f : L.Func k) (v) :
    val s e ε (func f v) = s.func f (fun i => (v i).val s e ε) := rfl

@[simp] lemma val_func₀ (f : L.Func 0) (v) :
    val s e ε (func f v) = s.func f ![] := by simp[val_func, Matrix.empty_eq]

@[simp] lemma val_func₁ (f : L.Func 1) (t) :
    val s e ε (func f ![t]) = s.func f ![t.val s e ε] :=
  by simp[val_func]; congr; funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma val_func₂ (f : L.Func 2) (t u) :
    val s e ε (func f ![t, u]) = s.func f ![t.val s e ε, u.val s e ε] :=
  by simp[val_func]; congr; funext i; cases' i using Fin.cases with i <;> simp

lemma val_rew (ω : Rew L μ₁ n₁ μ₂ n₂) (t : Subterm L μ₁ n₁) :
    (ω t).val s e₂ ε₂ = t.val s (val s e₂ ε₂ ∘ ω ∘ bvar) (val s e₂ ε₂ ∘ ω ∘ fvar) :=
  by induction t <;> simp[*, Rew.func, val_func]

lemma val_rewrite (f : μ₁ → Subterm L μ₂ n) (t : Subterm L μ₁ n) :
    (Rew.rewrite f t).val s e ε₂ = t.val s e (fun x => (f x).val s e ε₂) :=
  by simp[val_rew]; congr

lemma val_substs (w : Fin n₁ → Subterm L μ n₂) (t : Subterm L μ n₁) :
    (Rew.substs w t).val s e₂ ε = t.val s (fun x => (w x).val s e₂ ε) ε :=
  by simp[val_rew]; congr

@[simp] lemma val_bShift (a : M) (t : Subterm L μ n) :
    (Rew.bShift t).val s (a :> e) ε = t.val s e ε := by simp[val_rew, Function.comp]

@[simp] lemma val_emb {o : Type v'} [i : IsEmpty o] (t : Subterm L o n) :
    (Rew.emb t : Subterm L μ n).val s e ε = t.val s e i.elim := by
  simp[val_rew]; congr; { funext x; exact i.elim' x }

@[simp] lemma val_castLE (h : n₁ ≤ n₂) (t : Subterm L μ n₁) :
    (Rew.castLE h t).val s e₂ ε = t.val s (fun x => e₂ (x.castLE h)) ε  := by
  simp[val_rew]; congr

def Operator.val {M : Type w} [s : Structure L M] (o : Operator L k) (v : Fin k → M) : M :=
  Subterm.val s v Empty.elim o.term

lemma val_operator {k} (o : Operator L k) (v) :
    val s e ε (o.operator v) = o.val (fun x => (v x).val s e ε) := by
  simp[Operator.operator, val_substs]; congr; funext x; contradiction

@[simp] lemma val_const (o : Const L) :
    val s e ε o.const = o.val ![] := by
  simp[Operator.const, val_operator, Matrix.empty_eq]

@[simp] lemma val_operator₀ (o : Const L) :
    val s e ε (o.operator v) = o.val ![] := by
  simp[val_operator, Matrix.empty_eq]

@[simp] lemma val_operator₁ (o : Operator L 1) :
    val s e ε (o.operator ![t]) = o.val ![t.val s e ε] := by
  simp[val_operator, Matrix.empty_eq]; congr; funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma val_operator₂ (o : Operator L 2) (t u) :
    val s e ε (o.operator ![t, u]) = o.val ![t.val s e ε, u.val s e ε] :=
  by simp[val_operator]; congr; funext i; cases' i using Fin.cases with i <;> simp

namespace Operator

lemma val_comp (o₁ : Operator L k) (o₂ : Fin k → Operator L m) (v : Fin m → M) :
  (o₁.comp o₂).val v = o₁.val (fun i => (o₂ i).val v) := by simp[comp, val, val_operator]

end Operator

section Language

variable (φ : L₁ →ᵥ L₂) (e : Fin n → M) (ε : μ → M)

lemma val_lMap (φ : L₁ →ᵥ L₂) (s₂ : Structure L₂ M) (e : Fin n → M) (ε : μ → M) {t : Subterm L₁ μ n} :
    (t.lMap φ).val s₂ e ε = t.val (s₂.lMap φ) e ε :=
  by induction t <;> simp[*, val!, Function.comp, val_func, Subterm.lMap_func]

end Language

section Syntactic

variable (ε : ℕ → M)

lemma val_shift (t : SyntacticSubterm L n) :
    (Rew.shift t).val s e ε = t.val s e (ε ∘ Nat.succ) := by simp[val_rew]; congr

lemma val_free (a : M) (t : SyntacticSubterm L (n + 1)) :
    (Rew.free t).val s e (a :>ₙ ε) = t.val s (e <: a) ε :=
  by simp[val_rew]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma val_fix (a : M) (t : SyntacticSubterm L n) :
    (Rew.fix t).val s (e <: a) ε = t.val s e (a :>ₙ ε) :=
  by simp[val_rew]; congr <;> simp[Function.comp]; exact funext (Nat.cases (by simp) (by simp))

end Syntactic

end Subterm

namespace Structure

section

variable [s : Structure L M] (φ : M ≃ N)

lemma ofEquiv_func (f : L.Func k) (v : Fin k → N) :
    (ofEquiv φ).func f v = φ (func f (φ.symm ∘ v)) := rfl

lemma ofEquiv_val (e : Fin n → N) (ε : μ → N) (t : Subterm L μ n) :
    t.val (ofEquiv φ) e ε = φ (t.val s (φ.symm ∘ e) (φ.symm ∘ ε)) := by
  induction t <;> simp[*, Subterm.val_func, ofEquiv_func φ, Function.comp]

end

open Subterm

protected class Zero (L : Language.{u}) [Operator.Zero L] (M : Type w) [Zero M] [s : Structure L M] where
  zero : (@Operator.Zero.zero L _).val ![] = (0 : M)

protected class One (L : Language.{u}) [Operator.One L] (M : Type w) [One M] [s : Structure L M] where
  one : (@Operator.One.one L _).val ![] = (1 : M)

protected class Add (L : Language.{u}) [Operator.Add L] (M : Type w) [Add M] [s : Structure L M] where
  add : ∀ a b : M, (@Operator.Add.add L _).val ![a, b] = a + b

protected class Mul (L : Language.{u}) [Operator.Mul L] (M : Type w) [Mul M] [s : Structure L M] where
  mul : ∀ a b : M, (@Operator.Mul.mul L _).val ![a, b] = a * b

attribute [simp] Zero.zero One.one Add.add Mul.mul

@[simp] lemma zero_eq_of_lang [L.Zero] {M : Type w} [Zero M] [Structure L M] [Structure.Zero L M] :
    Structure.func (L := L) Language.Zero.zero ![] = (0 : M) := by
  simpa[Operator.val, Subterm.Operator.Zero.zero, val_func, ←Matrix.fun_eq_vec₂] using
    Structure.Zero.zero (L := L) (M := M)

@[simp] lemma one_eq_of_lang [L.One] {M : Type w} [One M] [Structure L M] [Structure.One L M] :
    Structure.func (L := L) Language.One.one ![] = (1 : M) := by
  simpa[Operator.val, Subterm.Operator.One.one, val_func, ←Matrix.fun_eq_vec₂] using
    Structure.One.one (L := L) (M := M)

@[simp] lemma add_eq_of_lang [L.Add] {M : Type w} [Add M] [Structure L M] [Structure.Add L M] {v : Fin 2 → M} :
    Structure.func (L := L) Language.Add.add v = v 0 + v 1 := by
  simpa[Operator.val, val_func, ←Matrix.fun_eq_vec₂] using
    Structure.Add.add (L := L) (v 0) (v 1)

@[simp] lemma mul_eq_of_lang [L.Mul] {M : Type w} [Mul M] [Structure L M] [Structure.Mul L M] {v : Fin 2 → M} :
    Structure.func (L := L) Language.Mul.mul v = v 0 * v 1 := by
  simpa[Operator.val, val_func, ←Matrix.fun_eq_vec₂] using
    Structure.Mul.mul (L := L) (v 0) (v 1)

end Structure

namespace Subformula

variable {M : Type w} {s : Structure L M}
variable {n : ℕ} {e : Fin n → M} {e₂ : Fin n₂ → M} {ε : μ → M} {ε₂ : μ₂ → M}

def Eval' (s : Structure L M) (ε : μ → M) : ∀ {n}, (Fin n → M) → Subformula L μ n → Prop
  | _, _, ⊤        => True
  | _, _, ⊥        => False
  | _, e, rel p v  => s.rel p (fun i => Subterm.val s e ε (v i))
  | _, e, nrel p v => ¬s.rel p (fun i => Subterm.val s e ε (v i))
  | _, e, p ⋏ q    => p.Eval' s ε e ∧ q.Eval' s ε e
  | _, e, p ⋎ q    => p.Eval' s ε e ∨ q.Eval' s ε e
  | _, e, ∀' p     => ∀ x : M, (p.Eval' s ε (x :> e))
  | _, e, ∃' p     => ∃ x : M, (p.Eval' s ε (x :> e))

@[simp] lemma Eval'_neg (p : Subformula L μ n) :
    Eval' s ε e (~p) = ¬Eval' s ε e p :=
  by induction p using rec' <;> simp[*, Eval', ←neg_eq, or_iff_not_imp_left]

def Eval (s : Structure L M) (e : Fin n → M) (ε : μ → M) : Subformula L μ n →L Prop where
  toTr := Eval' s ε e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp[Eval']
  map_or' := by simp[Eval']
  map_neg' := by simp[Eval'_neg]
  map_imply' := by simp[imp_eq, Eval'_neg, ←neg_eq, Eval', imp_iff_not_or]

abbrev Eval! (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : μ → M) :
    Subformula L μ n →L Prop := Eval s e ε

abbrev Val (s : Structure L M) (ε : μ → M) : Formula L μ →L Prop := Eval s ![] ε

abbrev PVal (s : Structure L M) (e : Fin n → M) : Subsentence L n →L Prop := Eval s e Empty.elim

abbrev Val! (M : Type w) [s : Structure L M] (ε : μ → M) :
    Formula L μ →L Prop := Val s ε

abbrev PVal! (M : Type w) [s : Structure L M] (e : Fin n → M) :
    Subformula L Empty n →L Prop := PVal s e

abbrev Realize (s : Structure L M) : Formula L M →L Prop := Eval s ![] id

lemma eval_rel {k} {r : L.Rel k} {v} :
    Eval s e ε (rel r v) ↔ s.rel r (fun i => Subterm.val s e ε (v i)) := of_eq rfl

@[simp] lemma eval_rel₀ {r : L.Rel 0} :
    Eval s e ε (rel r ![]) ↔ s.rel r ![] := by simp[eval_rel, Matrix.empty_eq]

@[simp] lemma eval_rel₁ {r : L.Rel 1} (t : Subterm L μ n) :
    Eval s e ε (rel r ![t]) ↔ s.rel r ![t.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_rel₂ {r : L.Rel 2} (t₁ t₂ : Subterm L μ n) :
    Eval s e ε (rel r ![t₁, t₂]) ↔ s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

lemma eval_nrel {k} {r : L.Rel k} {v} :
    Eval s e ε (nrel r v) ↔ ¬s.rel r (fun i => Subterm.val s e ε (v i)) := of_eq rfl

@[simp] lemma eval_nrel₀ {r : L.Rel 0} :
    Eval s e ε (nrel r ![]) ↔ ¬s.rel r ![] := by simp[eval_nrel, Matrix.empty_eq]

@[simp] lemma eval_nrel₁ {r : L.Rel 1} (t : Subterm L μ n) :
    Eval s e ε (nrel r ![t]) ↔ ¬s.rel r ![t.val s e ε] := by
  simp[eval_nrel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_nrel₂ {r : L.Rel 2} (t₁ t₂ : Subterm L μ n) :
    Eval s e ε (nrel r ![t₁, t₂]) ↔ ¬s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_nrel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_all {p : Subformula L μ (n + 1)} :
    Eval s e ε (∀' p) ↔ ∀ x : M, Eval s (x :> e) ε p := of_eq rfl

@[simp] lemma eval_univClosure {e'} {p : Subformula L μ n'} :
    Eval s e' ε (univClosure p) ↔ ∀ e, Eval s e ε p := by
  induction' n' with n' ih generalizing e' <;> simp[*, eq_finZeroElim]
  constructor
  · intro h e; simpa using h (Matrix.vecTail e) (Matrix.vecHead e)
  · intro h e x; exact h (x :> e)

@[simp] lemma eval_ball {p q : Subformula L μ (n + 1)} :
    Eval s e ε (∀[p] q) ↔ ∀ x : M, Eval s (x :> e) ε p → Eval s (x :> e) ε q := by
  simp[LogicSymbol.ball]

@[simp] lemma eval_ex {p : Subformula L μ (n + 1)} :
    Eval s e ε (∃' p) ↔ ∃ x : M, Eval s (x :> e) ε p := of_eq rfl

@[simp] lemma eval_exClosure {e'} {p : Subformula L μ n'} :
    Eval s e' ε (exClosure p) ↔ ∃ e, Eval s e ε p := by
  induction' n' with n' ih generalizing e' <;> simp[*, eq_finZeroElim]
  constructor
  · rintro ⟨e, x, h⟩; exact ⟨x :> e, h⟩
  · rintro ⟨e, h⟩; exact ⟨Matrix.vecTail e, Matrix.vecHead e, by simpa using h⟩

@[simp] lemma eval_bex {p q : Subformula L μ (n + 1)} :
    Eval s e ε (∃[p] q) ↔ ∃ x : M, Eval s (x :> e) ε p ⋏ Eval s (x :> e) ε q := by
  simp[LogicSymbol.bex]

lemma eval_rew (ω : Rew L μ₁ n₁ μ₂ n₂) (p : Subformula L μ₁ n₁) :
    Eval s e₂ ε₂ (ω.hom p) ↔ Eval s (Subterm.val s e₂ ε₂ ∘ ω ∘ Subterm.bvar) (Subterm.val s e₂ ε₂ ∘ ω ∘ Subterm.fvar) p := by
  induction p using rec' generalizing n₂ <;> simp[*, Subterm.val_rew, eval_rel, eval_nrel, Rew.rel, Rew.nrel]
  case hall => simp[Function.comp]; exact iff_of_eq $ forall_congr (fun x => by congr; funext i; cases i using Fin.cases <;> simp)
  case hex => simp[Function.comp]; exact exists_congr (fun x => iff_of_eq $ by congr; funext i; cases i using Fin.cases <;> simp)

lemma eval_map (b : Fin n₁ → Fin n₂) (f : μ₁ → μ₂) (e : Fin n₂ → M) (ε : μ₂ → M) (p : Subformula L μ₁ n₁) :
    Eval s e ε ((Rew.map b f).hom p) ↔ Eval s (e ∘ b) (ε ∘ f) p :=
  by simp[eval_rew, Function.comp]

lemma eval_rewrite (f : μ₁ → Subterm L μ₂ n) (p : Subformula L μ₁ n) :
    Eval s e ε₂ ((Rew.rewrite f).hom p) ↔ Eval s e (fun x => (f x).val s e ε₂) p :=
  by simp[eval_rew, Function.comp]

@[simp] lemma eval_castLE (h : n₁ ≤ n₂) (p : Subformula L μ n₁) :
    Eval s e₂ ε ((Rew.castLE h).hom p) ↔ Eval s (fun x => e₂ (x.castLE h)) ε p := by
  simp[eval_rew, Function.comp]

lemma eval_substs {k} (w : Fin k → Subterm L μ n) (p : Subformula L μ k) :
    Eval s e ε ((Rew.substs w).hom p) ↔ Eval s (fun i => (w i).val s e ε) ε p :=
  by simp[eval_rew, Function.comp]

@[simp] lemma eval_emb (p : Subformula L Empty n) :
    Eval s e ε (Rew.emb.hom p) ↔ Eval s e Empty.elim p := by
  simp[eval_rew, Function.comp]; apply iff_of_eq; congr; funext x; contradiction

section Syntactic

variable (ε : ℕ → M)

@[simp] lemma eval_free (p : SyntacticSubformula L (n + 1)) :
    Eval s e (a :>ₙ ε) (Rew.free.hom p) ↔ Eval s (e <: a) ε p :=
  by simp[eval_rew, Function.comp]; congr; apply iff_of_eq; congr; funext x; cases x using Fin.lastCases <;> simp

@[simp] lemma eval_shift (p : SyntacticSubformula L n) :
    Eval s e (a :>ₙ ε) (Rew.shift.hom p) ↔ Eval s e ε p :=
  by simp[eval_rew, Function.comp]

end Syntactic

def Operator.val {M : Type w} [s : Structure L M] {k} (o : Operator L k) (v : Fin k → M) : Prop :=
  Subformula.Eval s v Empty.elim o.sentence

@[simp] lemma val_operator_and {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.and o₂).val v ↔ o₁.val v ∧ o₂.val v := by simp[Operator.and, Operator.val]

@[simp] lemma val_operator_or {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.or o₂).val v ↔ o₁.val v ∨ o₂.val v := by simp[Operator.or, Operator.val]

lemma eval_operator {k} {o : Operator L k} {v : Fin k → Subterm L μ n} :
    Eval s e ε (o.operator v) ↔ o.val (fun i => (v i).val s e ε) := by
  simp[Operator.operator, eval_substs, Operator.val]

@[simp] lemma eval_operator₀ {o : Const L} {v} :
    Eval s e ε (o.operator v) ↔ o.val (M := M) ![] := by
  simp[eval_operator, Matrix.empty_eq]

@[simp] lemma eval_operator₁ {o : Operator L 1} {t : Subterm L μ n} :
    Eval s e ε (o.operator ![t]) ↔ o.val ![t.val s e ε] := by
  simp[eval_operator, Matrix.constant_eq_singleton]

@[simp] lemma eval_operator₂ {o : Operator L 2} {t₁ t₂ : Subterm L μ n} :
    Eval s e ε (o.operator ![t₁, t₂]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_operator]; apply of_eq; congr; funext i; cases' i using Fin.cases with i <;> simp

end Subformula

namespace Structure

section

open Subformula

protected class Eq (L : Language.{u}) [Operator.Eq L] (M : Type w) [s : Structure L M] where
  eq : ∀ a b : M, (@Operator.Eq.eq L _).val ![a, b] ↔ a = b

protected class LT (L : Language.{u}) [Operator.LT L] (M : Type w) [LT M] [s : Structure L M] where
  lt : ∀ a b : M, (@Operator.LT.lt L _).val ![a, b] ↔ a < b

protected class LE (L : Language.{u}) [Operator.LE L] (M : Type w) [LE M] [s : Structure L M] where
  le : ∀ a b : M, (@Operator.LE.le L _).val ![a, b] ↔ a ≤ b

class Mem (L : Language.{u}) [Operator.Mem L] (M : Type w) [Membership M M] [s : Structure L M] where
  mem : ∀ a b : M, (@Operator.Mem.mem L _).val ![a, b] ↔ a ∈ b

attribute [simp] Structure.Eq.eq Structure.LT.lt Structure.LE.le Structure.Mem.mem

@[simp] lemma le_iff_of_eq_of_lt [Operator.Eq L] [Operator.LT L] {M : Type w} [LT M]
    [Structure L M] [Structure.Eq L M] [Structure.LT L M] {a b : M} :
    (@Operator.LE.le L _).val ![a, b] ↔ a = b ∨ a < b := by
  simp[Operator.LE.def_of_Eq_of_LT]

@[simp] lemma eq_lang [L.Eq] {M : Type w} [Structure L M] [Structure.Eq L M] {v : Fin 2 → M} :
    Structure.rel (L := L) Language.Eq.eq v ↔ v 0 = v 1 := by
  simpa[Operator.val, Subformula.Operator.Eq.sentence_eq, eval_rel, ←Matrix.fun_eq_vec₂] using
    Structure.Eq.eq (L := L) (v 0) (v 1)

@[simp] lemma lt_lang [L.LT] {M : Type w} [LT M] [Structure L M] [Structure.LT L M] {v : Fin 2 → M} :
    Structure.rel (L := L) Language.LT.lt v ↔ v 0 < v 1 := by
  simpa[Operator.val, Subformula.Operator.LT.sentence_eq, eval_rel, ←Matrix.fun_eq_vec₂] using
    Structure.LT.lt (L := L) (v 0) (v 1)

end

section

open Subformula
variable [s : Structure L M] (φ : M ≃ N)

lemma ofEquiv_rel (r : L.Rel k) (v : Fin k → N) :
    (Structure.ofEquiv φ).rel r v ↔ Structure.rel r (φ.symm ∘ v) := iff_of_eq rfl

lemma eval_ofEquiv_iff : ∀ {n} {e : Fin n → N} {ε : μ → N} {p : Subformula L μ n},
    (Eval (ofEquiv φ) e ε p ↔ Eval s (φ.symm ∘ e) (φ.symm ∘ ε) p)
  | _, e, ε, ⊤                   => by simp
  | _, e, ε, ⊥                   => by simp
  | _, e, ε, Subformula.rel r v  => by simp[Function.comp, eval_rel, ofEquiv_rel φ, Structure.ofEquiv_val φ]
  | _, e, ε, Subformula.nrel r v => by simp[Function.comp, eval_nrel, ofEquiv_rel φ, Structure.ofEquiv_val φ]
  | _, e, ε, p ⋏ q               => by simp[eval_ofEquiv_iff (p := p), eval_ofEquiv_iff (p := q)]
  | _, e, ε, p ⋎ q               => by simp[eval_ofEquiv_iff (p := p), eval_ofEquiv_iff (p := q)]
  | _, e, ε, ∀' p                => by
    simp; exact
    ⟨fun h x => by simpa[Matrix.comp_vecCons''] using eval_ofEquiv_iff.mp (h (φ x)),
     fun h x => eval_ofEquiv_iff.mpr (by simpa[Matrix.comp_vecCons''] using h (φ.symm x))⟩
  | _, e, ε, ∃' p                => by
    simp; exact
    ⟨by rintro ⟨x, h⟩; exists φ.symm x; simpa[Matrix.comp_vecCons''] using eval_ofEquiv_iff.mp h,
     by rintro ⟨x, h⟩; exists φ x; apply eval_ofEquiv_iff.mpr; simpa[Matrix.comp_vecCons''] using h⟩

lemma operator_val_ofEquiv_iff {k : ℕ} {o : Operator L k} {v : Fin k → N} :
    letI : Structure L N := ofEquiv φ
    o.val v ↔ o.val (φ.symm ∘ v) := by simp[Operator.val, eval_ofEquiv_iff, Empty.eq_elim]

end

end Structure

instance semantics : Semantics (Sentence L) (Structure.{u, u} L) where
  models := (Subformula.Val · Empty.elim)

abbrev Models (M : Type u) [s : Structure L M] : Sentence L →L Prop := Semantics.models s

scoped postfix:max " ⊧ " => Models

abbrev ModelsTheory (M : Type u) [s : Structure L M] (T : Theory L) : Prop :=
  Semantics.modelsTheory (𝓢 := semantics) s T

scoped infix:55 " ⊧* " => ModelsTheory

abbrev Theory.Mod (M : Type u) [s : Structure L M] (T : Theory L) := Semantics.Mod s T

abbrev Realize (M : Type u) [s : Structure L M] : Formula L M →L Prop := Subformula.Val s id

scoped postfix:max " ⊧ᵣ " => Realize

structure Theory.semanticGe (T₁ : Theory L₁) (T₂ : Theory L₂) :=
  carrier : Type u → Type u
  struc : (M₁ : Type u) → [Structure L₁ M₁] → Structure L₂ (carrier M₁)
  modelsTheory : ∀ {M₁ : Type u} [Structure L₁ M₁], M₁ ⊧* T₁ → ModelsTheory (s := struc M₁) T₂

structure Theory.semanticEquiv (T₁ : Theory L₁) (T₂ : Theory L₂) :=
  toLeft : T₁.semanticGe T₂
  toRight : T₂.semanticGe T₁

def modelsTheory_iff_modelsTheory_s {M : Type u} [s : Structure L M] {T : Theory L} :
  M ⊧* T ↔ s ⊧ₛ* T := by rfl

section
variable {M : Type u} [s : Structure L M] {T : Theory L}

lemma models_def : M ⊧ = Subformula.Val s Empty.elim := rfl

lemma models_iff {σ : Sentence L} : M ⊧ σ ↔ Subformula.Val s Empty.elim σ := by simp[models_def]

lemma models_def' : Semantics.models s = Subformula.Val s Empty.elim := rfl

lemma modelsTheory_iff : M ⊧* T ↔ (∀ ⦃p⦄, p ∈ T → M ⊧ p) := of_eq rfl

lemma models_iff_models {σ : Sentence L} :
    M ⊧ σ ↔ Semantics.models s σ := of_eq rfl

lemma consequence_iff {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Inhabited M] [Structure L M], M ⊧* T → M ⊧ σ) := of_eq rfl

lemma consequence_iff' {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Inhabited M] [Structure L M] [Theory.Mod M T], M ⊧ σ) :=
  ⟨fun h M _ s _ => Semantics.consequence_iff'.mp h M s,
   fun h M i s hs => @h M i s ⟨hs⟩⟩

lemma satisfiableₛ_iff :
    Semantics.Satisfiableₛ T ↔ ∃ (M : Type u) (_ : Inhabited M) (_ : Structure L M), M ⊧* T :=
  of_eq rfl

lemma satisfiableₛ_intro (M : Type u) [i : Inhabited M] [s : Structure L M] (h : M ⊧* T) :
    Semantics.Satisfiableₛ T := ⟨M, i, s, h⟩

noncomputable def ModelOfSat (h : Semantics.Satisfiableₛ T) : Type u :=
  Classical.choose (satisfiableₛ_iff.mp h)

noncomputable instance inhabitedModelOfSat (h : Semantics.Satisfiableₛ T) :
    Inhabited (ModelOfSat h) := by
  choose i _ _ using Classical.choose_spec h; exact i

noncomputable def StructureModelOfSatAux (h : Semantics.Satisfiableₛ T) :
    { s : Structure L (ModelOfSat h) // ModelOfSat h ⊧* T } := by
  choose _ s h using Classical.choose_spec h
  exact ⟨s, h⟩

noncomputable instance StructureModelOfSat (h : Semantics.Satisfiableₛ T) :
    Structure L (ModelOfSat h) := StructureModelOfSatAux h

lemma ModelOfSat.models (h : Semantics.Satisfiableₛ T) : ModelOfSat h ⊧* T := (StructureModelOfSatAux h).prop

lemma valid_iff {σ : Sentence L} :
    Semantics.Valid σ ↔ ∀ ⦃M : Type u⦄ [Inhabited M] [Structure L M], M ⊧ σ :=
  of_eq rfl

lemma validₛ_iff {T : Theory L} :
    Semantics.Validₛ T ↔ ∀ ⦃M : Type u⦄ [Inhabited M] [Structure L M], M ⊧* T :=
  of_eq rfl

end

namespace Subformula

variable {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂}

section lMap
variable {M : Type u} {s₂ : Structure L₂ M} {n} {e : Fin n → M} {ε : μ → M}

lemma eval_lMap {p : Subformula L₁ μ n} :
    Eval s₂ e ε (lMap Φ p) ↔ Eval (s₂.lMap Φ) e ε p :=
  by induction p using rec' <;>
    simp[*, Subterm.val_lMap, lMap_rel, lMap_nrel, eval_rel, eval_nrel]

lemma models_lMap {σ : Sentence L₁} :
    Semantics.models s₂ (lMap Φ σ) ↔ Semantics.models (s₂.lMap Φ) σ :=
  by simp[Semantics.models, Val, eval_lMap]

end lMap

end Subformula

lemma lMap_models_lMap {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂}  {T : Theory L₁} {σ : Sentence L₁} (h : T ⊨ σ) :
    T.lMap Φ ⊨ Subformula.lMap Φ σ := by
  intro M _ s hM
  have : Semantics.models (s.lMap Φ) σ :=
    h M (s.lMap Φ) (fun q hq => Subformula.models_lMap.mp $ hM (Set.mem_image_of_mem _ hq))
  exact Subformula.models_lMap.mpr this

@[simp] lemma ModelsTheory.empty [Structure L M] : M ⊧* (∅ : Theory L)  := by intro _; simp

lemma ModelsTheory.of_ss [Structure L M] {T U : Theory L} (h : M ⊧* U) (ss : T ⊆ U) : M ⊧* T :=
  fun _ hσ => h (ss hσ)

namespace Theory

variable {L₁ L₂ : Language.{u}}
variable {M : Type u} [s₂ : Structure L₂ M]
variable {Φ : L₁ →ᵥ L₂}

lemma modelsTheory_onTheory₁ {T₁ : Theory L₁} :
    ModelsTheory (s := s₂) (T₁.lMap Φ) ↔ ModelsTheory (s := s₂.lMap Φ) T₁ :=
  by simp[Subformula.models_lMap, Theory.lMap, modelsTheory_iff, @modelsTheory_iff (T := T₁)]

namespace semanticGe

def of_ss {T₁ : Theory L₁} {T₂ : Theory L₂} (ss : T₁.lMap Φ ⊆ T₂) : T₂.semanticGe T₁ where
  carrier := id
  struc := fun _ s => s.lMap Φ
  modelsTheory := fun {M _} h => (modelsTheory_onTheory₁ (M := M)).mp (h.of_ss ss)

protected def refl {T : Theory L} : T.semanticGe T where
  carrier := id
  struc := fun _ s => s
  modelsTheory := fun h => h

protected def trans {T₁ : Theory L₁} {T₂ : Theory L₂} {T₃ : Theory L₃}
  (g₃ : T₃.semanticGe T₂) (g₂ : T₂.semanticGe T₁) : T₃.semanticGe T₁ where
  carrier := g₂.carrier ∘ g₃.carrier
  struc := fun M₃ _ => let _ := g₃.struc M₃; g₂.struc (g₃.carrier M₃)
  modelsTheory := fun {M₃ _} h =>
    let _ := g₃.struc M₃
    g₂.modelsTheory (g₃.modelsTheory h)

end semanticGe

namespace Mod

variable (M : Type u) [s : Structure L M] { T : Theory L} [Theory.Mod M T]

lemma models {σ : Sentence L} (hσ : σ ∈ T) : M ⊧ σ := Semantics.Mod.models M s hσ

def of_ss {T₁ T₂ : Theory L} [Theory.Mod M T₁] (ss : T₂ ⊆ T₁) : Theory.Mod M T₂ :=
  Semantics.Mod.of_ss M s ss

lemma of_subtheory [Inhabited M] {T₁ T₂ : Theory L} [Theory.Mod M T₁] (h : Semantics.Subtheory T₂ T₁) : Theory.Mod M T₂ :=
  Semantics.Mod.of_subtheory M s h

end Mod

end Theory

namespace Structure

variable (L)

abbrev theory (M : Type u) [s : Structure L M] : Theory L := Semantics.theory s

variable {L} {M : Type u} [Structure L M]

@[simp] lemma mem_theory_iff {σ} : σ ∈ theory L M ↔ M ⊧ σ := by rfl

lemma subset_of_models : T ⊆ theory L M ↔ M ⊧* T := ⟨fun h _ hσ ↦ h hσ, fun h _ hσ ↦ h hσ⟩

end Structure

end FirstOrder

end LO
