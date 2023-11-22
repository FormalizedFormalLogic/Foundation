import Logic.Logic.Semantics
import Logic.FirstOrder.Basic.Formula

namespace LO

namespace FirstOrder

variable {L : Language.{u}} {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂}

@[ext] class Structure (L : Language.{u}) (M : Type w) where
  func : ⦃k : ℕ⦄ → L.func k → (Fin k → M) → M
  rel : ⦃k : ℕ⦄ → L.rel k → (Fin k → M) → Prop

namespace Structure

instance [Inhabited M] : Inhabited (Structure L M) := ⟨{ func := fun _ _ => default, rel := fun _ _ _ => True }⟩

structure Hom (L : Language.{u}) (M₁ : Type w₁) (M₂ : Type w₂) [s₁ : Structure L M₁] [s₂ : Structure L M₂] where
  toFun : M₁ → M₂
  func' : ∀ {k} (f : L.func k) (v : Fin k → M₁), toFun (s₁.func f v) = s₂.func f (toFun ∘ v)
  rel' : ∀ {k} (r : L.rel k) (v : Fin k → M₁), s₁.rel r v ↔ s₂.rel r (toFun ∘ v)

notation:25 M " →ₛ[" L "] " M' => Hom L M M'

namespace Hom

variable {M₁ : Type w₁} {M₂ : Type w₂} [s₁ : Structure L M₁] [s₂ : Structure L M₂] (φ : M₁ →ₛ[L] M₂)

instance : FunLike (M₁ →ₛ[L] M₂) M₁ (fun _ => M₂) where
  coe := fun φ => φ.toFun
  coe_injective' := fun φ ψ h => by rcases φ; rcases ψ; simp at h ⊢; ext; exact congr_fun h _

instance : CoeFun (M₁ →ₛ[L] M₂) (fun _ => M₁ → M₂) := FunLike.hasCoeToFun

@[ext] lemma ext (φ ψ : M₁ →ₛ[L] M₂) (h : ∀ x, φ x = ψ x) : φ = ψ := FunLike.ext φ ψ h

protected lemma func {k} (f : L.func k) (v : Fin k → M₁) :
    φ (s₁.func f v) = s₂.func f (φ ∘ v) := φ.func' f v

protected lemma rel {k} (r : L.rel k) (v : Fin k → M₁) :
    s₁.rel r v ↔ s₂.rel r (φ ∘ v) := φ.rel' r v

end Hom

class Inclusion (L : Language.{u}) (M₁ : Type w₁) (M₂ : Type w₂) [Structure L M₁] [Structure L M₂] extends M₁ →ₛ[L] M₂ where
  inj' : Function.Injective toFun

notation:25 M₁ " ⊆ₛ[" L "] " M₂ => Inclusion L M₁ M₂

@[ext] structure ClosedSubset (L : Language.{u}) (M : Type w) [s : Structure L M] where
  domain : Set M
  domain_closed : ∀ {k} (f : L.func k) {v : Fin k → M}, (∀ i, v i ∈ domain) → s.func f v ∈ domain

instance (M : Type w) [Structure L M] : SetLike (ClosedSubset L M) M := ⟨ClosedSubset.domain, ClosedSubset.ext⟩

protected def lMap (φ : L₁ →ᵥ L₂) {M : Type w} (S : Structure L₂ M) : Structure L₁ M where
  func := fun _ f => S.func (φ.func f)
  rel := fun _ r => S.rel (φ.rel r)

variable (φ : L₁ →ᵥ L₂) {M : Type w} (s₂ : Structure L₂ M)

@[simp] lemma lMap_func {k} {f : L₁.func k} {v : Fin k → M} : (s₂.lMap φ).func f v = s₂.func (φ.func f) v := rfl

@[simp] lemma lMap_rel {k} {r : L₁.rel k} {v : Fin k → M} : (s₂.lMap φ).rel r v ↔ s₂.rel (φ.rel r) v := of_eq rfl

def ofEquiv {M : Type w} [Structure L M] {N : Type w'} (φ : M ≃ N) : Structure L N where
  func := fun _ f v => φ (func f (φ.symm ∘ v))
  rel  := fun _ r v => rel r (φ.symm ∘ v)

protected abbrev Decidable (L : Language.{u}) (M : Type w) [s : Structure L M] :=
  {k : ℕ} → (r : L.rel k) → (v : Fin k → M) → Decidable (s.rel r v)

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

lemma val_func {k} (f : L.func k) (v) :
    val s e ε (func f v) = s.func f (fun i => (v i).val s e ε) := rfl

@[simp] lemma val_func₀ (f : L.func 0) (v) :
    val s e ε (func f v) = s.func f ![] := by simp[val_func, Matrix.empty_eq]

@[simp] lemma val_func₁ (f : L.func 1) (t) :
    val s e ε (func f ![t]) = s.func f ![t.val s e ε] :=
  by simp[val_func]; congr; funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma val_func₂ (f : L.func 2) (t u) :
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
  Subterm.val s ![] v o.term

lemma val_operator {k} (o : Operator L k) (v) :
    val s e ε (o.operator v) = o.val (fun x => (v x).val s e ε) := by
  simp[Operator.operator, val_rewrite, Operator.val]; congr; funext x; exact x.elim0

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

namespace ClosedSubset

variable {M : Type w} [s : Structure L M] (u : ClosedSubset L M)

lemma closed {k} (f : L.func k) {v : Fin k → M} (hv : ∀ i, v i ∈ u) : s.func f v ∈ u := u.domain_closed f hv

instance toStructure [s : Structure L M] (u : ClosedSubset L M) : Structure L u where
  func := fun k f v => ⟨s.func f (fun i => ↑(v i)), u.closed f (by simp)⟩
  rel := fun k r v => s.rel r (fun i => v i)

protected lemma func {k} (f : L.func k) (v : Fin k → u) : u.toStructure.func f v = s.func f (fun i => v i) := rfl

protected lemma rel {k} (r : L.rel k) (v : Fin k → u) : u.toStructure.rel r v ↔ s.rel r (fun i => v i) := of_eq rfl

end ClosedSubset

namespace Hom

variable {M₁ : Type w₁} {M₂ : Type w₂} [s₁ : Structure L M₁] [s₂ : Structure L M₂] (φ : M₁ →ₛ[L] M₂)

lemma val (e : Fin n → M₁) (ε : μ → M₁) (t : Subterm L μ n) :
    φ (t.val s₁ e ε) = t.val s₂ (φ ∘ e) (φ ∘ ε) := by
  induction t <;> simp[*, Subterm.val_func, Hom.func, Function.comp]

def inclusion [s : Structure L M] (u : ClosedSubset L M) : u ⊆ₛ[L] M where
  toFun := Subtype.val
  func' := by simp[ClosedSubset.func, Function.comp]
  rel' := by simp[ClosedSubset.rel, Function.comp]
  inj' := Subtype.val_injective

end Hom

section

variable [s : Structure L M] (φ : M ≃ N)

lemma ofEquiv_func (f : L.func k) (v : Fin k → N) :
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

abbrev BVal (s : Structure L M) (e : Fin n → M) : Subformula L Empty n →L Prop := Eval s e Empty.elim

abbrev Val! (M : Type w) [s : Structure L M] (ε : μ → M) :
    Formula L μ →L Prop := Val s ε

abbrev BVal! (M : Type w) [s : Structure L M] (e : Fin n → M) :
    Subformula L Empty n →L Prop := BVal s e

abbrev Realize (s : Structure L M) : Formula L M →L Prop := Eval s ![] id

lemma eval_rel {k} {r : L.rel k} {v} :
    Eval s e ε (rel r v) ↔ s.rel r (fun i => Subterm.val s e ε (v i)) := of_eq rfl

@[simp] lemma eval_rel₀ {r : L.rel 0} :
    Eval s e ε (rel r ![]) ↔ s.rel r ![] := by simp[eval_rel, Matrix.empty_eq]

@[simp] lemma eval_rel₁ {r : L.rel 1} (t : Subterm L μ n) :
    Eval s e ε (rel r ![t]) ↔ s.rel r ![t.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_rel₂ {r : L.rel 2} (t₁ t₂ : Subterm L μ n) :
    Eval s e ε (rel r ![t₁, t₂]) ↔ s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

lemma eval_nrel {k} {r : L.rel k} {v} :
    Eval s e ε (nrel r v) ↔ ¬s.rel r (fun i => Subterm.val s e ε (v i)) := of_eq rfl

@[simp] lemma eval_nrel₀ {r : L.rel 0} :
    Eval s e ε (nrel r ![]) ↔ ¬s.rel r ![] := by simp[eval_nrel, Matrix.empty_eq]

@[simp] lemma eval_nrel₁ {r : L.rel 1} (t : Subterm L μ n) :
    Eval s e ε (nrel r ![t]) ↔ ¬s.rel r ![t.val s e ε] := by
  simp[eval_nrel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_nrel₂ {r : L.rel 2} (t₁ t₂ : Subterm L μ n) :
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
  Subformula.Eval s ![] v o.sentence

@[simp] lemma val_operator_and {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.and o₂).val v ↔ o₁.val v ∧ o₂.val v := by simp[Operator.and, Operator.val]

@[simp] lemma val_operator_or {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.or o₂).val v ↔ o₁.val v ∨ o₂.val v := by simp[Operator.or, Operator.val]

lemma eval_operator {k} {o : Operator L k} {v : Fin k → Subterm L μ n} :
    Eval s e ε (o.operator v) ↔ o.val (fun i => (v i).val s e ε) := by
  simp[Operator.operator, eval_rewrite, Operator.val, Matrix.empty_eq]

@[simp] lemma eval_operator₀ {o : Const L} {v} :
    Eval s e ε (o.operator v) ↔ o.val (M := M) ![] := by
  simp[eval_operator, Matrix.empty_eq]

@[simp] lemma eval_operator₁ {o : Operator L 1} {t : Subterm L μ n} :
    Eval s e ε (o.operator ![t]) ↔ o.val ![t.val s e ε] := by
  simp[eval_operator, Matrix.constant_eq_singleton]

@[simp] lemma eval_operator₂ {o : Operator L 2} {t₁ t₂ : Subterm L μ n} :
    Eval s e ε (o.operator ![t₁, t₂]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_operator]; apply of_eq; congr; funext i; cases' i using Fin.cases with i <;> simp

section Hom
variable {M₁ : Type w₁} {M₂ : Type w₂} [s₁ : Structure L M₁] [s₂ : Structure L M₂] (φ : M₁ →ₛ[L] M₂)
variable {e₁ : Fin n → M₁} {ε₁ : μ → M₁}

lemma eval_hom_iff_of_qfree : ∀ {n} {e₁ : Fin n → M₁} {ε₁ : μ → M₁} {p : Subformula L μ n}, p.qfree →
    (Eval s₁ e₁ ε₁ p ↔ Eval s₂ (φ ∘ e₁) (φ ∘ ε₁) p)
  | _, e₁, ε₁, ⊤,        _ => by simp
  | _, e₁, ε₁, ⊥,        _ => by simp
  | _, e₁, ε₁, rel r v,  _ => by simp[Function.comp, eval_rel, φ.rel, φ.val]
  | _, e₁, ε₁, nrel r v, _ => by simp[Function.comp, eval_nrel, φ.rel r, φ.val]
  | _, e₁, ε₁, p ⋏ q,    h => by simp at h ⊢; simp[eval_hom_iff_of_qfree h.1, eval_hom_iff_of_qfree h.2]
  | _, e₁, ε₁, p ⋎ q,    h => by simp at h ⊢; simp[eval_hom_iff_of_qfree h.1, eval_hom_iff_of_qfree h.2]

lemma eval_hom_univClosure {n} {ε₁ : μ → M₁} {p : Subformula L μ n} (hp : p.qfree) :
    Val s₂ (φ ∘ ε₁) (univClosure p) → Val s₁ ε₁ (univClosure p) := by
  simp; intro h e₁; exact (eval_hom_iff_of_qfree φ hp).mpr (h (φ ∘ e₁))

end Hom

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

namespace Inclusion

variable {M₁ : Type w₁} [Structure L M₁] {M₂ : Type w₂} [Structure L M₂] (φ : M₁ ⊆ₛ[L] M₂)

lemma inj : Function.Injective (↑φ.toHom : M₁ → M₂) := φ.inj'
end Inclusion

section

open Subformula
variable [s : Structure L M] (φ : M ≃ N)

lemma ofEquiv_rel (r : L.rel k) (v : Fin k → N) :
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

class Theory.Mod (M : Type u) [Structure L M] (T : Theory L) :=
  modelsTheory : M ⊧* T

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

variable (L)

def ElementaryEquiv (M₁ M₂ : Type u) [Structure L M₁] [Structure L M₂] : Prop :=
  ∀ σ : Sentence L, M₁ ⊧ σ ↔ M₂ ⊧ σ

notation:50 M₁ " ≃ₑ[" L "] " M₂ => ElementaryEquiv L M₁ M₂

variable {L}

section
variable {M : Type u} [s : Structure L M]

lemma models_def : M ⊧ = Subformula.Val s Empty.elim := rfl

lemma models_iff {σ : Sentence L} : M ⊧ σ ↔ Subformula.Val s Empty.elim σ := by simp[models_def]

lemma models_def' : Semantics.models s = Subformula.Val s Empty.elim := rfl

lemma modelsTheory_iff {T : Theory L} : M ⊧* T ↔ (∀ ⦃p⦄, p ∈ T → M ⊧ p) := of_eq rfl

lemma models_iff_models {σ : Sentence L} :
    M ⊧ σ ↔ Semantics.models s σ := of_eq rfl

lemma consequence_iff {T : Theory L} {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Inhabited M] [Structure L M], M ⊧* T → M ⊧ σ) := of_eq rfl

lemma consequence_iff' {T : Theory L} {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Inhabited M] [Structure L M] [Theory.Mod M T], M ⊧ σ) :=
  ⟨fun h M _ _ _ => consequence_iff.mp h M Theory.Mod.modelsTheory,
   fun h M i s hs => @h M i s ⟨hs⟩⟩

lemma satisfiableₛ_iff {T : Theory L} :
    Semantics.Satisfiableₛ T ↔ ∃ (M : Type u) (_ : Inhabited M) (_ : Structure L M), M ⊧* T :=
  of_eq rfl

lemma satisfiableₛ_intro {T : Theory L} (M : Type u) [i : Inhabited M] [s : Structure L M] (h : M ⊧* T) :
    Semantics.Satisfiableₛ T := ⟨M, i, s, h⟩

lemma valid_iff {σ : Sentence L} :
    Semantics.Valid σ ↔ ∀ ⦃M : Type u⦄ [Inhabited M] [Structure L M], M ⊧ σ :=
  of_eq rfl

lemma validₛ_iff {T : Theory L} :
    Semantics.Validₛ T ↔ ∀ ⦃M : Type u⦄ [Inhabited M] [Structure L M], M ⊧* T :=
  of_eq rfl

namespace ElementaryEquiv

@[refl]
lemma refl (M) [Structure L M] : M ≃ₑ[L] M := fun σ => by rfl

@[symm]
lemma symm {M₁ M₂} [Structure L M₁] [Structure L M₂] : (M₁ ≃ₑ[L] M₂) → (M₂ ≃ₑ[L] M₁) :=
  fun h σ => (h σ).symm

@[trans]
lemma trans {M₁ M₂ M₃ : Type u} [Structure L M₁] [Structure L M₂] [Structure L M₃] :
    (M₁ ≃ₑ[L] M₂) → (M₂ ≃ₑ[L] M₃) → (M₁ ≃ₑ[L] M₃) :=
  fun h₁ h₂ σ => Iff.trans (h₁ σ) (h₂ σ)

lemma models {M₁ M₂} [Structure L M₁] [Structure L M₂] (h : M₁ ≃ₑ[L] M₂) :
    ∀ {σ : Sentence L}, M₁ ⊧ σ ↔ M₂ ⊧ σ := @h

lemma modelsTheory {M₁ M₂} [Structure L M₁] [Structure L M₂] (h : M₁ ≃ₑ[L] M₂) {T : Theory L} :
    M₁ ⊧* T ↔ M₂ ⊧* T := by simp[modelsTheory_iff, h.models]

end ElementaryEquiv

section Hom
variable {M₁ : Type u} {M₂ : Type u} [s₁ : Structure L M₁] [s₂ : Structure L M₂] (φ : M₁ →ₛ[L] M₂)
variable {e₁ : Fin n → M₁} {ε₁ : μ → M₁}

lemma models_hom_iff_of_qfree {σ : Sentence L} (hσ : σ.qfree) : M₁ ⊧ σ ↔ M₂ ⊧ σ := by
  simpa[Matrix.empty_eq, Empty.eq_elim] using
    Subformula.eval_hom_iff_of_qfree (e₁ := finZeroElim) (ε₁ := Empty.elim) φ hσ

lemma models_hom_univClosure {n} {σ : Subsentence L n} (hσ : σ.qfree) :
    M₂ ⊧ (univClosure σ) → M₁ ⊧ (univClosure σ) := by
  simpa[Matrix.empty_eq, Empty.eq_elim, models_iff] using
    Subformula.eval_hom_univClosure (ε₁ := Empty.elim) φ hσ

lemma models_hom_univClosure_of_submodels [H : M₁ ⊆ₛ[L] M₂] {n} {σ : Subsentence L n} (hσ : σ.qfree) :
    M₂ ⊧ (univClosure σ) → M₁ ⊧ (univClosure σ) := models_hom_univClosure H.toHom hσ

section

open Subformula
variable [s : Structure L M] (φ : M ≃ N)

lemma ElementaryEquiv.ofEquiv :
    letI : Structure L N := Structure.ofEquiv φ
    M ≃ₑ[L] N := fun σ => by
  letI : Structure L N := Structure.ofEquiv φ
  simp[models_iff, Empty.eq_elim, Structure.eval_ofEquiv_iff]

end

end Hom

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
  by simp[Subformula.models_lMap, Theory.lMap, modelsTheory_iff, modelsTheory_iff (T := T₁)]

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

variable (M : Type u) [Structure L M] { T : Theory L} [Theory.Mod M T]

lemma models {σ : Sentence L} (hσ : σ ∈ T) : M ⊧ σ :=
  modelsTheory_iff.mp Theory.Mod.modelsTheory hσ

lemma of_ss {T₁ T₂ : Theory L} [Theory.Mod M T₁] (ss : T₂ ⊆ T₁) : Theory.Mod M T₂ :=
  ⟨ModelsTheory.of_ss Mod.modelsTheory ss⟩

end Mod

end Theory

namespace Structure

structure Model (L : Language.{u}) (M : Type w) :=
  intro : M

namespace Model

variable [Structure L M]

def equiv (L : Language.{u}) (M : Type w) : M ≃ Model L M where
  toFun := fun x => ⟨x⟩
  invFun := Model.intro
  left_inv := by intro x; simp
  right_inv := by rintro ⟨x⟩; simp

instance : Structure L (Model L M) := Structure.ofEquiv (equiv L M)

instance [Inhabited M] : Inhabited (Model L M) := ⟨equiv L M default⟩

lemma elementaryEquiv (L : Language.{u}) (M : Type u) [Structure L M] : M ≃ₑ[L] Model L M := ElementaryEquiv.ofEquiv _

section

open Subterm Subformula

instance [Operator.Zero L] : Zero (Model L M) := ⟨(@Operator.Zero.zero L _).val ![]⟩

instance [Operator.Zero L] : Structure.Zero L (Model L M) := ⟨rfl⟩

instance [Operator.One L] : One (Model L M) := ⟨(@Operator.One.one L _).val ![]⟩

instance [Operator.One L] : Structure.One L (Model L M) := ⟨rfl⟩

instance [Operator.Add L] : Add (Model L M) :=
  ⟨fun x y => (@Operator.Add.add L _).val ![x, y]⟩

instance [Operator.Add L] : Structure.Add L (Model L M) := ⟨fun _ _ => rfl⟩

instance [Operator.Mul L] : Mul (Model L M) :=
  ⟨fun x y => (@Operator.Mul.mul L _).val ![x, y]⟩

instance [Operator.Mul L] : Structure.Mul L (Model L M) := ⟨fun _ _ => rfl⟩

instance [Operator.Eq L] [Structure.Eq L M] : Structure.Eq L (Model L M) :=
  ⟨fun x y => by simp[operator_val_ofEquiv_iff]⟩

instance [Operator.LT L] : LT (Model L M) :=
  ⟨fun x y => (@Operator.LT.lt L _).val ![x, y]⟩

instance [Operator.LT L] : Structure.LT L (Model L M) := ⟨fun _ _ => iff_of_eq rfl⟩

instance [Operator.Mem L] : Membership (Model L M) (Model L M) :=
  ⟨fun x y => (@Operator.Mem.mem L _).val ![x, y]⟩

instance [Operator.Mem L] : Structure.Mem L (Model L M) := ⟨fun _ _ => iff_of_eq rfl⟩

end

end Model

section ofFunc

variable (F : ℕ → Type*) {M : Type*} (fF : {k : ℕ} → (f : F k) → (Fin k → M) → M)

def ofFunc : Structure (Language.ofFunc F) M where
  func := fun _ f v => fF f v
  rel  := fun _ r _ => r.elim

lemma func_ofFunc {k} (f : F k) (v : Fin k → M) : (ofFunc F fF).func f v = fF f v := rfl

end ofFunc

section add

variable (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) (M : Type*) [str₁ : Structure L₁ M] [str₂ : Structure L₂ M]

instance add : Structure (L₁.add L₂) M where
  func := fun _ f v =>
    match f with
    | Sum.inl f => func f v
    | Sum.inr f => func f v
  rel := fun _ r v =>
    match r with
    | Sum.inl r => rel r v
    | Sum.inr r => rel r v

variable {L₁ L₂ M}

@[simp] lemma func_sigma_inl {k} (f : L₁.func k) (v : Fin k → M) : (add L₁ L₂ M).func (Sum.inl f) v = func f v := rfl

@[simp] lemma func_sigma_inr {k} (f : L₂.func k) (v : Fin k → M) : (add L₁ L₂ M).func (Sum.inr f) v = func f v := rfl

@[simp] lemma rel_sigma_inl {k} (r : L₁.rel k) (v : Fin k → M) : (add L₁ L₂ M).rel (Sum.inl r) v ↔ rel r v := iff_of_eq rfl

@[simp] lemma rel_sigma_inr {k} (r : L₂.rel k) (v : Fin k → M) : (add L₁ L₂ M).rel (Sum.inr r) v ↔ rel r v := iff_of_eq rfl

@[simp] lemma val_lMap_add₁ {n} (t : Subterm L₁ μ n) (e : Fin n → M) (ε : μ → M) :
    Subterm.val (add L₁ L₂ M) e ε (t.lMap (Language.Hom.add₁ L₁ L₂)) = t.val str₁ e ε := by
  induction t <;> simp[Subterm.val, *]

@[simp] lemma val_lMap_add₂ {n} (t : Subterm L₂ μ n) (e : Fin n → M) (ε : μ → M) :
    Subterm.val (add L₁ L₂ M) e ε (t.lMap (Language.Hom.add₂ L₁ L₂)) = t.val str₂ e ε := by
  induction t <;> simp[Subterm.val, *]

@[simp] lemma eval_lMap_add₁ {n} (p : Subformula L₁ μ n) (e : Fin n → M) (ε : μ → M) :
    Subformula.Eval (add L₁ L₂ M) e ε (Subformula.lMap (Language.Hom.add₁ L₁ L₂) p) ↔ Subformula.Eval str₁ e ε p := by
  induction p using Subformula.rec' <;>
    simp[*, Subformula.eval_rel, Subformula.lMap_rel, Subformula.eval_nrel, Subformula.lMap_nrel]

@[simp] lemma eval_lMap_add₂ {n} (p : Subformula L₂ μ n) (e : Fin n → M) (ε : μ → M) :
    Subformula.Eval (add L₁ L₂ M) e ε (Subformula.lMap (Language.Hom.add₂ L₁ L₂) p) ↔ Subformula.Eval str₂ e ε p := by
  induction p using Subformula.rec' <;>
    simp[*, Subformula.eval_rel, Subformula.lMap_rel, Subformula.eval_nrel, Subformula.lMap_nrel]

end add

section sigma

variable (L : ι → Language) (M : Type*) [str : (i : ι) → Structure (L i) M]

instance sigma : Structure (Language.sigma L) M where
  func := fun _ ⟨_, f⟩ v => func f v
  rel  := fun _ ⟨_, r⟩ v => rel r v

@[simp] lemma func_sigma {k} (f : (L i).func k) (v : Fin k → M) : (sigma L M).func ⟨i, f⟩ v = func f v := rfl

@[simp] lemma rel_sigma {k} (r : (L i).rel k) (v : Fin k → M) : (sigma L M).rel ⟨i, r⟩ v ↔ rel r v := iff_of_eq rfl

@[simp] lemma val_lMap_sigma {n} (t : Subterm (L i) μ n) (e : Fin n → M) (ε : μ → M) :
    Subterm.val (sigma L M) e ε (t.lMap (Language.Hom.sigma L i)) = t.val (str i) e ε := by
  induction t <;> simp[Subterm.val, *]

@[simp] lemma eval_lMap_sigma {n} (p : Subformula (L i) μ n) (e : Fin n → M) (ε : μ → M) :
    Subformula.Eval (sigma L M) e ε (Subformula.lMap (Language.Hom.sigma L i) p) ↔ Subformula.Eval (str i) e ε p := by
  induction p using Subformula.rec' <;>
    simp[*, Subformula.eval_rel, Subformula.lMap_rel, Subformula.eval_nrel, Subformula.lMap_nrel]

end sigma

end Structure


end FirstOrder

end LO
