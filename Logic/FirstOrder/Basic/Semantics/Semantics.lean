import Logic.Logic.Semantics
import Logic.FirstOrder.Basic.Syntax.Rew

/-!
# Semantics of first-order logic

This file defines the structure and the evaluation of terms and formulas by Tarski's truth definition.

-/

namespace LO

namespace FirstOrder

variable {L : Language.{u}} {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂}

@[ext] class Structure (L : Language.{u}) (M : Type w) where
  func : ⦃k : ℕ⦄ → L.Func k → (Fin k → M) → M
  rel : ⦃k : ℕ⦄ → L.Rel k → (Fin k → M) → Prop

structure Struc (L : Language) where
  Dom : Type*
  nonempty : Nonempty Dom
  struc : Structure L Dom

abbrev SmallStruc (L : Language.{u}) := Struc.{u, u} L

namespace Structure

instance [n : Nonempty M] : Nonempty (Structure L M) := by
  rcases n with ⟨x⟩
  exact ⟨{ func := fun _ _ _ => x, rel := fun _ _ _ => True }⟩

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

@[reducible] def toStruc [i : Nonempty M] (s : Structure L M) : Struc L := ⟨M, i, s⟩

end Structure

namespace Struc

instance (s : Struc L) : Nonempty s.Dom := s.nonempty

instance (s : Struc L) : Structure L s.Dom := s.struc

end Struc

namespace Semiterm

variable
  {M : Type w} {s : Structure L M}
  {e : Fin n → M} {e₁ : Fin n₁ → M} {e₂ : Fin n₂ → M}
  {ε : μ → M} {ε₁ : μ₁ → M} {ε₂ : μ₂ → M}

def val (s : Structure L M) (e : Fin n → M) (ε : μ → M) : Semiterm L μ n → M
  | #x       => e x
  | &x       => ε x
  | func f v => s.func f (fun i => (v i).val s e ε)

abbrev valb (s : Structure L M) (e : Fin n → M) (t : Semiterm L Empty n) : M := t.val s e Empty.elim

abbrev valm (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : μ → M) : Semiterm L μ n → M := val s e ε

abbrev valbm (M : Type w) [s : Structure L M] {n} (e : Fin n → M) : Semiterm L Empty n → M := valb s e

abbrev realize (s : Structure L M) (t : Term L M) : M := t.val s ![] id

@[simp] lemma val_bvar (x) : val s e ε (#x : Semiterm L μ n) = e x := rfl

@[simp] lemma val_fvar (x) : val s e ε (&x : Semiterm L μ n) = ε x := rfl

lemma val_func {k} (f : L.Func k) (v) :
    val s e ε (func f v) = s.func f (fun i => (v i).val s e ε) := rfl

@[simp] lemma val_func₀ (f : L.Func 0) (v) :
    val s e ε (func f v) = s.func f ![] := by simp [val_func, Matrix.empty_eq]

@[simp] lemma val_func₁ (f : L.Func 1) (t) :
    val s e ε (func f ![t]) = s.func f ![t.val s e ε] :=
  by simp [val_func]; congr; funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma val_func₂ (f : L.Func 2) (t u) :
    val s e ε (func f ![t, u]) = s.func f ![t.val s e ε, u.val s e ε] :=
  by simp [val_func]; congr; funext i; cases' i using Fin.cases with i <;> simp

lemma val_rew (ω : Rew L μ₁ n₁ μ₂ n₂) (t : Semiterm L μ₁ n₁) :
    (ω t).val s e₂ ε₂ = t.val s (val s e₂ ε₂ ∘ ω ∘ bvar) (val s e₂ ε₂ ∘ ω ∘ fvar) :=
  by induction t <;> simp [*, Rew.func, val_func]

lemma val_rewrite (f : μ₁ → Semiterm L μ₂ n) (t : Semiterm L μ₁ n) :
    (Rew.rewrite f t).val s e ε₂ = t.val s e (fun x => (f x).val s e ε₂) :=
  by simp [val_rew]; congr

lemma val_rewriteMap (f : μ₁ → μ₂) (t : Semiterm L μ₁ n) :
    (Rew.rewriteMap f t).val s e ε₂ = t.val s e (fun x => ε₂ (f x)) :=
  by simp [val_rew]; congr

lemma val_substs (w : Fin n₁ → Semiterm L μ n₂) (t : Semiterm L μ n₁) :
    (Rew.substs w t).val s e₂ ε = t.val s (fun x => (w x).val s e₂ ε) ε :=
  by simp [val_rew]; congr

@[simp] lemma val_bShift (a : M) (t : Semiterm L μ n) :
    (Rew.bShift t).val s (a :> e) ε = t.val s e ε := by simp [val_rew, Function.comp]

lemma val_bShift' (e : Fin (n + 1) → M) (t : Semiterm L μ n) :
    (Rew.bShift t).val s e ε = t.val s (e ·.succ) ε := by simp [val_rew, Function.comp]

@[simp] lemma val_emb {o : Type v'} [i : IsEmpty o] (t : Semiterm L o n) :
    (Rew.emb t : Semiterm L μ n).val s e ε = t.val s e i.elim := by
  simp [val_rew]; congr; { funext x; exact i.elim' x }

@[simp] lemma val_castLE (h : n₁ ≤ n₂) (t : Semiterm L μ n₁) :
    (Rew.castLE h t).val s e₂ ε = t.val s (fun x => e₂ (x.castLE h)) ε  := by
  simp [val_rew]; congr

lemma val_embSubsts (w : Fin k → Semiterm L μ n) (t : Semiterm L Empty k) :
    (Rew.embSubsts w t).val s e ε = t.valb s (fun x ↦ (w x).val s e ε) := by
  simp [val_rew, Empty.eq_elim]; congr

@[simp] lemma val_toS {e : Fin n → M} (t : Semiterm L (Fin n) 0) :
    valb s e (Rew.toS t) = val s ![] e t := by
  simp [val_rew, Matrix.empty_eq]; congr

@[simp] lemma val_toF {e : Fin n → M} (t : Semiterm L Empty n) :
    val s ![] e (Rew.toF t) = valb s e t := by
  simp [val_rew, Matrix.empty_eq]; congr
  funext i; simp; contradiction

section Language

variable (φ : L₁ →ᵥ L₂) (e : Fin n → M) (ε : μ → M)

lemma val_lMap (φ : L₁ →ᵥ L₂) (s₂ : Structure L₂ M) (e : Fin n → M) (ε : μ → M) {t : Semiterm L₁ μ n} :
    (t.lMap φ).val s₂ e ε = t.val (s₂.lMap φ) e ε :=
  by induction t <;> simp [*, valm, Function.comp, val_func, Semiterm.lMap_func]

end Language

section Syntactic

variable (ε : ℕ → M)

lemma val_shift (t : SyntacticSemiterm L n) :
    (Rew.shift t).val s e ε = t.val s e (ε ∘ Nat.succ) := by simp [val_rew]; congr

lemma val_free (a : M) (t : SyntacticSemiterm L (n + 1)) :
    (Rew.free t).val s e (a :>ₙ ε) = t.val s (e <: a) ε :=
  by simp [val_rew]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma val_fix (a : M) (t : SyntacticSemiterm L n) :
    (Rew.fix t).val s (e <: a) ε = t.val s e (a :>ₙ ε) :=
  by simp [val_rew]; congr <;> simp [Function.comp]; exact funext (Nat.cases (by simp) (by simp))

end Syntactic

lemma val_eq_of_funEqOn (t : Semiterm L μ n) (h : Function.funEqOn t.fvar? ε ε') :
    val s e ε t = val s e ε' t := by
  induction t <;> simp [val_func]
  case fvar x => exact h x (by simp [fvar?])
  case func k f v ih =>
    congr; funext i; exact ih i (by intro x hx; exact h x (by simp; exact ⟨i, hx⟩))

end Semiterm

namespace Structure

section

variable [s : Structure L M] (φ : M ≃ N)

lemma ofEquiv_func (f : L.Func k) (v : Fin k → N) :
    (ofEquiv φ).func f v = φ (func f (φ.symm ∘ v)) := rfl

lemma ofEquiv_val (e : Fin n → N) (ε : μ → N) (t : Semiterm L μ n) :
    t.val (ofEquiv φ) e ε = φ (t.val s (φ.symm ∘ e) (φ.symm ∘ ε)) := by
  induction t <;> simp [*, Semiterm.val_func, ofEquiv_func φ, Function.comp]

end

end Structure

namespace Semiformula

variable {M : Type w} {s : Structure L M}
variable {n : ℕ} {e : Fin n → M} {e₂ : Fin n₂ → M} {ε : μ → M} {ε₂ : μ₂ → M}

def EvalAux (s : Structure L M) (ε : μ → M) : ∀ {n}, (Fin n → M) → Semiformula L μ n → Prop
  | _, _, ⊤        => True
  | _, _, ⊥        => False
  | _, e, rel p v  => s.rel p (fun i => Semiterm.val s e ε (v i))
  | _, e, nrel p v => ¬s.rel p (fun i => Semiterm.val s e ε (v i))
  | _, e, p ⋏ q    => p.EvalAux s ε e ∧ q.EvalAux s ε e
  | _, e, p ⋎ q    => p.EvalAux s ε e ∨ q.EvalAux s ε e
  | _, e, ∀' p     => ∀ x : M, (p.EvalAux s ε (x :> e))
  | _, e, ∃' p     => ∃ x : M, (p.EvalAux s ε (x :> e))

@[simp] lemma EvalAux_neg (p : Semiformula L μ n) :
    EvalAux s ε e (~p) = ¬EvalAux s ε e p :=
  by induction p using rec' <;> simp [*, EvalAux, ←neg_eq, or_iff_not_imp_left]

def Eval (s : Structure L M) (e : Fin n → M) (ε : μ → M) : Semiformula L μ n →ˡᶜ Prop where
  toTr := EvalAux s ε e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp [EvalAux]
  map_or' := by simp [EvalAux]
  map_neg' := by simp [EvalAux_neg]
  map_imply' := by simp [imp_eq, EvalAux_neg, ←neg_eq, EvalAux, imp_iff_not_or]

abbrev Evalm (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : μ → M) :
    Semiformula L μ n →ˡᶜ Prop := Eval s e ε

abbrev Evalf (s : Structure L M) (ε : μ → M) : Formula L μ →ˡᶜ Prop := Eval s ![] ε

abbrev Evalb (s : Structure L M) (e : Fin n → M) : Semisentence L n →ˡᶜ Prop := Eval s e Empty.elim

abbrev Evalfm (M : Type w) [s : Structure L M] (ε : μ → M) :
    Formula L μ →ˡᶜ Prop := Evalf s ε

abbrev Evalbm (M : Type w) [s : Structure L M] (e : Fin n → M) :
    Semiformula L Empty n →ˡᶜ Prop := Evalb s e

abbrev Realize (s : Structure L M) : Formula L M →ˡᶜ Prop := Eval s ![] id

lemma eval_rel {k} {r : L.Rel k} {v} :
    Eval s e ε (rel r v) ↔ s.rel r (fun i => Semiterm.val s e ε (v i)) := of_eq rfl

lemma Eval.of_eq {e e' : Fin n → M} {ε ε' : μ → M} {p} (h : Eval s e ε p) (he : e = e') (hε : ε = ε') : Eval s e' ε' p := he ▸ hε ▸ h

@[simp] lemma eval_rel₀ {r : L.Rel 0} :
    Eval s e ε (rel r ![]) ↔ s.rel r ![] := by simp [eval_rel, Matrix.empty_eq]

@[simp] lemma eval_rel₁ {r : L.Rel 1} (t : Semiterm L μ n) :
    Eval s e ε (rel r ![t]) ↔ s.rel r ![t.val s e ε] := by
  simp [eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_rel₂ {r : L.Rel 2} (t₁ t₂ : Semiterm L μ n) :
    Eval s e ε (rel r ![t₁, t₂]) ↔ s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp [eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

lemma eval_nrel {k} {r : L.Rel k} {v} :
    Eval s e ε (nrel r v) ↔ ¬s.rel r (fun i => Semiterm.val s e ε (v i)) := of_eq rfl

@[simp] lemma eval_nrel₀ {r : L.Rel 0} :
    Eval s e ε (nrel r ![]) ↔ ¬s.rel r ![] := by simp [eval_nrel, Matrix.empty_eq]

@[simp] lemma eval_nrel₁ {r : L.Rel 1} (t : Semiterm L μ n) :
    Eval s e ε (nrel r ![t]) ↔ ¬s.rel r ![t.val s e ε] := by
  simp [eval_nrel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_nrel₂ {r : L.Rel 2} (t₁ t₂ : Semiterm L μ n) :
    Eval s e ε (nrel r ![t₁, t₂]) ↔ ¬s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp [eval_nrel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_all {p : Semiformula L μ (n + 1)} :
    Eval s e ε (∀' p) ↔ ∀ x : M, Eval s (x :> e) ε p := of_eq rfl

@[simp] lemma eval_ex {p : Semiformula L μ (n + 1)} :
    Eval s e ε (∃' p) ↔ ∃ x : M, Eval s (x :> e) ε p := of_eq rfl

@[simp] lemma eval_ball {p q : Semiformula L μ (n + 1)} :
    Eval s e ε (∀[p] q) ↔ ∀ x : M, Eval s (x :> e) ε p → Eval s (x :> e) ε q := by
  simp [LogicalConnective.ball]

@[simp] lemma eval_bex {p q : Semiformula L μ (n + 1)} :
    Eval s e ε (∃[p] q) ↔ ∃ x : M, Eval s (x :> e) ε p ⋏ Eval s (x :> e) ε q := by
  simp [LogicalConnective.bex]

@[simp] lemma eval_univClosure {e'} {p : Semiformula L μ n'} :
    Eval s e' ε (∀* p) ↔ ∀ e, Eval s e ε p := by
  induction' n' with n' ih generalizing e' <;> simp [*, eq_finZeroElim, univClosure_succ]
  constructor
  · intro h e; simpa using h (Matrix.vecTail e) (Matrix.vecHead e)
  · intro h e x; exact h (x :> e)

@[simp] lemma eval_exClosure {e'} {p : Semiformula L μ n'} :
    Eval s e' ε (∃* p) ↔ ∃ e, Eval s e ε p := by
  induction' n' with n' ih generalizing e' <;> simp [*, eq_finZeroElim, exClosure_succ]
  constructor
  · rintro ⟨e, x, h⟩; exact ⟨x :> e, h⟩
  · rintro ⟨e, h⟩; exact ⟨Matrix.vecTail e, Matrix.vecHead e, by simpa using h⟩

@[simp] lemma eval_univItr {k} {e} {p : Semiformula L μ (n + k)} :
    Eval s e ε (∀^[k] p) ↔ ∀ e', Eval s (Matrix.appendr e' e) ε p := by
  induction' k with k ih generalizing e <;> simp [*, Matrix.empty_eq, univItr_succ]
  constructor
  · intro h e'
    exact Eval.of_eq (h (Matrix.vecTail e') (Matrix.vecHead e'))
      (by rw [←Matrix.appendr_cons, Matrix.cons_head_tail]) rfl
  · intro h e' x; simpa using h (x :> e')

@[simp] lemma eval_exItr {k} {e} {p : Semiformula L μ (n + k)} :
    Eval s e ε (∃^[k] p) ↔ ∃ e', Eval s (Matrix.appendr e' e) ε p := by
  induction' k with k ih generalizing e <;> simp [*, Matrix.empty_eq, exItr_succ]
  constructor
  · rintro ⟨e', x, h⟩
    exact ⟨x :> e', by simpa using h⟩
  · rintro ⟨e, h⟩
    exact ⟨Matrix.vecTail e, Matrix.vecHead e,
      by rw [←Matrix.appendr_cons, Matrix.cons_head_tail]; exact h⟩

lemma eval_rew (ω : Rew L μ₁ n₁ μ₂ n₂) (p : Semiformula L μ₁ n₁) :
    Eval s e₂ ε₂ (ω.hom p) ↔ Eval s (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.bvar) (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.fvar) p := by
  induction p using rec' generalizing n₂ <;> simp [*, Semiterm.val_rew, eval_rel, eval_nrel, Rew.rel, Rew.nrel]
  case hall => simp [Function.comp]; exact iff_of_eq $ forall_congr (fun x => by congr; funext i; cases i using Fin.cases <;> simp)
  case hex => simp [Function.comp]; exact exists_congr (fun x => iff_of_eq $ by congr; funext i; cases i using Fin.cases <;> simp)

lemma eval_rew_q {x e₂ ε₂} (ω : Rew L μ₁ n₁ μ₂ n₂) (p : Semiformula L μ₁ (n₁ + 1)) :
    Eval s (x :> e₂) ε₂ (ω.q.hom p) ↔
    Eval s
      (x :> Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.bvar)
      (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.fvar) p := by
  simp [eval_rew, Function.comp]
  apply iff_of_eq; congr 2
  · funext x
    cases x using Fin.cases <;> simp

lemma eval_map (b : Fin n₁ → Fin n₂) (f : μ₁ → μ₂) (e : Fin n₂ → M) (ε : μ₂ → M) (p : Semiformula L μ₁ n₁) :
    Eval s e ε ((Rew.map b f).hom p) ↔ Eval s (e ∘ b) (ε ∘ f) p :=
  by simp [eval_rew, Function.comp]

lemma eval_rewrite (f : μ₁ → Semiterm L μ₂ n) (p : Semiformula L μ₁ n) :
    Eval s e ε₂ ((Rew.rewrite f).hom p) ↔ Eval s e (fun x => (f x).val s e ε₂) p :=
  by simp [eval_rew, Function.comp]

lemma eval_rewriteMap (f : μ₁ → μ₂) (p : Semiformula L μ₁ n) :
    Eval s e ε₂ ((Rew.rewriteMap f).hom p) ↔ Eval s e (fun x => ε₂ (f x)) p :=
  by simp [eval_rew, Function.comp]

@[simp] lemma eval_castLE (h : n₁ ≤ n₂) (p : Semiformula L μ n₁) :
    Eval s e₂ ε ((Rew.castLE h).hom p) ↔ Eval s (fun x => e₂ (x.castLE h)) ε p := by
  simp [eval_rew, Function.comp]

@[simp] lemma eval_bShift (p : Semiformula L μ n) :
    Eval s (x :> e) ε (Rew.bShift.hom p) ↔ Eval s e ε p :=
  by simp [eval_rew, Function.comp]

lemma eval_bShift' (p : Semiformula L μ n) :
    Eval s e' ε (Rew.bShift.hom p) ↔ Eval s (e' ·.succ) ε p :=
  by simp [eval_rew, Function.comp]

lemma eval_substs {k} (w : Fin k → Semiterm L μ n) (p : Semiformula L μ k) :
    Eval s e ε ((Rew.substs w).hom p) ↔ Eval s (fun i => (w i).val s e ε) ε p :=
  by simp [eval_rew, Function.comp]

@[simp] lemma eval_emb (p : Semiformula L Empty n) :
    Eval s e ε (Rew.emb.hom p) ↔ Eval s e Empty.elim p := by
  simp [eval_rew, Function.comp]; apply iff_of_eq; congr; funext x; contradiction

@[simp] lemma eval_empty [h : IsEmpty o] (p : Formula L o) :
    Eval s e ε (Rew.empty.hom p) ↔ Eval s ![] h.elim p := by
  simp [eval_rew, Function.comp, Matrix.empty_eq]
  apply iff_of_eq; congr; funext x; exact h.elim' x

@[simp] lemma eval_toS {e : Fin n → M} {ε} (p : Formula L (Fin n)) :
    Eval s e ε (Rew.toS.hom p) ↔ Eval s ![] e p := by
  simp [Rew.toS, eval_rew, Function.comp, Matrix.empty_eq]

lemma eval_embSubsts {k} (w : Fin k → Semiterm L μ n) (σ : Semisentence L k) :
    Eval s e ε ((Rew.embSubsts w).hom σ) ↔ Evalb s (fun x ↦ (w x).val s e ε) σ := by
  simp [eval_rew, Function.comp, Empty.eq_elim]

section Syntactic

variable (ε : ℕ → M)

@[simp] lemma eval_free (p : SyntacticSemiformula L (n + 1)) :
    Eval s e (a :>ₙ ε) (Rew.free.hom p) ↔ Eval s (e <: a) ε p :=
  by simp [eval_rew, Function.comp]; congr; apply iff_of_eq; congr; funext x; cases x using Fin.lastCases <;> simp

@[simp] lemma eval_shift (p : SyntacticSemiformula L n) :
    Eval s e (a :>ₙ ε) (Rew.shift.hom p) ↔ Eval s e ε p :=
  by simp [eval_rew, Function.comp]

end Syntactic

lemma eval_iff_of_funEqOn (p : Semiformula L μ n) (h : Function.funEqOn (fvar? p) ε ε') :
    Eval s e ε p ↔ Eval s e ε' p := by
  unfold fvar? at h
  induction p using Semiformula.rec'
  case hverum => simp
  case hfalsum => simp
  case hrel k r v =>
    simp [eval_rel]; apply iff_of_eq; congr
    funext i
    exact Semiterm.val_eq_of_funEqOn (v i) (fun x hx ↦ h x (by simp [fvarList]; exact ⟨i, hx⟩))
  case hnrel k r v =>
    simp [eval_nrel]; apply iff_of_eq; congr
    funext i
    exact Semiterm.val_eq_of_funEqOn (v i) (fun x hx ↦ h x (by simp [fvarList]; exact ⟨i, hx⟩))
  case hand p q ihp ihq =>
    simp; apply and_congr
    · exact ihp (fun x (hx : x ∈ p.fvarList) ↦ h x $ by simp [hx, fvarList])
    · exact ihq (fun x (hx : x ∈ q.fvarList) ↦ h x $ by simp [hx, fvarList])
  case hor p q ihp ihq =>
    simp; apply or_congr
    · exact ihp (fun x (hx : x ∈ p.fvarList) ↦ h x $ by simp [hx, fvarList])
    · exact ihq (fun x (hx : x ∈ q.fvarList) ↦ h x $ by simp [hx, fvarList])
  case hall p ih =>
    simp; apply forall_congr'; intro x
    exact ih (fun x hx ↦ h _ $ by simp [fvar?]; exact hx)
  case hex p ih =>
    simp; apply exists_congr; intro x
    exact ih (fun x hx ↦ h _ $ by simp [fvar?]; exact hx)

lemma val_fvUnivClosure_inhabited [h : Nonempty μ] [DecidableEq μ] {p : Formula L μ} :
    Evalf s Empty.elim (∀ᶠ* p) ↔ ∀ ε, Evalf s ε p := by
  simp [Formula.fvUnivClosure, eval_rewriteMap]
  haveI : Inhabited μ := ⟨Classical.ofNonempty⟩
  constructor
  · intro h ε
    have := h (fun i ↦ ε $ Semiformula.fvListingInv _ i)
    exact (eval_iff_of_funEqOn p (by intro x hx; simp [fvListingInv_fvListing hx])).mp this
  · intro h e
    exact h (fun x ↦ e $ Semiformula.fvListing p x)

@[simp] lemma val_fvUnivClosure [Nonempty M] [DecidableEq μ] {p : Formula L μ} :
    Evalf s Empty.elim (∀ᶠ* p) ↔ ∀ ε, Evalf s ε p := by
  by_cases hμ : Nonempty μ
  · exact val_fvUnivClosure_inhabited
  · haveI hμ : IsEmpty μ := not_nonempty_iff.mp hμ
    simp [Formula.fvUnivClosure_sentence p, IsEmpty.eq_elim]
    simp [Matrix.empty_eq]

end Semiformula

namespace Structure

section

open Semiformula
variable [s : Structure L M] (φ : M ≃ N)

lemma ofEquiv_rel (r : L.Rel k) (v : Fin k → N) :
    (Structure.ofEquiv φ).rel r v ↔ Structure.rel r (φ.symm ∘ v) := iff_of_eq rfl

lemma eval_ofEquiv_iff : ∀ {n} {e : Fin n → N} {ε : μ → N} {p : Semiformula L μ n},
    (Eval (ofEquiv φ) e ε p ↔ Eval s (φ.symm ∘ e) (φ.symm ∘ ε) p)
  | _, e, ε, ⊤         => by simp
  | _, e, ε, ⊥         => by simp
  | _, e, ε, .rel r v  => by simp [Function.comp, eval_rel, ofEquiv_rel φ, Structure.ofEquiv_val φ]
  | _, e, ε, .nrel r v => by simp [Function.comp, eval_nrel, ofEquiv_rel φ, Structure.ofEquiv_val φ]
  | _, e, ε, p ⋏ q     => by simp [eval_ofEquiv_iff (p := p), eval_ofEquiv_iff (p := q)]
  | _, e, ε, p ⋎ q     => by simp [eval_ofEquiv_iff (p := p), eval_ofEquiv_iff (p := q)]
  | _, e, ε, ∀' p      => by
    simp; exact
    ⟨fun h x => by simpa[Matrix.comp_vecCons''] using eval_ofEquiv_iff.mp (h (φ x)),
     fun h x => eval_ofEquiv_iff.mpr (by simpa[Matrix.comp_vecCons''] using h (φ.symm x))⟩
  | _, e, ε, ∃' p      => by
    simp; exact
    ⟨by rintro ⟨x, h⟩; exists φ.symm x; simpa[Matrix.comp_vecCons''] using eval_ofEquiv_iff.mp h,
     by rintro ⟨x, h⟩; exists φ x; apply eval_ofEquiv_iff.mpr; simpa[Matrix.comp_vecCons''] using h⟩

end

end Structure

instance semantics : Semantics (Sentence L) (Struc L) where
  Realize := fun str ↦ Semiformula.Evalf str.struc Empty.elim

instance : Semantics.Tarski (Struc L) where
  realize_top := by simp [Semantics.Realize]
  realize_bot := by simp [Semantics.Realize]
  realize_not := by simp [Semantics.Realize]
  realize_and := by simp [Semantics.Realize]
  realize_or := by simp [Semantics.Realize]
  realize_imp := by simp [Semantics.Realize]

section

variable (M : Type*) [Nonempty M] [s : Structure L M] {T U : Theory L}

abbrev Models : Sentence L → Prop := Semantics.Realize s.toStruc

infix:45 " ⊧ₘ " => Models

abbrev ModelsTheory (T : Theory L) : Prop :=
  Semantics.RealizeSet s.toStruc T

infix:45 " ⊧ₘ* " => ModelsTheory

abbrev Realize (M : Type*) [s : Structure L M] : Formula L M → Prop := Semiformula.Evalf s id

infix:45 " ⊧ₘᵣ " => Realize

abbrev Consequence (T : Theory L) (σ : Sentence L) : Prop := T ⊨[SmallStruc L] σ

infix:45 " ⊨ " => Consequence

abbrev Satisfiable (T : Theory L) : Prop := Semantics.Satisfiable (SmallStruc L) T

variable {M}

def modelsTheory_iff_modelsTheory_s : M ⊧ₘ* T ↔ s.toStruc ⊧* T := by rfl

lemma models_def {f} : (M ⊧ₘ f) = Semiformula.Evalf s Empty.elim f := rfl

lemma models_iff {σ : Sentence L} : M ⊧ₘ σ ↔ Semiformula.Evalf s Empty.elim σ := by simp [models_def]

lemma models_def' : Semantics.Realize s.toStruc = Semiformula.Evalf s Empty.elim := rfl

lemma modelsTheory_iff : M ⊧ₘ* T ↔ (∀ {p}, p ∈ T → M ⊧ₘ p) := Semantics.realizeSet_iff

lemma models_iff_models {σ : Sentence L} :
    M ⊧ₘ σ ↔ s.toStruc ⊧ σ := of_eq rfl

lemma consequence_iff {σ : Sentence L} :
    T ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M], M ⊧ₘ* T → M ⊧ₘ σ) :=
  ⟨fun h _ _ _ hT ↦ h hT, fun h s hT ↦ h s.Dom hT⟩

lemma consequence_iff' {σ : Sentence L} :
    T ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [M ⊧ₘ* T], M ⊧ₘ σ) :=
  ⟨fun h _ _ s _ => Semantics.consequence_iff'.mp h s.toStruc,
   fun h s hs => @h s.Dom s.nonempty s.struc hs⟩

lemma valid_iff {σ : Sentence L} :
    Semantics.Valid (Struc.{v, u} L) σ ↔ ∀ (M : Type v) [Nonempty M] [Structure L M], M ⊧ₘ σ :=
  ⟨fun hσ _ _ s ↦ @hσ s.toStruc, fun h s ↦ h s.Dom⟩

lemma satisfiable_iff :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔ ∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M), M ⊧ₘ* T :=
  ⟨by rintro ⟨s, hs⟩; exact ⟨s.Dom, s.nonempty, s.struc, hs⟩, by rintro ⟨M, i, s, hT⟩; exact ⟨s.toStruc, hT⟩⟩

lemma satisfiable_intro (M : Type v) [Nonempty M] [s : Structure L M] (h : M ⊧ₘ* T) :
    Semantics.Satisfiable (Struc.{v, u} L) T := ⟨s.toStruc, h⟩

noncomputable def ModelOfSat (h : Semantics.Satisfiable (Struc.{v, u} L) T) : Type v :=
  Classical.choose (satisfiable_iff.mp h)

noncomputable instance nonemptyModelOfSat (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    Nonempty (ModelOfSat h) := by
  choose i _ _ using Classical.choose_spec (satisfiable_iff.mp h); exact i

noncomputable def StructureModelOfSatAux (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    { s : Structure L (ModelOfSat h) // ModelOfSat h ⊧ₘ* T } := by
  choose _ s h using Classical.choose_spec (satisfiable_iff.mp h)
  exact ⟨s, h⟩

noncomputable instance StructureModelOfSat (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    Structure L (ModelOfSat h) := StructureModelOfSatAux h

lemma ModelOfSat.models (h : Semantics.Satisfiable (Struc.{v, u} L) T) : ModelOfSat h ⊧ₘ* T := (StructureModelOfSatAux h).prop

end

namespace Semiformula

variable {L₁ L₂ : Language} {Φ : L₁ →ᵥ L₂}

section lMap
variable {M : Type u} [Nonempty M] {s₂ : Structure L₂ M} {n} {e : Fin n → M} {ε : μ → M}

lemma eval_lMap {p : Semiformula L₁ μ n} :
    Eval s₂ e ε (lMap Φ p) ↔ Eval (s₂.lMap Φ) e ε p :=
  by induction p using rec' <;>
    simp [*, Semiterm.val_lMap, lMap_rel, lMap_nrel, eval_rel, eval_nrel]

lemma models_lMap {σ : Sentence L₁} :
    s₂.toStruc ⊧ lMap Φ σ ↔ (s₂.lMap Φ).toStruc ⊧ σ :=
  by simp [Semantics.Realize, Evalf, eval_lMap]

end lMap

end Semiformula

lemma lMap_models_lMap {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂}  {T : Theory L₁} {σ : Sentence L₁} (h : T ⊨[Struc.{v, u} L₁] σ) :
    T.lMap Φ ⊨[Struc.{v, u} L₂] Semiformula.lMap Φ σ := by
  intro s hM
  have : (s.struc.lMap Φ).toStruc ⊧ σ :=
    h ⟨fun _ hq => Semiformula.models_lMap.mp <| hM.realize (Set.mem_image_of_mem _ hq)⟩
  exact Semiformula.models_lMap.mpr this

namespace ModelsTheory

variable (M) [Nonempty M] [Structure L M]

lemma models {T : Theory L} [M ⊧ₘ* T] {p} (h : p ∈ T) : M ⊧ₘ p := Semantics.RealizeSet.realize _ h

variable {M}

lemma of_ss {T U : Theory L} (h : M ⊧ₘ* U) (ss : T ⊆ U) : M ⊧ₘ* T :=
  Semantics.RealizeSet.of_subset h ss

@[simp] lemma add_iff {T U : Theory L} :
    M ⊧ₘ* T + U ↔ M ⊧ₘ* T ∧ M ⊧ₘ* U := by simp [Theory.add_def]

instance add (T U : Theory L) [M ⊧ₘ* T] [M ⊧ₘ* U] : M ⊧ₘ* T + U :=
  ModelsTheory.add_iff.mpr ⟨inferInstance, inferInstance⟩

end ModelsTheory

namespace Theory

variable {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂}

variable {M : Type u} [Nonempty M] [s₂ : Structure L₂ M]

lemma modelsTheory_onTheory₁ {T₁ : Theory L₁} :
    ModelsTheory (s := s₂) (T₁.lMap Φ) ↔ ModelsTheory (s := s₂.lMap Φ) T₁ :=
  by simp [Semiformula.models_lMap, Theory.lMap, modelsTheory_iff, @modelsTheory_iff (T := T₁)]

end Theory

namespace Structure

variable (L)

abbrev theory (M : Type u) [Nonempty M] [s : Structure L M] : Theory L := Semantics.theory s.toStruc

variable {L} {M : Type u} [Nonempty M] [Structure L M]

@[simp] lemma mem_theory_iff {σ} : σ ∈ theory L M ↔ M ⊧ₘ σ := by rfl

lemma subset_of_models : T ⊆ theory L M ↔ M ⊧ₘ* T := ⟨fun h  ↦ ⟨fun _ hσ ↦ h hσ⟩, fun h _ hσ ↦ h.RealizeSet hσ⟩

end Structure

end FirstOrder

end LO
