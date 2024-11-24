import Foundation.FirstOrder.Basic.Syntax.Rew

/-!
# Semantics of first-order logic

This file defines the structure and the evaluation of terms and formulas by Tarski's truth definition.

-/

namespace LO

namespace FirstOrder

variable {L : Language.{u}}

@[ext] class Structure (L : Language.{u}) (M : Type w) where
  func : ⦃k : ℕ⦄ → L.Func k → (Fin k → M) → M
  rel : ⦃k : ℕ⦄ → L.Rel k → (Fin k → M) → Prop

structure Struc (L : Language) where
  Dom : Type*
  nonempty : Nonempty Dom
  struc : Structure L Dom

abbrev SmallStruc (L : Language.{u}) := Struc.{u, u} L

instance : CoeSort (Struc L) (Type _) := ⟨Struc.Dom⟩

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

def ofEquiv {M : Type w} [Structure L M] {N : Type w'} (Θ : M ≃ N) : Structure L N where
  func := fun _ f v => Θ (func f (Θ.symm ∘ v))
  rel  := fun _ r v => rel r (Θ.symm ∘ v)

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
  {ε : ξ → M} {ε₁ : μ₁ → M} {ε₂ : μ₂ → M}

def val (s : Structure L M) (e : Fin n → M) (ε : ξ → M) : Semiterm L ξ n → M
  | #x       => e x
  | &x       => ε x
  | func f v => s.func f (fun i => (v i).val s e ε)

abbrev valb (s : Structure L M) (e : Fin n → M) (t : Semiterm L Empty n) : M := t.val s e Empty.elim

abbrev valm (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : ξ → M) : Semiterm L ξ n → M := val s e ε

abbrev valbm (M : Type w) [s : Structure L M] {n} (e : Fin n → M) : Semiterm L Empty n → M := valb s e

abbrev realize (s : Structure L M) (t : Term L M) : M := t.val s ![] id

@[simp] lemma val_bvar (x) : val s e ε (#x : Semiterm L ξ n) = e x := rfl

@[simp] lemma val_fvar (x) : val s e ε (&x : Semiterm L ξ n) = ε x := rfl

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

lemma val_substs (w : Fin n₁ → Semiterm L ξ n₂) (t : Semiterm L ξ n₁) :
    (Rew.substs w t).val s e₂ ε = t.val s (fun x => (w x).val s e₂ ε) ε :=
  by simp [val_rew]; congr

@[simp] lemma val_bShift (a : M) (t : Semiterm L ξ n) :
    (Rew.bShift t).val s (a :> e) ε = t.val s e ε := by simp [val_rew, Function.comp_def]

lemma val_bShift' (e : Fin (n + 1) → M) (t : Semiterm L ξ n) :
    (Rew.bShift t).val s e ε = t.val s (e ·.succ) ε := by simp [val_rew, Function.comp_def]

@[simp] lemma val_emb {o : Type v'} [i : IsEmpty o] (t : Semiterm L o n) :
    (Rew.emb t : Semiterm L ξ n).val s e ε = t.val s e i.elim := by
  simp [val_rew]; congr; { funext x; exact i.elim' x }

@[simp] lemma val_castLE (h : n₁ ≤ n₂) (t : Semiterm L ξ n₁) :
    (Rew.castLE h t).val s e₂ ε = t.val s (fun x => e₂ (x.castLE h)) ε  := by
  simp [val_rew]; congr

lemma val_embSubsts (w : Fin k → Semiterm L ξ n) (t : Semiterm L Empty k) :
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

variable (φ : L₁ →ᵥ L₂) (e : Fin n → M) (ε : ξ → M)

lemma val_lMap (φ : L₁ →ᵥ L₂) (s₂ : Structure L₂ M) (e : Fin n → M) (ε : ξ → M) {t : Semiterm L₁ ξ n} :
    (t.lMap φ).val s₂ e ε = t.val (s₂.lMap φ) e ε :=
  by induction t <;> simp [*, valm, Function.comp_def, val_func, Semiterm.lMap_func]

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
  by simp [val_rew]; congr <;> simp [Function.comp_def]; exact funext (Nat.cases (by simp) (by simp))

end Syntactic

lemma val_eq_of_funEqOn [DecidableEq ξ] (t : Semiterm L ξ n) (h : Function.funEqOn t.FVar? ε ε') :
    val s e ε t = val s e ε' t := by
  induction t <;> simp [val_func]
  case fvar x => exact h x (by simp [FVar?])
  case func k f v ih =>
    congr; funext i; exact ih i (by intro x hx; exact h x (by simp; exact ⟨i, hx⟩))

lemma val_toEmpty [DecidableEq ξ] (t : Semiterm L ξ n) (h : t.freeVariables = ∅) : val s e ε t = valb s e (t.toEmpty h) := by
  induction t <;> simp [val_func, Semiterm.toEmpty]
  case fvar => simp at h
  case func k f v ih =>
    have : ∀ i, (v i).freeVariables = ∅ := by
      simpa [Semiterm.freeVariables_func, Finset.biUnion_eq_empty] using h
    congr 1; funext i
    exact ih i (this i)

end Semiterm

namespace Structure

section

variable [s : Structure L M] (Θ : M ≃ N)

lemma ofEquiv_func (f : L.Func k) (v : Fin k → N) :
    (ofEquiv Θ).func f v = Θ (func f (Θ.symm ∘ v)) := rfl

lemma ofEquiv_val (e : Fin n → N) (ε : ξ → N) (t : Semiterm L ξ n) :
    t.val (ofEquiv Θ) e ε = Θ (t.val s (Θ.symm ∘ e) (Θ.symm ∘ ε)) := by
  induction t <;> simp [*, Semiterm.val_func, ofEquiv_func Θ, Function.comp_def]

end

end Structure

namespace Semiformula

variable {M : Type w} {s : Structure L M}
variable {n : ℕ} {e : Fin n → M} {e₂ : Fin n₂ → M} {ε : ξ → M} {ε₂ : μ₂ → M}

def EvalAux (s : Structure L M) (ε : ξ → M) : ∀ {n}, (Fin n → M) → Semiformula L ξ n → Prop
  | _, _, ⊤        => True
  | _, _, ⊥        => False
  | _, e, rel φ v  => s.rel φ (fun i => Semiterm.val s e ε (v i))
  | _, e, nrel φ v => ¬s.rel φ (fun i => Semiterm.val s e ε (v i))
  | _, e, φ ⋏ ψ    => φ.EvalAux s ε e ∧ ψ.EvalAux s ε e
  | _, e, φ ⋎ ψ    => φ.EvalAux s ε e ∨ ψ.EvalAux s ε e
  | _, e, ∀' φ     => ∀ x : M, (φ.EvalAux s ε (x :> e))
  | _, e, ∃' φ     => ∃ x : M, (φ.EvalAux s ε (x :> e))

@[simp] lemma EvalAux_neg (φ : Semiformula L ξ n) :
    EvalAux s ε e (∼φ) = ¬EvalAux s ε e φ :=
  by induction φ using rec' <;> simp [*, EvalAux, ←neg_eq, or_iff_not_imp_left]

def Eval (s : Structure L M) (e : Fin n → M) (ε : ξ → M) : Semiformula L ξ n →ˡᶜ Prop where
  toTr := EvalAux s ε e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp [EvalAux]
  map_or' := by simp [EvalAux]
  map_neg' := by simp [EvalAux_neg]
  map_imply' := by simp [imp_eq, EvalAux_neg, ←neg_eq, EvalAux, imp_iff_not_or]

abbrev Evalm (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : ξ → M) :
    Semiformula L ξ n →ˡᶜ Prop := Eval s e ε

abbrev Evalf (s : Structure L M) (ε : ξ → M) : Formula L ξ →ˡᶜ Prop := Eval s ![] ε

abbrev Evalb (s : Structure L M) (e : Fin n → M) : Semisentence L n →ˡᶜ Prop := Eval s e Empty.elim

abbrev Evalfm (M : Type w) [s : Structure L M] (ε : ξ → M) :
    Formula L ξ →ˡᶜ Prop := Evalf s ε

abbrev Evalbm (M : Type w) [s : Structure L M] (e : Fin n → M) :
    Semiformula L Empty n →ˡᶜ Prop := Evalb s e

notation:max M:90 " ⊧/" e:max => Evalbm M e

abbrev Realize (s : Structure L M) : Formula L M →ˡᶜ Prop := Eval s ![] id

lemma eval_rel {k} {r : L.Rel k} {v} :
    Eval s e ε (rel r v) ↔ s.rel r (fun i => Semiterm.val s e ε (v i)) := of_eq rfl

lemma Eval.of_eq {e e' : Fin n → M} {ε ε' : ξ → M} {φ} (h : Eval s e ε φ) (he : e = e') (hε : ε = ε') : Eval s e' ε' φ := he ▸ hε ▸ h

@[simp] lemma eval_rel₀ {r : L.Rel 0} :
    Eval s e ε (rel r ![]) ↔ s.rel r ![] := by simp [eval_rel, Matrix.empty_eq]

@[simp] lemma eval_rel₁ {r : L.Rel 1} (t : Semiterm L ξ n) :
    Eval s e ε (rel r ![t]) ↔ s.rel r ![t.val s e ε] := by
  simp [eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_rel₂ {r : L.Rel 2} (t₁ t₂ : Semiterm L ξ n) :
    Eval s e ε (rel r ![t₁, t₂]) ↔ s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp [eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

lemma eval_nrel {k} {r : L.Rel k} {v} :
    Eval s e ε (nrel r v) ↔ ¬s.rel r (fun i => Semiterm.val s e ε (v i)) := of_eq rfl

@[simp] lemma eval_nrel₀ {r : L.Rel 0} :
    Eval s e ε (nrel r ![]) ↔ ¬s.rel r ![] := by simp [eval_nrel, Matrix.empty_eq]

@[simp] lemma eval_nrel₁ {r : L.Rel 1} (t : Semiterm L ξ n) :
    Eval s e ε (nrel r ![t]) ↔ ¬s.rel r ![t.val s e ε] := by
  simp [eval_nrel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_nrel₂ {r : L.Rel 2} (t₁ t₂ : Semiterm L ξ n) :
    Eval s e ε (nrel r ![t₁, t₂]) ↔ ¬s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp [eval_nrel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_all {φ : Semiformula L ξ (n + 1)} :
    Eval s e ε (∀' φ) ↔ ∀ x : M, Eval s (x :> e) ε φ := of_eq rfl

@[simp] lemma eval_ex {φ : Semiformula L ξ (n + 1)} :
    Eval s e ε (∃' φ) ↔ ∃ x : M, Eval s (x :> e) ε φ := of_eq rfl

@[simp] lemma eval_ball {φ ψ : Semiformula L ξ (n + 1)} :
    Eval s e ε (∀[φ] ψ) ↔ ∀ x : M, Eval s (x :> e) ε φ → Eval s (x :> e) ε ψ := by
  simp [ball]

@[simp] lemma eval_bex {φ ψ : Semiformula L ξ (n + 1)} :
    Eval s e ε (∃[φ] ψ) ↔ ∃ x : M, Eval s (x :> e) ε φ ⋏ Eval s (x :> e) ε ψ := by
  simp [bex]

@[simp] lemma eval_univClosure {e'} {φ : Semiformula L ξ n'} :
    Eval s e' ε (∀* φ) ↔ ∀ e, Eval s e ε φ := by
  induction' n' with n' ih generalizing e' <;> simp [*, eq_finZeroElim, univClosure_succ]
  constructor
  · intro h e; simpa using h (Matrix.vecTail e) (Matrix.vecHead e)
  · intro h e x; exact h (x :> e)

@[simp] lemma eval_exClosure {e'} {φ : Semiformula L ξ n'} :
    Eval s e' ε (∃* φ) ↔ ∃ e, Eval s e ε φ := by
  induction' n' with n' ih generalizing e' <;> simp [*, eq_finZeroElim, exClosure_succ]
  constructor
  · rintro ⟨e, x, h⟩; exact ⟨x :> e, h⟩
  · rintro ⟨e, h⟩; exact ⟨Matrix.vecTail e, Matrix.vecHead e, by simpa using h⟩

@[simp] lemma eval_univItr {k} {e} {φ : Semiformula L ξ (n + k)} :
    Eval s e ε (∀^[k] φ) ↔ ∀ e', Eval s (Matrix.appendr e' e) ε φ := by
  induction' k with k ih generalizing e <;> simp [*, Matrix.empty_eq, univItr_succ]
  constructor
  · intro h e'
    exact Eval.of_eq (h (Matrix.vecTail e') (Matrix.vecHead e'))
      (by rw [←Matrix.appendr_cons, Matrix.cons_head_tail]) rfl
  · intro h e' x; simpa using h (x :> e')

@[simp] lemma eval_exItr {k} {e} {φ : Semiformula L ξ (n + k)} :
    Eval s e ε (∃^[k] φ) ↔ ∃ e', Eval s (Matrix.appendr e' e) ε φ := by
  induction' k with k ih generalizing e <;> simp [*, Matrix.empty_eq, exItr_succ]
  constructor
  · rintro ⟨e', x, h⟩
    exact ⟨x :> e', by simpa using h⟩
  · rintro ⟨e, h⟩
    exact ⟨Matrix.vecTail e, Matrix.vecHead e,
      by rw [←Matrix.appendr_cons, Matrix.cons_head_tail]; exact h⟩

section rew

variable {ε : ξ → M} {ε₂ : ξ₂ → M}

lemma eval_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    Eval s e₂ ε₂ (ω ▹ φ) ↔ Eval s (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.bvar) (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.fvar) φ := by
  induction φ using rec' generalizing n₂ <;> simp [*, Semiterm.val_rew, eval_rel, eval_nrel, rew_rel, rew_nrel]
  case hall => simp [Function.comp_def]; exact iff_of_eq <| forall_congr fun x ↦ by congr; funext i; cases i using Fin.cases <;> simp
  case hex => simp [Function.comp_def]; exact exists_congr fun x ↦ iff_of_eq $ by congr; funext i; cases i using Fin.cases <;> simp

lemma eval_rew_q {ε₂ : ξ₂ → M} (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ (n₁ + 1)) :
    Eval s (x :> e₂) ε₂ (ω.q ▹ φ) ↔
    Eval s
      (x :> Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.bvar)
      (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.fvar) φ := by
  simp [eval_rew, Function.comp_def]
  apply iff_of_eq; congr 2
  · funext x
    cases x using Fin.cases <;> simp

lemma eval_map (b : Fin n₁ → Fin n₂) (f : ξ₁ → ξ₂) (e : Fin n₂ → M) (ε : ξ₂ → M) (φ : Semiformula L ξ₁ n₁) :
    Eval s e ε ((Rew.map (L := L) b f) ▹ φ) ↔ Eval s (e ∘ b) (ε ∘ f) φ := by
  simp [eval_rew, Function.comp_def]

lemma eval_rewrite (f : ξ₁ → Semiterm L ξ₂ n) (φ : Semiformula L ξ₁ n) :
    Eval s e ε₂ (Rew.rewrite f ▹ φ) ↔ Eval s e (fun x ↦ (f x).val s e ε₂) φ := by
  simp [eval_rew, Function.comp_def]

lemma eval_rewriteMap (f : ξ₁ → ξ₂) (φ : Semiformula L ξ₁ n) :
    Eval s e ε₂ (Rew.rewriteMap (L := L) (n := n) f ▹ φ) ↔ Eval s e (fun x ↦ ε₂ (f x)) φ := by
  simp [eval_rew, Function.comp_def]

@[simp] lemma eval_castLE (h : n₁ ≤ n₂) (φ : Semiformula L ξ n₁) :
    Eval s e₂ ε (@Rew.castLE L ξ _ _ h ▹ φ) ↔ Eval s (fun x ↦ e₂ (x.castLE h)) ε φ := by
  simp [eval_rew, Function.comp_def]

@[simp] lemma eval_bShift (φ : Semiformula L ξ n) :
    Eval s (x :> e) ε (@Rew.bShift L ξ n ▹ φ) ↔ Eval s e ε φ := by
  simp [eval_rew, Function.comp_def]

lemma eval_bShift' (φ : Semiformula L ξ n) :
    Eval s e' ε (@Rew.bShift L ξ n ▹ φ) ↔ Eval s (e' ·.succ) ε φ := by
  simp [eval_rew, Function.comp_def]

lemma eval_substs {k} (w : Fin k → Semiterm L ξ n) (φ : Semiformula L ξ k) :
    Eval s e ε (φ ⇜ w) ↔ Eval s (fun i ↦ (w i).val s e ε) ε φ := by
  simp [eval_rew, Function.comp_def]

@[simp] lemma eval_emb {ε : ξ → M} (φ : Semiformula L Empty n) :
    Eval s e ε (Rewriting.embedding (ξ := ξ) φ : Semiformula L ξ n) ↔ Eval s e Empty.elim φ := by
  simp [eval_rew, Function.comp_def]; apply iff_of_eq; congr; funext x; contradiction

@[simp] lemma eval_empty [h : IsEmpty o] (φ : Formula L o) :
    Eval s e ε (@Rew.empty L o _ ξ n ▹ φ) ↔ Eval s ![] h.elim φ := by
  simp [eval_rew, Function.comp_def, Matrix.empty_eq]
  apply iff_of_eq; congr; funext x; exact h.elim' x

@[simp] lemma eval_toS {e : Fin n → M} {ε} (φ : Formula L (Fin n)) :
    Eval s e ε (@Rew.toS L n ▹ φ) ↔ Eval s ![] e φ := by
  simp [Rew.toS, eval_rew, Function.comp_def, Matrix.empty_eq]

lemma eval_embSubsts {ξ} {ε : ξ → M} {k} (w : Fin k → Semiterm L ξ n) (σ : Semisentence L k) :
    Eval s e ε ((@Rew.embSubsts L ξ n k w) ▹ σ) ↔ Evalb s (fun x ↦ (w x).val s e ε) σ := by
  simp [eval_rew, Function.comp_def, Empty.eq_elim]

section Syntactic

variable (ε : ℕ → M)

@[simp] lemma eval_free (φ : SyntacticSemiformula L (n + 1)) :
    Eval s e (a :>ₙ ε) (@Rew.free L n ▹ φ) ↔ Eval s (e <: a) ε φ := by
  simp [eval_rew, Function.comp_def]; apply iff_of_eq; congr; funext x; cases x using Fin.lastCases <;> simp

@[simp] lemma eval_shift (φ : SyntacticSemiformula L n) :
    Eval s e (a :>ₙ ε) (@Rew.shift L n ▹ φ) ↔ Eval s e ε φ := by
  simp [eval_rew, Function.comp_def]

end Syntactic

lemma eval_iff_of_funEqOn [DecidableEq ξ] (φ : Semiformula L ξ n) (h : Function.funEqOn φ.FVar? ε ε') :
    Eval s e ε φ ↔ Eval s e ε' φ := by
  induction φ using Semiformula.rec'
  case hverum => simp
  case hfalsum => simp
  case hrel k r v =>
    simp [eval_rel]; apply iff_of_eq; congr
    funext i
    exact Semiterm.val_eq_of_funEqOn (v i) (fun x hx ↦ h x (fvar?_rel.mpr ⟨i, hx⟩))
  case hnrel k r v =>
    simp [eval_nrel]; apply iff_of_eq; congr
    funext i
    exact Semiterm.val_eq_of_funEqOn (v i) (fun x hx ↦ h x (fvar?_nrel.mpr ⟨i, hx⟩))
  case hand φ ψ ihp ihq =>
    simp; apply and_congr
    · exact ihp fun x hx ↦ h x (by simp [hx])
    · exact ihq fun x hx ↦ h x (by simp [hx])
  case hor φ ψ ihp ihq =>
    simp; apply or_congr
    · exact ihp fun x hx ↦ h x (by simp [hx])
    · exact ihq fun x hx ↦ h x (by simp [hx])
  case hall φ ih =>
    simp; apply forall_congr'; intro x
    exact ih (fun x hx ↦ h _ $ by simp [FVar?]; exact hx)
  case hex φ ih =>
    simp; apply exists_congr; intro x
    exact ih (fun x hx ↦ h _ $ by simp [FVar?]; exact hx)

lemma eval_toEmpty [DecidableEq ξ] {φ : Semiformula L ξ n} (hp : φ.freeVariables = ∅) : Eval s e f φ ↔ Evalb s e (φ.toEmpty hp) := by
  induction φ using Semiformula.rec'
  case hrel k R v =>
    simp [eval_rel, Semiformula.toEmpty]
    apply iff_of_eq; congr; funext i
    rw [Semiterm.val_toEmpty]
  case hnrel k R v =>
    simp [eval_rel, Semiformula.toEmpty]
    apply iff_of_eq; congr; funext i
    rw [Semiterm.val_toEmpty]
  case hverum => simp
  case hfalsum => simp
  case hand φ ψ ihp ihq =>
    simp [ihp (e := e) (by simp [by simpa [Finset.union_eq_empty] using hp]), ihq (e := e) (by simp [by simpa [Finset.union_eq_empty] using hp])]
  case hor φ ψ ihp ihq =>
    simp [ihp (e := e) (by simp [by simpa [Finset.union_eq_empty] using hp]), ihq (e := e) (by simp [by simpa [Finset.union_eq_empty] using hp])]
  case hall φ ih => simp [fun x ↦ ih (e := (x :> e)) (by simpa using hp)]
  case hex φ ih => simp [fun x ↦ ih (e := (x :> e)) (by simpa using hp)]

lemma eval_close {ε} (φ : SyntacticFormula L) :
    Evalf s ε (∀∀φ) ↔ ∀ f, Evalf s f φ := by
  simp [close, eval_rew, Function.comp_def, Matrix.empty_eq]
  constructor
  · intro h f
    refine (eval_iff_of_funEqOn φ ?_).mp (h (fun x ↦ f x))
    intro x hx; simp [Rew.fixitr_fvar, lt_fvSup_of_fvar? hx]
  · intro h f
    refine (eval_iff_of_funEqOn φ ?_).mp (h (fun x ↦ if hx : x < φ.fvSup then f ⟨x, by simp [hx]⟩ else ε 0))
    intro x hx; simp [Rew.fixitr_fvar, lt_fvSup_of_fvar? hx]

lemma eval_close₀ [Nonempty M] (φ : SyntacticFormula L) :
    Evalb s ![] (∀∀₀φ) ↔ ∀ f, Evalf s f φ := by
  haveI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  simp [Semiformula.close₀, ←eval_toEmpty (f := default), eval_close]

end rew

end Semiformula

namespace Structure

section

open Semiformula
variable [s : Structure L M] (Θ : M ≃ N)

lemma ofEquiv_rel (r : L.Rel k) (v : Fin k → N) :
    (Structure.ofEquiv Θ).rel r v ↔ Structure.rel r (Θ.symm ∘ v) := iff_of_eq rfl

lemma eval_ofEquiv_iff : ∀ {n} {e : Fin n → N} {ε : ξ → N} {φ : Semiformula L ξ n},
    Eval (ofEquiv Θ) e ε φ ↔ Eval s (Θ.symm ∘ e) (Θ.symm ∘ ε) φ
  | _, e, ε, ⊤         => by simp
  | _, e, ε, ⊥         => by simp
  | _, e, ε, .rel r v  => by simp [Function.comp_def, eval_rel, ofEquiv_rel Θ, Structure.ofEquiv_val Θ]
  | _, e, ε, .nrel r v => by simp [Function.comp_def, eval_nrel, ofEquiv_rel Θ, Structure.ofEquiv_val Θ]
  | _, e, ε, φ ⋏ ψ     => by simp [eval_ofEquiv_iff (φ := φ), eval_ofEquiv_iff (φ := ψ)]
  | _, e, ε, φ ⋎ ψ     => by simp [eval_ofEquiv_iff (φ := φ), eval_ofEquiv_iff (φ := ψ)]
  | _, e, ε, ∀' φ      => by
    simp; exact
    ⟨fun h x => by simpa[Matrix.comp_vecCons''] using eval_ofEquiv_iff.mp (h (Θ x)),
     fun h x => eval_ofEquiv_iff.mpr (by simpa[Matrix.comp_vecCons''] using h (Θ.symm x))⟩
  | _, e, ε, ∃' φ      => by
    simp; exact
    ⟨by rintro ⟨x, h⟩; exists Θ.symm x; simpa[Matrix.comp_vecCons''] using eval_ofEquiv_iff.mp h,
     by rintro ⟨x, h⟩; exists Θ x; apply eval_ofEquiv_iff.mpr; simpa[Matrix.comp_vecCons''] using h⟩

lemma evalf_ofEquiv_iff {ε : ξ → N} {φ : Formula L ξ} :
    Evalf (ofEquiv Θ) ε φ ↔ Evalf s (Θ.symm ∘ ε) φ := by simpa using eval_ofEquiv_iff (Θ := Θ) (ε := ε) (φ := φ) (e := ![])

end

end Structure

instance : Semantics (SyntacticFormula L) (Struc L) where
  Realize := fun str φ ↦ ∀ f, Semiformula.Evalf str.struc f φ

instance : Semantics.Top (Struc L) := ⟨by simp [Semantics.Realize]⟩

instance : Semantics.Bot (Struc L) := ⟨by simp [Semantics.Realize]⟩

instance : Semantics.And (Struc L) := ⟨by
  intro 𝓜 φ ψ
  constructor
  · intro h; exact ⟨fun f ↦ (h f).left, fun f ↦ (h f).right⟩
  · rintro ⟨hp, hq⟩ f; exact ⟨hp f, hq f⟩ ⟩

section

variable (M : Type*) [Nonempty M] [s : Structure L M] {T U : Theory L}

abbrev Models : SyntacticFormula L → Prop := Semantics.Realize s.toStruc

infix:45 " ⊧ₘ " => Models

abbrev Models₀ (σ : Sentence L) : Prop := M ⊧ₘ (↑σ : SyntacticFormula L)

infix:45 " ⊧ₘ₀ " => Models₀

abbrev ModelsTheory (T : Theory L) : Prop :=
  Semantics.RealizeSet s.toStruc T

infix:45 " ⊧ₘ* " => ModelsTheory

abbrev Realize (M : Type*) [s : Structure L M] : Formula L M → Prop := Semiformula.Evalf s id

infix:45 " ⊧ₘᵣ " => Realize

abbrev Consequence (T : Theory L) (φ : SyntacticFormula L) : Prop := T ⊨[SmallStruc L] φ

infix:45 " ⊨ " => Consequence

abbrev Satisfiable (T : Theory L) : Prop := Semantics.Satisfiable (SmallStruc L) T

variable {M}

def modelsTheory_iff_modelsTheory_s : M ⊧ₘ* T ↔ s.toStruc ⊧* T := by rfl

lemma models_def {φ} : (M ⊧ₘ φ) = ∀ f, Semiformula.Evalf s f φ := rfl

lemma models_iff {φ} : M ⊧ₘ φ ↔ ∀ f, Semiformula.Evalf s f φ := by simp [models_def]

lemma models₀_iff {σ : Sentence L} : M ⊧ₘ₀ σ ↔ Semiformula.Evalb s ![] σ := by
  simp [models_iff]

lemma models_iff₀ {φ} : M ⊧ₘ φ ↔ Semiformula.Evalb s ![] ∀∀₀φ := by
  haveI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  simp [models_def, Semiformula.eval_close₀]

lemma modelsTheory_iff : M ⊧ₘ* T ↔ (∀ {φ}, φ ∈ T → M ⊧ₘ φ) := Semantics.realizeSet_iff

variable (M T)

lemma Theory.models [M ⊧ₘ* T] {φ} (hp : φ ∈ T) : M ⊧ₘ φ := Semantics.realizeSet_iff.mp inferInstance hp

variable {M T}

lemma models_iff_models {φ} :
    M ⊧ₘ φ ↔ s.toStruc ⊧ φ := of_eq rfl

lemma consequence_iff {φ} :
    T ⊨[Struc.{v, u} L] φ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M], M ⊧ₘ* T → M ⊧ₘ φ) :=
  ⟨fun h _ _ _ hT ↦ h hT, fun h s hT ↦ h s.Dom hT⟩

lemma consequence_iff' {φ} :
    T ⊨[Struc.{v, u} L] φ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [M ⊧ₘ* T], M ⊧ₘ φ) :=
  ⟨fun h _ _ s _ => Semantics.consequence_iff'.mp h s.toStruc,
   fun h s hs => @h s.Dom s.nonempty s.struc hs⟩

lemma valid_iff {φ} :
    Semantics.Valid (Struc.{v, u} L) φ ↔ ∀ (M : Type v) [Nonempty M] [Structure L M], M ⊧ₘ φ :=
  ⟨fun hσ _ _ s ↦ @hσ s.toStruc, fun h s ↦ h s.Dom⟩

lemma satisfiable_iff :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔ ∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M), M ⊧ₘ* T :=
  ⟨by rintro ⟨s, hs⟩; exact ⟨s.Dom, s.nonempty, s.struc, hs⟩, by rintro ⟨M, i, s, hT⟩; exact ⟨s.toStruc, hT⟩⟩

lemma unsatisfiable_iff :
    ¬Semantics.Satisfiable (Struc.{v, u} L) T ↔ ∀ (M : Type v) (_ : Nonempty M) (_ : Structure L M), ¬M ⊧ₘ* T := by
  simpa using satisfiable_iff.not

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

lemma consequence_iff_unsatisfiable {φ : SyntacticFormula L} :
    T ⊨[Struc.{v, u} L] φ ↔ ¬Semantics.Satisfiable (Struc.{v, u} L) (insert (∼∀∀φ) T) := by
  let σ := ∼∀∀₀φ
  have : ∼∀∀φ = Rewriting.embedding σ := by simp [Semiformula.close₀, σ]
  rw [this]
  constructor
  · intro h
    apply unsatisfiable_iff.mpr
    intro M _ s; simp only [Semantics.RealizeSet.insert_iff, models₀_iff, not_and']
    intro hT; simpa [σ] using models_iff₀.mp (h hT)
  · intro h; apply consequence_iff.mpr
    intro M _ s hT
    have : ¬(Semiformula.Evalb s ![]) σ := by
      have := by simpa only [Semantics.RealizeSet.insert_iff, not_and', models₀_iff] using unsatisfiable_iff.mp h M inferInstance s
      exact this hT
    apply models_iff₀.mpr (by simpa [σ] using this)

end

namespace Semiformula

variable {L₁ L₂ : Language} {Φ : L₁ →ᵥ L₂}

section lMap
variable {M : Type u} {s₂ : Structure L₂ M} {n} {e : Fin n → M} {ε : ξ → M}

lemma eval_lMap [Nonempty M] {φ : Semiformula L₁ ξ n} :
    Eval s₂ e ε (lMap Φ φ) ↔ Eval (s₂.lMap Φ) e ε φ :=
  by induction φ using rec' <;>
    simp [*, Semiterm.val_lMap, lMap_rel, lMap_nrel, eval_rel, eval_nrel]

lemma models_lMap [Nonempty M] {φ : SyntacticFormula L₁} :
    s₂.toStruc ⊧ lMap Φ φ ↔ (s₂.lMap Φ).toStruc ⊧ φ :=
  by simp [Semantics.Realize, Evalf, eval_lMap]

end lMap

end Semiformula

lemma lMap_models_lMap {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂}  {T : Theory L₁} {φ : SyntacticFormula L₁} (h : T ⊨[Struc.{v, u} L₁] φ) :
    T.lMap Φ ⊨[Struc.{v, u} L₂] Semiformula.lMap Φ φ := by
  intro s hM
  have : (s.struc.lMap Φ).toStruc ⊧ φ :=
    h ⟨fun _ hq => Semiformula.models_lMap.mp <| hM.realize _ (Set.mem_image_of_mem _ hq)⟩
  exact Semiformula.models_lMap.mpr this

namespace ModelsTheory

variable (M) [Nonempty M] [Structure L M]

lemma models {T : Theory L} [M ⊧ₘ* T] {φ} (h : φ ∈ T) : M ⊧ₘ φ := Semantics.RealizeSet.realize _ h

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
    ModelsTheory (s := s₂) M (T₁.lMap Φ) ↔ ModelsTheory (s := s₂.lMap Φ) M T₁ :=
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
