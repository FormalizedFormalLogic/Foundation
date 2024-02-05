import Logic.Logic.Semantics
import Logic.FirstOrder.Basic.Syntax.Formula

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

abbrev bVal (s : Structure L M) (e : Fin n → M) (t : Semiterm L Empty n) : M := t.val s e Empty.elim

abbrev val! (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : μ → M) : Semiterm L μ n → M := val s e ε

abbrev bVal! (M : Type w) [s : Structure L M] {n} (e : Fin n → M) : Semiterm L Empty n → M := bVal s e

abbrev realize (s : Structure L M) (t : Term L M) : M := t.val s ![] id

@[simp] lemma val_bvar (x) : val s e ε (#x : Semiterm L μ n) = e x := rfl

@[simp] lemma val_fvar (x) : val s e ε (&x : Semiterm L μ n) = ε x := rfl

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

lemma val_rew (ω : Rew L μ₁ n₁ μ₂ n₂) (t : Semiterm L μ₁ n₁) :
    (ω t).val s e₂ ε₂ = t.val s (val s e₂ ε₂ ∘ ω ∘ bvar) (val s e₂ ε₂ ∘ ω ∘ fvar) :=
  by induction t <;> simp[*, Rew.func, val_func]

lemma val_rewrite (f : μ₁ → Semiterm L μ₂ n) (t : Semiterm L μ₁ n) :
    (Rew.rewrite f t).val s e ε₂ = t.val s e (fun x => (f x).val s e ε₂) :=
  by simp[val_rew]; congr

lemma val_rewriteMap (f : μ₁ → μ₂) (t : Semiterm L μ₁ n) :
    (Rew.rewriteMap f t).val s e ε₂ = t.val s e (fun x => ε₂ (f x)) :=
  by simp[val_rew]; congr

lemma val_substs (w : Fin n₁ → Semiterm L μ n₂) (t : Semiterm L μ n₁) :
    (Rew.substs w t).val s e₂ ε = t.val s (fun x => (w x).val s e₂ ε) ε :=
  by simp[val_rew]; congr

@[simp] lemma val_bShift (a : M) (t : Semiterm L μ n) :
    (Rew.bShift t).val s (a :> e) ε = t.val s e ε := by simp[val_rew, Function.comp]

lemma val_bShift' (e : Fin (n + 1) → M) (t : Semiterm L μ n) :
    (Rew.bShift t).val s e ε = t.val s (e ·.succ) ε := by simp[val_rew, Function.comp]

@[simp] lemma val_emb {o : Type v'} [i : IsEmpty o] (t : Semiterm L o n) :
    (Rew.emb t : Semiterm L μ n).val s e ε = t.val s e i.elim := by
  simp[val_rew]; congr; { funext x; exact i.elim' x }

@[simp] lemma val_castLE (h : n₁ ≤ n₂) (t : Semiterm L μ n₁) :
    (Rew.castLE h t).val s e₂ ε = t.val s (fun x => e₂ (x.castLE h)) ε  := by
  simp[val_rew]; congr

lemma val_embSubsts (w : Fin k → Semiterm L μ n) (t : Semiterm L Empty k) :
    (Rew.embSubsts w t).val s e ε = t.bVal s (fun x ↦ (w x).val s e ε) := by
  simp [val_rew, Empty.eq_elim]; congr

section Language

variable (φ : L₁ →ᵥ L₂) (e : Fin n → M) (ε : μ → M)

lemma val_lMap (φ : L₁ →ᵥ L₂) (s₂ : Structure L₂ M) (e : Fin n → M) (ε : μ → M) {t : Semiterm L₁ μ n} :
    (t.lMap φ).val s₂ e ε = t.val (s₂.lMap φ) e ε :=
  by induction t <;> simp[*, val!, Function.comp, val_func, Semiterm.lMap_func]

end Language

section Syntactic

variable (ε : ℕ → M)

lemma val_shift (t : SyntacticSemiterm L n) :
    (Rew.shift t).val s e ε = t.val s e (ε ∘ Nat.succ) := by simp[val_rew]; congr

lemma val_free (a : M) (t : SyntacticSemiterm L (n + 1)) :
    (Rew.free t).val s e (a :>ₙ ε) = t.val s (e <: a) ε :=
  by simp[val_rew]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma val_fix (a : M) (t : SyntacticSemiterm L n) :
    (Rew.fix t).val s (e <: a) ε = t.val s e (a :>ₙ ε) :=
  by simp[val_rew]; congr <;> simp[Function.comp]; exact funext (Nat.cases (by simp) (by simp))

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
  induction t <;> simp[*, Semiterm.val_func, ofEquiv_func φ, Function.comp]

end

end Structure

namespace Semiformula

variable {M : Type w} {s : Structure L M}
variable {n : ℕ} {e : Fin n → M} {e₂ : Fin n₂ → M} {ε : μ → M} {ε₂ : μ₂ → M}

def Eval' (s : Structure L M) (ε : μ → M) : ∀ {n}, (Fin n → M) → Semiformula L μ n → Prop
  | _, _, ⊤        => True
  | _, _, ⊥        => False
  | _, e, rel p v  => s.rel p (fun i => Semiterm.val s e ε (v i))
  | _, e, nrel p v => ¬s.rel p (fun i => Semiterm.val s e ε (v i))
  | _, e, p ⋏ q    => p.Eval' s ε e ∧ q.Eval' s ε e
  | _, e, p ⋎ q    => p.Eval' s ε e ∨ q.Eval' s ε e
  | _, e, ∀' p     => ∀ x : M, (p.Eval' s ε (x :> e))
  | _, e, ∃' p     => ∃ x : M, (p.Eval' s ε (x :> e))

@[simp] lemma Eval'_neg (p : Semiformula L μ n) :
    Eval' s ε e (~p) = ¬Eval' s ε e p :=
  by induction p using rec' <;> simp[*, Eval', ←neg_eq, or_iff_not_imp_left]

def Eval (s : Structure L M) (e : Fin n → M) (ε : μ → M) : Semiformula L μ n →L Prop where
  toTr := Eval' s ε e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp[Eval']
  map_or' := by simp[Eval']
  map_neg' := by simp[Eval'_neg]
  map_imply' := by simp[imp_eq, Eval'_neg, ←neg_eq, Eval', imp_iff_not_or]

abbrev Eval! (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : μ → M) :
    Semiformula L μ n →L Prop := Eval s e ε

abbrev Val (s : Structure L M) (ε : μ → M) : Formula L μ →L Prop := Eval s ![] ε

abbrev PVal (s : Structure L M) (e : Fin n → M) : Semisentence L n →L Prop := Eval s e Empty.elim

abbrev Val! (M : Type w) [s : Structure L M] (ε : μ → M) :
    Formula L μ →L Prop := Val s ε

abbrev PVal! (M : Type w) [s : Structure L M] (e : Fin n → M) :
    Semiformula L Empty n →L Prop := PVal s e

abbrev Realize (s : Structure L M) : Formula L M →L Prop := Eval s ![] id

lemma eval_rel {k} {r : L.Rel k} {v} :
    Eval s e ε (rel r v) ↔ s.rel r (fun i => Semiterm.val s e ε (v i)) := of_eq rfl

@[simp] lemma eval_rel₀ {r : L.Rel 0} :
    Eval s e ε (rel r ![]) ↔ s.rel r ![] := by simp[eval_rel, Matrix.empty_eq]

@[simp] lemma eval_rel₁ {r : L.Rel 1} (t : Semiterm L μ n) :
    Eval s e ε (rel r ![t]) ↔ s.rel r ![t.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_rel₂ {r : L.Rel 2} (t₁ t₂ : Semiterm L μ n) :
    Eval s e ε (rel r ![t₁, t₂]) ↔ s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

lemma eval_nrel {k} {r : L.Rel k} {v} :
    Eval s e ε (nrel r v) ↔ ¬s.rel r (fun i => Semiterm.val s e ε (v i)) := of_eq rfl

@[simp] lemma eval_nrel₀ {r : L.Rel 0} :
    Eval s e ε (nrel r ![]) ↔ ¬s.rel r ![] := by simp[eval_nrel, Matrix.empty_eq]

@[simp] lemma eval_nrel₁ {r : L.Rel 1} (t : Semiterm L μ n) :
    Eval s e ε (nrel r ![t]) ↔ ¬s.rel r ![t.val s e ε] := by
  simp[eval_nrel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_nrel₂ {r : L.Rel 2} (t₁ t₂ : Semiterm L μ n) :
    Eval s e ε (nrel r ![t₁, t₂]) ↔ ¬s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_nrel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_all {p : Semiformula L μ (n + 1)} :
    Eval s e ε (∀' p) ↔ ∀ x : M, Eval s (x :> e) ε p := of_eq rfl

@[simp] lemma eval_univClosure {e'} {p : Semiformula L μ n'} :
    Eval s e' ε (∀* p) ↔ ∀ e, Eval s e ε p := by
  induction' n' with n' ih generalizing e' <;> simp[*, eq_finZeroElim, univClosure_succ]
  constructor
  · intro h e; simpa using h (Matrix.vecTail e) (Matrix.vecHead e)
  · intro h e x; exact h (x :> e)

@[simp] lemma eval_ball {p q : Semiformula L μ (n + 1)} :
    Eval s e ε (∀[p] q) ↔ ∀ x : M, Eval s (x :> e) ε p → Eval s (x :> e) ε q := by
  simp[LogicSymbol.ball]

@[simp] lemma eval_ex {p : Semiformula L μ (n + 1)} :
    Eval s e ε (∃' p) ↔ ∃ x : M, Eval s (x :> e) ε p := of_eq rfl

@[simp] lemma eval_exClosure {e'} {p : Semiformula L μ n'} :
    Eval s e' ε (exClosure p) ↔ ∃ e, Eval s e ε p := by
  induction' n' with n' ih generalizing e' <;> simp[*, eq_finZeroElim, exClosure_succ]
  constructor
  · rintro ⟨e, x, h⟩; exact ⟨x :> e, h⟩
  · rintro ⟨e, h⟩; exact ⟨Matrix.vecTail e, Matrix.vecHead e, by simpa using h⟩

@[simp] lemma eval_bex {p q : Semiformula L μ (n + 1)} :
    Eval s e ε (∃[p] q) ↔ ∃ x : M, Eval s (x :> e) ε p ⋏ Eval s (x :> e) ε q := by
  simp[LogicSymbol.bex]

lemma eval_rew (ω : Rew L μ₁ n₁ μ₂ n₂) (p : Semiformula L μ₁ n₁) :
    Eval s e₂ ε₂ (ω.hom p) ↔ Eval s (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.bvar) (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.fvar) p := by
  induction p using rec' generalizing n₂ <;> simp[*, Semiterm.val_rew, eval_rel, eval_nrel, Rew.rel, Rew.nrel]
  case hall => simp[Function.comp]; exact iff_of_eq $ forall_congr (fun x => by congr; funext i; cases i using Fin.cases <;> simp)
  case hex => simp[Function.comp]; exact exists_congr (fun x => iff_of_eq $ by congr; funext i; cases i using Fin.cases <;> simp)

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
  by simp[eval_rew, Function.comp]

lemma eval_rewrite (f : μ₁ → Semiterm L μ₂ n) (p : Semiformula L μ₁ n) :
    Eval s e ε₂ ((Rew.rewrite f).hom p) ↔ Eval s e (fun x => (f x).val s e ε₂) p :=
  by simp[eval_rew, Function.comp]

lemma eval_rewriteMap (f : μ₁ → μ₂) (p : Semiformula L μ₁ n) :
    Eval s e ε₂ ((Rew.rewriteMap f).hom p) ↔ Eval s e (fun x => ε₂ (f x)) p :=
  by simp[eval_rew, Function.comp]

@[simp] lemma eval_castLE (h : n₁ ≤ n₂) (p : Semiformula L μ n₁) :
    Eval s e₂ ε ((Rew.castLE h).hom p) ↔ Eval s (fun x => e₂ (x.castLE h)) ε p := by
  simp[eval_rew, Function.comp]

lemma eval_substs {k} (w : Fin k → Semiterm L μ n) (p : Semiformula L μ k) :
    Eval s e ε ((Rew.substs w).hom p) ↔ Eval s (fun i => (w i).val s e ε) ε p :=
  by simp[eval_rew, Function.comp]

@[simp] lemma eval_emb (p : Semiformula L Empty n) :
    Eval s e ε (Rew.emb.hom p) ↔ Eval s e Empty.elim p := by
  simp[eval_rew, Function.comp]; apply iff_of_eq; congr; funext x; contradiction

@[simp] lemma eval_empty [h : IsEmpty o] (p : Formula L o) :
    Eval s e ε (Rew.empty.hom p) ↔ Eval s ![] h.elim p := by
  simp[eval_rew, Function.comp, Matrix.empty_eq]
  apply iff_of_eq; congr; funext x; exact h.elim' x

@[simp] lemma eval_toS {e : Fin n → M} {ε} (p : Formula L (Fin n)) :
    Eval s e ε (Rew.toS.hom p) ↔ Eval s ![] e p := by
  simp [Rew.toS, eval_rew, Function.comp, Matrix.empty_eq]

lemma eval_embSubsts {k} (w : Fin k → Semiterm L μ n) (σ : Semisentence L k) :
    Eval s e ε ((Rew.embSubsts w).hom σ) ↔ PVal s (fun x ↦ (w x).val s e ε) σ := by
  simp[eval_rew, Function.comp, Empty.eq_elim]

section Syntactic

variable (ε : ℕ → M)

@[simp] lemma eval_free (p : SyntacticSemiformula L (n + 1)) :
    Eval s e (a :>ₙ ε) (Rew.free.hom p) ↔ Eval s (e <: a) ε p :=
  by simp[eval_rew, Function.comp]; congr; apply iff_of_eq; congr; funext x; cases x using Fin.lastCases <;> simp

@[simp] lemma eval_shift (p : SyntacticSemiformula L n) :
    Eval s e (a :>ₙ ε) (Rew.shift.hom p) ↔ Eval s e ε p :=
  by simp[eval_rew, Function.comp]

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
    Val s Empty.elim (∀ᶠ* p) ↔ ∀ ε, Val s ε p := by
  simp [Formula.fvUnivClosure, eval_rewriteMap]
  haveI : Inhabited μ := ⟨Classical.ofNonempty⟩
  constructor
  · intro h ε
    have := h (fun i ↦ ε $ Semiformula.fvListingInv _ i)
    exact (eval_iff_of_funEqOn p (by intro x hx; simp [fvListingInv_fvListing hx])).mp this
  · intro h e
    exact h (fun x ↦ e $ Semiformula.fvListing p x)

@[simp] lemma val_fvUnivClosure [Nonempty M] [DecidableEq μ] {p : Formula L μ} :
    Val s Empty.elim (∀ᶠ* p) ↔ ∀ ε, Val s ε p := by
  by_cases hμ : Nonempty μ
  · exact val_fvUnivClosure_inhabited
  · haveI hμ : IsEmpty μ := not_nonempty_iff.mp hμ
    simp [Formula.fv_univ_closure_sentence p, IsEmpty.eq_elim]
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
  | _, e, ε, .rel r v  => by simp[Function.comp, eval_rel, ofEquiv_rel φ, Structure.ofEquiv_val φ]
  | _, e, ε, .nrel r v => by simp[Function.comp, eval_nrel, ofEquiv_rel φ, Structure.ofEquiv_val φ]
  | _, e, ε, p ⋏ q     => by simp[eval_ofEquiv_iff (p := p), eval_ofEquiv_iff (p := q)]
  | _, e, ε, p ⋎ q     => by simp[eval_ofEquiv_iff (p := p), eval_ofEquiv_iff (p := q)]
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

instance semantics : Semantics (Sentence L) (Struc.{u, u} L) where
  realize := fun str ↦ Semiformula.Val str.struc Empty.elim

section

variable (M : Type u) [Nonempty M] [s : Structure L M] {T U : Theory L}

abbrev Models : Sentence L →L Prop := Semantics.realize s.toStruc

postfix:max " ⊧ₘ " => Models

abbrev ModelsTheory (T : Theory L) : Prop :=
  Semantics.realizeTheory s.toStruc T

infix:55 " ⊧ₘ* " => ModelsTheory

abbrev Theory.Mod (T : Theory L) := Semantics.Mod s.toStruc T

abbrev Realize (M : Type u) [s : Structure L M] : Formula L M →L Prop := Semiformula.Val s id

postfix:max " ⊧ₘᵣ " => Realize

variable {M}

def modelsTheory_iff_modelsTheory_s : M ⊧ₘ* T ↔ s.toStruc ⊧* T := by rfl

lemma models_def : M ⊧ₘ = Semiformula.Val s Empty.elim := rfl

lemma models_iff {σ : Sentence L} : M ⊧ₘ σ ↔ Semiformula.Val s Empty.elim σ := by simp[models_def]

lemma models_def' : Semantics.realize s.toStruc = Semiformula.Val s Empty.elim := rfl

lemma modelsTheory_iff : M ⊧ₘ* T ↔ (∀ ⦃p⦄, p ∈ T → M ⊧ₘ p) := of_eq rfl

lemma models_iff_models {σ : Sentence L} :
    M ⊧ₘ σ ↔ Semantics.realize s.toStruc σ := of_eq rfl

lemma consequence_iff {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Nonempty M] [Structure L M], M ⊧ₘ* T → M ⊧ₘ σ) :=
  ⟨fun h _ _ _ hT ↦ h hT, fun h s hT ↦ h s.Dom hT⟩

lemma consequence_iff' {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Nonempty M] [Structure L M] [Theory.Mod M T], M ⊧ₘ σ) :=
  ⟨fun h _ _ s _ => Semantics.consequence_iff'.mp h s.toStruc,
   fun h s hs => @h s.Dom s.nonempty s.struc ⟨hs⟩⟩

lemma valid_iff {σ : Sentence L} :
    Semantics.Valid σ ↔ ∀ (M : Type u) [Nonempty M] [Structure L M], M ⊧ₘ σ :=
  ⟨fun hσ _ _ s ↦ @hσ s.toStruc, fun h s ↦ h s.Dom⟩

lemma validₛ_iff {T : Theory L} :
    Semantics.ValidTheory T ↔ ∀ (M : Type u) [Nonempty M] [Structure L M], M ⊧ₘ* T :=
  ⟨fun hT _ _ s ↦ @hT s.toStruc, fun h s ↦ h s.Dom⟩

lemma satisfiableTheory_iff :
    Semantics.SatisfiableTheory T ↔ ∃ (M : Type u) (_ : Nonempty M) (_ : Structure L M), M ⊧ₘ* T :=
  ⟨by rintro ⟨s, hs⟩; exact ⟨s.Dom, s.nonempty, s.struc, hs⟩, by rintro ⟨M, i, s, hT⟩; exact ⟨s.toStruc, hT⟩⟩

lemma satisfiableTheory_intro (M : Type u) [Nonempty M] [s : Structure L M] (h : M ⊧ₘ* T) :
    Semantics.SatisfiableTheory T := ⟨s.toStruc, h⟩

noncomputable def ModelOfSat (h : Semantics.SatisfiableTheory T) : Type u :=
  Classical.choose (satisfiableTheory_iff.mp h)

noncomputable instance nonemptyModelOfSat (h : Semantics.SatisfiableTheory T) :
    Nonempty (ModelOfSat h) := by
  choose i _ _ using Classical.choose_spec (satisfiableTheory_iff.mp h); exact i

noncomputable def StructureModelOfSatAux (h : Semantics.SatisfiableTheory T) :
    { s : Structure L (ModelOfSat h) // ModelOfSat h ⊧ₘ* T } := by
  choose _ s h using Classical.choose_spec (satisfiableTheory_iff.mp h)
  exact ⟨s, h⟩

noncomputable instance StructureModelOfSat (h : Semantics.SatisfiableTheory T) :
    Structure L (ModelOfSat h) := StructureModelOfSatAux h

lemma ModelOfSat.models (h : Semantics.SatisfiableTheory T) : ModelOfSat h ⊧ₘ* T := (StructureModelOfSatAux h).prop

end

namespace Semiformula

variable {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂}

section lMap
variable {M : Type u} [Nonempty M] {s₂ : Structure L₂ M} {n} {e : Fin n → M} {ε : μ → M}

lemma eval_lMap {p : Semiformula L₁ μ n} :
    Eval s₂ e ε (lMap Φ p) ↔ Eval (s₂.lMap Φ) e ε p :=
  by induction p using rec' <;>
    simp[*, Semiterm.val_lMap, lMap_rel, lMap_nrel, eval_rel, eval_nrel]

lemma models_lMap {σ : Sentence L₁} :
    Semantics.realize s₂.toStruc (lMap Φ σ) ↔ Semantics.realize (s₂.lMap Φ).toStruc σ :=
  by simp[Semantics.realize, Val, eval_lMap]

end lMap

end Semiformula

lemma lMap_models_lMap {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂}  {T : Theory L₁} {σ : Sentence L₁} (h : T ⊨ σ) :
    T.lMap Φ ⊨ Semiformula.lMap Φ σ := by
  intro s hM
  have : Semantics.realize (s.struc.lMap Φ).toStruc σ :=
    h (fun q hq => Semiformula.models_lMap.mp $ hM (Set.mem_image_of_mem _ hq))
  exact Semiformula.models_lMap.mpr this

@[simp] lemma ModelsTheory.empty [Nonempty M] [Structure L M] : M ⊧ₘ* (∅ : Theory L) := by intro _; simp

lemma ModelsTheory.of_ss [Nonempty M] [Structure L M] {T U : Theory L} (h : M ⊧ₘ* U) (ss : T ⊆ U) : M ⊧ₘ* T :=
  fun _ hσ => h (ss hσ)

namespace Theory

section

variable {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂}

variable {M : Type u} [Nonempty M] [s₂ : Structure L₂ M]

lemma modelsTheory_onTheory₁ {T₁ : Theory L₁} :
    ModelsTheory (s := s₂) (T₁.lMap Φ) ↔ ModelsTheory (s := s₂.lMap Φ) T₁ :=
  by simp[Semiformula.models_lMap, Theory.lMap, modelsTheory_iff, @modelsTheory_iff (T := T₁)]

end

namespace Mod

variable (M : Type u) [Nonempty M] [s : Structure L M] (T U : Theory L) [Theory.Mod M T]

lemma modelsTheory : M ⊧ₘ* T := Semantics.Mod.realizeTheory

variable {T U}

lemma models {σ : Sentence L} (hσ : σ ∈ T) : M ⊧ₘ σ := Semantics.Mod.models s.toStruc hσ

lemma of_ss {T₁ T₂ : Theory L} [Theory.Mod M T₁] (ss : T₂ ⊆ T₁) : Theory.Mod M T₂ :=
  Semantics.Mod.of_ss s.toStruc ss

lemma of_subtheory [Nonempty M] {T₁ T₂ : Theory L} [Theory.Mod M T₁] (h : Semantics.Subtheory T₂ T₁) : Theory.Mod M T₂ :=
  Semantics.Mod.of_subtheory _ h

variable {M}

lemma of_models (h : M ⊧ₘ* T) : Theory.Mod (L := L) M T := ⟨fun _ hp ↦ h hp⟩

instance [T.Mod M] [U.Mod M] : (T + U).Mod M := of_models (by simp [add_def]; exact ⟨modelsTheory M T, modelsTheory M U⟩)

end Mod

end Theory

namespace Structure

variable (L)

abbrev theory (M : Type u) [Nonempty M] [s : Structure L M] : Theory L := Semantics.theory s.toStruc

variable {L} {M : Type u} [Nonempty M] [Structure L M]

@[simp] lemma mem_theory_iff {σ} : σ ∈ theory L M ↔ M ⊧ₘ σ := by rfl

lemma subset_of_models : T ⊆ theory L M ↔ M ⊧ₘ* T := ⟨fun h _ hσ ↦ h hσ, fun h _ hσ ↦ h hσ⟩

end Structure

end FirstOrder

end LO
