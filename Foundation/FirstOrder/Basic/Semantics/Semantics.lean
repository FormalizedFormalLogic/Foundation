module

public import Foundation.FirstOrder.Basic.Syntax.Schema
public import Foundation.Vorspiel.IsEmpty
public import Foundation.Vorspiel.Empty

@[expose] public section

/-!
# Model-theoretic semantics of first-order classical logic

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
  exact ⟨{ func := fun _ _ _ ↦ x, rel := fun _ _ _ ↦ True }⟩

protected def lMap (φ : L₁ →ᵥ L₂) {M : Type w} (S : Structure L₂ M) : Structure L₁ M where
  func := fun _ f => S.func (φ.func f)
  rel := fun _ r => S.rel (φ.rel r)

variable (φ : L₁ →ᵥ L₂) {M : Type w} (s₂ : Structure L₂ M)

@[simp] lemma lMap_func {k} {f : L₁.Func k} {v : Fin k → M} : (s₂.lMap φ).func f v = s₂.func (φ.func f) v := rfl

@[simp] lemma lMap_rel {k} {r : L₁.Rel k} {v : Fin k → M} : (s₂.lMap φ).rel r v ↔ s₂.rel (φ.rel r) v := of_eq rfl

def ofEquiv {M : Type w} [Structure L M] {N : Type w'} (Θ : M ≃ N) : Structure L N where
  func := fun _ f v ↦ Θ (func f (Θ.symm ∘ v))
  rel  := fun _ r v ↦ rel r (Θ.symm ∘ v)

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

def val [s : Structure L M] (e : Fin n → M) (ε : ξ → M) : Semiterm L ξ n → M
  |       #x => e x
  |       &x => ε x
  | func f v => s.func f fun i ↦ (v i).val e ε

abbrev valb (M : Type w) [s : Structure L M] (e : Fin n → M) (t : ClosedSemiterm L n) : M := t.val e Empty.elim

abbrev valf [s : Structure L M] {n} (e : Fin n → M) : Semiterm L Empty n → M := val e Empty.elim

@[simp] lemma val_bvar (x) : val e ε (#x : Semiterm L ξ n) = e x := rfl

@[simp] lemma val_fvar (x) : val e ε (&x : Semiterm L ξ n) = ε x := rfl

@[simp] lemma val_func {k} (f : L.Func k) (v) :
    (func f v).val e ε = s.func f (Semiterm.val e ε ∘ v) := rfl

lemma val_func' {k} (f : L.Func k) (v) :
    (func f v).val e ε = s.func f fun i ↦ Semiterm.val e ε (v i) := rfl

lemma val_rew (ω : Rew L μ₁ n₁ μ₂ n₂) (t : Semiterm L μ₁ n₁) :
    (ω t).val e₂ ε₂ = t.val (val e₂ ε₂ ∘ ω ∘ bvar) (val e₂ ε₂ ∘ ω ∘ fvar) := by
  induction t <;> simp [*, -val_func, val_func']

lemma val_rewrite (f : μ₁ → Semiterm L μ₂ n) (t : Semiterm L μ₁ n) :
    (Rew.rewrite f t).val e ε₂ = t.val e (val e ε₂ ∘ f) := by
  simp [val_rew]; congr

lemma val_rewriteMap (f : μ₁ → μ₂) (t : Semiterm L μ₁ n) :
    (Rew.rewriteMap f t).val e ε₂ = t.val e (ε₂ ∘ f) := by
  simp [val_rew]; congr

lemma val_substs (w : Fin n₁ → Semiterm L ξ n₂) (t : Semiterm L ξ n₁) :
    (Rew.subst w t).val e₂ ε = t.val (val e₂ ε ∘ w) ε := by
  simp [val_rew]; congr

@[simp] lemma val_bShift (a : M) (t : Semiterm L ξ n) :
    (Rew.bShift t).val (a :> e) ε = t.val e ε := by simp [val_rew, Function.comp_def]

lemma val_bShift' (e : Fin (n + 1) → M) (t : Semiterm L ξ n) :
    (Rew.bShift t).val e ε = t.val (e ·.succ) ε := by simp [val_rew, Function.comp_def]

@[simp] lemma val_emb {o : Type v'} [i : IsEmpty o] (t : Semiterm L o n) :
    (Rew.emb t : Semiterm L ξ n).val e ε = t.val e i.elim := by
  simp only [val_rew]; congr; funext x; exact i.elim' x

@[simp] lemma val_castLE (h : n₁ ≤ n₂) (t : Semiterm L ξ n₁) :
    (Rew.castLE h t).val e₂ ε = t.val (fun x ↦ e₂ (x.castLE h)) ε  := by
  simp [val_rew]; congr

lemma val_embSubsts (w : Fin k → Semiterm L ξ n) (t : Semiterm L Empty k) :
    (Rew.embSubsts w t).val e ε = t.valb M (val e ε ∘ w) := by
  simp [val_rew, Empty.eq_elim]; congr

section Language

variable (φ : L₁ →ᵥ L₂) (e : Fin n → M) (ε : ξ → M)

lemma val_lMap (φ : L₁ →ᵥ L₂) (s₂ : Structure L₂ M) (e : Fin n → M) (ε : ξ → M) {t : Semiterm L₁ ξ n} :
    (t.lMap φ).val (s := s₂) e ε = t.val (s := s₂.lMap φ) e ε := by
  induction t <;> simp [*, val_func, Semiterm.lMap_func, Function.comp_def]

end Language

section Syntactic

variable (ε : ℕ → M)

lemma val_shift (t : SyntacticSemiterm L n) :
    (Rew.shift t).val e ε = t.val e (ε ∘ Nat.succ) := by simp [val_rew]; congr

lemma val_free (a : M) (t : SyntacticSemiterm L (n + 1)) :
    (Rew.free t).val e (a :>ₙ ε) = t.val (e <: a) ε := by
  simp only [val_rew]
  congr; exact funext <| Fin.lastCases (by simp) (by simp)

lemma val_fix (a : M) (t : SyntacticSemiterm L n) :
    (Rew.fix t).val (e <: a) ε = t.val e (a :>ₙ ε) := by
  simp only [val_rew]; congr
  · simp [Function.comp_def]
  · simpa [Function.comp_def] using funext (Nat.cases (by simp) (by simp))

end Syntactic

lemma val_eq_of_funEqOn [DecidableEq ξ] (t : Semiterm L ξ n) (h : Function.funEqOn t.FVar? ε ε') :
    t.val e ε = t.val e ε' := by
  induction t
  case bvar => simp
  case fvar x =>
    exact h x (by simp [FVar?])
  case func k f v ih =>
    simp only [val_func, Function.comp_def]
    congr; funext i; exact ih i (by intro x hx; exact h x (by simpa using ⟨i, hx⟩))

lemma val_toEmpty [DecidableEq ξ] (t : Semiterm L ξ n) (h : t.freeVariables = ∅) : t.val e ε = (t.toEmpty h).valb M e := by
  induction t
  case bvar => simp [Semiterm.toEmpty]
  case fvar => simp at h
  case func k f v ih =>
    simp only [val_func]
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
    t.val (s := ofEquiv Θ) e ε = Θ (t.val (Θ.symm ∘ e) (Θ.symm ∘ ε)) := by
  induction t <;> simp [*, Semiterm.val_func, ofEquiv_func Θ, Function.comp_def]

end

end Structure

namespace Semiformula

variable {M : Type w} {s : Structure L M}
variable {n : ℕ} {e : Fin n → M} {e₂ : Fin n₂ → M} {ε : ξ → M} {ε₂ : μ₂ → M}

def EvalAux (s : Structure L M) (ε : ξ → M) {n} (e : Fin n → M) : Semiformula L ξ n → Prop
  |  rel φ v => s.rel φ (fun i ↦ Semiterm.val e ε (v i))
  | nrel φ v => ¬s.rel φ (fun i ↦ Semiterm.val e ε (v i))
  |        ⊤ => True
  |        ⊥ => False
  |    φ ⋏ ψ => φ.EvalAux s ε e ∧ ψ.EvalAux s ε e
  |    φ ⋎ ψ => φ.EvalAux s ε e ∨ ψ.EvalAux s ε e
  |     ∀⁰ φ => ∀ x : M, (φ.EvalAux s ε (x :> e))
  |     ∃⁰ φ => ∃ x : M, (φ.EvalAux s ε (x :> e))

@[simp] lemma EvalAux_neg (φ : Semiformula L ξ n) :
    EvalAux s ε e (∼φ) = ¬EvalAux s ε e φ :=
  by induction φ using rec' <;> simp [*, EvalAux, or_iff_not_imp_left]

/-- Evaluation of semiformula with variation of free-variables `ε` and bounded-variables `e` -/
def Eval [s : Structure L M] (e : Fin n → M) (ε : ξ → M) : Semiformula L ξ n →ˡᶜ Prop where
  toTr := EvalAux s ε e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp [EvalAux]
  map_or' := by simp [EvalAux]
  map_neg' := by simp [EvalAux_neg]
  map_imply' := by simp [EvalAux_neg, ←neg_eq, EvalAux, imp_iff_not_or]

abbrev Evalf [s : Structure L M] (ε : ξ → M) : Formula L ξ →ˡᶜ Prop := Eval (s := s) ![] ε

abbrev Evalb (M : Type w) [s : Structure L M] (e : Fin n → M) :
    Semiformula L Empty n →ˡᶜ Prop := Eval e Empty.elim

notation:max M:90 " ⊧/" e:max => Evalb M e

abbrev Models (s : Structure L M) : Formula L M →ˡᶜ Prop := Eval ![] id

lemma Eval.of_eq {e e' : Fin n → M} {ε ε' : ξ → M}
    {φ : Semiformula L ξ n} (h : Eval e ε φ) (he : e = e') (hε : ε = ε') : Eval e' ε' φ := he ▸ hε ▸ h

@[simp] lemma eval_rel {r : L.Rel k} {v} :
    Eval e ε (rel r v) ↔ s.rel r (Semiterm.val e ε ∘ v) := of_eq rfl

lemma eval_rel' {r : L.Rel k} {v} :
    Eval e ε (rel r v) ↔ s.rel r fun i ↦ (v i).val e ε := of_eq rfl

@[simp] lemma eval_nrel {r : L.Rel k} {v} :
    Eval e ε (nrel r v) ↔ ¬s.rel r (Semiterm.val e ε ∘ v) := of_eq rfl

lemma eval_nrel' {r : L.Rel k} {v} :
    Eval e ε (nrel r v) ↔ ¬s.rel r fun i ↦ (v i).val e ε := of_eq rfl

@[simp] lemma eval_all {φ : Semiformula L ξ (n + 1)} :
    Eval e ε (∀⁰ φ) ↔ ∀ x : M, Eval (x :> e) ε φ := of_eq rfl

@[simp] lemma eval_ex {φ : Semiformula L ξ (n + 1)} :
    Eval e ε (∃⁰ φ) ↔ ∃ x : M, Eval (x :> e) ε φ := of_eq rfl

@[simp] lemma eval_ball {φ ψ : Semiformula L ξ (n + 1)} :
    Eval e ε (∀⁰[φ] ψ) ↔ ∀ x : M, Eval (x :> e) ε φ → Eval (x :> e) ε ψ := by
  simp [ball]

@[simp] lemma eval_bexs {φ ψ : Semiformula L ξ (n + 1)} :
    Eval e ε (∃⁰[φ] ψ) ↔ ∃ x : M, Eval (x :> e) ε φ ⋏ Eval (x :> e) ε ψ := by
  simp [bexs]

@[simp] lemma eval_allClosure {e} {φ : Semiformula L ξ k} :
    Eval e ε (∀⁰* φ) ↔ ∀ e', Eval e' ε φ :=
  match k with
  |     0 => by simp [eq_finZeroElim]
  | k + 1 => by simpa [allClosure_succ, eval_allClosure (k := k), Matrix.forall_iff] using forall_comm

@[simp] lemma eval_exsClosure {e} {φ : Semiformula L ξ k} :
    Eval e ε (∃⁰* φ) ↔ ∃ e', Eval e' ε φ :=
  match k with
  |     0 => by simp [eq_finZeroElim]
  | k + 1 => by simpa [exsClosure_succ, eval_exsClosure (k := k), Matrix.exists_iff] using exists_comm

@[simp] lemma eval_allItr {e} {φ : Semiformula L ξ (n + k)} :
    Eval e ε (∀⁰^[k] φ) ↔ ∀ e', Eval (Matrix.appendr e' e) ε φ :=
  match k with
  |     0 => by simp [Matrix.empty_eq]
  | k + 1 => by simpa [allItr_succ, eval_allItr (k := k), Matrix.forall_iff] using forall_comm

@[simp] lemma eval_exsItr {e} {φ : Semiformula L ξ (n + k)} :
    Eval e ε (∃⁰^[k] φ) ↔ ∃ e', Eval (Matrix.appendr e' e) ε φ :=
  match k with
  |     0 => by simp [Matrix.empty_eq]
  | k + 1 => by simpa [exsItr_succ, eval_exsItr (k := k), Matrix.exists_iff] using exists_comm

section rew

variable {ε : ξ → M} {ε₂ : ξ₂ → M}

lemma eval_rew {n₁ n₂ e₂ ε₂} (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    Eval e₂ ε₂ (ω ▹ φ) ↔ Eval (Semiterm.val (s := s) e₂ ε₂ ∘ ω ∘ Semiterm.bvar) (Semiterm.val (s := s) e₂ ε₂ ∘ ω ∘ Semiterm.fvar) φ := by
  match φ with
  | .rel r v | .nrel r v =>
    simp only [rew_rel_eq_comp, eval_rel, eval_nrel]; apply iff_of_eq
    congr; funext i
    simp [Semiterm.val_rew]
  | ⊤ | ⊥ => simp
  | φ ⋏ ψ | φ ⋎ ψ => simp [eval_rew ω φ, eval_rew ω ψ]
  | ∀⁰ φ =>
    simpa [Function.comp_def, eval_rew ω.q φ] using
      iff_of_eq <| forall_congr fun x ↦ by congr; funext i; cases i using Fin.cases <;> simp
  | ∃⁰ φ =>
    simpa [Function.comp_def, eval_rew ω.q φ] using
      exists_congr fun x ↦ iff_of_eq $ by congr; funext i; cases i using Fin.cases <;> simp

lemma eval_rew_q {ε₂ : ξ₂ → M} (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ (n₁ + 1)) :
    Eval (x :> e₂) ε₂ (ω.q ▹ φ) ↔
    Eval
      (x :> Semiterm.val e₂ ε₂ ∘ ω ∘ Semiterm.bvar)
      (Semiterm.val e₂ ε₂ ∘ ω ∘ Semiterm.fvar) φ := by
  simp only [Nat.succ_eq_add_one, eval_rew, Function.comp_def, Rew.q_fvar, Semiterm.val_bShift]
  apply iff_of_eq; congr 2
  · funext x
    cases x using Fin.cases <;> simp

lemma eval_map (b : Fin n₁ → Fin n₂) (f : ξ₁ → ξ₂) (e : Fin n₂ → M) (ε : ξ₂ → M) (φ : Semiformula L ξ₁ n₁) :
    Eval e ε ((Rew.map (L := L) b f) ▹ φ) ↔ Eval (e ∘ b) (ε ∘ f) φ := by
  simp [eval_rew, Function.comp_def]

lemma eval_rewrite (f : ξ₁ → Semiterm L ξ₂ n) (φ : Semiformula L ξ₁ n) :
    Eval e ε₂ (Rew.rewrite f ▹ φ) ↔ Eval e (fun x ↦ (f x).val e ε₂) φ := by
  simp [eval_rew, Function.comp_def]

lemma eval_rewriteMap (f : ξ₁ → ξ₂) (φ : Semiformula L ξ₁ n) :
    Eval e ε₂ (Rew.rewriteMap (L := L) (n := n) f ▹ φ) ↔ Eval e (fun x ↦ ε₂ (f x)) φ := by
  simp [eval_rew, Function.comp_def]

@[simp] lemma eval_castLE (h : n₁ ≤ n₂) (φ : Semiformula L ξ n₁) :
    Eval e₂ ε (@Rew.castLE L ξ _ _ h ▹ φ) ↔ Eval (fun x ↦ e₂ (x.castLE h)) ε φ := by
  simp [eval_rew, Function.comp_def]

@[simp] lemma eval_bShift (φ : Semiformula L ξ n) :
    Eval (x :> e) ε (@Rew.bShift L ξ n ▹ φ) ↔ Eval e ε φ := by
  simp [eval_rew, Function.comp_def]

lemma eval_bShift' (φ : Semiformula L ξ n) :
    Eval e' ε (@Rew.bShift L ξ n ▹ φ) ↔ Eval (e' ·.succ) ε φ := by
  simp [eval_rew, Function.comp_def]

@[simp] lemma eval_substs {k} (w : Fin k → Semiterm L ξ n) (φ : Semiformula L ξ k) :
    Eval e ε (φ ⇜ w) ↔ Eval (fun i ↦ (w i).val e ε) ε φ := by
  simp [eval_rew, Function.comp_def]

@[simp] lemma eval_emb {ε : ξ → M} (φ : Semiformula L Empty n) :
    Eval e ε (Rewriting.emb (ξ := ξ) φ : Semiformula L ξ n) ↔ Eval e Empty.elim φ := by
  simp [eval_rew, Function.comp_def, Empty.eq_elim]

@[simp] lemma eval_empty [h : IsEmpty o] (φ : Formula L o) :
    Eval e ε (@Rew.empty L o _ ξ n ▹ φ) ↔ Eval (s := s) ![] h.elim φ := by
  simp [eval_rew, Function.comp_def, Matrix.empty_eq]
  simp [IsEmpty.eq_elim]

@[simp] lemma eval_embSubsts {ξ} {ε : ξ → M} {k} (w : Fin k → Semiterm L ξ n) (σ : Semisentence L k) :
    Eval e ε ((@Rew.embSubsts L ξ n k w) ▹ σ) ↔ σ.Evalb M (fun x ↦ (w x).val e ε) := by
  simp [eval_rew, Function.comp_def, Empty.eq_elim]

section Syntactic

variable (ε : ℕ → M)

@[simp] lemma eval_free (φ : Semiproposition L (n + 1)) :
    Eval e (a :>ₙ ε) (@Rew.free L n ▹ φ) ↔ Eval (e <: a) ε φ := by
  simp only [eval_rew, Function.comp_def, Rew.free_fvar, Semiterm.val_fvar, Nat.cases_succ, Nat.succ_eq_add_one]
  apply iff_of_eq; congr; funext x; cases x using Fin.lastCases <;> simp

@[simp] lemma eval_shift (φ : Semiproposition L n) :
    Eval e (a :>ₙ ε) (@Rew.shift L n ▹ φ) ↔ Eval e ε φ := by
  simp [eval_rew, Function.comp_def]

end Syntactic

lemma eval_iff_of_funEqOn [DecidableEq ξ] {n e} (φ : Semiformula L ξ n) (h : Function.funEqOn φ.FVar? ε ε') :
    Eval e ε φ ↔ Eval e ε' φ := by
  match φ with
  |  .rel r v =>
    simp only [eval_rel]; apply iff_of_eq; congr 1
    funext i
    exact Semiterm.val_eq_of_funEqOn (v i) (fun x hx ↦ h x (fvar?_rel.mpr ⟨i, hx⟩))
  | .nrel r v =>
    simp only [eval_nrel]; apply iff_of_eq; congr 2
    funext i
    exact Semiterm.val_eq_of_funEqOn (v i) (fun x hx ↦ h x (fvar?_nrel.mpr ⟨i, hx⟩))
  | ⊤ | ⊥ => simp
  |     φ ⋏ ψ =>
    suffices Eval e ε φ ∧ Eval e ε ψ ↔ Eval e ε' φ ∧ Eval e ε' ψ by simpa
    apply and_congr
    · exact eval_iff_of_funEqOn φ fun x hx ↦ h x (by simp [hx])
    · exact eval_iff_of_funEqOn ψ fun x hx ↦ h x (by simp [hx])
  |     φ ⋎ ψ =>
    suffices Eval e ε φ ∨ Eval e ε ψ ↔ Eval e ε' φ ∨ Eval e ε' ψ by simpa
    apply or_congr
    · exact eval_iff_of_funEqOn φ fun x hx ↦ h x (by simp [hx])
    · exact eval_iff_of_funEqOn ψ fun x hx ↦ h x (by simp [hx])
  |      ∀⁰ φ =>
    suffices (∀ x, Eval (x :> e) ε φ) ↔ (∀ x, Eval (x :> e) ε' φ) by simpa
    apply forall_congr'; intro x
    exact eval_iff_of_funEqOn φ fun x hx ↦ h _ (by simpa [FVar?])
  |      ∃⁰ φ =>
    suffices (∃ x, Eval (x :> e) ε φ) ↔ (∃ x, Eval (x :> e) ε' φ) by simpa
    apply exists_congr; intro x
    exact eval_iff_of_funEqOn φ fun x hx ↦ h _ (by simpa [FVar?])

lemma eval_toEmpty [DecidableEq ξ] {n} {φ : Semiformula L ξ n} (hp : φ.freeVariables = ∅) {e} : Eval e f φ ↔ Evalb M e (φ.toEmpty hp) := by
  match φ with
  |  .rel r v =>
    simp only [eval_rel]
    apply iff_of_eq; congr 2; funext i
    simpa [Semiterm.val_toEmpty] using Semiterm.val_toEmpty _ ?_
  | .nrel r v =>
    apply iff_of_eq; congr; funext i
    rw [Semiterm.val_toEmpty]
  | ⊤ | ⊥ => simp
  | φ ⋏ ψ | φ ⋎ ψ =>
    simp [eval_toEmpty (φ := φ) (by simp [by simpa [Finset.union_eq_empty] using hp]),
      eval_toEmpty (φ := ψ) (by simp [by simpa [Finset.union_eq_empty] using hp])]
  | ∀⁰ φ =>
    have : ∀ x, Eval (x :> e) f φ ↔ Evalb M (x :> e) (φ.toEmpty hp) :=
      fun x ↦ eval_toEmpty (φ := φ) (e := (x :> e)) (by simpa using hp)
    simp [this]
  | ∃⁰ φ =>
    have : ∀ x, Eval (x :> e) f φ ↔ Evalb M (x :> e) (φ.toEmpty hp) :=
      fun x ↦ eval_toEmpty (φ := φ) (e := (x :> e)) (by simpa using hp)
    simp [this]

@[simp] lemma eval_univCl' {ε : ℕ → M} (φ : Proposition L) :
    Evalf ε φ.univCl' ↔ ∀ f : ℕ → M, Evalf f φ := by
  simp only [univCl', eval_allClosure, eval_rew, Matrix.empty_eq, Function.comp_def]
  constructor
  · intro h f
    refine (eval_iff_of_funEqOn φ ?_).mp (h (fun x ↦ f x))
    intro x hx; simp [Rew.fixitr_fvar, lt_fvSup_of_fvar? hx]
  · intro h f
    refine (eval_iff_of_funEqOn φ ?_).mp (h (fun x ↦ if hx : x < φ.fvSup then f ⟨x, by simp [hx]⟩ else ε 0))
    intro x hx; simp [Rew.fixitr_fvar, lt_fvSup_of_fvar? hx]

@[simp] lemma eval_univCl [Nonempty M] (φ : Proposition L) :
    Evalb M ![] φ.univCl ↔ ∀ f : ℕ → M, Evalf f φ := by
  haveI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  simp [Semiformula.univCl, ←eval_toEmpty (f := default)]

@[simp] lemma eval_enumarateFVar_idxOfFVar_eq_id [DecidableEq M] [Inhabited M] (φ : Semiformula L M n) (v) :
    Semiformula.Eval v (fun x ↦ φ.enumarateFVar (φ.idxOfFVar x)) φ ↔ Semiformula.Eval v id φ :=
  Semiformula.eval_iff_of_funEqOn _ <| by
    intro x hx; simp [Semiformula.enumarateFVar_idxOfFVar (Semiformula.mem_fvarList_iff_fvar?.mpr hx)]

end rew

end Semiformula

namespace Structure

section

open Semiformula
variable [s : Structure L M] (Θ : M ≃ N)

lemma ofEquiv_rel (r : L.Rel k) (v : Fin k → N) :
    (Structure.ofEquiv Θ).rel r v ↔ Structure.rel r (Θ.symm ∘ v) := iff_of_eq rfl

lemma eval_ofEquiv_iff {e : Fin n → N} {ε : ξ → N} {φ : Semiformula L ξ n} :
    Eval (s := ofEquiv Θ) e ε φ ↔ Eval (Θ.symm ∘ e) (Θ.symm ∘ ε) φ :=
  match φ with
  | .rel r v | .nrel r v => by simp [Function.comp_def, ofEquiv_rel Θ, Structure.ofEquiv_val Θ]
  | ⊤ | ⊥ => by simp
  | φ ⋏ ψ | φ ⋎ ψ => by simp [eval_ofEquiv_iff (φ := φ), eval_ofEquiv_iff (φ := ψ)]
  | ∀⁰ φ =>
    ⟨fun h x ↦ by simpa [Matrix.comp_vecCons''] using eval_ofEquiv_iff.mp (h (Θ x)),
     fun h x ↦ eval_ofEquiv_iff.mpr (by simpa [Matrix.comp_vecCons''] using h (Θ.symm x))⟩
  | ∃⁰ φ =>
    ⟨by rintro ⟨x, h⟩; exists Θ.symm x; simpa [Matrix.comp_vecCons''] using eval_ofEquiv_iff.mp h,
     by rintro ⟨x, h⟩; exists Θ x; apply eval_ofEquiv_iff.mpr; simpa [Matrix.comp_vecCons''] using h⟩

lemma evalf_ofEquiv_iff {ε : ξ → N} {φ : Formula L ξ} :
    Evalf (s := ofEquiv Θ) ε φ ↔ Evalf (s := s) (Θ.symm ∘ ε) φ := by simpa using eval_ofEquiv_iff (Θ := Θ) (ε := ε) (φ := φ) (e := ![])

end

end Structure

instance : Semantics (Struc L) (Sentence L) where
  Models := fun str ↦ Semiformula.Evalb str.Dom ![]

instance : Semantics.Tarski (Struc L) where
  models_verum := by simp [Semantics.Models]
  models_falsum := by simp [Semantics.Models]
  models_and := by simp [Semantics.Models]
  models_or := by simp [Semantics.Models]
  models_imply := by simp [Semantics.Models]
  models_not := by simp [Semantics.Models]

section

variable (M : Type*) [Nonempty M] [s : Structure L M] {T U : Theory L}

/-- Standard structure inferred from a given domain -/
abbrev Language.str (M : Type*) [Nonempty M] (L : Language) [s : Structure L M] : Struc L := s.toStruc

notation: max M "↓[" L "]" => Language.str M L

abbrev Consequence (T : Theory L) (σ : Sentence L) : Prop := T ⊨[SmallStruc L] σ

/-- Semantic entailment, also known as logical consequence. -/
scoped infix:45 " ⊨ " => Consequence

abbrev Satisfiable (T : Theory L) : Prop := Semantics.Satisfiable (SmallStruc L) T

variable {M}

lemma models_iff : M↓[L] ⊧ σ ↔ M ⊧/![] σ := by rfl

lemma models_iff_proposition {φ : Proposition L} : M↓[L] ⊧ φ.univCl ↔ ∀ f : ℕ → M, φ.Evalf f := by
  simp [models_iff]

lemma models_theory_iff : M↓[L] ⊧* T ↔ (∀ {φ}, φ ∈ T → M↓[L] ⊧ φ) := Semantics.modelsSet_iff

lemma models_schema_iff {𝓢 : Schema L} : M↓[L] ⊧* 𝓢 ↔ (∀ {φ : Proposition L}, φ ∈ 𝓢 → ∀ f : ℕ → M, φ.Evalf f) := by
  simp [models_theory_iff, models_iff]

lemma models_of_mem {T : Theory L} [M↓[L] ⊧* T] {φ} (h : φ ∈ T) : M↓[L] ⊧ φ := Semantics.ModelsSet.models _ h

variable (M T)

lemma Theory.models [M↓[L] ⊧* T] {σ} (hσ : σ ∈ T) : M↓[L] ⊧ σ := Semantics.modelsSet_iff.mp inferInstance hσ

variable {M T}

lemma models_iff_models {φ} :
    M↓[L] ⊧ φ ↔ s.toStruc ⊧ φ := of_eq rfl

lemma consequence_iff {φ} :
    T ⊨[Struc.{v, u} L] φ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M], M↓[L] ⊧* T → M↓[L] ⊧ φ) :=
  ⟨fun h _ _ _ hT ↦ h hT, fun h s hT ↦ h s.Dom hT⟩

lemma consequence_iff' {φ} :
    T ⊨[Struc.{v, u} L] φ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [M↓[L] ⊧* T], M↓[L] ⊧ φ) :=
  ⟨fun h _ _ s _ ↦ Semantics.consequence_iff'.mp h s.toStruc,
   fun h s hs ↦ @h s.Dom s.nonempty s.struc hs⟩

lemma valid_iff {φ} :
    Semantics.Valid (Struc.{v, u} L) φ ↔ ∀ (M : Type v) [Nonempty M] [Structure L M], M↓[L] ⊧ φ :=
  ⟨fun hσ _ _ s ↦ @hσ s.toStruc, fun h s ↦ h s.Dom⟩

lemma satisfiable_iff :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔ ∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M), M↓[L] ⊧* T :=
  ⟨by rintro ⟨s, hs⟩; exact ⟨s.Dom, s.nonempty, s.struc, hs⟩, by rintro ⟨M, i, s, hT⟩; exact ⟨s.toStruc, hT⟩⟩

lemma unsatisfiable_iff :
    ¬Semantics.Satisfiable (Struc.{v, u} L) T ↔ ∀ (M : Type v) (_ : Nonempty M) (_ : Structure L M), ¬M↓[L] ⊧* T := by
  simpa using satisfiable_iff.not

lemma satisfiable_intro (M : Type v) [Nonempty M] [s : Structure L M] (h : M↓[L] ⊧* T) :
    Semantics.Satisfiable (Struc.{v, u} L) T := ⟨s.toStruc, h⟩

noncomputable def ModelOfSat (h : Semantics.Satisfiable (Struc.{v, u} L) T) : Type v :=
  Classical.choose (satisfiable_iff.mp h)

noncomputable instance nonemptyModelOfSat (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    Nonempty (ModelOfSat h) := by
  choose i _ _ using Classical.choose_spec (satisfiable_iff.mp h); exact i

noncomputable def StructureModelOfSatAux (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    { _s : Structure L (ModelOfSat h) // (ModelOfSat h)↓[L] ⊧* T } := by
  choose _ s h using Classical.choose_spec (satisfiable_iff.mp h)
  exact ⟨s, h⟩

noncomputable instance StructureModelOfSat (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    Structure L (ModelOfSat h) := StructureModelOfSatAux h

lemma ModelOfSat.models (h : Semantics.Satisfiable (Struc.{v, u} L) T) : (ModelOfSat h)↓[L] ⊧* T := (StructureModelOfSatAux h).prop

lemma consequence_iff_unsatisfiable {σ : Sentence L} :
    T ⊨[Struc.{v, u} L] σ ↔ ¬Semantics.Satisfiable (Struc.{v, u} L) (insert (∼σ) T) := by
  constructor
  · intro h
    apply unsatisfiable_iff.mpr
    intro M _ s; simp only [Semantics.ModelsSet.insert_iff, models_iff, not_and']
    intro hT; simpa using models_iff.mp (h hT)
  · intro h; apply consequence_iff.mpr
    intro M _ s hT
    have : σ.Evalb M ![] := by
      have := by simpa only [Semantics.ModelsSet.insert_iff, not_and', models_iff] using unsatisfiable_iff.mp h M inferInstance s
      simpa using this hT
    apply models_iff.mpr (by simpa using this)

end

namespace Semiformula

variable {L₁ L₂ : Language} {Φ : L₁ →ᵥ L₂}

section lMap
variable {M : Type u} {s₂ : Structure L₂ M} {n} {e : Fin n → M} {ε : ξ → M}

lemma eval_lMap [Nonempty M] {φ : Semiformula L₁ ξ n} :
    Eval (s := s₂) e ε (lMap Φ φ) ↔ Eval (s := s₂.lMap Φ) e ε φ := by
  induction φ using rec' <;>
    simp [*, Semiterm.val_lMap, lMap_rel, lMap_nrel, eval_rel, eval_nrel, Function.comp_def]

lemma models_lMap [Nonempty M] {σ : Sentence L₁} :
    s₂.toStruc ⊧ lMap Φ σ ↔ (s₂.lMap Φ).toStruc ⊧ σ := by
  simp [Semantics.Models, eval_lMap]

end lMap

end Semiformula

section schema

variable (M) [Nonempty M] [Structure L M]

variable {M}

lemma of_ss {T U : Theory L} (h : M↓[L] ⊧* U) (ss : T ⊆ U) : M↓[L] ⊧* T :=
  Semantics.ModelsSet.of_subset h ss

variable {𝓢 : Schema L}

@[simp] lemma schema_sup_iff {𝓢₁ 𝓢₂ : Schema L} :
    M↓[L] ⊧* 𝓢₁ ∪ 𝓢₂ ↔ M↓[L] ⊧* 𝓢₁ ∧ M↓[L] ⊧* ↑𝓢₂ := by simp []

instance models_schema_sup (𝓢₁ 𝓢₂ : Schema L) [M↓[L] ⊧* 𝓢₁] [M↓[L] ⊧* 𝓢₂] : M↓[L] ⊧* 𝓢₁ ⊔ 𝓢₂ := by
  simp only [Set.sup_eq_union, Semantics.ModelsSet.union_iff]
  constructor
  · infer_instance
  · infer_instance

end schema

namespace Structure

variable (L)

abbrev theory (M : Type*) [Nonempty M] [s : Structure L M] : Theory L := Semantics.theory s.toStruc

variable {L} {M : Type v} [Nonempty M] [s : Structure L M]

@[simp] lemma mem_theory_iff {σ} : σ ∈ theory L M ↔ M↓[L] ⊧ σ := by rfl

lemma subset_of_models : T ⊆ theory L M ↔ M↓[L] ⊧* T := ⟨fun h  ↦ ⟨fun _ hσ ↦ h hσ⟩, fun h _ hσ ↦ h.models_set hσ⟩

lemma theory_satisfiable : Semantics.Satisfiable (Struc.{v} L) (theory L M) := ⟨s.toStruc, by simp⟩

end Structure

end FirstOrder

end LO
end
