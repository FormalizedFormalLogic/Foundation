import Logic.Predicate.FirstOrder.Basic.Formula.Formula

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

class Eq (L : Language.{u}) [L.Eq] (M : Type w) [s : Structure L M] where
  eq : ∀ a b, s.rel Language.Eq.eq ![a, b] ↔ a = b

attribute [simp] Eq.eq

namespace Inclusion

variable {M₁ : Type w₁} [Structure L M₁] {M₂ : Type w₂} [Structure L M₂] (φ : M₁ ⊆ₛ[L] M₂)

lemma inj : Function.Injective (↑φ.toHom : M₁ → M₂) := φ.inj'

def eq_of_inj [L.Eq] [Eq L M₂] : Eq L M₁ where
  eq := fun a b => by
    simp[φ.rel, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp]
    exact Function.Injective.eq_iff φ.inj (a := a) (b := b)

end Inclusion

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
  by simp[val_func]; apply of_eq; congr; funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma val_func₂ (f : L.func 2) (t u) :
    val s e ε (func f ![t, u]) = s.func f ![t.val s e ε, u.val s e ε] :=
  by simp[val_func]; apply of_eq; congr; funext i; cases' i using Fin.cases with i <;> simp

lemma val_rew (ω : Rew L μ₁ n₁ μ₂ n₂) (t : Subterm L μ₁ n₁) :
    (ω t).val s e₂ ε₂ = t.val s (val s e₂ ε₂ ∘ ω ∘ bvar) (val s e₂ ε₂ ∘ ω ∘ fvar) :=
  by induction t <;> simp[*, Rew.func, val_func]

lemma val_substs {n'} (w : Fin n' → Subterm L μ n) (t : Subterm L μ n') :
    (Rew.substs w t).val s e ε = t.val s (fun x => (w x).val s e ε) ε :=
  by simp[val_rew]; congr

@[simp] lemma val_bShift (a : M) (t : Subterm L μ n) :
    (Rew.bShift t).val s (a :> e) ε = t.val s e ε := by simp[val_rew, Function.comp]

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
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_nrel₂ {r : L.rel 2} (t₁ t₂ : Subterm L μ n) :
    Eval s e ε (nrel r ![t₁, t₂]) ↔ ¬s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_all {p : Subformula L μ (n + 1)} :
    Eval s e ε (∀' p) ↔ ∀ x : M, Eval s (x :> e) ε p := of_eq rfl

@[simp] lemma eval_univClosure {e'} {p : Subformula L μ n'} :
    Eval s e' ε (univClosure p) ↔ ∀ e, Eval s e ε p := by
  induction' n' with n' ih generalizing e' <;> simp[*, eq_finZeroElim]
  constructor
  · intro h e; simpa using h (Matrix.vecTail e) (Matrix.vecHead e)
  · intro h e x; exact h (x :> e)

@[simp] lemma eval_ex {p : Subformula L μ (n + 1)} :
    Eval s e ε (∃' p) ↔ ∃ x : M, Eval s (x :> e) ε p := of_eq rfl

lemma eval_rew (ω : Rew L μ₁ n₁ μ₂ n₂) (p : Subformula L μ₁ n₁) :
    Eval s e₂ ε₂ (ω.hom p) ↔ Eval s (Subterm.val s e₂ ε₂ ∘ ω ∘ Subterm.bvar) (Subterm.val s e₂ ε₂ ∘ ω ∘ Subterm.fvar) p := by
  induction p using rec' generalizing n₂ <;> simp[*, Subterm.val_rew, eval_rel, eval_nrel, Rew.rel, Rew.nrel]
  case hall => simp[Function.comp]; exact iff_of_eq $ forall_congr (fun x => by congr; funext i; cases i using Fin.cases <;> simp)
  case hex => simp[Function.comp]; exact exists_congr (fun x => iff_of_eq $ by congr; funext i; cases i using Fin.cases <;> simp)

lemma eval_map (b : Fin n₁ → Fin n₂) (f : μ₁ → μ₂) (e : Fin n₂ → M) (ε : μ₂ → M) (p : Subformula L μ₁ n₁) :
    Eval s e ε (Rew.mapl b f p) ↔ Eval s (e ∘ b) (ε ∘ f) p :=
  by simp[eval_rew, Function.comp]

lemma eval_substs {k} (w : Fin k → Subterm L μ n) (p : Subformula L μ k) :
    Eval s e ε (Rew.substsl w p) ↔ Eval s (fun i => (w i).val s e ε) ε p :=
  by simp[eval_rew, Function.comp]

@[simp] lemma eval_emb (p : Subformula L Empty n) :
    Eval s e ε (Rew.embl p) ↔ Eval s e Empty.elim p := by simp[eval_rew, Function.comp]; apply iff_of_eq; congr; funext x; contradiction

section Syntactic

variable (ε : ℕ → M)

@[simp] lemma eval_free (p : SyntacticSubformula L (n + 1)) :
    Eval s e (a :>ₙ ε) (Rew.freel p) ↔ Eval s (e <: a) ε p :=
  by simp[eval_rew, Function.comp]; congr; apply iff_of_eq; congr; funext x; cases x using Fin.lastCases <;> simp

@[simp] lemma eval_shift (p : SyntacticSubformula L n) :
    Eval s e (a :>ₙ ε) (Rew.shiftl p) ↔ Eval s e ε p :=
  by simp[eval_rew, Function.comp]

end Syntactic

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

open Logic

instance semantics : Semantics (Sentence L) (Structure.{u, u} L) where
  models := (Subformula.Val · Empty.elim)

abbrev Models (M : Type u) [s : Structure L M] : Sentence L →L Prop := Semantics.models s

scoped postfix:max " ⊧ " => Models

abbrev ModelsTheory (M : Type u) [s : Structure L M] (T : Theory L) : Prop :=
  Semantics.modelsTheory (𝓢 := semantics) s T

scoped infix:55 " ⊧* " => ModelsTheory

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

@[refl]
lemma ElementaryEquiv.refl (M) [Structure L M] : M ≃ₑ[L] M := fun σ => by rfl

@[symm]
lemma ElementaryEquiv.symm {M₁ M₂} [Structure L M₁] [Structure L M₂] : (M₁ ≃ₑ[L] M₂) → (M₂ ≃ₑ[L] M₁) :=
  fun h σ => (h σ).symm

@[trans]
lemma ElementaryEquiv.trans {M₁ M₂ M₃ : Type u} [Structure L M₁] [Structure L M₂] [Structure L M₃] :
    (M₁ ≃ₑ[L] M₂) → (M₂ ≃ₑ[L] M₃) → (M₁ ≃ₑ[L] M₃) :=
  fun h₁ h₂ σ => Iff.trans (h₁ σ) (h₂ σ)

lemma ElementaryEquiv.models {M₁ M₂} [Structure L M₁] [Structure L M₂] (h : M₁ ≃ₑ[L] M₂) :
    ∀ {σ : Sentence L}, M₁ ⊧ σ ↔ M₂ ⊧ σ := @h

lemma ElementaryEquiv.modelsTheory {M₁ M₂} [Structure L M₁] [Structure L M₂] (h : M₁ ≃ₑ[L] M₂) :
    ∀ {T : Theory L}, M₁ ⊧* T ↔ M₂ ⊧* T := by simp[modelsTheory_iff, h.models]

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

end Theory

namespace Subformula

variable {L : Language.{u}} [L.Eq] {μ : Type v} (M : Type w) (s : Structure L M) [s.Eq]
  {n} (e : Fin n → M) (ε : μ → M)

@[simp] lemma eval_eq (t u : Subterm L μ n) :
    Eval s e ε (rel Language.Eq.eq ![t, u]) ↔ t.val s e ε = u.val s e ε :=
  by simp

end Subformula

end FirstOrder

end LO
