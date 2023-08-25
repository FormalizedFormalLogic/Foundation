import Logic.Predicate.Term

universe u u₁ u₂ v v₁ v₂ w w₁ w₂

namespace FirstOrder

variable
  {L : ℕ → Type u} {L₁ : ℕ → Type u₁} {L₂ : ℕ → Type u₂}
  {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂}
  {n n₁ n₂ n₃ : ℕ}

-- Structure of Term
@[ext] class TStructure (L : ℕ → Type u) (M : Type w) where
  func : ⦃k : ℕ⦄ → L k → (Fin k → M) → M

namespace TStructure

instance [Inhabited M] : Inhabited (TStructure L M) := ⟨{ func := fun _ _ => default }⟩

structure Hom (L : ℕ → Type u) (M₁ : Type w₁) (M₂ : Type w₂) [s₁ : TStructure L M₁] [s₂ : TStructure L M₂] where
  toFun : M₁ → M₂
  toFun_func' : ∀ {k} (f : L k) (v : Fin k → M₁), toFun (s₁.func f v) = s₂.func f (fun i => toFun (v i))

notation:25 M " →ᴱₛ[" L "] " M' => Hom L M M'

namespace Hom

variable {M : Type w} {M' : Type w'} [TStructure L M] [TStructure L M']

instance : FunLike (M →ᴱₛ[L] M') M (fun _ => M') where
  coe := TStructure.Hom.toFun
  coe_injective' := fun φ ψ h => by rcases φ; rcases ψ; simp; exact h

instance : CoeFun (M →ᴱₛ[L] M') (fun _ => M → M') := ⟨fun f => f.toFun⟩

@[ext] lemma ext (φ ψ : M →ᴱₛ[L] M') (h : ∀ x, φ x = ψ x) : φ = ψ := FunLike.ext φ ψ h

end Hom

end TStructure

class SubTStructure (L : ℕ → Type u) (M₁ : Type w₁) (M₂ : Type w₂) [TStructure L M₁] [TStructure L M₂] where
  inclusion : M₁ →ᴱₛ[L] M₂
  inclusion_inj : Function.Injective inclusion.toFun

notation:25 M₁ " ⊆ᴱₛ[" L "] " M₂ => SubTStructure L M₁ M₂

@[ext] structure TStructure.ClosedSubset (L : ℕ → Type u) (M : Type w) [s : TStructure L M] where
  domain : Set M
  domain_closed : ∀ {k} (f : L k) {v : Fin k → M}, (∀ i, v i ∈ domain) → s.func f v ∈ domain

instance (M : Type w) [TStructure L M] : SetLike (TStructure.ClosedSubset L M) M :=
  ⟨TStructure.ClosedSubset.domain, TStructure.ClosedSubset.ext⟩

namespace TStructure

protected def lMap (φ : ⦃k : ℕ⦄ → L₁ k → L₂ k) {M : Type w} (S : TStructure L₂ M) : TStructure L₁ M where
  func := fun _ f => S.func (φ f)

variable (φ : ⦃k : ℕ⦄ → L₁ k → L₂ k) {M : Type w} (s₂ : TStructure L₂ M)

@[simp] lemma lMap_func {k} {f : L₁ k} {v : Fin k → M} :
    (s₂.lMap φ).func f v = s₂.func (φ f) v := rfl

/-
variable [Inhabited M] (s₁ : TStructure L₁ M)

lemma extendTStructure_func
  {k} (injf : Function.Injective (φ.onFunc : L₁.func k → L₂.func k)) (f₁ : L₁.func k) (v : Fin k → M) :
    (φ.extendTStructure s₁).func (φ.onFunc f₁) v = s₁.func f₁ v := by
  simp[Language.Hom.extendTStructure]
  have : ∃ y, ∃ f₁' : L₁.func k, φ.onFunc f₁' = φ.onFunc f₁ ∧ y = s₁.func f₁' v := ⟨s₁.func f₁ v, f₁, rfl, rfl⟩
  rcases Classical.epsilon_spec this with ⟨f', f'eq, h⟩
  rcases injf f'eq with rfl; exact h

lemma extendTStructure_rel
  {k} (injr : Function.Injective (φ.onRel : L₁.rel k → L₂.rel k)) (r₁ : L₁.rel k) (v : Fin k → M) :
    (φ.extendTStructure s₁).rel (φ.onRel r₁) v ↔ s₁.rel r₁ v := by
  simp[Language.Hom.extendTStructure]
  refine ⟨by intros h; rcases h with ⟨r₁', e, h⟩; rcases injr e; exact h, by intros h; refine ⟨r₁, rfl, h⟩⟩

-/

end TStructure

namespace SubTerm

variable {M : Type w} (s : TStructure L M) (e : Fin n → M) (e₁ : Fin n₁ → M) (e₂ : Fin n₂ → M) (ε : μ → M) (ε₂ : μ₂ → M)

def val : SubTerm L μ n → M
  | #x       => e x
  | &x       => ε x
  | func f v => s.func f (fun i => (v i).val)

abbrev bVal (t : SubTerm L Empty n) : M := t.val s e Empty.elim

variable (M) {s}

abbrev val! [s : TStructure L M] {n} (e : Fin n → M) (ε : μ → M) : SubTerm L μ n → M := val s e ε

abbrev bVal! [s : TStructure L M] {n} (e : Fin n → M) : SubTerm L Empty n → M := bVal s e

variable {M e e₂ ε ε₂}

@[simp] lemma val_bvar (x) : val s e ε (#x : SubTerm L μ n) = e x := rfl

@[simp] lemma val_fvar (x) : val s e ε (&x : SubTerm L μ n) = ε x := rfl

lemma val_func {k} (f : L k) (v) :
    val s e ε (func f v) = s.func f (fun i => (v i).val s e ε) := rfl

@[simp] lemma val_func₀ (f : L 0) (v) :
    val s e ε (func f v) = s.func f ![] := by simp[val_func, Matrix.empty_eq]

@[simp] lemma val_func₁ (f : L 1) (t) :
    val s e ε (func f ![t]) = s.func f ![t.val s e ε] :=
  by simp[val_func]; apply of_eq; congr; funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma val_func₂ (f : L 2) (t u) :
    val s e ε (func f ![t, u]) = s.func f ![t.val s e ε, u.val s e ε] :=
  by simp[val_func]; apply of_eq; congr; funext i; cases' i using Fin.cases with i <;> simp

lemma val_hom (ω : SubTerm.Hom L μ₁ n₁ μ₂ n₂) (t : SubTerm L μ₁ n₁) :
    (ω t).val s e₂ ε₂ = t.val s (val s e₂ ε₂ ∘ ω ∘ bvar) (val s e₂ ε₂ ∘ ω ∘ fvar) :=
  by induction t <;> simp[*, Hom.func, val_func]

/-
lemma val_bind (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂) (t : SubTerm L μ₁ n₁) :
    (bind b e t).val s e₂ ε₂ = t.val s (val s e₂ ε₂ ∘ b) (val s e₂ ε₂ ∘ e) :=
  by simp[val_hom]

lemma val_map (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) (t : SubTerm L μ₁ n₁) :
    (map b e t).val s e₂ ε₂ = t.val s (e₂ ∘ b) (ε₂ ∘ e) := by simp[val_hom]; congr
-/

lemma val_substs {n'} (w : Fin n' → SubTerm L μ n) (t : SubTerm L μ n') :
    (substs w t).val s e ε = t.val s (fun x => (w x).val s e ε) ε :=
  by simp[val_hom]; congr

@[simp] lemma val_bShift (a : M) (t : SubTerm L μ n) :
    t.bShift.val s (a :> e) ε = t.val s e ε := by simp[val_hom, Function.comp]
section Language

variable (φ : ⦃k : ℕ⦄ → L₁ k → L₂ k) (e : Fin n → M) (ε : μ → M)

lemma val_lMap (s₂ : TStructure L₂ M) {t : SubTerm L₁ μ n} :
    (t.lMap φ).val s₂ e ε = t.val (s₂.lMap φ) e ε :=
  by induction t <;> simp[*, val!, Function.comp, val_func, SubTerm.lMap_func]

/-
variable [Inhabited M]

lemma val_extendTStructure_lMap
    (injf : ∀ k, Function.Injective (φ.onFunc : L₁.func k → L₂.func k))
    (s₁ : TStructure L₁ M) (t : SubTerm L₁ μ n) :
    val (φ.extendTStructure s₁) e ε (φ.lMap t) = val s₁ e ε t := by
  induction t <;> simp[*, Language.Hom.lMap_func, val_func]
  case func k f v ih => 
    exact TStructure.extendTStructure_func φ s₁ (injf k) f (fun i => val s₁ e ε (v i))
-/

end Language

section Syntactic

variable (ε : ℕ → M)

lemma val_shift (t : SyntacticSubTerm L n) :
    t.shift.val s e ε = t.val s e (ε ∘ Nat.succ) := by simp[val_hom]; congr

lemma val_free (a : M) (t : SyntacticSubTerm L (n + 1)) :
    t.free.val s e (a :>ₙ ε) = t.val s (e <: a) ε :=
  by simp[val_hom]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma val_fix (a : M) (t : SyntacticSubTerm L n) :
    t.fix.val s (e <: a) ε = t.val s e (a :>ₙ ε) :=
  by simp[val_hom]; congr <;> simp[Function.comp]; exact funext (Nat.cases (by simp) (by simp))

end Syntactic

end SubTerm

namespace TStructure

namespace ClosedSubset

variable {M : Type w} [s : TStructure L M] (u : ClosedSubset L M)

lemma closed {k} (f : L k) {v : Fin k → M} (hv : ∀ i, v i ∈ u) : s.func f v ∈ u := u.domain_closed f hv

instance toTStructure [s : TStructure L M] (u : ClosedSubset L M) : TStructure L u where
  func := fun k f v => ⟨s.func f (fun i => ↑(v i)), u.closed f (by simp)⟩

lemma coe_func {k} (f : L k) (v : Fin k → u) : (u.toTStructure.func f v : M) = s.func f (fun i => ↑(v i)) := rfl

end ClosedSubset

namespace Hom

variable {M₁ : Type w₁} {M₂ : Type w₂} [s₁ : TStructure L M₁] [s₂ : TStructure L M₂] (φ : M₁ →ᴱₛ[L] M₂)

protected lemma func {k} (f : L k) (v : Fin k → M₁) :
    φ (s₁.func f v) = s₂.func f (φ ∘ v) := φ.toFun_func' f v

lemma val (e : Fin n → M₁) (ε : μ → M₁) (t : SubTerm L μ n) :
    φ (t.val s₁ e ε) = t.val s₂ (φ ∘ e) (φ ∘ ε) := by
  induction t <;> simp[*, SubTerm.val_func, Hom.func, Function.comp]

def inclusion [s : TStructure L M] (u : ClosedSubset L M) : u →ᴱₛ[L] M where
  toFun := Subtype.val
  toFun_func' := by simp[ClosedSubset.coe_func]

end Hom

end TStructure

namespace SubTStructure
open TStructure

variable {M : Type w} {M₁ : Type w₁} {M₂ : Type w₂}
  [s : TStructure L M] [s₁ : TStructure L M₁] [s₂ : TStructure L M₂] [H : M₁ ⊆ᴱₛ[L] M₂]

instance closedSubset (u : ClosedSubset L M) : u ⊆ᴱₛ[L] M where
  inclusion := TStructure.Hom.inclusion u
  inclusion_inj := by simp[TStructure.Hom.inclusion]; exact Subtype.val_injective

lemma inclusion_func {k} (f : L k) (v : Fin k → M₁) :
  H.inclusion (s₁.func f v) = s₂.func f (H.inclusion ∘ v) := H.inclusion.func f v

lemma inclusion_val (e : Fin n → M₁) (ε : μ → M₁) (t : SubTerm L μ n) :
    H.inclusion (t.val s₁ e ε) = t.val s₂ (H.inclusion ∘ e) (H.inclusion ∘ ε) := 
  H.inclusion.val e ε t

end SubTStructure

end FirstOrder