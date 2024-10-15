import Foundation.FirstOrder.Basic.Semantics.Semantics

namespace LO

namespace FirstOrder

section

variable {L : Language}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable [Nonempty M] [Nonempty M₁] [Nonempty M₂] [Nonempty M₃]
  [s : Structure L M] [s₁ : Structure L M₁] [s₂ : Structure L M₂] [s₃ : Structure L M₃]

namespace Structure

variable (L M M₁ M₂ M₃)

structure Hom where
  toFun : M₁ → M₂
  func' : ∀ {k} (f : L.Func k) (v : Fin k → M₁), toFun (s₁.func f v) = s₂.func f (toFun ∘ v)
  rel' : ∀ {k} (r : L.Rel k) (v : Fin k → M₁), s₁.rel r v → s₂.rel r (toFun ∘ v)

notation:25 M " →ₛ[" L "] " M' => Hom L M M'

structure Embedding extends M₁ →ₛ[L] M₂ where
  toFun_inj : Function.Injective toFun
  rel_inv' {k} (r : L.Rel k) (v : Fin k → M₁) : s₂.rel r (toFun ∘ v) → s₁.rel r v

notation:25 M " ↪ₛ[" L "] " M' => Embedding L M M'

structure Iso extends M₁ ↪ₛ[L] M₂ where
  toFun_bij : Function.Bijective toFun

notation:25 M " ≃ₛ[" L "] " M' => Iso L M M'

@[ext] structure ClosedSubset where
  domain : Set M
  domain_closed : ∀ {k} (f : L.Func k) {v : Fin k → M}, (∀ i, v i ∈ domain) → s.func f v ∈ domain

class HomClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂] [FunLike F M₁ M₂] where
  map_func : ∀ (h : F) {k} (f : L.Func k) (v : Fin k → M₁), h (func f v) = func f (h ∘ v)
  map_rel : ∀ (h : F) {k} (r : L.Rel k) (v : Fin k → M₁), s₁.rel r v → s₂.rel r (h ∘ v)

class EmbeddingClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂] [FunLike F M₁ M₂]
    extends HomClass F L M₁ M₂ where
  map_inj (f : F) : Function.Injective f
  map_rel_inv (f : F) {k} (r : L.Rel k) (v : Fin k → M₁) : s₂.rel r (f ∘ v) → s₁.rel r v

class IsoClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂] [FunLike F M₁ M₂]
    extends EmbeddingClass F L M₁ M₂ where
  map_bij (f : F) : Function.Bijective f

variable {L M M₁ M₂ M₃}

instance : FunLike (M₁ →ₛ[L] M₂) M₁ M₂ where
  coe := fun φ => φ.toFun
  coe_injective' := fun φ ψ h => by rcases φ; rcases ψ; simp at h ⊢; ext; exact congr_fun h _

instance : HomClass (M₁ →ₛ[L] M₂) L M₁ M₂ where
  map_func := Hom.func'
  map_rel := Hom.rel'

@[ext] lemma Hom.ext (φ ψ : M₁ →ₛ[L] M₂) (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext φ ψ h

namespace HomClass

variable {F : Type*} [FunLike F M₁ M₂] [HomClass F L M₁ M₂] (φ : F)

@[ext] lemma ext (φ ψ : F) (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext φ ψ h

protected lemma func {k} (f : L.Func k) (v : Fin k → M₁) :
    φ (s₁.func f v) = s₂.func f (φ ∘ v) := map_func φ f v

protected lemma rel {k} (r : L.Rel k) (v : Fin k → M₁) :
    s₁.rel r v → s₂.rel r (φ ∘ v) := map_rel φ r v

lemma val_term (e : Fin n → M₁) (ε : ξ → M₁) (t : Semiterm L ξ n) :
    φ (t.val s₁ e ε) = t.val s₂ (φ ∘ e) (φ ∘ ε) := by
  induction t <;> simp [*, Semiterm.val_func, HomClass.func, Function.comp]

end HomClass

instance : FunLike (M₁ ↪ₛ[L] M₂) M₁ M₂ where
  coe := fun φ => φ.toFun
  coe_injective' := fun φ ψ h => by rcases φ; rcases ψ; simp at h ⊢; ext; exact congr_fun h _

instance : EmbeddingClass (M₁ ↪ₛ[L] M₂) L M₁ M₂ where
  map_func := fun φ => φ.func'
  map_rel := fun φ => φ.rel'
  map_inj := Embedding.toFun_inj
  map_rel_inv := fun φ => φ.rel_inv'

@[ext] lemma Embedding.ext (φ ψ : M₁ ↪ₛ[L] M₂) (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext φ ψ h

namespace EmbeddingClass
open HomClass
variable {F : Type*} [FunLike F M₁ M₂] [EmbeddingClass F L M₁ M₂] (φ : F)

def toEmbedding : M₁ ↪ M₂ where
  toFun := φ
  inj'  := map_inj φ

protected lemma func {k} (f : L.Func k) (v : Fin k → M₁) :
    φ (s₁.func f v) = s₂.func f (φ ∘ v) := map_func φ f v

protected lemma rel {k} (r : L.Rel k) (v : Fin k → M₁) :
    s₂.rel r (φ ∘ v) ↔ s₁.rel r v := ⟨map_rel_inv φ r v, HomClass.rel φ r v⟩

end EmbeddingClass

instance : FunLike (M₁ ≃ₛ[L] M₂) M₁ M₂ where
  coe := fun φ => φ.toFun
  coe_injective' := fun φ ψ h => by rcases φ; rcases ψ; simp at h ⊢; ext; exact congr_fun h _

instance : IsoClass (M₁ ≃ₛ[L] M₂) L M₁ M₂ where
  map_func := fun φ => φ.func'
  map_rel := fun φ => φ.rel'
  map_inj := fun φ => φ.toFun_inj
  map_rel_inv := fun φ => φ.rel_inv'
  map_bij := fun φ => φ.toFun_bij

@[ext] lemma Iso.ext (φ ψ : M₁ ≃ₛ[L] M₂) (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext φ ψ h

namespace IsoClass

end IsoClass

namespace ClosedSubset

variable (u : ClosedSubset L M)

instance : SetLike (ClosedSubset L M) M := ⟨ClosedSubset.domain, ClosedSubset.ext⟩

lemma closed {k} (f : L.Func k) {v : Fin k → M} (hv : ∀ i, v i ∈ u) : s.func f v ∈ u := u.domain_closed f hv

instance toStructure [s : Structure L M] (u : ClosedSubset L M) : Structure L u where
  func := fun k f v => ⟨s.func f (fun i ↦ ↑(v i)), u.closed f (by simp)⟩
  rel := fun k r v => s.rel r (fun i ↦ v i)

protected lemma func {k} (f : L.Func k) (v : Fin k → u) : u.toStructure.func f v = s.func f (fun i ↦ v i) := rfl

protected lemma rel {k} (r : L.Rel k) (v : Fin k → u) : u.toStructure.rel r v ↔ s.rel r (fun i ↦ v i) := of_eq rfl

def inclusion : u ↪ₛ[L] M where
  toFun := Subtype.val
  func' := by simp [ClosedSubset.func, Function.comp]
  rel' := by simp [ClosedSubset.rel, Function.comp]
  rel_inv' := by simp [ClosedSubset.rel, Function.comp]
  toFun_inj := Subtype.val_injective

end ClosedSubset

end Structure

namespace Semiformula
open Structure

variable {F : Type*} [FunLike F M₁ M₂] [EmbeddingClass F L M₁ M₂] (φ : F)
variable {e₁ : Fin n → M₁} {ε₁ : ξ → M₁}

lemma eval_hom_iff_of_open : ∀ {n} {e₁ : Fin n → M₁} {ε₁ : ξ → M₁} {p : Semiformula L ξ n}, p.Open →
    (Eval s₁ e₁ ε₁ p ↔ Eval s₂ (φ ∘ e₁) (φ ∘ ε₁) p)
  | _, e₁, ε₁, ⊤,        _ => by simp
  | _, e₁, ε₁, ⊥,        _ => by simp
  | _, e₁, ε₁, rel r v,  _ => by simp [Function.comp, eval_rel, ←EmbeddingClass.rel φ, HomClass.val_term]
  | _, e₁, ε₁, nrel r v, _ => by simp [Function.comp, eval_nrel, ←EmbeddingClass.rel φ, HomClass.val_term]
  | _, e₁, ε₁, p ⋏ q,    h => by simp at h ⊢; simp [eval_hom_iff_of_open h.1, eval_hom_iff_of_open h.2]
  | _, e₁, ε₁, p ⋎ q,    h => by simp at h ⊢; simp [eval_hom_iff_of_open h.1, eval_hom_iff_of_open h.2]

lemma eval_hom_univClosure {n} {ε₁ : ξ → M₁} {p : Semiformula L ξ n} (hp : p.Open) :
    Evalf s₂ (φ ∘ ε₁) (∀* p) → Evalf s₁ ε₁ (∀* p) := by
  simp; intro h e₁; exact (eval_hom_iff_of_open φ hp).mpr (h (φ ∘ e₁))

end Semiformula

end

section

variable {L : Language} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable [Nonempty M] [Nonempty M₁] [Nonempty M₂] [Nonempty M₃]
  [s : Structure L M] [s₁ : Structure L M₁] [s₂ : Structure L M₂] [s₃ : Structure L M₃]

namespace Structure

variable (L M₁ M₂)

def ElementaryEquiv : Prop := ∀ p : SyntacticFormula L, M₁ ⊧ₘ p ↔ M₂ ⊧ₘ p

notation:50 M₁ " ≡ₑ[" L "] " M₂ => ElementaryEquiv L M₁ M₂

variable {L M₁ M₂}

namespace ElementaryEquiv

@[refl]
lemma refl (M) [Nonempty M] [Structure L M] : M ≡ₑ[L] M := fun σ => by rfl

@[symm]
lemma symm : (M₁ ≡ₑ[L] M₂) → (M₂ ≡ₑ[L] M₁) :=
  fun h σ => (h σ).symm

@[trans]
lemma trans :
    (M₁ ≡ₑ[L] M₂) → (M₂ ≡ₑ[L] M₃) → (M₁ ≡ₑ[L] M₃) :=
  fun h₁ h₂ σ => Iff.trans (h₁ σ) (h₂ σ)

lemma models (h : M₁ ≡ₑ[L] M₂) :
    ∀ {p : SyntacticFormula L}, M₁ ⊧ₘ p ↔ M₂ ⊧ₘ p := @h

lemma modelsTheory (h : M₁ ≡ₑ[L] M₂) {T : Theory L} :
    M₁ ⊧ₘ* T ↔ M₂ ⊧ₘ* T := by simp [modelsTheory_iff, h.models]

lemma ofEquiv [Nonempty N] (φ : M ≃ N) :
    letI : Structure L N := Structure.ofEquiv φ
    M ≡ₑ[L] N := fun p => by
  letI : Structure L N := Structure.ofEquiv φ
  simp [models_iff, Empty.eq_elim, Structure.evalf_ofEquiv_iff (φ := φ)]
  constructor
  · intro h f; exact h _
  · intro h f; simpa [←Function.comp.assoc] using h (φ ∘ f)

end ElementaryEquiv

end Structure

end

end FirstOrder

end LO
