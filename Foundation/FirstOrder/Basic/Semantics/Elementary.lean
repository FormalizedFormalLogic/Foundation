module

public import Foundation.FirstOrder.Basic.Semantics.Semantics

@[expose] public section

namespace LO.FirstOrder

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
  coe_injective' := fun φ ψ h => by
    rcases φ; rcases ψ
    simp only [Hom.mk.injEq] at h ⊢
    ext; exact congr_fun h _

instance : HomClass (M₁ →ₛ[L] M₂) L M₁ M₂ where
  map_func := Hom.func'
  map_rel := Hom.rel'

omit [Nonempty M₁] [Nonempty M₂]
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
  induction t <;> simp [*, Semiterm.val_func, HomClass.func, Function.comp_def]

end HomClass

instance : FunLike (M₁ ↪ₛ[L] M₂) M₁ M₂ where
  coe := fun φ => φ.toFun
  coe_injective' := fun φ ψ h => by
    rcases φ; rcases ψ; simp only [Embedding.mk.injEq] at h ⊢; ext; exact congr_fun h _

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
  coe_injective' := fun φ ψ h => by
    rcases φ; rcases ψ; simp only [Iso.mk.injEq] at h ⊢; ext; exact congr_fun h _

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

instance : SetLike (ClosedSubset L M) M := ⟨ClosedSubset.domain, fun _ _ ↦ ClosedSubset.ext⟩

omit [Nonempty M]
lemma closed {k} (f : L.Func k) {v : Fin k → M} (hv : ∀ i, v i ∈ u) : s.func f v ∈ u := u.domain_closed f hv

instance toStructure [s : Structure L M] (u : ClosedSubset L M) : Structure L u where
  func := fun k f v => ⟨s.func f (fun i ↦ ↑(v i)), u.closed f (by simp)⟩
  rel := fun k r v => s.rel r (fun i ↦ v i)

protected lemma func {k} (f : L.Func k) (v : Fin k → u) : u.toStructure.func f v = s.func f (fun i ↦ v i) := rfl

protected lemma rel {k} (r : L.Rel k) (v : Fin k → u) : u.toStructure.rel r v ↔ s.rel r (fun i ↦ v i) := of_eq rfl

def inclusion : u ↪ₛ[L] M where
  toFun := Subtype.val
  func' := by simp [ClosedSubset.func, Function.comp_def]
  rel' := by simp [ClosedSubset.rel, Function.comp_def]
  rel_inv' := by simp [ClosedSubset.rel, Function.comp_def]
  toFun_inj := Subtype.val_injective

end ClosedSubset

end Structure

namespace Semiformula
open Structure

variable {F : Type*} [FunLike F M₁ M₂] [EmbeddingClass F L M₁ M₂] (Θ : F)
variable {e₁ : Fin n → M₁} {ε₁ : ξ → M₁}

omit [Nonempty M₁] [Nonempty M₂]
lemma eval_hom_iff_of_open {n} {e₁ : Fin n → M₁} {ε₁ : ξ → M₁} : {φ : Semiformula L ξ n} → φ.Open →
    (Eval s₁ e₁ ε₁ φ ↔ Eval s₂ (Θ ∘ e₁) (Θ ∘ ε₁) φ)
  | ⊤,        _ => by simp
  | ⊥,        _ => by simp
  | rel r v,  _ => by simp [Function.comp_def, eval_rel, ←EmbeddingClass.rel Θ, HomClass.val_term]
  | nrel r v, _ => by simp [Function.comp_def, eval_nrel, ←EmbeddingClass.rel Θ, HomClass.val_term]
  | φ ⋏ ψ,    h => by simp at h ⊢; simp [eval_hom_iff_of_open h.1, eval_hom_iff_of_open h.2]
  | φ ⋎ ψ,    h => by simp at h ⊢; simp [eval_hom_iff_of_open h.1, eval_hom_iff_of_open h.2]

lemma eval_hom_univClosure {n} {ε₁ : ξ → M₁} {φ : Semiformula L ξ n} (hp : φ.Open) :
    Evalf s₂ (Θ ∘ ε₁) (∀* φ) → Evalf s₁ ε₁ (∀* φ) := by
  simp only [eval_univClosure]
  intro h e₁; exact (eval_hom_iff_of_open Θ hp).mpr (h (Θ ∘ e₁))

end Semiformula

end

section

variable {L : Language} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable [Nonempty M] [Nonempty M₁] [Nonempty M₂] [Nonempty M₃]
  [s : Structure L M] [s₁ : Structure L M₁] [s₂ : Structure L M₂] [s₃ : Structure L M₃]

namespace Structure

variable (L M₁ M₂)

class ElementaryEquiv : Prop where
  models {φ : Sentence L} : M₁ ⊧ₘ φ ↔ M₂ ⊧ₘ φ

notation:50 M₁ " ≡ₑ[" L "] " M₂ => ElementaryEquiv L M₁ M₂

variable {L M₁ M₂}

namespace ElementaryEquiv

@[refl] instance refl (M) [Nonempty M] [Structure L M] : M ≡ₑ[L] M := ⟨by rfl⟩

@[symm] lemma symm : (M₁ ≡ₑ[L] M₂) → (M₂ ≡ₑ[L] M₁) := fun h ↦ ⟨h.models.symm⟩

@[trans] lemma trans : (M₁ ≡ₑ[L] M₂) → (M₂ ≡ₑ[L] M₃) → (M₁ ≡ₑ[L] M₃) :=
  fun h₁ h₂ ↦ ⟨Iff.trans h₁.models h₂.models⟩

lemma modelsTheory [h : M₁ ≡ₑ[L] M₂] {T : Theory L} :
    M₁ ⊧ₘ* T ↔ M₂ ⊧ₘ* T := by simp [modelsTheory_iff, h.models]

variable (M₁ M₂)

lemma modelsTheory' [M₁ ≡ₑ[L] M₂] (T : Theory L) [M₂ ⊧ₘ* T] :
    M₁ ⊧ₘ* T := modelsTheory.mpr (inferInstanceAs (M₂ ⊧ₘ* T))

variable {M₁ M₂}

lemma ofEquiv [Nonempty N] (Θ : M ≃ N) :
    letI : Structure L N := Structure.ofEquiv Θ
    M ≡ₑ[L] N :=
  letI : Structure L N := Structure.ofEquiv Θ
  ⟨by simp [models_iff, Empty.eq_elim, Structure.evalf_ofEquiv_iff (Θ := Θ)]⟩

omit [Nonempty M₁] [Nonempty M₂] in
lemma val_eq_of_equiv {f₁ f₂ b₁ b₂}
    (I : M₁ ≃ M₂)
    (hf : ∀ x, I (f₁ x) = f₂ x) (hb : ∀ x, I (b₁ x) = b₂ x)
    (hfunc : ∀ {k} (f : L.Func k) {v₁ : Fin k → M₁} {v₂ : Fin k → M₂}, (∀ i, I (v₁ i) = v₂ i) → I (s₁.func f v₁) = s₂.func f v₂)
    (t : Semiterm L ξ n) :
    I (t.val s₁ b₁ f₁) = t.val s₂ b₂ f₂ :=
  match t with
  | #x => by simp [hb]
  | &x => by simp [hf]
  | .func f v => by
    have ih : ∀ i, I (Semiterm.val s₁ b₁ f₁ (v i)) = Semiterm.val s₂ b₂ f₂ (v i) := fun i ↦
      val_eq_of_equiv I hf hb hfunc (v i)
    simp [Semiterm.val_func, hfunc, ih]

omit [Nonempty M₁] [Nonempty M₂] in
lemma eval_iff_of_equiv {f₁ f₂ b₁ b₂}
    (I : M₁ ≃ M₂)
    (hf : ∀ x, I (f₁ x) = f₂ x) (hb : ∀ x, I (b₁ x) = b₂ x)
    (hrel : ∀ {k} (R : L.Rel k) {v₁ : Fin k → M₁} {v₂ : Fin k → M₂}, (∀ i, I (v₁ i) = v₂ i) → (s₁.rel R v₁ ↔ s₂.rel R v₂))
    (hfunc : ∀ {k} (f : L.Func k) {v₁ : Fin k → M₁} {v₂ : Fin k → M₂}, (∀ i, I (v₁ i) = v₂ i) → I (s₁.func f v₁) = s₂.func f v₂)
    (φ : Semiformula L ξ n) :
    Semiformula.Eval s₁ b₁ f₁ φ ↔ Semiformula.Eval s₂ b₂ f₂ φ :=
  match φ with
  | .rel R v => by
    simpa [Semiformula.eval_rel]
      using hrel R fun i ↦ val_eq_of_equiv I hf hb hfunc (v i)
  | .nrel R v => by
    simpa [Semiformula.eval_nrel]
      using not_congr <| hrel R fun i ↦ val_eq_of_equiv I hf hb hfunc (v i)
  | ⊤ => by simp
  | ⊥ => by simp
  | φ ⋏ ψ => by
    simp [eval_iff_of_equiv I hf hb hrel hfunc φ, eval_iff_of_equiv I hf hb hrel hfunc ψ]
  | φ ⋎ ψ => by
    simp [eval_iff_of_equiv I hf hb hrel hfunc φ, eval_iff_of_equiv I hf hb hrel hfunc ψ]
  | ∀' φ => by
    suffices
      (∀ x₁ : M₁, φ.Eval s₁ (x₁ :> b₁) f₁) ↔ (∀ x₂ : M₂, φ.Eval s₂ (x₂ :> b₂) f₂) by simpa
    constructor
    · intro h x₂
      have : φ.Eval s₁ (I.symm x₂ :> b₁) f₁ ↔ φ.Eval s₂ (x₂ :> b₂) f₂ :=
        eval_iff_of_equiv I (b₁ := I.symm x₂ :> b₁) (b₂ := x₂ :> b₂) hf
          (by intro i; cases i using Fin.cases <;> simp [hb])
          hrel hfunc φ
      exact this.mp (h (I.symm x₂))
    · intro h x₁
      have : φ.Eval s₁ (x₁ :> b₁) f₁ ↔ φ.Eval s₂ (I x₁ :> b₂) f₂ :=
        eval_iff_of_equiv I (b₁ := x₁ :> b₁) (b₂ := I x₁ :> b₂) hf
          (by intro i; cases i using Fin.cases <;> simp [hb])
          hrel hfunc φ
      exact this.mpr (h _)
  | ∃' φ => by
    suffices
      (∃ x₁, φ.Eval s₁ (x₁ :> b₁) f₁) ↔ (∃ x₂, φ.Eval s₂ (x₂ :> b₂) f₂) by simpa
    constructor
    · rintro ⟨x₁, h⟩
      have : φ.Eval s₁ (x₁ :> b₁) f₁ ↔ φ.Eval s₂ (I x₁ :> b₂) f₂ :=
        eval_iff_of_equiv I (b₁ := x₁ :> b₁) (b₂ := I x₁ :> b₂) hf
          (by intro i; cases i using Fin.cases <;> simp [hb])
          hrel hfunc φ
      exact ⟨I x₁, this.mp h⟩
    · rintro ⟨x₂, h⟩
      have : φ.Eval s₁ (I.symm x₂ :> b₁) f₁ ↔ φ.Eval s₂ (x₂ :> b₂) f₂ :=
        eval_iff_of_equiv I (b₁ := I.symm x₂ :> b₁) (b₂ := x₂ :> b₂) hf
          (by intro i; cases i using Fin.cases <;> simp [hb])
          hrel hfunc φ
      exact ⟨I.symm x₂, this.mpr h⟩

lemma of_equiv
    (I : M₁ ≃ M₂)
    (hrel : ∀ {k} (R : L.Rel k) {v₁ : Fin k → M₁} {v₂ : Fin k → M₂}, (∀ i, I (v₁ i) = v₂ i) → (s₁.rel R v₁ ↔ s₂.rel R v₂))
    (hfunc : ∀ {k} (f : L.Func k) {v₁ : Fin k → M₁} {v₂ : Fin k → M₂}, (∀ i, I (v₁ i) = v₂ i) → I (s₁.func f v₁) = s₂.func f v₂) :
    M₁ ≡ₑ[L] M₂ := ⟨fun {φ} ↦
  eval_iff_of_equiv
    (b₁ := ![]) (b₂ := ![]) (f₁ := Empty.elim) (f₂ := Empty.elim) I (by simp) (by simp) hrel hfunc φ⟩

end ElementaryEquiv

end Structure

end

end  LO.FirstOrder
end
