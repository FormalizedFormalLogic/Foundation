import Logic.FirstOrder.Basic.Semantics

namespace LO

namespace FirstOrder

section

variable {L : Language}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable [s : Structure L M] [s₁ : Structure L M₁] [s₂ : Structure L M₂] [s₃ : Structure L M₃]

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
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂]
    extends FunLike F M₁ (fun _ => M₂) where
  map_func : ∀ (h : F) {k} (f : L.Func k) (v : Fin k → M₁), h (func f v) = func f (h ∘ v)
  map_rel : ∀ (h : F) {k} (r : L.Rel k) (v : Fin k → M₁), s₁.rel r v → s₂.rel r (h ∘ v)

class EmbeddingClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂]
    extends HomClass F L M₁ M₂ where
  map_inj (f : F) : Function.Injective f
  map_rel_inv (f : F) {k} (r : L.Rel k) (v : Fin k → M₁) : s₂.rel r (f ∘ v) → s₁.rel r v

class IsoClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂]
    extends EmbeddingClass F L M₁ M₂ where
  map_bij (f : F) : Function.Bijective f

variable {L M M₁ M₂ M₃}

instance : HomClass (M₁ →ₛ[L] M₂) L M₁ M₂ where
  coe := fun φ => φ.toFun
  coe_injective' := fun φ ψ h => by rcases φ; rcases ψ; simp at h ⊢; ext; exact congr_fun h _
  map_func := Hom.func'
  map_rel := Hom.rel'

@[ext] lemma Hom.ext (φ ψ : M₁ →ₛ[L] M₂) (h : ∀ x, φ x = ψ x) : φ = ψ := FunLike.ext φ ψ h

namespace HomClass

variable {F : Type*} [HomClass F L M₁ M₂] (φ : F)

@[ext] lemma ext (φ ψ : F) (h : ∀ x, φ x = ψ x) : φ = ψ := FunLike.ext φ ψ h

protected lemma func {k} (f : L.Func k) (v : Fin k → M₁) :
    φ (s₁.func f v) = s₂.func f (φ ∘ v) := map_func φ f v

protected lemma rel {k} (r : L.Rel k) (v : Fin k → M₁) :
    s₁.rel r v → s₂.rel r (φ ∘ v) := map_rel φ r v

lemma val_term (e : Fin n → M₁) (ε : μ → M₁) (t : Subterm L μ n) :
    φ (t.val s₁ e ε) = t.val s₂ (φ ∘ e) (φ ∘ ε) := by
  induction t <;> simp[*, Subterm.val_func, HomClass.func, Function.comp]

end HomClass

instance : EmbeddingClass (M₁ ↪ₛ[L] M₂) L M₁ M₂ where
  coe := fun φ => φ.toFun
  coe_injective' := fun φ ψ h => by rcases φ; rcases ψ; simp at h ⊢; ext; exact congr_fun h _
  map_func := fun φ => φ.func'
  map_rel := fun φ => φ.rel'
  map_inj := Embedding.toFun_inj
  map_rel_inv := fun φ => φ.rel_inv'

@[ext] lemma Embedding.ext (φ ψ : M₁ ↪ₛ[L] M₂) (h : ∀ x, φ x = ψ x) : φ = ψ := FunLike.ext φ ψ h

namespace EmbeddingClass
open HomClass
variable {F : Type*} [EmbeddingClass F L M₁ M₂] (φ : F)

def toEmbedding : M₁ ↪ M₂ where
  toFun := φ
  inj'  := map_inj φ

protected lemma func {k} (f : L.Func k) (v : Fin k → M₁) :
    φ (s₁.func f v) = s₂.func f (φ ∘ v) := map_func φ f v

protected lemma rel {k} (r : L.Rel k) (v : Fin k → M₁) :
    s₂.rel r (φ ∘ v) ↔ s₁.rel r v := ⟨map_rel_inv φ r v, HomClass.rel φ r v⟩

end EmbeddingClass

instance : IsoClass (M₁ ≃ₛ[L] M₂) L M₁ M₂ where
  coe := fun φ => φ.toFun
  coe_injective' := fun φ ψ h => by rcases φ; rcases ψ; simp at h ⊢; ext; exact congr_fun h _
  map_func := fun φ => φ.func'
  map_rel := fun φ => φ.rel'
  map_inj := fun φ => φ.toFun_inj
  map_rel_inv := fun φ => φ.rel_inv'
  map_bij := fun φ => φ.toFun_bij

@[ext] lemma Iso.ext (φ ψ : M₁ ≃ₛ[L] M₂) (h : ∀ x, φ x = ψ x) : φ = ψ := FunLike.ext φ ψ h

namespace IsoClass

end IsoClass

namespace ClosedSubset

variable (u : ClosedSubset L M)

instance : SetLike (ClosedSubset L M) M := ⟨ClosedSubset.domain, ClosedSubset.ext⟩

lemma closed {k} (f : L.Func k) {v : Fin k → M} (hv : ∀ i, v i ∈ u) : s.func f v ∈ u := u.domain_closed f hv

instance toStructure [s : Structure L M] (u : ClosedSubset L M) : Structure L u where
  func := fun k f v => ⟨s.func f (fun i => ↑(v i)), u.closed f (by simp)⟩
  rel := fun k r v => s.rel r (fun i => v i)

protected lemma func {k} (f : L.Func k) (v : Fin k → u) : u.toStructure.func f v = s.func f (fun i => v i) := rfl

protected lemma rel {k} (r : L.Rel k) (v : Fin k → u) : u.toStructure.rel r v ↔ s.rel r (fun i => v i) := of_eq rfl

def inclusion : u ↪ₛ[L] M where
  toFun := Subtype.val
  func' := by simp[ClosedSubset.func, Function.comp]
  rel' := by simp[ClosedSubset.rel, Function.comp]
  rel_inv' := by simp[ClosedSubset.rel, Function.comp]
  toFun_inj := Subtype.val_injective

end ClosedSubset

end Structure

namespace Subformula
open Structure

variable {F : Type*} [EmbeddingClass F L M₁ M₂] (φ : F)
variable {e₁ : Fin n → M₁} {ε₁ : μ → M₁}

lemma eval_hom_iff_of_qfree : ∀ {n} {e₁ : Fin n → M₁} {ε₁ : μ → M₁} {p : Subformula L μ n}, p.qfree →
    (Eval s₁ e₁ ε₁ p ↔ Eval s₂ (φ ∘ e₁) (φ ∘ ε₁) p)
  | _, e₁, ε₁, ⊤,        _ => by simp
  | _, e₁, ε₁, ⊥,        _ => by simp
  | _, e₁, ε₁, rel r v,  _ => by simp[Function.comp, eval_rel, ←EmbeddingClass.rel φ, HomClass.val_term]
  | _, e₁, ε₁, nrel r v, _ => by simp[Function.comp, eval_nrel, ←EmbeddingClass.rel φ, HomClass.val_term]
  | _, e₁, ε₁, p ⋏ q,    h => by simp at h ⊢; simp[eval_hom_iff_of_qfree h.1, eval_hom_iff_of_qfree h.2]
  | _, e₁, ε₁, p ⋎ q,    h => by simp at h ⊢; simp[eval_hom_iff_of_qfree h.1, eval_hom_iff_of_qfree h.2]

lemma eval_hom_univClosure {n} {ε₁ : μ → M₁} {p : Subformula L μ n} (hp : p.qfree) :
    Val s₂ (φ ∘ ε₁) (univClosure p) → Val s₁ ε₁ (univClosure p) := by
  simp; intro h e₁; exact (eval_hom_iff_of_qfree φ hp).mpr (h (φ ∘ e₁))

end Subformula

end

section

variable {L : Language} {M₁ : Type u} {M₂ : Type u} [s₁ : Structure L M₁] [s₂ : Structure L M₂]

namespace Structure

variable (L M₁ M₂)

def ElementaryEquiv : Prop := ∀ σ : Sentence L, M₁ ⊧ σ ↔ M₂ ⊧ σ

notation:50 M₁ " ≡ₑ[" L "] " M₂ => ElementaryEquiv L M₁ M₂

variable {L M₁ M₂}

namespace ElementaryEquiv

@[refl]
lemma refl (M) [Structure L M] : M ≡ₑ[L] M := fun σ => by rfl

@[symm]
lemma symm {M₁ M₂} [Structure L M₁] [Structure L M₂] : (M₁ ≡ₑ[L] M₂) → (M₂ ≡ₑ[L] M₁) :=
  fun h σ => (h σ).symm

@[trans]
lemma trans {M₁ M₂ M₃ : Type u} [Structure L M₁] [Structure L M₂] [Structure L M₃] :
    (M₁ ≡ₑ[L] M₂) → (M₂ ≡ₑ[L] M₃) → (M₁ ≡ₑ[L] M₃) :=
  fun h₁ h₂ σ => Iff.trans (h₁ σ) (h₂ σ)

lemma models {M₁ M₂} [Structure L M₁] [Structure L M₂] (h : M₁ ≡ₑ[L] M₂) :
    ∀ {σ : Sentence L}, M₁ ⊧ σ ↔ M₂ ⊧ σ := @h

lemma modelsTheory {M₁ M₂} [Structure L M₁] [Structure L M₂] (h : M₁ ≡ₑ[L] M₂) {T : Theory L} :
    M₁ ⊧* T ↔ M₂ ⊧* T := by simp[modelsTheory_iff, h.models]

lemma ofEquiv [Structure L M] (φ : M ≃ N) :
    letI : Structure L N := Structure.ofEquiv φ
    M ≡ₑ[L] N := fun σ => by
  letI : Structure L N := Structure.ofEquiv φ
  simp[models_iff, Empty.eq_elim, Structure.eval_ofEquiv_iff]

end ElementaryEquiv

end Structure

section EmbeddingClass

variable {F : Type*} [Structure.EmbeddingClass F L M₁ M₂] (φ : F)
variable {e₁ : Fin n → M₁} {ε₁ : μ → M₁}

lemma models_hom_iff_of_qfree {σ : Sentence L} (hσ : σ.qfree) : M₁ ⊧ σ ↔ M₂ ⊧ σ := by
  simpa[Matrix.empty_eq, Empty.eq_elim] using
    Subformula.eval_hom_iff_of_qfree (e₁ := finZeroElim) (ε₁ := Empty.elim) φ hσ

lemma models_hom_univClosure {n} {σ : Subsentence L n} (hσ : σ.qfree) :
    M₂ ⊧ (univClosure σ) → M₁ ⊧ (univClosure σ) := by
  simpa[Matrix.empty_eq, Empty.eq_elim, models_iff] using
    Subformula.eval_hom_univClosure (ε₁ := Empty.elim) φ hσ

lemma models_hom_univClosure_of_submodels (H : M₁ ↪ₛ[L] M₂) {n} {σ : Subsentence L n} (hσ : σ.qfree) :
    M₂ ⊧ (univClosure σ) → M₁ ⊧ (univClosure σ) := models_hom_univClosure H hσ

section

open Subformula
variable [s : Structure L M] (φ : M ≃ N)

lemma ElementaryEquiv.ofEquiv :
    letI : Structure L N := Structure.ofEquiv φ
    M ≡ₑ[L] N := fun σ => by
  letI : Structure L N := Structure.ofEquiv φ
  simp[models_iff, Empty.eq_elim, Structure.eval_ofEquiv_iff]

end

end EmbeddingClass

end

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

lemma elementaryEquiv (L : Language.{u}) (M : Type u) [Structure L M] : M ≡ₑ[L] Model L M :=
  ElementaryEquiv.ofEquiv _

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

@[simp] lemma func_sigma_inl {k} (f : L₁.Func k) (v : Fin k → M) : (add L₁ L₂ M).func (Sum.inl f) v = func f v := rfl

@[simp] lemma func_sigma_inr {k} (f : L₂.Func k) (v : Fin k → M) : (add L₁ L₂ M).func (Sum.inr f) v = func f v := rfl

@[simp] lemma rel_sigma_inl {k} (r : L₁.Rel k) (v : Fin k → M) : (add L₁ L₂ M).rel (Sum.inl r) v ↔ rel r v := iff_of_eq rfl

@[simp] lemma rel_sigma_inr {k} (r : L₂.Rel k) (v : Fin k → M) : (add L₁ L₂ M).rel (Sum.inr r) v ↔ rel r v := iff_of_eq rfl

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

@[simp] lemma func_sigma {k} (f : (L i).Func k) (v : Fin k → M) : (sigma L M).func ⟨i, f⟩ v = func f v := rfl

@[simp] lemma rel_sigma {k} (r : (L i).Rel k) (v : Fin k → M) : (sigma L M).rel ⟨i, r⟩ v ↔ rel r v := iff_of_eq rfl

@[simp] lemma val_lMap_sigma {n} (t : Subterm (L i) μ n) (e : Fin n → M) (ε : μ → M) :
    Subterm.val (sigma L M) e ε (t.lMap (Language.Hom.sigma L i)) = t.val (str i) e ε := by
  induction t <;> simp[Subterm.val, *]

@[simp] lemma eval_lMap_sigma {n} (p : Subformula (L i) μ n) (e : Fin n → M) (ε : μ → M) :
    Subformula.Eval (sigma L M) e ε (Subformula.lMap (Language.Hom.sigma L i) p) ↔ Subformula.Eval (str i) e ε p := by
  induction p using Subformula.rec' <;>
    simp[*, Subformula.eval_rel, Subformula.lMap_rel, Subformula.eval_nrel, Subformula.lMap_nrel]

end sigma

end Structure

section Definability

variable {L : Language.{u}} {α : Type u} [Structure L α]

def DefinableIn {k} (C : Set (Subsentence L k)) (R : Set (Fin k → α)) : Prop :=
  ∃ p ∈ C, ∀ v, v ∈ R ↔ Subformula.PVal! α v p

end Definability

end FirstOrder

end LO
