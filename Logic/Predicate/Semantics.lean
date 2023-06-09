import Logic.Predicate.Term

universe u u₁ u₂ v v₁ v₂ w w₁ w₂

variable
  {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}}
  {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂}

namespace FirstOrder
variable (L)

@[ext] class Structure (M : Type w) where
  func : {k : ℕ} → L.func k → (Fin k → M) → M
  rel  : {k : ℕ} → L.rel k → (Fin k → M) → Prop

@[ext] structure Structure.Hom (M₁ : Type w₁) (M₂ : Type w₂) [s₁ : Structure L M₁] [s₂ : Structure L M₂] where
  toFun : M₁ → M₂
  toFun_func' : ∀ {k} (f : L.func k) (v : Fin k → M₁), toFun (s₁.func f v) = s₂.func f (fun i => toFun (v i))
  toFun_rel' : ∀ {k} (r : L.rel k) (v : Fin k → M₁), s₁.rel r v ↔ s₂.rel r (fun i => toFun (v i))

notation:25 M " →ₛ[" L "] " M' => Structure.Hom L M M'

instance (M : Type w) (M' : Type w') [Structure L M] [Structure L M'] :
  CoeFun (M →ₛ[L] M') (fun _ => M → M') := ⟨fun f => f.toFun⟩

class SubStructure (M₁ : Type w₁) (M₂ : Type w₂) [Structure L M₁] [Structure L M₂] where
  inclusion : M₁ →ₛ[L] M₂
  inclusion_inj : Function.Injective inclusion.toFun

notation:25 M₁ " ⊆ₛ[" L "] " M₂ => SubStructure L M₁ M₂

@[ext] structure Structure.ClosedSubset (M : Type w) [s : Structure L M] where
  domain : Set M
  domain_closed : ∀ {k} (f : L.func k) {v : Fin k → M}, (∀ i, v i ∈ domain) → s.func f v ∈ domain

instance (M : Type w) [Structure L M] : SetLike (Structure.ClosedSubset L M) M := ⟨Structure.ClosedSubset.domain, Structure.ClosedSubset.ext⟩

end FirstOrder

namespace Language

namespace Hom

open FirstOrder

def onStructure (Φ : L₁ →ᵥ L₂) {M : Type w} (S : Structure L₂ M) : Structure L₁ M where
  func := fun f => S.func (Φ.onFunc f)
  rel := fun r => S.rel (Φ.onRel r)

instance subLanguageStructure {pf : ∀ k, Language.func L k → Prop} {pr : ∀ k, L.rel k → Prop}
  {M : Type w} (s : Structure L M) : Structure (subLanguage L pf pr) M :=
  onStructure (ofSubLanguage L) s

noncomputable def extendStructure (Φ : L₁ →ᵥ L₂) {M : Type w} [Inhabited M] (s : Structure L₁ M) : Structure L₂ M where
  func := fun {k} f₂ v => Classical.epsilon (fun y => ∃ f₁ : L₁.func k, Φ.onFunc f₁ = f₂ ∧ y = s.func f₁ v)
  rel  := fun {k} r₂ v => ∃ r₁ : L₁.rel k, Φ.onRel r₁ = r₂ ∧ s.rel r₁ v

end Hom
end Language

namespace FirstOrder

namespace Structure

instance [Inhabited M] : Inhabited (Structure L M) :=
⟨{ func := fun _ _ => default, rel := fun _ _ => True }⟩

variable (Φ : L₁ →ᵥ L₂) {M : Type w} (s₂ : Structure L₂ M)

@[simp] lemma onStructure_func {k} {f : L₁.func k} {v : Fin k → M} :
    (Φ.onStructure s₂).func f v = s₂.func (Φ.onFunc f) v := rfl

@[simp] lemma onStructure_rel {k} {r : L₁.rel k} {v : Fin k → M} :
    (Φ.onStructure s₂).rel r v ↔ s₂.rel (Φ.onRel r) v := of_eq rfl

variable [Inhabited M] (s₁ : Structure L₁ M)

lemma extendStructure_func
  {k} (injf : Function.Injective (Φ.onFunc : L₁.func k → L₂.func k)) (f₁ : L₁.func k) (v : Fin k → M) :
    (Φ.extendStructure s₁).func (Φ.onFunc f₁) v = s₁.func f₁ v := by
  simp[Language.Hom.extendStructure]
  have : ∃ y, ∃ f₁' : L₁.func k, Φ.onFunc f₁' = Φ.onFunc f₁ ∧ y = s₁.func f₁' v := ⟨s₁.func f₁ v, f₁, rfl, rfl⟩
  rcases Classical.epsilon_spec this with ⟨f', f'eq, h⟩
  rcases injf f'eq with rfl; exact h

lemma extendStructure_rel
  {k} (injr : Function.Injective (Φ.onRel : L₁.rel k → L₂.rel k)) (r₁ : L₁.rel k) (v : Fin k → M) :
    (Φ.extendStructure s₁).rel (Φ.onRel r₁) v ↔ s₁.rel r₁ v := by
  simp[Language.Hom.extendStructure]
  refine ⟨by intros h; rcases h with ⟨r₁', e, h⟩; rcases injr e; exact h, by intros h; refine ⟨r₁, rfl, h⟩⟩

class Eq (L : Language.{u}) [L.Eq] (M : Type w) [s : Structure L M] where
  eq : ∀ a b, s.rel Language.Eq.eq ![a, b] ↔ a = b

attribute [simp] Eq.eq

end Structure

end FirstOrder

namespace SubTerm

open FirstOrder

variable {M : Type w} (s : Structure L M) {n n₁ n₂ : ℕ} (e : Fin n → M) (e₂ : Fin n₂ → M) (ε : μ → M) (ε₂ : μ₂ → M)

def val : SubTerm L μ n → M
  | #x       => e x
  | &x       => ε x
  | func f v => s.func f (fun i => (v i).val)

abbrev bVal (t : SubTerm L Empty n) : M := t.val s e Empty.elim

variable (M) {s}

abbrev val! [s : Structure L M] {n} (e : Fin n → M) (ε : μ → M) : SubTerm L μ n → M := val s e ε

abbrev bVal! [s : Structure L M] {n} (e : Fin n → M) : SubTerm L Empty n → M := bVal s e

variable {M e e₂ ε ε₂}

@[simp] lemma val_bvar (x) : val s e ε (#x : SubTerm L μ n) = e x := rfl

@[simp] lemma val_fvar (x) : val s e ε (&x : SubTerm L μ n) = ε x := rfl

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

lemma val_bind (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (t : SubTerm L μ₁ n₁) :
    (bind bound free t).val s e₂ ε₂ = t.val s (val s e₂ ε₂ ∘ bound) (val s e₂ ε₂ ∘ free) :=
  by induction t <;> simp[*, bind_func, val_func]

lemma val_map (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (t : SubTerm L μ₁ n₁) :
    (map bound free t).val s e₂ ε₂ = t.val s (e₂ ∘ bound) (ε₂ ∘ free) := val_bind _ _ _

/-
lemma val_subst (u : SubTerm L μ n) (t : SubTerm L μ (n + 1)) :
    (subst u t).val s e ε = t.val s (e <: u.val s e ε) ε :=
  by simp[subst, val_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)
-/

lemma val_substs {n'} (w : Fin n' → SubTerm L μ n) (t : SubTerm L μ n') :
    (substs w t).val s e ε = t.val s (fun x => (w x).val s e ε) ε :=
  by simp[substs, val_bind]; congr

@[simp] lemma val_bShift (a : M) (t : SubTerm L μ n) :
    t.bShift.val s (a :> e) ε = t.val s e ε := by simp[bShift, val_map, Function.comp]

section Language

variable (Φ : L₁ →ᵥ L₂) (e : Fin n → M) (ε : μ → M)

lemma val_onSubTerm (s₂ : Structure L₂ M) {t : SubTerm L₁ μ n} :
    val s₂ e ε (Φ.onSubTerm t) = val (Φ.onStructure s₂) e ε t :=
  by induction t <;> simp[*, val!, Function.comp, val_func, Language.Hom.onSubTerm_func]

variable [Inhabited M]

lemma val_extendStructure_onSubTerm
    (injf : ∀ k, Function.Injective (Φ.onFunc : L₁.func k → L₂.func k))
    (s₁ : Structure L₁ M) (t : SubTerm L₁ μ n) :
    val (Φ.extendStructure s₁) e ε (Φ.onSubTerm t) = val s₁ e ε t := by
  induction t <;> simp[*, Language.Hom.onSubTerm_func, val_func]
  case func k f v ih => 
    exact Structure.extendStructure_func Φ s₁ (injf k) f (fun i => val s₁ e ε (v i))

end Language

section Syntactic

variable (ε : ℕ → M)

lemma val_shift (t : SyntacticSubTerm L n) :
    t.shift.val s e ε = t.val s e (ε ∘ Nat.succ) := by simp[shift, val_map]

lemma val_free (a : M) (t : SyntacticSubTerm L (n + 1)) :
    t.free.val s e (a :>ₙ ε) = t.val s (e <: a) ε :=
  by simp[free, val_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma val_fix (a : M) (t : SyntacticSubTerm L n) :
    t.fix.val s (e <: a) ε = t.val s e (a :>ₙ ε) :=
  by simp[fix, val_bind, Function.comp]; congr; exact funext (Nat.cases (by simp) (by simp))

end Syntactic

end SubTerm

namespace FirstOrder

namespace Structure

namespace ClosedSubset
variable {M : Type w} [s : Structure L M] (u : ClosedSubset L M)

lemma closed {k} (f : L.func k) {v : Fin k → M} (hv : ∀ i, v i ∈ u) : s.func f v ∈ u := u.domain_closed f hv

instance toStructure [s : Structure L M] (u : ClosedSubset L M) : Structure L u where
  func := fun f v => ⟨s.func f (fun i => ↑(v i)), u.closed f (by simp)⟩
  rel := fun r v => s.rel r (fun i => ↑(v i))

lemma coe_func {k} (f : L.func k) (v : Fin k → u) : (u.toStructure.func f v : M) = s.func f (fun i => ↑(v i)) := rfl

lemma coe_rel {k} (r : L.rel k) (v : Fin k → u) : u.toStructure.rel r v ↔ s.rel r (fun i => ↑(v i)) := of_eq rfl

end ClosedSubset

namespace Hom
variable {M₁ : Type w₁} {M₂ : Type w₂} [s₁ : Structure L M₁] [s₂ : Structure L M₂] (φ : M₁ →ₛ[L] M₂)

lemma hom_func {k} (f : L.func k) (v : Fin k → M₁) :
  φ (s₁.func f v) = s₂.func f (φ ∘ v) := φ.toFun_func' f v

lemma hom_rel {k} (r : L.rel k) (v : Fin k → M₁) :
  s₁.rel r v ↔ s₂.rel r (φ ∘ v) := φ.toFun_rel' r v

lemma hom_val (e : Fin n → M₁) (ε : μ → M₁) (t : SubTerm L μ n) :
    φ (t.val s₁ e ε) = t.val s₂ (φ ∘ e) (φ ∘ ε) := by
  induction t <;> simp[*, SubTerm.val_func, hom_func, Function.comp]

def eq_of_inj [L.Eq] [s₂.Eq] (h : Function.Injective φ) : s₁.Eq where
  eq := fun a b => by simp[φ.hom_rel, Matrix.comp_vecCons', Matrix.constant_eq_singleton, h.eq_iff, Function.comp]

def inclusion [s : Structure L M] (u : ClosedSubset L M) : u →ₛ[L] M where
  toFun := Subtype.val
  toFun_func' := by simp[ClosedSubset.coe_func]
  toFun_rel' := by simp[ClosedSubset.coe_rel]

end Hom

end Structure

namespace SubStructure
open Structure

variable {M : Type w} {M₁ : Type w₁} {M₂ : Type w₂}
  [s : Structure L M] [s₁ : Structure L M₁] [s₂ : Structure L M₂] [H : M₁ ⊆ₛ[L] M₂]

def eq_of_eq [L.Eq] [s₂.Eq] : s₁.Eq := H.inclusion.eq_of_inj H.inclusion_inj

instance closedSubset (u : ClosedSubset L M) : u ⊆ₛ[L] M where
  inclusion := Structure.Hom.inclusion u
  inclusion_inj := by simp[Structure.Hom.inclusion]; exact Subtype.val_injective

lemma inclusion_func {k} (f : L.func k) (v : Fin k → M₁) :
  H.inclusion (s₁.func f v) = s₂.func f (H.inclusion ∘ v) := H.inclusion.hom_func f v

lemma inclusion_val (e : Fin n → M₁) (ε : μ → M₁) (t : SubTerm L μ n) :
    H.inclusion (t.val s₁ e ε) = t.val s₂ (H.inclusion ∘ e) (H.inclusion ∘ ε) := 
  H.inclusion.hom_val e ε t
  
end SubStructure

end FirstOrder