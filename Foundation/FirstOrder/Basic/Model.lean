import Foundation.FirstOrder.Basic.Operator
import Foundation.FirstOrder.Basic.Semantics.Elementary

namespace LO

namespace FirstOrder

namespace Structure

structure Model (L : Language) (M : Type*) where
  intro : M

namespace Model

variable [Structure L M]

def equiv (L : Language) (M : Type*) : M ≃ Model L M where
  toFun := fun x => ⟨x⟩
  invFun := Model.intro
  left_inv := by intro x; simp
  right_inv := by rintro ⟨x⟩; simp

instance : Structure L (Model L M) := Structure.ofEquiv (equiv L M)

instance [h : Nonempty M] : Nonempty (Model L M) := by
  rcases h with ⟨x⟩; exact ⟨equiv L M x⟩

instance elementaryEquiv (L : Language) (M : Type*) [Nonempty M] [Structure L M] : M ≡ₑ[L] Model L M :=
  ElementaryEquiv.ofEquiv _

section

open Semiterm Semiformula

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

instance [Operator.Exp L] : Exp (Model L M) :=
  ⟨fun x => (@Operator.Exp.exp L _).val ![x]⟩

instance [Operator.Exp L] : Structure.Exp L (Model L M) := ⟨fun _ => rfl⟩

instance [Operator.Eq L] [Structure.Eq L M] : Structure.Eq L (Model L M) :=
  ⟨fun x y => by simp [operator_val_ofEquiv_iff]⟩

instance [Operator.LT L] : LT (Model L M) :=
  ⟨fun x y => (@Operator.LT.lt L _).val ![x, y]⟩

instance [Operator.LT L] : Structure.LT L (Model L M) := ⟨fun _ _ => iff_of_eq rfl⟩

instance [Operator.Mem L] : Membership (Model L M) (Model L M) :=
  ⟨fun x y => (@Operator.Mem.mem L _).val ![y, x]⟩

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

@[simp] lemma func_sigma_inl {k} (f : L₁.Func k) (v : Fin k → M) :
    (add L₁ L₂ M).func (Sum.inl f) v = func f v := rfl

@[simp] lemma func_sigma_inr {k} (f : L₂.Func k) (v : Fin k → M) :
    (add L₁ L₂ M).func (Sum.inr f) v = func f v := rfl

@[simp] lemma rel_sigma_inl {k} (r : L₁.Rel k) (v : Fin k → M) :
    (add L₁ L₂ M).rel (Sum.inl r) v ↔ rel r v := iff_of_eq rfl

@[simp] lemma rel_sigma_inr {k} (r : L₂.Rel k) (v : Fin k → M) :
    (add L₁ L₂ M).rel (Sum.inr r) v ↔ rel r v := iff_of_eq rfl

@[simp] lemma val_lMap_add₁ {n} (t : Semiterm L₁ μ n) (e : Fin n → M) (ε : μ → M) :
    Semiterm.val (add L₁ L₂ M) e ε (t.lMap (Language.Hom.add₁ L₁ L₂)) = t.val str₁ e ε := by
  induction t <;> simp [Semiterm.lMap_func, Semiterm.val, Language.Hom.func_add₁, *]

@[simp] lemma val_lMap_add₂ {n} (t : Semiterm L₂ μ n) (e : Fin n → M) (ε : μ → M) :
    Semiterm.val (add L₁ L₂ M) e ε (t.lMap (Language.Hom.add₂ L₁ L₂)) = t.val str₂ e ε := by
  induction t <;> simp [Semiterm.lMap_func, Semiterm.val, Language.Hom.func_add₂, *]

@[simp] lemma eval_lMap_add₁ {n} (φ : Semiformula L₁ μ n) (e : Fin n → M) (ε : μ → M) :
    Semiformula.Eval (add L₁ L₂ M) e ε (Semiformula.lMap (Language.Hom.add₁ L₁ L₂) φ)
    ↔ Semiformula.Eval str₁ e ε φ := by
  induction φ using Semiformula.rec' <;>
    simp [*, Language.Hom.rel_add₁, Semiformula.eval_rel,
      Semiformula.lMap_rel, Semiformula.eval_nrel, Semiformula.lMap_nrel]

@[simp] lemma eval_lMap_add₂ {n} (φ : Semiformula L₂ μ n) (e : Fin n → M) (ε : μ → M) :
    Semiformula.Eval (add L₁ L₂ M) e ε (Semiformula.lMap (Language.Hom.add₂ L₁ L₂) φ)
    ↔ Semiformula.Eval str₂ e ε φ := by
  induction φ using Semiformula.rec' <;>
    simp [*, Language.Hom.rel_add₂, Semiformula.eval_rel,
      Semiformula.lMap_rel, Semiformula.eval_nrel, Semiformula.lMap_nrel]

end add

section sigma

variable (L : ι → Language) (M : Type*) [str : (i : ι) → Structure (L i) M]

instance sigma : Structure (Language.sigma L) M where
  func := fun _ ⟨_, f⟩ v => func f v
  rel  := fun _ ⟨_, r⟩ v => rel r v

@[simp] lemma func_sigma {k} (f : (L i).Func k) (v : Fin k → M) : (sigma L M).func ⟨i, f⟩ v = func f v := rfl

@[simp] lemma rel_sigma {k} (r : (L i).Rel k) (v : Fin k → M) : (sigma L M).rel ⟨i, r⟩ v ↔ rel r v := iff_of_eq rfl

@[simp] lemma val_lMap_sigma {n} (t : Semiterm (L i) μ n) (e : Fin n → M) (ε : μ → M) :
    Semiterm.val (sigma L M) e ε (t.lMap (Language.Hom.sigma L i)) = t.val (str i) e ε := by
  induction t <;> simp [Semiterm.lMap_func, Semiterm.val, Language.Hom.func_sigma, *]

@[simp] lemma eval_lMap_sigma {n} (φ : Semiformula (L i) μ n) (e : Fin n → M) (ε : μ → M) :
    Semiformula.Eval (sigma L M) e ε (Semiformula.lMap (Language.Hom.sigma L i) φ)
    ↔ Semiformula.Eval (str i) e ε φ := by
  induction φ using Semiformula.rec' <;>
    simp [*, Language.Hom.rel_sigma, Semiformula.eval_rel,
      Semiformula.lMap_rel, Semiformula.eval_nrel, Semiformula.lMap_nrel]

end sigma

end Structure

section ULift

variable {L : Language.{u}} {M : Type v} [Structure L M]

instance : Structure L (ULift.{v'} M) where
  func := fun _ f v ↦ ⟨Structure.func f fun i ↦ (v i).down⟩
  rel := fun _ r v ↦ Structure.rel r fun i ↦ (v i).down

@[simp] lemma Structure.func_uLift {k} (f : L.Func k) (v : Fin k → ULift.{v'} M) :
    Structure.func f v = ⟨Structure.func f fun i ↦ (v i).down⟩ := rfl

@[simp] lemma Structure.rel_uLift {k} (r : L.Rel k) (v : Fin k → ULift.{v'} M) :
    Structure.rel r v = Structure.rel r fun i ↦ (v i).down := rfl

lemma Semiterm.valm_uLift {e : Fin n → ULift.{v'} M} {ε : ξ → ULift.{v'} M} {t : Semiterm L ξ n} :
    Semiterm.valm (ULift.{v'} M) e ε t = ⟨Semiterm.valm M (fun i ↦ (e i).down) (fun i ↦ (ε i).down) t⟩ := by
  induction t <;> simp [*, Semiterm.val_func]

lemma Semiformula.evalm_uLift {e : Fin n → ULift.{v'} M} {ε : ξ → ULift.{v'} M} {φ : Semiformula L ξ n} :
    Semiformula.Evalm (ULift.{v'} M) e ε φ ↔ Semiformula.Evalm M (fun i ↦ (e i).down) (fun i ↦ (ε i).down) φ := by
  induction φ using Semiformula.rec' <;>
    simp [*, Semiformula.eval_rel, Semiformula.eval_nrel, Semiterm.valm_uLift, Matrix.comp_vecCons']

variable (L M)

lemma uLift_elementaryEquiv [Nonempty M] : ULift.{v'} M ≡ₑ[L] M := ⟨by
  intro σ; simp [models_iff, Semiformula.evalm_uLift, Matrix.empty_eq, Empty.eq_elim]⟩

end ULift

end FirstOrder

end LO
