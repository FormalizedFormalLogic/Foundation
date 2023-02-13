import Logic.Predicate.Term

universe u u₁ u₂ v v₁ v₂ w w₁ w₂

variable
  {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}}
  {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂}

@[ext] class Structure₁ (L : Language.{u}) (M : Type w) :=
  (func : {k : ℕ} → L.func k → (Fin k → M) → M)
  (rel : {k : ℕ} → L.rel  k → (Fin k → M) → Prop)

namespace Language
namespace Hom

/-
set_option linter.unusedVariables false in
def onModel₁ (Φ : L₁ →ᵥ L₂) (M₂ : Type w₂) [Structure₁ L₂ M₂] := M₂

def cast (Φ : L₁ →ᵥ L₂) {M₂ : Type w₂} [Structure₁ L₂ M₂] (a : M₂) : Φ.onModel₁ M₂ := a

def uncast (Φ : L₁ →ᵥ L₂) {M₂ : Type w₂} [Structure₁ L₂ M₂] (a : Φ.onModel₁ M₂) : M₂ := a

variable {Φ : L₁ →ᵥ L₂} {M₂ : Type w₂} [Structure₁ L₂ M₂]

instance [Inhabited M₂] : Inhabited (Φ.onModel₁ M₂) := ⟨Φ.cast default⟩

@[simp] lemma uncast_cast (a : M₂) : Φ.uncast (Φ.cast a) = a := rfl

@[simp] lemma cast_uncast (a : Φ.onModel₁ M₂) : Φ.cast (Φ.uncast a) = a := rfl

lemma cast_injective : Function.Injective (Φ.cast : M₂ → Φ.onModel₁ M₂) := fun _ _ => id

lemma uncast_injective : Function.Injective (Φ.uncast : Φ.onModel₁ M₂ → M₂) := fun _ _ => id

@[simp] lemma cast_inj_iff (a b : M₂) : Φ.cast a = Φ.cast b ↔ a = b := cast_injective.eq_iff

@[simp] lemma uncast_inj_iff (a b : Φ.onModel₁ M₂) : Φ.uncast a = Φ.uncast b ↔ a = b := uncast_injective.eq_iff

attribute [irreducible] onModel₁
-/

def onStructure₁ (Φ : L₁ →ᵥ L₂) {M : Type w} (S : Structure₁ L₂ M) : Structure₁ L₁ M where
  func := fun f => S.func (Φ.onFunc f)
  rel := fun r => S.rel (Φ.onRel r)

instance subLanguageStructure₁ {pfunc : ∀ k, Language.func L k → Prop} {prel : ∀ k, L.rel k → Prop}
  {M : Type w} [s : Structure₁ L M] : Structure₁ (subLanguage L pfunc prel) M :=
  onStructure₁ (ofSub L) s

end Hom
end Language

namespace Structure₁

instance [Inhabited M] : Inhabited (Structure₁ L M) :=
⟨{ func := fun _ _ => default, rel := fun _ _ => True }⟩

variable (Φ : L₁ →ᵥ L₂) {M : Type w} (S : Structure₁ L₂ M)

/-
instance [Structure₁ L₂ M₂] : Structure₁ L₁ (Φ.onModel₁ M₂) where
  func := fun f v => Φ.cast $ Structure₁.func (Φ.onFunc f) (Φ.uncast ∘ v)
  rel := fun r v => Structure₁.rel (Φ.onRel r) (Φ.uncast ∘ v)

@[simp] lemma onModel₁_func {k} {f : L₁.func k} {v : Fin k → Φ.onModel₁ M₂} :
    func f v = (Φ.cast $ func (Φ.onFunc f) (Φ.uncast ∘ v)) := rfl

@[simp] lemma onModel₁_rel {k} {r : L₁.rel k} {v : Fin k → Φ.onModel₁ M₂} :
    rel r v ↔ rel (Φ.onRel r) (Φ.uncast ∘ v) := of_eq rfl
-/

@[simp] lemma onStructure₁_func {k} {f : L₁.func k} {v : Fin k → M} :
    (Φ.onStructure₁ S).func f v = S.func (Φ.onFunc f) v := rfl

@[simp] lemma onStructure₁_rel {k} {r : L₁.rel k} {v : Fin k → M} :
    (Φ.onStructure₁ S).rel r v ↔ S.rel (Φ.onRel r) v := of_eq rfl

end Structure₁

namespace SubTerm

variable {M} (s : Structure₁ L M) {n n₁ n₂ : ℕ} (e : Fin n → M) (e₂ : Fin n₂ → M) (ε : μ → M) (ε₂ : μ₂ → M)

def val : SubTerm L μ n → M
  | #x       => e x
  | &x       => ε x
  | func f v => s.func f (fun i => (v i).val)

variable (M) {s}

@[reducible] def val! [s : Structure₁ L M] {n} (e : Fin n → M) (ε : μ → M) : SubTerm L μ n → M := val s e ε

variable {M e e₂ ε ε₂}

@[simp] lemma val_fixedVar (x) : val s e ε (#x : SubTerm L μ n) = e x := rfl

@[simp] lemma val_freeVar (x) : val s e ε (&x : SubTerm L μ n) = ε x := rfl

@[simp] lemma val_func {k} (f : L.func k) (v) :
    val s e ε (func f v) = s.func f (fun i => (v i).val s e ε) := rfl
  
lemma val_bind (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (t : SubTerm L μ₁ n₁) :
    (bind fixed free t).val s e₂ ε₂ = t.val s (val s e₂ ε₂ ∘ fixed) (val s e₂ ε₂ ∘ free) :=
  by induction t <;> simp[*]

lemma val_map (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (t : SubTerm L μ₁ n₁) :
    (map fixed free t).val s e₂ ε₂ = t.val s (e₂ ∘ fixed) (ε₂ ∘ free) := val_bind _ _ _

lemma val_subst (u : SubTerm L μ n) (t : SubTerm L μ (n + 1)) :
    (subst u t).val s e ε = t.val s (e <: u.val s e ε) ε :=
  by simp[subst, val_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

@[simp] lemma val_fixedSucc (a : M) (t : SubTerm L μ n) :
    t.fixedSucc.val s (a :> e) ε = t.val s e ε := by simp[fixedSucc, val_map, Function.comp]

section onStructure₁
variable (Φ : L₁ →ᵥ L₂) (s : Structure₁ L₂ M) (e : Fin n → M) (ε : μ → M)

lemma val_onSubTerm {t : SubTerm L₁ μ n} :
    val s e ε (Φ.onSubTerm t) = val (Φ.onStructure₁ s) e ε t :=
  by induction t <;> simp[*, val!, Function.comp]

end onStructure₁

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


