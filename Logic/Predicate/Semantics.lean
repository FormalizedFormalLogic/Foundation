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

def onStructure₁ (Φ : L₁ →ᵥ L₂) {M : Type w} (S : Structure₁ L₂ M) : Structure₁ L₁ M where
  func := fun f => S.func (Φ.onFunc f)
  rel := fun r => S.rel (Φ.onRel r)

end Hom
end Language

namespace Structure₁

instance [Inhabited M] : Inhabited (Structure₁ L M) :=
⟨{ func := fun _ _ => default, rel := fun _ _ => True }⟩

variable (Φ : L₁ →ᵥ L₂) {M : Type w} (s₂ : Structure₁ L₂ M)

@[simp] lemma onStructure₁_func {k} {f : L₁.func k} {v : Fin k → M} :
    (Φ.onStructure₁ s₂).func f v = s₂.func (Φ.onFunc f) v := rfl

@[simp] lemma onStructure₁_rel {k} {r : L₁.rel k} {v : Fin k → M} :
    (Φ.onStructure₁ s₂).rel r v ↔ s₂.rel (Φ.onRel r) v := of_eq rfl

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

section Language
variable (Φ : L₁ →ᵥ L₂) (e : Fin n → M) (ε : μ → M)

lemma val_onSubTerm (s₂ : Structure₁ L₂ M) {t : SubTerm L₁ μ n} :
    val s₂ e ε (Φ.onSubTerm t) = val (Φ.onStructure₁ s₂) e ε t :=
  by induction t <;> simp[*, val!, Function.comp]

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