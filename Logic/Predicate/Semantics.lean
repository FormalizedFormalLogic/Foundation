import Logic.Predicate.Term

variable {L : Language} {μ μ₁ μ₂ : Type _}

structure Structure₁ (L : Language.{u}) :=
(dom : Type u)
(domInhabited : Inhabited dom)
(func : {k : ℕ} → L.func k → (Fin k → dom) → dom)
(rel : {k : ℕ} → L.rel  k → (Fin k → dom) → Prop)

instance Structure₁_coe : CoeSort (Structure₁ L) (Type _) := ⟨Structure₁.dom⟩

instance Structure₁_Inhabited (S : Structure₁ L) : Inhabited S := S.domInhabited

namespace SubTerm
variable {n n₁ n₂ : ℕ} (S : Structure₁ L) (e : Fin n → S) (Φ : μ → S)

@[simp] def val : SubTerm L μ n → S
  | (#x)       => e x
  | (&x)       => Φ x
  | (func f v) => S.func f (fun i => (v i).val)

lemma val_bind (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (e : Fin n₂ → S) (Φ : μ₂ → S) (t : SubTerm L μ₁ n₁) :
    (bind fixed free t).val S e Φ = t.val S (fun x => val S e Φ (fixed x)) (fun x => val S e Φ (free x)) :=
  by induction t <;> simp[*]

lemma val_map (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (e : Fin n₂ → S) (Φ : μ₂ → S) (t : SubTerm L μ₁ n₁) :
    (map fixed free t).val S e Φ = t.val S (fun x => e (fixed x)) (fun x => Φ (free x)) := val_bind _ _ _ _ _ _

lemma val_subst (u : SubTerm L μ n) (t : SubTerm L μ (n + 1)) :
    (subst u t).val S e Φ = t.val S (e <: u.val S e Φ) Φ :=
  by simp[subst, val_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

@[simp] lemma val_fixedSucc (a : S) (t : SubTerm L μ n) :
    t.fixedSucc.val S (a :> e) Φ = t.val S e Φ := by simp[fixedSucc, val_map]

section Syntactic
variable (Ψ : ℕ → S)

lemma val_shift (t : SyntacticSubTerm L n) :
    t.shift.val S e Ψ = t.val S e (fun x => Ψ $ x + 1) := by simp[shift, val_map]

lemma val_free (a : S) (t : SyntacticSubTerm L (n + 1)) :
    t.free.val S e (a :>ₙ Ψ) = t.val S (e <: a) Ψ :=
  by simp[free, val_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma val_fix (a : S) (t : SyntacticSubTerm L n) :
    t.fix.val S (e <: a) Ψ = t.val S e (a :>ₙ Ψ) :=
  by simp[fix, val_bind]; congr; exact funext (Nat.cases (by simp) (by simp))

end Syntactic

end SubTerm


