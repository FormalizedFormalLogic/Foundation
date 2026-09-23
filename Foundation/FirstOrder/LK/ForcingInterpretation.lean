module

public import Foundation.FirstOrder.LK.Completeness.CounterModel
public import Foundation.FirstOrder.Kripke.Classical
public import Foundation.Vorspiel.ExistsUnique

/-!
# Forcing Interpretation

## References

- [Avi04, Sections 2.2–2.4]
-/

@[expose] public section

namespace FFL.FirstOrder

/-- A definable forcing structure with persistent function graphs. -/
structure ForcingTranslation {L : Language} [L.Eq] (T : Theory L) [𝗘𝗤 L ⪯ T] (K : Language) where
  isCond : Semiformula.Operator L 1
  /-- `strongerThan q p` means that `q` is stronger than `p`. -/
  strongerThan : Semiformula.Operator L 2
  domain : Semiformula.Operator L 2
  /-- The arguments are the condition followed by the relation's arguments. -/
  rel {k} : K.Rel k → Semiformula.Operator L (k + 1)
  /-- The arguments are the condition, the value, and the function's arguments. -/
  func {k} : K.Func k → Semiformula.Operator L (k + 2)
  condition_nonempty :
    T ⊢ “∃ p, %isCond p”
  strongerThan_refl :
    T ⊢ “∀ p, %isCond p → %strongerThan p p”
  strongerThan_trans :
    T ⊢ “∀ p q r, %isCond p → %isCond q → %isCond r →
      %strongerThan p q → %strongerThan q r → %strongerThan p r”
  domain_nonempty :
    T ⊢ “∀ p, %isCond p → ∃ x, %domain p x”
  domain_monotone :
    T ⊢ “∀ p q x, %isCond p → %isCond q → %strongerThan q p → %domain p x → %domain q x”
  rel_monotone {k} (R : K.Rel k) :
    T ⊢ ∀¹* “p q. %isCond p → %isCond q → %strongerThan q p →
      %(rel R) p ⋯ → %(rel R) q ⋯”
  func_defined {k} (f : K.Func k) :
    T ⊢ ∀¹* “p. %isCond p → (⋀ i, %domain p #(i : Fin k).succ) →
      ∃! y, %domain p y ∧ %(func f) p y ⋯”
  func_monotone {k} (f : K.Func k) :
    T ⊢ ∀¹* “p q y. %isCond p → %isCond q → %strongerThan q p →
      (⋀ i, %domain p #(i : Fin k).succ.succ.succ) → %domain p y →
      %(func f) p y ⋯ → %(func f) q y ⋯”

namespace ForcingTranslation

variable {L K : Language} [L.Eq] {T : Theory L} [𝗘𝗤 L ⪯ T]

variable (ℙ : ForcingTranslation T K)

/-- Universal quantification over conditions stronger than `p`. -/
def allCond (p : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∀¹[ℙ.isCond.operator ![#0] ⋏ ℙ.strongerThan.operator ![#0, Rew.bShift p]] φ

/-- Universal quantification over the domain at `p`. -/
def fal (p : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∀¹[ℙ.domain.operator ![Rew.bShift p, #0]] φ

/-- Existential quantification over the domain at `p`. -/
def exs (p : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∃¹[ℙ.domain.operator ![Rew.bShift p, #0]] φ

notation:64 "∀≤[" ℙ ", " p "] " φ => allCond ℙ p φ
notation:64 "∀_[" ℙ ", " p "] " φ => fal ℙ p φ
notation:64 "∃_[" ℙ ", " p "] " φ => exs ℙ p φ

end ForcingTranslation

namespace BinderNotation

open Lean

syntax:max "∀ " ident " ≤[" term "] " first_order_term ", " first_order_formula:0 : first_order_formula
syntax:max "∀ " ident " ∈[" term "] " first_order_term ", " first_order_formula:0 : first_order_formula
syntax:max "∃ " ident " ∈[" term "] " first_order_term ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀ $q ≤[$ℙ] $p, $φ ]) => do
    if binders.elem q then Macro.throwErrorAt q "error: variable is duplicated."
    `(∀≤[$ℙ, ⤫term($type)[ $binders* | $fbinders* | $p ]]
      ⤫formula($type)[ $q $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀ $x ∈[$ℙ] $p, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated."
    `(∀_[$ℙ, ⤫term($type)[ $binders* | $fbinders* | $p ]]
      ⤫formula($type)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃ $x ∈[$ℙ] $p, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated."
    `(∃_[$ℙ, ⤫term($type)[ $binders* | $fbinders* | $p ]]
      ⤫formula($type)[ $x $binders* | $fbinders* | $φ ])

end BinderNotation

namespace ForcingTranslation

variable {L K : Language} [L.Eq] {T : Theory L} [𝗘𝗤 L ⪯ T]
variable (ℙ : ForcingTranslation T K)

/-- The value of a term, with the condition and value preceding the original variables. -/
def varEqual {n} : Semiterm K ξ n → Semiformula L ξ (n + 2)
  | #x => “p y. %ℙ.domain p y ∧ y = #x.succ.succ”
  | &x => “p y. %ℙ.domain p y ∧ y = &x”
  | .func (arity := k) f v =>
    “p y. %ℙ.domain p y” ⋏ ∃¹^[k] (
      (Matrix.conj fun i ↦
        varEqual (v i) ⇜
          (#((0 : Fin (n + 2)).addNat k) :> #(i.addCast (n + 2)) :>
            fun j ↦ #(j.succ.succ.addNat k))) ⋏
      (ℙ.func f).operator
        (#((0 : Fin (n + 2)).addNat k) :> #((1 : Fin (n + 2)).addNat k) :>
          fun i ↦ #(i.addCast (n + 2))))

def translateRel {k} (R : K.Rel k) (v : Fin k → Semiterm K ξ n) : Semiformula L ξ (n + 1) :=
  ∃¹^[k] (
    (Matrix.conj fun i ↦
      ℙ.varEqual (v i) ⇜
        (#((0 : Fin (n + 1)).addNat k) :> #(i.addCast (n + 1)) :>
          fun j ↦ #(j.succ.addNat k))) ⋏
    (ℙ.rel R).operator
      (#((0 : Fin (n + 1)).addNat k) :> fun i ↦ #(i.addCast (n + 1))))

/-- Internal description of `p ⊩ φ`, with the condition at bound variable zero. -/
def translationᵢ {n} : Semiformulaᵢ K ξ n → Semiformula L ξ (n + 1)
  | .rel R v => ℙ.translateRel R v
  | ⊥ => ⊥
  | φ ⋏ ψ => translationᵢ φ ⋏ translationᵢ ψ
  | φ ⋎ ψ => translationᵢ φ ⋎ translationᵢ ψ
  | φ 🡒 ψ => “p. ∀ q ≤[ℙ] p, !(translationᵢ φ) q ⋯ → !(translationᵢ ψ) q ⋯”
  | ∀¹ φ => “p. ∀ q ≤[ℙ] p, ∀ x ∈[ℙ] q, !(translationᵢ φ) q x ⋯”
  | ∃¹ φ => “p. ∃ x ∈[ℙ] p, !(translationᵢ φ) p x ⋯”

def translation {n} : Semiformula K ξ n → Semiformula L ξ (n + 1) := fun φ ↦ ℙ.translationᵢ φᴺ

def interpret (φ : Semiformula K ξ n) : Semiformula L ξ n := “∀ p, %ℙ.isCond p → !(ℙ.translation φ) p ⋯”

section semantics

variable {M : Type*} [Tarski.Structure L M]

def IsCond (x : M) : Prop := ℙ.isCond.val ![x]

variable (M)

abbrev Condition := {x : M // ℙ.IsCond x}

variable {M}

section

variable {ℙ} {bv : Fin n → M} {fv : ξ → M}
variable {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)}

@[simp] lemma eval_allCond :
    (∀≤[ℙ, t] φ).Eval bv fv ↔ ∀ q : ℙ.Condition M,
      ℙ.strongerThan.val ![(q : M), t.val bv fv] → φ.Eval ((q : M) :> bv) fv := by
  simp [allCond, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton, Subtype.forall, IsCond]

@[simp] lemma eval_fal :
    (∀_[ℙ, t] φ).Eval bv fv ↔
      ∀ x : {x : M // ℙ.domain.val ![t.val bv fv, x]}, φ.Eval (x.val :> bv) fv := by
  simp [fal, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton, Subtype.forall]

@[simp] lemma eval_exs :
    (∃_[ℙ, t] φ).Eval bv fv ↔
      ∃ x : {x : M // ℙ.domain.val ![t.val bv fv, x]}, φ.Eval (x.val :> bv) fv := by
  simp [exs, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton, Subtype.exists]

end

variable [Nonempty M] [M↓[L] ⊧* T]

instance : Preorder (ℙ.Condition M) where
  le p q := ℙ.strongerThan.val ![(p : M), (q : M)]
  le_refl p := by
    have h : ∀ p : M, ℙ.IsCond p → ℙ.strongerThan.val ![p, p] := by
      simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
        Matrix.constant_eq_singleton] using
        models_of_provable (M := M) inferInstance ℙ.strongerThan_refl
    exact h p p.prop
  le_trans p q r hpq hqr := by
    have h : ∀ p q r : M, ℙ.IsCond p → ℙ.IsCond q → ℙ.IsCond r →
        ℙ.strongerThan.val ![p, q] → ℙ.strongerThan.val ![q, r] →
        ℙ.strongerThan.val ![p, r] := by
      simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
        Matrix.constant_eq_singleton] using
        models_of_provable (M := M) inferInstance ℙ.strongerThan_trans
    exact h p q r p.prop q.prop r.prop hpq hqr

lemma condition_le_iff {p q : ℙ.Condition M} :
    p ≤ q ↔ ℙ.strongerThan.val ![(p : M), (q : M)] := Iff.rfl

variable [K.Relational]

instance kripkeModel : Kripke.Model K (ℙ.Condition M) M where
  Domain p x := ℙ.domain.val ![↑p, x]
  Rel p k R v := (ℙ.rel R).val (↑p :> v)
  domain_nonempty p := by
    have h : ∀ p : M, ℙ.IsCond p → ∃ x, ℙ.domain.val ![p, x] := by
      simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
        Matrix.constant_eq_singleton] using
        models_of_provable (M := M) inferInstance ℙ.domain_nonempty
    exact h p p.prop
  domain_antimonotone := by
    intro p q hpq x hx
    have h : ∀ p q x : M, ℙ.IsCond p → ℙ.IsCond q →
        ℙ.strongerThan.val ![q, p] → ℙ.domain.val ![p, x] → ℙ.domain.val ![q, x] := by
      simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
        Matrix.constant_eq_singleton] using
        models_of_provable (M := M) inferInstance ℙ.domain_monotone
    exact h p q x p.prop q.prop hpq hx
  rel_monotone := by
    intro p k R v hp q hqp
    have h : ∀ p q : M, ∀ v : Fin k → M, ℙ.IsCond p → ℙ.IsCond q →
        ℙ.strongerThan.val ![q, p] → (ℙ.rel R).val (p :> v) → (ℙ.rel R).val (q :> v) := by
      simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
        Matrix.constant_eq_singleton, Matrix.vecForall_iff] using
        models_of_provable (M := M) inferInstance (ℙ.rel_monotone R)
    exact h p q v p.prop q.prop hqp hp

variable {ℙ}

variable {p : ℙ.Condition M} {bv : Fin n → M} {fv : ξ → M}

lemma forcesExists_iff {x : M} :
    p ⊩↓ x ↔ ℙ.domain.val ![(p : M), x] := Iff.rfl

variable [Tarski.Structure.Eq L M]

private lemma eval_varEqual (t : Semiterm K ξ n) (y : M) :
    (ℙ.varEqual t).Eval ((p : M) :> y :> bv) fv ↔
      p ⊩↓ y ∧ y = t.relationalVal bv fv := by
  rcases t.bvar_or_fvar_of_relational with (⟨i, rfl⟩ | ⟨i, rfl⟩) <;>
    simp [varEqual, Semiformula.eval_operator, Matrix.comp_vecCons',
      Function.comp_def, Matrix.constant_eq_singleton, forcesExists_iff]

private lemma eval_translationᵢ_rel {k} (R : K.Rel k) (v : Fin k → Semiterm K ξ n)
    (hbv : ∀ i, p ⊩↓ bv i) (hfv : ∀ i, p ⊩↓ fv i) :
    (ℙ.translationᵢ (.rel R v)).Eval ((p : M) :> bv) fv ↔
      Kripke.Model.Forces p bv fv (.rel R v) := by
  have h : ∀ i, ℙ.domain.val ![(p : M), (v i).relationalVal bv fv] := by
    intro i
    rcases (v i).bvar_or_fvar_of_relational with (⟨j, hj⟩ | ⟨j, hj⟩)
    . simpa [hj, forcesExists_iff] using hbv j
    . simpa [hj, forcesExists_iff] using hfv j
  simp [translationᵢ, translateRel, Matrix.comp_vecCons', Function.comp_def,
    eval_varEqual, forall_and, ← funext_iff, h, Kripke.Model.Forces, Kripke.Model.Rel, forcesExists_iff]

lemma eval_translationᵢ_iff_kripke {φ : Semiformulaᵢ K ξ n}
    (hbv : ∀ i, p ⊩↓ bv i) (hfv : ∀ i, p ⊩↓ fv i) :
    (ℙ.translationᵢ φ).Eval (↑p :> bv) fv ↔ Kripke.Model.Forces p bv fv φ := by
  induction φ using Semiformulaᵢ.rec' generalizing p with
  | hRel R v => exact eval_translationᵢ_rel R v hbv hfv
  | hFalsum => rfl
  | hAnd φ ψ ihφ ihψ =>
    exact and_congr (ihφ hbv hfv) (ihψ hbv hfv)
  | hOr φ ψ ihφ ihψ =>
    exact or_congr (ihφ hbv hfv) (ihψ hbv hfv)
  | hImp φ ψ ihφ ihψ =>
    simpa [translationᵢ, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton, Kripke.Model.Forces, condition_le_iff, forcesExists_iff] using
      (forall_congr' fun q : ℙ.Condition M ↦ imp_congr_right fun hqp : q ≤ p ↦ by
        have hbq := fun i ↦ Kripke.Model.domain_monotone (hbv i) q hqp
        have hfq := fun i ↦ Kripke.Model.domain_monotone (hfv i) q hqp
        exact imp_congr (ihφ hbq hfq) (ihψ hbq hfq))
  | hAll φ ih =>
    simpa [translationᵢ, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton, Kripke.Model.Forces, Kripke.Model.Domain,
      Membership.mem, Set.Mem, condition_le_iff, forcesExists_iff] using
      (forall_congr' fun q : ℙ.Condition M ↦ imp_congr_right fun hqp : q ≤ p ↦
        forall_congr' fun x : q ↦
          ih (bv := x.val :> bv)
            (Fin.cases x.prop (fun i ↦ Kripke.Model.domain_monotone (hbv i) q hqp))
            (fun i ↦ Kripke.Model.domain_monotone (hfv i) q hqp))
  | hExs φ ih =>
    simpa [translationᵢ, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton, Kripke.Model.Forces, Kripke.Model.Domain,
      Membership.mem, Set.Mem] using
      (exists_congr fun x : p ↦ ih (bv := x.val :> bv) (Fin.cases x.prop hbv) hfv)

lemma eval_translation_iff_kripke {φ : Semiformula K ξ n}
    (hbv : ∀ i, p ⊩↓ bv i) (hfv : ∀ i, p ⊩↓ fv i) :
    (ℙ.translation φ).Eval (↑p :> bv) fv ↔ Kripke.Model.WeaklyForces p bv fv φ :=
  eval_translationᵢ_iff_kripke hbv hfv

lemma models_translationᵢ {φ : Sentenceᵢ K} :
    (ℙ.translationᵢ φ).Evalb ![(p : M)] ↔ p ⊩ φ := eval_translationᵢ_iff_kripke (by simp) (by simp)

lemma models_translation {φ : Sentence K} :
    (ℙ.translation φ).Evalb ![(p : M)] ↔ p ⊩ᶜ φ := eval_translation_iff_kripke (by simp) (by simp)

lemma models_interpret {φ : Sentence K} :
    M↓[L] ⊧ ℙ.interpret φ ↔ ℙ.Condition M ∀⊩ᶜ φ := by
  simp [models_iff, interpret, ←models_translation]; rfl

end semantics

variable [K.Relational] {V : Theory K}

structure Interpret (V : Theory K) : Prop where
  proves_interpret : ∀ ψ ∈ V, T ⊢ ℙ.interpret ψ

theorem soundness (H : ℙ.Interpret V) : V ⊢ φ → T ⊢ ℙ.interpret φ := fun h ↦ by
  apply Theory.Proof.complete_on_eq_models.{_,0}
  intro M _ _ _ _
  apply ℙ.models_interpret.mpr
  apply Kripke.Model.WeaklyForces₀.sound_theory h
  intro ψ hψ
  exact ℙ.models_interpret.mp
    (models_of_provable (M := M) inferInstance (H.proves_interpret ψ hψ))

theorem soundness_consistency (H : ℙ.Interpret V) :
    Entailment.Consistent T → Entailment.Consistent V := by
  intro hT
  apply Entailment.consistent_iff_unprovable_bot.mpr
  intro hV
  apply Entailment.consistent_iff_unprovable_bot.mp hT
  apply Theory.Proof.complete_on_eq_models.{_,0}
  intro M _ _ _ _
  have h₁ : ∃ p : M, ℙ.IsCond p := by
    simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton] using
      models_of_provable (M := M) inferInstance ℙ.condition_nonempty
  obtain ⟨p, hp⟩ := h₁
  have h₂ : ℙ.Condition M ∀⊩ᶜ (⊥ : Sentence K) := ℙ.models_interpret.mp
    (models_of_provable (M := M) inferInstance (ℙ.soundness H hV))
  simpa using h₂ ⟨p, hp⟩

end ForcingTranslation

end FFL.FirstOrder
