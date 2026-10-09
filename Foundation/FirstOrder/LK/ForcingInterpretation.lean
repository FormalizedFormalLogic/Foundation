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

variable {L K : Language} [L.Eq] {T : Theory L} [𝗘𝗤 L ⪯ T] {ξ : Type*} {n : ℕ}

variable (𝔭 : ForcingTranslation T K)

/-- Universal quantification over conditions stronger than `p`. -/
def allCond (p : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∀¹[𝔭.isCond.operator ![#0] ⋏ 𝔭.strongerThan.operator ![#0, Rew.bShift p]] φ

/-- Universal quantification over the domain at `p`. -/
def fal (p : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∀¹[𝔭.domain.operator ![Rew.bShift p, #0]] φ

/-- Existential quantification over the domain at `p`. -/
def exs (p : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∃¹[𝔭.domain.operator ![Rew.bShift p, #0]] φ

notation:64 "∀≤[" 𝔭 ", " p "] " φ => allCond 𝔭 p φ
notation:64 "∀_[" 𝔭 ", " p "] " φ => fal 𝔭 p φ
notation:64 "∃_[" 𝔭 ", " p "] " φ => exs 𝔭 p φ

end ForcingTranslation

namespace BinderNotation

open Lean

syntax:max "∀ " ident " ≤[" term "] " first_order_term ", "
  first_order_formula:0 : first_order_formula
syntax:max "∀ " ident " ∈[" term "] " first_order_term ", "
  first_order_formula:0 : first_order_formula
syntax:max "∃ " ident " ∈[" term "] " first_order_term ", "
  first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀ $q ≤[$𝔭] $p, $φ ]) => do
    if binders.elem q then Macro.throwErrorAt q "error: variable is duplicated."
    `(∀≤[$𝔭, ⤫term($type)[ $binders* | $fbinders* | $p ]]
      ⤫formula($type)[ $q $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀ $x ∈[$𝔭] $p, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated."
    `(∀_[$𝔭, ⤫term($type)[ $binders* | $fbinders* | $p ]]
      ⤫formula($type)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃ $x ∈[$𝔭] $p, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated."
    `(∃_[$𝔭, ⤫term($type)[ $binders* | $fbinders* | $p ]]
      ⤫formula($type)[ $x $binders* | $fbinders* | $φ ])

end BinderNotation

namespace ForcingTranslation

variable {L K : Language} [L.Eq] {T : Theory L} [𝗘𝗤 L ⪯ T] {ξ : Type*} {n : ℕ}
variable (𝔭 : ForcingTranslation T K)

/-- The value of a term, with the condition and value preceding the original variables. -/
def varEqual {n} : Semiterm K ξ n → Semiformula L ξ (n + 2)
  | #x => “p y. %𝔭.domain p y ∧ y = #x.succ.succ”
  | &x => “p y. %𝔭.domain p y ∧ y = &x”
  | .func (arity := k) f v =>
    “p y. %𝔭.domain p y” ⋏ ∃¹^[k] (
      (Matrix.conj fun i ↦
        varEqual (v i) ⇜
          (#((0 : Fin (n + 2)).addNat k) :> #(i.addCast (n + 2)) :>
            fun j ↦ #(j.succ.succ.addNat k))) ⋏
      (𝔭.func f).operator
        (#((0 : Fin (n + 2)).addNat k) :> #((1 : Fin (n + 2)).addNat k) :>
          fun i ↦ #(i.addCast (n + 2))))

def translateRel {k} (R : K.Rel k) (v : Fin k → Semiterm K ξ n) : Semiformula L ξ (n + 1) :=
  ∃¹^[k] (
    (Matrix.conj fun i ↦
      𝔭.varEqual (v i) ⇜
        (#((0 : Fin (n + 1)).addNat k) :> #(i.addCast (n + 1)) :>
          fun j ↦ #(j.succ.addNat k))) ⋏
    (𝔭.rel R).operator
      (#((0 : Fin (n + 1)).addNat k) :> fun i ↦ #(i.addCast (n + 1))))

/-- Internal description of `p ⊩ φ`, with the condition at bound variable zero. -/
def translationᵢ {n} : Semiformulaᵢ K ξ n → Semiformula L ξ (n + 1)
  | .rel R v => 𝔭.translateRel R v
  | ⊥ => ⊥
  | φ ⋏ ψ => translationᵢ φ ⋏ translationᵢ ψ
  | φ ⋎ ψ => translationᵢ φ ⋎ translationᵢ ψ
  | φ 🡒 ψ => “p. ∀ q ≤[𝔭] p, !(translationᵢ φ) q ⋯ → !(translationᵢ ψ) q ⋯”
  | ∀¹ φ => “p. ∀ q ≤[𝔭] p, ∀ x ∈[𝔭] q, !(translationᵢ φ) q x ⋯”
  | ∃¹ φ => “p. ∃ x ∈[𝔭] p, !(translationᵢ φ) p x ⋯”

def translation {n} : Semiformula K ξ n → Semiformula L ξ (n + 1) := fun φ ↦ 𝔭.translationᵢ φᴺ

def interpret (φ : Semiformula K ξ n) : Semiformula L ξ n :=
  “∀ p, %𝔭.isCond p → !(𝔭.translation φ) p ⋯”

section semantics

variable {M : Type*} [Tarski.Structure L M]

def IsCond (x : M) : Prop := 𝔭.isCond.val ![x]

variable (M)

abbrev Condition := {x : M // 𝔭.IsCond x}

variable {M}

section

variable {𝔭} {bv : Fin n → M} {fv : ξ → M}
variable {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)}

@[simp] lemma eval_allCond :
    (∀≤[𝔭, t] φ).Eval bv fv ↔ ∀ q : 𝔭.Condition M,
      𝔭.strongerThan.val ![(q : M), t.val bv fv] → φ.Eval ((q : M) :> bv) fv := by
  simp [allCond, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton, Subtype.forall, IsCond]

@[simp] lemma eval_fal :
    (∀_[𝔭, t] φ).Eval bv fv ↔
      ∀ x : {x : M // 𝔭.domain.val ![t.val bv fv, x]}, φ.Eval (x.val :> bv) fv := by
  simp [fal, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton, Subtype.forall]

@[simp] lemma eval_exs :
    (∃_[𝔭, t] φ).Eval bv fv ↔
      ∃ x : {x : M // 𝔭.domain.val ![t.val bv fv, x]}, φ.Eval (x.val :> bv) fv := by
  simp [exs, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton, Subtype.exists]

end

variable [Nonempty M] [M↓[L] ⊧* T]

instance : Preorder (𝔭.Condition M) where
  le p q := 𝔭.strongerThan.val ![(p : M), (q : M)]
  le_refl p := by
    have h : ∀ p : M, 𝔭.IsCond p → 𝔭.strongerThan.val ![p, p] := by
      simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
        Matrix.constant_eq_singleton] using
        models_of_provable (M := M) inferInstance 𝔭.strongerThan_refl
    exact h p p.prop
  le_trans p q r hpq hqr := by
    have h : ∀ p q r : M, 𝔭.IsCond p → 𝔭.IsCond q → 𝔭.IsCond r →
        𝔭.strongerThan.val ![p, q] → 𝔭.strongerThan.val ![q, r] →
        𝔭.strongerThan.val ![p, r] := by
      simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
        Matrix.constant_eq_singleton] using
        models_of_provable (M := M) inferInstance 𝔭.strongerThan_trans
    exact h p q r p.prop q.prop r.prop hpq hqr

lemma condition_le_iff {p q : 𝔭.Condition M} :
    p ≤ q ↔ 𝔭.strongerThan.val ![(p : M), (q : M)] := Iff.rfl

variable [K.Relational]

instance kripkeModel : Kripke.Model K (𝔭.Condition M) M where
  Domain p x := 𝔭.domain.val ![↑p, x]
  Rel p k R v := (𝔭.rel R).val (↑p :> v)
  domain_nonempty p := by
    have h : ∀ p : M, 𝔭.IsCond p → ∃ x, 𝔭.domain.val ![p, x] := by
      simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
        Matrix.constant_eq_singleton] using
        models_of_provable (M := M) inferInstance 𝔭.domain_nonempty
    exact h p p.prop
  domain_antimonotone := by
    intro p q hpq x hx
    have h : ∀ p q x : M, 𝔭.IsCond p → 𝔭.IsCond q →
        𝔭.strongerThan.val ![q, p] → 𝔭.domain.val ![p, x] → 𝔭.domain.val ![q, x] := by
      simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
        Matrix.constant_eq_singleton] using
        models_of_provable (M := M) inferInstance 𝔭.domain_monotone
    exact h p q x p.prop q.prop hpq hx
  rel_monotone := by
    intro p k R v hp q hqp
    have h : ∀ p q : M, ∀ v : Fin k → M, 𝔭.IsCond p → 𝔭.IsCond q →
        𝔭.strongerThan.val ![q, p] → (𝔭.rel R).val (p :> v) → (𝔭.rel R).val (q :> v) := by
      simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
        Matrix.constant_eq_singleton, Matrix.vecForall_iff] using
        models_of_provable (M := M) inferInstance (𝔭.rel_monotone R)
    exact h p q v p.prop q.prop hqp hp

variable {𝔭}

variable {p : 𝔭.Condition M} {bv : Fin n → M} {fv : ξ → M}

lemma forcesExists_iff {x : M} :
    p ⊩↓ x ↔ 𝔭.domain.val ![(p : M), x] := Iff.rfl

variable [Tarski.Structure.Eq L M]

private lemma eval_varEqual (t : Semiterm K ξ n) (y : M) :
    (𝔭.varEqual t).Eval ((p : M) :> y :> bv) fv ↔
      p ⊩↓ y ∧ y = t.relationalVal bv fv := by
  rcases t.bvar_or_fvar_of_relational with (⟨i, rfl⟩ | ⟨i, rfl⟩) <;>
    simp [varEqual, Semiformula.eval_operator, Matrix.comp_vecCons',
      Function.comp_def, Matrix.constant_eq_singleton, forcesExists_iff]

private lemma eval_translationᵢ_rel {k} (R : K.Rel k) (v : Fin k → Semiterm K ξ n)
    (hbv : ∀ i, p ⊩↓ bv i) (hfv : ∀ i, p ⊩↓ fv i) :
    (𝔭.translationᵢ (.rel R v)).Eval ((p : M) :> bv) fv ↔
      Kripke.Model.Forces p bv fv (.rel R v) := by
  have h : ∀ i, 𝔭.domain.val ![(p : M), (v i).relationalVal bv fv] := by
    intro i
    rcases (v i).bvar_or_fvar_of_relational with (⟨j, hj⟩ | ⟨j, hj⟩)
    · simpa [hj, forcesExists_iff] using hbv j
    · simpa [hj, forcesExists_iff] using hfv j
  simp [translationᵢ, translateRel, Matrix.comp_vecCons', Function.comp_def,
    eval_varEqual, forall_and, ← funext_iff, h, Kripke.Model.Forces, Kripke.Model.Rel,
    forcesExists_iff]

lemma eval_translationᵢ_iff_kripke {φ : Semiformulaᵢ K ξ n}
    (hbv : ∀ i, p ⊩↓ bv i) (hfv : ∀ i, p ⊩↓ fv i) :
    (𝔭.translationᵢ φ).Eval (↑p :> bv) fv ↔ Kripke.Model.Forces p bv fv φ := by
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
      (forall_congr' fun q : 𝔭.Condition M ↦ imp_congr_right fun hqp : q ≤ p ↦ by
        have hbq := fun i ↦ Kripke.Model.domain_monotone (hbv i) q hqp
        have hfq := fun i ↦ Kripke.Model.domain_monotone (hfv i) q hqp
        exact imp_congr (ihφ hbq hfq) (ihψ hbq hfq))
  | hAll φ ih =>
    simpa [translationᵢ, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton, Kripke.Model.Forces, Kripke.Model.Domain,
      Membership.mem, Set.Mem, condition_le_iff, forcesExists_iff] using
      (forall_congr' fun q : 𝔭.Condition M ↦ imp_congr_right fun hqp : q ≤ p ↦
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
    (𝔭.translation φ).Eval (↑p :> bv) fv ↔ Kripke.Model.WeaklyForces p bv fv φ :=
  eval_translationᵢ_iff_kripke hbv hfv

lemma models_translationᵢ {φ : Sentenceᵢ K} :
    (𝔭.translationᵢ φ).Evalb ![(p : M)] ↔ p ⊩ φ := eval_translationᵢ_iff_kripke (by simp) (by simp)

lemma models_translation {φ : Sentence K} :
    (𝔭.translation φ).Evalb ![(p : M)] ↔ p ⊩ᶜ φ := eval_translation_iff_kripke (by simp) (by simp)

lemma models_interpret {φ : Sentence K} :
    M↓[L] ⊧ 𝔭.interpret φ ↔ 𝔭.Condition M ∀⊩ᶜ φ := by
  simp [models_iff, interpret, ←models_translation]; rfl

end semantics

variable {U : Theory L} [T ⪯ U] [K.Relational] {V : Theory K}

structure Interpret (U : Theory L) [T ⪯ U] (V : Theory K) : Prop where
  proves_interpret : ∀ ψ ∈ V, U ⊢ 𝔭.interpret ψ

theorem soundness {φ : Sentence K} (H : 𝔭.Interpret U V) : V ⊢ φ → U ⊢ 𝔭.interpret φ := fun h ↦ by
  have : 𝗘𝗤 L ⪯ U := Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 L ⪯ T) (inferInstance : T ⪯ U)
  apply Theory.Proof.complete_on_eq_models.{_,0}
  intro M _ _ _ _
  have : M↓[L] ⊧* T := ModelsTheory.of_provably_subtheory M T U inferInstance
  apply 𝔭.models_interpret.mpr
  apply Kripke.Model.WeaklyForces₀.sound_theory h
  intro ψ hψ
  exact 𝔭.models_interpret.mp
    (models_of_provable (M := M) inferInstance (H.proves_interpret ψ hψ))

theorem soundness_consistency (H : 𝔭.Interpret U V) :
    Entailment.Consistent U → Entailment.Consistent V := by
  have : 𝗘𝗤 L ⪯ U := Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 L ⪯ T) (inferInstance : T ⪯ U)
  intro hT
  apply Entailment.consistent_iff_unprovable_bot.mpr
  intro hV
  apply Entailment.consistent_iff_unprovable_bot.mp hT
  apply Theory.Proof.complete_on_eq_models.{_,0}
  intro M _ _ _ _
  have : M↓[L] ⊧* T := ModelsTheory.of_provably_subtheory M T U inferInstance
  have h₁ : ∃ p : M, 𝔭.IsCond p := by
    simpa [models_iff, IsCond, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton] using
      models_of_provable (M := M) inferInstance 𝔭.condition_nonempty
  obtain ⟨p, hp⟩ := h₁
  have h₂ : 𝔭.Condition M ∀⊩ᶜ (⊥ : Sentence K) := 𝔭.models_interpret.mp
    (models_of_provable (M := M) inferInstance (𝔭.soundness H hV))
  simpa using h₂ ⟨p, hp⟩

end ForcingTranslation

end FFL.FirstOrder
