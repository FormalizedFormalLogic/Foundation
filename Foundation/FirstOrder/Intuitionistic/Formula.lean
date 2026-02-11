module

public import Foundation.FirstOrder.Basic

@[expose] public section
/-!
# Formulas of intuitionistic first-order logic

This file defines the formulas of first-order logic.

`φ : Semiformulaᵢ L ξ n` is a (semi-)formula of language `L` with bounded variables of `Fin n` and free variables of `ξ`.
The quantification is represented by de Bruijn index.

-/

namespace LO.FirstOrder

inductive Semiformulaᵢ (L : Language) (ξ : Type*) : ℕ → Type _ where
  | falsum : Semiformulaᵢ L ξ n
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformulaᵢ L ξ n
  |    and : Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n
  |     or : Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n
  |    imp : Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n
  |    all : Semiformulaᵢ L ξ (n + 1) → Semiformulaᵢ L ξ n
  |    exs : Semiformulaᵢ L ξ (n + 1) → Semiformulaᵢ L ξ n

abbrev Formulaᵢ (L : Language) (ξ : Type*) := Semiformulaᵢ L ξ 0

abbrev Sentenceᵢ (L : Language) := Formulaᵢ L Empty

abbrev Semisentenceᵢ (L : Language) (n : ℕ) := Semiformulaᵢ L Empty n

abbrev SyntacticSemiformulaᵢ (L : Language) (n : ℕ) := Semiformulaᵢ L ℕ n

abbrev SyntacticFormulaᵢ (L : Language) := SyntacticSemiformulaᵢ L 0

variable {L : Language}

namespace Semiformulaᵢ

instance : Bot (Semiformulaᵢ L ξ n) := ⟨falsum⟩

instance : Arrow (Semiformulaᵢ L ξ n) := ⟨imp⟩

abbrev neg (φ : Semiformulaᵢ L ξ n) : Semiformulaᵢ L ξ n := φ ➝ ⊥

abbrev verum : Semiformulaᵢ L ξ n := ⊥ ➝ ⊥

instance : LogicalConnective (Semiformulaᵢ L ξ n) where
  wedge := and
  vee := or
  top := verum
  tilde := neg

lemma neg_def (φ : Semiformulaᵢ L ξ n) : ∼φ = φ ➝ ⊥ := rfl

lemma verum_def : (⊤ : Semiformulaᵢ L ξ n) = ⊥ ➝ ⊥ := rfl

instance : Quantifier (Semiformulaᵢ L ξ) where
  all := all
  exs := exs

section ToString

variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)] [ToString ξ]

def toStr : ∀ {n}, Semiformulaᵢ L ξ n → String
  | _, ⊥ => "\\bot"
  | _, rel (arity := 0) r _ => "{" ++ toString r ++ "}"
  | _, rel (arity := _ + 1) r v => "{" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | _, φ ⋏ ψ => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | _, φ ⋎ ψ => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"
  | _, φ ➝ ψ => "\\left(" ++ toStr φ ++ " \\to "  ++ toStr ψ ++ "\\right)"
  | n, all φ => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr φ
  | n, exs φ => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr φ

instance : Repr (Semiformulaᵢ L ξ n) := ⟨fun t _ => toStr t⟩

instance : ToString (Semiformulaᵢ L ξ n) := ⟨toStr⟩

end ToString

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformulaᵢ L ξ n) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp [Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformulaᵢ L ξ n) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp [Vee.vee]

@[simp] lemma imp_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformulaᵢ L ξ n} :
    φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Arrow.arrow]

@[simp] lemma all_inj (φ ψ : Semiformulaᵢ L ξ (n + 1)) : ∀⁰ φ = ∀⁰ ψ ↔ φ = ψ := by
  simp [UnivQuantifier.all]

@[simp] lemma exs_inj (φ ψ : Semiformulaᵢ L ξ (n + 1)) : ∃⁰ φ = ∃⁰ ψ ↔ φ = ψ := by
  simp [ExsQuantifier.exs]

@[simp] lemma allClosure_inj (φ ψ : Semiformulaᵢ L ξ n) : ∀⁰* φ = ∀⁰* ψ ↔ φ = ψ := by
  induction n <;> simp [*, allClosure_succ]

@[simp] lemma exsClosure_inj (φ ψ : Semiformulaᵢ L ξ n) : ∃⁰* φ = ∃⁰* ψ ↔ φ = ψ := by
  induction n <;> simp [*, exsClosure_succ]

@[simp] lemma allItr_inj {k} (φ ψ : Semiformulaᵢ L ξ (n + k)) : ∀⁰^[k] φ = ∀⁰^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, allItr_succ]

@[simp] lemma exsItr_inj {k} (φ ψ : Semiformulaᵢ L ξ (n + k)) : ∃⁰^[k] φ = ∃⁰^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, exsItr_succ]

def complexity {n} : Semiformulaᵢ L ξ n → ℕ
|       ⊥ => 0
| rel _ _ => 0
|   φ ⋏ ψ => max φ.complexity ψ.complexity + 1
|   φ ⋎ ψ => max φ.complexity ψ.complexity + 1
|   φ ➝ ψ => max φ.complexity ψ.complexity + 1
|    ∀⁰ φ => φ.complexity + 1
|    ∃⁰ φ => φ.complexity + 1

@[simp] lemma complexity_top : complexity (⊤ : Semiformulaᵢ L ξ n) = 1 := rfl

@[simp] lemma complexity_bot : complexity (⊥ : Semiformulaᵢ L ξ n) = 0 := rfl

@[simp] lemma complexity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : complexity (rel r v) = 0 := rfl

@[simp] lemma complexity_and (φ ψ : Semiformulaᵢ L ξ n) : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_and' (φ ψ : Semiformulaᵢ L ξ n) : complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_or (φ ψ : Semiformulaᵢ L ξ n) : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_or' (φ ψ : Semiformulaᵢ L ξ n) : complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_imp (φ ψ : Semiformulaᵢ L ξ n) : complexity (φ ➝ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_imp' (φ ψ : Semiformulaᵢ L ξ n) : complexity (imp φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_all (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (∀⁰ φ) = φ.complexity + 1 := rfl
@[simp] lemma complexity_all' (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (all φ) = φ.complexity + 1 := rfl

@[simp] lemma complexity_exs (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (∃⁰ φ) = φ.complexity + 1 := rfl
@[simp] lemma complexity_exs' (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (exs φ) = φ.complexity + 1 := rfl

@[simp] lemma complexity_neg (φ : Semiformulaᵢ L ξ n) : complexity (∼φ) = complexity φ + 1 := by simp [neg_def]

@[elab_as_elim]
def cases' {C : ∀ n, Semiformulaᵢ L ξ n → Sort w}
  (hRel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hFalsum : ∀ {n : ℕ}, C n ⊥)
  (hAnd : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n (φ ⋏ ψ))
  (hOr : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n (φ ⋎ ψ))
  (hImp : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n (φ ➝ ψ))
  (hAll : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C n (∀⁰ φ))
  (hExs : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C n (∃⁰ φ)) {n} :
    (φ : Semiformulaᵢ L ξ n) → C n φ
  | rel r v => hRel r v
  |       ⊥ => hFalsum
  |   φ ⋏ ψ => hAnd φ ψ
  |   φ ⋎ ψ => hOr φ ψ
  |   φ ➝ ψ => hImp φ ψ
  |    ∀⁰ φ => hAll φ
  |    ∃⁰ φ => hExs φ

@[elab_as_elim]
def rec' {C : ∀ n, Semiformulaᵢ L ξ n → Sort w}
  (hRel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hFalsum : ∀ {n : ℕ}, C n ⊥)
  (hAnd : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n φ → C n ψ → C n (φ ⋏ ψ))
  (hOr : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n φ → C n ψ → C n (φ ⋎ ψ))
  (hImp : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n φ → C n ψ → C n (φ ➝ ψ))
  (hAll : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C (n + 1) φ → C n (∀⁰ φ))
  (hExs : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C (n + 1) φ → C n (∃⁰ φ)) {n} :
    (φ : Semiformulaᵢ L ξ n) → C n φ
  | rel r v => hRel r v
  |       ⊥ => hFalsum
  |   φ ⋏ ψ => hAnd φ ψ (rec' hRel hFalsum hAnd hOr hImp hAll hExs φ) (rec' hRel hFalsum hAnd hOr hImp hAll hExs ψ)
  |   φ ⋎ ψ => hOr φ ψ (rec' hRel hFalsum hAnd hOr hImp hAll hExs φ) (rec' hRel hFalsum hAnd hOr hImp hAll hExs ψ)
  |   φ ➝ ψ => hImp φ ψ (rec' hRel hFalsum hAnd hOr hImp hAll hExs φ) (rec' hRel hFalsum hAnd hOr hImp hAll hExs ψ)
  |    ∀⁰ φ => hAll φ (rec' hRel hFalsum hAnd hOr hImp hAll hExs φ)
  |    ∃⁰ φ => hExs φ (rec' hRel hFalsum hAnd hOr hImp hAll hExs φ)

section Decidable

variable [L.DecidableEq] [DecidableEq ξ]

def hasDecEq {n} : (φ ψ : Semiformulaᵢ L ξ n) → Decidable (φ = ψ)
  | ⊥, ψ => by cases ψ using cases' <;>
      { simp only [reduceCtorEq]; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | rel r v, ψ => by
      cases ψ using cases' <;> try { simpa using isFalse not_false }
      case hRel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simpa [h] using Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp [h])
        · exact isFalse (by simp [e])
  | φ ⋏ ψ, χ => by
      cases χ using cases' <;> try { simpa using isFalse not_false }
      case hAnd φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | φ ⋎ ψ, χ => by
      cases χ using cases' <;> try { simpa using isFalse not_false }
      case hOr φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | φ ➝ ψ, χ => by
      cases χ using cases' <;> try { simpa using isFalse not_false }
      case hImp φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | ∀⁰ φ, ψ => by
      cases ψ using cases' <;> try { simpa using isFalse not_false }
      case hAll φ' => simpa using hasDecEq φ φ'
  | ∃⁰ φ, ψ => by
      cases ψ using cases' <;> try { simpa using isFalse not_false }
      case hExs φ' => simpa using hasDecEq φ φ'

instance : DecidableEq (Semiformulaᵢ L ξ n) := hasDecEq

end Decidable

end Semiformulaᵢ

/-! ## (Weak) Negative formula -/

namespace Semiformulaᵢ

inductive IsNegative : Semiformulaᵢ L ξ n → Prop
  | falsum : IsNegative ⊥
  | and {φ ψ} : IsNegative φ → IsNegative ψ → IsNegative (φ ⋏ ψ)
  | imply {φ ψ} : IsNegative ψ → IsNegative (φ ➝ ψ)
  | all {φ} : IsNegative φ → IsNegative (∀⁰ φ)

attribute [simp] IsNegative.falsum

namespace IsNegative

@[simp] lemma and_iff {φ ψ : Semiformulaᵢ L ξ n} : (φ ⋏ ψ).IsNegative ↔ φ.IsNegative ∧ ψ.IsNegative :=
  ⟨by rintro ⟨⟩; simp_all, by rintro ⟨hφ, hψ⟩; exact .and hφ hψ⟩

@[simp] lemma imp_iff {φ ψ : Semiformulaᵢ L ξ n} : (φ ➝ ψ).IsNegative ↔ ψ.IsNegative :=
  ⟨by rintro ⟨⟩; simp_all, by rintro h; exact .imply h⟩

@[simp] lemma all_iff {φ : Semiformulaᵢ L ξ (n + 1)} : (∀⁰ φ).IsNegative ↔ φ.IsNegative :=
  ⟨by rintro ⟨⟩; simp_all, by rintro h; exact .all h⟩

@[simp] lemma verum : (⊤ : Semiformulaᵢ L ξ n).IsNegative := by simp [verum_def]

@[simp] lemma not_or {φ ψ : Semiformulaᵢ L ξ n} : ¬(φ ⋎ ψ).IsNegative := by rintro ⟨⟩

@[simp] lemma not_exs {φ : Semiformulaᵢ L ξ (n + 1)} : ¬(∃⁰ φ).IsNegative := by rintro ⟨⟩

@[simp] lemma not_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ¬(rel r v).IsNegative := by rintro ⟨⟩

@[simp] lemma neg (φ : Semiformulaᵢ L ξ n) : (∼φ).IsNegative := .imply .falsum

end IsNegative

end Semiformulaᵢ


end LO.FirstOrder
