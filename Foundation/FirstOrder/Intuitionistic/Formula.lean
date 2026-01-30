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
  | falsum {n} : Semiformulaᵢ L ξ n
  | rel    {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformulaᵢ L ξ n
  | and    {n} : Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n
  | or     {n} : Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n
  | imp    {n} : Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n
  | all    {n} : Semiformulaᵢ L ξ (n + 1) → Semiformulaᵢ L ξ n
  | ex     {n} : Semiformulaᵢ L ξ (n + 1) → Semiformulaᵢ L ξ n

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
  univ := all
  ex := ex

section ToString

variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)] [ToString ξ]

def toStr : ∀ {n}, Semiformulaᵢ L ξ n → String
  | _, ⊥                         => "\\bot"
  | _, rel (arity := 0) r _      => "{" ++ toString r ++ "}"
  | _, rel (arity := _ + 1) r v  => "{" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | _, φ ⋏ ψ                     => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | _, φ ⋎ ψ                     => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"
  | _, φ ➝ ψ                     => "\\left(" ++ toStr φ ++ " \\to "  ++ toStr ψ ++ "\\right)"
  | n, all φ                     => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr φ
  | n, ex φ                      => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr φ

instance : Repr (Semiformulaᵢ L ξ n) := ⟨fun t _ => toStr t⟩

instance : ToString (Semiformulaᵢ L ξ n) := ⟨toStr⟩

end ToString

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformulaᵢ L ξ n) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp [Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformulaᵢ L ξ n) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp [Vee.vee]

@[simp] lemma imp_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformulaᵢ L ξ n} :
    φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Arrow.arrow]

@[simp] lemma all_inj (φ ψ : Semiformulaᵢ L ξ (n + 1)) : ∀' φ = ∀' ψ ↔ φ = ψ := by
  simp [UnivQuantifier.univ]

@[simp] lemma ex_inj (φ ψ : Semiformulaᵢ L ξ (n + 1)) : ∃' φ = ∃' ψ ↔ φ = ψ := by
  simp [ExQuantifier.ex]

@[simp] lemma univClosure_inj (φ ψ : Semiformulaᵢ L ξ n) : ∀* φ = ∀* ψ ↔ φ = ψ := by
  induction n <;> simp [*, univClosure_succ]

@[simp] lemma exClosure_inj (φ ψ : Semiformulaᵢ L ξ n) : ∃* φ = ∃* ψ ↔ φ = ψ := by
  induction n <;> simp [*, exClosure_succ]

@[simp] lemma univItr_inj {k} (φ ψ : Semiformulaᵢ L ξ (n + k)) : ∀^[k] φ = ∀^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, univItr_succ]

@[simp] lemma exItr_inj {k} (φ ψ : Semiformulaᵢ L ξ (n + k)) : ∃^[k] φ = ∃^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, exItr_succ]

def complexity : {n : ℕ} → Semiformulaᵢ L ξ n → ℕ
| _, ⊥        => 0
| _, rel _ _  => 0
| _, φ ⋏ ψ    => max φ.complexity ψ.complexity + 1
| _, φ ⋎ ψ    => max φ.complexity ψ.complexity + 1
| _, φ ➝ ψ    => max φ.complexity ψ.complexity + 1
| _, ∀' φ     => φ.complexity + 1
| _, ∃' φ     => φ.complexity + 1

@[simp] lemma complexity_top : complexity (⊤ : Semiformulaᵢ L ξ n) = 1 := rfl

@[simp] lemma complexity_bot : complexity (⊥ : Semiformulaᵢ L ξ n) = 0 := rfl

@[simp] lemma complexity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : complexity (rel r v) = 0 := rfl

@[simp] lemma complexity_and (φ ψ : Semiformulaᵢ L ξ n) : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_and' (φ ψ : Semiformulaᵢ L ξ n) : complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_or (φ ψ : Semiformulaᵢ L ξ n) : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_or' (φ ψ : Semiformulaᵢ L ξ n) : complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_imp (φ ψ : Semiformulaᵢ L ξ n) : complexity (φ ➝ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_imp' (φ ψ : Semiformulaᵢ L ξ n) : complexity (imp φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_all (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (∀' φ) = φ.complexity + 1 := rfl
@[simp] lemma complexity_all' (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (all φ) = φ.complexity + 1 := rfl

@[simp] lemma complexity_ex (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (∃' φ) = φ.complexity + 1 := rfl
@[simp] lemma complexity_ex' (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (ex φ) = φ.complexity + 1 := rfl

@[simp] lemma complexity_neg (φ : Semiformulaᵢ L ξ n) : complexity (∼φ) = complexity φ + 1 := by simp [neg_def]

@[elab_as_elim]
def cases' {C : ∀ n, Semiformulaᵢ L ξ n → Sort w}
  (hRel    : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hFalsum : ∀ {n : ℕ}, C n ⊥)
  (hAnd    : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n (φ ⋏ ψ))
  (hOr     : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n (φ ⋎ ψ))
  (hImp    : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n (φ ➝ ψ))
  (hAll    : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C n (∀' φ))
  (hEx     : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C n (∃' φ)) :
    ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ n), C n φ
  | _, rel r v => hRel r v
  | _, ⊥       => hFalsum
  | _, φ ⋏ ψ   => hAnd φ ψ
  | _, φ ⋎ ψ   => hOr φ ψ
  | _, φ ➝ ψ   => hImp φ ψ
  | _, ∀' φ    => hAll φ
  | _, ∃' φ    => hEx φ

@[elab_as_elim]
def rec' {C : ∀ n, Semiformulaᵢ L ξ n → Sort w}
  (hRel    : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hFalsum : ∀ {n : ℕ}, C n ⊥)
  (hAnd    : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n φ → C n ψ → C n (φ ⋏ ψ))
  (hOr     : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n φ → C n ψ → C n (φ ⋎ ψ))
  (hImp    : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n φ → C n ψ → C n (φ ➝ ψ))
  (hAll    : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C (n + 1) φ → C n (∀' φ))
  (hEx     : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C (n + 1) φ → C n (∃' φ)) :
    ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ n), C n φ
  | _, rel r v => hRel r v
  | _, ⊥       => hFalsum
  | _, φ ⋏ ψ   => hAnd φ ψ (rec' hRel hFalsum hAnd hOr hImp hAll hEx φ) (rec' hRel hFalsum hAnd hOr hImp hAll hEx ψ)
  | _, φ ⋎ ψ   => hOr φ ψ (rec' hRel hFalsum hAnd hOr hImp hAll hEx φ) (rec' hRel hFalsum hAnd hOr hImp hAll hEx ψ)
  | _, φ ➝ ψ   => hImp φ ψ (rec' hRel hFalsum hAnd hOr hImp hAll hEx φ) (rec' hRel hFalsum hAnd hOr hImp hAll hEx ψ)
  | _, ∀' φ    => hAll φ (rec' hRel hFalsum hAnd hOr hImp hAll hEx φ)
  | _, ∃' φ    => hEx φ (rec' hRel hFalsum hAnd hOr hImp hAll hEx φ)

section Decidable

variable [L.DecidableEq] [DecidableEq ξ]

def hasDecEq : {n : ℕ} → (φ ψ : Semiformulaᵢ L ξ n) → Decidable (φ = ψ)
  | _, ⊥,        ψ => by cases ψ using cases' <;>
      { simp only [reduceCtorEq]; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | _, rel r v,  ψ => by
      cases ψ using cases' <;> try { simpa using isFalse not_false }
      case hRel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simpa [h] using Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp [h])
        · exact isFalse (by simp [e])
  | _, φ ⋏ ψ,    χ => by
      cases χ using cases' <;> try { simpa using isFalse not_false }
      case hAnd φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | _, φ ⋎ ψ,    χ => by
      cases χ using cases' <;> try { simpa using isFalse not_false }
      case hOr φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | _, φ ➝ ψ,    χ => by
      cases χ using cases' <;> try { simpa using isFalse not_false }
      case hImp φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | _, ∀' φ,     ψ => by
      cases ψ using cases' <;> try { simpa using isFalse not_false }
      case hAll φ' => simpa using hasDecEq φ φ'
  | _, ∃' φ,     ψ => by
      cases ψ using cases' <;> try { simpa using isFalse not_false }
      case hEx φ' => simpa using hasDecEq φ φ'

instance : DecidableEq (Semiformulaᵢ L ξ n) := hasDecEq

end Decidable

end Semiformulaᵢ

/-! (Weak) Negative Formula -/
namespace Semiformulaᵢ

inductive IsNegative : Semiformulaᵢ L ξ n → Prop
  | falsum : IsNegative ⊥
  | and {φ ψ} : IsNegative φ → IsNegative ψ → IsNegative (φ ⋏ ψ)
  | imply {φ ψ} : IsNegative ψ → IsNegative (φ ➝ ψ)
  | all {φ} : IsNegative φ → IsNegative (∀' φ)

attribute [simp] IsNegative.falsum

namespace IsNegative

@[simp] lemma and_iff {φ ψ : Semiformulaᵢ L ξ n} : (φ ⋏ ψ).IsNegative ↔ φ.IsNegative ∧ ψ.IsNegative :=
  ⟨by rintro ⟨⟩; simp_all, by rintro ⟨hφ, hψ⟩; exact .and hφ hψ⟩

@[simp] lemma imp_iff {φ ψ : Semiformulaᵢ L ξ n} : (φ ➝ ψ).IsNegative ↔ ψ.IsNegative :=
  ⟨by rintro ⟨⟩; simp_all, by rintro h; exact .imply h⟩

@[simp] lemma all_iff {φ : Semiformulaᵢ L ξ (n + 1)} : (∀' φ).IsNegative ↔ φ.IsNegative :=
  ⟨by rintro ⟨⟩; simp_all, by rintro h; exact .all h⟩

@[simp] lemma verum : (⊤ : Semiformulaᵢ L ξ n).IsNegative := by simp [verum_def]

@[simp] lemma not_or {φ ψ : Semiformulaᵢ L ξ n} : ¬(φ ⋎ ψ).IsNegative := by rintro ⟨⟩

@[simp] lemma not_ex {φ : Semiformulaᵢ L ξ (n + 1)} : ¬(∃' φ).IsNegative := by rintro ⟨⟩

@[simp] lemma not_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ¬(rel r v).IsNegative := by rintro ⟨⟩

@[simp] lemma neg (φ : Semiformulaᵢ L ξ n) : (∼φ).IsNegative := .imply .falsum

end IsNegative

end Semiformulaᵢ


end LO.FirstOrder
