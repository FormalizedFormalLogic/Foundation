module

public import Foundation.FirstOrder.Basic
public import Foundation.LinearLogic.LogicSymbol

/-!
# First-order linear logic
-/

@[expose] public section

namespace LO.FirstOrder.LinearLogic

open FirstOrder

inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  /-- Literals -/
  |    one : Semiformula L ξ n
  | falsum : Semiformula L ξ n
  | tensor : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |    par : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  /-- Multiplicative connectives -/
  |  verum : Semiformula L ξ n
  |   zero : Semiformula L ξ n
  |   with : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |   plus : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  /-- Additive connectives -/
  |   bang : Semiformula L ξ n → Semiformula L ξ n
  |  quest : Semiformula L ξ n → Semiformula L ξ n
  /-- Exponentials -/
  |    all : Semiformula L ξ (n + 1) → Semiformula L ξ n
  |    exs : Semiformula L ξ (n + 1) → Semiformula L ξ n
  /-- Quantifiers -/

abbrev Formula (L : Language) (ξ : Type*) := Semiformula L ξ 0

abbrev Semisentence (L : Language) (n : ℕ) := Semiformula L Empty n

abbrev Sentence (L : Language) := Semiformula L Empty 0

abbrev Semistatement (L : Language) (n : ℕ) := Semiformula L ℕ n

abbrev Statement (L : Language) := Formula L ℕ

namespace Semiformula

variable {L : Language} {ξ : Type*}

instance : MultiplicativeConnective (Semiformula L ξ n) where
  one := one
  bot := falsum
  tensor := tensor
  par := par

instance : AdditiveConnective (Semiformula L ξ n) where
  top := verum
  zero := zero
  with' := .with
  plus := plus

instance : ExponentialConnective (Semiformula L ξ n) where
  bang := bang
  quest := quest

instance : Quantifier (Semiformula L ξ) where
  all := all
  exs := exs

@[simp] lemma tensor_inj {φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n} :
    φ₁ ⨂ ψ₁ = φ₂ ⨂ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := iff_of_eq (by apply tensor.injEq)

@[simp] lemma par_inj {φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n} :
    φ₁ ⅋ ψ₁ = φ₂ ⅋ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := iff_of_eq (by apply par.injEq)

@[simp] lemma with_inj {φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n} :
    φ₁ ＆ ψ₁ = φ₂ ＆ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := iff_of_eq (by apply with.injEq)

@[simp] lemma plus_inj {φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n} :
    φ₁ ⨁ ψ₁ = φ₂ ⨁ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := iff_of_eq (by apply plus.injEq)

@[simp] lemma bang_inj {φ₁ φ₂ : Semiformula L ξ n} :
    ！φ₁ = ！φ₂ ↔ φ₁ = φ₂ := iff_of_eq (by apply bang.injEq)

@[simp] lemma quant_inj {φ₁ φ₂ : Semiformula L ξ n} :
    ？φ₁ = ？φ₂ ↔ φ₁ = φ₂ := iff_of_eq (by apply quest.injEq)

@[simp] lemma all_inj {φ₁ φ₂ : Semiformula L ξ (n + 1)} :
    ∀⁰ φ₁ = ∀⁰ φ₂ ↔ φ₁ = φ₂ := iff_of_eq (by apply all.injEq)

@[simp] lemma exs_inj {φ₁ φ₂ : Semiformula L ξ (n + 1)} :
    ∃⁰ φ₁ = ∃⁰ φ₂ ↔ φ₁ = φ₂ := iff_of_eq (by apply exs.injEq)

def neg : Semiformula L ξ n → Semiformula L ξ n
  |  rel R v => nrel R v
  | nrel R v => rel R v
  |        1 => ⊥
  |        ⊥ => 1
  |    φ ⨂ ψ => φ.neg ⅋ ψ.neg
  |    φ ⅋ ψ => φ.neg ⨂ ψ.neg
  |        ⊤ => 0
  |        0 => ⊤
  |    φ ＆ ψ => φ.neg ⨁ ψ.neg
  |    φ ⨁ ψ => φ.neg ＆ ψ.neg
  |       ！φ => ？φ.neg
  |       ？φ => ！φ.neg
  |     ∀⁰ φ => ∃⁰ φ.neg
  |     ∃⁰ φ => ∀⁰ φ.neg

instance : Tilde (Semiformula L ξ n) := ⟨neg⟩

instance : MultiplicativeConnective.DeMorgan (Semiformula L ξ n) where
  one := rfl
  falsum := rfl
  tensor _ _ := rfl
  par _ _ := rfl

instance : AdditiveConnective.DeMorgan (Semiformula L ξ n) where
  verum := rfl
  zero := rfl
  with_ _ _ := rfl
  plus _ _ := rfl

instance : ExponentialConnective.DeMorgan (Semiformula L ξ n) where
  bang _ := rfl
  quest _ := rfl

@[simp] lemma neg_rel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
  ∼rel R v = nrel R v := rfl

@[simp] lemma neg_nrel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
  ∼nrel R v = rel R v := rfl

@[simp] lemma neg_all (φ : Semiformula L ξ (n + 1)) :
  ∼(∀⁰ φ) = ∃⁰ ∼φ := rfl

@[simp] lemma neg_exs (φ : Semiformula L ξ (n + 1)) :
  ∼(∃⁰ φ) = ∀⁰ ∼φ := rfl

lemma neg_neg {n} (φ : Semiformula L ξ n) : ∼∼φ = φ := by
  match φ with
  |  rel R v => rfl
  | nrel R v => rfl
  |        1 => rfl
  |        ⊥ => rfl
  |    φ ⨂ ψ => simp [neg_neg φ, neg_neg ψ]
  |    φ ⅋ ψ => simp [neg_neg φ, neg_neg ψ]
  |        ⊤ => rfl
  |        0 => rfl
  |    φ ＆ ψ => simp [neg_neg φ, neg_neg ψ]
  |    φ ⨁ ψ => simp [neg_neg φ, neg_neg ψ]
  |       ！φ => simp [neg_neg φ]
  |       ？φ => simp [neg_neg φ]
  |     ∀⁰ φ => simp [neg_neg φ]
  |     ∃⁰ φ => simp [neg_neg φ]

instance : NegInvolutive (Semiformula L ξ n) := ⟨neg_neg⟩

/-- Usual logical connectives are defined to align with `⊤` and `⊥` -/
instance : LogicalConnective (Semiformula L ξ n) where
  wedge := .with
  vee := .par
  arrow φ ψ := φ ⊸ ψ

lemma wedge_def (φ ψ : Semiformula L ξ n) : φ ⋏ ψ = φ ＆ ψ := rfl

lemma vee_def (φ ψ : Semiformula L ξ n) :  φ ⋎ ψ = φ ⅋ ψ := rfl

lemma imply_def (φ ψ : Semiformula L ξ n) : φ ➝ ψ = φ ⊸ ψ := rfl

lemma imply_def' (φ ψ : Semiformula L ξ n) : φ ➝ ψ = ∼φ ⅋ ψ := rfl

@[simp] lemma neg_inj {φ ψ : Semiformula L ξ n} : ∼φ = ∼ψ ↔ φ = ψ := by
  constructor
  · intro h; rw [←neg_neg φ, ←neg_neg ψ, h]
  · intro h; rw [h]

instance : LCWQ (Semiformula L ξ) where
  connectives _ := inferInstance

@[elab_as_elim]
def cases' {C : ∀ n, Semiformula L ξ n → Sort w}
    (hRel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hNrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hOne : ∀ {n : ℕ}, C n 1)
    (hFalsum : ∀ {n : ℕ}, C n ⊥)
    (hTensor : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⨂ ψ))
    (hPar : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⅋ ψ))
    (hVerum : ∀ {n : ℕ}, C n ⊤)
    (hZero : ∀ {n : ℕ}, C n 0)
    (hWith : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ＆ ψ))
    (hPlus : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⨁ ψ))
    (hBang : ∀ {n : ℕ} (φ : Semiformula L ξ n), C n (！φ))
    (hQuest : ∀ {n : ℕ} (φ : Semiformula L ξ n), C n (？φ))
    (hAll : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (∀⁰ φ))
    (hExs : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (∃⁰ φ)) {n} :
    (φ : Semiformula L ξ n) → C n φ
  | rel r v => hRel r v
  | nrel r v => hNrel r v
  | 1 => hOne
  | ⊥ => hFalsum
  | φ ⨂ ψ => hTensor φ ψ
  | φ ⅋ ψ => hPar φ ψ
  | ⊤ => hVerum
  | 0 => hZero
  | φ ＆ ψ => hWith φ ψ
  | φ ⨁ ψ => hPlus φ ψ
  | ！φ => hBang φ
  | ？φ => hQuest φ
  | ∀⁰ φ => hAll φ
  | ∃⁰ φ => hExs φ

@[elab_as_elim]
def rec' {C : ∀ n, Semiformula L ξ n → Sort w}
  (hRel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hNrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
  (hOne : ∀ {n : ℕ}, C n 1)
  (hFalsum : ∀ {n : ℕ}, C n ⊥)
  (hTensor : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⨂ ψ))
  (hPar : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⅋ ψ))
  (hVerum : ∀ {n : ℕ}, C n ⊤)
  (hZero : ∀ {n : ℕ}, C n 0)
  (hWith : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ＆ ψ))
  (hPlus : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⨁ ψ))
  (hBang : ∀ {n : ℕ} (φ : Semiformula L ξ n), C n φ → C n (！φ))
  (hQuest : ∀ {n : ℕ} (φ : Semiformula L ξ n), C n φ → C n (？φ))
  (hAll : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (∀⁰ φ))
  (hExs : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (∃⁰ φ)) {n} :
    (φ : Semiformula L ξ n) → C n φ
  | rel r v => hRel r v
  | nrel r v => hNrel r v
  | 1 => hOne
  | ⊥ => hFalsum
  | φ ⨂ ψ => hTensor φ ψ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs φ)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs ψ)
  | φ ⅋ ψ => hPar φ ψ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs φ)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs ψ)
  | ⊤ => hVerum
  | 0 => hZero
  | φ ＆ ψ => hWith φ ψ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs φ)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs ψ)
  | φ ⨁ ψ => hPlus φ ψ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs φ)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs ψ)
  | ！φ => hBang φ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs φ)
  | ？φ => hQuest φ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs φ)
  | ∀⁰ φ => hAll φ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs φ)
  | ∃⁰ φ => hExs φ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs φ)

def complexity : Semiformula L ξ n → ℕ
  |  rel _ _ => 0
  | nrel _ _ => 0
  |        1 => 0
  |        ⊥ => 0
  |    φ ⨂ ψ => max (complexity φ) (complexity ψ) + 1
  |    φ ⅋ ψ => max (complexity φ) (complexity ψ) + 1
  |        ⊤ => 0
  |        0 => 0
  |    φ ＆ ψ => max (complexity φ) (complexity ψ) + 1
  |    φ ⨁ ψ => max (complexity φ) (complexity ψ) + 1
  |       ！φ => complexity φ + 1
  |       ？φ => complexity φ + 1
  |     ∀⁰ φ => complexity φ + 1
  |     ∃⁰ φ => complexity φ + 1

@[simp] lemma complexity_rel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
    complexity (rel R v) = 0 := rfl

@[simp] lemma complexity_nrel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
    complexity (nrel R v) = 0 := rfl

@[simp] lemma complexity_one : (1 : Semiformula L ξ n).complexity = 0 := rfl
@[simp] lemma complexity_one' : (.one : Semiformula L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_falsum : (⊥ : Semiformula L ξ n).complexity = 0 := rfl
@[simp] lemma complexity_falsum' : (.falsum : Semiformula L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_tensor (φ ψ : Semiformula L ξ n) :
    (φ ⨂ ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_tensor' (φ ψ : Semiformula L ξ n) :
    (φ.tensor ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_par (φ ψ : Semiformula L ξ n) :
    (φ ⅋ ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_par' (φ ψ : Semiformula L ξ n) :
    (φ.par ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_verum : (⊤ : Semiformula L ξ n).complexity = 0 := rfl
@[simp] lemma complexity_verum' : (.verum : Semiformula L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_zero : (0 : Semiformula L ξ n).complexity = 0 := rfl
@[simp] lemma complexity_zero' : (.zero : Semiformula L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_with (φ ψ : Semiformula L ξ n) :
    (φ ＆ ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_with' (φ ψ : Semiformula L ξ n) :
    (φ.with ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_plus (φ ψ : Semiformula L ξ n) :
    (φ ⨁ ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_plus' (φ ψ : Semiformula L ξ n) :
    (φ.plus ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_bang (φ : Semiformula L ξ n) :
    (！φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_bang' (φ : Semiformula L ξ n) :
    (φ.bang).complexity = φ.complexity + 1 := rfl

@[simp] lemma complexity_quest (φ : Semiformula L ξ n) :
    (？φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_quest' (φ : Semiformula L ξ n) :
    (φ.quest).complexity = φ.complexity + 1 := rfl

@[simp] lemma complexity_all (φ : Semiformula L ξ (n + 1)) :
    (∀⁰ φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_all' (φ : Semiformula L ξ (n + 1)) :
    φ.all.complexity = φ.complexity + 1 := rfl

@[simp] lemma complexity_exs (φ : Semiformula L ξ (n + 1)) :
    (∃⁰ φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_exs' (φ : Semiformula L ξ (n + 1)) :
    φ.exs.complexity = φ.complexity + 1 := rfl

@[simp] lemma complexity_neg (φ : Semiformula L ξ n) :
    (∼φ).complexity = φ.complexity := by
  induction φ using rec' <;> simp [*]

instance [L.DecidableEq] [DecidableEq ξ] : DecidableEq (Semiformula L ξ n) :=
  let rec dc {n} : (φ ψ : Semiformula L ξ n) → Decidable (φ = ψ)
    | .rel (arity := ar₁) R₁ v₁, φ₂ =>
      match φ₂ with
      | .rel (arity := ar₂) R₂ v₂ => by
        by_cases har : ar₁ = ar₂
        · rcases har
          exact match decEq R₁ R₂ with
            |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ decEq (v₁ i) (v₂ i)
            | isFalse h => isFalse (by simp_all)
        · exact isFalse (by simp_all)
      | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | .nrel (arity := ar₁) R₁ v₁, φ₂ =>
      match φ₂ with
      | .nrel (arity := ar₂) R₂ v₂ => by
        by_cases har : ar₁ = ar₂
        · rcases har
          exact match decEq R₁ R₂ with
            |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ decEq (v₁ i) (v₂ i)
            | isFalse h => isFalse (by simp_all)
        · exact isFalse (by simp_all)
      | .rel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | 1, φ₂ =>
      match φ₂ with
      | 1 => isTrue rfl
      | .rel _ _ | .nrel _ _ | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | ⊥, φ₂ =>
      match φ₂ with
      | ⊥ => isTrue rfl
      | .rel _ _ | .nrel _ _ | 1 | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | φ₁ ⨂ ψ₁, φ₂ =>
      match φ₂ with
      | φ₂ ⨂ ψ₂ =>
        match dc φ₁ φ₂, dc ψ₁ ψ₂ with
        |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
        | isFalse h₁,          _ => isFalse (by simp_all)
        |          _, isFalse h₂ => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | φ₁ ⅋ ψ₁, φ₂ =>
      match φ₂ with
      | φ₂ ⅋ ψ₂ =>
        match dc φ₁ φ₂, dc ψ₁ ψ₂ with
        |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
        | isFalse h₁,          _ => isFalse (by simp_all)
        |          _, isFalse h₂ => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | ⊤, φ₂ =>
      match φ₂ with
      | ⊤ => isTrue rfl
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | 0, φ₂ =>
      match φ₂ with
      | 0 => isTrue rfl
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | φ₁ ＆ ψ₁, φ₂ =>
      match φ₂ with
      | φ₂ ＆ ψ₂ =>
        match dc φ₁ φ₂, dc ψ₁ ψ₂ with
        |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
        | isFalse h₁,          _ => isFalse (by simp_all)
        |          _, isFalse h₂ => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ⨁ _ | ！_ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | φ₁ ⨁ ψ₁, φ₂ =>
      match φ₂ with
      | φ₂ ⨁ ψ₂ =>
        match dc φ₁ φ₂, dc ψ₁ ψ₂ with
        |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
        | isFalse h₁,          _ => isFalse (by simp_all)
        |          _, isFalse h₂ => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | ！_ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | ！φ₁, φ₂ =>
      match φ₂ with
      | ！φ₂ =>
        match dc φ₁ φ₂ with
        |  isTrue h => isTrue (by simp_all)
        | isFalse h => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ？_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | ？φ₁, φ₂ =>
      match φ₂ with
      | ？φ₂ =>
        match dc φ₁ φ₂ with
        |  isTrue h => isTrue (by simp_all)
        | isFalse h => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ∀⁰ _ | ∃⁰ _ =>
        isFalse (by simp_all)
    | ∀⁰ φ₁, φ₂ =>
      match φ₂ with
      | ∀⁰ φ₂ =>
        match dc φ₁ φ₂ with
        |  isTrue h => isTrue (by simp_all)
        | isFalse h => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∃⁰ _ =>
        isFalse (by simp_all)
    | ∃⁰ φ₁, φ₂ =>
      match φ₂ with
      | ∃⁰ φ₂ =>
        match dc φ₁ φ₂ with
        |  isTrue h => isTrue (by simp_all)
        | isFalse h => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀⁰ _ =>
        isFalse (by simp_all)
  dc

inductive IsQuest : Semiformula L ξ n → Prop
  | intro : IsQuest (？φ)

@[simp] lemma IsQuest.not_one : ¬IsQuest (1 : Semiformula L ξ n) := by intro h; cases h
@[simp] lemma IsQuest.not_falsum : ¬IsQuest (⊥ : Semiformula L ξ n) := by intro h; cases h
@[simp] lemma IsQuest.not_tensor (φ ψ : Semiformula L ξ n) : ¬IsQuest (φ ⨂ ψ) := by intro h; cases h
@[simp] lemma IsQuest.not_par (φ ψ : Semiformula L ξ n) : ¬IsQuest (φ ⅋ ψ) := by intro h; cases h
@[simp] lemma IsQuest.not_verum : ¬IsQuest (⊤ : Semiformula L ξ n) := by intro h; cases h
@[simp] lemma IsQuest.not_zero : ¬IsQuest (0 : Semiformula L ξ n) := by intro h; cases h
@[simp] lemma IsQuest.not_with (φ ψ : Semiformula L ξ n) : ¬IsQuest (φ ＆ ψ) := by intro h; cases h
@[simp] lemma IsQuest.not_plus (φ ψ : Semiformula L ξ n) : ¬IsQuest (φ ⨁ ψ) := by intro h; cases h
@[simp] lemma IsQuest.not_bang (φ : Semiformula L ξ n) : ¬IsQuest (！φ) := by intro h; cases h
@[simp] lemma IsQuest.quest (φ : Semiformula L ξ n) : IsQuest (？φ) := .intro
@[simp] lemma IsQuest.not_all (φ : Semiformula L ξ (n + 1)) : ¬IsQuest (∀⁰ φ) := by intro h; cases h
@[simp] lemma IsQuest.not_exs (φ : Semiformula L ξ (n + 1)) : ¬IsQuest (∃⁰ φ) := by intro h; cases h

/-! ### Polarity -/

inductive Negative : Semiformula L ξ n → Prop
  | quest (φ : Semiformula L ξ n) : Negative (？φ)
  | verum : Negative (⊤ : Semiformula L ξ n)
  | falsum : Negative (⊥ : Semiformula L ξ n)
  | par : Negative φ → Negative ψ → Negative (φ ⅋ ψ)
  | with : Negative φ → Negative ψ → Negative (φ ＆ ψ)
  | all : Negative φ → Negative (∀⁰ φ)

namespace Negative

attribute [simp] quest verum falsum

@[simp] lemma par_iff {φ ψ : Semiformula L ξ n} :
    Negative (φ ⅋ ψ) ↔ Negative φ ∧ Negative ψ := by
  constructor
  · rintro ⟨h₁, h₂⟩; grind
  · rintro ⟨h₁, h₂⟩; exact par h₁ h₂

@[simp] lemma with_iff {φ ψ : Semiformula L ξ n} :
    Negative (φ ＆ ψ) ↔ Negative φ ∧ Negative ψ := by
  constructor
  · rintro ⟨h₁, h₂⟩; grind
  · rintro ⟨h₁, h₂⟩; exact .with h₁ h₂

@[simp] lemma all_iff {φ : Semiformula L ξ (n + 1)} :
    Negative (∀⁰ φ) ↔ Negative φ := by
  constructor
  · rintro ⟨h⟩; assumption
  · rintro h; exact all h

@[simp] lemma not_rel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) : ¬Negative (rel R v) := by rintro ⟨⟩

@[simp] lemma not_nrel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) : ¬Negative (nrel R v) := by rintro ⟨⟩

@[simp] lemma not_one : ¬Negative (1 : Semiformula L ξ n) := by rintro ⟨⟩

@[simp] lemma not_zero : ¬Negative (0 : Semiformula L ξ n) := by rintro ⟨⟩

@[simp] lemma not_tensor (φ ψ : Semiformula L ξ n) : ¬Negative (φ ⨂ ψ) := by rintro ⟨⟩

@[simp] lemma not_plus (φ ψ : Semiformula L ξ n) : ¬Negative (φ ⨁ ψ) := by rintro ⟨⟩

@[simp] lemma not_bang (φ : Semiformula L ξ n) : ¬Negative (！φ) := by rintro ⟨⟩

@[simp] lemma not_exs (φ : Semiformula L ξ (n + 1)) : ¬Negative (∃⁰ φ) := by rintro ⟨⟩

instance (φ : Semiformula L ξ n) : Decidable φ.Negative :=
  let rec dc {n} : (φ : Semiformula L ξ n) → Decidable φ.Negative
  |       ？φ => isTrue (by simp)
  |        ⊤ => isTrue (by simp)
  |        ⊥ => isTrue (by simp)
  |    φ ⅋ ψ =>
    match dc φ, dc ψ with
    |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
    |  isTrue h₁, isFalse h₂ => isFalse (by simp_all)
    | isFalse h₁,  isTrue h₂ => isFalse (by simp_all)
    | isFalse h₁, isFalse h₂ => isFalse (by simp_all)
  | φ ＆ ψ =>
    match dc φ, dc ψ with
    |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
    |  isTrue h₁, isFalse h₂ => isFalse (by simp_all)
    | isFalse h₁,  isTrue h₂ => isFalse (by simp_all)
    | isFalse h₁, isFalse h₂ => isFalse (by simp_all)
  | ∀⁰ φ =>
    match dc φ with
    | isTrue h => isTrue (by simp_all)
    | isFalse h => isFalse (by simp_all)
  | rel _ _ | nrel _ _ | 1 | 0 | φ ⨂ ψ | φ ⨁ ψ | ！φ | ∃⁰ φ => isFalse (by simp)
  dc φ

end Negative

end Semiformula

end LO.FirstOrder.LinearLogic

end
