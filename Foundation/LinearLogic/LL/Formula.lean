module

public import Foundation.FirstOrder.Basic
public import Foundation.Logic.Entailment
public import Foundation.LinearLogic.LogicSymbol

/-!
# First-order linear logic
-/

@[expose] public section

namespace LO.FirstOrder

open FirstOrder

inductive Semiformulaₗ (L : Language) (ξ : Type*) : ℕ → Type _ where
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformulaₗ L ξ n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformulaₗ L ξ n
  /-- Multiplicative connectives -/
  |    one : Semiformulaₗ L ξ n
  | falsum : Semiformulaₗ L ξ n
  | tensor : Semiformulaₗ L ξ n → Semiformulaₗ L ξ n → Semiformulaₗ L ξ n
  |    par : Semiformulaₗ L ξ n → Semiformulaₗ L ξ n → Semiformulaₗ L ξ n
  /-- Additive connectives -/
  |  verum : Semiformulaₗ L ξ n
  |   zero : Semiformulaₗ L ξ n
  |   with : Semiformulaₗ L ξ n → Semiformulaₗ L ξ n → Semiformulaₗ L ξ n
  |   plus : Semiformulaₗ L ξ n → Semiformulaₗ L ξ n → Semiformulaₗ L ξ n
  /-- Exponentials -/
  |   bang : Semiformulaₗ L ξ n → Semiformulaₗ L ξ n
  |  quest : Semiformulaₗ L ξ n → Semiformulaₗ L ξ n
  /-- Quantifiers -/
  |    all : Semiformulaₗ L ξ (n + 1) → Semiformulaₗ L ξ n
  |     ex : Semiformulaₗ L ξ (n + 1) → Semiformulaₗ L ξ n

abbrev Formulaₗ (L : Language) (ξ : Type*) := Semiformulaₗ L ξ 0

abbrev Semisentenceₗ (L : Language) (n : ℕ) := Semiformulaₗ L Empty n

abbrev Sentenceₗ (L : Language) := Semiformulaₗ L Empty 0

abbrev Semistatementₗ (L : Language) (n : ℕ) := Semiformulaₗ L ℕ n

abbrev Statementₗ (L : Language) := Formulaₗ L ℕ

namespace Semiformulaₗ

variable {L : Language} {ξ : Type*}

instance : MultiplicativeConnective (Semiformulaₗ L ξ n) where
  one := one
  bot := falsum
  tensor := tensor
  par := par

instance : AdditiveConnective (Semiformulaₗ L ξ n) where
  top := verum
  zero := zero
  with' := .with
  plus := plus

instance : ExponentialConnective (Semiformulaₗ L ξ n) where
  bang := bang
  quest := quest

instance : Quantifier (Semiformulaₗ L ξ) where
  univ := all
  ex := ex

@[simp] lemma tensor_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformulaₗ L ξ n) :
    φ₁ ⨂ ψ₁ = φ₂ ⨂ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := iff_of_eq (by apply tensor.injEq)

@[simp] lemma par_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformulaₗ L ξ n) :
    φ₁ ⅋ ψ₁ = φ₂ ⅋ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := iff_of_eq (by apply par.injEq)

@[simp] lemma with_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformulaₗ L ξ n) :
    φ₁ ＆ ψ₁ = φ₂ ＆ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := iff_of_eq (by apply with.injEq)

@[simp] lemma plus_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformulaₗ L ξ n) :
    φ₁ ⨁ ψ₁ = φ₂ ⨁ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := iff_of_eq (by apply plus.injEq)

@[simp] lemma bang_inj (φ₁ φ₂ : Semiformulaₗ L ξ n) :
    ！φ₁ = ！φ₂ ↔ φ₁ = φ₂ := iff_of_eq (by apply bang.injEq)

@[simp] lemma quest_inj (φ₁ φ₂ : Semiformulaₗ L ξ n) :
    ？φ₁ = ？φ₂ ↔ φ₁ = φ₂ := iff_of_eq (by apply quest.injEq)

@[simp] lemma all_inj (φ₁ φ₂ : Semiformulaₗ L ξ (n + 1)) :
    ∀' φ₁ = ∀' φ₂ ↔ φ₁ = φ₂ := iff_of_eq (by apply all.injEq)

@[simp] lemma ex_inj (φ₁ φ₂ : Semiformulaₗ L ξ (n + 1)) :
    ∃' φ₁ = ∃' φ₂ ↔ φ₁ = φ₂ := iff_of_eq (by apply ex.injEq)

def neg : Semiformulaₗ L ξ n → Semiformulaₗ L ξ n
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
  |     ∀' φ => ∃' φ.neg
  |     ∃' φ => ∀' φ.neg

instance : Tilde (Semiformulaₗ L ξ n) := ⟨neg⟩

instance : MultiplicativeConnective.DeMorgan (Semiformulaₗ L ξ n) where
  one := rfl
  falsum := rfl
  tensor _ _ := rfl
  par _ _ := rfl

instance : AdditiveConnective.DeMorgan (Semiformulaₗ L ξ n) where
  verum := rfl
  zero := rfl
  with_ _ _ := rfl
  plus _ _ := rfl

instance : ExponentialConnective.DeMorgan (Semiformulaₗ L ξ n) where
  bang _ := rfl
  quest _ := rfl

@[simp] lemma neg_rel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
  ∼rel R v = nrel R v := rfl

@[simp] lemma neg_nrel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
  ∼nrel R v = rel R v := rfl

@[simp] lemma neg_all (φ : Semiformulaₗ L ξ (n + 1)) :
  ∼(∀' φ) = ∃' ∼φ := rfl

@[simp] lemma neg_ex (φ : Semiformulaₗ L ξ (n + 1)) :
  ∼(∃' φ) = ∀' ∼φ := rfl

lemma neg_neg {n} (φ : Semiformulaₗ L ξ n) : ∼∼φ = φ := by
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
  |     ∀' φ => simp [neg_neg φ]
  |     ∃' φ => simp [neg_neg φ]

instance : NegInvolutive (Semiformulaₗ L ξ n) := ⟨neg_neg⟩

/-- Usual logical connectives are defined to align with `⊤` and `⊥` -/
instance : LogicalConnective (Semiformulaₗ L ξ n) where
  wedge := .with
  vee := .par
  arrow φ ψ := φ ⊸ ψ

lemma wedge_def (φ ψ : Semiformulaₗ L ξ n) : φ ⋏ ψ = φ ＆ ψ := rfl

lemma vee_def (φ ψ : Semiformulaₗ L ξ n) :  φ ⋎ ψ = φ ⅋ ψ := rfl

lemma imply_def (φ ψ : Semiformulaₗ L ξ n) : φ ➝ ψ = φ ⊸ ψ := rfl

lemma imply_def' (φ ψ : Semiformulaₗ L ξ n) : φ ➝ ψ = ∼φ ⅋ ψ := rfl

instance : LCWQ (Semiformulaₗ L ξ) where
  connectives _ := inferInstance

@[elab_as_elim]
def cases' {C : ∀ n, Semiformulaₗ L ξ n → Sort w}
    (hRel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hNrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hOne : ∀ {n : ℕ}, C n 1)
    (hFalsum : ∀ {n : ℕ}, C n ⊥)
    (hTensor : ∀ {n : ℕ} (φ ψ : Semiformulaₗ L ξ n), C n (φ ⨂ ψ))
    (hPar : ∀ {n : ℕ} (φ ψ : Semiformulaₗ L ξ n), C n (φ ⅋ ψ))
    (hVerum : ∀ {n : ℕ}, C n ⊤)
    (hZero : ∀ {n : ℕ}, C n 0)
    (hWith : ∀ {n : ℕ} (φ ψ : Semiformulaₗ L ξ n), C n (φ ＆ ψ))
    (hPlus : ∀ {n : ℕ} (φ ψ : Semiformulaₗ L ξ n), C n (φ ⨁ ψ))
    (hBang : ∀ {n : ℕ} (φ : Semiformulaₗ L ξ n), C n (！φ))
    (hQuest : ∀ {n : ℕ} (φ : Semiformulaₗ L ξ n), C n (？φ))
    (hAll : ∀ {n : ℕ} (φ : Semiformulaₗ L ξ (n + 1)), C n (∀' φ))
    (hEx : ∀ {n : ℕ} (φ : Semiformulaₗ L ξ (n + 1)), C n (∃' φ)) {n} :
    (φ : Semiformulaₗ L ξ n) → C n φ
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
  | ∀' φ => hAll φ
  | ∃' φ => hEx φ

@[elab_as_elim]
def rec' {C : ∀ n, Semiformulaₗ L ξ n → Sort w}
  (hRel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hNrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
  (hOne : ∀ {n : ℕ}, C n 1)
  (hFalsum : ∀ {n : ℕ}, C n ⊥)
  (hTensor : ∀ {n : ℕ} (φ ψ : Semiformulaₗ L ξ n), C n φ → C n ψ → C n (φ ⨂ ψ))
  (hPar : ∀ {n : ℕ} (φ ψ : Semiformulaₗ L ξ n), C n φ → C n ψ → C n (φ ⅋ ψ))
  (hVerum : ∀ {n : ℕ}, C n ⊤)
  (hZero : ∀ {n : ℕ}, C n 0)
  (hWith : ∀ {n : ℕ} (φ ψ : Semiformulaₗ L ξ n), C n φ → C n ψ → C n (φ ＆ ψ))
  (hPlus : ∀ {n : ℕ} (φ ψ : Semiformulaₗ L ξ n), C n φ → C n ψ → C n (φ ⨁ ψ))
  (hBang : ∀ {n : ℕ} (φ : Semiformulaₗ L ξ n), C n φ → C n (！φ))
  (hQuest : ∀ {n : ℕ} (φ : Semiformulaₗ L ξ n), C n φ → C n (？φ))
  (hAll : ∀ {n : ℕ} (φ : Semiformulaₗ L ξ (n + 1)), C (n + 1) φ → C n (∀' φ))
  (hEx : ∀ {n : ℕ} (φ : Semiformulaₗ L ξ (n + 1)), C (n + 1) φ → C n (∃' φ)) {n} :
    (φ : Semiformulaₗ L ξ n) → C n φ
  | rel r v => hRel r v
  | nrel r v => hNrel r v
  | 1 => hOne
  | ⊥ => hFalsum
  | φ ⨂ ψ => hTensor φ ψ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx φ)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx ψ)
  | φ ⅋ ψ => hPar φ ψ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx φ)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx ψ)
  | ⊤ => hVerum
  | 0 => hZero
  | φ ＆ ψ => hWith φ ψ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx φ)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx ψ)
  | φ ⨁ ψ => hPlus φ ψ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx φ)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx ψ)
  | ！φ => hBang φ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx φ)
  | ？φ => hQuest φ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx φ)
  | ∀' φ => hAll φ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx φ)
  | ∃' φ => hEx φ (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hEx φ)

def complexity : Semiformulaₗ L ξ n → ℕ
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
  |     ∀' φ => complexity φ + 1
  |     ∃' φ => complexity φ + 1

@[simp] lemma complexity_rel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
    complexity (rel R v) = 0 := rfl

@[simp] lemma complexity_nrel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
    complexity (nrel R v) = 0 := rfl

@[simp] lemma complexity_one : complexity (1 : Semiformulaₗ L ξ n) = 0 := rfl

@[simp] lemma complexity_falsum : complexity (⊥ : Semiformulaₗ L ξ n) = 0 := rfl

@[simp] lemma complexity_tensor (φ ψ : Semiformulaₗ L ξ n) :
    complexity (φ ⨂ ψ) = max (complexity φ) (complexity ψ) + 1 := rfl

@[simp] lemma complexity_par (φ ψ : Semiformulaₗ L ξ n) :
    complexity (φ ⅋ ψ) = max (complexity φ) (complexity ψ) + 1 := rfl

@[simp] lemma complexity_verum : complexity (⊤ : Semiformulaₗ L ξ n) = 0 := rfl

@[simp] lemma complexity_zero : complexity (0 : Semiformulaₗ L ξ n) = 0 := rfl

@[simp] lemma complexity_with (φ ψ : Semiformulaₗ L ξ n) :
    complexity (φ ＆ ψ) = max (complexity φ) (complexity ψ) + 1 := rfl

@[simp] lemma complexity_plus (φ ψ : Semiformulaₗ L ξ n) :
    complexity (φ ⨁ ψ) = max (complexity φ) (complexity ψ) + 1 := rfl

@[simp] lemma complexity_bang (φ : Semiformulaₗ L ξ n) :
    complexity (！φ) = complexity φ + 1 := rfl

@[simp] lemma complexity_quest (φ : Semiformulaₗ L ξ n) :
    complexity (？φ) = complexity φ + 1 := rfl

@[simp] lemma complexity_all (φ : Semiformulaₗ L ξ (n + 1)) :
    complexity (∀' φ) = complexity φ + 1 := rfl

@[simp] lemma complexity_ex (φ : Semiformulaₗ L ξ (n + 1)) :
    complexity (∃' φ) = complexity φ + 1 := rfl

@[simp] lemma complexity_neg (φ : Semiformulaₗ L ξ n) :
    complexity (∼φ) = complexity φ := by
  induction φ using rec' <;> simp [*]

end Semiformulaₗ

end LO.FirstOrder

end
