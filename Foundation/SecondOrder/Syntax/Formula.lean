module

public import Foundation.FirstOrder.Basic

@[expose] public section

/-!
# Formulas of monadic second-order logic
-/

namespace LO.SecondOrder

open FirstOrder

inductive Semiformula (L : Language) (Ξ ξ : Type*) : ℕ → ℕ → Type _ where
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L Ξ ξ N n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L Ξ ξ N n
  |   bvar : Fin N → Semiterm L ξ n → Semiformula L Ξ ξ N n
  |  nbvar : Fin N → Semiterm L ξ n → Semiformula L Ξ ξ N n
  |   fvar : Ξ → Semiterm L ξ n → Semiformula L Ξ ξ N n
  |  nfvar : Ξ → Semiterm L ξ n → Semiformula L Ξ ξ N n
  |  verum : Semiformula L Ξ ξ N n
  | falsum : Semiformula L Ξ ξ N n
  |    and : Semiformula L Ξ ξ N n → Semiformula L Ξ ξ N n → Semiformula L Ξ ξ N n
  |     or : Semiformula L Ξ ξ N n → Semiformula L Ξ ξ N n → Semiformula L Ξ ξ N n
  |   all₀ : Semiformula L Ξ ξ N (n + 1) → Semiformula L Ξ ξ N n
  |   exs₀ : Semiformula L Ξ ξ N (n + 1) → Semiformula L Ξ ξ N n
  |   all₁ : Semiformula L Ξ ξ (N + 1) n → Semiformula L Ξ ξ N n
  |   exs₁ : Semiformula L Ξ ξ (N + 1) n → Semiformula L Ξ ξ N n

abbrev Formula (L : Language) (Ξ ξ : Type*) := Semiformula L Ξ ξ 0 0

abbrev Semisentence (L : Language) (n N : ℕ) := Semiformula L Empty Empty n N

abbrev Sentence (L : Language) := Semiformula L Empty Empty 0 0

abbrev Semistatement (L : Language) (n N : ℕ) := Semiformula L ℕ ℕ n N

abbrev Statement (L : Language) := Semiformula L ℕ ℕ 0 0

namespace Semiformula

variable {L : Language} {Ξ ξ : Type*}

instance : Top (Semiformula L Ξ ξ N n) := ⟨verum⟩

instance : Bot (Semiformula L Ξ ξ N n) := ⟨falsum⟩

instance : Wedge (Semiformula L Ξ ξ N n) := ⟨and⟩

instance : Vee (Semiformula L Ξ ξ N n) := ⟨or⟩

instance : FirstOrder.Quantifier (Semiformula L Ξ ξ N) where
  all := all₀
  exs := exs₀

instance : SecondOrder.Quantifier (Semiformula L Ξ ξ) where
  all₁ := all₁
  exs₁ := exs₁

scoped notation:80 t " ∈# " X => Semiformula.bvar X t
scoped notation:80 t " ∉# " X => Semiformula.nbvar X t
scoped notation:80 t " ∈& " X => Semiformula.fvar X t
scoped notation:80 t " ∉& " X => Semiformula.nfvar X t

def neg : Semiformula L Ξ ξ N n → Semiformula L Ξ ξ N n
  |  rel R v => nrel R v
  | nrel R v => rel R v
  |   t ∈# X => t ∉# X
  |   t ∉# X => t ∈# X
  |   t ∈& X => t ∉& X
  |   t ∉& X => t ∈& X
  |        ⊤ => ⊥
  |        ⊥ => ⊤
  |    φ ⋏ ψ => φ.neg ⋎ ψ.neg
  |    φ ⋎ ψ => φ.neg ⋏ ψ.neg
  |     ∀⁰ φ => ∃⁰ φ.neg
  |     ∃⁰ φ => ∀⁰ φ.neg
  |     ∀¹ φ => ∃¹ φ.neg
  |     ∃¹ φ => ∀¹ φ.neg

instance : Tilde (Semiformula L Ξ ξ N n) := ⟨neg⟩

instance : LogicalConnective (Semiformula L Ξ ξ N n) where
  arrow φ ψ := ∼φ ⋎ ψ

instance : DeMorgan (Semiformula L Ξ ξ N n) where
  verum := rfl
  falsum := rfl
  and _ _ := rfl
  or _ _ := rfl
  imply _ _ := rfl

@[simp] lemma neg_rel (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    ∼(rel R v : Semiformula L Ξ ξ N n) = nrel R v := rfl

@[simp] lemma neg_nrel (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    ∼(nrel R v : Semiformula L Ξ ξ N n) = rel R v := rfl

@[simp] lemma neg_bvar (X : Fin N) (t : Semiterm L ξ n) :
    ∼(t ∈# X : Semiformula L Ξ ξ N n) = t ∉# X := rfl

@[simp] lemma neg_nbvar (X : Fin N) (t : Semiterm L ξ n) :
    ∼(t ∉# X : Semiformula L Ξ ξ N n) = t ∈# X := rfl

@[simp] lemma neg_fvar (X : Ξ) (t : Semiterm L ξ n) :
    ∼(t ∈& X : Semiformula L Ξ ξ N n) = t ∉& X := rfl

@[simp] lemma neg_nfvar (X : Ξ) (t : Semiterm L ξ n) :
    ∼(t ∉& X : Semiformula L Ξ ξ N n) = t ∈& X := rfl

@[simp] lemma neg_all₀ (φ : Semiformula L Ξ ξ N (n + 1)) :
    ∼(∀⁰ φ : Semiformula L Ξ ξ N n) = ∃⁰ ∼φ := rfl

@[simp] lemma neg_exs₀ (φ : Semiformula L Ξ ξ N (n + 1)) :
    ∼(∃⁰ φ : Semiformula L Ξ ξ N n) = ∀⁰ ∼φ := rfl

@[simp] lemma neg_all₁ (φ : Semiformula L Ξ ξ (N + 1) n) :
    ∼(∀¹ φ : Semiformula L Ξ ξ N n) = ∃¹ ∼φ := rfl

@[simp] lemma neg_exs₁ (φ : Semiformula L Ξ ξ (N + 1) n) :
    ∼(∃¹ φ : Semiformula L Ξ ξ N n) = ∀¹ ∼φ := rfl

lemma neg_neg (φ : Semiformula L Ξ ξ N n) : ∼∼φ = φ :=
  match φ with
  |  rel R v => rfl
  | nrel R v => rfl
  |   t ∈# X => rfl
  |   t ∉# X => rfl
  |   t ∈& X => rfl
  |   t ∉& X => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    φ ⋏ ψ => by simp [neg_neg φ, neg_neg ψ]
  |    φ ⋎ ψ => by simp [neg_neg φ, neg_neg ψ]
  |     ∀⁰ φ => by simp [neg_neg φ]
  |     ∃⁰ φ => by simp [neg_neg φ]
  |     ∀¹ φ => by simp [neg_neg φ]
  |     ∃¹ φ => by simp [neg_neg φ]

instance : NegInvolutive (Semiformula L Ξ ξ N n) := ⟨neg_neg⟩

@[simp] lemma and_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula L Ξ ξ N n} :
    φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := iff_of_eq (by apply and.injEq)

@[simp] lemma or_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula L Ξ ξ N n} :
    φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := iff_of_eq (by apply or.injEq)

@[simp] lemma all₀_inj {φ ψ : Semiformula L Ξ ξ N (n + 1)} :
    ∀⁰ φ = ∀⁰ ψ ↔ φ = ψ := iff_of_eq (by apply all₀.injEq)

@[simp] lemma exs₀_inj {φ ψ : Semiformula L Ξ ξ N (n + 1)} :
    ∃⁰ φ = ∃⁰ ψ ↔ φ = ψ := iff_of_eq (by apply exs₀.injEq)

@[simp] lemma all₁_inj {φ ψ : Semiformula L Ξ ξ (N + 1) n} :
    ∀¹ φ = ∀¹ ψ ↔ φ = ψ := iff_of_eq (by apply all₁.injEq)

@[simp] lemma exs₁_inj {φ ψ : Semiformula L Ξ ξ (N + 1) n} :
    ∃¹ φ = ∃¹ ψ ↔ φ = ψ := iff_of_eq (by apply exs₁.injEq)

@[elab_as_elim]
def cases' {C : ∀ N n, Semiformula L Ξ ξ N n → Sort w}
    (hRel : ∀ {N n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C N n (rel r v))
    (hNrel : ∀ {N n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C N n (nrel r v))
    (hBvar : ∀ {N n} (X : Fin N) (t : Semiterm L ξ n), C N n (t ∈# X))
    (hNbvar : ∀ {N n} (X : Fin N) (t : Semiterm L ξ n), C N n (t ∉# X))
    (hFvar : ∀ {N n} (X : Ξ) (t : Semiterm L ξ n), C N n (t ∈& X))
    (hNfvar : ∀ {N n} (X : Ξ) (t : Semiterm L ξ n), C N n (t ∉& X))
    (hVerum : ∀ {N n}, C N n ⊤)
    (hFalsum : ∀ {N n}, C N n ⊥)
    (hAnd : ∀ {N n} (φ ψ : Semiformula L Ξ ξ N n), C N n (φ ⋏ ψ))
    (hOr : ∀ {N n} (φ ψ : Semiformula L Ξ ξ N n), C N n (φ ⋎ ψ))
    (hAll₀ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N n (∀⁰ φ))
    (hExs₀ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N n (∃⁰ φ))
    (hAll₁ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C N n (∀¹ φ))
    (hExs₁ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C N n (∃¹ φ))
    {N n} : (φ : Semiformula L Ξ ξ N n) → C N n φ
  |  rel r v => hRel r v
  | nrel r v => hNrel r v
  |   t ∈# X => hBvar X t
  |   t ∉# X => hNbvar X t
  |   t ∈& X => hFvar X t
  |   t ∉& X => hNfvar X t
  |        ⊤ => hVerum
  |        ⊥ => hFalsum
  |    φ ⋏ ψ => hAnd φ ψ
  |    φ ⋎ ψ => hOr φ ψ
  |     ∀⁰ φ => hAll₀ φ
  |     ∃⁰ φ => hExs₀ φ
  |     ∀¹ φ => hAll₁ φ
  |     ∃¹ φ => hExs₁ φ

@[elab_as_elim]
def rec' {C : ∀ N n, Semiformula L Ξ ξ N n → Sort w}
    (hRel : ∀ {N n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C N n (rel r v))
    (hNrel : ∀ {N n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C N n (nrel r v))
    (hBvar : ∀ {N n} (X : Fin N) (t : Semiterm L ξ n), C N n (t ∈# X))
    (hNbvar : ∀ {N n} (X : Fin N) (t : Semiterm L ξ n), C N n (t ∉# X))
    (hFvar : ∀ {N n} (X : Ξ) (t : Semiterm L ξ n), C N n (t ∈& X))
    (hNfvar : ∀ {N n} (X : Ξ) (t : Semiterm L ξ n), C N n (t ∉& X))
    (hVerum : ∀ {N n}, C N n ⊤)
    (hFalsum : ∀ {N n}, C N n ⊥)
    (hAnd : ∀ {N n} (φ ψ : Semiformula L Ξ ξ N n), C N n φ → C N n ψ → C N n (φ ⋏ ψ))
    (hOr : ∀ {N n} (φ ψ : Semiformula L Ξ ξ N n), C N n φ → C N n ψ → C N n (φ ⋎ ψ))
    (hAll₀ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N (n + 1) φ → C N n (∀⁰ φ))
    (hExs₀ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N (n + 1) φ → C N n (∃⁰ φ))
    (hAll₁ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C (N + 1) n φ → C N n (∀¹ φ))
    (hExs₁ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C (N + 1) n φ → C N n (∃¹ φ))
    {N n} : (φ : Semiformula L Ξ ξ N n) → C N n φ
  |  rel r v => hRel r v
  | nrel r v => hNrel r v
  |   t ∈# X => hBvar X t
  |   t ∉# X => hNbvar X t
  |   t ∈& X => hFvar X t
  |   t ∉& X => hNfvar X t
  |        ⊤ => hVerum
  |        ⊥ => hFalsum
  |    φ ⋏ ψ => hAnd φ ψ
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₀ hExs₀ hAll₁ hExs₁ φ)
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₀ hExs₀ hAll₁ hExs₁ ψ)
  |    φ ⋎ ψ => hOr φ ψ
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₀ hExs₀ hAll₁ hExs₁ φ)
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₀ hExs₀ hAll₁ hExs₁ ψ)
  |     ∀⁰ φ => hAll₀ φ (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₀ hExs₀ hAll₁ hExs₁ φ)
  |     ∃⁰ φ => hExs₀ φ (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₀ hExs₀ hAll₁ hExs₁ φ)
  |     ∀¹ φ => hAll₁ φ (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₀ hExs₀ hAll₁ hExs₁ φ)
  |     ∃¹ φ => hExs₁ φ (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₀ hExs₀ hAll₁ hExs₁ φ)

def complexity : Semiformula L Ξ ξ N n → ℕ
  |  rel _ _ => 0
  | nrel _ _ => 0
  |   _ ∈# _ => 0
  |   _ ∉# _ => 0
  |   _ ∈& _ => 0
  |   _ ∉& _ => 0
  |        ⊤ => 0
  |        ⊥ => 0
  |    φ ⋏ ψ => max φ.complexity ψ.complexity + 1
  |    φ ⋎ ψ => max φ.complexity ψ.complexity + 1
  |     ∀⁰ φ => φ.complexity + 1
  |     ∃⁰ φ => φ.complexity + 1
  |     ∀¹ φ => φ.complexity + 1
  |     ∃¹ φ => φ.complexity + 1

@[simp] lemma complexity_rel {k} (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel R v : Semiformula L Ξ ξ N n).complexity = 0 := rfl

@[simp] lemma complexity_nrel {k} (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel R v : Semiformula L Ξ ξ N n).complexity = 0 := rfl

@[simp] lemma complexity_bvar (X : Fin N) (t : Semiterm L ξ n) :
    (t ∈# X : Semiformula L Ξ ξ N n).complexity = 0 := rfl

@[simp] lemma complexity_nbvar (X : Fin N) (t : Semiterm L ξ n) :
    (t ∉# X : Semiformula L Ξ ξ N n).complexity = 0 := rfl

@[simp] lemma complexity_fvar (X : Ξ) (t : Semiterm L ξ n) :
    (t ∈& X : Semiformula L Ξ ξ N n).complexity = 0 := rfl

@[simp] lemma complexity_nfvar (X : Ξ) (t : Semiterm L ξ n) :
    (t ∉& X : Semiformula L Ξ ξ N n).complexity = 0 := rfl

@[simp] lemma complexity_verum : (⊤ : Semiformula L Ξ ξ N n).complexity = 0 := rfl
@[simp] lemma complexity_verum' : (verum : Semiformula L Ξ ξ N n).complexity = 0 := rfl

@[simp] lemma complexity_falsum : (⊥ : Semiformula L Ξ ξ N n).complexity = 0 := rfl
@[simp] lemma complexity_falsum' : (falsum : Semiformula L Ξ ξ N n).complexity = 0 := rfl

@[simp] lemma complexity_and (φ ψ : Semiformula L Ξ ξ N n) :
    (φ ⋏ ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_and' (φ ψ : Semiformula L Ξ ξ N n) :
    (φ.and ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_or (φ ψ : Semiformula L Ξ ξ N n) :
    (φ ⋎ ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_or' (φ ψ : Semiformula L Ξ ξ N n) :
    (φ.or ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_all₀ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∀⁰ φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_all₀' (φ : Semiformula L Ξ ξ N (n + 1)) :
    φ.all₀.complexity = φ.complexity + 1 := rfl

@[simp] lemma complexity_exs₀ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∃⁰ φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_exs₀' (φ : Semiformula L Ξ ξ N (n + 1)) :
    φ.exs₀.complexity = φ.complexity + 1 := rfl

@[simp] lemma complexity_all₁ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∀¹ φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_all₁' (φ : Semiformula L Ξ ξ (N + 1) n) :
    φ.all₁.complexity = φ.complexity + 1 := rfl

@[simp] lemma complexity_exs₁ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∃¹ φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_exs₁' (φ : Semiformula L Ξ ξ (N + 1) n) :
    φ.exs₁.complexity = φ.complexity + 1 := rfl

end Semiformula

end SecondOrder

end LO
