module

public import Foundation.FirstOrder.Syntax.Classical.Formula

@[expose] public section
set_option autoImplicit true

/-!
# Formulas of monadic second-order logic
-/

namespace FFL.SecondOrder

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
  |   all₁ : Semiformula L Ξ ξ N (n + 1) → Semiformula L Ξ ξ N n
  |   exs₁ : Semiformula L Ξ ξ N (n + 1) → Semiformula L Ξ ξ N n
  |   all₂ : Semiformula L Ξ ξ (N + 1) n → Semiformula L Ξ ξ N n
  |   exs₂ : Semiformula L Ξ ξ (N + 1) n → Semiformula L Ξ ξ N n

abbrev Formula (L : Language) (Ξ ξ : Type*) := Semiformula L Ξ ξ 0 0

abbrev Semisentence (L : Language) (n N : ℕ) := Semiformula L Empty Empty n N

abbrev Sentence (L : Language) := Semiformula L Empty Empty 0 0

abbrev Semiproposition (L : Language) (n N : ℕ) := Semiformula L ℕ ℕ n N

abbrev Proposition (L : Language) := Semiformula L ℕ ℕ 0 0

abbrev Theory (L : Language) := Set (Sentence L)

namespace Semiformula

variable {L : Language} {Ξ ξ : Type*}

section Decidable

variable [L.DecidableEq] [DecidableEq Ξ] [DecidableEq ξ]

/-- Decides formula equality by structural recursion (a routine syntactic construction). -/
def hasDecEq : {N n : ℕ} → (φ ψ : Semiformula L Ξ ξ N n) → Decidable (φ = ψ)
  | _, _, φ, ψ => by
    cases φ <;> cases ψ <;> try { apply isFalse; intro h; cases h; done };
    case verum.verum => exact isTrue rfl;
    case falsum.falsum => exact isTrue rfl;
    case rel.rel k r v k' r' v' | nrel.nrel k r v k' r' v' =>
      by_cases h : k = k';
      · subst k';
        simpa only [rel.injEq, nrel.injEq, heq_eq_eq, true_and] using
          (inferInstance : Decidable (r = r' ∧ v = v'));
      · exact isFalse (by intro e; cases e; exact h rfl);
    case bvar.bvar X t Y u | nbvar.nbvar X t Y u |
        fvar.fvar X t Y u | nfvar.nfvar X t Y u =>
      simpa only [bvar.injEq, nbvar.injEq, fvar.injEq, nfvar.injEq] using
        (inferInstance : Decidable (X = Y ∧ t = u));
    case and.and φ ψ φ' ψ' | or.or φ ψ φ' ψ' =>
      letI := hasDecEq φ φ';
      letI := hasDecEq ψ ψ';
      simpa only [and.injEq, or.injEq] using
        (inferInstance : Decidable (φ = φ' ∧ ψ = ψ'));
    case all₁.all₁ φ ψ | exs₁.exs₁ φ ψ | all₂.all₂ φ ψ | exs₂.exs₂ φ ψ =>
      simpa only [all₁.injEq, exs₁.injEq, all₂.injEq, exs₂.injEq] using hasDecEq φ ψ;
termination_by _ _ φ _ => sizeOf φ
instance : DecidableEq (Semiformula L Ξ ξ N n) := hasDecEq

end Decidable

instance : Top (Semiformula L Ξ ξ N n) := ⟨verum⟩

instance : Bot (Semiformula L Ξ ξ N n) := ⟨falsum⟩

instance : LogicalNeutral (Semiformula L Ξ ξ N n) where
  top := verum
  bot := falsum

instance : Wedge (Semiformula L Ξ ξ N n) := ⟨and⟩

instance : Vee (Semiformula L Ξ ξ N n) := ⟨or⟩

instance : FirstOrder.Quantifier (Semiformula L Ξ ξ N) where
  all := all₁
  exs := exs₁

instance : SecondOrder.Quantifier (Semiformula L Ξ ξ) where
  all₁ := all₂
  exs₁ := exs₂

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
  |     ∀¹ φ => ∃¹ φ.neg
  |     ∃¹ φ => ∀¹ φ.neg
  |     ∀² φ => ∃² φ.neg
  |     ∃² φ => ∀² φ.neg

instance : Tilde (Semiformula L Ξ ξ N n) := ⟨neg⟩

instance : LogicalConnective (Semiformula L Ξ ξ N n) where
  arrow φ ψ := ∼φ ⋎ ψ

instance : LogicalConnective.DeMorgan (Semiformula L Ξ ξ N n) where
  imply _ _ := rfl
  and _ _ := rfl
  or _ _ := rfl

instance : LogicalNeutral.DeMorgan (Semiformula L Ξ ξ N n) where
  verum := rfl
  falsum := rfl

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

@[simp] lemma neg_all₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    ∼(∀¹ φ : Semiformula L Ξ ξ N n) = ∃¹ ∼φ := rfl

@[simp] lemma neg_exs₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    ∼(∃¹ φ : Semiformula L Ξ ξ N n) = ∀¹ ∼φ := rfl

@[simp] lemma neg_all₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    ∼(∀² φ : Semiformula L Ξ ξ N n) = ∃² ∼φ := rfl

@[simp] lemma neg_exs₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    ∼(∃² φ : Semiformula L Ξ ξ N n) = ∀² ∼φ := rfl

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
  |     ∀¹ φ => by simp [neg_neg φ]
  |     ∃¹ φ => by simp [neg_neg φ]
  |     ∀² φ => by simp [neg_neg φ]
  |     ∃² φ => by simp [neg_neg φ]

instance : TildeInvolutive (Semiformula L Ξ ξ N n) := ⟨neg_neg⟩

@[simp] lemma and_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula L Ξ ξ N n} :
    φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := iff_of_eq (by apply and.injEq)

@[simp] lemma or_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula L Ξ ξ N n} :
    φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := iff_of_eq (by apply or.injEq)

@[simp] lemma all₁_inj {φ ψ : Semiformula L Ξ ξ N (n + 1)} :
    ∀¹ φ = ∀¹ ψ ↔ φ = ψ := iff_of_eq (by apply all₁.injEq)

@[simp] lemma exs₁_inj {φ ψ : Semiformula L Ξ ξ N (n + 1)} :
    ∃¹ φ = ∃¹ ψ ↔ φ = ψ := iff_of_eq (by apply exs₁.injEq)

@[simp] lemma all₂_inj {φ ψ : Semiformula L Ξ ξ (N + 1) n} :
    ∀² φ = ∀² ψ ↔ φ = ψ := iff_of_eq (by apply all₂.injEq)

@[simp] lemma exs₂_inj {φ ψ : Semiformula L Ξ ξ (N + 1) n} :
    ∃² φ = ∃² ψ ↔ φ = ψ := iff_of_eq (by apply exs₂.injEq)

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
    (hAll₁ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N n (∀¹ φ))
    (hExs₁ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N n (∃¹ φ))
    (hAll₂ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C N n (∀² φ))
    (hExs₂ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C N n (∃² φ))
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
  |     ∀¹ φ => hAll₁ φ
  |     ∃¹ φ => hExs₁ φ
  |     ∀² φ => hAll₂ φ
  |     ∃² φ => hExs₂ φ

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
    (hAll₁ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N (n + 1) φ → C N n (∀¹ φ))
    (hExs₁ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N (n + 1) φ → C N n (∃¹ φ))
    (hAll₂ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C (N + 1) n φ → C N n (∀² φ))
    (hExs₂ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C (N + 1) n φ → C N n (∃² φ))
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
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ ψ)
  |    φ ⋎ ψ => hOr φ ψ
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ ψ)
  |     ∀¹ φ => hAll₁ φ
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)
  |     ∃¹ φ => hExs₁ φ
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)
  |     ∀² φ => hAll₂ φ
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)
  |     ∃² φ => hExs₂ φ
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)

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
  |     ∀¹ φ => φ.complexity + 1
  |     ∃¹ φ => φ.complexity + 1
  |     ∀² φ => φ.complexity + 1
  |     ∃² φ => φ.complexity + 1

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

@[simp] lemma complexity_all₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∀¹ φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_all₁' (φ : Semiformula L Ξ ξ N (n + 1)) :
    φ.all₁.complexity = φ.complexity + 1 := rfl

@[simp] lemma complexity_exs₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∃¹ φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_exs₁' (φ : Semiformula L Ξ ξ N (n + 1)) :
    φ.exs₁.complexity = φ.complexity + 1 := rfl

@[simp] lemma complexity_all₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∀² φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_all₂' (φ : Semiformula L Ξ ξ (N + 1) n) :
    φ.all₂.complexity = φ.complexity + 1 := rfl

@[simp] lemma complexity_exs₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∃² φ).complexity = φ.complexity + 1 := rfl
@[simp] lemma complexity_exs₂' (φ : Semiformula L Ξ ξ (N + 1) n) :
    φ.exs₂.complexity = φ.complexity + 1 := rfl

/- ### Elementary Semiformulas -/

inductive IsElementary : Semiformula L Ξ ξ N n → Prop
| rel {k} (R : L.Rel k) (v : Fin k → Semiterm L ξ n) : IsElementary (rel R v)
| nrel {k} (R : L.Rel k) (v : Fin k → Semiterm L ξ n) : IsElementary (nrel R v)
| bvar : IsElementary (t ∈# X)
| nbvar : IsElementary (t ∉# X)
| fvar : IsElementary (t ∈& X)
| nfvar : IsElementary (t ∉& X)
| verum : IsElementary ⊤
| falsum : IsElementary ⊥
| and (φ ψ : Semiformula L Ξ ξ N n) : IsElementary φ → IsElementary ψ → IsElementary (φ ⋏ ψ)
| or (φ ψ : Semiformula L Ξ ξ N n) : IsElementary φ → IsElementary ψ → IsElementary (φ ⋎ ψ)
| all₁ (φ : Semiformula L Ξ ξ N (n + 1)) : IsElementary φ → IsElementary (∀¹ φ)
| exs₁ (φ : Semiformula L Ξ ξ N (n + 1)) : IsElementary φ → IsElementary (∃¹ φ)

namespace IsElementary

attribute [simp] rel nrel verum falsum bvar nbvar fvar nfvar

@[simp] lemma and_iff {φ ψ : Semiformula L Ξ ξ N n} :
    (φ ⋏ ψ).IsElementary ↔ φ.IsElementary ∧ ψ.IsElementary := by
  constructor
  · intro h
    cases h with
    | and _ _ hφ hψ => exact ⟨hφ, hψ⟩
  · rintro ⟨hφ, hψ⟩
    exact .and _ _ hφ hψ

@[simp] lemma or_iff {φ ψ : Semiformula L Ξ ξ N n} :
    (φ ⋎ ψ).IsElementary ↔ φ.IsElementary ∧ ψ.IsElementary := by
  constructor
  · intro h
    cases h with
    | or _ _ hφ hψ => exact ⟨hφ, hψ⟩
  · rintro ⟨hφ, hψ⟩
    exact .or _ _ hφ hψ

@[simp] lemma all₁_iff {φ : Semiformula L Ξ ξ N (n + 1)} :
    (∀¹ φ).IsElementary ↔ φ.IsElementary := by
  constructor
  · intro h
    cases h with
    | all₁ _ hφ => exact hφ
  · exact .all₁ _

@[simp] lemma exs₁_iff {φ : Semiformula L Ξ ξ N (n + 1)} :
    (∃¹ φ).IsElementary ↔ φ.IsElementary := by
  constructor
  · intro h
    cases h with
    | exs₁ _ hφ => exact hφ
  · exact .exs₁ _

@[simp] lemma not_all₂ {φ : Semiformula L Ξ ξ (N + 1) n} :
    ¬(∀² φ).IsElementary := by
  intro h
  cases h

@[simp] lemma not_exs₂ {φ : Semiformula L Ξ ξ (N + 1) n} :
    ¬(∃² φ).IsElementary := by
  intro h
  cases h

end IsElementary

end Semiformula

end SecondOrder

namespace FirstOrder.Semiformula

variable (Ξ N)

def toSecondOrderAux : Semiformula L ξ n → SecondOrder.Semiformula L Ξ ξ N n
|  .rel R v => .rel R v
| .nrel R v => .nrel R v
|         ⊤ => ⊤
|         ⊥ => ⊥
|     φ ⋏ ψ => φ.toSecondOrderAux ⋏ ψ.toSecondOrderAux
|     φ ⋎ ψ => φ.toSecondOrderAux ⋎ ψ.toSecondOrderAux
|      ∀¹ φ => ∀¹ φ.toSecondOrderAux
|      ∃¹ φ => ∃¹ φ.toSecondOrderAux

lemma toSecondOrderAux_neg (φ : FirstOrder.Semiformula L ξ n) :
    (∼φ).toSecondOrderAux Ξ N = ∼φ.toSecondOrderAux Ξ N := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel R v => rfl
  | nrel R v => rfl
  | and φ ψ ihφ ihψ =>
    change (toSecondOrderAux Ξ N (∼φ)) ⋎ toSecondOrderAux Ξ N (∼ψ) =
      (∼toSecondOrderAux Ξ N φ) ⋎ ∼toSecondOrderAux Ξ N ψ
    rw [ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    change (toSecondOrderAux Ξ N (∼φ)) ⋏ toSecondOrderAux Ξ N (∼ψ) =
      (∼toSecondOrderAux Ξ N φ) ⋏ ∼toSecondOrderAux Ξ N ψ
    rw [ihφ, ihψ]
  | all φ ih =>
    change ∃¹ toSecondOrderAux Ξ N (∼φ) = ∃¹ ∼toSecondOrderAux Ξ N φ
    rw [ih]
  | exs φ ih =>
    change ∀¹ toSecondOrderAux Ξ N (∼φ) = ∀¹ ∼toSecondOrderAux Ξ N φ
    rw [ih]

def toSecondOrder : FirstOrder.Semiformula L ξ n →ˡᶜ SecondOrder.Semiformula L Ξ ξ N n where
  toTr := toSecondOrderAux Ξ N
  map_top' := rfl
  map_bot' := rfl
  map_neg' := toSecondOrderAux_neg Ξ N
  map_and' _ _ := rfl
  map_or' _ _ := rfl
  map_imply' φ ψ := by
    change (∼φ).toSecondOrderAux Ξ N ⋎ toSecondOrderAux Ξ N ψ =
      ∼toSecondOrderAux Ξ N φ ⋎ toSecondOrderAux Ξ N ψ
    rw [toSecondOrderAux_neg]

end Semiformula

@[coe] def Theory.toSecondOrder (T : Theory L) : SecondOrder.Theory L :=
  Semiformula.toSecondOrder Empty 0 '' T

instance : Coe (Theory L) (SecondOrder.Theory L) := ⟨Theory.toSecondOrder⟩

end FirstOrder

namespace SecondOrder.Semiformula

lemma isElementary_toSecondOrder (φ : FirstOrder.Semiformula L ξ n) :
    (φ.toSecondOrder Ξ N).IsElementary := by
  change (FirstOrder.Semiformula.toSecondOrderAux Ξ N φ).IsElementary
  induction φ with
  | verum => exact .verum
  | falsum => exact .falsum
  | rel R v => exact .rel R v
  | nrel R v => exact .nrel R v
  | and φ ψ ihφ ihψ => exact .and _ _ ihφ ihψ
  | or φ ψ ihφ ihψ => exact .or _ _ ihφ ihψ
  | all φ ih => exact .all₁ _ ih
  | exs φ ih => exact .exs₁ _ ih

end SecondOrder.Semiformula

end FFL
