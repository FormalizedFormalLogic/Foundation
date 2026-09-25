module

public import Foundation.Logic.Entailment
public import Foundation.Vorspiel.Finset.Basic

@[expose] public section

namespace FFL.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev NegEquiv [LogicalNeutral F] := ∼φ 🡘 (φ 🡒 ⊥)

protected abbrev Verum [LogicalNeutral F] : F := ⊤

protected abbrev ImplyK := φ 🡒 ψ 🡒 φ

protected abbrev ImplyS := (φ 🡒 ψ 🡒 χ) 🡒 (φ 🡒 ψ) 🡒 φ 🡒 χ

protected abbrev AndElim₁ := φ ⋏ ψ 🡒 φ

protected abbrev AndElim₂ := φ ⋏ ψ 🡒 ψ

protected abbrev AndInst := φ 🡒 ψ 🡒 φ ⋏ ψ

protected abbrev OrInst₁ := φ 🡒 φ ⋎ ψ

protected abbrev OrInst₂ := ψ 🡒 φ ⋎ ψ

protected abbrev OrElim := (φ 🡒 χ) 🡒 (ψ 🡒 χ) 🡒 (φ ⋎ ψ 🡒 χ)

end FFL.Axioms

namespace FFL.Entailment

section

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class ModusPonens (𝓢 : S) where
  mdp {φ ψ : F} : 𝓢 ⊢ φ 🡒 ψ → 𝓢 ⊢ φ → 𝓢 ⊢ ψ

export ModusPonens (mdp)

infixl:90 "⨀" => mdp

/-- Negation `∼φ` is equivalent to `φ 🡒 ⊥` on **system**.

This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ 🡒 ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv [LogicalNeutral F] (𝓢 : S) where
  neg_equiv {φ : F} : 𝓢 ⊢ Axioms.NegEquiv φ
export NegationEquiv (neg_equiv)

attribute [simp] neg_equiv

class HasAxiomVerum [LogicalNeutral F] (𝓢 : S) where
  verum : 𝓢 ⊢ Axioms.Verum
export HasAxiomVerum (verum)

attribute [simp] verum

class HasAxiomImplyK (𝓢 : S) where
  implyK {φ ψ : F} : 𝓢 ⊢ Axioms.ImplyK φ ψ
export HasAxiomImplyK (implyK)

attribute [simp] implyK

lemma C_of_conseq [ModusPonens 𝓢] [HasAxiomImplyK 𝓢] (h : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ 🡒 φ := implyK ⨀ h
alias dhyp := C_of_conseq

class HasAxiomImplyS (𝓢 : S) where
  implyS {φ ψ χ : F} : 𝓢 ⊢ Axioms.ImplyS φ ψ χ
export HasAxiomImplyS (implyS)

attribute [simp] implyS

class HasAxiomAndElim (𝓢 : S) where
  and₁ {φ ψ : F} : 𝓢 ⊢ Axioms.AndElim₁ φ ψ
  and₂ {φ ψ : F} : 𝓢 ⊢ Axioms.AndElim₂ φ ψ
export HasAxiomAndElim (and₁ and₂)

attribute [simp] and₁

@[grind ->] lemma K_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ φ := and₁ ⨀ d

attribute [simp] and₂

@[grind ->] lemma K_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ := and₂ ⨀ d

class HasAxiomAndInst (𝓢 : S) where
  and₃ {φ ψ : F} : 𝓢 ⊢ Axioms.AndInst φ ψ
export HasAxiomAndInst (and₃)

attribute [simp] and₃

@[grind <-] lemma K_intro [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢ φ) (d₂ : 𝓢 ⊢ ψ) :
    𝓢 ⊢ φ ⋏ ψ := and₃ ⨀ d₁ ⨀ d₂

class HasAxiomOrInst (𝓢 : S) where
  or₁ {φ ψ : F} : 𝓢 ⊢ Axioms.OrInst₁ φ ψ
  or₂ {φ ψ : F} : 𝓢 ⊢ Axioms.OrInst₂ φ ψ
export HasAxiomOrInst (or₁ or₂)

attribute [simp] or₁

@[grind .] lemma A_intro_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ φ ⋎ ψ := or₁ ⨀ d

attribute [simp] or₂

@[grind .] lemma A_intro_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋎ ψ := or₂ ⨀ d

class HasAxiomOrElim (𝓢 : S) where
  or₃ {φ ψ χ : F} : 𝓢 ⊢ Axioms.OrElim φ ψ χ
export HasAxiomOrElim (or₃)

attribute [simp] or₃

lemma left_A_intro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ 🡒 χ) (d₂ : 𝓢 ⊢ ψ 🡒 χ) :
    𝓢 ⊢ φ ⋎ ψ 🡒 χ := or₃ ⨀ d₁ ⨀ d₂
alias CA_of_C_of_C := left_A_intro

lemma of_C_of_C_of_A [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ 🡒 χ) (d₂ : 𝓢 ⊢ ψ 🡒 χ)
    (d₃ : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ χ := or₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
alias A_cases := of_C_of_C_of_A

protected class Minimal [LogicalNeutral F] (𝓢 : S) extends
              ModusPonens 𝓢,
              NegationEquiv 𝓢,
              HasAxiomVerum 𝓢,
              HasAxiomImplyK 𝓢, HasAxiomImplyS 𝓢,
              HasAxiomAndElim 𝓢, HasAxiomAndInst 𝓢,
              HasAxiomOrInst 𝓢, HasAxiomOrElim 𝓢

end

section

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} [ModusPonens 𝓢] {φ ψ χ : F}
variable {φ₁ φ₂ ψ₁ ψ₂ s t u : F}

lemma CO_of_N [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] :
    𝓢 ⊢ ∼φ → 𝓢 ⊢ φ 🡒 ⊥ := fun h => (K_left neg_equiv) ⨀ h
lemma N_of_CO [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] :
    𝓢 ⊢ φ 🡒 ⊥ → 𝓢 ⊢ ∼φ := fun h => (K_right neg_equiv) ⨀ h
@[grind =] lemma N_iff_CO [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] :
    𝓢 ⊢ ∼φ ↔ 𝓢 ⊢ φ 🡒 ⊥ := ⟨CO_of_N, N_of_CO⟩

@[grind ←] lemma E_intro [HasAxiomAndInst 𝓢] (b₁ : 𝓢 ⊢ φ 🡒 ψ) (b₂ : 𝓢 ⊢ ψ 🡒 φ) :
    𝓢 ⊢ φ 🡘 ψ := K_intro b₁ b₂

@[grind =] lemma K_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] :
    𝓢 ⊢ φ ⋏ ψ ↔ 𝓢 ⊢ φ ∧ 𝓢 ⊢ ψ := by grind
@[grind =] lemma E_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] :
    𝓢 ⊢ φ 🡘 ψ ↔ 𝓢 ⊢ φ 🡒 ψ ∧ 𝓢 ⊢ ψ 🡒 φ := ⟨fun h ↦ ⟨K_left h, K_right h⟩, by grind⟩

@[grind →] lemma C_of_E_mp [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢ φ 🡘 ψ) :
    𝓢 ⊢ φ 🡒 ψ := K_left h

@[grind →] lemma C_of_E_mpr [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢ φ 🡘 ψ) :
    𝓢 ⊢ ψ 🡒 φ := K_right h

@[grind →] lemma iff_of_E [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢ φ 🡘 ψ) :
    𝓢 ⊢ φ ↔ 𝓢 ⊢ ψ := ⟨fun hp ↦ K_left h ⨀ hp, fun hq ↦ K_right h ⨀ hq⟩

@[simp] theorem C_id [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] {φ : F} :
    𝓢 ⊢ φ 🡒 φ := implyS (φ := φ) (ψ := (φ 🡒 φ)) (χ := φ) ⨀ implyK ⨀ implyK

@[simp] theorem E_id [HasAxiomAndInst 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] {φ : F} :
    𝓢 ⊢ φ 🡘 φ := K_intro C_id C_id

instance [LogicalNeutral F] [NegAbbrev F] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    [HasAxiomAndInst 𝓢] : Entailment.NegationEquiv 𝓢 where
  neg_equiv := by simp [Axioms.NegEquiv, NegAbbrev.neg]

@[simp] lemma NO [LogicalNeutral F] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] [NegationEquiv 𝓢]
    [HasAxiomAndElim 𝓢] : 𝓢 ⊢ ∼⊥ := N_of_CO C_id

@[grind →] lemma mdp₁ [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ) (bq : 𝓢 ⊢ φ 🡒 ψ) :
    𝓢 ⊢ φ 🡒 χ := implyS ⨀ bqr ⨀ bq

infixl:90 "⨀₁" => mdp₁

@[grind →] lemma mdp₂ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s)
    (bq : 𝓢 ⊢ φ 🡒 ψ 🡒 χ) : 𝓢 ⊢ φ 🡒 ψ 🡒 s := C_of_conseq (implyS) ⨀₁ bqr ⨀₁ bq

infixl:90 "⨀₂" => mdp₂

@[grind →] lemma mdp₃ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s 🡒 t)
    (bq : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s) : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 t :=
  (C_of_conseq <| C_of_conseq <| implyS) ⨀₂ bqr ⨀₂ bq

infixl:90 "⨀₃" => mdp₃

@[grind →] lemma mdp₄ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s 🡒 t 🡒 u)
    (bq : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s 🡒 t) : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s 🡒 u :=
  (C_of_conseq <| C_of_conseq <| C_of_conseq <| implyS) ⨀₃ bqr ⨀₃ bq
infixl:90 "⨀₄" => mdp₄

@[grind <=] lemma C_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bpq : 𝓢 ⊢ φ 🡒 ψ)
    (bqr : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ φ 🡒 χ := implyS ⨀ C_of_conseq bqr ⨀ bpq

lemma C_replace [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢ ψ₁ 🡒 φ₁) (h₂ : 𝓢 ⊢ φ₂ 🡒 ψ₂) :
    𝓢 ⊢ φ₁ 🡒 φ₂ → 𝓢 ⊢ ψ₁ 🡒 ψ₂ := fun h => C_trans h₁ <| C_trans h h₂

lemma E_replace [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (h₁ : 𝓢 ⊢ φ₁ 🡘 ψ₁) (h₂ : 𝓢 ⊢ φ₂ 🡘 ψ₂) (h₃ : 𝓢 ⊢ φ₁ 🡘 φ₂) : 𝓢 ⊢ ψ₁ 🡘 ψ₂ := by
  apply E_intro;
  · exact C_replace (C_of_E_mpr h₁) (C_of_E_mp h₂) (C_of_E_mp h₃);
  · exact C_replace (C_of_E_mpr h₂) (C_of_E_mp h₁) (C_of_E_mpr h₃);

@[grind <=]
lemma E_trans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (h₁ : 𝓢 ⊢ φ 🡘 ψ) (h₂ : 𝓢 ⊢ ψ 🡘 χ) : 𝓢 ⊢ φ 🡘 χ := by
  apply E_intro;
  · exact C_trans (K_left h₁) (K_left h₂);
  · exact C_trans (K_right h₂) (K_right h₁);

@[grind .]
lemma CCCC [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 φ := C_trans implyK implyK

@[grind <=]
lemma CK_of_C_of_C [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (bq : 𝓢 ⊢ φ 🡒 ψ) (br : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ φ 🡒 ψ ⋏ χ := C_of_conseq and₃ ⨀₁ bq ⨀₁ br

@[simp, grind .] lemma CKK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢]
    [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ ⋏ ψ 🡒 ψ ⋏ φ := CK_of_C_of_C and₂ and₁

@[grind <-] lemma K_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢]
    [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ ⋏ φ := CKK ⨀ h

@[simp] lemma CEE [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    𝓢 ⊢ (φ 🡘 ψ) 🡒 (ψ 🡘 φ) := CKK

@[grind <-] lemma E_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢]
    [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ ψ 🡘 φ := CEE ⨀ h

@[simp, grind .] lemma ECKCC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢]
    [HasAxiomImplyS 𝓢] : 𝓢 ⊢ (φ ⋏ ψ 🡒 χ) 🡘 (φ 🡒 ψ 🡒 χ) := by
  let b₁ : 𝓢 ⊢ (φ ⋏ ψ 🡒 χ) 🡒 φ 🡒 ψ 🡒 χ := CCCC ⨀₃ C_of_conseq (ψ := φ ⋏ ψ 🡒 χ) and₃
  let b₂ : 𝓢 ⊢ (φ 🡒 ψ 🡒 χ) 🡒 φ ⋏ ψ 🡒 χ :=
    implyK ⨀₂ (C_of_conseq (ψ := φ 🡒 ψ 🡒 χ) and₁) ⨀₂ (C_of_conseq (ψ := φ 🡒 ψ 🡒 χ) and₂);
  exact E_intro b₁ b₂

lemma CC_of_CK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (d : 𝓢 ⊢ φ ⋏ ψ 🡒 χ) : 𝓢 ⊢ φ 🡒 ψ 🡒 χ := (K_left <| ECKCC) ⨀ d
lemma CK_of_CC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (d : 𝓢 ⊢ φ 🡒 ψ 🡒 χ) : 𝓢 ⊢ φ ⋏ ψ 🡒 χ := (K_right <| ECKCC) ⨀ d

@[grind =] lemma CK_iff_CC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢]
    [HasAxiomImplyS 𝓢] : (𝓢 ⊢ φ ⋏ ψ 🡒 χ) ↔ (𝓢 ⊢ φ 🡒 ψ 🡒 χ) := iff_of_E ECKCC

@[simp] lemma CV [LogicalNeutral F] [HasAxiomVerum 𝓢] [HasAxiomImplyK 𝓢] :
    𝓢 ⊢ φ 🡒 ⊤ := C_of_conseq verum

@[grind →]
lemma unprovable_C_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hpq : 𝓢 ⊢ φ 🡒 ψ) :
    𝓢 ⊬ φ 🡒 χ → 𝓢 ⊬ ψ 🡒 χ := by
  contrapose!;
  exact C_trans hpq;

@[grind →]
lemma uniff_of_E [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (H : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊬ φ ↔ 𝓢 ⊬ ψ := by
  constructor;
  · intro hp hq; have := K_right H ⨀ hq; contradiction;
  · intro hq hp; have := K_left H ⨀ hp; contradiction;

end

section

variable {S F : Type*} [LogicalConnective F] [LogicalNeutral F] [Entailment S F]
variable {𝓢 : S} [Entailment.Minimal 𝓢] {φ ψ χ : F}

variable {Γ Δ : List F}

theorem conj₂_nth : (Γ : List F) → (n : ℕ) → (hn : n < Γ.length) → 𝓢 ⊢ ⋀Γ 🡒 Γ[n]
  |          [],     _, hn => by simp at hn
  |         [ψ],     0, _  => C_id
  | φ :: ψ :: Γ,     0, _  => and₁
  | φ :: ψ ::
    Γ, n + 1, hn => C_trans (and₂ (φ := φ)) (conj₂_nth (ψ :: Γ) n (Nat.succ_lt_succ_iff.mp hn))

open scoped Classical in
lemma left_Conj_intro {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢ Γ.conj 🡒 φ :=
  match Γ with
  |     [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ
    then e ▸ and₁
    else
      have : φ ∈ Γ := by simpa [e] using h
      C_trans and₂ (left_Conj_intro this)

lemma Conj_intro {Γ : List F} (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ Γ.conj :=
  match Γ with
  |     [] => verum
  | ψ :: Γ => K_intro (b ψ (by simp)) (Conj_intro (fun ψ hq ↦ b ψ (by simp [hq])))

theorem right_Conj_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ φ 🡒 Γ.conj :=
  match Γ with
  |     [] => C_of_conseq verum
  | ψ :: Γ => CK_of_C_of_C (b ψ (by simp)) (right_Conj_intro φ Γ (fun ψ hq ↦ b ψ (by simp [hq])))

open scoped Classical in
lemma CConjConj (h : Δ ⊆ Γ) :
    𝓢 ⊢ Γ.conj 🡒 Δ.conj := right_Conj_intro _ _ (fun _ hq ↦ left_Conj_intro (h hq))

open scoped Classical in
lemma left_Conj₂_intro {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ 🡒 φ :=
  have : Γ.idxOf φ < Γ.length := List.idxOf_lt_length_of_mem h
  cast <| conj₂_nth Γ (Γ.idxOf φ) (by assumption)

lemma Conj₂_intro {Γ : List F} (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ ⋀Γ :=
  match Γ with
  |          [] => verum
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => K_intro (b ψ (by simp)) (Conj₂_intro (by aesop))

lemma right_Conj₂_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ φ 🡒 ⋀Γ :=
  match Γ with
  |          [] => C_of_conseq verum
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by
    apply CK_of_C_of_C (b ψ (by simp)) (right_Conj₂_intro φ _ (fun ψ hq ↦ b ψ (by simp [hq])));

open scoped Classical in
lemma CConj₂Conj₂ {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢ ⋀Γ 🡒 ⋀Δ :=
  right_Conj₂_intro _ _ (fun _ hq ↦ left_Conj₂_intro (h hq))

section

variable {G T : Type*} [Entailment T G] [LogicalConnective G] [LogicalNeutral G] {𝓣 : T}

abbrev Minimal.ofEquiv (𝓢 : S) [Entailment.Minimal 𝓢] (𝓣 : T)
    (f : G →ˡᶜ F) (e : ∀ φ, 𝓢 ⊢ f φ ↔ 𝓣 ⊢ φ) : Entailment.Minimal 𝓣 where
  mdp {φ ψ} dpq dp := (e ψ).mp <| (by simpa using (e (φ 🡒 ψ)).mpr dpq) ⨀ (e φ).mpr dp
  neg_equiv := (e _).mp (by simp)
  verum := (e _).mp (by simp)
  implyK := (e _).mp (by simp)
  implyS := (e _).mp (by simp)
  and₁ := (e _).mp (by simp)
  and₂ := (e _).mp (by simp)
  and₃ := (e _).mp (by simp)
  or₁ := (e _).mp (by simp)
  or₂ := (e _).mp (by simp)
  or₃ := (e _).mp (by simp)

end

end

section

variable {F : Type*} {S : Type*}

structure FiniteContext (F) (𝓢 : S) where
  ctx : List F

namespace FiniteContext

variable {𝓢 : S}

instance : Coe (List F) (FiniteContext F 𝓢) := ⟨mk⟩

abbrev conj [LogicalConnective F] [LogicalNeutral F] (Γ : FiniteContext F 𝓢) : F := ⋀Γ.ctx

abbrev disj [LogicalConnective F] [LogicalNeutral F] (Γ : FiniteContext F 𝓢) : F := ⋁Γ.ctx

instance : EmptyCollection (FiniteContext F 𝓢) := ⟨⟨[]⟩⟩

instance : Membership F (FiniteContext F 𝓢) := ⟨fun Γ x => (x ∈ Γ.ctx)⟩

instance : HasSubset (FiniteContext F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Adjoin F (FiniteContext F 𝓢) := ⟨(· :: ·.ctx)⟩

lemma mem_def {φ : F} {Γ : FiniteContext F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx := iff_of_eq rfl

@[simp] lemma coe_subset_coe_iff {Γ Δ : List F} :
    (Γ : FiniteContext F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl

@[simp] lemma mem_coe_iff {φ : F} {Γ : List F} :
    φ ∈ (Γ : FiniteContext F 𝓢) ↔ φ ∈ Γ := iff_of_eq rfl

@[simp] lemma not_mem_empty (φ : F) :
    ¬φ ∈ (∅ : FiniteContext F 𝓢) := by simp [EmptyCollection.emptyCollection]

instance : AdjunctiveSet F (FiniteContext F 𝓢) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin, mem_def]

variable [Entailment S F] [LogicalConnective F] [LogicalNeutral F]
variable {Γ : List F} {φ ψ χ : F}

instance (𝓢 : S) : Entailment (FiniteContext F 𝓢) F := ⟨(𝓢 ⊢ ·.conj 🡒 ·)⟩

abbrev Provable (𝓢 : S) (Γ : List F) (φ : F) : Prop := (Γ : FiniteContext F 𝓢) ⊢ φ

abbrev Unprovable (𝓢 : S) (Γ : List F) (φ : F) : Prop := (Γ : FiniteContext F 𝓢) ⊬ φ

abbrev ProvableSet (𝓢 : S) (Γ : List F) (s : Set F) : Prop := (Γ : FiniteContext F 𝓢) ⊢* s

notation Γ:45 " ⊢[" 𝓢 "] " φ:46 => Provable 𝓢 Γ φ

notation Γ:45 " ⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ

notation Γ:45 " ⊢[" 𝓢 "]* " s:46 => ProvableSet 𝓢 Γ s

lemma entailment_def (Γ : FiniteContext F 𝓢) (φ : F) : (Γ ⊢ φ) = (𝓢 ⊢ Γ.conj 🡒 φ) := rfl

lemma toₛ (b : Γ ⊢[𝓢] φ) : 𝓢 ⊢ ⋀Γ 🡒 φ := b

lemma provable_iff {φ : F} : Γ ⊢[𝓢] φ ↔ 𝓢 ⊢ ⋀Γ 🡒 φ := iff_of_eq rfl

section

variable {Γ Δ E : List F}
variable [Entailment.Minimal 𝓢]

open scoped Classical in
instance : Axiomatized (FiniteContext F 𝓢) where
  prfAxm := fun hp ↦ left_Conj₂_intro hp
  weakening := fun H _ b ↦ C_trans (CConj₂Conj₂ H) b

instance : Compact (FiniteContext F 𝓢) where
  finite_provable {Γ _} b :=
    ⟨Γ, by simp, by rcases Γ; simp [AdjunctiveSet.Finite, AdjunctiveSet.set], b⟩

lemma nth_axm {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢] Γ[n] := conj₂_nth Γ n h

open scoped Classical in
lemma by_axm {φ} (h : φ ∈ Γ := by simp) : Γ ⊢[𝓢] φ := Axiomatized.prfAxm (by simpa)

open scoped Classical in
lemma weakening (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢] φ → Δ ⊢[𝓢] φ := Axiomatized.weakening (by simpa)

lemma of {φ : F} (b : 𝓢 ⊢ φ) : Γ ⊢[𝓢] φ := C_of_conseq (ψ := ⋀Γ) b

lemma emptyPrf {φ : F} : [] ⊢[𝓢] φ → 𝓢 ⊢ φ := fun b ↦ b ⨀ verum

theorem provable_iff_provable {φ : F} : 𝓢 ⊢ φ ↔ [] ⊢[𝓢] φ :=
  ⟨of, emptyPrf⟩

open scoped Classical in
lemma of' (h : 𝓢 ⊢ φ) : Γ ⊢[𝓢] φ := weakening (by simp) <| provable_iff_provable.mp h

@[simp] lemma id : [φ] ⊢[𝓢] φ := nth_axm 0

lemma by_axm₀ : (φ :: Γ) ⊢[𝓢] φ := nth_axm 0

lemma by_axm₁ : (φ :: ψ :: Γ) ⊢[𝓢] ψ := nth_axm 1

lemma by_axm₂ : (φ :: ψ :: χ :: Γ) ⊢[𝓢] χ := nth_axm 2

instance (Γ : FiniteContext F 𝓢) : Entailment.ModusPonens Γ := ⟨mdp₁⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomVerum Γ := ⟨of verum⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImplyK Γ := ⟨of implyK⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImplyS Γ := ⟨of implyS⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndElim Γ := ⟨of and₁, of and₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndInst Γ := ⟨of and₃⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrInst Γ := ⟨of or₁, of or₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrElim Γ := ⟨of or₃⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.NegationEquiv Γ := ⟨of neg_equiv⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.Minimal Γ where

open scoped Classical in
lemma mdp' (bΓ : Γ ⊢[𝓢] φ 🡒 ψ) (bΔ : Δ ⊢[𝓢] φ) : (Γ ++ Δ) ⊢[𝓢] ψ :=
  wk (by simp) bΓ ⨀ wk (by simp) bΔ

lemma deduct {φ ψ : F} : {Γ : List F} → (φ :: Γ) ⊢[𝓢] ψ → Γ ⊢[𝓢] φ 🡒 ψ
  | .nil => fun b ↦ provable_iff.mpr <| C_of_conseq (toₛ b)
  | .cons _ _ => fun b ↦ provable_iff.mpr <| CC_of_CK (C_trans CKK (toₛ b))

lemma deductInv {φ ψ : F} : {Γ : List F} → Γ ⊢[𝓢] φ 🡒 ψ → (φ :: Γ) ⊢[𝓢] ψ
  | .nil => fun b ↦ provable_iff.mpr <| toₛ b ⨀ verum
  | .cons _ _ => fun b ↦ provable_iff.mpr <| C_trans CKK (CK_of_CC (toₛ b))

lemma deduct_iff {φ ψ : F} {Γ : List F} : Γ ⊢[𝓢] φ 🡒 ψ ↔ (φ :: Γ) ⊢[𝓢] ψ :=
  ⟨deductInv, deduct⟩

lemma deduct' : [φ] ⊢[𝓢] ψ → 𝓢 ⊢ φ 🡒 ψ := fun b ↦ emptyPrf <| deduct b

lemma deductInv' : 𝓢 ⊢ φ 🡒 ψ → [φ] ⊢[𝓢] ψ := fun b ↦ deductInv <| of b

instance deduction : Deduction (FiniteContext F 𝓢) where
  ofInsert := deduct
  inv := deductInv

open scoped Classical in
instance : StrongCut (FiniteContext F 𝓢) (FiniteContext F 𝓢) :=
  ⟨fun {Γ Δ _} bΓ bΔ ↦
    have : Γ ⊢ Δ.conj := Conj₂_intro (fun _ hp ↦ bΓ hp)
    C_trans this bΔ⟩

end

end FiniteContext

variable (F)

structure Context (𝓢 : S) where
  ctx : Set F

variable {F}

namespace Context

variable {𝓢 : S}

instance : Coe (Set F) (Context F 𝓢) := ⟨mk⟩

instance : EmptyCollection (Context F 𝓢) := ⟨⟨∅⟩⟩

instance : Membership F (Context F 𝓢) := ⟨fun Γ x => (x ∈ Γ.ctx)⟩

instance : HasSubset (Context F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Adjoin F (Context F 𝓢) := ⟨(⟨insert · ·.ctx⟩)⟩

lemma mem_def {φ : F} {Γ : Context F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx := iff_of_eq rfl

@[simp] lemma coe_subset_coe_iff {Γ Δ : Set F} : (Γ : Context F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl

@[simp] lemma mem_coe_iff {φ : F} {Γ : Set F} : φ ∈ (Γ : Context F 𝓢) ↔ φ ∈ Γ := iff_of_eq rfl

@[simp] lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ : Context F 𝓢) := by exact fun a ↦ a

instance : AdjunctiveSet F (Context F 𝓢) where
  subset_iff := by rintro ⟨s⟩ ⟨u⟩; simp [Set.subset_def]
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin, mem_def]

variable [LogicalConnective F] [LogicalNeutral F] [Entailment S F]

instance (𝓢 : S) : Entailment (Context F 𝓢) F :=
  ⟨fun Γ φ ↦ ∃ Δ : List F, (∀ ψ ∈ Δ, ψ ∈ Γ) ∧ Δ ⊢[𝓢] φ⟩

variable (𝓢)

abbrev Provable (Γ : Set F) (φ : F) : Prop := (Γ : Context F 𝓢) ⊢ φ

abbrev Unprovable (Γ : Set F) (φ : F) : Prop := (Γ : Context F 𝓢) ⊬ φ

abbrev ProvableSet (Γ : Set F) (s : Set F) : Prop := (Γ : Context F 𝓢) ⊢* s

notation Γ:45 " *⊢[" 𝓢 "] " φ:46 => Provable 𝓢 Γ φ

notation Γ:45 " *⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ

notation Γ:45 " *⊢[" 𝓢 "]* " s:46 => ProvableSet 𝓢 Γ s

section

variable {𝓢}
variable {Γ Δ : Set F} {φ ψ χ : F}

lemma provable_iff {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : List F, (∀ ψ ∈ Δ, ψ ∈ Γ) ∧ Δ ⊢[𝓢] φ := Iff.rfl

section minimal

variable [Entailment.Minimal 𝓢]

open scoped Classical in
instance : Axiomatized (Context F 𝓢) where
  prfAxm := fun {Γ φ} hp ↦ ⟨[φ], by simpa using hp, FiniteContext.by_axm⟩
  weakening := fun h _ ⟨Δ, hΔ, b⟩ ↦ ⟨Δ, fun φ hp ↦ AdjunctiveSet.subset_iff.mp h φ (hΔ φ hp), b⟩

instance : Compact (Context F 𝓢) where
  finite_provable := fun {Γ _} ⟨Δ, hΔ, b⟩ ↦
    ⟨AdjunctiveSet.set Δ, by rcases Γ; exact hΔ, by simp [AdjunctiveSet.Finite, AdjunctiveSet.set],
      ⟨Δ, by simp [AdjunctiveSet.set], b⟩⟩

open scoped Classical in
lemma deduct {φ ψ : F} {Γ : Set F} : (insert φ Γ) *⊢[𝓢] ψ → Γ *⊢[𝓢] φ 🡒 ψ
  | ⟨Δ, h, b⟩ =>
    have h : ∀ ψ ∈ Δ, ψ = φ ∨ ψ ∈ Γ := by simpa using h
    have b' : (φ :: Δ.filter (· ≠ φ)) ⊢[𝓢] ψ :=
      FiniteContext.weakening
        (by simp [List.subset_def, List.mem_filter]; grind)
        b
    ⟨ Δ.filter (· ≠ φ), by
      intro ψ
      suffices ψ ∈ Δ → ψ ≠ φ → ψ ∈ Γ by simpa [List.mem_filter]
      intro hq ne
      rcases h ψ hq
      · contradiction
      · assumption,
      FiniteContext.deduct b' ⟩

lemma deductInv {φ ψ : F} {Γ : Set F} : Γ *⊢[𝓢] φ 🡒 ψ → (insert φ Γ) *⊢[𝓢] ψ
  | ⟨Δ, h, b⟩ => ⟨φ :: Δ, by simpa using fun χ hr ↦ Or.inr (h χ hr), FiniteContext.deductInv b⟩

open scoped Classical in
instance deduction : Deduction (Context F 𝓢) where
  ofInsert := deduct
  inv := deductInv

open scoped Classical in
lemma weakening (h : Γ ⊆ Δ) {φ : F} : Γ *⊢[𝓢] φ → Δ *⊢[𝓢] φ := Axiomatized.weakening (by simpa)

lemma of {φ : F} (b : 𝓢 ⊢ φ) : Γ *⊢[𝓢] φ := ⟨[], by simp, FiniteContext.of b⟩

open scoped Classical in
lemma mdp {Γ : Set F} : Γ *⊢[𝓢] φ 🡒 ψ → Γ *⊢[𝓢] φ → Γ *⊢[𝓢] ψ
  | ⟨Δ₁, h₁, b₁⟩, ⟨Δ₂, h₂, b₂⟩ =>
    ⟨Δ₁ ++ Δ₂, fun χ hχ ↦ (List.mem_append.mp hχ).elim (h₁ χ) (h₂ χ), FiniteContext.mdp' b₁ b₂⟩

open scoped Classical in
lemma by_axm (h : φ ∈ Γ) : Γ *⊢[𝓢] φ := Entailment.by_axm (by simpa)

lemma emptyPrf {φ : F} : ∅ *⊢[𝓢] φ → 𝓢 ⊢ φ := by
  rintro ⟨Γ, hΓ, h⟩;
  have := List.eq_nil_iff_forall_not_mem.mpr hΓ;
  subst this;
  exact FiniteContext.emptyPrf h;

lemma provable_iff_provable {φ : F} : 𝓢 ⊢ φ ↔ ∅ *⊢[𝓢] φ := ⟨of, emptyPrf⟩

open scoped Classical in
lemma iff_provable_context_provable_finiteContext_toList {Δ : Finset F} :
    ↑Δ *⊢[𝓢] φ ↔ Δ.toList ⊢[𝓢] φ := by
  constructor;
  · intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply FiniteContext.weakening ?_ hΓ₂;
    intro ψ hψ;
    simpa using hΓ₁ ψ hψ;
  · intro h;
    apply Context.provable_iff.mpr;
    use Δ.toList;
    constructor;
    · simp only [Finset.mem_toList, SetLike.mem_coe];
      tauto;
    · assumption;

open scoped Classical in
instance minimal (Γ : Context F 𝓢) : Entailment.Minimal Γ where
  mdp := mdp
  verum := of verum
  implyK := of implyK
  implyS := of implyS
  and₁ := of and₁
  and₂ := of and₂
  and₃ := of and₃
  or₁ := of or₁
  or₂ := of or₂
  or₃ := of or₃
  neg_equiv := of neg_equiv

end minimal

end

end Context

end

section

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F]
         {S : Type*} [Entailment S F]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open List

@[simp] lemma CVNO : 𝓢 ⊢ ⊤ 🡒 ∼⊥ := deduct' NO

open scoped Classical in
lemma inner_mdp : 𝓢 ⊢ φ ⋏ (φ 🡒 ψ) 🡒 ψ := by
  apply deduct';
  have hp  : [φ, φ 🡒 ψ] ⊢[𝓢] φ := FiniteContext.by_axm;
  have hpq : [φ, φ 🡒 ψ] ⊢[𝓢] φ 🡒 ψ := FiniteContext.by_axm;
  exact hpq ⨀ hp;

open scoped Classical in
lemma bot_of_mem_either (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ⊥ := by
  have hp : Γ ⊢[𝓢] φ := FiniteContext.by_axm h₁;
  have hnp : Γ ⊢[𝓢] φ 🡒 ⊥ := CO_of_N <| FiniteContext.by_axm h₂;
  exact hnp ⨀ hp

lemma neg_mdp (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ := (CO_of_N hnp) ⨀ hn

lemma right_A_intro_left (h : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ φ 🡒 (χ ⋎ ψ) := by
  apply deduct';
  apply A_intro_left;
  apply deductInv;
  exact of h;

lemma right_A_intro_right (h : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ ψ 🡒 (φ ⋎ χ) := by
  apply deduct';
  apply A_intro_right;
  apply deductInv;
  exact of h;

open scoped Classical in
lemma right_K_intro (hq : 𝓢 ⊢ φ 🡒 ψ) (hr : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ φ 🡒 ψ ⋏ χ := by
  apply deduct';
  replace hq : [] ⊢[𝓢] φ 🡒 ψ := of hq;
  replace hr : [] ⊢[𝓢] φ 🡒 χ := of hr;
  exact K_intro (mdp' hq FiniteContext.id) (mdp' hr FiniteContext.id)

lemma left_K_symm (d : 𝓢 ⊢ φ ⋏ ψ 🡒 χ) : 𝓢 ⊢ ψ ⋏ φ 🡒 χ := C_trans CKK d

open scoped Classical in
lemma left_K_intro_right (h : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ (ψ ⋏ φ) 🡒 χ := by
  apply CK_iff_CC.mpr;
  apply deduct';
  exact FiniteContext.of' (Γ := [ψ]) h;

open scoped Classical in
lemma left_K_intro_left (h : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ (φ ⋏ ψ) 🡒 χ := C_trans CKK (left_K_intro_right h)

open scoped Classical in
lemma cut {c : F} (d₁ : 𝓢 ⊢ φ₁ ⋏ c 🡒 ψ₁) (d₂ : 𝓢 ⊢ φ₂ 🡒 c ⋎ ψ₂) :
    𝓢 ⊢ φ₁ ⋏ φ₂ 🡒 ψ₁ ⋎ ψ₂ := by
  apply deduct';
  exact of_C_of_C_of_A (right_A_intro_left <| of' (CK_iff_CC.mp d₁) ⨀ (K_left id)) or₂
    (of' d₂ ⨀ K_right id);

lemma CAA : 𝓢 ⊢ φ ⋎ ψ 🡒 ψ ⋎ φ := by
  apply deduct';
  exact of_C_of_C_of_A or₂ or₁ <| FiniteContext.id

lemma A_symm (h : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ψ ⋎ φ := CAA ⨀ h

lemma A_assoc : 𝓢 ⊢ φ ⋎ (ψ ⋎ χ) ↔ 𝓢 ⊢ (φ ⋎ ψ) ⋎ χ := by
  constructor;
  · intro h;
    exact of_C_of_C_of_A
      (right_A_intro_left <| right_A_intro_left C_id)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact of_C_of_C_of_A (right_A_intro_left <| right_A_intro_right C_id)
          (right_A_intro_right C_id) id;
      )
      h;
  · intro h;
    exact of_C_of_C_of_A
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact of_C_of_C_of_A (right_A_intro_left C_id)
          (right_A_intro_right <| right_A_intro_left C_id) id;
      )
      (right_A_intro_right <| right_A_intro_right C_id)
      h;

lemma K_assoc : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ 🡘 φ ⋏ (ψ ⋏ χ) := by
  apply E_intro;
  · apply FiniteContext.deduct';
    have hp : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] φ := K_left <| K_left id;
    have hq : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] ψ := K_right <| K_left id;
    have hr : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] χ := K_right id;
    exact K_intro hp (K_intro hq hr);
  · apply FiniteContext.deduct';
    have hp : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] φ := K_left id;
    have hq : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] ψ := K_left <| K_right id;
    have hr : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] χ := K_right <| K_right id;
    apply K_intro;
    · exact K_intro hp hq;
    · exact hr;

lemma K_assoc_mp (h : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ) : 𝓢 ⊢ φ ⋏ (ψ ⋏ χ) := C_of_E_mp K_assoc ⨀ h
lemma K_assoc_mpr (h : 𝓢 ⊢ φ ⋏ (ψ ⋏ χ)) : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ := C_of_E_mpr K_assoc ⨀ h

lemma K_replace_left (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ φ 🡒 χ) :
    𝓢 ⊢ χ ⋏ ψ := K_intro (h ⨀ K_left hc) (K_right hc)

lemma CKK_of_C (h : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ φ ⋏ ψ 🡒 χ ⋏ ψ := by
  apply deduct';
  exact K_replace_left FiniteContext.id (of h)

lemma K_replace_right (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ ψ 🡒 χ) :
    𝓢 ⊢ φ ⋏ χ := K_intro (K_left hc) (h ⨀ K_right hc)

lemma CKK_of_C' (h : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ φ ⋏ ψ 🡒 φ ⋏ χ := by
  apply deduct';
  exact K_replace_right (FiniteContext.id) (of h)

lemma K_replace (hc : 𝓢 ⊢ φ ⋏ ψ) (h₁ : 𝓢 ⊢ φ 🡒 χ) (h₂ : 𝓢 ⊢ ψ 🡒 ξ) :
    𝓢 ⊢ χ ⋏ ξ := K_replace_right (K_replace_left hc h₁) h₂

lemma CKK_of_C_of_C (h₁ : 𝓢 ⊢ φ 🡒 χ) (h₂ : 𝓢 ⊢ ψ 🡒 ξ) : 𝓢 ⊢ φ ⋏ ψ 🡒 χ ⋏ ξ := by
  apply deduct';
  exact K_replace FiniteContext.id (of h₁) (of h₂)

lemma A_replace_left (hc : 𝓢 ⊢ φ ⋎ ψ) (hp : 𝓢 ⊢ φ 🡒 χ) :
    𝓢 ⊢ χ ⋎ ψ := of_C_of_C_of_A (C_trans hp or₁) (or₂) hc

lemma CAA_of_C_left (hp : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ φ ⋎ ψ 🡒 χ ⋎ ψ := by
  apply deduct';
  exact A_replace_left FiniteContext.id (of hp)

lemma A_replace_right (hc : 𝓢 ⊢ φ ⋎ ψ) (hq : 𝓢 ⊢ ψ 🡒 χ) :
    𝓢 ⊢ φ ⋎ χ := of_C_of_C_of_A (or₁) (C_trans hq or₂) hc

lemma CAA_of_C_right (hq : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ φ ⋎ ψ 🡒 φ ⋎ χ := by
  apply deduct';
  exact A_replace_right FiniteContext.id (of hq)

lemma A_replace (h : 𝓢 ⊢ φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢ φ₁ 🡒 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡒 ψ₂) :
    𝓢 ⊢ φ₂ ⋎ ψ₂ := A_replace_right (A_replace_left h hp) hq

lemma CAA_of_C_of_C (hp : 𝓢 ⊢ φ₁ 🡒 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡒 ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ 🡒 φ₂ ⋎ ψ₂ := by
  apply deduct';
  exact A_replace FiniteContext.id (of hp) (of hq) ;

lemma EAA_of_E_of_E (hp : 𝓢 ⊢ φ₁ 🡘 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡘 ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ 🡘 φ₂ ⋎ ψ₂ := by
  apply E_intro;
  · exact CAA_of_C_of_C (K_left hp) (K_left hq);
  · exact CAA_of_C_of_C (K_right hp) (K_right hq);

lemma EAAAA : 𝓢 ⊢ φ ⋎ (ψ ⋎ χ) 🡘 (φ ⋎ ψ) ⋎ χ := by
  apply E_intro;
  · exact deduct' <| A_assoc.mp id;
  · exact deduct' <| A_assoc.mpr id;

lemma EAA_of_E_right (d : 𝓢 ⊢ ψ 🡘 χ) : 𝓢 ⊢ φ ⋎ ψ 🡘 φ ⋎ χ := by
  apply E_intro;
  · apply CAA_of_C_right; exact K_left d;
  · apply CAA_of_C_right; exact K_right d;

lemma EAA_of_E_left (d : 𝓢 ⊢ φ 🡘 χ) : 𝓢 ⊢ φ ⋎ ψ 🡘 χ ⋎ ψ := by
  apply E_intro;
  · apply CAA_of_C_left; exact K_left d;
  · apply CAA_of_C_left; exact K_right d;

lemma EKK_of_E_of_E (hp : 𝓢 ⊢ φ₁ 🡘 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡘 ψ₂) : 𝓢 ⊢ φ₁ ⋏ ψ₁ 🡘 φ₂ ⋏ ψ₂ := by
  apply E_intro;
  · exact CKK_of_C_of_C (K_left hp) (K_left hq);
  · exact CKK_of_C_of_C (K_right hp) (K_right hq);

lemma ECC_of_E_of_E (hp : 𝓢 ⊢ φ₁ 🡘 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡘 ψ₂) : 𝓢 ⊢ (φ₁ 🡒 ψ₁) 🡘 (φ₂ 🡒 ψ₂) := by
  apply E_intro;
  · apply deduct'; exact C_trans (of <| K_right hp) <| C_trans (FiniteContext.id) (of <| K_left hq);
  · apply deduct'; exact C_trans (of <| K_left hp) <| C_trans (FiniteContext.id) (of <| K_right hq);

open scoped Classical in
lemma C_iff_C_of_E_of_E (hp : 𝓢 ⊢ φ₁ 🡘 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡘 ψ₂) : 𝓢 ⊢ φ₁ 🡒 ψ₁ ↔ 𝓢 ⊢ φ₂ 🡒 ψ₂ :=
  iff_of_E (ECC_of_E_of_E hp hq)

open scoped Classical in
@[simp] lemma dni : 𝓢 ⊢ φ 🡒 ∼∼φ := by
  apply deduct';
  apply N_of_CO;
  apply deduct;
  exact bot_of_mem_either (φ := φ) (by simp) (by simp);

open scoped Classical in
lemma dni' (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ∼∼φ := dni ⨀ b

open scoped Classical in
lemma ANNNN_of_A (d : 𝓢 ⊢ φ ⋎ ψ) :
    𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ := of_C_of_C_of_A (C_trans dni or₁) (C_trans dni or₂) d

open scoped Classical in
lemma KNNNN_of_K (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ∼∼φ ⋏ ∼∼ψ := K_intro (dni' <| K_left d) (dni' <| K_right d)

lemma CNNOO : 𝓢 ⊢ ∼∼⊥ 🡒 ⊥ := by
  apply deduct'
  have d₁ : [∼∼⊥] ⊢[𝓢] ∼⊥ 🡒 ⊥ := CO_of_N by_axm₀
  have d₂ : [∼∼⊥] ⊢[𝓢] ∼⊥ := N_of_CO C_id
  exact d₁ ⨀ d₂

open scoped Classical in
lemma ENNOO : 𝓢 ⊢ ∼∼⊥ 🡘 ⊥ := K_intro CNNOO dni

open scoped Classical in
@[simp] theorem CCCNN : 𝓢 ⊢ (φ 🡒 ψ) 🡒 (∼ψ 🡒 ∼φ) := by
  apply deduct';
  apply deduct;
  apply N_of_CO;
  apply deduct;
  have dp  : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢] φ := FiniteContext.by_axm;
  have dpq : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢] φ 🡒 ψ := FiniteContext.by_axm;
  have dq  : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢] ψ := dpq ⨀ dp;
  have dnq : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢] ψ 🡒 ⊥ := CO_of_N <| FiniteContext.by_axm;
  exact dnq ⨀ dq;

@[deprecated "use `CCCNN`" (since := "2026-07-20")] alias contra₀ := CCCNN

open scoped Classical in
lemma contra (b : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ ∼ψ 🡒 ∼φ := CCCNN ⨀ b

@[deprecated "use `contra`" (since := "2026-07-20")] alias contra₀' := contra

open scoped Classical in
@[grind <=] lemma CNNNN_of_C (b : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ ∼∼φ 🡒 ∼∼ψ := contra <| contra b

open scoped Classical in
@[simp] lemma CCCNNNN : 𝓢 ⊢ (φ 🡒 ψ) 🡒 (∼∼φ 🡒 ∼∼ψ) := deduct' <| CNNNN_of_C FiniteContext.id

open scoped Classical in
lemma CN_of_CN_right (b : 𝓢 ⊢ φ 🡒 ∼ψ) : 𝓢 ⊢ ψ 🡒 ∼φ := C_trans dni (contra b)

open scoped Classical in
lemma CCNCN : 𝓢 ⊢ (φ 🡒 ∼ψ) 🡒 (ψ 🡒 ∼φ) := deduct' <| CN_of_CN_right FiniteContext.id

open scoped Classical in
lemma ENN_of_E (b : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ ∼φ 🡘 ∼ψ := E_intro (contra <| K_right b) (contra <| K_left b)

section NegationEquiv

open scoped Classical in
@[simp] lemma ENNCCOO : 𝓢 ⊢ ∼∼φ 🡘 ((φ 🡒 ⊥) 🡒 ⊥) := by
  apply E_intro;
  · exact C_trans (by apply contra; exact K_right neg_equiv) (K_left neg_equiv)
  · exact C_trans (K_right neg_equiv) (by apply contra; exact K_left neg_equiv)

end NegationEquiv

open scoped Classical in
@[simp] lemma tne : 𝓢 ⊢ ∼(∼∼φ) 🡒 ∼φ := contra dni

open scoped Classical in
lemma tne' (b : 𝓢 ⊢ ∼(∼∼φ)) : 𝓢 ⊢ ∼φ := tne ⨀ b

open scoped Classical in
lemma tneIff : 𝓢 ⊢ ∼∼∼φ 🡘 ∼φ := K_intro tne dni

lemma CCC_of_C_left (h : 𝓢 ⊢ ψ 🡒 φ) : 𝓢 ⊢ (φ 🡒 χ) 🡒 (ψ 🡒 χ) := by
  apply deduct';
  exact C_trans (of h) id;

@[deprecated "use `CCC_of_C_left`" (since := "2026-07-20")] alias rev_dhyp_imp' := CCC_of_C_left

lemma C_iff_C_of_iff_left (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ φ 🡒 χ ↔ 𝓢 ⊢ ψ 🡒 χ := by
  constructor;
  · exact C_trans <| K_right h;
  · exact C_trans <| K_left h;

lemma C_iff_C_of_iff_right (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ χ 🡒 φ ↔ 𝓢 ⊢ χ 🡒 ψ := by
  constructor;
  · intro hrp; exact C_trans hrp <| K_left h;
  · intro hrq; exact C_trans hrq <| K_right h;

open scoped Classical in
lemma C_swap (h : 𝓢 ⊢ φ 🡒 ψ 🡒 χ) : 𝓢 ⊢ ψ 🡒 φ 🡒 χ := by
  apply deduct';
  apply deduct;
  exact (of (Γ := [φ, ψ]) h) ⨀ FiniteContext.by_axm ⨀ FiniteContext.by_axm;

open scoped Classical in
@[simp] lemma CCCCC : 𝓢 ⊢ (φ 🡒 ψ 🡒 χ) 🡒 (ψ 🡒 φ 🡒 χ) := deduct' <| C_swap FiniteContext.id

open scoped Classical in
lemma C_of_CC (h : 𝓢 ⊢ φ 🡒 φ 🡒 ψ) : 𝓢 ⊢ φ 🡒 ψ := by
  apply deduct';
  have := of (Γ := [φ]) h;
  exact this ⨀ (FiniteContext.by_axm) ⨀ (FiniteContext.by_axm);

open scoped Classical in
lemma CCC : 𝓢 ⊢ φ 🡒 (φ 🡒 ψ) 🡒 ψ := C_swap <| C_id

lemma CCC_of_C_right (h : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ (χ 🡒 φ) 🡒 (χ 🡒 ψ) := implyS ⨀ (C_of_conseq h)

open scoped Classical in
@[simp] lemma CNNCCNNNN : 𝓢 ⊢ ∼∼(φ 🡒 ψ) 🡒 (∼∼φ 🡒 ∼∼ψ) := by
  apply C_swap;
  apply deduct';
  exact C_trans (CNNNN_of_C <| deductInv <| of <| C_swap <| CCCNNNN) tne;

open scoped Classical in
lemma CNNNN_of_NNC (b : 𝓢 ⊢ ∼∼(φ 🡒 ψ)) : 𝓢 ⊢ ∼∼φ 🡒 ∼∼ψ := CNNCCNNNN ⨀ b

lemma O_intro_of_KN (h : 𝓢 ⊢ φ ⋏ ∼φ) : 𝓢 ⊢ ⊥ := (CO_of_N <| K_right h) ⨀ (K_left h)
/-- Law of contradiction -/
alias lac' := O_intro_of_KN

@[simp] lemma CKNO : 𝓢 ⊢ φ ⋏ ∼φ 🡒 ⊥ := by
  apply deduct';
  exact O_intro_of_KN (φ := φ) <| FiniteContext.id
/-- Law of contradiction -/
alias lac := CKNO

open scoped Classical in
@[simp] lemma CANNNK : 𝓢 ⊢ (∼φ ⋎ ∼ψ) 🡒 ∼(φ ⋏ ψ) := left_A_intro (contra and₁) (contra and₂)

open scoped Classical in
lemma NK_of_ANN (d : 𝓢 ⊢ ∼φ ⋎ ∼ψ) : 𝓢 ⊢ ∼(φ ⋏ ψ)  := CANNNK ⨀ d

open scoped Classical in
@[simp] lemma CKNNNA : 𝓢 ⊢ (∼φ ⋏ ∼ψ) 🡒 ∼(φ ⋎ ψ) := by
  apply CK_of_CC;
  apply deduct';
  apply deduct;
  apply N_of_CO;
  apply deduct;
  exact of_C_of_C_of_A (CO_of_N FiniteContext.by_axm) (CO_of_N FiniteContext.by_axm)
    (FiniteContext.by_axm (φ := φ ⋎ ψ));

open scoped Classical in
lemma NA_of_KNN (d : 𝓢 ⊢ ∼φ ⋏ ∼ψ) : 𝓢 ⊢ ∼(φ ⋎ ψ) := CKNNNA ⨀ d

open scoped Classical in
@[simp] lemma CNAKNN : 𝓢 ⊢ ∼(φ ⋎ ψ) 🡒 (∼φ ⋏ ∼ψ) := by
  apply deduct';
  exact K_intro (deductInv <| contra <| or₁) (deductInv <| contra <| or₂)

open scoped Classical in
lemma KNN_of_NA (b : 𝓢 ⊢ ∼(φ ⋎ ψ)) : 𝓢 ⊢ ∼φ ⋏ ∼ψ := CNAKNN ⨀ b

section Conjunction

variable {ι : Type*}

@[simp] lemma EConj₂Conj : {Γ : List F} → 𝓢 ⊢ ⋀Γ 🡘 Γ.conj
  | []          => E_id
  | [_]         => E_intro (deduct' <| K_intro FiniteContext.id verum) and₁
  | _ :: _ :: _ => EKK_of_E_of_E E_id EConj₂Conj

lemma CConj_iff_CConj₂ : 𝓢 ⊢ Γ.conj 🡒 φ ↔ 𝓢 ⊢ ⋀Γ 🡒 φ := C_iff_C_of_iff_left <| E_symm EConj₂Conj

open scoped Classical in
/-- Note: It may be easier to handle define `List.conj` based on `List.conj' (?)` -/
lemma right_Conj'_intro (φ : F) (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢ φ 🡒 ψ i) :
    𝓢 ⊢ φ 🡒 l.conj' ψ :=
  right_Conj₂_intro φ (l.map ψ) fun χ h ↦
    let ⟨i, hi, e⟩ := l.chooseX (fun i ↦ ψ i = χ) (by simpa using h)
    e ▸ (b i hi)

open scoped Classical in
lemma left_Conj'_intro {l : List ι} {i : ι} (h : i ∈ l) (φ : ι → F) :
    𝓢 ⊢ l.conj' φ 🡒 φ i :=
  left_Conj₂_intro (by simp only [mem_map]; use i)

lemma right_Fconj_intro (φ : F) (s : Finset F) (b : (ψ : F) → ψ ∈ s → 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ φ 🡒 s.conj :=
  right_Conj₂_intro φ s.toList fun ψ hψ ↦ b ψ (by simpa using hψ)

lemma left_Fconj_intro [DecidableEq F] {s : Finset F} (h : φ ∈ s) :
    𝓢 ⊢ s.conj 🡒 φ := left_Conj₂_intro <| by simp [h]

open scoped Classical in
lemma right_Fconj'_intro (φ : F) (s : Finset ι) (ψ : ι → F) (b : ∀ i ∈ s, 𝓢 ⊢ φ 🡒 ψ i) :
    𝓢 ⊢ φ 🡒 ⩕ i ∈ s, ψ i := right_Conj'_intro φ s.toList ψ (by simpa)

open scoped Classical in
lemma left_Fconj'_intro {s : Finset ι} (φ : ι → F) {i} (hi : i ∈ s) : 𝓢 ⊢ (⩕ i ∈ s, φ i) 🡒 φ i :=
  left_Conj'_intro (by simpa) φ

open scoped Classical in
lemma right_Uconj_intro [Fintype ι] (φ : F) (ψ : ι → F) (b : (i : ι) → 𝓢 ⊢ φ 🡒 ψ i) :
    𝓢 ⊢ φ 🡒 ⩕ i, ψ i := right_Fconj'_intro φ Finset.univ ψ (by simpa using b)

open scoped Classical in
lemma left_Uconj_intro [Fintype ι] (φ : ι → F) (i) :
    𝓢 ⊢ (⩕ i, φ i) 🡒 φ i := left_Fconj'_intro _ <| by simp

open scoped Classical in
lemma Conj₂_iff_forall_provable {Γ : List F} : (𝓢 ⊢ ⋀Γ) ↔ (∀ φ ∈ Γ, 𝓢 ⊢ φ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, conj₂_cons_nonempty, mem_cons, forall_eq_or_imp];
    constructor;
    · intro h;
      constructor;
      · exact K_left h;
      · exact ih.mp (K_right h);
    · rintro ⟨h₁, h₂⟩;
      exact K_intro h₁ (ih.mpr h₂);

open scoped Classical in
lemma CConj₂Conj₂_of_subset (h : ∀ φ, φ ∈ Γ → φ ∈ Δ) : 𝓢 ⊢ ⋀Δ 🡒 ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle =>
    simp_all only [mem_cons, not_mem_nil, or_false, forall_eq, conj₂_singleton]
    exact left_Conj₂_intro h;
  | hcons φ Γ hne ih =>
    simp_all only [ne_eq, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp,
      not_false_eq_true, conj₂_cons_nonempty];
    exact right_K_intro (left_Conj₂_intro h.1) ih;

open scoped Classical in
lemma CConj₂Conj₂_of_provable (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢] φ) : 𝓢 ⊢ ⋀Δ 🡒 ⋀Γ :=
  by induction Γ using List.induction_with_singleton with
  | hnil => exact C_of_conseq verum;
  | hsingle =>
    simp_all only [mem_cons, not_mem_nil, or_false, forall_eq, conj₂_singleton]
    exact provable_iff.mp h;
  | hcons φ Γ hne ih =>
    simp_all only [ne_eq, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp,
      not_false_eq_true, conj₂_cons_nonempty];
    exact right_K_intro (provable_iff.mp h.1) ih;

open scoped Classical in
lemma CConj₂_of_forall_provable (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢] φ) :
    Δ ⊢[𝓢] ⋀Γ := provable_iff.mpr <| CConj₂Conj₂_of_provable h

open scoped Classical in
lemma CConj₂_of_unique (he : ∀ g ∈ Γ, g = φ) : 𝓢 ⊢ φ 🡒 ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hcons χ Γ h ih =>
    simp_all only [ne_eq, mem_cons, true_or, or_true, implies_true, forall_const, forall_eq_or_imp,
      not_false_eq_true, conj₂_cons_nonempty];
    have ⟨he₁, he₂⟩ := he; subst he₁;
    exact right_K_intro C_id ih;
  | _ => simp_all;

open scoped Classical in
lemma C_of_CConj₂_of_unique (he : ∀ g ∈ Γ, g = φ) (hd : 𝓢 ⊢ ⋀Γ 🡒 ψ) :
    𝓢 ⊢ φ 🡒 ψ := C_trans (CConj₂_of_unique he) hd

open scoped Classical in
lemma CConj₂_iff_CKConj₂ : 𝓢 ⊢ ⋀(φ :: Γ) 🡒 ψ ↔ 𝓢 ⊢ φ ⋏ ⋀Γ 🡒 ψ := by
  induction Γ with
  | nil =>
    simp only [conj₂_singleton, conj₂_nil, CK_iff_CC];
    constructor;
    · intro h; apply C_swap; exact C_of_conseq h;
    · intro h; exact C_swap h ⨀ verum;
  | cons ψ ih => simp;

open scoped Classical in
@[simp] lemma CConj₂AppendKConj₂Conj₂ : 𝓢 ⊢ ⋀(Γ ++ Δ) 🡒 ⋀Γ ⋏ ⋀Δ := by
  apply FiniteContext.deduct';
  have : [⋀(Γ ++ Δ)] ⊢[𝓢] ⋀(Γ ++ Δ) := id;
  have d := Conj₂_iff_forall_provable.mp this;
  apply K_intro;
  · apply Conj₂_iff_forall_provable.mpr;
    intro φ hp;
    exact d φ (by simp only [mem_append]; left; exact hp);
  · apply Conj₂_iff_forall_provable.mpr;
    intro φ hp;
    exact d φ (by simp only [mem_append]; right; exact hp);

@[simp]
lemma CKConj₂RemoveConj₂ [DecidableEq F] : 𝓢 ⊢ ⋀(Γ.remove φ) ⋏ φ 🡒 ⋀Γ := by
  apply deduct';
  apply Conj₂_iff_forall_provable.mpr;
  intro ψ hq;
  by_cases e : ψ = φ;
  · subst e; exact K_right id;
  · exact Conj₂_iff_forall_provable.mp (K_left id) ψ (by apply List.mem_remove_iff.mpr; simp_all);

lemma CKConj₂Remove_of_CConj₂ [DecidableEq F] (b : 𝓢 ⊢ ⋀Γ 🡒 ψ) :
    𝓢 ⊢ ⋀(Γ.remove φ) ⋏ φ 🡒 ψ := C_trans CKConj₂RemoveConj₂ b

open scoped Classical in
lemma Conj₂Append_iff_KConj₂Conj₂ : 𝓢 ⊢ ⋀(Γ ++ Δ) ↔ 𝓢 ⊢ ⋀Γ ⋏ ⋀Δ := by
  constructor;
  · intro h;
    replace h := Conj₂_iff_forall_provable.mp h;
    apply K_intro;
    · apply Conj₂_iff_forall_provable.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; left; simpa);
    · apply Conj₂_iff_forall_provable.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; right; simpa);
  · intro h;
    apply Conj₂_iff_forall_provable.mpr;
    simp only [List.mem_append];
    rintro φ (hp₁ | hp₂);
    · exact (Conj₂_iff_forall_provable.mp <| K_left h) φ hp₁;
    · exact (Conj₂_iff_forall_provable.mp <| K_right h) φ hp₂;

open scoped Classical in
@[simp] lemma EConj₂AppendKConj₂Conj₂ : 𝓢 ⊢ ⋀(Γ ++ Δ) 🡘 ⋀Γ ⋏ ⋀Δ := by
  apply E_intro;
  · apply deduct'; apply Conj₂Append_iff_KConj₂Conj₂.mp; exact id;
  · apply deduct'; apply Conj₂Append_iff_KConj₂Conj₂.mpr; exact id;

open scoped Classical in
lemma CConj₂Append_iff_CKConj₂Conj₂ : 𝓢 ⊢ ⋀(Γ ++ Δ) 🡒 φ ↔ 𝓢 ⊢ (⋀Γ ⋏ ⋀Δ) 🡒 φ := by
  constructor;
  · intro h; exact C_trans (K_right EConj₂AppendKConj₂Conj₂) h;
  · intro h; exact C_trans (K_left EConj₂AppendKConj₂Conj₂) h;

open scoped Classical in
@[simp] lemma CConj₂FConj {Γ : Finset F} : 𝓢 ⊢ ⋀Γ.toList 🡒 Γ.conj := by
  apply CConj₂Conj₂_of_provable;
  apply FiniteContext.by_axm;

@[simp] lemma CConj₂FConj_list [DecidableEq F] {Γ : List F} : 𝓢 ⊢ ⋀Γ 🡒 Γ.toFinset.conj := by
  apply C_trans ?_ CConj₂FConj;
  apply CConj₂Conj₂_of_subset;
  simp;

open scoped Classical in
@[simp] lemma CFConjConj₂ {Γ : Finset F} : 𝓢 ⊢ Γ.conj 🡒 ⋀Γ.toList := by
  apply right_Conj₂_intro;
  intro φ hφ;
  apply left_Fconj_intro;
  simpa using hφ;

@[simp] lemma CFConjConj₂_list [DecidableEq F] {Γ : List F} : 𝓢 ⊢ Γ.toFinset.conj 🡒 ⋀Γ := by
  apply C_trans <| CFConjConj₂;
  apply CConj₂Conj₂_of_subset;
  simp;

open scoped Classical in
lemma FConj_DT {Γ : Finset F} : 𝓢 ⊢ Γ.conj 🡒 φ ↔ Γ *⊢[𝓢] φ := by
  constructor;
  · intro h;
    apply Context.provable_iff.mpr;
    use Γ.toList;
    constructor;
    · simp;
    · apply FiniteContext.provable_iff.mpr;
      exact C_trans (by simp) h;
  · intro h;
    obtain ⟨Δ, hΔ₁, hΔ₂⟩ := Context.provable_iff.mp h;
    replace hΔ₂ : 𝓢 ⊢ ⋀Γ.toList 🡒 φ :=
      C_trans (CConj₂Conj₂_of_subset (by simpa)) <| FiniteContext.provable_iff.mp hΔ₂
    exact C_trans (by simp) hΔ₂;

lemma FConj_iff_forall_provable [DecidableEq F] {Γ : Finset F} :
    (𝓢 ⊢ Γ.conj) ↔ (∀ φ ∈ Γ, 𝓢 ⊢ φ) := by
  apply Iff.trans Conj₂_iff_forall_provable;
  constructor <;> simp_all;

open scoped Classical in
lemma FConj_of_FConj_of_subset {Γ Δ : Finset F} (h : Δ ⊆ Γ) (hΓ : 𝓢 ⊢ Γ.conj) : 𝓢 ⊢ Δ.conj := by
  rw [FConj_iff_forall_provable] at hΓ ⊢;
  intro φ hφ;
  apply hΓ;
  apply h hφ;

open scoped Classical in
lemma CFConjFConj_of_subset {Γ Δ : Finset F} (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj 🡒 Δ.conj := by
  apply FConj_DT.mpr;
  apply FConj_of_FConj_of_subset h;
  apply FConj_DT.mp;
  simp;

@[simp] lemma CFconjUnionKFconj [DecidableEq F] {Γ Δ : Finset F} :
    𝓢 ⊢ (Γ ∪ Δ).conj 🡒 Γ.conj ⋏ Δ.conj := by
  apply FConj_DT.mpr;
  apply K_intro <;>
  · apply FConj_DT.mp;
    apply CFConjFConj_of_subset;
    simp;

@[simp] lemma CinsertFConjKFConj [DecidableEq F] {Γ : Finset F} :
    𝓢 ⊢ (insert φ Γ).conj 🡒 φ ⋏ Γ.conj := by
  suffices 𝓢 ⊢ ({φ} ∪ Γ).conj 🡒 (Finset.conj {φ}) ⋏ Γ.conj by simpa using this;
  apply CFconjUnionKFconj;

@[simp] lemma CKFconjFconjUnion [DecidableEq F] {Γ Δ : Finset F} :
    𝓢 ⊢ Γ.conj ⋏ Δ.conj 🡒 (Γ ∪ Δ).conj := by
  apply right_Fconj_intro;
  simp only [Finset.mem_union];
  rintro φ (hφ | hφ);
  · apply left_K_intro_left
    apply left_Fconj_intro hφ;
  · apply left_K_intro_right;
    apply left_Fconj_intro hφ;

@[simp]
lemma CKFConjinsertFConj [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ φ ⋏ Γ.conj 🡒 (insert φ Γ).conj := by
  suffices 𝓢 ⊢ (Finset.conj {φ}) ⋏ Γ.conj 🡒 ({φ} ∪ Γ).conj by simpa using this;
  apply CKFconjFconjUnion;

lemma FConj_DT' [DecidableEq F] {Γ Δ : Finset F} : Γ *⊢[𝓢] Δ.conj 🡒 φ ↔ ↑(Γ ∪ Δ) *⊢[𝓢] φ := by
  constructor;
  · intro h; exact FConj_DT.mp <| C_trans CFconjUnionKFconj <| CK_iff_CC.mpr <| FConj_DT.mpr h;
  · intro h; exact FConj_DT.mp <| CK_iff_CC.mp <| C_trans CKFconjFconjUnion <| FConj_DT.mpr h;

lemma CFconjFconj_of_provable [DecidableEq F] {Γ Δ : Finset _} (h : ∀ φ, φ ∈ Γ → Δ *⊢[𝓢] φ) :
    𝓢 ⊢ Δ.conj 🡒 Γ.conj := by
  have : 𝓢 ⊢ ⋀(Δ.toList) 🡒 ⋀(Γ.toList) := CConj₂Conj₂_of_provable <| by
    intro φ hφ;
    apply Context.iff_provable_context_provable_finiteContext_toList.mp
    apply h φ;
    simpa using hφ;
  refine C_replace ?_ ?_ this;
  · simp;
  · simp;

end Conjunction

section disjunction

variable {ι : Type*}

open scoped Classical in
theorem right_Disj_intro (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢ φ 🡒 Γ.disj :=
  match Γ with
  |     [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ then cast (or₁ : 𝓢 ⊢ φ 🡒 φ ⋎ Γ.disj) (by simp [e])
    else
      have : φ ∈ Γ := by simpa [e] using h
      C_trans (right_Disj_intro Γ this) or₂

open scoped Classical in
theorem right_Disj_intro' (Γ : List F) (h : φ ∈ Γ) (hψ : 𝓢 ⊢ ψ 🡒 φ) : 𝓢 ⊢ ψ 🡒 Γ.disj :=
  C_trans hψ (right_Disj_intro Γ h)

open scoped Classical in
theorem right_Disj₂_intro (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢ φ 🡒 ⋁Γ :=
  match Γ with
  |     [] => by simp at h
  |    [ψ] => (show ⋁[ψ] = φ by simp_all) ▸ C_id
  | ψ :: χ :: Γ =>
    if e : φ = ψ then cast (or₁ : 𝓢 ⊢ φ 🡒 φ ⋎ ⋁(χ :: Γ)) (by simp [e])
    else
      have : φ ∈ χ :: Γ := by simpa [e] using h
      C_trans (right_Disj₂_intro _ this) or₂

open scoped Classical in
lemma right_Disj'_intro (φ : ι → F) (l : List ι) {i : ι} (h : i ∈ l) :
    𝓢 ⊢ φ i 🡒 l.disj' φ :=
  right_Disj₂_intro (l.map φ) (by simpa using ⟨i, h, rfl⟩)

lemma right_Fdisj_intro [DecidableEq F] (s : Finset F) (h : φ ∈ s) :
    𝓢 ⊢ φ 🡒 s.disj := right_Disj₂_intro _ (by simp [h])

open scoped Classical in
lemma right_Fdisj'_intro (s : Finset ι) (φ : ι → F) {i} (hi : i ∈ s) : 𝓢 ⊢ φ i 🡒 ⩖ j ∈ s, φ j :=
  right_Disj'_intro _ _ (by simp [hi])

open scoped Classical in
lemma right_Udisj_intro [Fintype ι] (φ : ι → F) {i : ι} : 𝓢 ⊢ φ i 🡒 ⩖ j, φ j :=
  right_Fdisj'_intro _ _ (by simp)

end disjunction

section

variable {Γ Δ : Finset F}

lemma CFConjFDisj_of_K_intro [DecidableEq F] (hp : φ ∈ Γ) (hpq : ψ ∈ Γ) (hψ : φ ⋏ ψ ∈ Δ) :
    𝓢 ⊢ Γ.conj 🡒 Δ.disj := by
  apply C_trans (ψ := Finset.disj {φ ⋏ ψ});
  · apply C_trans (ψ := Finset.conj {φ, ψ}) ?_;
    · apply FConj_DT.mpr;
      simp only [Finset.coe_insert, Finset.coe_singleton, Finset.disj_singleton];
      apply K_intro <;> exact Context.by_axm <| by simp;
    · apply CFConjFConj_of_subset;
      apply Finset.doubleton_subset.mpr;
      tauto;
  · simp only [Finset.disj_singleton];
    apply right_Fdisj_intro _ hψ;

lemma CFConjFDisj_of_innerMDP [DecidableEq F] (hp : φ ∈ Γ) (hpq : φ 🡒 ψ ∈ Γ) (hψ : ψ ∈ Δ) :
    𝓢 ⊢ Γ.conj 🡒 Δ.disj := by
  apply C_trans (ψ := Finset.disj {ψ});
  · apply C_trans (ψ := Finset.conj {φ, φ 🡒 ψ}) ?_;
    · apply FConj_DT.mpr;
      have h₁ : ({φ, φ 🡒 ψ}) *⊢[𝓢] φ 🡒 ψ := Context.by_axm <| by simp;
      have h₂ : ({φ, φ 🡒 ψ}) *⊢[𝓢] φ := Context.by_axm <| by simp;
      simpa using h₁ ⨀ h₂;
    · apply CFConjFConj_of_subset;
      apply Finset.doubleton_subset.mpr;
      tauto;
  · simp only [Finset.disj_singleton];
    apply right_Fdisj_intro _ hψ;

lemma iff_FiniteContext_Context [DecidableEq F] {Γ : List F} : Γ ⊢[𝓢] φ ↔ ↑Γ.toFinset *⊢[𝓢] φ := by
  constructor;
  · intro h;
    replace h := FiniteContext.provable_iff.mp h;
    apply FConj_DT.mp;
    exact C_trans (by simp) h;
  · intro h;
    replace h := FConj_DT.mpr h;
    apply FiniteContext.provable_iff.mpr;
    exact C_trans (by simp) h;

open scoped Classical in
lemma FConj'_iff_forall_provable {α : Type*} {s : Finset α} {ι : α → F} :
    (𝓢 ⊢ ⩕ i ∈ s, ι i) ↔ (∀ i ∈ s, 𝓢 ⊢ ι i) := by
  have : 𝓢 ⊢ ⋀(s.toList.map ι) ↔ ∀ i ∈ s, 𝓢 ⊢ ι i := by
    simpa using Conj₂_iff_forall_provable (Γ := s.toList.map ι);
  apply Iff.trans ?_ this;
  simp [Finset.conj', List.conj'];

end

namespace Context

open scoped Classical in
lemma provable_iff_finset {Γ : Set F} {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ :
    Finset F, (↑Δ ⊆ Γ) ∧ Δ *⊢[𝓢] φ := by
  apply Iff.trans Context.provable_iff;
  constructor;
  · rintro ⟨Δ, hΔ₁, hΔ₂⟩;
    use Δ.toFinset;
    constructor;
    · simpa;
    · apply provable_iff.mpr
      use Δ;
      constructor <;> simp_all;
  · rintro ⟨Δ, hΔ₁, hΔ₂⟩;
    use Δ.toList;
    constructor;
    · simpa;
    · apply FiniteContext.provable_iff.mpr;
      refine C_trans ?_ (FConj_DT.mpr hΔ₂);
      simp;

open scoped Classical in
lemma bot_of_mem_neg {Γ : Set F} (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ *⊢[𝓢] ⊥ := by
  replace h₁ : Γ *⊢[𝓢] φ := by_axm h₁;
  replace h₂ : Γ *⊢[𝓢] φ 🡒 ⊥ := N_iff_CO.mp <| by_axm h₂;
  exact h₂ ⨀ h₁;

end Context

end

end FFL.Entailment

end
