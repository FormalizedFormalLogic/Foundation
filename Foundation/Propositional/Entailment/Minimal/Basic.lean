import Foundation.Logic.Entailment
import Foundation.Vorspiel.Finset.Supplemental


namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)


protected abbrev NegEquiv := ∼φ ⭤ (φ ➝ ⊥)


protected abbrev Verum : F := ⊤

protected abbrev ImplyK := φ ➝ ψ ➝ φ

protected abbrev ImplyS := (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ

protected abbrev AndElim₁ := φ ⋏ ψ ➝ φ

protected abbrev AndElim₂ := φ ⋏ ψ ➝ ψ

protected abbrev AndInst := φ ➝ ψ ➝ φ ⋏ ψ

protected abbrev OrInst₁ := φ ➝ φ ⋎ ψ

protected abbrev OrInst₂ := ψ ➝ φ ⋎ ψ

protected abbrev OrElim := (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)

end LO.Axioms




namespace LO.Entailment


-- def cast (e : φ = ψ) (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ := e ▸ b
-- lemma cast! (e : φ = ψ) (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ := ⟨cast e b.some⟩

section

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class ModusPonens (𝓢 : S) where
  mdp {φ ψ : F} : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! φ → 𝓢 ⊢! ψ

alias mdp := ModusPonens.mdp
infixl:90 "⨀" => mdp

lemma mdp! [ModusPonens 𝓢] : 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ φ → 𝓢 ⊢ ψ := by
  rintro ⟨hpq⟩ ⟨hp⟩;
  exact ⟨hpq ⨀ hp⟩
infixl:90 "⨀" => mdp!
infixl:90 "⨀!" => mdp!




/--
  Negation `∼φ` is equivalent to `φ ➝ ⊥` on **system**.

  This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ ➝ ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv (𝓢 : S) where
  negEquiv {φ : F} : 𝓢 ⊢! Axioms.NegEquiv φ
export NegationEquiv (negEquiv)

@[simp] lemma neg_equiv! [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ ⭤ (φ ➝ ⊥) := ⟨negEquiv⟩


class HasAxiomVerum (𝓢 : S) where
  verum : 𝓢 ⊢! Axioms.Verum

def verum [HasAxiomVerum 𝓢] : 𝓢 ⊢! ⊤ := HasAxiomVerum.verum
@[simp] lemma verum! [HasAxiomVerum 𝓢] : 𝓢 ⊢ ⊤ := ⟨verum⟩


class HasAxiomImplyK (𝓢 : S)  where
  implyK {φ ψ : F} : 𝓢 ⊢! Axioms.ImplyK φ ψ
export HasAxiomImplyK (implyK)

@[simp] lemma implyK! [HasAxiomImplyK 𝓢] : 𝓢 ⊢ φ ➝ ψ ➝ φ := ⟨implyK⟩

def C_of_conseq [ModusPonens 𝓢] [HasAxiomImplyK 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ ➝ φ := implyK ⨀ h
alias dhyp := C_of_conseq

lemma C!_of_conseq! [ModusPonens 𝓢] [HasAxiomImplyK 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ ➝ φ := ⟨C_of_conseq d.some⟩
alias dhyp! := C!_of_conseq!


class HasAxiomImplyS (𝓢 : S)  where
  implyS {φ ψ χ : F} : 𝓢 ⊢! Axioms.ImplyS φ ψ χ
export HasAxiomImplyS (implyS)

@[simp] lemma implyS! [HasAxiomImplyS 𝓢] : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := ⟨implyS⟩


class HasAxiomAndElim (𝓢 : S)  where
  and₁ {φ ψ : F} : 𝓢 ⊢! Axioms.AndElim₁ φ ψ
  and₂ {φ ψ : F} : 𝓢 ⊢! Axioms.AndElim₂ φ ψ
export HasAxiomAndElim (and₁ and₂)


@[simp] lemma and₁! [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ φ := ⟨and₁⟩

def K_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! φ := and₁ ⨀ d
@[grind] lemma K!_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ φ := ⟨K_left d.some⟩


@[simp] lemma and₂! [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ ψ := ⟨and₂⟩

def K_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ := and₂ ⨀ d
@[grind] lemma K!_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ := ⟨K_right d.some⟩


class HasAxiomAndInst (𝓢 : S) where
  and₃ {φ ψ : F} : 𝓢 ⊢! Axioms.AndInst φ ψ
export HasAxiomAndInst (and₃)

@[simp] lemma and₃! [HasAxiomAndInst 𝓢] : 𝓢 ⊢ φ ➝ ψ ➝ φ ⋏ ψ := ⟨and₃⟩

def K_intro [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢! φ) (d₂: 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋏ ψ := and₃ ⨀ d₁ ⨀ d₂
@[grind] lemma K!_intro  [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢ φ) (d₂: 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋏ ψ := ⟨K_intro d₁.some d₂.some⟩


class HasAxiomOrInst (𝓢 : S) where
  or₁ {φ ψ : F} : 𝓢 ⊢! Axioms.OrInst₁ φ ψ
  or₂ {φ ψ : F} : 𝓢 ⊢! Axioms.OrInst₂ φ ψ
export HasAxiomOrInst (or₁ or₂)

@[simp] lemma or₁! [HasAxiomOrInst 𝓢] : 𝓢 ⊢ φ ➝ φ ⋎ ψ := ⟨or₁⟩

def A_intro_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! φ ⋎ ψ := or₁ ⨀ d
@[grind] lemma A!_intro_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ φ ⋎ ψ := ⟨A_intro_left d.some⟩

@[simp] lemma or₂! [HasAxiomOrInst 𝓢] : 𝓢 ⊢ ψ ➝ φ ⋎ ψ := ⟨or₂⟩

def A_intro_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋎ ψ := or₂ ⨀ d
@[grind] lemma A!_intro_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋎ ψ := ⟨A_intro_right d.some⟩


class HasAxiomOrElim (𝓢 : S) where
  or₃ {φ ψ χ : F} : 𝓢 ⊢! Axioms.OrElim φ ψ χ
export HasAxiomOrElim (or₃)

@[simp] lemma or₃! [HasAxiomOrElim 𝓢] : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ) ➝ χ := ⟨or₃⟩

def left_A_intro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ➝ χ) (d₂ : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ χ := or₃ ⨀ d₁ ⨀ d₂
alias CA_of_C_of_C := left_A_intro

lemma left_A!_intro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ➝ χ) (d₂ : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ χ := ⟨left_A_intro d₁.some d₂.some⟩
alias CA!_of_C!_of_C! := left_A!_intro

def of_C_of_C_of_A [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ➝ χ) (d₂ : 𝓢 ⊢! ψ ➝ χ) (d₃ : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! χ := or₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
alias A_cases := of_C_of_C_of_A

lemma of_C!_of_C!_of_A! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ➝ χ) (d₂ : 𝓢 ⊢ ψ ➝ χ) (d₃ : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ χ := ⟨of_C_of_C_of_A d₁.some d₂.some d₃.some⟩
alias A!_cases := of_C!_of_C!_of_A!

protected class Minimal (𝓢 : S) extends
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

def CO_of_N [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ → 𝓢 ⊢! φ ➝ ⊥ := λ h => (K_left negEquiv) ⨀ h
def N_of_CO [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! φ ➝ ⊥ → 𝓢 ⊢! ∼φ := λ h => (K_right negEquiv) ⨀ h
@[grind] lemma N!_iff_CO! [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ ↔ 𝓢 ⊢ φ ➝ ⊥ := ⟨λ ⟨h⟩ => ⟨CO_of_N h⟩, λ ⟨h⟩ => ⟨N_of_CO h⟩⟩


def E_intro [HasAxiomAndInst 𝓢] (b₁ : 𝓢 ⊢! φ ➝ ψ) (b₂ : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! φ ⭤ ψ := K_intro b₁ b₂
@[grind] lemma E!_intro [HasAxiomAndInst 𝓢] (h₁ : 𝓢 ⊢ φ ➝ ψ) (h₂ : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ φ ⭤ ψ := ⟨K_intro h₁.some h₂.some⟩

@[grind] lemma K!_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ↔ 𝓢 ⊢ φ ∧ 𝓢 ⊢ ψ := by grind
@[grind] lemma E!_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⭤ ψ ↔ 𝓢 ⊢ φ ➝ ψ ∧ 𝓢 ⊢ ψ ➝ φ := ⟨fun h ↦ ⟨K!_left h, K!_right h⟩, by grind⟩

@[grind] lemma C_of_E_mp! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ φ ➝ ψ := by grind
@[grind] lemma C_of_E_mpr! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ψ ➝ φ := by grind

@[grind] lemma iff_of_E! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ φ ↔ 𝓢 ⊢ ψ := ⟨fun hp ↦ K!_left h ⨀ hp, fun hq ↦ K!_right h ⨀ hq⟩

def C_id [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] {φ : F} : 𝓢 ⊢! φ ➝ φ := implyS (φ := φ) (ψ := (φ ➝ φ)) (χ := φ) ⨀ implyK ⨀ implyK
@[simp] def C!_id [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ ➝ φ := ⟨C_id⟩

def E_Id [HasAxiomAndInst 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] {φ : F} : 𝓢 ⊢! φ ⭤ φ := K_intro C_id C_id
@[simp] def E!_id [HasAxiomAndInst 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ ⭤ φ := ⟨E_Id⟩

instance [NegAbbrev F] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] [HasAxiomAndInst 𝓢] : Entailment.NegationEquiv 𝓢 where
  negEquiv {φ} := by
    suffices 𝓢 ⊢! (φ ➝ ⊥) ⭤ (φ ➝ ⊥) by simpa [Axioms.NegEquiv, NegAbbrev.neg];
    apply E_Id;


def NO [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! ∼⊥ := N_of_CO C_id
@[simp] lemma NO! [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ ∼⊥ := ⟨NO⟩


def mdp₁ [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ ➝ ψ ➝ χ) (bq : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ χ := implyS ⨀ bqr ⨀ bq
@[grind] lemma mdp₁! [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ ➝ ψ ➝ χ) (hq : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ χ := ⟨mdp₁ hqr.some hq.some⟩

infixl:90 "⨀₁" => mdp₁
infixl:90 "⨀₁" => mdp₁!

def mdp₂ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s) (bq : 𝓢 ⊢! φ ➝ ψ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ➝ s := C_of_conseq (implyS) ⨀₁ bqr ⨀₁ bq
@[grind] lemma mdp₂! [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s) (hq : 𝓢 ⊢ φ ➝ ψ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ➝ s := ⟨mdp₂ hqr.some hq.some⟩

infixl:90 "⨀₂" => mdp₂
infixl:90 "⨀₂" => mdp₂!

def mdp₃ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t) (bq : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ t := (C_of_conseq <| C_of_conseq <| implyS) ⨀₂ bqr ⨀₂ bq
@[grind] lemma mdp₃! [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t) (hq : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ t := ⟨mdp₃ hqr.some hq.some⟩

infixl:90 "⨀₃" => mdp₃
infixl:90 "⨀₃" => mdp₃!

def mdp₄ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t ➝ u) (bq : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ u := (C_of_conseq <| C_of_conseq <| C_of_conseq <| implyS) ⨀₃ bqr ⨀₃ bq
@[grind] lemma mdp₄! [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t ➝ u) (hq : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ u := ⟨mdp₄ hqr.some hq.some⟩
infixl:90 "⨀₄" => mdp₄
infixl:90 "⨀₄" => mdp₄!


def C_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bpq : 𝓢 ⊢! φ ➝ ψ) (bqr : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ➝ χ := implyS ⨀ C_of_conseq bqr ⨀ bpq
@[grind] lemma C!_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hpq : 𝓢 ⊢ φ ➝ ψ) (hqr : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ➝ χ := ⟨C_trans hpq.some hqr.some⟩

def C_replace [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢! ψ₁ ➝ φ₁) (h₂ : 𝓢 ⊢! φ₂ ➝ ψ₂) : 𝓢 ⊢! φ₁ ➝ φ₂ → 𝓢 ⊢! ψ₁ ➝ ψ₂ := λ h => C_trans h₁ $ C_trans h h₂
@[grind] lemma C!_replace [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢ ψ₁ ➝ φ₁) (h₂ : 𝓢 ⊢ φ₂ ➝ ψ₂) : 𝓢 ⊢ φ₁ ➝ φ₂ → 𝓢 ⊢ ψ₁ ➝ ψ₂ := λ h => ⟨C_replace h₁.some h₂.some h.some⟩

def E_trans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢! φ ⭤ ψ) (h₂ : 𝓢 ⊢! ψ ⭤ χ) : 𝓢 ⊢! φ ⭤ χ := by
  apply E_intro;
  . exact C_trans (K_left h₁) (K_left h₂);
  . exact C_trans (K_right h₂) (K_right h₁);
@[grind] lemma E!_trans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢ φ ⭤ ψ) (h₂ : 𝓢 ⊢ ψ ⭤ χ) : 𝓢 ⊢ φ ⭤ χ := ⟨E_trans h₁.some h₂.some⟩

def CCCC [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ φ := C_trans implyK implyK
@[grind] lemma CCCC! [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ φ := ⟨CCCC⟩

def CK_of_C_of_C [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bq : 𝓢 ⊢! φ ➝ ψ) (br : 𝓢 ⊢! φ ➝ χ)
  : 𝓢 ⊢! φ ➝ ψ ⋏ χ := C_of_conseq and₃ ⨀₁ bq ⨀₁ br
@[grind] lemma CK!_of_C!_of_C! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hq : 𝓢 ⊢ φ ➝ ψ) (hr : 𝓢 ⊢ φ ➝ χ)
  : 𝓢 ⊢ φ ➝ ψ ⋏ χ := ⟨CK_of_C_of_C hq.some hr.some⟩


def CKK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! φ ⋏ ψ ➝ ψ ⋏ φ := CK_of_C_of_C and₂ and₁
@[simp] lemma CKK! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ ψ ⋏ φ := ⟨CKK⟩

def K_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ ⋏ φ := CKK ⨀ h
@[grind] lemma K!_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ ⋏ φ := ⟨K_symm h.some⟩


def CEE [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! (φ ⭤ ψ) ➝ (ψ ⭤ φ) := CKK
@[simp] lemma CEE! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ (φ ⭤ ψ) ➝ (ψ ⭤ φ) := ⟨CEE⟩

def E_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ψ ⭤ φ := CEE ⨀ h
@[grind] lemma E!_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ψ ⭤ φ := ⟨E_symm h.some⟩


def ECKCC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! (φ ⋏ ψ ➝ χ) ⭤ (φ ➝ ψ ➝ χ) := by
  let b₁ : 𝓢 ⊢! (φ ⋏ ψ ➝ χ) ➝ φ ➝ ψ ➝ χ := CCCC ⨀₃ C_of_conseq (ψ := φ ⋏ ψ ➝ χ) and₃
  let b₂ : 𝓢 ⊢! (φ ➝ ψ ➝ χ) ➝ φ ⋏ ψ ➝ χ := implyK ⨀₂ (C_of_conseq (ψ := φ ➝ ψ ➝ χ) and₁) ⨀₂ (C_of_conseq (ψ := φ ➝ ψ ➝ χ) and₂);
  exact E_intro b₁ b₂
@[simp, grind] lemma ECKCC! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ (φ ⋏ ψ ➝ χ) ⭤ (φ ➝ ψ ➝ χ) := ⟨ECKCC⟩

def CC_of_CK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ➝ χ := (K_left $ ECKCC) ⨀ d
def CK_of_CC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (d : 𝓢 ⊢! φ ➝ ψ ➝ χ) : 𝓢 ⊢! φ ⋏ ψ ➝ χ := (K_right $ ECKCC) ⨀ d

@[grind] lemma CK!_iff_CC! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]: (𝓢 ⊢ φ ⋏ ψ ➝ χ) ↔ (𝓢 ⊢ φ ➝ ψ ➝ χ) := iff_of_E! ECKCC!

def CV [HasAxiomVerum 𝓢] [HasAxiomImplyK 𝓢] : 𝓢 ⊢! φ ➝ ⊤ := C_of_conseq verum
@[simp] lemma CV! [HasAxiomImplyK 𝓢] [HasAxiomVerum 𝓢] : 𝓢 ⊢ φ ➝ ⊤ := ⟨CV⟩


@[grind] lemma unprovable_C!_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hpq : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊬ φ ➝ χ → 𝓢 ⊬ ψ ➝ χ := by
  contrapose!;
  exact C!_trans hpq;

@[grind] lemma uniff_of_E! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (H : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊬ φ ↔ 𝓢 ⊬ ψ := by
  constructor;
  . intro hp hq; have := K!_right H ⨀ hq; contradiction;
  . intro hq hp; have := K!_left H ⨀ hp; contradiction;

end


section

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} [Entailment.Minimal 𝓢] {φ ψ χ : F}

variable {Γ Δ : List F}

def conj₂Nth : (Γ : List F) → (n : ℕ) → (hn : n < Γ.length) → 𝓢 ⊢! ⋀Γ ➝ Γ[n]
  |          [],     _, hn => by simp at hn
  |         [ψ],     0, _  => C_id
  | φ :: ψ :: Γ,     0, _  => and₁
  | φ :: ψ :: Γ, n + 1, hn => C_trans (and₂ (φ := φ)) (conj₂Nth (ψ :: Γ) n (Nat.succ_lt_succ_iff.mp hn))

def conj₂_nth! (Γ : List F) (n : ℕ) (hn : n < Γ.length) : 𝓢 ⊢ ⋀Γ ➝ Γ[n] := ⟨conj₂Nth Γ n hn⟩

def left_Conj_intro [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢! Γ.conj ➝ φ :=
  match Γ with
  |     [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ
    then e ▸ and₁
    else
      have : φ ∈ Γ := by simpa [e] using h
      C_trans and₂ (left_Conj_intro this)
lemma left_Conj!_intro [DecidableEq F] (h : φ ∈ Γ) : 𝓢 ⊢ Γ.conj ➝ φ := ⟨left_Conj_intro h⟩

def Conj_intro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) : 𝓢 ⊢! Γ.conj :=
  match Γ with
  |     [] => verum
  | ψ :: Γ => K_intro (b ψ (by simp)) (Conj_intro Γ (fun ψ hq ↦ b ψ (by simp [hq])))
lemma Conj!_intro {Γ : List F} (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ Γ.conj := ⟨Conj_intro Γ λ φ hφ => (b φ hφ).some⟩

def right_Conj_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ Γ.conj :=
  match Γ with
  |     [] => C_of_conseq verum
  | ψ :: Γ => CK_of_C_of_C (b ψ (by simp)) (right_Conj_intro φ Γ (fun ψ hq ↦ b ψ (by simp [hq])))
def right_Conj!_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ Γ.conj := ⟨right_Conj_intro φ Γ fun ψ h ↦ (b ψ h).get⟩

def CConjConj [DecidableEq F] (h : Δ ⊆ Γ) : 𝓢 ⊢! Γ.conj ➝ Δ.conj := right_Conj_intro _ _ (fun _ hq ↦ left_Conj_intro (h hq))

def left_Conj₂_intro [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ ➝ φ :=
  have : Γ.idxOf φ < Γ.length := List.idxOf_lt_length_of_mem h
  have : Γ[Γ.idxOf φ] = φ := List.getElem_idxOf this
  cast (by rw [this]) <| conj₂Nth Γ (Γ.idxOf φ) (by assumption)
lemma left_Conj₂!_intro [DecidableEq F] (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ ➝ φ := ⟨left_Conj₂_intro h⟩

def Conj₂_intro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) : 𝓢 ⊢! ⋀Γ :=
  match Γ with
  |          [] => verum
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by exact K_intro (b ψ (by simp)) (Conj₂_intro _ (by aesop))
lemma Conj₂!_intro (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ ⋀Γ := ⟨Conj₂_intro Γ (λ φ hp => (b φ hp).some)⟩

def right_Conj₂_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ ⋀Γ :=
  match Γ with
  |          [] => C_of_conseq verum
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by apply CK_of_C_of_C (b ψ (by simp)) (right_Conj₂_intro φ _ (fun ψ hq ↦ b ψ (by simp [hq])));
lemma right_Conj₂!_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ ⋀Γ := ⟨right_Conj₂_intro φ Γ (λ ψ hq => (b ψ hq).some)⟩

def CConj₂Conj₂ [DecidableEq F] {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢! ⋀Γ ➝ ⋀Δ :=
  right_Conj₂_intro _ _ (fun _ hq ↦ left_Conj₂_intro (h hq))
lemma CConj₂_Conj₂! [DecidableEq F] {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢ ⋀Γ ➝ ⋀Δ := ⟨CConj₂Conj₂ h⟩


section

variable {G T : Type*} [Entailment T G] [LogicalConnective G] {𝓣 : T}

def Minimal.ofEquiv (𝓢 : S) [Entailment.Minimal 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢! f φ ≃ 𝓣 ⊢! φ) : Entailment.Minimal 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢! f φ ➝ f ψ := by simpa using (e (φ ➝ ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  negEquiv := e _ (by simpa using negEquiv)
  verum := e _ (by simpa using verum)
  implyK := e _ (by simpa using implyK)
  implyS := e _ (by simpa using implyS)
  and₁ := e _ (by simpa using and₁)
  and₂ := e _ (by simpa using and₂)
  and₃ := e _ (by simpa using and₃)
  or₁ := e _ (by simpa using or₁)
  or₂ := e _ (by simpa using or₂)
  or₃ := e _ (by simpa using or₃)

end

end


section

structure FiniteContext (F) (𝓢 : S) where
  ctx : List F

namespace FiniteContext

variable {F} {S} {𝓢 : S}

instance : Coe (List F) (FiniteContext F 𝓢) := ⟨mk⟩

abbrev conj [LogicalConnective F] (Γ : FiniteContext F 𝓢) : F := ⋀Γ.ctx

abbrev disj [LogicalConnective F] (Γ : FiniteContext F 𝓢) : F := ⋁Γ.ctx

instance : EmptyCollection (FiniteContext F 𝓢) := ⟨⟨[]⟩⟩

instance : Membership F (FiniteContext F 𝓢) := ⟨λ Γ x => (x ∈ Γ.ctx)⟩

instance : HasSubset (FiniteContext F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Adjoin F (FiniteContext F 𝓢) := ⟨(· :: ·.ctx)⟩

lemma mem_def {φ : F} {Γ : FiniteContext F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx := iff_of_eq rfl

@[simp] lemma coe_subset_coe_iff {Γ Δ : List F} : (Γ : FiniteContext F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl

@[simp] lemma mem_coe_iff {φ : F} {Γ : List F} : φ ∈ (Γ : FiniteContext F 𝓢) ↔ φ ∈ Γ := iff_of_eq rfl

@[simp] lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ : FiniteContext F 𝓢) := by simp [EmptyCollection.emptyCollection]

instance : AdjunctiveSet F (FiniteContext F 𝓢) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin, mem_def]

variable [Entailment S F] [LogicalConnective F]

instance (𝓢 : S) : Entailment (FiniteContext F 𝓢) F := ⟨(𝓢 ⊢! ·.conj ➝ ·)⟩

abbrev Prf (𝓢 : S) (Γ : List F) (φ : F) : Type _ := (Γ : FiniteContext F 𝓢) ⊢! φ

abbrev Provable (𝓢 : S) (Γ : List F) (φ : F) : Prop := (Γ : FiniteContext F 𝓢) ⊢ φ

abbrev Unprovable (𝓢 : S) (Γ : List F) (φ : F) : Prop := (Γ : FiniteContext F 𝓢) ⊬ φ

abbrev PrfSet (𝓢 : S) (Γ : List F) (s : Set F) : Type _ := (Γ : FiniteContext F 𝓢) ⊢!* s

abbrev ProvableSet (𝓢 : S) (Γ : List F) (s : Set F) : Prop := (Γ : FiniteContext F 𝓢) ⊢* s

notation Γ:45 " ⊢[" 𝓢 "]! " φ:46 => Prf 𝓢 Γ φ

notation Γ:45 " ⊢[" 𝓢 "] " φ:46 => Provable 𝓢 Γ φ

notation Γ:45 " ⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ

notation Γ:45 " ⊢[" 𝓢 "]!* " s:46 => PrfSet 𝓢 Γ s

notation Γ:45 " ⊢[" 𝓢 "]* " s:46 => ProvableSet 𝓢 Γ s

lemma entailment_def (Γ : FiniteContext F 𝓢) (φ : F) : (Γ ⊢! φ) = (𝓢 ⊢! Γ.conj ➝ φ) := rfl

def ofDef {Γ : List F} {φ : F} (b : 𝓢 ⊢! ⋀Γ ➝ φ) : Γ ⊢[𝓢]! φ := b

def toDef {Γ : List F} {φ : F} (b : Γ ⊢[𝓢]! φ) : 𝓢 ⊢! ⋀Γ ➝ φ := b

lemma toₛ! (b : Γ ⊢[𝓢] φ) : 𝓢 ⊢ ⋀Γ ➝ φ := b

lemma provable_iff {φ : F} : Γ ⊢[𝓢] φ ↔ 𝓢 ⊢ ⋀Γ ➝ φ := iff_of_eq rfl

def cast {Γ φ} (d : Γ ⊢[𝓢]! φ) (eΓ : Γ = Γ') (eφ : φ = φ') : Γ' ⊢[𝓢]! φ' := eΓ ▸ eφ ▸ d

section

variable {Γ Δ E : List F}
variable [Entailment.Minimal 𝓢]

instance [DecidableEq F] : Axiomatized (FiniteContext F 𝓢) where
  prfAxm := fun hp ↦ left_Conj₂_intro hp
  weakening := fun H b ↦ C_trans (CConj₂Conj₂ H) b

instance : Compact (FiniteContext F 𝓢) where
  Γ := fun {Γ} _ _ ↦ Γ
  ΓPrf := id
  Γ_subset := by simp
  Γ_finite := by rintro ⟨Γ⟩; simp [AdjunctiveSet.Finite, AdjunctiveSet.set]

def nthAxm {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢]! Γ[n] := conj₂Nth Γ n h
lemma nth_axm! {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢] Γ[n] := ⟨nthAxm n h⟩

def byAxm [DecidableEq F] {φ} (h : φ ∈ Γ := by simp) : Γ ⊢[𝓢]! φ := Axiomatized.prfAxm (by simpa)

lemma by_axm! [DecidableEq F] {φ} (h : φ ∈ Γ := by simp) : Γ ⊢[𝓢] φ := Axiomatized.provable_axm _ (by simpa)

def weakening [DecidableEq F] (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢]! φ → Δ ⊢[𝓢]! φ := Axiomatized.weakening (by simpa)

lemma weakening! [DecidableEq F] (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢] φ → Δ ⊢[𝓢] φ := fun h ↦
  (Axiomatized.le_of_subset (by simpa)).subset h

def of {φ : F} (b : 𝓢 ⊢! φ) : Γ ⊢[𝓢]! φ := C_of_conseq (ψ := ⋀Γ) b

def emptyPrf {φ : F} : [] ⊢[𝓢]! φ → 𝓢 ⊢! φ := fun b ↦ b ⨀ verum

def provable_iff_provable {φ : F} : 𝓢 ⊢ φ ↔ [] ⊢[𝓢] φ :=
  ⟨fun b ↦ ⟨of b.some⟩, fun b ↦ ⟨emptyPrf b.some⟩⟩

lemma of'! [DecidableEq F] (h : 𝓢 ⊢ φ) : Γ ⊢[𝓢] φ := weakening! (by simp) $ provable_iff_provable.mp h

def id : [φ] ⊢[𝓢]! φ := nthAxm 0
@[simp] lemma id! : [φ] ⊢[𝓢] φ := nth_axm! 0

def byAxm₀ : (φ :: Γ) ⊢[𝓢]! φ := nthAxm 0
lemma by_axm₀! : (φ :: Γ) ⊢[𝓢] φ := nth_axm! 0

def byAxm₁ : (φ :: ψ :: Γ) ⊢[𝓢]! ψ := nthAxm 1
lemma by_axm₁! : (φ :: ψ :: Γ) ⊢[𝓢] ψ := nth_axm! 1

def byAxm₂ : (φ :: ψ :: χ :: Γ) ⊢[𝓢]! χ := nthAxm 2
lemma by_axm₂! : (φ :: ψ :: χ :: Γ) ⊢[𝓢] χ := nth_axm! 2

instance (Γ : FiniteContext F 𝓢) : Entailment.ModusPonens Γ := ⟨mdp₁⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomVerum Γ := ⟨of verum⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImplyK Γ := ⟨of implyK⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImplyS Γ := ⟨of implyS⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndElim Γ := ⟨of and₁, of and₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndInst Γ := ⟨of and₃⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrInst Γ := ⟨of or₁, of or₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrElim Γ := ⟨of or₃⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.NegationEquiv Γ := ⟨of negEquiv⟩

instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : Entailment.Minimal Γ where


def mdp' [DecidableEq F] (bΓ : Γ ⊢[𝓢]! φ ➝ ψ) (bΔ : Δ ⊢[𝓢]! φ) : (Γ ++ Δ) ⊢[𝓢]! ψ :=
  wk (by simp) bΓ ⨀ wk (by simp) bΔ

def deduct {φ ψ : F} : {Γ : List F} → (φ :: Γ) ⊢[𝓢]! ψ → Γ ⊢[𝓢]! φ ➝ ψ
  | .nil => fun b ↦ ofDef <| C_of_conseq (toDef b)
  | .cons _ _ => fun b ↦ ofDef <| CC_of_CK (C_trans CKK (toDef b))

lemma deduct! (h : (φ :: Γ) ⊢[𝓢] ψ) :  Γ ⊢[𝓢] φ ➝ ψ  := ⟨FiniteContext.deduct h.some⟩

def deductInv {φ ψ : F} : {Γ : List F} → Γ ⊢[𝓢]! φ ➝ ψ → (φ :: Γ) ⊢[𝓢]! ψ
  | .nil => λ b => ofDef <| (toDef b) ⨀ verum
  | .cons _ _ => λ b => ofDef <| (C_trans CKK (CK_of_CC (toDef b)))

lemma deductInv! (h : Γ ⊢[𝓢] φ ➝ ψ) : (φ :: Γ) ⊢[𝓢] ψ := ⟨FiniteContext.deductInv h.some⟩

lemma deduct_iff {φ ψ : F} {Γ : List F} : Γ ⊢[𝓢] φ ➝ ψ ↔ (φ :: Γ) ⊢[𝓢] ψ :=
  ⟨fun h ↦ ⟨deductInv h.some⟩, fun h ↦ ⟨deduct h.some⟩⟩

def deduct' : [φ] ⊢[𝓢]! ψ → 𝓢 ⊢! φ ➝ ψ := fun b ↦ emptyPrf <| deduct b

lemma deduct'! (h : [φ] ⊢[𝓢] ψ) : 𝓢 ⊢ φ ➝ ψ := ⟨FiniteContext.deduct' h.some⟩


def deductInv' : 𝓢 ⊢! φ ➝ ψ → [φ] ⊢[𝓢]! ψ := fun b ↦ deductInv <| of b

lemma deductInv'! (h : 𝓢 ⊢ φ ➝ ψ) : [φ] ⊢[𝓢] ψ := ⟨FiniteContext.deductInv' h.some⟩


instance deduction : Deduction (FiniteContext F 𝓢) where
  ofInsert := deduct
  inv := deductInv

instance [DecidableEq F] : StrongCut (FiniteContext F 𝓢) (FiniteContext F 𝓢) :=
  ⟨fun {Γ Δ _} bΓ bΔ ↦
    have : Γ ⊢! Δ.conj := Conj₂_intro _ (fun _ hp ↦ bΓ hp)
    ofDef <| C_trans (toDef this) (toDef bΔ)⟩

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

instance : Membership F (Context F 𝓢) := ⟨λ Γ x => (x ∈ Γ.ctx)⟩

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

variable [LogicalConnective F] [Entailment S F]

structure Proof (Γ : Context F 𝓢) (φ : F) where
  ctx : List F
  subset : ∀ ψ ∈ ctx, ψ ∈ Γ
  prf : ctx ⊢[𝓢]! φ

instance (𝓢 : S) : Entailment (Context F 𝓢) F := ⟨Proof⟩

variable (𝓢)

abbrev Prf (Γ : Set F) (φ : F) : Type _ := (Γ : Context F 𝓢) ⊢! φ

abbrev Provable (Γ : Set F) (φ : F) : Prop := (Γ : Context F 𝓢) ⊢ φ

abbrev Unprovable (Γ : Set F) (φ : F) : Prop := (Γ : Context F 𝓢) ⊬ φ

abbrev PrfSet (Γ : Set F) (s : Set F) : Type _ := (Γ : Context F 𝓢) ⊢!* s

abbrev ProvableSet (Γ : Set F) (s : Set F) : Prop := (Γ : Context F 𝓢) ⊢* s

notation Γ:45 " *⊢[" 𝓢 "]! " φ:46 => Prf 𝓢 Γ φ

notation Γ:45 " *⊢[" 𝓢 "] " φ:46 => Provable 𝓢 Γ φ

notation Γ:45 " *⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ

notation Γ:45 " *⊢[" 𝓢 "]!* " s:46 => PrfSet 𝓢 Γ s

notation Γ:45 " *⊢[" 𝓢 "]* " s:46 => ProvableSet 𝓢 Γ s

section

variable {𝓢}

lemma provable_iff {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : List F, (∀ ψ ∈ Δ, ψ ∈ Γ) ∧ Δ ⊢[𝓢] φ :=
  ⟨by rintro ⟨⟨Δ, h, b⟩⟩; exact ⟨Δ, h, ⟨b⟩⟩, by rintro ⟨Δ, h, ⟨d⟩⟩; exact ⟨⟨Δ, h, d⟩⟩⟩

section minimal

variable [Entailment.Minimal 𝓢]

instance [DecidableEq F] : Axiomatized (Context F 𝓢) where
  prfAxm := fun {Γ φ} hp ↦ ⟨[φ], by simpa using hp, byAxm (by simp [AdjunctiveSet.set])⟩
  weakening := fun h b ↦ ⟨b.ctx, fun φ hp ↦ AdjunctiveSet.subset_iff.mp h φ (b.subset φ hp), b.prf⟩

def byAxm [DecidableEq F] {Γ : Set F} {φ : F} (h : φ ∈ Γ) : Γ *⊢[𝓢]! φ := Axiomatized.prfAxm (by simpa)

lemma by_axm [DecidableEq F] {Γ : Set F} {φ : F} (h : φ ∈ Γ) : Γ *⊢[𝓢] φ := Axiomatized.provable_axm _ (by simpa)

instance : Compact (Context F 𝓢) where
  Γ := fun b ↦ AdjunctiveSet.set b.ctx
  ΓPrf := fun b ↦ ⟨b.ctx, by simp [AdjunctiveSet.set], b.prf⟩
  Γ_subset := by rintro ⟨Γ⟩ φ b; exact b.subset
  Γ_finite := by rintro ⟨Γ⟩; simp [AdjunctiveSet.Finite, AdjunctiveSet.set]

-- lemma provable_iff' [DecidableEq F] {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : Finset F, (↑Δ ⊆ Γ) ∧ Δ *⊢[𝓢] φ

def deduct [DecidableEq F] {φ ψ : F} {Γ : Set F} : (insert φ Γ) *⊢[𝓢]! ψ → Γ *⊢[𝓢]! φ ➝ ψ
  | ⟨Δ, h, b⟩ =>
    have h : ∀ ψ ∈ Δ, ψ = φ ∨ ψ ∈ Γ := by simpa using h
    let b' : (φ :: Δ.filter (· ≠ φ)) ⊢[𝓢]! ψ :=
      FiniteContext.weakening
        (by simp [List.subset_def, List.mem_filter]; rintro χ hr; simp [hr]; tauto)
        b
    ⟨ Δ.filter (· ≠ φ), by
      intro ψ; simp [List.mem_filter]
      intro hq ne
      rcases h ψ hq
      · contradiction
      · assumption,
      FiniteContext.deduct b' ⟩
lemma deduct! [DecidableEq F] (h : (insert φ Γ) *⊢[𝓢] ψ) : Γ *⊢[𝓢] φ ➝ ψ := ⟨Context.deduct h.some⟩

def deductInv {φ ψ : F} {Γ : Set F} : Γ *⊢[𝓢]! φ ➝ ψ → (insert φ Γ) *⊢[𝓢]! ψ
  | ⟨Δ, h, b⟩ => ⟨φ :: Δ, by simp; intro χ hr; exact Or.inr (h χ hr), FiniteContext.deductInv b⟩
lemma deductInv! [DecidableEq F] (h : Γ *⊢[𝓢] φ ➝ ψ) : (insert φ Γ) *⊢[𝓢] ψ := ⟨Context.deductInv h.some⟩

instance deduction [DecidableEq F] : Deduction (Context F 𝓢) where
  ofInsert := deduct
  inv := deductInv

def weakening [DecidableEq F] (h : Γ ⊆ Δ) {φ : F} : Γ *⊢[𝓢]! φ → Δ *⊢[𝓢]! φ := Axiomatized.weakening (by simpa)
lemma weakening! [DecidableEq F] (h : Γ ⊆ Δ) {φ : F} : Γ *⊢[𝓢] φ → Δ *⊢[𝓢] φ := fun h ↦ (Axiomatized.le_of_subset (by simpa)).subset h

def of {φ : F} (b : 𝓢 ⊢! φ) : Γ *⊢[𝓢]! φ := ⟨[], by simp, FiniteContext.of b⟩

lemma of! (b : 𝓢 ⊢ φ) : Γ *⊢[𝓢] φ := ⟨Context.of b.some⟩

def mdp [DecidableEq F] {Γ : Set F} (bpq : Γ *⊢[𝓢]! φ ➝ ψ) (bp : Γ *⊢[𝓢]! φ) : Γ *⊢[𝓢]! ψ :=
  ⟨ bpq.ctx ++ bp.ctx, by
    simp; rintro χ (hr | hr)
    · exact bpq.subset χ hr
    · exact bp.subset χ hr,
    FiniteContext.mdp' bpq.prf bp.prf ⟩

lemma by_axm! [DecidableEq F] (h : φ ∈ Γ) : Γ *⊢[𝓢] φ := Entailment.by_axm _ (by simpa)

def emptyPrf {φ : F} : ∅ *⊢[𝓢]! φ → 𝓢 ⊢! φ := by
  rintro ⟨Γ, hΓ, h⟩;
  have := List.eq_nil_iff_forall_not_mem.mpr hΓ;
  subst this;
  exact FiniteContext.emptyPrf h;

lemma emptyPrf! {φ : F} : ∅ *⊢[𝓢] φ → 𝓢 ⊢ φ := fun h ↦ ⟨emptyPrf h.some⟩

lemma provable_iff_provable {φ : F} : 𝓢 ⊢ φ ↔ ∅ *⊢[𝓢] φ := ⟨of!, emptyPrf!⟩

lemma iff_provable_context_provable_finiteContext_toList [DecidableEq F] {Δ : Finset F} : ↑Δ *⊢[𝓢] φ ↔ Δ.toList ⊢[𝓢] φ := by
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply FiniteContext.weakening! ?_ hΓ₂;
    intro ψ hψ;
    simpa using hΓ₁ ψ hψ;
  . intro h;
    apply Context.provable_iff.mpr;
    use Δ.toList;
    constructor;
    . simp;
    . assumption;

instance minimal [DecidableEq F] (Γ : Context F 𝓢) : Entailment.Minimal Γ where
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
  negEquiv := of negEquiv

end minimal

end

end Context

end


section

variable {F : Type*} [LogicalConnective F]
         {S : Type*} [Entailment S F]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open List

@[simp] lemma CONV! : 𝓢 ⊢ ⊤ ➝ ∼⊥ := deduct'! NO!

def innerMDP [DecidableEq F] : 𝓢 ⊢! φ ⋏ (φ ➝ ψ) ➝ ψ := by
  apply deduct';
  have hp  : [φ, φ ➝ ψ] ⊢[𝓢]! φ := FiniteContext.byAxm;
  have hpq : [φ, φ ➝ ψ] ⊢[𝓢]! φ ➝ ψ := FiniteContext.byAxm;
  exact hpq ⨀ hp;
lemma inner_mdp! [DecidableEq F] : 𝓢 ⊢ φ ⋏ (φ ➝ ψ) ➝ ψ := ⟨innerMDP⟩

def bot_of_mem_either [DecidableEq F] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ⊥ := by
  have hp : Γ ⊢[𝓢]! φ := FiniteContext.byAxm h₁;
  have hnp : Γ ⊢[𝓢]! φ ➝ ⊥ := CO_of_N $ FiniteContext.byAxm h₂;
  exact hnp ⨀ hp
lemma bot_of_mem_either! [DecidableEq F] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ⊥ := ⟨bot_of_mem_either h₁ h₂⟩

def negMDP (hnp : 𝓢 ⊢! ∼φ) (hn : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊥ := (CO_of_N hnp) ⨀ hn
lemma neg_mdp (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ := ⟨negMDP hnp.some hn.some⟩


def right_A_intro_left (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ (χ ⋎ ψ) := by
  apply deduct';
  apply A_intro_left;
  apply deductInv;
  exact of h;
lemma right_A!_intro_left (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ (χ ⋎ ψ) := ⟨right_A_intro_left h.some⟩

def right_A_intro_right (h : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! ψ ➝ (φ ⋎ χ) := by
  apply deduct';
  apply A_intro_right;
  apply deductInv;
  exact of h;
lemma right_A!_intro_right (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ ψ ➝ (φ ⋎ χ) := ⟨right_A_intro_right h.some⟩


def right_K_intro [DecidableEq F] (hq : 𝓢 ⊢! φ ➝ ψ) (hr : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ⋏ χ := by
  apply deduct';
  replace hq : [] ⊢[𝓢]! φ ➝ ψ := of hq;
  replace hr : [] ⊢[𝓢]! φ ➝ χ := of hr;
  exact K_intro (mdp' hq FiniteContext.id) (mdp' hr FiniteContext.id)
lemma right_K!_intro [DecidableEq F] (hq : 𝓢 ⊢ φ ➝ ψ) (hr : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ⋏ χ := ⟨right_K_intro hq.some hr.some⟩

lemma left_K!_symm (d : 𝓢 ⊢ φ ⋏ ψ ➝ χ) : 𝓢 ⊢ ψ ⋏ φ ➝ χ := C!_trans CKK! d


lemma left_K!_intro_right [DecidableEq F] (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ (ψ ⋏ φ) ➝ χ := by
  apply CK!_iff_CC!.mpr;
  apply deduct'!;
  exact FiniteContext.of'! (Γ := [ψ]) h;


lemma left_K!_intro_left [DecidableEq F] (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ (φ ⋏ ψ) ➝ χ := C!_trans CKK! (left_K!_intro_right h)


lemma cut! [DecidableEq F] (d₁ : 𝓢 ⊢ φ₁ ⋏ c ➝ ψ₁) (d₂ : 𝓢 ⊢ φ₂ ➝ c ⋎ ψ₂) : 𝓢 ⊢ φ₁ ⋏ φ₂ ➝ ψ₁ ⋎ ψ₂ := by
  apply deduct'!;
  exact of_C!_of_C!_of_A! (right_A!_intro_left $ of'! (CK!_iff_CC!.mp d₁) ⨀ (K!_left id!)) or₂! (of'! d₂ ⨀ K!_right id!);


def inner_A_symm : 𝓢 ⊢! φ ⋎ ψ ➝ ψ ⋎ φ := by
  apply deduct';
  exact of_C_of_C_of_A or₂ or₁ $ FiniteContext.id
lemma or_comm! : 𝓢 ⊢ φ ⋎ ψ ➝ ψ ⋎ φ := ⟨inner_A_symm⟩

def A_symm (h : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ψ ⋎ φ := inner_A_symm ⨀ h
lemma or_comm'! (h : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ψ ⋎ φ := ⟨A_symm h.some⟩



lemma A!_assoc : 𝓢 ⊢ φ ⋎ (ψ ⋎ χ) ↔ 𝓢 ⊢ (φ ⋎ ψ) ⋎ χ := by
  constructor;
  . intro h;
    exact of_C!_of_C!_of_A!
      (right_A!_intro_left $ right_A!_intro_left C!_id)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact of_C!_of_C!_of_A! (right_A!_intro_left $ right_A!_intro_right C!_id) (right_A!_intro_right C!_id) id!;
      )
      h;
  . intro h;
    exact of_C!_of_C!_of_A!
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact of_C!_of_C!_of_A! (right_A!_intro_left C!_id) (right_A!_intro_right $ right_A!_intro_left C!_id) id!;
      )
      (right_A!_intro_right $ right_A!_intro_right C!_id)
      h;



lemma K!_assoc : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ ⭤ φ ⋏ (ψ ⋏ χ) := by
  apply E!_intro;
  . apply FiniteContext.deduct'!;
    have hp : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] φ := K!_left $ K!_left id!;
    have hq : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] ψ := K!_right $ K!_left id!;
    have hr : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] χ := K!_right id!;
    exact K!_intro hp (K!_intro hq hr);
  . apply FiniteContext.deduct'!;
    have hp : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] φ := K!_left id!;
    have hq : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] ψ := K!_left $ K!_right id!;
    have hr : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] χ := K!_right $ K!_right id!;
    apply K!_intro;
    . exact K!_intro hp hq;
    . exact hr;

lemma K!_assoc_mp (h : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ) : 𝓢 ⊢ φ ⋏ (ψ ⋏ χ) := C_of_E_mp! K!_assoc ⨀ h
lemma K!_assoc_mpr (h : 𝓢 ⊢ φ ⋏ (ψ ⋏ χ)) : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ := C_of_E_mpr! K!_assoc ⨀ h

def K_replace_left (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! χ ⋏ ψ := K_intro (h ⨀ K_left hc) (K_right hc)
lemma K!_replace_left (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ χ ⋏ ψ := ⟨K_replace_left hc.some h.some⟩


def CKK_of_C (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ⋏ ψ ➝ χ ⋏ ψ := by
  apply deduct';
  exact K_replace_left FiniteContext.id (of h)
lemma CKK!_of_C! (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ⋏ ψ ➝ χ ⋏ ψ := ⟨CKK_of_C h.some⟩


def K_replace_right (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋏ χ := K_intro (K_left hc) (h ⨀ K_right hc)
lemma K!_replace_right (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋏ χ := ⟨K_replace_right hc.some h.some⟩

def CKK_of_C' (h : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋏ ψ ➝ φ ⋏ χ := by
  apply deduct';
  exact K_replace_right (FiniteContext.id) (of h)
lemma CKK!_of_C!' (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋏ ψ ➝ φ ⋏ χ := ⟨CKK_of_C' h.some⟩

def K_replace (hc : 𝓢 ⊢! φ ⋏ ψ) (h₁ : 𝓢 ⊢! φ ➝ χ) (h₂ : 𝓢 ⊢! ψ ➝ ξ) : 𝓢 ⊢! χ ⋏ ξ := K_replace_right (K_replace_left hc h₁) h₂
lemma K!_replace (hc : 𝓢 ⊢ φ ⋏ ψ) (h₁ : 𝓢 ⊢ φ ➝ χ) (h₂ : 𝓢 ⊢ ψ ➝ ξ) : 𝓢 ⊢ χ ⋏ ξ := ⟨K_replace hc.some h₁.some h₂.some⟩

def CKK_of_C_of_C (h₁ : 𝓢 ⊢! φ ➝ χ) (h₂ : 𝓢 ⊢! ψ ➝ ξ) : 𝓢 ⊢! φ ⋏ ψ ➝ χ ⋏ ξ := by
  apply deduct';
  exact K_replace FiniteContext.id (of h₁) (of h₂)
lemma CKK!_of_C!_of_C! (h₁ : 𝓢 ⊢ φ ➝ χ) (h₂ : 𝓢 ⊢ ψ ➝ ξ) : 𝓢 ⊢ φ ⋏ ψ ➝ χ ⋏ ξ := ⟨CKK_of_C_of_C h₁.some h₂.some⟩

def A_replace_left (hc : 𝓢 ⊢! φ ⋎ ψ) (hp : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! χ ⋎ ψ := of_C_of_C_of_A (C_trans hp or₁) (or₂) hc
lemma A!_replace_left (hc : 𝓢 ⊢ φ ⋎ ψ) (hp : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ χ ⋎ ψ := ⟨A_replace_left hc.some hp.some⟩

def CAA_of_C_left (hp : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ χ ⋎ ψ := by
  apply deduct';
  exact A_replace_left FiniteContext.id (of hp)
lemma A_replace_left! (hp : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ χ ⋎ ψ := ⟨CAA_of_C_left hp.some⟩

def A_replace_right (hc : 𝓢 ⊢! φ ⋎ ψ) (hq : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ χ := of_C_of_C_of_A (or₁) (C_trans hq or₂) hc
lemma A!_replace_right (hc : 𝓢 ⊢ φ ⋎ ψ) (hq : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ χ := ⟨A_replace_right hc.some hq.some⟩

def CAA_of_C_right (hq : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ φ ⋎ χ := by
  apply deduct';
  exact A_replace_right FiniteContext.id (of hq)
lemma CAA!_of_C!_right (hq : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ φ ⋎ χ := ⟨CAA_of_C_right hq.some⟩

def A_replace (h : 𝓢 ⊢! φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢! φ₁ ➝ φ₂) (hq : 𝓢 ⊢! ψ₁ ➝ ψ₂) : 𝓢 ⊢! φ₂ ⋎ ψ₂ := A_replace_right (A_replace_left h hp) hq
lemma A!_replace (h : 𝓢 ⊢ φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢ φ₁ ➝ φ₂) (hq : 𝓢 ⊢ ψ₁ ➝ ψ₂) : 𝓢 ⊢ φ₂ ⋎ ψ₂ := ⟨A_replace h.some hp.some hq.some⟩

def CAA_of_C_of_C (hp : 𝓢 ⊢! φ₁ ➝ φ₂) (hq : 𝓢 ⊢! ψ₁ ➝ ψ₂) : 𝓢 ⊢! φ₁ ⋎ ψ₁ ➝ φ₂ ⋎ ψ₂ := by
  apply deduct';
  exact A_replace FiniteContext.id (of hp) (of hq) ;
lemma CAA!_of_C!_of_C! (hp : 𝓢 ⊢ φ₁ ➝ φ₂) (hq : 𝓢 ⊢ ψ₁ ➝ ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ ➝ φ₂ ⋎ ψ₂ := ⟨CAA_of_C_of_C hp.some hq.some⟩

def EAA_of_E_of_E (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ⋎ ψ₁ ⭤ φ₂ ⋎ ψ₂ := by
  apply E_intro;
  . exact CAA_of_C_of_C (K_left hp) (K_left hq);
  . exact CAA_of_C_of_C (K_right hp) (K_right hq);
lemma EAA!_of_E!_of_E! (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ ⭤ φ₂ ⋎ ψ₂ := ⟨EAA_of_E_of_E hp.some hq.some⟩


lemma EAAAA! : 𝓢 ⊢ φ ⋎ (ψ ⋎ χ) ⭤ (φ ⋎ ψ) ⋎ χ := by
  apply E!_intro;
  . exact deduct'! $ A!_assoc.mp id!;
  . exact deduct'! $ A!_assoc.mpr id!;


lemma EAA!_of_E!_right (d : 𝓢 ⊢ ψ ⭤ χ) : 𝓢 ⊢ φ ⋎ ψ ⭤ φ ⋎ χ := by
  apply E!_intro;
  . apply CAA!_of_C!_right; exact K!_left d;
  . apply CAA!_of_C!_right; exact K!_right d;


lemma EAA!_of_E!_left (d : 𝓢 ⊢ φ ⭤ χ) : 𝓢 ⊢ φ ⋎ ψ ⭤ χ ⋎ ψ := by
  apply E!_intro;
  . apply A_replace_left!; exact K!_left d;
  . apply A_replace_left!; exact K!_right d;


def EKK_of_E_of_E (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ⋏ ψ₁ ⭤ φ₂ ⋏ ψ₂ := by
  apply E_intro;
  . exact CKK_of_C_of_C (K_left hp) (K_left hq);
  . exact CKK_of_C_of_C (K_right hp) (K_right hq);
lemma EKK!_of_E!_of_E! (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ φ₁ ⋏ ψ₁ ⭤ φ₂ ⋏ ψ₂ := ⟨EKK_of_E_of_E hp.some hq.some⟩

def ECC_of_E_of_E (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! (φ₁ ➝ ψ₁) ⭤ (φ₂ ➝ ψ₂) := by
  apply E_intro;
  . apply deduct'; exact C_trans (of $ K_right hp) $ C_trans (FiniteContext.id) (of $ K_left hq);
  . apply deduct'; exact C_trans (of $ K_left hp) $ C_trans (FiniteContext.id) (of $ K_right hq);
lemma ECC!_of_E!_of_E! (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ (φ₁ ➝ ψ₁) ⭤ (φ₂ ➝ ψ₂) := ⟨ECC_of_E_of_E hp.some hq.some⟩


lemma C!_repalce [DecidableEq F] (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ φ₁ ➝ ψ₁ ↔ 𝓢 ⊢ φ₂ ➝ ψ₂ :=
  iff_of_E! (ECC!_of_E!_of_E! hp hq)

def dni [DecidableEq F] : 𝓢 ⊢! φ ➝ ∼∼φ := by
  apply deduct';
  apply N_of_CO;
  apply deduct;
  exact bot_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma dni! [DecidableEq F] : 𝓢 ⊢ φ ➝ ∼∼φ := ⟨dni⟩

def dni' [DecidableEq F] (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼∼φ := dni ⨀ b
lemma dni'! [DecidableEq F] (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ∼∼φ := ⟨dni' b.some⟩

def ANNNN_of_A [DecidableEq F] (d : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ := of_C_of_C_of_A (C_trans dni or₁) (C_trans dni or₂) d
lemma ANNNN!_of_A! [DecidableEq F] (d : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ := ⟨ANNNN_of_A d.some⟩

def KNNNN_of_K [DecidableEq F] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ∼∼φ ⋏ ∼∼ψ := K_intro (dni' $ K_left d) (dni' $ K_right d)
lemma KNNNN!_of_K! [DecidableEq F] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ∼∼φ ⋏ ∼∼ψ := ⟨KNNNN_of_K d.some⟩

def CNNOO : 𝓢 ⊢! ∼∼⊥ ➝ ⊥ := by
  apply deduct'
  have d₁ : [∼∼⊥] ⊢[𝓢]! ∼⊥ ➝ ⊥ := CO_of_N byAxm₀
  have d₂ : [∼∼⊥] ⊢[𝓢]! ∼⊥ := N_of_CO C_id
  exact d₁ ⨀ d₂

def ENNOO [DecidableEq F] : 𝓢 ⊢! ∼∼⊥ ⭤ ⊥ := K_intro CNNOO dni


def CCCNN [DecidableEq F] : 𝓢 ⊢! (φ ➝ ψ) ➝ (∼ψ ➝ ∼φ) := by
  apply deduct';
  apply deduct;
  apply N_of_CO;
  apply deduct;
  have dp  : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢]! φ := FiniteContext.byAxm;
  have dpq : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢]! φ ➝ ψ := FiniteContext.byAxm;
  have dq  : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢]! ψ := dpq ⨀ dp;
  have dnq : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢]! ψ ➝ ⊥ := CO_of_N $ FiniteContext.byAxm;
  exact dnq ⨀ dq;
@[simp] def CCCNN! [DecidableEq F] : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼ψ ➝ ∼φ) := ⟨CCCNN⟩

@[deprecated "use `CCCNN`"] alias contra₀ := CCCNN
@[deprecated "use `CCCNN!`"] alias contra₀! := CCCNN!

def contra [DecidableEq F] (b : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼ψ ➝ ∼φ := CCCNN ⨀ b
lemma contra! [DecidableEq F] (b : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼ψ ➝ ∼φ := ⟨contra b.some⟩

@[deprecated "use `contra`"] alias contra₀' := contra
@[deprecated "use `contra!`"] alias contra₀'! := contra!

def CNNNN_of_C [DecidableEq F] (b : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ := contra $ contra b
@[grind] lemma CNNNN!_of_C! [DecidableEq F] (b : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ := ⟨CNNNN_of_C b.some⟩

def CCCNNNN [DecidableEq F] : 𝓢 ⊢! (φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := deduct' $ CNNNN_of_C FiniteContext.id
@[simp] lemma CCCNNNN! [DecidableEq F] : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := ⟨CCCNNNN⟩


def CN_of_CN_right [DecidableEq F] (b : 𝓢 ⊢! φ ➝ ∼ψ) : 𝓢 ⊢! ψ ➝ ∼φ := C_trans dni (contra b)
lemma CN!_of_CN!_right [DecidableEq F] (b : 𝓢 ⊢ φ ➝ ∼ψ) : 𝓢 ⊢ ψ ➝ ∼φ := ⟨CN_of_CN_right b.some⟩

def CCNCN [DecidableEq F] : 𝓢 ⊢! (φ ➝ ∼ψ) ➝ (ψ ➝ ∼φ) := deduct' $ CN_of_CN_right FiniteContext.id
lemma CCNCN! [DecidableEq F] : 𝓢 ⊢ (φ ➝ ∼ψ) ➝ (ψ ➝ ∼φ) := ⟨CCNCN⟩

def ENN_of_E [DecidableEq F] (b : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ∼φ ⭤ ∼ψ := E_intro (contra $ K_right b) (contra $ K_left b)
lemma ENN!_of_E! [DecidableEq F] (b : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ∼φ ⭤ ∼ψ := ⟨ENN_of_E b.some⟩


section NegationEquiv

variable [Entailment.NegationEquiv 𝓢]

def ENNCCOO [DecidableEq F] : 𝓢 ⊢! ∼∼φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := by
  apply E_intro;
  . exact C_trans (by apply contra; exact K_right negEquiv) (K_left negEquiv)
  . exact C_trans (K_right negEquiv) (by apply contra; exact K_left negEquiv)
@[simp] lemma ENNCCOO! [DecidableEq F] : 𝓢 ⊢ ∼∼φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := ⟨ENNCCOO⟩

end NegationEquiv


def tne [DecidableEq F] : 𝓢 ⊢! ∼(∼∼φ) ➝ ∼φ := contra dni
@[simp] lemma tne! [DecidableEq F] : 𝓢 ⊢ ∼(∼∼φ) ➝ ∼φ := ⟨tne⟩

def tne' [DecidableEq F] (b : 𝓢 ⊢! ∼(∼∼φ)) : 𝓢 ⊢! ∼φ := tne ⨀ b
lemma tne'! [DecidableEq F] (b : 𝓢 ⊢ ∼(∼∼φ)) : 𝓢 ⊢ ∼φ := ⟨tne' b.some⟩

def tneIff [DecidableEq F] : 𝓢 ⊢! ∼∼∼φ ⭤ ∼φ := K_intro tne dni

def CCC_of_C_left (h : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ χ) := by
  apply deduct';
  exact C_trans (of h) id;
lemma CCC!_of_C!_left (h : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) := ⟨CCC_of_C_left h.some⟩

@[deprecated "use `CCC_of_C_left`"] alias rev_dhyp_imp' := CCC_of_C_left
@[deprecated "use `CCC!_of_C!_left`"] alias rev_dhyp_imp'! := CCC!_of_C!_left

lemma C!_iff_C!_of_iff_left (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ φ ➝ χ ↔ 𝓢 ⊢ ψ ➝ χ := by
  constructor;
  . exact C!_trans $ K!_right h;
  . exact C!_trans $ K!_left h;

lemma C!_iff_C!_of_iff_right (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ χ ➝ φ ↔ 𝓢 ⊢ χ ➝ ψ := by
  constructor;
  . intro hrp; exact C!_trans hrp $ K!_left h;
  . intro hrq; exact C!_trans hrq $ K!_right h;

def C_swap [DecidableEq F] (h : 𝓢 ⊢! φ ➝ ψ ➝ χ) : 𝓢 ⊢! ψ ➝ φ ➝ χ := by
  apply deduct';
  apply deduct;
  exact (of (Γ := [φ, ψ]) h) ⨀ FiniteContext.byAxm ⨀ FiniteContext.byAxm;
lemma C!_swap [DecidableEq F] (h : 𝓢 ⊢ (φ ➝ ψ ➝ χ)) : 𝓢 ⊢ (ψ ➝ φ ➝ χ) := ⟨C_swap h.some⟩

def CCCCC [DecidableEq F] : 𝓢 ⊢! (φ ➝ ψ ➝ χ) ➝ (ψ ➝ φ ➝ χ) := deduct' $ C_swap FiniteContext.id
@[simp] lemma CCCCC! [DecidableEq F] : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ (ψ ➝ φ ➝ χ) := ⟨CCCCC⟩

def C_of_CC [DecidableEq F] (h : 𝓢 ⊢! φ ➝ φ ➝ ψ) : 𝓢 ⊢! φ ➝ ψ := by
  apply deduct';
  have := of (Γ := [φ]) h;
  exact this ⨀ (FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
lemma C!_of_CC! [DecidableEq F] (h : 𝓢 ⊢ φ ➝ φ ➝ ψ) : 𝓢 ⊢ φ ➝ ψ := ⟨C_of_CC h.some⟩

def CCC [DecidableEq F] : 𝓢 ⊢! φ ➝ (φ ➝ ψ) ➝ ψ := C_swap $ C_id
lemma CCC! [DecidableEq F] : 𝓢 ⊢ φ ➝ (φ ➝ ψ) ➝ ψ := ⟨CCC⟩

def CCC_of_C_right (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! (χ ➝ φ) ➝ (χ ➝ ψ) := implyS ⨀ (C_of_conseq h)
lemma CCC!_of_C!_right (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ (χ ➝ φ) ➝ (χ ➝ ψ) := ⟨CCC_of_C_right h.some⟩

def CNNCCNNNN [DecidableEq F] : 𝓢 ⊢! ∼∼(φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := by
  apply C_swap;
  apply deduct';
  exact C_trans (CNNNN_of_C $ deductInv $ of $ C_swap $ CCCNNNN) tne;
@[simp] lemma CNNCCNNNN! [DecidableEq F] : 𝓢 ⊢ ∼∼(φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := ⟨CNNCCNNNN⟩

def CNNNN_of_NNC [DecidableEq F] (b : 𝓢 ⊢! ∼∼(φ ➝ ψ)) : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ := CNNCCNNNN ⨀ b
lemma CNNNN!_of_NNC! [DecidableEq F] (b : 𝓢 ⊢ ∼∼(φ ➝ ψ)) : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ := ⟨CNNNN_of_NNC b.some⟩

def O_intro_of_KN (h : 𝓢 ⊢! φ ⋏ ∼φ) : 𝓢 ⊢! ⊥ := (CO_of_N $ K_right h) ⨀ (K_left h)
lemma O!_intro_of_KN! (h : 𝓢 ⊢ φ ⋏ ∼φ) : 𝓢 ⊢ ⊥ := ⟨O_intro_of_KN h.some⟩
/-- Law of contradiction -/
alias lac'! := O!_intro_of_KN!

def CKNO : 𝓢 ⊢! φ ⋏ ∼φ ➝ ⊥ := by
  apply deduct';
  exact O_intro_of_KN (φ := φ) $ FiniteContext.id
@[simp] lemma CKNO! : 𝓢 ⊢ φ ⋏ ∼φ ➝ ⊥ := ⟨CKNO⟩
/-- Law of contradiction -/
alias lac! := CKNO!

def CANNNK [DecidableEq F] : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ➝ ∼(φ ⋏ ψ) := left_A_intro (contra and₁) (contra and₂)
@[simp] lemma CANNNK! [DecidableEq F] : 𝓢 ⊢ (∼φ ⋎ ∼ψ) ➝ ∼(φ ⋏ ψ) := ⟨CANNNK⟩

def NK_of_ANN [DecidableEq F] (d : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! ∼(φ ⋏ ψ)  := CANNNK ⨀ d
lemma NK!_of_ANN! [DecidableEq F] (d : 𝓢 ⊢ ∼φ ⋎ ∼ψ) : 𝓢 ⊢ ∼(φ ⋏ ψ) := ⟨NK_of_ANN d.some⟩

def CKNNNA [DecidableEq F] : 𝓢 ⊢! (∼φ ⋏ ∼ψ) ➝ ∼(φ ⋎ ψ) := by
  apply CK_of_CC;
  apply deduct';
  apply deduct;
  apply N_of_CO;
  apply deduct;
  exact of_C_of_C_of_A (CO_of_N FiniteContext.byAxm) (CO_of_N FiniteContext.byAxm) (FiniteContext.byAxm (φ := φ ⋎ ψ));
@[simp] lemma CKNNNA! [DecidableEq F] : 𝓢 ⊢ ∼φ ⋏ ∼ψ ➝ ∼(φ ⋎ ψ) := ⟨CKNNNA⟩

def NA_of_KNN [DecidableEq F] (d : 𝓢 ⊢! ∼φ ⋏ ∼ψ) : 𝓢 ⊢! ∼(φ ⋎ ψ) := CKNNNA ⨀ d
lemma NA!_of_KNN! [DecidableEq F] (d : 𝓢 ⊢ ∼φ ⋏ ∼ψ) : 𝓢 ⊢ ∼(φ ⋎ ψ) := ⟨NA_of_KNN d.some⟩


def CNAKNN [DecidableEq F] : 𝓢 ⊢! ∼(φ ⋎ ψ) ➝ (∼φ ⋏ ∼ψ) := by
  apply deduct';
  exact K_intro (deductInv $ contra $ or₁) (deductInv $ contra $ or₂)
@[simp] lemma CNAKNN! [DecidableEq F] : 𝓢 ⊢ ∼(φ ⋎ ψ) ➝ (∼φ ⋏ ∼ψ) := ⟨CNAKNN⟩

def KNN_of_NA [DecidableEq F] (b : 𝓢 ⊢! ∼(φ ⋎ ψ)) : 𝓢 ⊢! ∼φ ⋏ ∼ψ := CNAKNN ⨀ b
lemma KNN!_of_NA! [DecidableEq F] (b : 𝓢 ⊢ ∼(φ ⋎ ψ)) : 𝓢 ⊢ ∼φ ⋏ ∼ψ := ⟨KNN_of_NA b.some⟩




section Conjunction

def EConj₂Conj : (Γ : List F) → 𝓢 ⊢! ⋀Γ ⭤ Γ.conj
  | []          => E_Id
  | [_]         => E_intro (deduct' <| K_intro FiniteContext.id verum) and₁
  | _ :: ψ :: Γ => EKK_of_E_of_E (E_Id) (EConj₂Conj (ψ :: Γ))
@[simp] lemma EConj₂Conj! : 𝓢 ⊢ ⋀Γ ⭤ Γ.conj := ⟨EConj₂Conj Γ⟩

lemma CConj!_iff_CConj₂ : 𝓢 ⊢ Γ.conj ➝ φ ↔ 𝓢 ⊢ ⋀Γ ➝ φ := C!_iff_C!_of_iff_left $ E!_symm EConj₂Conj!

/--! note: It may be easier to handle define `List.conj` based on `List.conj' (?)`  -/
def right_Conj'_intro [DecidableEq F] (φ : F) (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢! φ ➝ ψ i) : 𝓢 ⊢! φ ➝ l.conj' ψ :=
  right_Conj₂_intro φ (l.map ψ) fun χ h ↦
    let ⟨i, hi, e⟩ := l.chooseX (fun i ↦ ψ i = χ) (by simpa using h)
    e ▸ (b i hi)
lemma right_Conj'!_intro [DecidableEq F] (φ : F) (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢ φ ➝ ψ i) : 𝓢 ⊢ φ ➝ l.conj' ψ :=
  ⟨right_Conj'_intro φ l ψ fun i hi ↦ (b i hi).get⟩

def left_Conj'_intro [DecidableEq F] {l : List ι} (h : i ∈ l) (φ : ι → F) : 𝓢 ⊢! l.conj' φ ➝ φ i := left_Conj₂_intro (by simp; use i)
lemma left_Conj'!_intro [DecidableEq F] {l : List ι} (h : i ∈ l) (φ : ι → F) : 𝓢 ⊢ l.conj' φ ➝ φ i := ⟨left_Conj'_intro h φ⟩


lemma right_Fconj!_intro (φ : F) (s : Finset F) (b : (ψ : F) → ψ ∈ s → 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ s.conj :=
  right_Conj₂!_intro φ s.toList fun ψ hψ ↦ b ψ (by simpa using hψ)

lemma left_Fconj!_intro [DecidableEq F] {s : Finset F} (h : φ ∈ s) : 𝓢 ⊢ s.conj ➝ φ := left_Conj₂!_intro <| by simp [h]

lemma right_Fconj'!_intro [DecidableEq F] (φ : F) (s : Finset ι) (ψ : ι → F) (b : ∀ i ∈ s, 𝓢 ⊢ φ ➝ ψ i) :
    𝓢 ⊢ φ ➝ ⩕ i ∈ s, ψ i := right_Conj'!_intro φ s.toList ψ (by simpa)

lemma left_Fconj'!_intro [DecidableEq F] {s : Finset ι} (φ : ι → F) {i} (hi : i ∈ s) : 𝓢 ⊢ (⩕ i ∈ s, φ i) ➝ φ i :=
  left_Conj'!_intro (by simpa) φ

lemma right_Uconj!_intro [DecidableEq F] [Fintype ι] (φ : F) (ψ : ι → F) (b : (i : ι) → 𝓢 ⊢ φ ➝ ψ i) :
    𝓢 ⊢ φ ➝ ⩕ i, ψ i := right_Fconj'!_intro φ Finset.univ ψ (by simpa using b)

lemma left_Uconj!_intro [DecidableEq F] [Fintype ι] (φ : ι → F) (i) : 𝓢 ⊢ (⩕ i, φ i) ➝ φ i := left_Fconj'!_intro _ <| by simp


lemma Conj₂!_iff_forall_provable [DecidableEq F] {Γ : List F} : (𝓢 ⊢ ⋀Γ) ↔ (∀ φ ∈ Γ, 𝓢 ⊢ φ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all;
    constructor;
    . intro h;
      constructor;
      . exact K!_left h;
      . exact ih.mp (K!_right h);
    . rintro ⟨h₁, h₂⟩;
      exact K!_intro h₁ (ih.mpr h₂);

lemma CConj₂Conj₂!_of_subset [DecidableEq F] (h : ∀ φ, φ ∈ Γ → φ ∈ Δ) : 𝓢 ⊢ ⋀Δ ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp_all; exact left_Conj₂!_intro h;
  | hcons φ Γ hne ih => simp_all; exact right_K!_intro (left_Conj₂!_intro h.1) ih;

lemma CConj₂Conj₂!_of_provable [DecidableEq F] (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢] φ) : 𝓢 ⊢ ⋀Δ ➝ ⋀Γ :=
  by induction Γ using List.induction_with_singleton with
  | hnil => exact C!_of_conseq! verum!;
  | hsingle => simp_all; exact provable_iff.mp h;
  | hcons φ Γ hne ih => simp_all; exact right_K!_intro (provable_iff.mp h.1) ih;

lemma CConj₂!_of_forall_provable [DecidableEq F] (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢] φ) : Δ ⊢[𝓢] ⋀Γ := provable_iff.mpr $ CConj₂Conj₂!_of_provable h

lemma CConj₂!_of_unique [DecidableEq F] (he : ∀ g ∈ Γ, g = φ) : 𝓢 ⊢ φ ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hcons χ Γ h ih =>
    simp_all;
    have ⟨he₁, he₂⟩ := he; subst he₁;
    exact right_K!_intro C!_id ih;
  | _ => simp_all;

lemma C!_of_CConj₂!_of_unique [DecidableEq F] (he : ∀ g ∈ Γ, g = φ) (hd : 𝓢 ⊢ ⋀Γ ➝ ψ) : 𝓢 ⊢ φ ➝ ψ := C!_trans (CConj₂!_of_unique he) hd

lemma CConj₂!_iff_CKConj₂! [DecidableEq F] : 𝓢 ⊢ ⋀(φ :: Γ) ➝ ψ ↔ 𝓢 ⊢ φ ⋏ ⋀Γ ➝ ψ := by
  induction Γ with
  | nil =>
    simp [CK!_iff_CC!];
    constructor;
    . intro h; apply C!_swap; exact C!_of_conseq! h;
    . intro h; exact C!_swap h ⨀ verum!;
  | cons ψ ih => simp;


@[simp] lemma CConj₂AppendKConj₂Conj₂! [DecidableEq F] : 𝓢 ⊢ ⋀(Γ ++ Δ) ➝ ⋀Γ ⋏ ⋀Δ := by
  apply FiniteContext.deduct'!;
  have : [⋀(Γ ++ Δ)] ⊢[𝓢] ⋀(Γ ++ Δ) := id!;
  have d := Conj₂!_iff_forall_provable.mp this;
  apply K!_intro;
  . apply Conj₂!_iff_forall_provable.mpr;
    intro φ hp;
    exact d φ (by simp; left; exact hp);
  . apply Conj₂!_iff_forall_provable.mpr;
    intro φ hp;
    exact d φ (by simp; right; exact hp);

@[simp]
lemma CKConj₂RemoveConj₂! [DecidableEq F] : 𝓢 ⊢ ⋀(Γ.remove φ) ⋏ φ ➝ ⋀Γ := by
  apply deduct'!;
  apply Conj₂!_iff_forall_provable.mpr;
  intro ψ hq;
  by_cases e : ψ = φ;
  . subst e; exact K!_right id!;
  . exact Conj₂!_iff_forall_provable.mp (K!_left id!) ψ (by apply List.mem_remove_iff.mpr; simp_all);

lemma CKConj₂Remove!_of_CConj₂! [DecidableEq F] (b : 𝓢 ⊢ ⋀Γ ➝ ψ) : 𝓢 ⊢ ⋀(Γ.remove φ) ⋏ φ ➝ ψ := C!_trans CKConj₂RemoveConj₂! b


lemma Conj₂Append!_iff_KConj₂Conj₂! [DecidableEq F] : 𝓢 ⊢ ⋀(Γ ++ Δ) ↔ 𝓢 ⊢ ⋀Γ ⋏ ⋀Δ := by
  constructor;
  . intro h;
    replace h := Conj₂!_iff_forall_provable.mp h;
    apply K!_intro;
    . apply Conj₂!_iff_forall_provable.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; left; simpa);
    . apply Conj₂!_iff_forall_provable.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; right; simpa);
  . intro h;
    apply Conj₂!_iff_forall_provable.mpr;
    simp only [List.mem_append];
    rintro φ (hp₁ | hp₂);
    . exact (Conj₂!_iff_forall_provable.mp $ K!_left h) φ hp₁;
    . exact (Conj₂!_iff_forall_provable.mp $ K!_right h) φ hp₂;


@[simp] lemma EConj₂AppendKConj₂Conj₂! [DecidableEq F] : 𝓢 ⊢ ⋀(Γ ++ Δ) ⭤ ⋀Γ ⋏ ⋀Δ := by
  apply E!_intro;
  . apply deduct'!; apply Conj₂Append!_iff_KConj₂Conj₂!.mp; exact id!;
  . apply deduct'!; apply Conj₂Append!_iff_KConj₂Conj₂!.mpr; exact id!;


lemma CConj₂Append!_iff_CKConj₂Conj₂! [DecidableEq F] : 𝓢 ⊢ ⋀(Γ ++ Δ) ➝ φ ↔ 𝓢 ⊢ (⋀Γ ⋏ ⋀Δ) ➝ φ := by
  constructor;
  . intro h; exact C!_trans (K!_right EConj₂AppendKConj₂Conj₂!) h;
  . intro h; exact C!_trans (K!_left EConj₂AppendKConj₂Conj₂!) h;

@[simp] lemma CFConjConj₂ [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ ⋀Γ.toList ➝ Γ.conj := by
  apply CConj₂Conj₂!_of_provable;
  apply FiniteContext.by_axm!;

@[simp] lemma CConj₂Conj_list [DecidableEq F] {Γ : List F} : 𝓢 ⊢ ⋀Γ ➝ Γ.toFinset.conj := by
  apply C!_trans ?_ CFConjConj₂;
  apply CConj₂Conj₂!_of_subset;
  simp;

@[simp] lemma CConj₂FConj [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ Γ.conj ➝ ⋀Γ.toList := by
  apply right_Conj₂!_intro;
  intro φ hφ;
  apply left_Fconj!_intro;
  simpa using hφ;

@[simp] lemma CConj₂FConj_list [DecidableEq F] {Γ : List F} : 𝓢 ⊢ Γ.toFinset.conj ➝ ⋀Γ := by
  apply C!_trans $ CConj₂FConj;
  apply CConj₂Conj₂!_of_subset;
  simp;

lemma FConj_DT [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ Γ.conj ➝ φ ↔ Γ *⊢[𝓢] φ := by
  constructor;
  . intro h;
    apply Context.provable_iff.mpr;
    use Γ.toList;
    constructor;
    . simp;
    . apply FiniteContext.provable_iff.mpr;
      exact C!_trans (by simp) h;
  . intro h;
    obtain ⟨Δ, hΔ₁, hΔ₂⟩ := Context.provable_iff.mp h;
    replace hΔ₂ : 𝓢 ⊢ ⋀Γ.toList ➝ φ := C!_trans (CConj₂Conj₂!_of_subset (by simpa)) $ FiniteContext.provable_iff.mp hΔ₂
    exact C!_trans (by simp) hΔ₂;

lemma FConj!_iff_forall_provable [DecidableEq F] {Γ : Finset F} : (𝓢 ⊢ Γ.conj) ↔ (∀ φ ∈ Γ, 𝓢 ⊢ φ) := by
  apply Iff.trans Conj₂!_iff_forall_provable;
  constructor <;> simp_all;

lemma FConj_of_FConj!_of_subset [DecidableEq F] {Γ Δ : Finset F} (h : Δ ⊆ Γ) (hΓ : 𝓢 ⊢ Γ.conj) : 𝓢 ⊢ Δ.conj := by
  rw [FConj!_iff_forall_provable] at hΓ ⊢;
  intro φ hφ;
  apply hΓ;
  apply h hφ;

lemma CFConj_FConj!_of_subset [DecidableEq F] {Γ Δ : Finset F} (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj ➝ Δ.conj := by
  apply FConj_DT.mpr;
  apply FConj_of_FConj!_of_subset h;
  apply FConj_DT.mp;
  simp;

@[simp] lemma CFconjUnionKFconj! [DecidableEq F] {Γ Δ : Finset F} : 𝓢 ⊢ (Γ ∪ Δ).conj ➝ Γ.conj ⋏ Δ.conj := by
  apply FConj_DT.mpr;
  apply K!_intro <;>
  . apply FConj_DT.mp;
    apply CFConj_FConj!_of_subset;
    simp;

@[simp] lemma CinsertFConjKFConj! [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ (insert φ Γ).conj ➝ φ ⋏ Γ.conj := by
  suffices 𝓢 ⊢ ({φ} ∪ Γ).conj ➝ (Finset.conj {φ}) ⋏ Γ.conj by simpa using this;
  apply CFconjUnionKFconj!;

@[simp] lemma CKFconjFconjUnion! [DecidableEq F] {Γ Δ : Finset F} : 𝓢 ⊢ Γ.conj ⋏ Δ.conj ➝ (Γ ∪ Δ).conj := by
  apply right_Fconj!_intro;
  simp only [Finset.mem_union];
  rintro φ (hφ | hφ);
  . apply left_K!_intro_left
    apply left_Fconj!_intro hφ;
  . apply left_K!_intro_right;
    apply left_Fconj!_intro hφ;

@[simp]
lemma CKFConjinsertFConj! [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ φ ⋏ Γ.conj ➝ (insert φ Γ).conj := by
  suffices 𝓢 ⊢ (Finset.conj {φ}) ⋏ Γ.conj ➝ ({φ} ∪ Γ).conj by simpa using this;
  apply CKFconjFconjUnion!;

lemma FConj_DT' [DecidableEq F] {Γ Δ : Finset F} : Γ *⊢[𝓢] Δ.conj ➝ φ ↔ ↑(Γ ∪ Δ) *⊢[𝓢] φ := by
  constructor;
  . intro h; exact FConj_DT.mp $ C!_trans CFconjUnionKFconj! $ CK!_iff_CC!.mpr $ FConj_DT.mpr h;
  . intro h; exact FConj_DT.mp $ CK!_iff_CC!.mp $ C!_trans CKFconjFconjUnion! $ FConj_DT.mpr h;

lemma CFconjFconj!_of_provable [DecidableEq F] {Γ Δ : Finset _} (h : ∀ φ, φ ∈ Γ → Δ *⊢[𝓢] φ) : 𝓢 ⊢ Δ.conj ➝ Γ.conj := by
  have : 𝓢 ⊢ ⋀(Δ.toList) ➝ ⋀(Γ.toList) := CConj₂Conj₂!_of_provable $ by
    intro φ hφ;
    apply Context.iff_provable_context_provable_finiteContext_toList.mp
    apply h φ;
    simpa using hφ;
  refine C!_replace ?_ ?_ this;
  . simp;
  . simp;

end Conjunction


section disjunction

def right_Disj_intro [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢! φ ➝ Γ.disj :=
  match Γ with
  |     [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ then cast (by simp [e]) (or₁ : 𝓢 ⊢! φ ➝ φ ⋎ Γ.disj)
    else
      have : φ ∈ Γ := by simpa [e] using h
      C_trans (right_Disj_intro Γ this) or₂
def right_Disj!_intro [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢ φ ➝ Γ.disj := ⟨right_Disj_intro Γ h⟩

def right_Disj_intro' [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) (hψ : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! ψ ➝ Γ.disj :=
  C_trans hψ (right_Disj_intro Γ h)
def right_Disj!_intro' [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) (hψ : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ ψ ➝ Γ.disj := ⟨right_Disj_intro' Γ h hψ.get⟩

def right_Disj₂_intro [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢! φ ➝ ⋁Γ :=
  match Γ with
  |     [] => by simp at h
  |    [ψ] => (show ⋁[ψ] = φ by simp_all) ▸ C_id
  | ψ :: χ :: Γ =>
    if e : φ = ψ then cast (by simp [e]) (or₁ : 𝓢 ⊢! φ ➝ φ ⋎ ⋁(χ :: Γ))
    else
      have : φ ∈ χ :: Γ := by simpa [e] using h
      C_trans (right_Disj₂_intro _ this) or₂
def right_Disj₂!_intro [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢ φ ➝ ⋁Γ := ⟨right_Disj₂_intro Γ h⟩

def right_Disj'_intro [DecidableEq F] (φ : ι → F) (l : List ι) (h : i ∈ l) : 𝓢 ⊢! φ i ➝ l.disj' φ :=
  right_Disj₂_intro (l.map φ) (by simp; exact ⟨i, h, rfl⟩)
lemma right_Disj'!_intro [DecidableEq F] (φ : ι → F) (l : List ι) (h : i ∈ l) : 𝓢 ⊢ φ i ➝ l.disj' φ := ⟨right_Disj'_intro φ l h⟩

lemma right_Fdisj!_intro [DecidableEq F] (s : Finset F) (h : φ ∈ s) : 𝓢 ⊢ φ ➝ s.disj := right_Disj₂!_intro _ (by simp [h])

lemma right_Fdisj'!_intro [DecidableEq F] (s : Finset ι) (φ : ι → F) {i} (hi : i ∈ s) : 𝓢 ⊢ φ i ➝ ⩖ j ∈ s, φ j :=
  right_Disj'!_intro _ _ (by simp [hi])

lemma right_Udisj!_intro [DecidableEq F] [Fintype ι] (φ : ι → F) : 𝓢 ⊢ φ i ➝ ⩖ j, φ j := right_Fdisj'!_intro _ _ (by simp)

end disjunction


section

variable {Γ Δ : Finset F}

lemma CFConj_CDisj!_of_K_intro [DecidableEq F] (hp : φ ∈ Γ) (hpq : ψ ∈ Γ) (hψ : φ ⋏ ψ ∈ Δ) : 𝓢 ⊢ Γ.conj ➝ Δ.disj := by
  apply C!_trans (ψ := Finset.disj {φ ⋏ ψ});
  . apply C!_trans (ψ := Finset.conj {φ, ψ}) ?_;
    . apply FConj_DT.mpr;
      simp only [Finset.coe_insert, Finset.coe_singleton, Finset.disj_singleton];
      apply K!_intro <;> exact Context.by_axm! $ by simp;
    . apply CFConj_FConj!_of_subset;
      apply Finset.doubleton_subset.mpr;
      tauto;
  . simp only [Finset.disj_singleton];
    apply right_Fdisj!_intro _ hψ;

lemma CFConj_CDisj!_of_innerMDP [DecidableEq F] (hp : φ ∈ Γ) (hpq : φ ➝ ψ ∈ Γ) (hψ : ψ ∈ Δ) : 𝓢 ⊢ Γ.conj ➝ Δ.disj := by
  apply C!_trans (ψ := Finset.disj {ψ});
  . apply C!_trans (ψ := Finset.conj {φ, φ ➝ ψ}) ?_;
    . apply FConj_DT.mpr;
      have h₁ : ({φ, φ ➝ ψ}) *⊢[𝓢] φ ➝ ψ := Context.by_axm! $ by simp;
      have h₂ : ({φ, φ ➝ ψ}) *⊢[𝓢] φ := Context.by_axm! $ by simp;
      simpa using h₁ ⨀ h₂;
    . apply CFConj_FConj!_of_subset;
      apply Finset.doubleton_subset.mpr;
      tauto;
  . simp only [Finset.disj_singleton];
    apply right_Fdisj!_intro _ hψ;

lemma iff_FiniteContext_Context [DecidableEq F] {Γ : List F} : Γ ⊢[𝓢] φ ↔ ↑Γ.toFinset *⊢[𝓢] φ := by
  constructor;
  . intro h;
    replace h := FiniteContext.provable_iff.mp h;
    apply FConj_DT.mp;
    exact C!_trans (by simp) h;
  . intro h;
    replace h := FConj_DT.mpr h;
    apply FiniteContext.provable_iff.mpr;
    exact C!_trans (by simp) h;

lemma FConj'_iff_forall_provable [DecidableEq F] {s : Finset α} {ι : α → F} : (𝓢 ⊢ ⩕ i ∈ s, ι i) ↔ (∀ i ∈ s, 𝓢 ⊢ ι i) := by
  have : 𝓢 ⊢ ⋀(s.toList.map ι) ↔ ∀ i ∈ s, 𝓢 ⊢ ι i := by simpa using Conj₂!_iff_forall_provable (Γ := s.toList.map ι);
  apply Iff.trans ?_ this;
  simp [Finset.conj', List.conj'];

end


namespace Context

lemma provable_iff_finset [DecidableEq F] {Γ : Set F} {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : Finset F, (Δ.toSet ⊆ Γ) ∧ Δ *⊢[𝓢] φ := by
  apply Iff.trans Context.provable_iff;
  constructor;
  . rintro ⟨Δ, hΔ₁, hΔ₂⟩;
    use Δ.toFinset;
    constructor;
    . simpa;
    . apply provable_iff.mpr
      use Δ;
      constructor <;> simp_all;
  . rintro ⟨Δ, hΔ₁, hΔ₂⟩;
    use Δ.toList;
    constructor;
    . simpa;
    . apply FiniteContext.provable_iff.mpr;
      refine C!_trans ?_ (FConj_DT.mpr hΔ₂);
      simp;

lemma bot_of_mem_neg [DecidableEq F] {Γ : Set F}  (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ *⊢[𝓢] ⊥ := by
  replace h₁ : Γ *⊢[𝓢] φ := by_axm! h₁;
  replace h₂ : Γ *⊢[𝓢] φ ➝ ⊥ := N!_iff_CO!.mp $ by_axm! h₂;
  exact h₂ ⨀ h₁;

end Context

end


end LO.Entailment
