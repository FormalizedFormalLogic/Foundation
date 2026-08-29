module

public import Foundation.Logic.Entailment
public import Foundation.Vorspiel.Finset.Basic

@[expose] public section

namespace LO.Axioms

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

end LO.Axioms




namespace LO.Entailment


-- def cast (e : φ = ψ) (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ := e ▸ b
-- lemma cast! (e : φ = ψ) (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ := ⟨cast e b.some⟩

section

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class ModusPonens (𝓢 : S) where
  mdp! {φ ψ : F} : 𝓢 ⊢! φ 🡒 ψ → 𝓢 ⊢! φ → 𝓢 ⊢! ψ

alias mdp! := ModusPonens.mdp!
infixl:90 "⨀" => mdp!

lemma mdp [ModusPonens 𝓢] : 𝓢 ⊢ φ 🡒 ψ → 𝓢 ⊢ φ → 𝓢 ⊢ ψ := by
  rintro ⟨hpq⟩ ⟨hp⟩;
  exact ⟨hpq ⨀ hp⟩
infixl:90 "⨀" => mdp
infixl:90 "⨀!" => mdp!




/--
  Negation `∼φ` is equivalent to `φ 🡒 ⊥` on **system**.

  This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ 🡒 ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv [LogicalNeutral F] (𝓢 : S) where
  negEquiv! {φ : F} : 𝓢 ⊢! Axioms.NegEquiv φ
export NegationEquiv (negEquiv!)

@[simp] lemma neg_equiv [LogicalNeutral F] [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ 🡘 (φ 🡒 ⊥) := ⟨negEquiv!⟩


class HasAxiomVerum [LogicalNeutral F] (𝓢 : S) where
  verum! : 𝓢 ⊢! Axioms.Verum

def verum! [LogicalNeutral F] [HasAxiomVerum 𝓢] : 𝓢 ⊢! ⊤ := HasAxiomVerum.verum!

omit [LogicalConnective F] in
@[simp] lemma verum [LogicalNeutral F] [HasAxiomVerum 𝓢] : 𝓢 ⊢ ⊤ := ⟨verum!⟩


class HasAxiomImplyK (𝓢 : S)  where
  implyK! {φ ψ : F} : 𝓢 ⊢! Axioms.ImplyK φ ψ
export HasAxiomImplyK (implyK!)

@[simp] lemma implyK [HasAxiomImplyK 𝓢] : 𝓢 ⊢ φ 🡒 ψ 🡒 φ := ⟨implyK!⟩

def C!_of_conseq! [ModusPonens 𝓢] [HasAxiomImplyK 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ 🡒 φ := implyK! ⨀ h
alias dhyp! := C!_of_conseq!

lemma C_of_conseq [ModusPonens 𝓢] [HasAxiomImplyK 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ 🡒 φ := ⟨C!_of_conseq! d.some⟩
alias dhyp := C_of_conseq


class HasAxiomImplyS (𝓢 : S)  where
  implyS! {φ ψ χ : F} : 𝓢 ⊢! Axioms.ImplyS φ ψ χ
export HasAxiomImplyS (implyS!)

@[simp] lemma implyS [HasAxiomImplyS 𝓢] : 𝓢 ⊢ (φ 🡒 ψ 🡒 χ) 🡒 (φ 🡒 ψ) 🡒 φ 🡒 χ := ⟨implyS!⟩


class HasAxiomAndElim (𝓢 : S)  where
  and₁! {φ ψ : F} : 𝓢 ⊢! Axioms.AndElim₁ φ ψ
  and₂! {φ ψ : F} : 𝓢 ⊢! Axioms.AndElim₂ φ ψ
export HasAxiomAndElim (and₁! and₂!)


@[simp] lemma and₁ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ 🡒 φ := ⟨and₁!⟩

def K!_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! φ := and₁! ⨀ d
@[grind ->] lemma K_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ φ := ⟨K!_left d.some⟩


@[simp] lemma and₂ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ 🡒 ψ := ⟨and₂!⟩

def K!_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ := and₂! ⨀ d
@[grind ->] lemma K_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ := ⟨K!_right d.some⟩


class HasAxiomAndInst (𝓢 : S) where
  and₃! {φ ψ : F} : 𝓢 ⊢! Axioms.AndInst φ ψ
export HasAxiomAndInst (and₃!)

@[simp] lemma and₃ [HasAxiomAndInst 𝓢] : 𝓢 ⊢ φ 🡒 ψ 🡒 φ ⋏ ψ := ⟨and₃!⟩

def K!_intro [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢! φ) (d₂: 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋏ ψ := and₃! ⨀ d₁ ⨀ d₂
@[grind <-] lemma K_intro  [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢ φ) (d₂: 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋏ ψ := ⟨K!_intro d₁.some d₂.some⟩


class HasAxiomOrInst (𝓢 : S) where
  or₁! {φ ψ : F} : 𝓢 ⊢! Axioms.OrInst₁ φ ψ
  or₂! {φ ψ : F} : 𝓢 ⊢! Axioms.OrInst₂ φ ψ
export HasAxiomOrInst (or₁! or₂!)

@[simp] lemma or₁ [HasAxiomOrInst 𝓢] : 𝓢 ⊢ φ 🡒 φ ⋎ ψ := ⟨or₁!⟩

def A!_intro_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! φ ⋎ ψ := or₁! ⨀ d
@[grind .] lemma A_intro_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ φ ⋎ ψ := ⟨A!_intro_left d.some⟩

@[simp] lemma or₂ [HasAxiomOrInst 𝓢] : 𝓢 ⊢ ψ 🡒 φ ⋎ ψ := ⟨or₂!⟩

def A!_intro_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋎ ψ := or₂! ⨀ d
@[grind .] lemma A_intro_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋎ ψ := ⟨A!_intro_right d.some⟩


class HasAxiomOrElim (𝓢 : S) where
  or₃! {φ ψ χ : F} : 𝓢 ⊢! Axioms.OrElim φ ψ χ
export HasAxiomOrElim (or₃!)

@[simp] lemma or₃ [HasAxiomOrElim 𝓢] : 𝓢 ⊢ (φ 🡒 χ) 🡒 (ψ 🡒 χ) 🡒 (φ ⋎ ψ) 🡒 χ := ⟨or₃!⟩

def left_A!_intro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ 🡒 χ) (d₂ : 𝓢 ⊢! ψ 🡒 χ) : 𝓢 ⊢! φ ⋎ ψ 🡒 χ := or₃! ⨀ d₁ ⨀ d₂
alias CA!_of_C!_of_C! := left_A!_intro

lemma left_A_intro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ 🡒 χ) (d₂ : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ φ ⋎ ψ 🡒 χ := ⟨left_A!_intro d₁.some d₂.some⟩
alias CA_of_C_of_C := left_A_intro

def of_C!_of_C!_of_A! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ 🡒 χ) (d₂ : 𝓢 ⊢! ψ 🡒 χ) (d₃ : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! χ := or₃! ⨀ d₁ ⨀ d₂ ⨀ d₃
alias A!_cases := of_C!_of_C!_of_A!

lemma of_C_of_C_of_A [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ 🡒 χ) (d₂ : 𝓢 ⊢ ψ 🡒 χ) (d₃ : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ χ := ⟨of_C!_of_C!_of_A! d₁.some d₂.some d₃.some⟩
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

def CO!_of_N! [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ → 𝓢 ⊢! φ 🡒 ⊥ := λ h => (K!_left negEquiv!) ⨀ h
def N!_of_CO! [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! φ 🡒 ⊥ → 𝓢 ⊢! ∼φ := λ h => (K!_right negEquiv!) ⨀ h
@[grind =] lemma N_iff_CO [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ ↔ 𝓢 ⊢ φ 🡒 ⊥ := ⟨λ ⟨h⟩ => ⟨CO!_of_N! h⟩, λ ⟨h⟩ => ⟨N!_of_CO! h⟩⟩


def E!_intro [HasAxiomAndInst 𝓢] (b₁ : 𝓢 ⊢! φ 🡒 ψ) (b₂ : 𝓢 ⊢! ψ 🡒 φ) : 𝓢 ⊢! φ 🡘 ψ := K!_intro b₁ b₂
@[grind ←] lemma E_intro [HasAxiomAndInst 𝓢] (h₁ : 𝓢 ⊢ φ 🡒 ψ) (h₂ : 𝓢 ⊢ ψ 🡒 φ) : 𝓢 ⊢ φ 🡘 ψ := ⟨K!_intro h₁.some h₂.some⟩

@[grind =] lemma K_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ↔ 𝓢 ⊢ φ ∧ 𝓢 ⊢ ψ := by grind
@[grind =] lemma E_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ 🡘 ψ ↔ 𝓢 ⊢ φ 🡒 ψ ∧ 𝓢 ⊢ ψ 🡒 φ := ⟨fun h ↦ ⟨K_left h, K_right h⟩, by grind⟩

def C!_of_E!_mp [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! φ 🡘 ψ) : 𝓢 ⊢! φ 🡒 ψ := K!_left h
@[grind →] lemma C_of_E_mp [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ 🡘 ψ → 𝓢 ⊢ φ 🡒 ψ := λ ⟨d⟩ => ⟨C!_of_E!_mp d⟩

def C!_of_E!_mpr [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! φ 🡘 ψ) : 𝓢 ⊢! ψ 🡒 φ := K!_right h
@[grind →] lemma C_of_E_mpr [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ 🡘 ψ → 𝓢 ⊢ ψ 🡒 φ := λ ⟨d⟩ => ⟨C!_of_E!_mpr d⟩

@[grind →] lemma iff_of_E [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ φ ↔ 𝓢 ⊢ ψ := ⟨fun hp ↦ K_left h ⨀ hp, fun hq ↦ K_right h ⨀ hq⟩

def C!_id [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] {φ : F} : 𝓢 ⊢! φ 🡒 φ := implyS! (φ := φ) (ψ := (φ 🡒 φ)) (χ := φ) ⨀ implyK! ⨀ implyK!
@[simp] theorem C_id [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ 🡒 φ := ⟨C!_id⟩

def E!_id [HasAxiomAndInst 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] {φ : F} : 𝓢 ⊢! φ 🡘 φ := K!_intro C!_id C!_id
@[simp] theorem E_id [HasAxiomAndInst 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ 🡘 φ := ⟨E!_id⟩

instance [LogicalNeutral F] [NegAbbrev F] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] [HasAxiomAndInst 𝓢] : Entailment.NegationEquiv 𝓢 where
  negEquiv! {φ} := by
    suffices 𝓢 ⊢! (φ 🡒 ⊥) 🡘 (φ 🡒 ⊥) by simpa [Axioms.NegEquiv, NegAbbrev.neg];
    apply E!_id;


def NO! [LogicalNeutral F] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! ∼⊥ := N!_of_CO! C!_id
@[simp] lemma NO [LogicalNeutral F] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ ∼⊥ := ⟨NO!⟩


def mdp₁! [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ 🡒 ψ 🡒 χ) (bq : 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! φ 🡒 χ := implyS! ⨀ bqr ⨀ bq
@[grind →] lemma mdp₁ [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ) (hq : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ φ 🡒 χ := ⟨mdp₁! hqr.some hq.some⟩

infixl:90 "⨀₁" => mdp₁!
infixl:90 "⨀₁" => mdp₁

def mdp₂! [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 s) (bq : 𝓢 ⊢! φ 🡒 ψ 🡒 χ) : 𝓢 ⊢! φ 🡒 ψ 🡒 s := C!_of_conseq! (implyS!) ⨀₁ bqr ⨀₁ bq
@[grind →] lemma mdp₂ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s) (hq : 𝓢 ⊢ φ 🡒 ψ 🡒 χ) : 𝓢 ⊢ φ 🡒 ψ 🡒 s := ⟨mdp₂! hqr.some hq.some⟩

infixl:90 "⨀₂" => mdp₂!
infixl:90 "⨀₂" => mdp₂

def mdp₃! [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 s 🡒 t) (bq : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 s) : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 t := (C!_of_conseq! <| C!_of_conseq! <| implyS!) ⨀₂ bqr ⨀₂ bq
@[grind →] lemma mdp₃ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s 🡒 t) (hq : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s) : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 t := ⟨mdp₃! hqr.some hq.some⟩

infixl:90 "⨀₃" => mdp₃!
infixl:90 "⨀₃" => mdp₃

def mdp₄! [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 s 🡒 t 🡒 u) (bq : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 s 🡒 t) : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 s 🡒 u := (C!_of_conseq! <| C!_of_conseq! <| C!_of_conseq! <| implyS!) ⨀₃ bqr ⨀₃ bq
@[grind →] lemma mdp₄ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s 🡒 t 🡒 u) (hq : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s 🡒 t) : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 s 🡒 u := ⟨mdp₄! hqr.some hq.some⟩
infixl:90 "⨀₄" => mdp₄!
infixl:90 "⨀₄" => mdp₄


def C!_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bpq : 𝓢 ⊢! φ 🡒 ψ) (bqr : 𝓢 ⊢! ψ 🡒 χ) : 𝓢 ⊢! φ 🡒 χ := implyS! ⨀ C!_of_conseq! bqr ⨀ bpq
@[grind <=] lemma C_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hpq : 𝓢 ⊢ φ 🡒 ψ) (hqr : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ φ 🡒 χ := ⟨C!_trans hpq.some hqr.some⟩

def C!_replace [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢! ψ₁ 🡒 φ₁) (h₂ : 𝓢 ⊢! φ₂ 🡒 ψ₂) : 𝓢 ⊢! φ₁ 🡒 φ₂ → 𝓢 ⊢! ψ₁ 🡒 ψ₂ := λ h => C!_trans h₁ $ C!_trans h h₂
lemma C_replace [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢ ψ₁ 🡒 φ₁) (h₂ : 𝓢 ⊢ φ₂ 🡒 ψ₂) : 𝓢 ⊢ φ₁ 🡒 φ₂ → 𝓢 ⊢ ψ₁ 🡒 ψ₂ := λ h => ⟨C!_replace h₁.some h₂.some h.some⟩

def E!_replace [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢! φ₁ 🡘 ψ₁) (h₂ : 𝓢 ⊢! φ₂ 🡘 ψ₂) (h₃ : 𝓢 ⊢! φ₁ 🡘 φ₂) : 𝓢 ⊢! ψ₁ 🡘 ψ₂ := by
  apply E!_intro;
  . exact C!_replace (C!_of_E!_mpr h₁) (C!_of_E!_mp h₂) (C!_of_E!_mp h₃);
  . exact C!_replace (C!_of_E!_mpr h₂) (C!_of_E!_mp h₁) (C!_of_E!_mpr h₃);
lemma E_replace [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ₁ 🡘 ψ₁ → 𝓢 ⊢ φ₂ 🡘 ψ₂ → 𝓢 ⊢ φ₁ 🡘 φ₂ → 𝓢 ⊢ ψ₁ 🡘 ψ₂ := λ ⟨d₁⟩ ⟨d₂⟩ ⟨d₃⟩ => ⟨E!_replace d₁ d₂ d₃⟩

def E!_trans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢! φ 🡘 ψ) (h₂ : 𝓢 ⊢! ψ 🡘 χ) : 𝓢 ⊢! φ 🡘 χ := by
  apply E!_intro;
  . exact C!_trans (K!_left h₁) (K!_left h₂);
  . exact C!_trans (K!_right h₂) (K!_right h₁);
@[grind <=]
lemma E_trans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢ φ 🡘 ψ) (h₂ : 𝓢 ⊢ ψ 🡘 χ) : 𝓢 ⊢ φ 🡘 χ := ⟨E!_trans h₁.some h₂.some⟩

def CCCC! [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! φ 🡒 ψ 🡒 χ 🡒 φ := C!_trans implyK! implyK!
@[grind .]
lemma CCCC [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ 🡒 ψ 🡒 χ 🡒 φ := ⟨CCCC!⟩

def CK!_of_C!_of_C! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bq : 𝓢 ⊢! φ 🡒 ψ) (br : 𝓢 ⊢! φ 🡒 χ)
  : 𝓢 ⊢! φ 🡒 ψ ⋏ χ := C!_of_conseq! and₃! ⨀₁ bq ⨀₁ br
@[grind <=]
lemma CK_of_C_of_C [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hq : 𝓢 ⊢ φ 🡒 ψ) (hr : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ φ 🡒 ψ ⋏ χ := ⟨CK!_of_C!_of_C! hq.some hr.some⟩


def CKK! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! φ ⋏ ψ 🡒 ψ ⋏ φ := CK!_of_C!_of_C! and₂! and₁!
@[simp, grind .] lemma CKK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ ⋏ ψ 🡒 ψ ⋏ φ := ⟨CKK!⟩

def K!_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ ⋏ φ := CKK! ⨀ h
@[grind <-] lemma K_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ ⋏ φ := ⟨K!_symm h.some⟩


def CEE! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! (φ 🡘 ψ) 🡒 (ψ 🡘 φ) := CKK!
@[simp] lemma CEE [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ (φ 🡘 ψ) 🡒 (ψ 🡘 φ) := ⟨CEE!⟩

def E!_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢! φ 🡘 ψ) : 𝓢 ⊢! ψ 🡘 φ := CEE! ⨀ h
@[grind <-] lemma E_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ ψ 🡘 φ := ⟨E!_symm h.some⟩


def ECKCC! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! (φ ⋏ ψ 🡒 χ) 🡘 (φ 🡒 ψ 🡒 χ) := by
  let b₁ : 𝓢 ⊢! (φ ⋏ ψ 🡒 χ) 🡒 φ 🡒 ψ 🡒 χ := CCCC! ⨀₃ C!_of_conseq! (ψ := φ ⋏ ψ 🡒 χ) and₃!
  let b₂ : 𝓢 ⊢! (φ 🡒 ψ 🡒 χ) 🡒 φ ⋏ ψ 🡒 χ := implyK! ⨀₂ (C!_of_conseq! (ψ := φ 🡒 ψ 🡒 χ) and₁!) ⨀₂ (C!_of_conseq! (ψ := φ 🡒 ψ 🡒 χ) and₂!);
  exact E!_intro b₁ b₂
@[simp, grind .] lemma ECKCC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ (φ ⋏ ψ 🡒 χ) 🡘 (φ 🡒 ψ 🡒 χ) := ⟨ECKCC!⟩

def CC!_of_CK! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ 🡒 χ) : 𝓢 ⊢! φ 🡒 ψ 🡒 χ := (K!_left $ ECKCC!) ⨀ d
def CK!_of_CC! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (d : 𝓢 ⊢! φ 🡒 ψ 🡒 χ) : 𝓢 ⊢! φ ⋏ ψ 🡒 χ := (K!_right $ ECKCC!) ⨀ d

@[grind =] lemma CK_iff_CC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    (𝓢 ⊢ φ ⋏ ψ 🡒 χ) ↔ (𝓢 ⊢ φ 🡒 ψ 🡒 χ) := iff_of_E ECKCC

def CV! [LogicalNeutral F] [HasAxiomVerum 𝓢] [HasAxiomImplyK 𝓢] : 𝓢 ⊢! φ 🡒 ⊤ := C!_of_conseq! verum!
@[simp] lemma CV [LogicalNeutral F] [HasAxiomImplyK 𝓢] [HasAxiomVerum 𝓢] : 𝓢 ⊢ φ 🡒 ⊤ := ⟨CV!⟩


@[grind →]
lemma unprovable_C_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hpq : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊬ φ 🡒 χ → 𝓢 ⊬ ψ 🡒 χ := by
  contrapose!;
  exact C_trans hpq;

@[grind →]
lemma uniff_of_E [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (H : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊬ φ ↔ 𝓢 ⊬ ψ := by
  constructor;
  . intro hp hq; have := K_right H ⨀ hq; contradiction;
  . intro hq hp; have := K_left H ⨀ hp; contradiction;

end


section

variable {S F : Type*} [LogicalConnective F] [LogicalNeutral F] [Entailment S F]
variable {𝓢 : S} [Entailment.Minimal 𝓢] {φ ψ χ : F}

variable {Γ Δ : List F}

def conj₂Nth! : (Γ : List F) → (n : ℕ) → (hn : n < Γ.length) → 𝓢 ⊢! ⋀Γ 🡒 Γ[n]
  |          [],     _, hn => by simp at hn
  |         [ψ],     0, _  => C!_id
  | φ :: ψ :: Γ,     0, _  => and₁!
  | φ :: ψ :: Γ, n + 1, hn => C!_trans (and₂! (φ := φ)) (conj₂Nth! (ψ :: Γ) n (Nat.succ_lt_succ_iff.mp hn))

theorem conj₂_nth (Γ : List F) (n : ℕ) (hn : n < Γ.length) : 𝓢 ⊢ ⋀Γ 🡒 Γ[n] := ⟨conj₂Nth! Γ n hn⟩

def left_Conj!_intro [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢! Γ.conj 🡒 φ :=
  match Γ with
  |     [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ
    then e ▸ and₁!
    else
      have : φ ∈ Γ := by simpa [e] using h
      C!_trans and₂! (left_Conj!_intro this)
lemma left_Conj_intro [DecidableEq F] (h : φ ∈ Γ) : 𝓢 ⊢ Γ.conj 🡒 φ := ⟨left_Conj!_intro h⟩

def Conj!_intro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) : 𝓢 ⊢! Γ.conj :=
  match Γ with
  |     [] => verum!
  | ψ :: Γ => K!_intro (b ψ (by simp)) (Conj!_intro Γ (fun ψ hq ↦ b ψ (by simp [hq])))
lemma Conj_intro {Γ : List F} (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ Γ.conj := ⟨Conj!_intro Γ λ φ hφ => (b φ hφ).some⟩

def right_Conj!_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! φ 🡒 Γ.conj :=
  match Γ with
  |     [] => C!_of_conseq! verum!
  | ψ :: Γ => CK!_of_C!_of_C! (b ψ (by simp)) (right_Conj!_intro φ Γ (fun ψ hq ↦ b ψ (by simp [hq])))
theorem right_Conj_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ φ 🡒 Γ.conj := ⟨right_Conj!_intro φ Γ fun ψ h ↦ (b ψ h).get⟩

def CConjConj! [DecidableEq F] (h : Δ ⊆ Γ) : 𝓢 ⊢! Γ.conj 🡒 Δ.conj := right_Conj!_intro _ _ (fun _ hq ↦ left_Conj!_intro (h hq))

def left_Conj₂!_intro [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ 🡒 φ :=
  have : Γ.idxOf φ < Γ.length := List.idxOf_lt_length_of_mem h
  cast <| conj₂Nth! Γ (Γ.idxOf φ) (by assumption)
lemma left_Conj₂_intro [DecidableEq F] (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ 🡒 φ := ⟨left_Conj₂!_intro h⟩

def Conj₂!_intro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) : 𝓢 ⊢! ⋀Γ :=
  match Γ with
  |          [] => verum!
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by exact K!_intro (b ψ (by simp)) (Conj₂!_intro _ (by aesop))
lemma Conj₂_intro (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ ⋀Γ := ⟨Conj₂!_intro Γ (λ φ hp => (b φ hp).some)⟩

def right_Conj₂!_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! φ 🡒 ⋀Γ :=
  match Γ with
  |          [] => C!_of_conseq! verum!
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by apply CK!_of_C!_of_C! (b ψ (by simp)) (right_Conj₂!_intro φ _ (fun ψ hq ↦ b ψ (by simp [hq])));
lemma right_Conj₂_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ φ 🡒 ⋀Γ := ⟨right_Conj₂!_intro φ Γ (λ ψ hq => (b ψ hq).some)⟩

def CConj₂Conj₂! [DecidableEq F] {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢! ⋀Γ 🡒 ⋀Δ :=
  right_Conj₂!_intro _ _ (fun _ hq ↦ left_Conj₂!_intro (h hq))
lemma CConj₂Conj₂ [DecidableEq F] {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢ ⋀Γ 🡒 ⋀Δ := ⟨CConj₂Conj₂! h⟩


section

variable {G T : Type*} [Entailment T G] [LogicalConnective G] [LogicalNeutral G] {𝓣 : T}

abbrev Minimal.ofEquiv (𝓢 : S) [Entailment.Minimal 𝓢] (𝓣 : T)
    (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢! f φ ≃ 𝓣 ⊢! φ) : Entailment.Minimal 𝓣 where
  mdp! {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢! f φ 🡒 f ψ := by simpa using (e (φ 🡒 ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  negEquiv! := e _ (by simpa using negEquiv!)
  verum! := e _ (by simpa using verum!)
  implyK! := e _ (by simpa using implyK!)
  implyS! := e _ (by simpa using implyS!)
  and₁! := e _ (by simpa using and₁!)
  and₂! := e _ (by simpa using and₂!)
  and₃! := e _ (by simpa using and₃!)
  or₁! := e _ (by simpa using or₁!)
  or₂! := e _ (by simpa using or₂!)
  or₃! := e _ (by simpa using or₃!)

end

end


section

structure FiniteContext (F) (𝓢 : S) where
  ctx : List F

namespace FiniteContext

variable {F} {S} {𝓢 : S}

instance : Coe (List F) (FiniteContext F 𝓢) := ⟨mk⟩

abbrev conj [LogicalConnective F] [LogicalNeutral F] (Γ : FiniteContext F 𝓢) : F := ⋀Γ.ctx

abbrev disj [LogicalConnective F] [LogicalNeutral F] (Γ : FiniteContext F 𝓢) : F := ⋁Γ.ctx

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

variable [Entailment S F] [LogicalConnective F] [LogicalNeutral F]

instance (𝓢 : S) : Entailment (FiniteContext F 𝓢) F := ⟨(𝓢 ⊢! ·.conj 🡒 ·)⟩

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

lemma entailment_def (Γ : FiniteContext F 𝓢) (φ : F) : (Γ ⊢! φ) = (𝓢 ⊢! Γ.conj 🡒 φ) := rfl

def ofDef! {Γ : List F} {φ : F} (b : 𝓢 ⊢! ⋀Γ 🡒 φ) : Γ ⊢[𝓢]! φ := b

def toDef! {Γ : List F} {φ : F} (b : Γ ⊢[𝓢]! φ) : 𝓢 ⊢! ⋀Γ 🡒 φ := b

lemma toₛ (b : Γ ⊢[𝓢] φ) : 𝓢 ⊢ ⋀Γ 🡒 φ := b

lemma provable_iff {φ : F} : Γ ⊢[𝓢] φ ↔ 𝓢 ⊢ ⋀Γ 🡒 φ := iff_of_eq rfl

def cast! {Γ φ} (d : Γ ⊢[𝓢]! φ) (eΓ : Γ = Γ') (eφ : φ = φ') : Γ' ⊢[𝓢]! φ' := eΓ ▸ eφ ▸ d

section

variable {Γ Δ E : List F}
variable [Entailment.Minimal 𝓢]

instance [DecidableEq F] : Axiomatized (FiniteContext F 𝓢) where
  prfAxm := fun hp ↦ left_Conj₂!_intro hp
  weakening := fun H b ↦ C!_trans (CConj₂Conj₂! H) b

instance : Compact (FiniteContext F 𝓢) where
  core := fun {Γ} _ _ ↦ Γ
  corePrf := id
  core_subset := by simp
  core_finite := by rintro ⟨Γ⟩; simp [AdjunctiveSet.Finite, AdjunctiveSet.set]

def nthAxm! {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢]! Γ[n] := conj₂Nth! Γ n h
lemma nth_axm {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢] Γ[n] := ⟨nthAxm! n h⟩

def byAxm! [DecidableEq F] {φ} (h : φ ∈ Γ := by simp) : Γ ⊢[𝓢]! φ := Axiomatized.prfAxm (by simpa)

lemma by_axm [DecidableEq F] {φ} (h : φ ∈ Γ := by simp) : Γ ⊢[𝓢] φ := Axiomatized.provable_refl _ (by simpa)

def weakening! [DecidableEq F] (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢]! φ → Δ ⊢[𝓢]! φ := Axiomatized.weakening (by simpa)

lemma weakening [DecidableEq F] (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢] φ → Δ ⊢[𝓢] φ := fun h ↦
  (Axiomatized.le_of_subset (by simpa)).subset h

def of! {φ : F} (b : 𝓢 ⊢! φ) : Γ ⊢[𝓢]! φ := C!_of_conseq! (ψ := ⋀Γ) b

def emptyPrf! {φ : F} : [] ⊢[𝓢]! φ → 𝓢 ⊢! φ := fun b ↦ b ⨀ verum!

theorem provable_iff_provable {φ : F} : 𝓢 ⊢ φ ↔ [] ⊢[𝓢] φ :=
  ⟨fun b ↦ ⟨of! b.some⟩, fun b ↦ ⟨emptyPrf! b.some⟩⟩

lemma of' [DecidableEq F] (h : 𝓢 ⊢ φ) : Γ ⊢[𝓢] φ := weakening (by simp) $ provable_iff_provable.mp h

def id! : [φ] ⊢[𝓢]! φ := nthAxm! 0
@[simp] lemma id : [φ] ⊢[𝓢] φ := nth_axm 0

def byAxm₀! : (φ :: Γ) ⊢[𝓢]! φ := nthAxm! 0
lemma by_axm₀ : (φ :: Γ) ⊢[𝓢] φ := nth_axm 0

def byAxm₁! : (φ :: ψ :: Γ) ⊢[𝓢]! ψ := nthAxm! 1
lemma by_axm₁ : (φ :: ψ :: Γ) ⊢[𝓢] ψ := nth_axm 1

def byAxm₂! : (φ :: ψ :: χ :: Γ) ⊢[𝓢]! χ := nthAxm! 2
lemma by_axm₂ : (φ :: ψ :: χ :: Γ) ⊢[𝓢] χ := nth_axm 2

instance (Γ : FiniteContext F 𝓢) : Entailment.ModusPonens Γ := ⟨mdp₁!⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomVerum Γ := ⟨of! verum!⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImplyK Γ := ⟨of! implyK!⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImplyS Γ := ⟨of! implyS!⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndElim Γ := ⟨of! and₁!, of! and₂!⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndInst Γ := ⟨of! and₃!⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrInst Γ := ⟨of! or₁!, of! or₂!⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrElim Γ := ⟨of! or₃!⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.NegationEquiv Γ := ⟨of! negEquiv!⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.Minimal Γ where


def mdp'! [DecidableEq F] (bΓ : Γ ⊢[𝓢]! φ 🡒 ψ) (bΔ : Δ ⊢[𝓢]! φ) : (Γ ++ Δ) ⊢[𝓢]! ψ :=
  wk (by simp) bΓ ⨀ wk (by simp) bΔ

def deduct! {φ ψ : F} : {Γ : List F} → (φ :: Γ) ⊢[𝓢]! ψ → Γ ⊢[𝓢]! φ 🡒 ψ
  | .nil => fun b ↦ ofDef! <| C!_of_conseq! (toDef! b)
  | .cons _ _ => fun b ↦ ofDef! <| CC!_of_CK! (C!_trans CKK! (toDef! b))

lemma deduct (h : (φ :: Γ) ⊢[𝓢] ψ) :  Γ ⊢[𝓢] φ 🡒 ψ  := ⟨FiniteContext.deduct! h.some⟩

def deductInv! {φ ψ : F} : {Γ : List F} → Γ ⊢[𝓢]! φ 🡒 ψ → (φ :: Γ) ⊢[𝓢]! ψ
  | .nil => λ b => ofDef! <| (toDef! b) ⨀ verum!
  | .cons _ _ => λ b => ofDef! <| (C!_trans CKK! (CK!_of_CC! (toDef! b)))

lemma deductInv (h : Γ ⊢[𝓢] φ 🡒 ψ) : (φ :: Γ) ⊢[𝓢] ψ := ⟨FiniteContext.deductInv! h.some⟩

lemma deduct_iff {φ ψ : F} {Γ : List F} : Γ ⊢[𝓢] φ 🡒 ψ ↔ (φ :: Γ) ⊢[𝓢] ψ :=
  ⟨fun h ↦ ⟨deductInv! h.some⟩, fun h ↦ ⟨deduct! h.some⟩⟩

def deduct'! : [φ] ⊢[𝓢]! ψ → 𝓢 ⊢! φ 🡒 ψ := fun b ↦ emptyPrf! <| deduct! b

lemma deduct' (h : [φ] ⊢[𝓢] ψ) : 𝓢 ⊢ φ 🡒 ψ := ⟨FiniteContext.deduct'! h.some⟩


def deductInv'! : 𝓢 ⊢! φ 🡒 ψ → [φ] ⊢[𝓢]! ψ := fun b ↦ deductInv! <| of! b

lemma deductInv' (h : 𝓢 ⊢ φ 🡒 ψ) : [φ] ⊢[𝓢] ψ := ⟨FiniteContext.deductInv'! h.some⟩


instance deduction : Deduction (FiniteContext F 𝓢) where
  ofInsert := deduct!
  inv := deductInv!

instance [DecidableEq F] : StrongCut (FiniteContext F 𝓢) (FiniteContext F 𝓢) :=
  ⟨fun {Γ Δ _} bΓ bΔ ↦
    have : Γ ⊢! Δ.conj := Conj₂!_intro _ (fun _ hp ↦ bΓ hp)
    ofDef! <| C!_trans (toDef! this) (toDef! bΔ)⟩

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

variable [LogicalConnective F] [LogicalNeutral F] [Entailment S F]

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
  prfAxm := fun {Γ φ} hp ↦ ⟨[φ], by simpa using hp, byAxm (by simp)⟩
  weakening := fun h b ↦ ⟨b.ctx, fun φ hp ↦ AdjunctiveSet.subset_iff.mp h φ (b.subset φ hp), b.prf⟩

def byAxm! [DecidableEq F] {Γ : Set F} {φ : F} (h : φ ∈ Γ) : Γ *⊢[𝓢]! φ := Axiomatized.prfAxm (by simpa)

instance : Compact (Context F 𝓢) where
  core := fun b ↦ AdjunctiveSet.set b.ctx
  corePrf := fun b ↦ ⟨b.ctx, by simp [AdjunctiveSet.set], b.prf⟩
  core_subset := by rintro ⟨Γ⟩ φ b; exact b.subset
  core_finite := by rintro ⟨Γ⟩; simp [AdjunctiveSet.Finite, AdjunctiveSet.set]

-- lemma provable_iff' [DecidableEq F] {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : Finset F, (↑Δ ⊆ Γ) ∧ Δ *⊢[𝓢] φ

def deduct! [DecidableEq F] {φ ψ : F} {Γ : Set F} : (insert φ Γ) *⊢[𝓢]! ψ → Γ *⊢[𝓢]! φ 🡒 ψ
  | ⟨Δ, h, b⟩ =>
    have h : ∀ ψ ∈ Δ, ψ = φ ∨ ψ ∈ Γ := by simpa using h
    let b' : (φ :: Δ.filter (· ≠ φ)) ⊢[𝓢]! ψ :=
      FiniteContext.weakening!
        (by simp [List.subset_def, List.mem_filter]; grind)
        b
    ⟨ Δ.filter (· ≠ φ), by
      intro ψ
      suffices ψ ∈ Δ → ψ ≠ φ → ψ ∈ Γ by simpa [List.mem_filter]
      intro hq ne
      rcases h ψ hq
      · contradiction
      · assumption,
      FiniteContext.deduct! b' ⟩
lemma deduct [DecidableEq F] (h : (insert φ Γ) *⊢[𝓢] ψ) : Γ *⊢[𝓢] φ 🡒 ψ := ⟨Context.deduct! h.some⟩

def deductInv! {φ ψ : F} {Γ : Set F} : Γ *⊢[𝓢]! φ 🡒 ψ → (insert φ Γ) *⊢[𝓢]! ψ
  | ⟨Δ, h, b⟩ => ⟨φ :: Δ, by simpa using fun χ hr ↦ Or.inr (h χ hr), FiniteContext.deductInv! b⟩
lemma deductInv [DecidableEq F] (h : Γ *⊢[𝓢] φ 🡒 ψ) : (insert φ Γ) *⊢[𝓢] ψ := ⟨Context.deductInv! h.some⟩

instance deduction [DecidableEq F] : Deduction (Context F 𝓢) where
  ofInsert := deduct!
  inv := deductInv!

def weakening! [DecidableEq F] (h : Γ ⊆ Δ) {φ : F} : Γ *⊢[𝓢]! φ → Δ *⊢[𝓢]! φ := Axiomatized.weakening (by simpa)
lemma weakening [DecidableEq F] (h : Γ ⊆ Δ) {φ : F} : Γ *⊢[𝓢] φ → Δ *⊢[𝓢] φ := fun h ↦ (Axiomatized.le_of_subset (by simpa)).subset h

def of! {φ : F} (b : 𝓢 ⊢! φ) : Γ *⊢[𝓢]! φ := ⟨[], by simp, FiniteContext.of! b⟩

lemma of (b : 𝓢 ⊢ φ) : Γ *⊢[𝓢] φ := ⟨Context.of! b.some⟩

def mdp! [DecidableEq F] {Γ : Set F} (bpq : Γ *⊢[𝓢]! φ 🡒 ψ) (bp : Γ *⊢[𝓢]! φ) : Γ *⊢[𝓢]! ψ :=
  ⟨ bpq.ctx ++ bp.ctx, by
    simp only [List.mem_append, mem_coe_iff]
    rintro χ (hr | hr)
    · exact bpq.subset χ hr
    · exact bp.subset χ hr,
    FiniteContext.mdp'! bpq.prf bp.prf ⟩

lemma by_axm [DecidableEq F] (h : φ ∈ Γ) : Γ *⊢[𝓢] φ := Entailment.by_axm (by simpa)

def emptyPrf! {φ : F} : ∅ *⊢[𝓢]! φ → 𝓢 ⊢! φ := by
  rintro ⟨Γ, hΓ, h⟩;
  have := List.eq_nil_iff_forall_not_mem.mpr hΓ;
  subst this;
  exact FiniteContext.emptyPrf! h;

lemma emptyPrf {φ : F} : ∅ *⊢[𝓢] φ → 𝓢 ⊢ φ := fun h ↦ ⟨emptyPrf! h.some⟩

lemma provable_iff_provable {φ : F} : 𝓢 ⊢ φ ↔ ∅ *⊢[𝓢] φ := ⟨of, emptyPrf⟩

lemma iff_provable_context_provable_finiteContext_toList [DecidableEq F] {Δ : Finset F} : ↑Δ *⊢[𝓢] φ ↔ Δ.toList ⊢[𝓢] φ := by
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply FiniteContext.weakening ?_ hΓ₂;
    intro ψ hψ;
    simpa using hΓ₁ ψ hψ;
  . intro h;
    apply Context.provable_iff.mpr;
    use Δ.toList;
    constructor;
    . simp only [Finset.mem_toList, SetLike.mem_coe];
      tauto;
    . assumption;

instance minimal [DecidableEq F] (Γ : Context F 𝓢) : Entailment.Minimal Γ where
  mdp! := mdp!
  verum! := of! verum!
  implyK! := of! implyK!
  implyS! := of! implyS!
  and₁! := of! and₁!
  and₂! := of! and₂!
  and₃! := of! and₃!
  or₁! := of! or₁!
  or₂! := of! or₂!
  or₃! := of! or₃!
  negEquiv! := of! negEquiv!

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

def innerMDP! [DecidableEq F] : 𝓢 ⊢! φ ⋏ (φ 🡒 ψ) 🡒 ψ := by
  apply deduct'!;
  have hp  : [φ, φ 🡒 ψ] ⊢[𝓢]! φ := FiniteContext.byAxm!;
  have hpq : [φ, φ 🡒 ψ] ⊢[𝓢]! φ 🡒 ψ := FiniteContext.byAxm!;
  exact hpq ⨀ hp;
lemma inner_mdp [DecidableEq F] : 𝓢 ⊢ φ ⋏ (φ 🡒 ψ) 🡒 ψ := ⟨innerMDP!⟩

def bot_of_mem_either! [DecidableEq F] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ⊥ := by
  have hp : Γ ⊢[𝓢]! φ := FiniteContext.byAxm! h₁;
  have hnp : Γ ⊢[𝓢]! φ 🡒 ⊥ := CO!_of_N! $ FiniteContext.byAxm! h₂;
  exact hnp ⨀ hp
lemma bot_of_mem_either [DecidableEq F] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ⊥ := ⟨bot_of_mem_either! h₁ h₂⟩

def negMDP! (hnp : 𝓢 ⊢! ∼φ) (hn : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊥ := (CO!_of_N! hnp) ⨀ hn
lemma neg_mdp (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ := ⟨negMDP! hnp.some hn.some⟩


def right_A!_intro_left (h : 𝓢 ⊢! φ 🡒 χ) : 𝓢 ⊢! φ 🡒 (χ ⋎ ψ) := by
  apply deduct'!;
  apply A!_intro_left;
  apply deductInv!;
  exact of! h;
lemma right_A_intro_left (h : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ φ 🡒 (χ ⋎ ψ) := ⟨right_A!_intro_left h.some⟩

def right_A!_intro_right (h : 𝓢 ⊢! ψ 🡒 χ) : 𝓢 ⊢! ψ 🡒 (φ ⋎ χ) := by
  apply deduct'!;
  apply A!_intro_right;
  apply deductInv!;
  exact of! h;
lemma right_A_intro_right (h : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ ψ 🡒 (φ ⋎ χ) := ⟨right_A!_intro_right h.some⟩


def right_K!_intro [DecidableEq F] (hq : 𝓢 ⊢! φ 🡒 ψ) (hr : 𝓢 ⊢! φ 🡒 χ) : 𝓢 ⊢! φ 🡒 ψ ⋏ χ := by
  apply deduct'!;
  replace hq : [] ⊢[𝓢]! φ 🡒 ψ := of! hq;
  replace hr : [] ⊢[𝓢]! φ 🡒 χ := of! hr;
  exact K!_intro (mdp'! hq FiniteContext.id!) (mdp'! hr FiniteContext.id!)
lemma right_K_intro [DecidableEq F] (hq : 𝓢 ⊢ φ 🡒 ψ) (hr : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ φ 🡒 ψ ⋏ χ := ⟨right_K!_intro hq.some hr.some⟩

lemma left_K_symm (d : 𝓢 ⊢ φ ⋏ ψ 🡒 χ) : 𝓢 ⊢ ψ ⋏ φ 🡒 χ := C_trans CKK d


lemma left_K_intro_right [DecidableEq F] (h : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ (ψ ⋏ φ) 🡒 χ := by
  apply CK_iff_CC.mpr;
  apply deduct';
  exact FiniteContext.of' (Γ := [ψ]) h;


lemma left_K_intro_left [DecidableEq F] (h : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ (φ ⋏ ψ) 🡒 χ := C_trans CKK (left_K_intro_right h)


lemma cut [DecidableEq F] (d₁ : 𝓢 ⊢ φ₁ ⋏ c 🡒 ψ₁) (d₂ : 𝓢 ⊢ φ₂ 🡒 c ⋎ ψ₂) : 𝓢 ⊢ φ₁ ⋏ φ₂ 🡒 ψ₁ ⋎ ψ₂ := by
  apply deduct';
  exact of_C_of_C_of_A (right_A_intro_left $ of' (CK_iff_CC.mp d₁) ⨀ (K_left id)) or₂ (of' d₂ ⨀ K_right id);


def CAA! : 𝓢 ⊢! φ ⋎ ψ 🡒 ψ ⋎ φ := by
  apply deduct'!;
  exact of_C!_of_C!_of_A! or₂! or₁! $ FiniteContext.id!
lemma CAA : 𝓢 ⊢ φ ⋎ ψ 🡒 ψ ⋎ φ := ⟨CAA!⟩

def A!_symm (h : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ψ ⋎ φ := CAA! ⨀ h
lemma A_symm (h : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ψ ⋎ φ := ⟨A!_symm h.some⟩



lemma A_assoc : 𝓢 ⊢ φ ⋎ (ψ ⋎ χ) ↔ 𝓢 ⊢ (φ ⋎ ψ) ⋎ χ := by
  constructor;
  . intro h;
    exact of_C_of_C_of_A
      (right_A_intro_left $ right_A_intro_left C_id)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact of_C_of_C_of_A (right_A_intro_left $ right_A_intro_right C_id) (right_A_intro_right C_id) id;
      )
      h;
  . intro h;
    exact of_C_of_C_of_A
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact of_C_of_C_of_A (right_A_intro_left C_id) (right_A_intro_right $ right_A_intro_left C_id) id;
      )
      (right_A_intro_right $ right_A_intro_right C_id)
      h;



lemma K_assoc : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ 🡘 φ ⋏ (ψ ⋏ χ) := by
  apply E_intro;
  . apply FiniteContext.deduct';
    have hp : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] φ := K_left $ K_left id;
    have hq : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] ψ := K_right $ K_left id;
    have hr : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] χ := K_right id;
    exact K_intro hp (K_intro hq hr);
  . apply FiniteContext.deduct';
    have hp : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] φ := K_left id;
    have hq : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] ψ := K_left $ K_right id;
    have hr : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] χ := K_right $ K_right id;
    apply K_intro;
    . exact K_intro hp hq;
    . exact hr;

lemma K_assoc_mp (h : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ) : 𝓢 ⊢ φ ⋏ (ψ ⋏ χ) := C_of_E_mp K_assoc ⨀ h
lemma K_assoc_mpr (h : 𝓢 ⊢ φ ⋏ (ψ ⋏ χ)) : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ := C_of_E_mpr K_assoc ⨀ h

def K!_replace_left (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! φ 🡒 χ) : 𝓢 ⊢! χ ⋏ ψ := K!_intro (h ⨀ K!_left hc) (K!_right hc)
lemma K_replace_left (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ χ ⋏ ψ := ⟨K!_replace_left hc.some h.some⟩


def CKK!_of_C! (h : 𝓢 ⊢! φ 🡒 χ) : 𝓢 ⊢! φ ⋏ ψ 🡒 χ ⋏ ψ := by
  apply deduct'!;
  exact K!_replace_left FiniteContext.id! (of! h)
lemma CKK_of_C (h : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ φ ⋏ ψ 🡒 χ ⋏ ψ := ⟨CKK!_of_C! h.some⟩


def K!_replace_right (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! ψ 🡒 χ) : 𝓢 ⊢! φ ⋏ χ := K!_intro (K!_left hc) (h ⨀ K!_right hc)
lemma K_replace_right (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ φ ⋏ χ := ⟨K!_replace_right hc.some h.some⟩

def CKK!_of_C!' (h : 𝓢 ⊢! ψ 🡒 χ) : 𝓢 ⊢! φ ⋏ ψ 🡒 φ ⋏ χ := by
  apply deduct'!;
  exact K!_replace_right (FiniteContext.id!) (of! h)
lemma CKK_of_C' (h : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ φ ⋏ ψ 🡒 φ ⋏ χ := ⟨CKK!_of_C!' h.some⟩

def K!_replace (hc : 𝓢 ⊢! φ ⋏ ψ) (h₁ : 𝓢 ⊢! φ 🡒 χ) (h₂ : 𝓢 ⊢! ψ 🡒 ξ) : 𝓢 ⊢! χ ⋏ ξ := K!_replace_right (K!_replace_left hc h₁) h₂
lemma K_replace (hc : 𝓢 ⊢ φ ⋏ ψ) (h₁ : 𝓢 ⊢ φ 🡒 χ) (h₂ : 𝓢 ⊢ ψ 🡒 ξ) : 𝓢 ⊢ χ ⋏ ξ := ⟨K!_replace hc.some h₁.some h₂.some⟩

def CKK!_of_C!_of_C! (h₁ : 𝓢 ⊢! φ 🡒 χ) (h₂ : 𝓢 ⊢! ψ 🡒 ξ) : 𝓢 ⊢! φ ⋏ ψ 🡒 χ ⋏ ξ := by
  apply deduct'!;
  exact K!_replace FiniteContext.id! (of! h₁) (of! h₂)
lemma CKK_of_C_of_C (h₁ : 𝓢 ⊢ φ 🡒 χ) (h₂ : 𝓢 ⊢ ψ 🡒 ξ) : 𝓢 ⊢ φ ⋏ ψ 🡒 χ ⋏ ξ := ⟨CKK!_of_C!_of_C! h₁.some h₂.some⟩

def A!_replace_left (hc : 𝓢 ⊢! φ ⋎ ψ) (hp : 𝓢 ⊢! φ 🡒 χ) : 𝓢 ⊢! χ ⋎ ψ := of_C!_of_C!_of_A! (C!_trans hp or₁!) (or₂!) hc
lemma A_replace_left (hc : 𝓢 ⊢ φ ⋎ ψ) (hp : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ χ ⋎ ψ := ⟨A!_replace_left hc.some hp.some⟩

def CAA!_of_C!_left (hp : 𝓢 ⊢! φ 🡒 χ) : 𝓢 ⊢! φ ⋎ ψ 🡒 χ ⋎ ψ := by
  apply deduct'!;
  exact A!_replace_left FiniteContext.id! (of! hp)
lemma CAA_of_C_left (hp : 𝓢 ⊢ φ 🡒 χ) : 𝓢 ⊢ φ ⋎ ψ 🡒 χ ⋎ ψ := ⟨CAA!_of_C!_left hp.some⟩

def A!_replace_right (hc : 𝓢 ⊢! φ ⋎ ψ) (hq : 𝓢 ⊢! ψ 🡒 χ) : 𝓢 ⊢! φ ⋎ χ := of_C!_of_C!_of_A! (or₁!) (C!_trans hq or₂!) hc
lemma A_replace_right (hc : 𝓢 ⊢ φ ⋎ ψ) (hq : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ φ ⋎ χ := ⟨A!_replace_right hc.some hq.some⟩

def CAA!_of_C!_right (hq : 𝓢 ⊢! ψ 🡒 χ) : 𝓢 ⊢! φ ⋎ ψ 🡒 φ ⋎ χ := by
  apply deduct'!;
  exact A!_replace_right FiniteContext.id! (of! hq)
lemma CAA_of_C_right (hq : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ φ ⋎ ψ 🡒 φ ⋎ χ := ⟨CAA!_of_C!_right hq.some⟩

def A!_replace (h : 𝓢 ⊢! φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢! φ₁ 🡒 φ₂) (hq : 𝓢 ⊢! ψ₁ 🡒 ψ₂) : 𝓢 ⊢! φ₂ ⋎ ψ₂ := A!_replace_right (A!_replace_left h hp) hq
lemma A_replace (h : 𝓢 ⊢ φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢ φ₁ 🡒 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡒 ψ₂) : 𝓢 ⊢ φ₂ ⋎ ψ₂ := ⟨A!_replace h.some hp.some hq.some⟩

def CAA!_of_C!_of_C! (hp : 𝓢 ⊢! φ₁ 🡒 φ₂) (hq : 𝓢 ⊢! ψ₁ 🡒 ψ₂) : 𝓢 ⊢! φ₁ ⋎ ψ₁ 🡒 φ₂ ⋎ ψ₂ := by
  apply deduct'!;
  exact A!_replace FiniteContext.id! (of! hp) (of! hq) ;
lemma CAA_of_C_of_C (hp : 𝓢 ⊢ φ₁ 🡒 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡒 ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ 🡒 φ₂ ⋎ ψ₂ := ⟨CAA!_of_C!_of_C! hp.some hq.some⟩

def EAA!_of_E!_of_E! (hp : 𝓢 ⊢! φ₁ 🡘 φ₂) (hq : 𝓢 ⊢! ψ₁ 🡘 ψ₂) : 𝓢 ⊢! φ₁ ⋎ ψ₁ 🡘 φ₂ ⋎ ψ₂ := by
  apply E!_intro;
  . exact CAA!_of_C!_of_C! (K!_left hp) (K!_left hq);
  . exact CAA!_of_C!_of_C! (K!_right hp) (K!_right hq);
lemma EAA_of_E_of_E (hp : 𝓢 ⊢ φ₁ 🡘 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡘 ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ 🡘 φ₂ ⋎ ψ₂ := ⟨EAA!_of_E!_of_E! hp.some hq.some⟩


lemma EAAAA : 𝓢 ⊢ φ ⋎ (ψ ⋎ χ) 🡘 (φ ⋎ ψ) ⋎ χ := by
  apply E_intro;
  . exact deduct' $ A_assoc.mp id;
  . exact deduct' $ A_assoc.mpr id;


lemma EAA_of_E_right (d : 𝓢 ⊢ ψ 🡘 χ) : 𝓢 ⊢ φ ⋎ ψ 🡘 φ ⋎ χ := by
  apply E_intro;
  . apply CAA_of_C_right; exact K_left d;
  . apply CAA_of_C_right; exact K_right d;


lemma EAA_of_E_left (d : 𝓢 ⊢ φ 🡘 χ) : 𝓢 ⊢ φ ⋎ ψ 🡘 χ ⋎ ψ := by
  apply E_intro;
  . apply CAA_of_C_left; exact K_left d;
  . apply CAA_of_C_left; exact K_right d;


def EKK!_of_E!_of_E! (hp : 𝓢 ⊢! φ₁ 🡘 φ₂) (hq : 𝓢 ⊢! ψ₁ 🡘 ψ₂) : 𝓢 ⊢! φ₁ ⋏ ψ₁ 🡘 φ₂ ⋏ ψ₂ := by
  apply E!_intro;
  . exact CKK!_of_C!_of_C! (K!_left hp) (K!_left hq);
  . exact CKK!_of_C!_of_C! (K!_right hp) (K!_right hq);
lemma EKK_of_E_of_E (hp : 𝓢 ⊢ φ₁ 🡘 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡘 ψ₂) : 𝓢 ⊢ φ₁ ⋏ ψ₁ 🡘 φ₂ ⋏ ψ₂ := ⟨EKK!_of_E!_of_E! hp.some hq.some⟩

def ECC!_of_E!_of_E! (hp : 𝓢 ⊢! φ₁ 🡘 φ₂) (hq : 𝓢 ⊢! ψ₁ 🡘 ψ₂) : 𝓢 ⊢! (φ₁ 🡒 ψ₁) 🡘 (φ₂ 🡒 ψ₂) := by
  apply E!_intro;
  . apply deduct'!; exact C!_trans (of! $ K!_right hp) $ C!_trans (FiniteContext.id!) (of! $ K!_left hq);
  . apply deduct'!; exact C!_trans (of! $ K!_left hp) $ C!_trans (FiniteContext.id!) (of! $ K!_right hq);
lemma ECC_of_E_of_E (hp : 𝓢 ⊢ φ₁ 🡘 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡘 ψ₂) : 𝓢 ⊢ (φ₁ 🡒 ψ₁) 🡘 (φ₂ 🡒 ψ₂) := ⟨ECC!_of_E!_of_E! hp.some hq.some⟩


lemma C_iff_C_of_E_of_E [DecidableEq F] (hp : 𝓢 ⊢ φ₁ 🡘 φ₂) (hq : 𝓢 ⊢ ψ₁ 🡘 ψ₂) : 𝓢 ⊢ φ₁ 🡒 ψ₁ ↔ 𝓢 ⊢ φ₂ 🡒 ψ₂ :=
  iff_of_E (ECC_of_E_of_E hp hq)

def dni! [DecidableEq F] : 𝓢 ⊢! φ 🡒 ∼∼φ := by
  apply deduct'!;
  apply N!_of_CO!;
  apply deduct!;
  exact bot_of_mem_either! (φ := φ) (by simp) (by simp);
@[simp] lemma dni [DecidableEq F] : 𝓢 ⊢ φ 🡒 ∼∼φ := ⟨dni!⟩

def dni'! [DecidableEq F] (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼∼φ := dni! ⨀ b
lemma dni' [DecidableEq F] (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ∼∼φ := ⟨dni'! b.some⟩

def ANNNN!_of_A! [DecidableEq F] (d : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ := of_C!_of_C!_of_A! (C!_trans dni! or₁!) (C!_trans dni! or₂!) d
lemma ANNNN_of_A [DecidableEq F] (d : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ := ⟨ANNNN!_of_A! d.some⟩

def KNNNN!_of_K! [DecidableEq F] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ∼∼φ ⋏ ∼∼ψ := K!_intro (dni'! $ K!_left d) (dni'! $ K!_right d)
lemma KNNNN_of_K [DecidableEq F] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ∼∼φ ⋏ ∼∼ψ := ⟨KNNNN!_of_K! d.some⟩

def CNNOO! : 𝓢 ⊢! ∼∼⊥ 🡒 ⊥ := by
  apply deduct'!
  have d₁ : [∼∼⊥] ⊢[𝓢]! ∼⊥ 🡒 ⊥ := CO!_of_N! byAxm₀!
  have d₂ : [∼∼⊥] ⊢[𝓢]! ∼⊥ := N!_of_CO! C!_id
  exact d₁ ⨀ d₂

def ENNOO! [DecidableEq F] : 𝓢 ⊢! ∼∼⊥ 🡘 ⊥ := K!_intro CNNOO! dni!


def CCCNN! [DecidableEq F] : 𝓢 ⊢! (φ 🡒 ψ) 🡒 (∼ψ 🡒 ∼φ) := by
  apply deduct'!;
  apply deduct!;
  apply N!_of_CO!;
  apply deduct!;
  have dp  : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢]! φ := FiniteContext.byAxm!;
  have dpq : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢]! φ 🡒 ψ := FiniteContext.byAxm!;
  have dq  : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢]! ψ := dpq ⨀ dp;
  have dnq : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢]! ψ 🡒 ⊥ := CO!_of_N! $ FiniteContext.byAxm!;
  exact dnq ⨀ dq;
@[simp] theorem CCCNN [DecidableEq F] : 𝓢 ⊢ (φ 🡒 ψ) 🡒 (∼ψ 🡒 ∼φ) := ⟨CCCNN!⟩

@[deprecated "use `CCCNN!`" (since := "2026-07-20")] alias contra₀! := CCCNN!
@[deprecated "use `CCCNN`" (since := "2026-07-20")] alias contra₀ := CCCNN

def contra! [DecidableEq F] (b : 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! ∼ψ 🡒 ∼φ := CCCNN! ⨀ b
lemma contra [DecidableEq F] (b : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ ∼ψ 🡒 ∼φ := ⟨contra! b.some⟩

@[deprecated "use `contra!`" (since := "2026-07-20")] alias contra₀'! := contra!
@[deprecated "use `contra`" (since := "2026-07-20")] alias contra₀' := contra

def CNNNN!_of_C! [DecidableEq F] (b : 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! ∼∼φ 🡒 ∼∼ψ := contra! $ contra! b
@[grind <=] lemma CNNNN_of_C [DecidableEq F] (b : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ ∼∼φ 🡒 ∼∼ψ := ⟨CNNNN!_of_C! b.some⟩

def CCCNNNN! [DecidableEq F] : 𝓢 ⊢! (φ 🡒 ψ) 🡒 (∼∼φ 🡒 ∼∼ψ) := deduct'! $ CNNNN!_of_C! FiniteContext.id!
@[simp] lemma CCCNNNN [DecidableEq F] : 𝓢 ⊢ (φ 🡒 ψ) 🡒 (∼∼φ 🡒 ∼∼ψ) := ⟨CCCNNNN!⟩


def CN!_of_CN!_right [DecidableEq F] (b : 𝓢 ⊢! φ 🡒 ∼ψ) : 𝓢 ⊢! ψ 🡒 ∼φ := C!_trans dni! (contra! b)
lemma CN_of_CN_right [DecidableEq F] (b : 𝓢 ⊢ φ 🡒 ∼ψ) : 𝓢 ⊢ ψ 🡒 ∼φ := ⟨CN!_of_CN!_right b.some⟩

def CCNCN! [DecidableEq F] : 𝓢 ⊢! (φ 🡒 ∼ψ) 🡒 (ψ 🡒 ∼φ) := deduct'! $ CN!_of_CN!_right FiniteContext.id!
lemma CCNCN [DecidableEq F] : 𝓢 ⊢ (φ 🡒 ∼ψ) 🡒 (ψ 🡒 ∼φ) := ⟨CCNCN!⟩

def ENN!_of_E! [DecidableEq F] (b : 𝓢 ⊢! φ 🡘 ψ) : 𝓢 ⊢! ∼φ 🡘 ∼ψ := E!_intro (contra! $ K!_right b) (contra! $ K!_left b)
lemma ENN_of_E [DecidableEq F] (b : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ ∼φ 🡘 ∼ψ := ⟨ENN!_of_E! b.some⟩


section NegationEquiv

def ENNCCOO! [DecidableEq F] : 𝓢 ⊢! ∼∼φ 🡘 ((φ 🡒 ⊥) 🡒 ⊥) := by
  apply E!_intro;
  . exact C!_trans (by apply contra!; exact K!_right negEquiv!) (K!_left negEquiv!)
  . exact C!_trans (K!_right negEquiv!) (by apply contra!; exact K!_left negEquiv!)
@[simp] lemma ENNCCOO [DecidableEq F] : 𝓢 ⊢ ∼∼φ 🡘 ((φ 🡒 ⊥) 🡒 ⊥) := ⟨ENNCCOO!⟩

end NegationEquiv


def tne! [DecidableEq F] : 𝓢 ⊢! ∼(∼∼φ) 🡒 ∼φ := contra! dni!
@[simp] lemma tne [DecidableEq F] : 𝓢 ⊢ ∼(∼∼φ) 🡒 ∼φ := ⟨tne!⟩

def tne'! [DecidableEq F] (b : 𝓢 ⊢! ∼(∼∼φ)) : 𝓢 ⊢! ∼φ := tne! ⨀ b
lemma tne' [DecidableEq F] (b : 𝓢 ⊢ ∼(∼∼φ)) : 𝓢 ⊢ ∼φ := ⟨tne'! b.some⟩

def tneIff! [DecidableEq F] : 𝓢 ⊢! ∼∼∼φ 🡘 ∼φ := K!_intro tne! dni!

def CCC!_of_C!_left (h : 𝓢 ⊢! ψ 🡒 φ) : 𝓢 ⊢! (φ 🡒 χ) 🡒 (ψ 🡒 χ) := by
  apply deduct'!;
  exact C!_trans (of! h) id!;
lemma CCC_of_C_left (h : 𝓢 ⊢ ψ 🡒 φ) : 𝓢 ⊢ (φ 🡒 χ) 🡒 (ψ 🡒 χ) := ⟨CCC!_of_C!_left h.some⟩

@[deprecated "use `CCC!_of_C!_left`" (since := "2026-07-20")] alias rev_dhyp_imp'! := CCC!_of_C!_left
@[deprecated "use `CCC_of_C_left`" (since := "2026-07-20")] alias rev_dhyp_imp' := CCC_of_C_left

lemma C_iff_C_of_iff_left (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ φ 🡒 χ ↔ 𝓢 ⊢ ψ 🡒 χ := by
  constructor;
  . exact C_trans $ K_right h;
  . exact C_trans $ K_left h;

lemma C_iff_C_of_iff_right (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ χ 🡒 φ ↔ 𝓢 ⊢ χ 🡒 ψ := by
  constructor;
  . intro hrp; exact C_trans hrp $ K_left h;
  . intro hrq; exact C_trans hrq $ K_right h;

def C!_swap [DecidableEq F] (h : 𝓢 ⊢! φ 🡒 ψ 🡒 χ) : 𝓢 ⊢! ψ 🡒 φ 🡒 χ := by
  apply deduct'!;
  apply deduct!;
  exact (of! (Γ := [φ, ψ]) h) ⨀ FiniteContext.byAxm! ⨀ FiniteContext.byAxm!;
lemma C_swap [DecidableEq F] (h : 𝓢 ⊢ (φ 🡒 ψ 🡒 χ)) : 𝓢 ⊢ (ψ 🡒 φ 🡒 χ) := ⟨C!_swap h.some⟩

def CCCCC! [DecidableEq F] : 𝓢 ⊢! (φ 🡒 ψ 🡒 χ) 🡒 (ψ 🡒 φ 🡒 χ) := deduct'! $ C!_swap FiniteContext.id!
@[simp] lemma CCCCC [DecidableEq F] : 𝓢 ⊢ (φ 🡒 ψ 🡒 χ) 🡒 (ψ 🡒 φ 🡒 χ) := ⟨CCCCC!⟩

def C!_of_CC! [DecidableEq F] (h : 𝓢 ⊢! φ 🡒 φ 🡒 ψ) : 𝓢 ⊢! φ 🡒 ψ := by
  apply deduct'!;
  have := of! (Γ := [φ]) h;
  exact this ⨀ (FiniteContext.byAxm!) ⨀ (FiniteContext.byAxm!);
lemma C_of_CC [DecidableEq F] (h : 𝓢 ⊢ φ 🡒 φ 🡒 ψ) : 𝓢 ⊢ φ 🡒 ψ := ⟨C!_of_CC! h.some⟩

def CCC! [DecidableEq F] : 𝓢 ⊢! φ 🡒 (φ 🡒 ψ) 🡒 ψ := C!_swap $ C!_id
lemma CCC [DecidableEq F] : 𝓢 ⊢ φ 🡒 (φ 🡒 ψ) 🡒 ψ := ⟨CCC!⟩

def CCC!_of_C!_right (h : 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! (χ 🡒 φ) 🡒 (χ 🡒 ψ) := implyS! ⨀ (C!_of_conseq! h)
lemma CCC_of_C_right (h : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ (χ 🡒 φ) 🡒 (χ 🡒 ψ) := ⟨CCC!_of_C!_right h.some⟩

def CNNCCNNNN! [DecidableEq F] : 𝓢 ⊢! ∼∼(φ 🡒 ψ) 🡒 (∼∼φ 🡒 ∼∼ψ) := by
  apply C!_swap;
  apply deduct'!;
  exact C!_trans (CNNNN!_of_C! $ deductInv! $ of! $ C!_swap $ CCCNNNN!) tne!;
@[simp] lemma CNNCCNNNN [DecidableEq F] : 𝓢 ⊢ ∼∼(φ 🡒 ψ) 🡒 (∼∼φ 🡒 ∼∼ψ) := ⟨CNNCCNNNN!⟩

def CNNNN!_of_NNC! [DecidableEq F] (b : 𝓢 ⊢! ∼∼(φ 🡒 ψ)) : 𝓢 ⊢! ∼∼φ 🡒 ∼∼ψ := CNNCCNNNN! ⨀ b
lemma CNNNN_of_NNC [DecidableEq F] (b : 𝓢 ⊢ ∼∼(φ 🡒 ψ)) : 𝓢 ⊢ ∼∼φ 🡒 ∼∼ψ := ⟨CNNNN!_of_NNC! b.some⟩

def O!_intro_of_KN! (h : 𝓢 ⊢! φ ⋏ ∼φ) : 𝓢 ⊢! ⊥ := (CO!_of_N! $ K!_right h) ⨀ (K!_left h)
lemma O_intro_of_KN (h : 𝓢 ⊢ φ ⋏ ∼φ) : 𝓢 ⊢ ⊥ := ⟨O!_intro_of_KN! h.some⟩
/-- Law of contradiction -/
alias lac' := O_intro_of_KN

def CKNO! : 𝓢 ⊢! φ ⋏ ∼φ 🡒 ⊥ := by
  apply deduct'!;
  exact O!_intro_of_KN! (φ := φ) $ FiniteContext.id!
@[simp] lemma CKNO : 𝓢 ⊢ φ ⋏ ∼φ 🡒 ⊥ := ⟨CKNO!⟩
/-- Law of contradiction -/
alias lac := CKNO

def CANNNK! [DecidableEq F] : 𝓢 ⊢! (∼φ ⋎ ∼ψ) 🡒 ∼(φ ⋏ ψ) := left_A!_intro (contra! and₁!) (contra! and₂!)
@[simp] lemma CANNNK [DecidableEq F] : 𝓢 ⊢ (∼φ ⋎ ∼ψ) 🡒 ∼(φ ⋏ ψ) := ⟨CANNNK!⟩

def NK!_of_ANN! [DecidableEq F] (d : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! ∼(φ ⋏ ψ)  := CANNNK! ⨀ d
lemma NK_of_ANN [DecidableEq F] (d : 𝓢 ⊢ ∼φ ⋎ ∼ψ) : 𝓢 ⊢ ∼(φ ⋏ ψ) := ⟨NK!_of_ANN! d.some⟩

def CKNNNA! [DecidableEq F] : 𝓢 ⊢! (∼φ ⋏ ∼ψ) 🡒 ∼(φ ⋎ ψ) := by
  apply CK!_of_CC!;
  apply deduct'!;
  apply deduct!;
  apply N!_of_CO!;
  apply deduct!;
  exact of_C!_of_C!_of_A! (CO!_of_N! FiniteContext.byAxm!) (CO!_of_N! FiniteContext.byAxm!) (FiniteContext.byAxm! (φ := φ ⋎ ψ));
@[simp] lemma CKNNNA [DecidableEq F] : 𝓢 ⊢ ∼φ ⋏ ∼ψ 🡒 ∼(φ ⋎ ψ) := ⟨CKNNNA!⟩

def NA!_of_KNN! [DecidableEq F] (d : 𝓢 ⊢! ∼φ ⋏ ∼ψ) : 𝓢 ⊢! ∼(φ ⋎ ψ) := CKNNNA! ⨀ d
lemma NA_of_KNN [DecidableEq F] (d : 𝓢 ⊢ ∼φ ⋏ ∼ψ) : 𝓢 ⊢ ∼(φ ⋎ ψ) := ⟨NA!_of_KNN! d.some⟩


def CNAKNN! [DecidableEq F] : 𝓢 ⊢! ∼(φ ⋎ ψ) 🡒 (∼φ ⋏ ∼ψ) := by
  apply deduct'!;
  exact K!_intro (deductInv! $ contra! $ or₁!) (deductInv! $ contra! $ or₂!)
@[simp] lemma CNAKNN [DecidableEq F] : 𝓢 ⊢ ∼(φ ⋎ ψ) 🡒 (∼φ ⋏ ∼ψ) := ⟨CNAKNN!⟩

def KNN!_of_NA! [DecidableEq F] (b : 𝓢 ⊢! ∼(φ ⋎ ψ)) : 𝓢 ⊢! ∼φ ⋏ ∼ψ := CNAKNN! ⨀ b
lemma KNN_of_NA [DecidableEq F] (b : 𝓢 ⊢ ∼(φ ⋎ ψ)) : 𝓢 ⊢ ∼φ ⋏ ∼ψ := ⟨KNN!_of_NA! b.some⟩




section Conjunction

def EConj₂Conj! : (Γ : List F) → 𝓢 ⊢! ⋀Γ 🡘 Γ.conj
  | []          => E!_id
  | [_]         => E!_intro (deduct'! <| K!_intro FiniteContext.id! verum!) and₁!
  | _ :: ψ :: Γ => EKK!_of_E!_of_E! (E!_id) (EConj₂Conj! (ψ :: Γ))
@[simp] lemma EConj₂Conj : 𝓢 ⊢ ⋀Γ 🡘 Γ.conj := ⟨EConj₂Conj! Γ⟩

lemma CConj_iff_CConj₂ : 𝓢 ⊢ Γ.conj 🡒 φ ↔ 𝓢 ⊢ ⋀Γ 🡒 φ := C_iff_C_of_iff_left $ E_symm EConj₂Conj

/--! note: It may be easier to handle define `List.conj` based on `List.conj' (?)`  -/
def right_Conj'!_intro [DecidableEq F] (φ : F) (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢! φ 🡒 ψ i) : 𝓢 ⊢! φ 🡒 l.conj' ψ :=
  right_Conj₂!_intro φ (l.map ψ) fun χ h ↦
    let ⟨i, hi, e⟩ := l.chooseX (fun i ↦ ψ i = χ) (by simpa using h)
    e ▸ (b i hi)
lemma right_Conj'_intro [DecidableEq F] (φ : F) (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢ φ 🡒 ψ i) : 𝓢 ⊢ φ 🡒 l.conj' ψ :=
  ⟨right_Conj'!_intro φ l ψ fun i hi ↦ (b i hi).get⟩

def left_Conj'!_intro [DecidableEq F] {l : List ι} (h : i ∈ l) (φ : ι → F) : 𝓢 ⊢! l.conj' φ 🡒 φ i :=
  left_Conj₂!_intro (by simp only [mem_map]; use i)
lemma left_Conj'_intro [DecidableEq F] {l : List ι} (h : i ∈ l) (φ : ι → F) : 𝓢 ⊢ l.conj' φ 🡒 φ i := ⟨left_Conj'!_intro h φ⟩


lemma right_Fconj_intro (φ : F) (s : Finset F) (b : (ψ : F) → ψ ∈ s → 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ φ 🡒 s.conj :=
  right_Conj₂_intro φ s.toList fun ψ hψ ↦ b ψ (by simpa using hψ)

lemma left_Fconj_intro [DecidableEq F] {s : Finset F} (h : φ ∈ s) : 𝓢 ⊢ s.conj 🡒 φ := left_Conj₂_intro <| by simp [h]

lemma right_Fconj'_intro [DecidableEq F] (φ : F) (s : Finset ι) (ψ : ι → F) (b : ∀ i ∈ s, 𝓢 ⊢ φ 🡒 ψ i) :
    𝓢 ⊢ φ 🡒 ⩕ i ∈ s, ψ i := right_Conj'_intro φ s.toList ψ (by simpa)

lemma left_Fconj'_intro [DecidableEq F] {s : Finset ι} (φ : ι → F) {i} (hi : i ∈ s) : 𝓢 ⊢ (⩕ i ∈ s, φ i) 🡒 φ i :=
  left_Conj'_intro (by simpa) φ

lemma right_Uconj_intro [DecidableEq F] [Fintype ι] (φ : F) (ψ : ι → F) (b : (i : ι) → 𝓢 ⊢ φ 🡒 ψ i) :
    𝓢 ⊢ φ 🡒 ⩕ i, ψ i := right_Fconj'_intro φ Finset.univ ψ (by simpa using b)

lemma left_Uconj_intro [DecidableEq F] [Fintype ι] (φ : ι → F) (i) : 𝓢 ⊢ (⩕ i, φ i) 🡒 φ i := left_Fconj'_intro _ <| by simp


lemma Conj₂_iff_forall_provable [DecidableEq F] {Γ : List F} : (𝓢 ⊢ ⋀Γ) ↔ (∀ φ ∈ Γ, 𝓢 ⊢ φ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, conj₂_cons_nonempty, mem_cons, forall_eq_or_imp];
    constructor;
    . intro h;
      constructor;
      . exact K_left h;
      . exact ih.mp (K_right h);
    . rintro ⟨h₁, h₂⟩;
      exact K_intro h₁ (ih.mpr h₂);

lemma CConj₂Conj₂_of_subset [DecidableEq F] (h : ∀ φ, φ ∈ Γ → φ ∈ Δ) : 𝓢 ⊢ ⋀Δ 🡒 ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp_all only [mem_cons, not_mem_nil, or_false, forall_eq, conj₂_singleton]; exact left_Conj₂_intro h;
  | hcons φ Γ hne ih =>
    simp_all only [ne_eq, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp, not_false_eq_true,
      conj₂_cons_nonempty];
    exact right_K_intro (left_Conj₂_intro h.1) ih;

lemma CConj₂Conj₂_of_provable [DecidableEq F] (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢] φ) : 𝓢 ⊢ ⋀Δ 🡒 ⋀Γ :=
  by induction Γ using List.induction_with_singleton with
  | hnil => exact C_of_conseq verum;
  | hsingle => simp_all only [mem_cons, not_mem_nil, or_false, forall_eq, conj₂_singleton]; exact provable_iff.mp h;
  | hcons φ Γ hne ih =>
    simp_all only [ne_eq, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp, not_false_eq_true,
      conj₂_cons_nonempty];
    exact right_K_intro (provable_iff.mp h.1) ih;

lemma CConj₂_of_forall_provable [DecidableEq F] (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢] φ) : Δ ⊢[𝓢] ⋀Γ := provable_iff.mpr $ CConj₂Conj₂_of_provable h

lemma CConj₂_of_unique [DecidableEq F] (he : ∀ g ∈ Γ, g = φ) : 𝓢 ⊢ φ 🡒 ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hcons χ Γ h ih =>
    simp_all only [ne_eq, mem_cons, true_or, or_true, implies_true, forall_const, forall_eq_or_imp,
      not_false_eq_true, conj₂_cons_nonempty];
    have ⟨he₁, he₂⟩ := he; subst he₁;
    exact right_K_intro C_id ih;
  | _ => simp_all;

lemma C_of_CConj₂_of_unique [DecidableEq F] (he : ∀ g ∈ Γ, g = φ) (hd : 𝓢 ⊢ ⋀Γ 🡒 ψ) : 𝓢 ⊢ φ 🡒 ψ := C_trans (CConj₂_of_unique he) hd

lemma CConj₂_iff_CKConj₂ [DecidableEq F] : 𝓢 ⊢ ⋀(φ :: Γ) 🡒 ψ ↔ 𝓢 ⊢ φ ⋏ ⋀Γ 🡒 ψ := by
  induction Γ with
  | nil =>
    simp only [conj₂_singleton, conj₂_nil, CK_iff_CC];
    constructor;
    . intro h; apply C_swap; exact C_of_conseq h;
    . intro h; exact C_swap h ⨀ verum;
  | cons ψ ih => simp;


@[simp] lemma CConj₂AppendKConj₂Conj₂ [DecidableEq F] : 𝓢 ⊢ ⋀(Γ ++ Δ) 🡒 ⋀Γ ⋏ ⋀Δ := by
  apply FiniteContext.deduct';
  have : [⋀(Γ ++ Δ)] ⊢[𝓢] ⋀(Γ ++ Δ) := id;
  have d := Conj₂_iff_forall_provable.mp this;
  apply K_intro;
  . apply Conj₂_iff_forall_provable.mpr;
    intro φ hp;
    exact d φ (by simp only [mem_append]; left; exact hp);
  . apply Conj₂_iff_forall_provable.mpr;
    intro φ hp;
    exact d φ (by simp only [mem_append]; right; exact hp);

@[simp]
lemma CKConj₂RemoveConj₂ [DecidableEq F] : 𝓢 ⊢ ⋀(Γ.remove φ) ⋏ φ 🡒 ⋀Γ := by
  apply deduct';
  apply Conj₂_iff_forall_provable.mpr;
  intro ψ hq;
  by_cases e : ψ = φ;
  . subst e; exact K_right id;
  . exact Conj₂_iff_forall_provable.mp (K_left id) ψ (by apply List.mem_remove_iff.mpr; simp_all);

lemma CKConj₂Remove_of_CConj₂ [DecidableEq F] (b : 𝓢 ⊢ ⋀Γ 🡒 ψ) : 𝓢 ⊢ ⋀(Γ.remove φ) ⋏ φ 🡒 ψ := C_trans CKConj₂RemoveConj₂ b


lemma Conj₂Append_iff_KConj₂Conj₂ [DecidableEq F] : 𝓢 ⊢ ⋀(Γ ++ Δ) ↔ 𝓢 ⊢ ⋀Γ ⋏ ⋀Δ := by
  constructor;
  . intro h;
    replace h := Conj₂_iff_forall_provable.mp h;
    apply K_intro;
    . apply Conj₂_iff_forall_provable.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; left; simpa);
    . apply Conj₂_iff_forall_provable.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; right; simpa);
  . intro h;
    apply Conj₂_iff_forall_provable.mpr;
    simp only [List.mem_append];
    rintro φ (hp₁ | hp₂);
    . exact (Conj₂_iff_forall_provable.mp $ K_left h) φ hp₁;
    . exact (Conj₂_iff_forall_provable.mp $ K_right h) φ hp₂;


@[simp] lemma EConj₂AppendKConj₂Conj₂ [DecidableEq F] : 𝓢 ⊢ ⋀(Γ ++ Δ) 🡘 ⋀Γ ⋏ ⋀Δ := by
  apply E_intro;
  . apply deduct'; apply Conj₂Append_iff_KConj₂Conj₂.mp; exact id;
  . apply deduct'; apply Conj₂Append_iff_KConj₂Conj₂.mpr; exact id;


lemma CConj₂Append_iff_CKConj₂Conj₂ [DecidableEq F] : 𝓢 ⊢ ⋀(Γ ++ Δ) 🡒 φ ↔ 𝓢 ⊢ (⋀Γ ⋏ ⋀Δ) 🡒 φ := by
  constructor;
  . intro h; exact C_trans (K_right EConj₂AppendKConj₂Conj₂) h;
  . intro h; exact C_trans (K_left EConj₂AppendKConj₂Conj₂) h;

@[simp] lemma CConj₂FConj [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ ⋀Γ.toList 🡒 Γ.conj := by
  apply CConj₂Conj₂_of_provable;
  apply FiniteContext.by_axm;

@[simp] lemma CConj₂FConj_list [DecidableEq F] {Γ : List F} : 𝓢 ⊢ ⋀Γ 🡒 Γ.toFinset.conj := by
  apply C_trans ?_ CConj₂FConj;
  apply CConj₂Conj₂_of_subset;
  simp;

@[simp] lemma CFConjConj₂ [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ Γ.conj 🡒 ⋀Γ.toList := by
  apply right_Conj₂_intro;
  intro φ hφ;
  apply left_Fconj_intro;
  simpa using hφ;

@[simp] lemma CFConjConj₂_list [DecidableEq F] {Γ : List F} : 𝓢 ⊢ Γ.toFinset.conj 🡒 ⋀Γ := by
  apply C_trans $ CFConjConj₂;
  apply CConj₂Conj₂_of_subset;
  simp;

lemma FConj_DT [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ Γ.conj 🡒 φ ↔ Γ *⊢[𝓢] φ := by
  constructor;
  . intro h;
    apply Context.provable_iff.mpr;
    use Γ.toList;
    constructor;
    . simp;
    . apply FiniteContext.provable_iff.mpr;
      exact C_trans (by simp) h;
  . intro h;
    obtain ⟨Δ, hΔ₁, hΔ₂⟩ := Context.provable_iff.mp h;
    replace hΔ₂ : 𝓢 ⊢ ⋀Γ.toList 🡒 φ := C_trans (CConj₂Conj₂_of_subset (by simpa)) $ FiniteContext.provable_iff.mp hΔ₂
    exact C_trans (by simp) hΔ₂;

lemma FConj_iff_forall_provable [DecidableEq F] {Γ : Finset F} : (𝓢 ⊢ Γ.conj) ↔ (∀ φ ∈ Γ, 𝓢 ⊢ φ) := by
  apply Iff.trans Conj₂_iff_forall_provable;
  constructor <;> simp_all;

lemma FConj_of_FConj_of_subset [DecidableEq F] {Γ Δ : Finset F} (h : Δ ⊆ Γ) (hΓ : 𝓢 ⊢ Γ.conj) : 𝓢 ⊢ Δ.conj := by
  rw [FConj_iff_forall_provable] at hΓ ⊢;
  intro φ hφ;
  apply hΓ;
  apply h hφ;

lemma CFConjFConj_of_subset [DecidableEq F] {Γ Δ : Finset F} (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj 🡒 Δ.conj := by
  apply FConj_DT.mpr;
  apply FConj_of_FConj_of_subset h;
  apply FConj_DT.mp;
  simp;

@[simp] lemma CFconjUnionKFconj [DecidableEq F] {Γ Δ : Finset F} : 𝓢 ⊢ (Γ ∪ Δ).conj 🡒 Γ.conj ⋏ Δ.conj := by
  apply FConj_DT.mpr;
  apply K_intro <;>
  . apply FConj_DT.mp;
    apply CFConjFConj_of_subset;
    simp;

@[simp] lemma CinsertFConjKFConj [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ (insert φ Γ).conj 🡒 φ ⋏ Γ.conj := by
  suffices 𝓢 ⊢ ({φ} ∪ Γ).conj 🡒 (Finset.conj {φ}) ⋏ Γ.conj by simpa using this;
  apply CFconjUnionKFconj;

@[simp] lemma CKFconjFconjUnion [DecidableEq F] {Γ Δ : Finset F} : 𝓢 ⊢ Γ.conj ⋏ Δ.conj 🡒 (Γ ∪ Δ).conj := by
  apply right_Fconj_intro;
  simp only [Finset.mem_union];
  rintro φ (hφ | hφ);
  . apply left_K_intro_left
    apply left_Fconj_intro hφ;
  . apply left_K_intro_right;
    apply left_Fconj_intro hφ;

@[simp]
lemma CKFConjinsertFConj [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ φ ⋏ Γ.conj 🡒 (insert φ Γ).conj := by
  suffices 𝓢 ⊢ (Finset.conj {φ}) ⋏ Γ.conj 🡒 ({φ} ∪ Γ).conj by simpa using this;
  apply CKFconjFconjUnion;

lemma FConj_DT' [DecidableEq F] {Γ Δ : Finset F} : Γ *⊢[𝓢] Δ.conj 🡒 φ ↔ ↑(Γ ∪ Δ) *⊢[𝓢] φ := by
  constructor;
  . intro h; exact FConj_DT.mp $ C_trans CFconjUnionKFconj $ CK_iff_CC.mpr $ FConj_DT.mpr h;
  . intro h; exact FConj_DT.mp $ CK_iff_CC.mp $ C_trans CKFconjFconjUnion $ FConj_DT.mpr h;

lemma CFconjFconj_of_provable [DecidableEq F] {Γ Δ : Finset _} (h : ∀ φ, φ ∈ Γ → Δ *⊢[𝓢] φ) : 𝓢 ⊢ Δ.conj 🡒 Γ.conj := by
  have : 𝓢 ⊢ ⋀(Δ.toList) 🡒 ⋀(Γ.toList) := CConj₂Conj₂_of_provable $ by
    intro φ hφ;
    apply Context.iff_provable_context_provable_finiteContext_toList.mp
    apply h φ;
    simpa using hφ;
  refine C_replace ?_ ?_ this;
  . simp;
  . simp;

end Conjunction


section disjunction

def right_Disj!_intro [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢! φ 🡒 Γ.disj :=
  match Γ with
  |     [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ then cast (or₁! : 𝓢 ⊢! φ 🡒 φ ⋎ Γ.disj) (by simp [e])
    else
      have : φ ∈ Γ := by simpa [e] using h
      C!_trans (right_Disj!_intro Γ this) or₂!
theorem right_Disj_intro [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢ φ 🡒 Γ.disj := ⟨right_Disj!_intro Γ h⟩

def right_Disj!_intro' [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) (hψ : 𝓢 ⊢! ψ 🡒 φ) : 𝓢 ⊢! ψ 🡒 Γ.disj :=
  C!_trans hψ (right_Disj!_intro Γ h)
theorem right_Disj_intro' [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) (hψ : 𝓢 ⊢ ψ 🡒 φ) : 𝓢 ⊢ ψ 🡒 Γ.disj := ⟨right_Disj!_intro' Γ h hψ.get⟩

def right_Disj₂!_intro [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢! φ 🡒 ⋁Γ :=
  match Γ with
  |     [] => by simp at h
  |    [ψ] => (show ⋁[ψ] = φ by simp_all) ▸ C!_id
  | ψ :: χ :: Γ =>
    if e : φ = ψ then cast (or₁! : 𝓢 ⊢! φ 🡒 φ ⋎ ⋁(χ :: Γ)) (by simp [e])
    else
      have : φ ∈ χ :: Γ := by simpa [e] using h
      C!_trans (right_Disj₂!_intro _ this) or₂!
theorem right_Disj₂_intro [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢ φ 🡒 ⋁Γ := ⟨right_Disj₂!_intro Γ h⟩

def right_Disj'!_intro [DecidableEq F] (φ : ι → F) (l : List ι) (h : i ∈ l) : 𝓢 ⊢! φ i 🡒 l.disj' φ :=
  right_Disj₂!_intro (l.map φ) (by simpa using ⟨i, h, rfl⟩)
lemma right_Disj'_intro [DecidableEq F] (φ : ι → F) (l : List ι) (h : i ∈ l) : 𝓢 ⊢ φ i 🡒 l.disj' φ := ⟨right_Disj'!_intro φ l h⟩

lemma right_Fdisj_intro [DecidableEq F] (s : Finset F) (h : φ ∈ s) : 𝓢 ⊢ φ 🡒 s.disj := right_Disj₂_intro _ (by simp [h])

lemma right_Fdisj'_intro [DecidableEq F] (s : Finset ι) (φ : ι → F) {i} (hi : i ∈ s) : 𝓢 ⊢ φ i 🡒 ⩖ j ∈ s, φ j :=
  right_Disj'_intro _ _ (by simp [hi])

lemma right_Udisj_intro [DecidableEq F] [Fintype ι] (φ : ι → F) : 𝓢 ⊢ φ i 🡒 ⩖ j, φ j := right_Fdisj'_intro _ _ (by simp)

end disjunction


section

variable {Γ Δ : Finset F}

lemma CFConjFDisj_of_K_intro [DecidableEq F] (hp : φ ∈ Γ) (hpq : ψ ∈ Γ) (hψ : φ ⋏ ψ ∈ Δ) : 𝓢 ⊢ Γ.conj 🡒 Δ.disj := by
  apply C_trans (ψ := Finset.disj {φ ⋏ ψ});
  . apply C_trans (ψ := Finset.conj {φ, ψ}) ?_;
    . apply FConj_DT.mpr;
      simp only [Finset.coe_insert, Finset.coe_singleton, Finset.disj_singleton];
      apply K_intro <;> exact Context.by_axm $ by simp;
    . apply CFConjFConj_of_subset;
      apply Finset.doubleton_subset.mpr;
      tauto;
  . simp only [Finset.disj_singleton];
    apply right_Fdisj_intro _ hψ;

lemma CFConjFDisj_of_innerMDP [DecidableEq F] (hp : φ ∈ Γ) (hpq : φ 🡒 ψ ∈ Γ) (hψ : ψ ∈ Δ) : 𝓢 ⊢ Γ.conj 🡒 Δ.disj := by
  apply C_trans (ψ := Finset.disj {ψ});
  . apply C_trans (ψ := Finset.conj {φ, φ 🡒 ψ}) ?_;
    . apply FConj_DT.mpr;
      have h₁ : ({φ, φ 🡒 ψ}) *⊢[𝓢] φ 🡒 ψ := Context.by_axm $ by simp;
      have h₂ : ({φ, φ 🡒 ψ}) *⊢[𝓢] φ := Context.by_axm $ by simp;
      simpa using h₁ ⨀ h₂;
    . apply CFConjFConj_of_subset;
      apply Finset.doubleton_subset.mpr;
      tauto;
  . simp only [Finset.disj_singleton];
    apply right_Fdisj_intro _ hψ;

lemma iff_FiniteContext_Context [DecidableEq F] {Γ : List F} : Γ ⊢[𝓢] φ ↔ ↑Γ.toFinset *⊢[𝓢] φ := by
  constructor;
  . intro h;
    replace h := FiniteContext.provable_iff.mp h;
    apply FConj_DT.mp;
    exact C_trans (by simp) h;
  . intro h;
    replace h := FConj_DT.mpr h;
    apply FiniteContext.provable_iff.mpr;
    exact C_trans (by simp) h;

lemma FConj'_iff_forall_provable [DecidableEq F] {s : Finset α} {ι : α → F} : (𝓢 ⊢ ⩕ i ∈ s, ι i) ↔ (∀ i ∈ s, 𝓢 ⊢ ι i) := by
  have : 𝓢 ⊢ ⋀(s.toList.map ι) ↔ ∀ i ∈ s, 𝓢 ⊢ ι i := by simpa using Conj₂_iff_forall_provable (Γ := s.toList.map ι);
  apply Iff.trans ?_ this;
  simp [Finset.conj', List.conj'];

end


namespace Context

lemma provable_iff_finset [DecidableEq F] {Γ : Set F} {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : Finset F, (↑Δ ⊆ Γ) ∧ Δ *⊢[𝓢] φ := by
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
      refine C_trans ?_ (FConj_DT.mpr hΔ₂);
      simp;

lemma bot_of_mem_neg [DecidableEq F] {Γ : Set F}  (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ *⊢[𝓢] ⊥ := by
  replace h₁ : Γ *⊢[𝓢] φ := by_axm h₁;
  replace h₂ : Γ *⊢[𝓢] φ 🡒 ⊥ := N_iff_CO.mp $ by_axm h₂;
  exact h₂ ⨀ h₁;

end Context

end


end LO.Entailment

end
