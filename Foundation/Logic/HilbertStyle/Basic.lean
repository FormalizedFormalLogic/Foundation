import Foundation.Logic.Entailment
import Foundation.Logic.Axioms

/-!
# Basic Lemmata of Hilbert-Style Deduction System.

## Naming Convention

The names of the formalized proofs are determined by the following steps. (e.g. `𝓢 ⊢! (φ ⋏ ψ ➝ χ) ⭤ (φ ➝ ψ ➝ χ)`):
1. Convert the formula to Łukasiewicz's notation (`ECKφψχCφCψχ`).
2. Remove meta variables (`ECKCC`).
3. Postfix `!` if it is a proposition (`ECKCC!`).
4. Use snake_case even if it is definition.
-/

namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment F S]
variable {𝓢 : S} {φ ψ χ : F}


def cast (e : φ = ψ) (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ := e ▸ b
def cast! (e : φ = ψ) (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ := ⟨cast e b.some⟩


class ModusPonens (𝓢 : S) where
  mdp {φ ψ : F} : 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ φ → 𝓢 ⊢ ψ

alias mdp := ModusPonens.mdp
infixl:90 "⨀" => mdp

lemma mdp! [ModusPonens 𝓢] : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! φ → 𝓢 ⊢! ψ := by
  rintro ⟨hpq⟩ ⟨hp⟩;
  exact ⟨hpq ⨀ hp⟩
infixl:90 "⨀" => mdp!

class HasAxiomVerum (𝓢 : S) where
  verum : 𝓢 ⊢ Axioms.Verum

def verum [HasAxiomVerum 𝓢] : 𝓢 ⊢ ⊤ := HasAxiomVerum.verum
@[simp] lemma verum! [HasAxiomVerum 𝓢] : 𝓢 ⊢! ⊤ := ⟨verum⟩


class HasAxiomImply₁ (𝓢 : S)  where
  imply₁ (φ ψ : F) : 𝓢 ⊢ Axioms.Imply₁ φ ψ

def imply₁ [HasAxiomImply₁ 𝓢] : 𝓢 ⊢ φ ➝ ψ ➝ φ := HasAxiomImply₁.imply₁ _ _
@[simp] lemma imply₁! [HasAxiomImply₁ 𝓢] : 𝓢 ⊢! φ ➝ ψ ➝ φ := ⟨imply₁⟩

def C_of_conseq [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (h : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ ➝ φ := imply₁ ⨀ h
alias dhyp := C_of_conseq

lemma C!_of_conseq! [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ ➝ φ := ⟨C_of_conseq d.some⟩
alias dhyp! := C!_of_conseq!

class HasAxiomImply₂ (𝓢 : S)  where
  imply₂ (φ ψ χ : F) : 𝓢 ⊢ Axioms.Imply₂ φ ψ χ

def imply₂ [HasAxiomImply₂ 𝓢] : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := HasAxiomImply₂.imply₂ _ _ _
@[simp] lemma imply₂! [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := ⟨imply₂⟩

class HasAxiomAndElim (𝓢 : S)  where
  and₁ (φ ψ : F) : 𝓢 ⊢ Axioms.AndElim₁ φ ψ
  and₂ (φ ψ : F) : 𝓢 ⊢ Axioms.AndElim₂ φ ψ

def and₁ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ φ := HasAxiomAndElim.and₁ _ _
@[simp] lemma and₁! [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ➝ φ := ⟨and₁⟩

def K_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ φ := and₁ ⨀ d

lemma K!_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! (φ ⋏ ψ)) : 𝓢 ⊢! φ := ⟨K_left d.some⟩

def and₂ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ ψ := HasAxiomAndElim.and₂ _ _
@[simp] lemma and₂! [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ➝ ψ := ⟨and₂⟩

def K_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ := and₂ ⨀ d

lemma K!_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! (φ ⋏ ψ)) : 𝓢 ⊢! ψ := ⟨K_right d.some⟩

class HasAxiomAndInst (𝓢 : S) where
  and₃ (φ ψ : F) : 𝓢 ⊢ Axioms.AndInst φ ψ

def and₃ [HasAxiomAndInst 𝓢] : 𝓢 ⊢ φ ➝ ψ ➝ φ ⋏ ψ := HasAxiomAndInst.and₃ _ _
@[simp] lemma and₃! [HasAxiomAndInst 𝓢] : 𝓢 ⊢! φ ➝ ψ ➝ φ ⋏ ψ := ⟨and₃⟩

def K_intro [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢ φ) (d₂: 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋏ ψ := and₃ ⨀ d₁ ⨀ d₂

lemma K!_intro  [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢! φ) (d₂: 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋏ ψ := ⟨K_intro d₁.some d₂.some⟩


class HasAxiomOrInst (𝓢 : S) where
  or₁ (φ ψ : F) : 𝓢 ⊢ Axioms.OrInst₁ φ ψ
  or₂ (φ ψ : F) : 𝓢 ⊢ Axioms.OrInst₂ φ ψ

def or₁  [HasAxiomOrInst 𝓢] : 𝓢 ⊢ φ ➝ φ ⋎ ψ := HasAxiomOrInst.or₁ _ _
@[simp] lemma or₁! [HasAxiomOrInst 𝓢] : 𝓢 ⊢! φ ➝ φ ⋎ ψ := ⟨or₁⟩

def A_intro_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ φ ⋎ ψ := or₁ ⨀ d
lemma A!_intro_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! φ ⋎ ψ := ⟨A_intro_left d.some⟩

def or₂ [HasAxiomOrInst 𝓢] : 𝓢 ⊢ ψ ➝ φ ⋎ ψ := HasAxiomOrInst.or₂ _ _
@[simp] lemma or₂! [HasAxiomOrInst 𝓢] : 𝓢 ⊢! ψ ➝ φ ⋎ ψ := ⟨or₂⟩

def A_intro_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋎ ψ := or₂ ⨀ d
lemma A!_intro_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋎ ψ := ⟨A_intro_right d.some⟩


class HasAxiomOrElim (𝓢 : S) where
  or₃ (φ ψ χ : F) : 𝓢 ⊢ Axioms.OrElim φ ψ χ

def or₃ [HasAxiomOrElim 𝓢] : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ) ➝ χ := HasAxiomOrElim.or₃ _ _ _
@[simp] lemma or₃! [HasAxiomOrElim 𝓢] : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ) ➝ χ := ⟨or₃⟩

def left_A_intro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ➝ χ) (d₂ : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ χ := or₃ ⨀ d₁ ⨀ d₂
lemma left_A!_intro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ➝ χ) (d₂ : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ χ := ⟨left_A_intro d₁.some d₂.some⟩
alias CA_of_C_of_C := left_A_intro
alias CA!_of_C!_of_C! := left_A!_intro

def of_C_of_C_of_A [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ➝ χ) (d₂ : 𝓢 ⊢ ψ ➝ χ) (d₃ : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ χ := or₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
alias A_cases := of_C_of_C_of_A

lemma of_C!_of_C!_of_A! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ➝ χ) (d₂ : 𝓢 ⊢! ψ ➝ χ) (d₃ : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! χ := ⟨of_C_of_C_of_A d₁.some d₂.some d₃.some⟩
alias A!_cases := of_C!_of_C!_of_A!


class HasAxiomEFQ (𝓢 : S) where
  efq (φ : F) : 𝓢 ⊢ Axioms.EFQ φ

def efq [HasAxiomEFQ 𝓢] : 𝓢 ⊢ ⊥ ➝ φ := HasAxiomEFQ.efq _
@[simp] lemma efq! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⊥ ➝ φ := ⟨efq⟩

def of_O [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ⊥) : 𝓢 ⊢ φ := efq ⨀ b
lemma of_O! [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! ⊥) : 𝓢 ⊢! φ := ⟨of_O h.some⟩


class HasAxiomLEM (𝓢 : S) where
  lem (φ : F) : 𝓢 ⊢ Axioms.LEM φ

def lem [HasAxiomLEM 𝓢] : 𝓢 ⊢ φ ⋎ ∼φ := HasAxiomLEM.lem φ
@[simp] lemma lem! [HasAxiomLEM 𝓢] : 𝓢 ⊢! φ ⋎ ∼φ := ⟨lem⟩


class HasAxiomDNE (𝓢 : S) where
  dne (φ : F) : 𝓢 ⊢ Axioms.DNE φ

def dne [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼φ ➝ φ := HasAxiomDNE.dne _
@[simp] lemma dne! [HasAxiomDNE 𝓢] : 𝓢 ⊢! ∼∼φ ➝ φ := ⟨dne⟩

def of_NN [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼∼φ) : 𝓢 ⊢ φ := dne ⨀ b
lemma of_NN! [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! ∼∼φ) : 𝓢 ⊢! φ := ⟨of_NN h.some⟩

/--
  Negation `∼φ` is equivalent to `φ ➝ ⊥` on **system**.

  This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ ➝ ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv (𝓢 : S) where
  negEquiv (φ : F) : 𝓢 ⊢ Axioms.NegEquiv φ

def negEquiv [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ ⭤ (φ ➝ ⊥) := NegationEquiv.negEquiv _
@[simp] lemma neg_equiv! [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ ⭤ (φ ➝ ⊥) := ⟨negEquiv⟩

class HasAxiomElimContra (𝓢 : S)  where
  elimContra (φ ψ : F) : 𝓢 ⊢ Axioms.ElimContra φ ψ

def elimContra [HasAxiomElimContra 𝓢] : 𝓢 ⊢ ((∼ψ) ➝ (∼φ)) ➝ (φ ➝ ψ) := HasAxiomElimContra.elimContra _ _
@[simp] lemma elim_contra! [HasAxiomElimContra 𝓢] : 𝓢 ⊢! (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)  := ⟨elimContra⟩

protected class Minimal (𝓢 : S) extends
              ModusPonens 𝓢,
              NegationEquiv 𝓢,
              HasAxiomVerum 𝓢,
              HasAxiomImply₁ 𝓢, HasAxiomImply₂ 𝓢,
              HasAxiomAndElim 𝓢, HasAxiomAndInst 𝓢,
              HasAxiomOrInst 𝓢, HasAxiomOrElim 𝓢

protected class Int (𝓢 : S) extends Entailment.Minimal 𝓢, HasAxiomEFQ 𝓢

protected class Cl (𝓢 : S) extends Entailment.Minimal 𝓢, HasAxiomDNE 𝓢


section

variable [ModusPonens 𝓢]

def CO_of_N [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ → 𝓢 ⊢ φ ➝ ⊥ := λ h => (K_left negEquiv) ⨀ h
def N_of_CO [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ φ ➝ ⊥ → 𝓢 ⊢ ∼φ := λ h => (K_right negEquiv) ⨀ h
lemma N!_iff_CO! [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ ↔ 𝓢 ⊢! φ ➝ ⊥ := ⟨λ ⟨h⟩ => ⟨CO_of_N h⟩, λ ⟨h⟩ => ⟨N_of_CO h⟩⟩

def E_intro [HasAxiomAndInst 𝓢] (b₁ : 𝓢 ⊢ φ ➝ ψ) (b₂ : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ φ ⭤ ψ := K_intro b₁ b₂
def E!_intro [HasAxiomAndInst 𝓢] (h₁ : 𝓢 ⊢! φ ➝ ψ) (h₂ : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! φ ⭤ ψ := ⟨K_intro h₁.some h₂.some⟩

lemma K!_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ↔ 𝓢 ⊢! φ ∧ 𝓢 ⊢! ψ := ⟨fun h ↦ ⟨K!_left h, K!_right h⟩, fun h ↦ K!_intro h.1 h.2⟩

lemma E!_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⭤ ψ ↔ 𝓢 ⊢! φ ➝ ψ ∧ 𝓢 ⊢! ψ ➝ φ := ⟨fun h ↦ ⟨K!_left h, K!_right h⟩, fun h ↦ K!_intro h.1 h.2⟩

lemma C_of_E_mp! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! φ ➝ ψ := by exact E!_intro_iff.mp h |>.1;
lemma C_of_E_mpr! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ψ ➝ φ := by exact E!_intro_iff.mp h |>.2;

lemma iff_of_E!  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! φ ↔ 𝓢 ⊢! ψ := ⟨fun hp ↦ K!_left h ⨀ hp, fun hq ↦ K!_right h ⨀ hq⟩

def C_id [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ : F) : 𝓢 ⊢ φ ➝ φ := imply₂ (φ := φ) (ψ := (φ ➝ φ)) (χ := φ) ⨀ imply₁ ⨀ imply₁
@[simp] def C!_id [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ ➝ φ := ⟨C_id φ⟩

def E_Id [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ : F) : 𝓢 ⊢ φ ⭤ φ := K_intro (C_id φ) (C_id φ)
@[simp] def E!_id [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ ⭤ φ := ⟨E_Id φ⟩

instance [NegAbbrev F] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [HasAxiomAndInst 𝓢] : Entailment.NegationEquiv 𝓢 where
  negEquiv := by intro φ; simp [Axioms.NegEquiv, NegAbbrev.neg]; apply E_Id;


def NO [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ ∼⊥ := N_of_CO (C_id ⊥)
@[simp] lemma NO! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! ∼⊥ := ⟨NO⟩

def mdp₁ [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ) (bq : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ χ := imply₂ ⨀ bqr ⨀ bq
lemma mdp₁! [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ) (hq : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ χ := ⟨mdp₁ hqr.some hq.some⟩

infixl:90 "⨀₁" => mdp₁
infixl:90 "⨀₁" => mdp₁!

def mdp₂ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s) (bq : 𝓢 ⊢ φ ➝ ψ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ➝ s := C_of_conseq (imply₂) ⨀₁ bqr ⨀₁ bq
lemma mdp₂! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s) (hq : 𝓢 ⊢! φ ➝ ψ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ➝ s := ⟨mdp₂ hqr.some hq.some⟩

infixl:90 "⨀₂" => mdp₂
infixl:90 "⨀₂" => mdp₂!

def mdp₃ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t) (bq : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ t := (C_of_conseq <| C_of_conseq <| imply₂) ⨀₂ bqr ⨀₂ bq
lemma mdp₃! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t) (hq : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ t := ⟨mdp₃ hqr.some hq.some⟩

infixl:90 "⨀₃" => mdp₃
infixl:90 "⨀₃" => mdp₃!

def mdp₄ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t ➝ u) (bq : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ u := (C_of_conseq <| C_of_conseq <| C_of_conseq <| imply₂) ⨀₃ bqr ⨀₃ bq
lemma mdp₄! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t ➝ u) (hq : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ u := ⟨mdp₄ hqr.some hq.some⟩
infixl:90 "⨀₄" => mdp₄
infixl:90 "⨀₄" => mdp₄!

def C_trans [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bpq : 𝓢 ⊢ φ ➝ ψ) (bqr : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ➝ χ := imply₂ ⨀ C_of_conseq bqr ⨀ bpq
lemma C!_trans [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : 𝓢 ⊢! φ ➝ ψ) (hqr : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ➝ χ := ⟨C_trans hpq.some hqr.some⟩

lemma C!_replace [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h₁ : 𝓢 ⊢! ψ₁ ➝ φ₁) (h₂ : 𝓢 ⊢! φ₂ ➝ ψ₂) : 𝓢 ⊢! φ₁ ➝ φ₂ → 𝓢 ⊢! ψ₁ ➝ ψ₂ := λ h => C!_trans h₁ $ C!_trans h h₂

lemma unprovable_C!_trans [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊬ φ ➝ χ → 𝓢 ⊬ ψ ➝ χ := by
  contrapose; simp [neg_neg];
  exact C!_trans hpq;

def E_trans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h₁ : 𝓢 ⊢ φ ⭤ ψ) (h₂ : 𝓢 ⊢ ψ ⭤ χ) : 𝓢 ⊢ φ ⭤ χ := by
  apply E_intro;
  . exact C_trans (K_left h₁) (K_left h₂);
  . exact C_trans (K_right h₂) (K_right h₁);
lemma E!_trans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]  (h₁ : 𝓢 ⊢! φ ⭤ ψ) (h₂ : 𝓢 ⊢! ψ ⭤ χ) : 𝓢 ⊢! φ ⭤ χ := ⟨E_trans h₁.some h₂.some⟩

lemma uniff_of_E! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (H : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊬ φ ↔ 𝓢 ⊬ ψ := by
  constructor;
  . intro hp hq; have := K!_right H ⨀ hq; contradiction;
  . intro hq hp; have := K!_left H ⨀ hp; contradiction;

def CCCC [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ φ := C_trans imply₁ imply₁
@[simp] lemma CCCC! [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ φ := ⟨CCCC φ ψ χ⟩

def CK_of_C_of_C [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (bq : 𝓢 ⊢ φ ➝ ψ) (br : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ⋏ χ := C_of_conseq and₃ ⨀₁ bq ⨀₁ br
lemma CK!_of_C!_of_C! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hq : 𝓢 ⊢! φ ➝ ψ) (hr : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ⋏ χ := ⟨CK_of_C_of_C hq.some hr.some⟩


def CKK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ : F) : 𝓢 ⊢ φ ⋏ ψ ➝ ψ ⋏ φ := CK_of_C_of_C and₂ and₁
lemma CKK! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ ⋏ ψ ➝ ψ ⋏ φ := ⟨CKK φ ψ⟩

def K_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ ⋏ φ := CKK _ _ ⨀ h
lemma K!_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ ⋏ φ := ⟨K_symm h.some⟩


def CEE [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ : F) : 𝓢 ⊢ (φ ⭤ ψ) ➝ (ψ ⭤ φ) := CKK _ _
lemma CEE!  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (φ ⭤ ψ) ➝ (ψ ⭤ φ) := ⟨CEE φ ψ⟩

def E_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ψ ⭤ φ := CEE _ _ ⨀ h
lemma E!_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ψ ⭤ φ := ⟨E_symm h.some⟩


def ECKCC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) : 𝓢 ⊢ (φ ⋏ ψ ➝ χ) ⭤ (φ ➝ ψ ➝ χ) := by
  let b₁ : 𝓢 ⊢ (φ ⋏ ψ ➝ χ) ➝ φ ➝ ψ ➝ χ :=
    CCCC (φ ⋏ ψ ➝ χ) φ ψ ⨀₃ C_of_conseq (ψ := φ ⋏ ψ ➝ χ) and₃
  let b₂ : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ φ ⋏ ψ ➝ χ :=
    imply₁ ⨀₂ (C_of_conseq (ψ := φ ➝ ψ ➝ χ) and₁) ⨀₂ (C_of_conseq (ψ := φ ➝ ψ ➝ χ) and₂);
  exact E_intro b₁ b₂
lemma ECKCC! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (φ ⋏ ψ ➝ χ) ⭤ (φ ➝ ψ ➝ χ) := ⟨ECKCC φ ψ χ⟩

def CC_of_CK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ➝ χ := (K_left $ ECKCC φ ψ χ) ⨀ d
def CK_of_CC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d : 𝓢 ⊢ φ ➝ ψ ➝ χ) : 𝓢 ⊢ φ ⋏ ψ ➝ χ := (K_right $ ECKCC φ ψ χ) ⨀ d

lemma CK!_iff_CC! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]: (𝓢 ⊢! φ ⋏ ψ ➝ χ) ↔ (𝓢 ⊢! φ ➝ ψ ➝ χ) := by
  apply Iff.intro;
  . intro ⟨h⟩; exact ⟨CC_of_CK h⟩
  . intro ⟨h⟩; exact ⟨CK_of_CC h⟩

def CV [HasAxiomVerum 𝓢] [HasAxiomImply₁ 𝓢] : 𝓢 ⊢ φ ➝ ⊤ := C_of_conseq verum
@[simp] lemma CV! [HasAxiomImply₁ 𝓢] [HasAxiomVerum 𝓢] : 𝓢 ⊢! φ ➝ ⊤ := ⟨CV⟩

instance [(𝓢 : S) → ModusPonens 𝓢] [(𝓢 : S) → HasAxiomEFQ 𝓢] : DeductiveExplosion S := ⟨fun b _ ↦ efq ⨀ b⟩

section Conjunction

variable [Entailment.Minimal 𝓢]

def conj₂Nth : (Γ : List F) → (n : ℕ) → (hn : n < Γ.length) → 𝓢 ⊢ ⋀Γ ➝ Γ[n]
  |          [],     _, hn => by simp at hn
  |         [ψ],     0, _  => C_id ψ
  | φ :: ψ :: Γ,     0, _  => and₁
  | φ :: ψ :: Γ, n + 1, hn => C_trans (and₂ (φ := φ)) (conj₂Nth (ψ :: Γ) n (Nat.succ_lt_succ_iff.mp hn))

def conj₂_nth! (Γ : List F) (n : ℕ) (hn : n < Γ.length) : 𝓢 ⊢! ⋀Γ ➝ Γ[n] := ⟨conj₂Nth Γ n hn⟩

variable {Γ Δ : List F}

def left_Conj_intro [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢ Γ.conj ➝ φ :=
  match Γ with
  |     [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ
    then cast (by simp [e]) (and₁ (φ := φ) (ψ := Γ.conj))
    else
      have : φ ∈ Γ := by simpa [e] using h
      C_trans and₂ (left_Conj_intro this)
lemma left_Conj!_intro [DecidableEq F] (h : φ ∈ Γ) : 𝓢 ⊢! Γ.conj ➝ φ := ⟨left_Conj_intro h⟩

def Conj_intro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ Γ.conj :=
  match Γ with
  |     [] => verum
  | ψ :: Γ => K_intro (b ψ (by simp)) (Conj_intro Γ (fun ψ hq ↦ b ψ (by simp [hq])))

def right_Conj_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ Γ.conj :=
  match Γ with
  |     [] => C_of_conseq verum
  | ψ :: Γ => CK_of_C_of_C (b ψ (by simp)) (right_Conj_intro φ Γ (fun ψ hq ↦ b ψ (by simp [hq])))
def right_Conj!_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ Γ.conj := ⟨right_Conj_intro φ Γ fun ψ h ↦ (b ψ h).get⟩

def CConjConj [DecidableEq F] (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj ➝ Δ.conj := right_Conj_intro _ _ (fun _ hq ↦ left_Conj_intro (h hq))

def left_Conj₂_intro [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ ➝ φ :=
  have : Γ.idxOf φ < Γ.length := List.idxOf_lt_length h
  have : Γ[Γ.idxOf φ] = φ := List.getElem_idxOf this
  cast (by rw[this]) <| conj₂Nth Γ (Γ.idxOf φ) (by assumption)
lemma left_Conj₂!_intro [DecidableEq F] (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ ➝ φ := ⟨left_Conj₂_intro h⟩

def Conj₂_intro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ ⋀Γ :=
  match Γ with
  |          [] => verum
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by
    simp;
    exact K_intro (b ψ (by simp)) (Conj₂_intro _ (by aesop))
lemma Conj₂!_intro (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) : 𝓢 ⊢! ⋀Γ := ⟨Conj₂_intro Γ (λ φ hp => (b φ hp).some)⟩

def right_Conj₂_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ ⋀Γ :=
  match Γ with
  |          [] => C_of_conseq verum
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by
    simp;
    apply CK_of_C_of_C (b ψ (by simp)) (right_Conj₂_intro φ _ (fun ψ hq ↦ b ψ (by simp [hq])));
lemma right_Conj₂!_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ ⋀Γ := ⟨right_Conj₂_intro φ Γ (λ ψ hq => (b ψ hq).some)⟩

def CConj₂Conj₂ [DecidableEq F] {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢ ⋀Γ ➝ ⋀Δ :=
  right_Conj₂_intro _ _ (fun _ hq ↦ left_Conj₂_intro (h hq))
lemma CConj₂_Conj₂! [DecidableEq F] {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢! ⋀Γ ➝ ⋀Δ := ⟨CConj₂Conj₂ h⟩

end Conjunction

end


section

variable {G T : Type*} [Entailment G T] [LogicalConnective G] {𝓣 : T}

def Minimal.ofEquiv (𝓢 : S) [Entailment.Minimal 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢ f φ ≃ 𝓣 ⊢ φ) : Entailment.Minimal 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢ f φ ➝ f ψ := by simpa using (e (φ ➝ ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  negEquiv φ := e _ (by simpa using negEquiv)
  verum := e _ (by simpa using verum)
  imply₁ φ ψ := e _ (by simpa using imply₁)
  imply₂ φ ψ χ := e _ (by simpa using imply₂)
  and₁ φ ψ := e _ (by simpa using and₁)
  and₂ φ ψ := e _ (by simpa using and₂)
  and₃ φ ψ := e _ (by simpa using and₃)
  or₁ φ ψ := e _ (by simpa using or₁)
  or₂ φ ψ := e _ (by simpa using or₂)
  or₃ φ ψ χ := e _ (by simpa using or₃)

def Cl.ofEquiv (𝓢 : S) [Entailment.Cl 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢ f φ ≃ 𝓣 ⊢ φ) : Entailment.Cl 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢ f φ ➝ f ψ := by simpa using (e (φ ➝ ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  negEquiv φ := e _ (by simpa using negEquiv)
  verum := e _ (by simpa using verum)
  imply₁ φ ψ := e _ (by simpa using imply₁)
  imply₂ φ ψ χ := e _ (by simpa using imply₂)
  and₁ φ ψ := e _ (by simpa using and₁)
  and₂ φ ψ := e _ (by simpa using and₂)
  and₃ φ ψ := e _ (by simpa using and₃)
  or₁ φ ψ := e _ (by simpa using or₁)
  or₂ φ ψ := e _ (by simpa using or₂)
  or₃ φ ψ χ := e _ (by simpa using or₃)
  dne φ := e _ (by simpa using dne)

end

end LO.Entailment
