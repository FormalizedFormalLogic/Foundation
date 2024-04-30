import Logic.Logic.System
import Logic.Logic.Init

namespace LO.System

variable {S F : Type*} [LogicalConnective F] [System F S]

variable (𝓢 : S)

class ModusPonens where
  mdp {p q : F} : 𝓢 ⊢ p ⟶ q → 𝓢 ⊢ p → 𝓢 ⊢ q

class Minimal extends ModusPonens 𝓢 where
  verum              : 𝓢 ⊢ ⊤
  imply₁ (p q : F)   : 𝓢 ⊢ p ⟶ q ⟶ p
  imply₂ (p q r : F) : 𝓢 ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁  (p q : F)   : 𝓢 ⊢ p ⋏ q ⟶ p
  conj₂  (p q : F)   : 𝓢 ⊢ p ⋏ q ⟶ q
  conj₃  (p q : F)   : 𝓢 ⊢ p ⟶ q ⟶ p ⋏ q
  disj₁  (p q : F)   : 𝓢 ⊢ p ⟶ p ⋎ q
  disj₂  (p q : F)   : 𝓢 ⊢ q ⟶ p ⋎ q
  disj₃  (p q r : F) : 𝓢 ⊢ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r

/-- Supplymental -/
class HasEFQ where
  efq (p : F) : 𝓢 ⊢ ⊥ ⟶ p

class HasWeakLEM where
  wlem (p : F) : 𝓢 ⊢ ~p ⋎ ~~p

class HasLEM where
  lem (p : F) : 𝓢 ⊢ p ⋎ ~p

class HasDNE where
  dne (p : F) : 𝓢 ⊢ ~~p ⟶ p

class Dummett where
  dummett (p q : F) : 𝓢 ⊢ (p ⟶ q) ⋎ (q ⟶ p)

class Peirce where
  peirce (p q : F) : 𝓢 ⊢ ((p ⟶ q) ⟶ p) ⟶ p

/--
  Intuitionistic Propositional Logic.

  Modal companion of `𝐒𝟒`
-/
class Intuitionistic extends Minimal 𝓢, HasEFQ 𝓢

/--
  Propositional Logic for Weak Law of Excluded Middle.

  Modal companion of `𝐒𝟒.𝟐`
-/
class WeakLEM extends Intuitionistic 𝓢, HasWeakLEM 𝓢

/--
  Gödel-Dummett Propositional Logic.

  Modal companion of `𝐒𝟒.𝟑`
-/
class GD extends Intuitionistic 𝓢, Dummett 𝓢

/--
  Classical Propositional Logic.

  Modal companion of `𝐒𝟓`
-/
class Classical extends Minimal 𝓢, HasDNE 𝓢

variable {𝓢}

infixl:90 "⨀" => ModusPonens.mdp

infixl:90 "⨀" => ModusPonens.mdp!

variable [Minimal 𝓢]

def cast {p q : F} (e : p = q) (b : 𝓢 ⊢ p) : 𝓢 ⊢ q := e ▸ b

alias verum := Minimal.verum
@[simp] lemma verum! : 𝓢 ⊢! ⊤ := ⟨verum⟩

def imply₁ : 𝓢 ⊢ p ⟶ q ⟶ p := Minimal.imply₁ _ _
@[simp] lemma imply₁! : 𝓢 ⊢! p ⟶ q ⟶ p := ⟨imply₁⟩

def imply₂ : 𝓢 ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := Minimal.imply₂ _ _ _
@[simp] lemma imply₂! : 𝓢 ⊢! (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := ⟨imply₂⟩

def conj₁ : 𝓢 ⊢ p ⋏ q ⟶ p := Minimal.conj₁ _ _
@[simp] lemma conj₁! : 𝓢 ⊢! p ⋏ q ⟶ p := ⟨conj₁⟩

def conj₂ : 𝓢 ⊢ p ⋏ q ⟶ q := Minimal.conj₂ _ _
@[simp] lemma conj₂! : 𝓢 ⊢! p ⋏ q ⟶ q := ⟨conj₂⟩

def conj₃ : 𝓢 ⊢ p ⟶ q ⟶ p ⋏ q := Minimal.conj₃ _ _
@[simp] lemma conj₃! : 𝓢 ⊢! p ⟶ q ⟶ p ⋏ q := ⟨conj₃⟩

def disj₁ : 𝓢 ⊢ p ⟶ p ⋎ q := Minimal.disj₁ _ _
@[simp] lemma disj₁! : 𝓢 ⊢! p ⟶ p ⋎ q := ⟨disj₁⟩

def disj₂ : 𝓢 ⊢ q ⟶ p ⋎ q := Minimal.disj₂ _ _
@[simp] lemma disj₂! : 𝓢 ⊢! q ⟶ p ⋎ q := ⟨disj₂⟩

def disj₃ : 𝓢 ⊢ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q) ⟶ r := Minimal.disj₃ _ _ _
@[simp] lemma disj₃! : 𝓢 ⊢! (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q) ⟶ r := ⟨disj₃⟩

def efq [HasEFQ 𝓢] : 𝓢 ⊢ ⊥ ⟶ p := HasEFQ.efq _
@[simp] lemma efq! [HasEFQ 𝓢] : 𝓢 ⊢! ⊥ ⟶ p := ⟨efq⟩

def efq' [HasEFQ 𝓢] (b : 𝓢 ⊢ ⊥) : 𝓢 ⊢ p := efq ⨀ b
@[simp] lemma efq'! [HasEFQ 𝓢] (h : 𝓢 ⊢! ⊥) : 𝓢 ⊢! p := ⟨efq' h.some⟩

def lem [HasLEM 𝓢] : 𝓢 ⊢ p ⋎ ~p := HasLEM.lem p
@[simp] lemma lem! [HasLEM 𝓢] : 𝓢 ⊢! p ⋎ ~p := ⟨lem⟩

def imply₁' (h : 𝓢 ⊢ p) : 𝓢 ⊢ q ⟶ p := imply₁ ⨀ h
lemma imply₁'! (d : 𝓢 ⊢! p) : 𝓢 ⊢! q ⟶ p := ⟨imply₁' d.some⟩

def dhyp (q : F) (b : 𝓢 ⊢ p) : 𝓢 ⊢ q ⟶ p := imply₁' b

def imply₂' (d₁ : 𝓢 ⊢ p ⟶ q ⟶ r) (d₂ : 𝓢 ⊢ p ⟶ q) (d₃ : 𝓢 ⊢ p) : 𝓢 ⊢ r := imply₂ ⨀ d₁ ⨀ d₂ ⨀ d₃
lemma imply₂'! (d₁ : 𝓢 ⊢! p ⟶ q ⟶ r) (d₂ : 𝓢 ⊢! p ⟶ q) (d₃ : 𝓢 ⊢! p) : 𝓢 ⊢! r := ⟨imply₂' d₁.some d₂.some d₃.some⟩

def conj₁' (d : 𝓢 ⊢ p ⋏ q) : 𝓢 ⊢ p := conj₁ ⨀ d
lemma conj₁'! (d : 𝓢 ⊢! (p ⋏ q)) : 𝓢 ⊢! p := ⟨conj₁' d.some⟩

alias andLeft := conj₁'
alias and_left! := conj₁'!

def conj₂' (d : 𝓢 ⊢ p ⋏ q) : 𝓢 ⊢ q := conj₂ ⨀ d
lemma conj₂'! (d : 𝓢 ⊢! (p ⋏ q)) : 𝓢 ⊢! q := ⟨conj₂' d.some⟩

alias andRight := conj₂'
alias and_right! := conj₂'!

def conj₃' (d₁ : 𝓢 ⊢ p) (d₂: 𝓢 ⊢ q) : 𝓢 ⊢ p ⋏ q := conj₃ ⨀ d₁ ⨀ d₂
lemma conj₃'! (d₁ : 𝓢 ⊢! p) (d₂: 𝓢 ⊢! q) : 𝓢 ⊢! p ⋏ q := ⟨conj₃' d₁.some d₂.some⟩

alias andIntro := conj₃'
alias and_intro! := conj₃'!

def iffIntro (b₁ : 𝓢 ⊢ p ⟶ q) (b₂ : 𝓢 ⊢ q ⟶ p) : 𝓢 ⊢ p ⟷ q := andIntro b₁ b₂
def iff_intro! (h₁ : 𝓢 ⊢! p ⟶ q) (h₂ : 𝓢 ⊢! q ⟶ p) : 𝓢 ⊢! p ⟷ q := ⟨andIntro h₁.some h₂.some⟩

lemma and_intro_iff : 𝓢 ⊢! p ⋏ q ↔ 𝓢 ⊢! p ∧ 𝓢 ⊢! q := ⟨fun h ↦ ⟨and_left! h, and_right! h⟩, fun h ↦ and_intro! h.1 h.2⟩

lemma iff_intro_iff : 𝓢 ⊢! p ⟷ q ↔ 𝓢 ⊢! p ⟶ q ∧ 𝓢 ⊢! q ⟶ p := ⟨fun h ↦ ⟨and_left! h, and_right! h⟩, fun h ↦ and_intro! h.1 h.2⟩

def disj₁' (d : 𝓢 ⊢ p) : 𝓢 ⊢ p ⋎ q := disj₁ ⨀ d
lemma disj₁'! (d : 𝓢 ⊢! p) : 𝓢 ⊢! p ⋎ q := ⟨disj₁' d.some⟩

def disj₂' (d : 𝓢 ⊢ q) : 𝓢 ⊢ p ⋎ q := disj₂ ⨀ d
lemma disj₂'! (d : 𝓢 ⊢! q) : 𝓢 ⊢! p ⋎ q := ⟨disj₂' d.some⟩

def disj₃' (d₁ : 𝓢 ⊢ p ⟶ r) (d₂ : 𝓢 ⊢ q ⟶ r) (d₃ : 𝓢 ⊢ p ⋎ q) : 𝓢 ⊢ r := disj₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
lemma disj₃'! (d₁ : 𝓢 ⊢! p ⟶ r) (d₂ : 𝓢 ⊢! q ⟶ r) (d₃ : 𝓢 ⊢! p ⋎ q) : 𝓢 ⊢! r := ⟨disj₃' d₁.some d₂.some d₃.some⟩

def impId (p : F) : 𝓢 ⊢ p ⟶ p := Minimal.imply₂ p (p ⟶ p) p ⨀ imply₁ ⨀ imply₁
@[simp] def imp_id! : 𝓢 ⊢! p ⟶ p := ⟨impId p⟩

def mdp₁ (bqr : 𝓢 ⊢ p ⟶ q ⟶ r) (bq : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ p ⟶ r := Minimal.imply₂ p q r ⨀ bqr ⨀ bq
lemma mdp₁! (hqr : 𝓢 ⊢! p ⟶ q ⟶ r) (hq : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! p ⟶ r := ⟨mdp₁ hqr.some hq.some⟩

infixl:90 "⨀₁" => mdp₁
infixl:90 "⨀₁" => mdp₁!

def mdp₂ (bqr : 𝓢 ⊢ p ⟶ q ⟶ r ⟶ s) (bq : 𝓢 ⊢ p ⟶ q ⟶ r) : 𝓢 ⊢ p ⟶ q ⟶ s := dhyp p (Minimal.imply₂ q r s) ⨀₁ bqr ⨀₁ bq
lemma mdp₂! (hqr : 𝓢 ⊢! p ⟶ q ⟶ r ⟶ s) (hq : 𝓢 ⊢! p ⟶ q ⟶ r) : 𝓢 ⊢! p ⟶ q ⟶ s := ⟨mdp₂ hqr.some hq.some⟩

infixl:90 "⨀₂" => mdp₂
infixl:90 "⨀₂" => mdp₂!

def mdp₃ (bqr : 𝓢 ⊢ p ⟶ q ⟶ r ⟶ s ⟶ t) (bq : 𝓢 ⊢ p ⟶ q ⟶ r ⟶ s) : 𝓢 ⊢ p ⟶ q ⟶ r ⟶ t := (dhyp p <| dhyp q <| Minimal.imply₂ r s t) ⨀₂ bqr ⨀₂ bq
lemma mdp₃! (hqr : 𝓢 ⊢! p ⟶ q ⟶ r ⟶ s ⟶ t) (hq : 𝓢 ⊢! p ⟶ q ⟶ r ⟶ s) : 𝓢 ⊢! p ⟶ q ⟶ r ⟶ t := ⟨mdp₃ hqr.some hq.some⟩

infixl:90 "⨀₃" => mdp₃
infixl:90 "⨀₃" => mdp₃!

def impTrans (bpq : 𝓢 ⊢ p ⟶ q) (bqr : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ p ⟶ r := imply₂ ⨀ dhyp p bqr ⨀ bpq
lemma imp_trans! (hpq : 𝓢 ⊢! p ⟶ q) (hqr : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! p ⟶ r := ⟨impTrans hpq.some hqr.some⟩

def imply₁₁ (p q r : F) : 𝓢 ⊢ p ⟶ q ⟶ r ⟶ p := impTrans (Minimal.imply₁ p r) (Minimal.imply₁ (r ⟶ p) q)
@[simp] lemma imply₁₁! (p q r : F) : 𝓢 ⊢! p ⟶ q ⟶ r ⟶ p := ⟨imply₁₁ p q r⟩

def generalConj [DecidableEq F] {Γ : List F} {p : F} (h : p ∈ Γ) : 𝓢 ⊢ Γ.conj ⟶ p :=
  match Γ with
  | []     => by simp at h
  | q :: Γ =>
    if e : p = q then cast (by simp [e]) (Minimal.conj₁ p Γ.conj) else
      have : p ∈ Γ := by simpa [e] using h
      impTrans (Minimal.conj₂ q Γ.conj) (generalConj this)

lemma generalConj! [DecidableEq F] {Γ : List F} {p : F} (h : p ∈ Γ) : 𝓢 ⊢! Γ.conj ⟶ p := ⟨generalConj h⟩

def implyAnd (bq : 𝓢 ⊢ p ⟶ q) (br : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⟶ q ⋏ r :=
  dhyp p (Minimal.conj₃ q r) ⨀₁ bq ⨀₁ br

def andComm (p q : F) : 𝓢 ⊢ p ⋏ q ⟶ q ⋏ p := implyAnd conj₂ conj₁

def iffComm (p q : F) : 𝓢 ⊢ (p ⟷ q) ⟶ (q ⟷ p) := andComm _ _

def andImplyIffImplyImply (p q r : F) : 𝓢 ⊢ (p ⋏ q ⟶ r) ⟷ (p ⟶ q ⟶ r) :=
  let b₁ : 𝓢 ⊢ (p ⋏ q ⟶ r) ⟶ p ⟶ q ⟶ r :=
    imply₁₁ (p ⋏ q ⟶ r) p q ⨀₃ dhyp (p ⋏ q ⟶ r) (Minimal.conj₃ p q)
  let b₂ : 𝓢 ⊢ (p ⟶ q ⟶ r) ⟶ p ⋏ q ⟶ r :=
    Minimal.imply₁ (p ⟶ q ⟶ r) (p ⋏ q) ⨀₂ dhyp (p ⟶ q ⟶ r) (Minimal.conj₁ p q) ⨀₂ dhyp (p ⟶ q ⟶ r) (Minimal.conj₂ p q)
  iffIntro b₁ b₂

def implyConj [DecidableEq F] (p : F) (Γ : List F) (b : (q : F) → q ∈ Γ → 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ p ⟶ Γ.conj :=
  match Γ with
  | []     => dhyp p verum
  | q :: Γ => implyAnd (b q (by simp)) (implyConj p Γ (fun q hq ↦ b q (by simp [hq])))

def conjImplyConj [DecidableEq F] {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj ⟶ Δ.conj :=
  implyConj _ _ (fun _ hq ↦ generalConj (h hq))

end LO.System
