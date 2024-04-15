import Aesop
import Logic.Logic.Init
import Logic.Logic.LogicSymbol

namespace LO

class Deduction {F : Type*} (Bew : Set F → F → Type*) where
  axm : ∀ {f}, f ∈ Γ → Bew Γ f
  weakening' : ∀ {T U f}, T ⊆ U → Bew T f → Bew U f

namespace Deduction

variable {F : Type*} [LogicalConnective F] (Bew : Set F → F → Type*) [Deduction Bew]

variable (Γ : Set F) (p : F)

def Deducible := Nonempty (Bew Γ p)

def Undeducible := ¬Deducible Bew Γ p

def Inconsistent := Deducible Bew Γ ⊥

def Consistent := Undeducible Bew Γ ⊥

variable {Bew Γ p}

lemma not_consistent : ¬Consistent Bew Γ ↔ Deducible Bew Γ ⊥ := by simp [Consistent, Undeducible]

lemma axm! (h : p ∈ Γ) : Deducible Bew Γ p := ⟨axm h⟩

end Deduction

namespace Hilbert

variable {F : Type*} [LogicalConnective F] [DecidableEq F] [NegDefinition F]

section

variable (Bew : Set F → F → Type*)

class HasModusPonens where
  modus_ponens {Γ₁ Γ₂ p q} : Bew Γ₁ (p ⟶ q) → Bew Γ₂ p → Bew (Γ₁ ∪ Γ₂) q

section

variable {Bew : Set F → F → Type*}

def HasModusPonens.of' [Deduction Bew] (b : {Γ : Set F} → {p q : F} → Bew Γ (p ⟶ q) → Bew Γ p → Bew Γ q) : HasModusPonens Bew :=
  ⟨fun {Γ₁ Γ₂ _ _}  b₁ b₂ ↦ b (Deduction.weakening' (Set.subset_union_left Γ₁ Γ₂) b₁) (Deduction.weakening' (Set.subset_union_right Γ₁ Γ₂) b₂)⟩

variable [HasModusPonens Bew]

end

/--
  Minimal Propositional Logic.
-/
class Minimal [NegDefinition F] extends Deduction Bew, HasModusPonens Bew where
  verum  (Γ : Set F)             : Bew Γ ⊤
  imply₁ (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ (q ⟶ p))
  imply₂ (Γ : Set F) (p q r : F) : Bew Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  conj₁  (Γ : Set F) (p q : F)   : Bew Γ (p ⋏ q ⟶ p)
  conj₂  (Γ : Set F) (p q : F)   : Bew Γ (p ⋏ q ⟶ q)
  conj₃  (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ q ⟶ p ⋏ q)
  disj₁  (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ p ⋎ q)
  disj₂  (Γ : Set F) (p q : F)   : Bew Γ (q ⟶ p ⋎ q)
  disj₃  (Γ : Set F) (p q r : F) : Bew Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q) ⟶ r)

/-- Supplymental -/
class HasDT where
  dtr' : Bew (insert p Γ) q → Bew Γ (p ⟶ q)

class HasEFQ where
  efq (Γ : Set F) (p : F) : Bew Γ (⊥ ⟶ p)

class HasWeakLEM where
  wlem (Γ : Set F) (p : F) : Bew Γ (~p ⋎ ~~p)

class HasLEM where
  lem (Γ : Set F) (p : F) : Bew Γ (p ⋎ ~p)

class HasDNE where
  dne (Γ : Set F) (p : F) : Bew Γ (~~p ⟶ p)

class HasDummett where
  dummett (Γ : Set F) (p q : F) : Bew Γ ((p ⟶ q) ⋎ (q ⟶ p))

class HasPeirce where
  peirce (Γ : Set F) (p q : F) : Bew Γ (((p ⟶ q) ⟶ p) ⟶ p)

class Compact where
  compact {Γ p} : (Bew Γ p) → ((Δ : { Δ : Finset F | ↑Δ ⊆ Γ}) × (Bew ↑Δ p))

/--
  Intuitionistic Propositional Logic.

  Modal companion of `𝐒𝟒`
-/
class Intuitionistic extends Minimal Bew, HasEFQ Bew

/--
  Propositional Logic for Weak Law of Excluded Middle.

  Modal companion of `𝐒𝟒.𝟐`
-/
class WeakLEM extends Intuitionistic Bew, HasWeakLEM Bew


/--
  Gödel-Dummett Propositional Logic.

  Modal companion of `𝐒𝟒.𝟑`
-/
class GD extends Intuitionistic Bew, HasDummett Bew

/--
  Classical Propositional Logic.

  Modal companion of `𝐒𝟓`
-/
class Classical extends Minimal Bew, HasDNE Bew

end

variable {Bew : Set F → F → Type*}
local infix:50 " ⊢ " => Bew
local infix:50 " ⊢! " => Deduction.Deducible Bew
local infix:50 " ⊬! " => Deduction.Undeducible Bew

open Deduction

section Deductions

variable [HasModusPonens Bew] [Minimal Bew] [HasDT Bew]
-- variable [HasEFQ Bew] [HasDNE Bew] [HasLEM Bew]
variable {Γ Γ₁ Γ₂ : Set F} {p q r : F}

macro "tautology" : attr =>
  `(attr|aesop 8 safe (rule_sets := [$(Lean.mkIdent `Deduction):ident]))

macro "inference" : attr =>
  `(attr|aesop [unsafe 75% (rule_sets := [$(Lean.mkIdent `Deduction):ident])])

@[inference]
def modus_ponens' (d₁ : Γ₁ ⊢ p ⟶ q) (d₂ : Γ₂ ⊢ p) : (Γ₁ ∪ Γ₂) ⊢ q := HasModusPonens.modus_ponens d₁ d₂
infixl:90 "⨀" => modus_ponens'

 @[inference]
lemma modus_ponens'! (d₁ : Γ₁ ⊢! p ⟶ q) (d₂ : Γ₂ ⊢! p) : Γ₁ ∪ Γ₂ ⊢! q := ⟨d₁.some ⨀ d₂.some⟩
infixl:90 "⨀" => modus_ponens'!

@[inference]
def modus_ponens₂' (d₁ : Γ ⊢ p ⟶ q) (d₂ : Γ ⊢ p) : Γ ⊢ q := by simpa using d₁ ⨀ d₂
infixl:90 "⨀" => modus_ponens₂'

@[inference]
lemma modus_ponens₂'! (d₁ : Γ ⊢! (p ⟶ q)) (d₂ : Γ ⊢! p) : Γ ⊢! q := ⟨d₁.some ⨀ d₂.some⟩
infixl:90 "⨀" => modus_ponens₂'!

open Lean.Parser.Tactic (config)

macro "deduct" (config)? : tactic =>
  `(tactic| aesop (rule_sets := [$(Lean.mkIdent `Deduction):ident]) (config := { terminal := true }))

macro "deduct?" (config)? : tactic =>
  `(tactic| aesop? (rule_sets := [$(Lean.mkIdent `Deduction):ident]) (config := { terminal := true }))

-- set_option trace.aesop true

attribute [aesop 1 (rule_sets := [Deduction]) safe]
  LogicalConnective.iff
  NegDefinition.neg

@[tautology] def verum : Γ ⊢ ⊤ := by apply Minimal.verum
@[tautology] lemma verum! {Γ : Set F} : Γ ⊢! ⊤ := ⟨verum⟩

@[tautology] def imply₁ : Γ ⊢ p ⟶ q ⟶ p := by apply Minimal.imply₁
@[tautology] lemma imply₁! : Γ ⊢! (p ⟶ q ⟶ p) := ⟨imply₁⟩

@[tautology] def imply₂ : Γ ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := by apply Minimal.imply₂
@[tautology] lemma imply₂! : Γ ⊢! ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) := ⟨imply₂⟩

@[tautology] def conj₁ : Γ ⊢ p ⋏ q ⟶ p := by apply Minimal.conj₁
@[tautology] lemma conj₁! : Γ ⊢! (p ⋏ q ⟶ p) := ⟨conj₁⟩

@[tautology] def conj₂ : Γ ⊢ p ⋏ q ⟶ q := by apply Minimal.conj₂
@[tautology] lemma conj₂! : Γ ⊢! (p ⋏ q ⟶ q) := ⟨conj₂⟩

@[tautology] def conj₃ : Γ ⊢ p ⟶ q ⟶ p ⋏ q := by apply Minimal.conj₃
@[tautology] lemma conj₃! : Γ ⊢! (p ⟶ q ⟶ p ⋏ q) := ⟨conj₃⟩

@[tautology] def disj₁ : Γ ⊢ p ⟶ p ⋎ q := by apply Minimal.disj₁
@[tautology] lemma disj₁! : Γ ⊢! (p ⟶ p ⋎ q) := ⟨disj₁⟩

@[tautology] def disj₂ : Γ ⊢ q ⟶ p ⋎ q := by apply Minimal.disj₂
@[tautology] lemma disj₂! : Γ ⊢! (q ⟶ p ⋎ q) := ⟨disj₂⟩

@[tautology] def disj₃ : Γ ⊢ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r := by apply Minimal.disj₃
@[tautology] lemma disj₃! (Γ : Set F) (p q r : F) : Γ ⊢! ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q) ⟶ r) := ⟨disj₃⟩

@[tautology] def efq [HasEFQ Bew] : Γ ⊢ ⊥ ⟶ p := by apply HasEFQ.efq
@[tautology] lemma efq! [HasEFQ Bew] : Γ ⊢! (⊥ ⟶ p) := ⟨efq⟩

@[inference]
def efq' [HasEFQ Bew] (h : Γ ⊢ ⊥) : Γ ⊢ p := by deduct

@[inference]
lemma efq'! [HasEFQ Bew] (h : Γ ⊢! ⊥) : Γ ⊢! p := ⟨efq' h.some⟩

@[tautology]
def lem [HasLEM Bew] : Γ ⊢ p ⋎ ~p := by apply HasLEM.lem

@[inference]
def axm' (h : p ∈ Γ) : Γ ⊢ p := Deduction.axm h

@[inference]
lemma axm! {Γ : Set F} {f : F} (h : f ∈ Γ) : Γ ⊢! f := ⟨axm' h⟩

@[inference]
def weakening' (h : Γ₁ ⊆ Γ₂) (d : Γ₁ ⊢ p) : Γ₂ ⊢ p := Deduction.weakening' h d

@[inference]
lemma weakening! (h : Γ₁ ⊆ Γ₂) (d : Γ₁ ⊢! p) : Γ₂ ⊢! p := ⟨weakening' h d.some⟩

@[inference]
def weakening'_empty (d : ∅ ⊢ p) : Γ ⊢ p := by deduct

@[inference]
lemma weakening'_empty! (d : ∅ ⊢! p) : Γ ⊢! p := ⟨weakening'_empty d.some⟩

@[inference] def imply₁' (h : Γ ⊢ p) : Γ ⊢ (q ⟶ p) := imply₁ ⨀ h
@[inference] lemma imply₁'! (d : Γ ⊢! p) : Γ ⊢! (q ⟶ p) := ⟨imply₁' d.some⟩

@[inference] def imply₂' (d₁ : Γ ⊢ (p ⟶ q ⟶ r)) (d₂ : Γ ⊢ (p ⟶ q)) (d₃ : Γ ⊢ p) : Γ ⊢ r := imply₂ ⨀ d₁ ⨀ d₂ ⨀ d₃
@[inference] lemma imply₂'! {Γ : Set F} {p q r : F} (d₁ : Γ ⊢! (p ⟶ q ⟶ r)) (d₂ : Γ ⊢! (p ⟶ q)) (d₃ : Γ ⊢! p) : Γ ⊢! r := ⟨imply₂' d₁.some d₂.some d₃.some⟩

@[inference] def conj₁' (d : Γ ⊢ p ⋏ q) : Γ ⊢ p := conj₁ ⨀ d
lemma conj₁'! (d : Γ ⊢! (p ⋏ q)) : Γ ⊢! p := ⟨conj₁' d.some⟩

@[inference] def conj₂' (d : Γ ⊢ p ⋏ q) : Γ ⊢ q := conj₂ ⨀ d
lemma conj₂'! (d : Γ ⊢! (p ⋏ q)) : Γ ⊢! q := ⟨conj₂' d.some⟩

@[inference] def conj₃' (d₁ : Γ ⊢ p) (d₂: Γ ⊢ q) : Γ ⊢ (p ⋏ q) := conj₃ ⨀ d₁ ⨀ d₂
lemma conj₃'! (d₁ : Γ ⊢! p) (d₂: Γ ⊢! q) : Γ ⊢! (p ⋏ q) := ⟨conj₃' d₁.some d₂.some⟩

@[inference]
def disj₁' (d : Γ ⊢ p) : Γ ⊢ (p ⋎ q) := disj₁ ⨀ d
lemma disj₁'! (d : Γ ⊢! p) : Γ ⊢! (p ⋎ q) := ⟨disj₁' d.some⟩

@[inference]
def disj₂' (d : Γ ⊢ q) : Γ ⊢ (p ⋎ q) := disj₂ ⨀ d
lemma disj₂'! (d : Γ ⊢! q) : Γ ⊢! (p ⋎ q) := ⟨disj₂' d.some⟩

@[inference]
def disj₃' (d₁ : Γ ⊢ (p ⟶ r)) (d₂ : Γ ⊢ (q ⟶ r)) (d₃ : Γ ⊢ (p ⋎ q)) : Γ ⊢ r := disj₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
lemma disj₃'! {Γ : Set F} {p q r : F} (d₁ : Γ ⊢! (p ⟶ r)) (d₂ : Γ ⊢! (q ⟶ r)) (d₃ : Γ ⊢! (p ⋎ q)) : Γ ⊢! r := ⟨disj₃' d₁.some d₂.some d₃.some⟩

@[inference] def dtl' (h : Γ ⊢ p ⟶ q) : (insert p Γ) ⊢ q := (show (insert p Γ) ⊢ (p ⟶ q) by deduct) ⨀ (by deduct)
@[inference] lemma dtl'! (d : Γ ⊢! (p ⟶ q)) : (insert p Γ) ⊢! q := ⟨dtl' d.some⟩

@[inference]
lemma dtl_not'! : ((insert p Γ) ⊬! q) → (Γ ⊬! (p ⟶ q)) := by
  contrapose;
  simp [Undeducible, Deducible];
  intro d;
  exact ⟨dtl' d⟩

@[inference] def dtr' (h : (insert p Γ) ⊢ q) : Γ ⊢ p ⟶ q := HasDT.dtr' h
@[inference] lemma dtr'! (d : (insert p Γ) ⊢! q) : Γ ⊢! (p ⟶ q) := ⟨dtr' d.some⟩

@[inference]
lemma dtr_not'! : (Γ ⊬! (p ⟶ q)) → ((insert p Γ) ⊬! q) := by
  contrapose;
  simp [Undeducible, Deducible];
  intro d;
  exact ⟨dtr' d⟩

@[tautology]
def imp_id : Γ ⊢ p ⟶ p := by
  have : Γ ⊢ (p ⟶ (p ⟶ p) ⟶ p) ⟶ (p ⟶ (p ⟶ p)) ⟶ p ⟶ p := imply₂;
  exact (by assumption) ⨀ imply₁ ⨀ imply₁;

@[tautology] lemma imp_id! : Γ ⊢! p ⟶ p := ⟨imp_id⟩

@[aesop 4 safe (rule_sets := [Deduction])]
def id_insert : (insert p Γ) ⊢ p := by deduct

@[aesop 4 safe (rule_sets := [Deduction])]
def id_singleton : {p} ⊢ p := by deduct

@[aesop unsafe 90% (rule_sets := [Deduction])]
def liftup (h : ∀ {Γ}, Γ ⊢ p → Γ ⊢ q) : Γ ⊢ p ⟶ q := by
  apply dtr';
  deduct;

@[inference] def iff_mp' (d : Γ ⊢ p ⟷ q) : Γ ⊢ (p ⟶ q) := by deduct
@[inference] lemma iff_mp'! (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (p ⟶ q) := ⟨iff_mp' d.some⟩

@[inference] def iff_mpr' (d : Γ ⊢ p ⟷ q) : Γ ⊢ (q ⟶ p) := by deduct
@[inference] lemma iff_mpr'! (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (q ⟶ p) := ⟨iff_mpr' d.some⟩

@[inference] def iff_right' (dpq : Γ ⊢ (p ⟷ q)) (dp : Γ ⊢ p) : Γ ⊢ q := iff_mp' dpq ⨀ dp
@[inference] lemma iff_right'! (dpq : Γ ⊢! (p ⟷ q)) (dp : Γ ⊢! p) : Γ ⊢! q := ⟨iff_right' dpq.some dp.some⟩

@[inference] def iff_left' (dpq : Γ ⊢ (p ⟷ q)) (dq : Γ ⊢ q) : Γ ⊢ p := iff_mpr' dpq ⨀ dq
@[inference] lemma iff_left'! (dpq : Γ ⊢! (p ⟷ q)) (dq : Γ ⊢! q) : Γ ⊢! p := ⟨iff_left' dpq.some dq.some⟩

@[inference] def iff_intro' (dpq : Γ ⊢ p ⟶ q) (dqp : Γ ⊢ q ⟶ p) : Γ ⊢ p ⟷ q := by deduct
@[inference] lemma iff_intro'! (dpq : Γ ⊢! (p ⟶ q)) (dqp : Γ ⊢! (q ⟶ p)) : Γ ⊢! (p ⟷ q) := ⟨iff_intro' dpq.some dqp.some⟩

@[inference] def conj_symm' (h : Γ ⊢ p ⋏ q) : Γ ⊢ q ⋏ p := conj₃' (conj₂' h) (conj₁' h)
@[inference] lemma conj_symm'! (d : Γ ⊢! (p ⋏ q)) : Γ ⊢! (q ⋏ p) := ⟨conj_symm' d.some⟩

@[tautology] def conj_symm : Γ ⊢ p ⋏ q ⟶ q ⋏ p := by deduct
@[tautology] lemma conj_symm! : Γ ⊢! (p ⋏ q) ⟶ (q ⋏ p) := ⟨conj_symm⟩

@[tautology] def conj_symm_iff : Γ ⊢ p ⋏ q ⟷ q ⋏ p := by deduct;
@[tautology] lemma conj_symm_iff! : Γ ⊢! (p ⋏ q) ⟷ (q ⋏ p) := ⟨conj_symm_iff⟩

@[inference] def disj_symm' (h : Γ ⊢ p ⋎ q) : Γ ⊢ q ⋎ p := disj₃' disj₂ disj₁ h
@[inference] lemma disj_symm'! (d : Γ ⊢! (p ⋎ q)) : Γ ⊢! (q ⋎ p) := ⟨disj_symm' d.some⟩

@[tautology] def disj_symm : Γ ⊢ (p ⋎ q) ⟶ (q ⋎ p) := by deduct
@[tautology] lemma disj_symm! : Γ ⊢! (p ⋎ q) ⟶ (q ⋎ p) := ⟨disj_symm⟩

@[inference] def iff_symm' (d : Γ ⊢ (p ⟷ q)) : Γ ⊢ (q ⟷ p) := by apply conj_symm'; deduct;
@[inference] lemma iff_symm'! (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (q ⟷ p) := ⟨iff_symm' d.some⟩

@[inference] lemma iff_def! : (Γ ⊢! (p ⟷ q)) ↔ (Γ ⊢! (p ⟶ q)) ∧ (Γ ⊢! (q ⟶ p)) := by constructor <;> deduct

@[inference]
def imp_trans' (h₁ : Γ ⊢ p ⟶ q) (h₂ : Γ ⊢ q ⟶ r) : Γ ⊢ p ⟶ r := by
  apply dtr';
  have : (insert p Γ) ⊢ p := by deduct;
  have : (insert p Γ) ⊢ q := by deduct;
  have : (insert p Γ) ⊢ q ⟶ r := weakening' (by simp) h₂;
  deduct;

@[inference]
lemma imp_trans'! {Γ : Set F} {p q r : F} (h₁ : Γ ⊢! (p ⟶ q)) (h₂ : Γ ⊢! (q ⟶ r)) : Γ ⊢! (p ⟶ r) := ⟨imp_trans' h₁.some h₂.some⟩

@[tautology]
def dni : Γ ⊢ (p ⟶ ~~p) := by
  simp [NegDefinition.neg]
  apply dtr';
  apply dtr';
  deduct;

@[tautology] lemma dni! : Γ ⊢! (p ⟶ ~~p) := ⟨dni⟩

@[inference] def dni' (h : Γ ⊢ p) : Γ ⊢ (~~p) := by deduct
@[inference] lemma dni'! {Γ : Set F} {p} (d : Γ ⊢! p) : Γ ⊢! (~~p) := ⟨dni' d.some⟩

@[tautology] def dne [HasDNE Bew] : Γ ⊢ ~~p ⟶ p := by apply HasDNE.dne
@[tautology] lemma dne! [HasDNE Bew] : Γ ⊢! (~~p ⟶ p) := ⟨dne⟩

@[inference] def dne' [HasDNE Bew] (h : Γ ⊢ (~~p)) : (Γ ⊢ p) := by deduct
@[inference] lemma dne'! [HasDNE Bew] (d : Γ ⊢! (~~p)) : Γ ⊢! p := ⟨dne' d.some⟩

@[inference]
def contra₀' (h : Γ ⊢ (p ⟶ q)) : Γ ⊢ (~q ⟶ ~p) := by
  simp [NegDefinition.neg];
  apply dtr';
  apply dtr';
  have d₁ : (insert p $ insert (q ⟶ ⊥) Γ) ⊢ (q ⟶ ⊥) := by deduct
  have d₂ : (insert p $ insert (q ⟶ ⊥) Γ) ⊢ p := by deduct
  simpa using d₁ ⨀ (h ⨀ d₂);

@[inference]
lemma contra₀'! (d : Γ ⊢! (p ⟶ q)) : Γ ⊢! (~q ⟶ ~p) := ⟨contra₀' d.some⟩

@[tautology] def contra₀ : Γ ⊢ ((p ⟶ q) ⟶ (~q ⟶ ~p)) := by deduct;
@[tautology] lemma contra₀! : Γ ⊢! ((p ⟶ q) ⟶ (~q ⟶ ~p)) := ⟨contra₀⟩

@[inference]
def contra₁' (h : Γ ⊢ p ⟶ ~q) : Γ ⊢ (q ⟶ ~p) := by
  have : Γ ⊢ q ⟶ ~~q := by deduct;
  have : Γ ⊢ ~~q ⟶ ~p := by deduct;
  exact imp_trans' (by assumption) (by assumption);

@[inference]
lemma contra₁'! (d : Γ ⊢! (p ⟶ ~q)) : Γ ⊢! (q ⟶ ~p) := ⟨contra₁' d.some⟩

@[tautology] def contra₁ : Γ ⊢ ((p ⟶ ~q) ⟶ (q ⟶ ~p)) := by deduct;
@[tautology] lemma contra₁! : Γ ⊢! ((p ⟶ ~q) ⟶ (q ⟶ ~p)) := ⟨contra₁⟩

@[inference] def neg_iff' (d : Γ ⊢ (p ⟷ q)) : Γ ⊢ (~p ⟷ ~q) := iff_intro' (by apply contra₀'; deduct) (by apply contra₀'; deduct)
@[inference] lemma neg_iff'! (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (~p ⟷ ~q) := ⟨neg_iff' d.some⟩

@[inference]
def contra₂' [HasDNE Bew] (h : Γ ⊢ (~p ⟶ q)) : Γ ⊢ (~q ⟶ p) := by
  have : Γ ⊢ (~q ⟶ ~~p) := by deduct;
  have : Γ ⊢ (~~p ⟶ p) := by deduct;
  exact imp_trans' (by assumption) (by assumption);

@[inference]
lemma contra₂'! [HasDNE Bew] (d : Γ ⊢! (~p ⟶ q)) : Γ ⊢! (~q ⟶ p) := ⟨contra₂' d.some⟩

@[tautology] def contra₂ [HasDNE Bew] : Γ ⊢ ((~p ⟶ q) ⟶ (~q ⟶ p)) := by deduct;
@[tautology] lemma contra₂! [HasDNE Bew] : Γ ⊢! ((~p ⟶ q) ⟶ (~q ⟶ p)) := ⟨contra₂⟩

@[inference]
def contra₃' [HasDNE Bew] (h : Γ ⊢ (~p ⟶ ~q)) : Γ ⊢ (q ⟶ p) := by
  have : Γ ⊢ ~~q ⟶ p := by deduct
  have : Γ ⊢ q ⟶ ~~q := by deduct
  exact imp_trans' (by assumption) (by assumption);

@[inference]
lemma contra₃'! [HasDNE Bew] (d : Γ ⊢! (~p ⟶ ~q)) : Γ ⊢! (q ⟶ p) := ⟨contra₃' d.some⟩

@[tautology] def contra₃ [HasDNE Bew] : Γ ⊢ ((~p ⟶ ~q) ⟶ (q ⟶ p)) := by deduct;
@[tautology] lemma contra₃! [HasDNE Bew] : Γ ⊢! ((~p ⟶ ~q) ⟶ (q ⟶ p)) := ⟨contra₃⟩

@[tautology] def dn [HasDNE Bew] : Γ ⊢ (p ⟷ ~~p) := by deduct
@[tautology] lemma dn! [HasDNE Bew] : Γ ⊢! (p ⟷ ~~p) := ⟨dn⟩

@[inference]
def dn_iff' (d : Γ ⊢ (p ⟷ q)) : Γ ⊢ (~~p ⟷ ~~q) := by
  apply iff_intro';
  . apply contra₀';
    apply contra₀';
    exact iff_mp' d;
  . apply contra₀';
    apply contra₀';
    exact iff_mpr' d;

@[inference] lemma dn_iff'! (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (~~p ⟷ ~~q) := ⟨dn_iff' d.some⟩

@[inference]
def assoc_conj_left' (h : Γ ⊢ ((p ⋏ q) ⋏ r)) : Γ ⊢ (p ⋏ (q ⋏ r)) := by
  have dpq := conj₁' h;
  have dp := conj₁' dpq;
  have dq := conj₂' dpq;
  have dr := conj₂' h;
  exact conj₃' dp (conj₃' dq dr)

@[tautology] def assoc_conj_left : Γ ⊢ ((p ⋏ q) ⋏ r ⟶ p ⋏ (q ⋏ r)) := by deduct

@[tautology]
def assoc_conj_right' (h : Γ ⊢ (p ⋏ (q ⋏ r))) : Γ ⊢ ((p ⋏ q) ⋏ r) := by
  have dp := conj₁' h;
  have dqr := conj₂' h;
  have dq := conj₁' dqr;
  have dr := conj₂' dqr;
  exact conj₃' (conj₃' dp dq) dr

@[tautology] def assoc_conj_right : Γ ⊢ (p ⋏ (q ⋏ r) ⟶ (p ⋏ q) ⋏ r) := by deduct

@[tautology] def assoc_conj : Γ ⊢ (p ⋏ q) ⋏ r ⟷ p ⋏ (q ⋏ r) := by deduct

@[inference]
def imp_assoc_right' (h : Γ ⊢ (p ⟶ q) ⟶ r) : Γ ⊢ p ⟶ q ⟶ r := by
  apply dtr';
  apply dtr';
  have d : (insert q (insert p Γ)) ⊢ p ⟶ q := by deduct;
  simpa using h ⨀ d;

@[inference]
def conj_dn_intro' (d : Γ ⊢ p ⋏ q) : Γ ⊢ ~~p ⋏ ~~q := by
  apply conj₃' (by apply dni'; deduct) (by apply dni'; deduct);

@[inference]
def disj_dn_elim' [HasDNE Bew] (d : Γ ⊢ ~~p ⋎ ~~q) : Γ ⊢ (p ⋎ q) := disj₃'
  (by apply dtr'; apply disj₁'; deduct)
  (by apply dtr'; apply disj₂'; deduct)
  d

@[inference] def disj_neg' (h : Γ ⊢ (~p ⋎ ~q)) : Γ ⊢ (~(p ⋏ q)) := disj₃' (by deduct) (by deduct) h

@[tautology] def disj_neg : Γ ⊢ (~p ⋎ ~q) ⟶ (~(p ⋏ q)) := by deduct;

@[tautology] def conj_to_disj_neg : Γ ⊢ (p ⋏ q) ⟶ (~(~p ⋎ ~q)) := by deduct;

@[inference] def conj_to_disj_neg' (h : Γ ⊢ p ⋏ q) : Γ ⊢ ~(~p ⋎ ~q) := by deduct;

@[inference]
def conj_neg' (h : Γ ⊢ ~p ⋏ ~q) : Γ ⊢ ~(p ⋎ q) := by
  simp [NegDefinition.neg];
  have dnp : (insert (p ⋎ q) Γ) ⊢ p ⟶ ⊥ := by simpa [NegDefinition.neg] using weakening' (show Γ ⊆ insert (p ⋎ q) Γ by simp) $ conj₁' h;
  have dnq : (insert (p ⋎ q) Γ) ⊢ q ⟶ ⊥ := by simpa [NegDefinition.neg] using weakening' (show Γ ⊆ insert (p ⋎ q) Γ by simp) $ conj₂' h;
  apply dtr';
  exact disj₃' dnp dnq (by deduct);

def tne : Bew Γ (~~(~p) ⟶ ~p) := by
  have : Bew Γ (p ⟶ ~~p) := dni;
  have : Bew Γ (~~(~p) ⟶ ~p) := contra₀' (by assumption)
  assumption

lemma tne! : Γ ⊢! ~~(~p) ⟶ ~p := ⟨tne⟩

def tne' : Bew Γ (~~(~p)) → Bew Γ (~p) := modus_ponens₂' tne

lemma tne'! (h : Γ ⊢! ~~(~p)) : Γ ⊢! ~p := ⟨tne' h.some⟩

def imp_swap' {Γ p q r} (h : Bew Γ (p ⟶ q ⟶ r)) : Bew Γ (q ⟶ p ⟶ r) := by
  apply dtr';
  apply dtr';
  rw [(show insert p (insert q Γ) = insert q (insert p Γ) by aesop)];
  apply dtl';
  apply dtl';
  simpa;

@[tautology]
def dn_distribute_imp_left : Bew Γ (~~(p ⟶ q) ⟶ (~~p ⟶ ~~q)) := by
  have : Bew {p ⟶ q} (~~p ⟶ ~~q) := contra₀' $ contra₀' $ axm (by simp);
  have : Bew ∅ ((p ⟶ q) ⟶ ~~p ⟶ ~~q) := dtr' (by simpa);
  have : Bew ∅ (~~p ⟶ (p ⟶ q) ⟶  ~~q) := imp_swap' (by simpa);
  have : Bew {~~p} ((p ⟶ q) ⟶ (~~q)) := by simpa using dtl' this;
  have : Bew {~~p} (~~(p ⟶ q) ⟶ ~~(~~q)) := contra₀' $ contra₀' $ (by assumption);
  have : Bew {~~p} (~~(p ⟶ q) ⟶ ~~q) := imp_trans' (by assumption) $ tne;
  have : Bew ∅ (~~p ⟶ ~~(p ⟶ q) ⟶ ~~q) := dtr' (by simpa);
  have : Bew ∅ (~~(p ⟶ q) ⟶ ~~p ⟶  ~~q) := imp_swap' (by simpa);
  exact weakening' (by simp) this

lemma dn_distribute_imp_left! : Γ ⊢! (~~(p ⟶ q) ⟶ (~~p ⟶ ~~q)) := ⟨dn_distribute_imp_left⟩

def dn_distribute_imp_left' : Γ ⊢ (~~(p ⟶ q)) → Γ ⊢ (~~p ⟶ ~~q) := modus_ponens₂' (dn_distribute_imp_left)

lemma dn_distribute_imp_left'! (h : Γ ⊢! ~~(p ⟶ q)) : Γ ⊢! ~~p ⟶ ~~q := ⟨dn_distribute_imp_left' h.some⟩

def efq_include [HasEFQ Bew] (h₁ : p ∈ Γ) (h₂ : ~p ∈ Γ) : Bew Γ q := by
  have d₁ : Γ ⊢ p := axm h₁;
  have d₂ : Γ ⊢ ~p := axm h₂;
  have : Γ ⊢ ⊥ := (by simpa [NegDefinition.neg] using d₂) ⨀ d₁;
  deduct;

@[tautology]
def imp_intro_of_or [HasEFQ Bew] : Bew Γ ((~p ⋎ q) ⟶ (p ⟶ q)) := by
  have d₁ : Bew Γ (~p ⟶ (p ⟶ q)) := by
    apply dtr';
    apply dtr';
    exact efq_include (show p ∈ insert p (insert (~p) Γ) by simp) (by simp);
  have d₂ : Bew Γ (q ⟶ (p ⟶ q)) := by
    apply dtr';
    apply dtr';
    exact axm (show q ∈ insert p (insert q Γ) by simp);
  exact disj₃ ⨀ d₁ ⨀ d₂

@[tautology]
def neg_or : Bew Γ (~(p ⋎ q) ⟶ (~p ⋏ ~q)) := by
  have d₁ : Bew ∅ (~(p ⋎ q) ⟶ ~p) := contra₀' $ disj₁;
  have d₂ : Bew ∅ (~(p ⋎ q) ⟶ ~q) := contra₀' $ disj₂;
  have : Bew {~(p ⋎ q)} (~p) := by simpa using dtl' d₁;
  have : Bew {~(p ⋎ q)} (~q) := by simpa using dtl' d₂;
  have : Bew ∅ (~(p ⋎ q) ⟶ (~p ⋏ ~q)) := dtr' $ conj₃' (by simpa using dtl' d₁) (by simpa using dtl' d₂);
  exact weakening' (by simp) this;

@[tautology]
def intro_bot_of_and : Bew Γ (p ⋏ ~p ⟶ ⊥) := by
  apply dtr';
  have : Bew {p ⋏ ~p} (p ⋏ ~p) := axm (by simp);
  have : Bew {p ⋏ ~p} p := conj₁' (by assumption);
  have : Bew {p ⋏ ~p} (~p) := conj₂' (by assumption);
  have : Bew {p ⋏ ~p} (p ⟶ ⊥) := by simpa [NegDefinition.neg];
  have : Bew {p ⋏ ~p} ⊥ := (by assumption) ⨀ (by assumption);
  exact weakening' (by simp) this

@[tautology]
def dn_distribute_imp_right [HasEFQ Bew] : Bew Γ ((~~p ⟶ ~~q) ⟶ ~~(p ⟶ q)) := by
  have : Bew ∅ (~(p ⟶ q) ⟶ ~(~p ⋎ q)) := contra₀' $ imp_intro_of_or;
  have : Bew ∅ (~(~p ⋎ q) ⟶ (~~p ⋏ ~q)) := neg_or
  have : Bew ∅ (~(p ⟶ q) ⟶ (~~p ⋏ ~q)) := imp_trans' (by assumption) (by assumption);

  let Γ' := (insert (~(p ⟶ q)) (insert (~~p ⟶ ~~q) Γ));

  have d₁ : Bew Γ' ((~q ⋏ ~~p)) := weakening' (show {~(p ⟶ q)} ⊆ Γ' by aesop) $ conj_symm' $ by simpa using dtl' this;
  have d₂ : Bew Γ' ((~q ⋏ ~~q)) := by
    have dnq : Bew Γ' (~q) := conj₁' d₁;
    have dnnq : Bew Γ' (~~q) := (axm (by aesop)) ⨀ (conj₂' d₁);
    exact conj₃' dnq dnnq;
  have d₃ : Bew Γ' ((~q ⋏ ~~q) ⟶ ⊥) := intro_bot_of_and;
  have : Bew (insert (~(p ⟶ q)) (insert (~~p ⟶ ~~q) Γ)) ⊥ := d₃ ⨀ d₂;

  nth_rw 5 [NegDefinition.neg];
  apply dtr';
  apply dtr';

  assumption;

@[tautology]
lemma dn_disctribute_imp_right! [HasEFQ Bew] : Γ ⊢! ((~~p ⟶ ~~q) ⟶ ~~(p ⟶ q)) := ⟨dn_distribute_imp_right⟩

def dn_distribute_imp_right' [HasEFQ Bew] : Bew Γ (~~p ⟶ ~~q) → Bew Γ (~~(p ⟶ q)) := modus_ponens₂' (dn_distribute_imp_right)

lemma dn_disctribute_imp_right'! [HasEFQ Bew] (d : Γ ⊢! (~~p ⟶ ~~q)) : Γ ⊢! (~~(p ⟶ q)) := ⟨dn_distribute_imp_right' d.some⟩

@[tautology] def conj_neg : Γ ⊢ (~p ⋏ ~q) ⟶ (~(p ⋎ q)) := by deduct;

@[tautology]
def neg_conj [HasDNE Bew] : Γ ⊢ (~(p ⋏ q)) ⟶ (~p ⋎ ~q) := by
  apply contra₂';
  apply dtr';
  exact conj₃' (by apply dtl'; deduct) (by apply dtl'; deduct);

@[inference] def neg_conj' [HasDNE Bew] (h : Γ ⊢ ~(p ⋏ q)) : Γ ⊢ ~p ⋎ ~q := neg_conj ⨀ h
@[inference] lemma neg_conj'! [HasDNE Bew] (h : Γ ⊢! (~(p ⋏ q))) : Γ ⊢! (~p ⋎ ~q) := ⟨neg_conj' h.some⟩

@[tautology]
def neg_disj [HasDNE Bew] : Γ ⊢ ~(p ⋎ q) ⟶ (~p ⋏ ~q) := by
  apply contra₃';
  apply dtr';
  apply dni';
  exact disj_dn_elim' $ neg_conj' $ (by deduct)

@[inference] def neg_disj' [HasDNE Bew] (h : Γ ⊢ ~(p ⋎ q)) : Γ ⊢ ~p ⋏ ~q := neg_disj ⨀ h

@[inference]
def imp_eq_mpr' [HasEFQ Bew] (h : Γ ⊢ ~p ⋎ q) : Γ ⊢ p ⟶ q := by
  apply dtr';
  have d : (insert p Γ) ⊢ (~p ⟶ q) := by
    apply dtr';
    have hp : (insert (~p) $ insert p Γ) ⊢ p := by deduct
    have hnp : (insert (~p) $ insert p Γ) ⊢ p ⟶ ⊥ := by simpa using axm' (by simp [NegDefinition.neg]);
    exact efq' $ hnp ⨀ hp;
  exact disj₃' d (by deduct) (weakening' (by deduct) h);

@[inference] lemma imp_eq_mpr'! [HasEFQ Bew] (h : Γ ⊢! (~p ⋎ q)) : Γ ⊢! (p ⟶ q) := ⟨imp_eq_mpr' h.some⟩

@[tautology] def imp_eq_mpr [HasEFQ Bew] : Γ ⊢ (~p ⋎ q) ⟶ (p ⟶ q) := by apply dtr'; deduct;
@[tautology] lemma imp_eq_mpr! [HasEFQ Bew] : Γ ⊢! (~p ⋎ q) ⟶ (p ⟶ q) := ⟨imp_eq_mpr⟩

@[inference]
def imp_eq_mp' [HasDNE Bew] (h : Γ ⊢ p ⟶ q) : Γ ⊢ (~p ⋎ q) := by
  apply dne';
  rw [NegDefinition.neg];
  apply dtr';
  have : (insert (~(~p ⋎ q)) Γ) ⊢ ~(~p ⋎ q) := by deduct;
  have : (insert (~(~p ⋎ q)) Γ) ⊢ ~~p ⋏ ~q := by deduct;
  have : (insert (~(~p ⋎ q)) Γ) ⊢ ~~p := by deduct;
  have : (insert (~(~p ⋎ q)) Γ) ⊢ ~q := by deduct;
  have : (insert (~(~p ⋎ q)) Γ) ⊢ q ⟶ ⊥ := by simpa [NegDefinition.neg] using this;
  have : (insert (~(~p ⋎ q)) Γ) ⊢ p := by deduct;
  have : (insert (~(~p ⋎ q)) Γ) ⊢ p ⟶ q := weakening' (by simp) h;
  have : (insert (~(~p ⋎ q)) Γ) ⊢ q := this ⨀ (by assumption);
  exact (by assumption) ⨀ this;

@[inference] lemma imp_eq_mp'! [HasDNE Bew] (h : Γ ⊢! (p ⟶ q) ) : Γ ⊢! (~p ⋎ q) := ⟨imp_eq_mp' h.some⟩

@[tautology] def imp_eq_mp [HasDNE Bew] : Γ ⊢ ((p ⟶ q) ⟶ (~p ⋎ q)) := by deduct

@[tautology] lemma imp_eq_mp! [HasDNE Bew] : Γ ⊢! ((p ⟶ q) ⟶ (~p ⋎ q)) := ⟨imp_eq_mp⟩

@[inference] lemma imp_eq! [HasEFQ Bew] [HasDNE Bew] : (Γ ⊢! (p ⟶ q)) ↔ (Γ ⊢! (~p ⋎ q)) := by deduct;

@[inference]
def conj_replace_left' (h₁ : Γ ⊢ p ⋏ q) (h₂ : Γ ⊢ p ⟶ r) : Γ ⊢ r ⋏ q := by
  have dr : Γ ⊢ r := h₂ ⨀ conj₁' h₁;
  have dq : Γ ⊢ q := conj₂' h₁;
  exact conj₃' dr dq;

@[inference] lemma conj_replace_left'! (h₁ : Γ ⊢! (p ⋏ q)) (h₂ : Γ ⊢! (p ⟶ r)) : Γ ⊢! (r ⋏ q) := ⟨conj_replace_left' h₁.some h₂.some⟩

@[inference] def conj_replace_right' (h₁ : Γ ⊢ p ⋏ q) (h₂ : Γ ⊢ q ⟶ r) : Γ ⊢ p ⋏ r := conj_symm' $ conj_replace_left' (conj_symm' h₁) h₂

@[inference] lemma conj_replace_right'! (h₁ : Γ ⊢! (p ⋏ q)) (h₂ : Γ ⊢! (q ⟶ r)) : Γ ⊢! (p ⋏ r) := ⟨conj_replace_right' h₁.some h₂.some⟩

@[inference]
def disj_replace_left' (h₁ : Γ ⊢ p ⋎ q) (h₂ : Γ ⊢ p ⟶ r) : Γ ⊢ r ⋎ q := by
  have dp : Γ ⊢ (p ⟶ (r ⋎ q)) := by
    have : (insert p Γ) ⊢ p := by deduct
    have : (insert p Γ) ⊢ r := (weakening' (by simp) h₂) ⨀ this;
    exact dtr' $ disj₁' this;
  have dq : Γ ⊢ (q ⟶ (r ⋎ q)) := by apply disj₂;
  exact disj₃' dp dq h₁

@[inference] lemma disj_replace_left'! (h₁ : Γ ⊢! (p ⋎ q)) (h₂ : Γ ⊢! (p ⟶ r)) : Γ ⊢! (r ⋎ q) := ⟨disj_replace_left' h₁.some h₂.some⟩

@[inference] def disj_replace_right' (h₁ : Γ ⊢ p ⋎ q) (h₂ : Γ ⊢ q ⟶ r) : Γ ⊢ p ⋎ r := disj_symm' $ disj_replace_left' (disj_symm' h₁) h₂

@[inference] lemma disj_replace_right'! (h₁ : Γ ⊢! (p ⋎ q)) (h₂ : Γ ⊢! (q ⟶ r)) : Γ ⊢! (p ⋎ r) := ⟨disj_replace_right' h₁.some h₂.some⟩

@[inference]
def neg_conj_replace_left [HasDNE Bew] (h₁ : Γ ⊢ ~(p ⋏ q)) (h₂ : Γ ⊢ ~p ⟶ ~r) : Γ ⊢ ~(r ⋏ q) := by
  apply disj_neg';
  exact disj_replace_left' (neg_conj' h₁) h₂

@[inference] lemma neg_conj_replace_left! [HasDNE Bew] (h₁ : Γ ⊢! ~(p ⋏ q)) (h₂ : Γ ⊢! ~p ⟶ ~r) : Γ ⊢! ~(r ⋏ q) := ⟨neg_conj_replace_left h₁.some h₂.some⟩

@[inference]
def neg_conj_replace_right [HasDNE Bew] (h₁ : Γ ⊢ ~(p ⋏ q)) (h₂ : Γ ⊢ ~q ⟶ ~r) : Γ ⊢ ~(p ⋏ r) := by
  apply disj_neg';
  exact disj_replace_right' (neg_conj' h₁) h₂

@[inference] lemma neg_conj_replace_right! [HasDNE Bew] (h₁ : Γ ⊢! ~(p ⋏ q)) (h₂ : Γ ⊢! ~q ⟶ ~r) : Γ ⊢! ~(p ⋏ r) := ⟨neg_conj_replace_right h₁.some h₂.some⟩

@[inference]
def neg_disj_replace_left [HasDNE Bew] (h₁ : Γ ⊢ ~(p ⋎ q)) (h₂ : Γ ⊢ ~p ⟶ ~r) : Γ ⊢ ~(r ⋎ q) := by
  apply conj_neg';
  exact conj_replace_left' (neg_disj' h₁) h₂

@[inference] lemma neg_disj_replace_left! [HasDNE Bew] (h₁ : Γ ⊢! ~(p ⋎ q)) (h₂ : Γ ⊢! ~p ⟶ ~r) : Γ ⊢! ~(r ⋎ q) := ⟨neg_disj_replace_left h₁.some h₂.some⟩

@[inference]
def neg_disj_replace_right [HasDNE Bew] (h₁ : Γ ⊢ ~(p ⋎ q)) (h₂ : Γ ⊢ ~q ⟶ ~r) : Γ ⊢ ~(p ⋎ r) := by
  apply conj_neg';
  exact conj_replace_right' (neg_disj' h₁) h₂

@[inference] lemma neg_disj_replace_right! [HasDNE Bew] (h₁ : Γ ⊢! ~(p ⋎ q)) (h₂ : Γ ⊢! ~q ⟶ ~r) : Γ ⊢! ~(p ⋎ r) := ⟨neg_disj_replace_right h₁.some h₂.some⟩

@[tautology] def iff_id : Γ ⊢ p ⟷ p := by deduct;
@[tautology] lemma iff_id! : Γ ⊢! p ⟷ p := ⟨iff_id⟩

@[inference] def imp_top' (d : Γ ⊢ ⊤ ⟶ p) : Γ ⊢ p := d ⨀ verum
@[inference] lemma imp_top! (d : Γ ⊢! (⊤ ⟶ p)) : Γ ⊢! p := ⟨imp_top' d.some⟩

@[inference] def iff_left_top' (d : Γ ⊢ (⊤ ⟷ p)) : Γ ⊢ p := by deduct;
@[inference] lemma iff_left_top! (d : Γ ⊢! (⊤ ⟷ p)) : Γ ⊢! p := ⟨iff_left_top' d.some⟩

@[inference] def iff_right_top' (d : Γ ⊢ (p ⟷ ⊤)) : Γ ⊢ p := by deduct;
@[inference] lemma iff_right_top! (d : Γ ⊢! (p ⟷ ⊤)) : Γ ⊢! p := ⟨iff_right_top' d.some⟩

@[inference]
def iff_trans' (h₁ : Γ ⊢ (p ⟷ q)) (h₂ : Γ ⊢ (q ⟷ r)) : Γ ⊢ (p ⟷ r) := by
  apply iff_intro';
  . exact imp_trans' (iff_mp' h₁) (iff_mp' h₂);
  . exact imp_trans' (iff_mpr' h₂) (iff_mpr' h₁);

@[inference]  lemma iff_trans'! (h₁ : Γ ⊢! (p ⟷ q)) (h₂ : Γ ⊢! (q ⟷ r)) : Γ ⊢! (p ⟷ r) := ⟨iff_trans' h₁.some h₂.some⟩

@[tautology] def equiv_dn [HasDNE Bew] : Γ ⊢ p ⟷ ~~p := by deduct
@[tautology] lemma equiv_dn! [HasDNE Bew] : Γ ⊢! p ⟷ ~~p := ⟨equiv_dn⟩

instance [HasDNE Bew] : HasEFQ Bew where
  efq Γ p := by
    have h₁ : (insert ⊥ Γ) ⊢ (⊥ ⟶ (p ⟶ ⊥) ⟶ ⊥) := imply₁
    have h₂ : (insert ⊥ Γ) ⊢ (((p ⟶ ⊥) ⟶ ⊥) ⟶ p) := by
      have : (insert ⊥ Γ) ⊢ (~~p ⟶ p) := dne
      simpa [NegDefinition.neg]
    exact dtr' $ h₂ ⨀ (h₁ ⨀ (axm (by simp)));

instance [HasDNE Bew] : Intuitionistic Bew where

instance [HasDNE Bew] : HasLEM Bew where
  lem Γ p := by
    apply disj_dn_elim';
    apply imp_eq_mp';
    apply dni;

def impimp_to_conj' (h : Γ ⊢ p ⟶ q ⟶ r) : Γ ⊢ (p ⋏ q) ⟶ r := by
  apply dtr';
  have : (insert (p ⋏ q) Γ) ⊢ p ⟶ q ⟶ r := weakening' (by simp) h
  exact this ⨀ (by deduct) ⨀ (by deduct)

lemma impimp_to_conj'! (h : Γ ⊢! p ⟶ q ⟶ r) : Γ ⊢! (p ⋏ q) ⟶ r := ⟨impimp_to_conj' h.some⟩

lemma _root_.Set.subset_insert_insert (x y : α) (s : Set α) : s ⊆ (insert x $ insert y s) := by
  have := Set.subset_insert x (insert y s);
  have := Set.subset_insert y s;
  exact Set.Subset.trans (by assumption) (by assumption)

def conj_to_impimp' (h : Γ ⊢ (p ⋏ q) ⟶ r) : Γ ⊢ p ⟶ q ⟶ r := by
  apply dtr';
  apply dtr';
  have d₁ : (insert q $ insert p Γ) ⊢ p ⋏ q := conj₃' (by deduct) (by deduct);
  have d₂ : (insert q $ insert p Γ) ⊢ p ⋏ q ⟶ r := weakening' (by apply Set.subset_insert_insert) h;
  exact d₂ ⨀ d₁;

lemma conj_to_impimp'! (h : Γ ⊢! (p ⋏ q) ⟶ r) : Γ ⊢! p ⟶ q ⟶ r := ⟨conj_to_impimp' h.some⟩

@[inference]
def imp_left_conj_comm' (h : Γ ⊢ (p ⋏ q) ⟶ r) : Γ ⊢ (q ⋏ p) ⟶ r := by
  apply dtr';
  have : (insert (q ⋏ p) Γ) ⊢ (p ⋏ q) ⟶ r := weakening' (by simp) h;
  have : (insert (q ⋏ p) Γ) ⊢ p ⋏ q := conj_symm' (by deduct);
  exact (by assumption) ⨀ this;

@[inference]
lemma imp_left_conj_comm'! (h : Γ ⊢! (p ⋏ q) ⟶ r) : Γ ⊢! (q ⋏ p) ⟶ r := ⟨imp_left_conj_comm' h.some⟩

def conj_iff' (h₁ : Γ ⊢ p₁ ⟷ q₁) (h₂ : Γ ⊢ p₂ ⟷ q₂) : (Γ ⊢ (p₁ ⋏ p₂) ⟷ (q₁ ⋏ q₂)) := by
  apply iff_intro';
  . apply dtr';
    have dp₁q₁ : (insert (p₁ ⋏ p₂) Γ) ⊢ p₁ ⟶ q₁ := weakening' (by simp) $ iff_mp' h₁;
    have dp₂q₂ : (insert (p₁ ⋏ p₂) Γ) ⊢ p₂ ⟶ q₂ := weakening' (by simp) $ iff_mp' h₂;
    exact conj₃' (dp₁q₁ ⨀ (by deduct)) (dp₂q₂ ⨀ (by deduct))
  . apply dtr';
    have dq₁p₁ : (insert (q₁ ⋏ q₂) Γ) ⊢ q₁ ⟶ p₁ := weakening' (by simp) $ iff_mpr' h₁;
    have dq₂p₂ : (insert (q₁ ⋏ q₂) Γ) ⊢ q₂ ⟶ p₂ := weakening' (by simp) $ iff_mpr' h₂;
    exact conj₃' (dq₁p₁ ⨀ (by deduct)) (dq₂p₂ ⨀ (by deduct))

lemma conj_iff'! (h₁ : Γ ⊢! p₁ ⟷ q₁) (h₂ : Γ ⊢! p₂ ⟷ q₂) : Γ ⊢! (p₁ ⋏ p₂) ⟷ (q₁ ⋏ q₂) := ⟨conj_iff' h₁.some h₂.some⟩

def disj_iff' (h₁ : Γ ⊢ p₁ ⟷ q₁) (h₂ : Γ ⊢ p₂ ⟷ q₂) : (Γ ⊢ (p₁ ⋎ p₂) ⟷ (q₁ ⋎ q₂)) := by
  apply iff_intro';
  . apply dtr';
    have dp₁q₁ : (insert p₁ $ insert (p₁ ⋎ p₂) Γ) ⊢ p₁ ⟶ q₁ := weakening' (by apply Set.subset_insert_insert) $ iff_mp' h₁;
    have dp₁ : (insert p₁ $ insert (p₁ ⋎ p₂) Γ) ⊢ p₁ := by deduct;
    have dp₂q₂ : (insert p₂ $ insert (p₁ ⋎ p₂) Γ) ⊢ p₂ ⟶ q₂ := weakening' (by apply Set.subset_insert_insert) $ iff_mp' h₂;
    have dp₂ : (insert p₂ $ insert (p₁ ⋎ p₂) Γ) ⊢ p₂ := by deduct;
    have dp₁p₂ : (insert (p₁ ⋎ p₂) Γ) ⊢ (p₁ ⋎ p₂) := by deduct;
    exact disj₃' (by apply dtr'; apply disj₁'; exact dp₁q₁ ⨀ dp₁) (by apply dtr'; apply disj₂'; exact dp₂q₂ ⨀ dp₂) dp₁p₂;
  . apply dtr';
    have dq₁p₁ : (insert q₁ $ insert (q₁ ⋎ q₂) Γ) ⊢ q₁ ⟶ p₁ := weakening' (by apply Set.subset_insert_insert) $ iff_mpr' h₁;
    have dq₁ : (insert q₁ $ insert (q₁ ⋎ q₂) Γ) ⊢ q₁ := by deduct;
    have dq₂p₂ : (insert q₂ $ insert (q₁ ⋎ q₂) Γ) ⊢ q₂ ⟶ p₂ := weakening' (by apply Set.subset_insert_insert) $ iff_mpr' h₂;
    have dq₂ : (insert q₂ $ insert (q₁ ⋎ q₂) Γ) ⊢ q₂ := by deduct;
    have dq₁q₂ : (insert (q₁ ⋎ q₂) Γ) ⊢ (q₁ ⋎ q₂) := by deduct;
    exact disj₃' (by apply dtr'; apply disj₁'; exact dq₁p₁ ⨀ dq₁) (by apply dtr'; apply disj₂'; exact dq₂p₂ ⨀ dq₂) dq₁q₂;

lemma disj_iff'! (h₁ : Γ ⊢! p₁ ⟷ q₁) (h₂ : Γ ⊢! p₂ ⟷ q₂) : Γ ⊢! (p₁ ⋎ p₂) ⟷ (q₁ ⋎ q₂) := ⟨disj_iff' h₁.some h₂.some⟩

def imp_iff' (h₁ : Γ ⊢ p₁ ⟷ q₁) (h₂ : Γ ⊢ p₂ ⟷ q₂) : (Γ ⊢ (p₁ ⟶ p₂) ⟷ (q₁ ⟶ q₂)) := by
  apply iff_intro';
  . apply dtr';
    apply dtr';
    have hq₁ : (insert q₁ $ insert (p₁ ⟶ p₂) Γ) ⊢ q₁ := by deduct;
    have hq₁p₁ : (insert q₁ $ insert (p₁ ⟶ p₂) Γ) ⊢ q₁ ⟶ p₁ := weakening' (by apply Set.subset_insert_insert) $ iff_mpr' h₁;
    have hp₁p₂ : (insert q₁ $ insert (p₁ ⟶ p₂) Γ) ⊢ p₁ ⟶ p₂ := by deduct;
    have hp₂q₂ : (insert q₁ $ insert (p₁ ⟶ p₂) Γ) ⊢ p₂ ⟶ q₂ := weakening' (by apply Set.subset_insert_insert) $ iff_mp' h₂;
    exact hp₂q₂ ⨀ (hp₁p₂ ⨀ (hq₁p₁ ⨀ hq₁))
  . apply dtr';
    apply dtr';
    have hp₁ : (insert p₁ $ insert (q₁ ⟶ q₂) Γ) ⊢ p₁ := by deduct;
    have hp₁q₁ : (insert p₁ $ insert (q₁ ⟶ q₂) Γ) ⊢ p₁ ⟶ q₁ := weakening' (by apply Set.subset_insert_insert) $ iff_mp' h₁;
    have hq₁q₂ : (insert p₁ $ insert (q₁ ⟶ q₂) Γ) ⊢ q₁ ⟶ q₂ := by deduct;
    have hq₂p₂ : (insert p₁ $ insert (q₁ ⟶ q₂) Γ) ⊢ q₂ ⟶ p₂ := weakening' (by apply Set.subset_insert_insert) $ iff_mpr' h₂;
    exact hq₂p₂ ⨀ (hq₁q₂ ⨀ (hp₁q₁ ⨀ hp₁));

lemma imp_iff'! (h₁ : Γ ⊢! p₁ ⟷ q₁) (h₂ : Γ ⊢! p₂ ⟷ q₂) : Γ ⊢! (p₁ ⟶ p₂) ⟷ (q₁ ⟶ q₂) := ⟨imp_iff' h₁.some h₂.some⟩

end Deductions

section Consistency

variable [hd : Deduction Bew] [HasModusPonens Bew] [HasDT Bew] [Minimal Bew]

lemma consistent_iff_undeducible_falsum : Consistent Bew Γ ↔ (Γ ⊬! ⊥) := Iff.rfl

lemma consistent_no_falsum {Γ} (h : Consistent Bew Γ) : ⊥ ∉ Γ := fun hC ↦ h ⟨hd.axm hC⟩

lemma consistent_of_subset {Γ Δ : Set F} (h : Γ ⊆ Δ) (hConsis : Consistent Bew Δ) : Consistent Bew Γ :=
  fun hD ↦ hConsis ⟨hd.weakening' h hD.some⟩

lemma consistent_of_insert {p} (hConsis : Consistent Bew (insert p Γ)) : Consistent Bew Γ := consistent_of_subset (by simp) hConsis

lemma consistent_no_falsum_subset {Γ Δ} (hConsis : Consistent Bew Γ) (hΔ : Δ ⊆ Γ) : ⊥ ∉ Δ := consistent_no_falsum $ consistent_of_subset hΔ hConsis

lemma consistent_subset_undeducible_falsum {Γ Δ} (hConsis : Consistent Bew Γ) (hΔ : Δ ⊆ Γ) : (Δ ⊬! ⊥) := by
  by_contra hC;
  simp_all [Consistent, Undeducible, Deducible];
  exact hConsis.false $ hd.weakening' hΔ hC.some;

lemma consistent_neither_undeducible {Γ : Set F} (hConsis : Consistent Bew Γ) (p) : (Γ ⊬! p) ∨ (Γ ⊬! ~p) := by
  by_contra hC; simp only [Undeducible, not_or] at hC;
  have h₁ : Γ ⊢! p  := by simpa using hC.1;
  have h₂ : Γ ⊢! p ⟶ ⊥ := by simpa [NegDefinition.neg] using hC.2;
  exact hConsis $ (h₂ ⨀ h₁);

lemma inconsistent_of_deduction {Γ : Set F} (d : Γ ⊢ ⊥) : Inconsistent Bew Γ := ⟨d⟩

lemma inconsistent_of_deducible {Γ : Set F} (d : Γ ⊢! ⊥) : Inconsistent Bew Γ := by simpa [Inconsistent];

lemma inconsistent_insert_falsum  : Inconsistent Bew (insert ⊥ Γ) := ⟨hd.axm (by simp)⟩

lemma inconsistent_insert (h : Inconsistent Bew (insert p Γ)) : (∃ Δ, (Δ ⊆ Γ) ∧ ((insert p Δ) ⊢! ⊥)) := by
  existsi Γ;
  constructor;
  . rfl;
  . exact h;

lemma inconsistent_iff_insert_neg [HasDNE Bew] : Inconsistent Bew (insert (~p) Γ) ↔ (Γ ⊢! p) := by
  constructor;
  . intro h;
    have : Γ ⊢ ~~p := by simpa [NegDefinition.neg] using (dtr' h.some);
    exact ⟨(dne' this)⟩
  . intro h;
    have : Γ ⊢ ((p ⟶ ⊥) ⟶ ⊥) := by simpa [NegDefinition.neg]  using dni' h.some
    exact ⟨by simpa [NegDefinition.neg] using (dtl' this)⟩;

lemma consistent_iff_insert_neg [HasDNE Bew] : Consistent Bew (insert (~p) Γ) ↔ (Γ ⊬! p) := (inconsistent_iff_insert_neg).not

lemma consistent_either {Γ : Set F} (hConsis : Consistent Bew Γ) (p) : (Consistent Bew (insert p Γ)) ∨ (Consistent Bew (insert (~p) Γ)) := by
  by_contra hC; simp [Undeducible, not_or, Consistent, NegDefinition.neg] at hC;
  have ⟨Δ₁, hΔ₁, ⟨dΔ₁⟩⟩ := inconsistent_insert hC.1;
  have ⟨Δ₂, hΔ₂, ⟨dΔ₂⟩⟩ := inconsistent_insert hC.2;
  exact consistent_subset_undeducible_falsum hConsis (by aesop) ⟨(dtr' dΔ₂) ⨀ (dtr' dΔ₁)⟩;

end Consistency

section Finset

variable [hd : Deduction Bew] [HasModusPonens Bew] [HasDT Bew] [Minimal Bew]
variable {Δ Δ₁ Δ₂ : Finset F}

lemma list_conj_iff! {Δ : List F} : (Γ ⊢! Δ.conj) ↔ (∀ p ∈ Δ, Γ ⊢! p) := by
  induction Δ
  case nil => simp [verum!]
  case cons p Δ ih =>
    simp; constructor
    · intro h; exact ⟨conj₁'! h, ih.mp (conj₂'! h)⟩
    · intro h; exact conj₃'! h.1 (ih.mpr h.2)

lemma finset_conj_iff! : (Γ ⊢! Δ.conj) ↔ (∀ p ∈ Δ, Γ ⊢! p) := by
  simp [Finset.conj, list_conj_iff!]

@[inference]
lemma insert_finset_conj'! : Γ ⊢! (insert p Δ).conj ↔ Γ ⊢! p ⋏ Δ.conj := by
  constructor;
  . intro h;
    have h₁ := finset_conj_iff!.mp h;
    exact conj₃'! (h₁ p (by simp)) (by apply finset_conj_iff!.mpr; intro p hp; exact h₁ p (by simp [hp]));
  . intro h;
    have : Γ ⊢! p := conj₁'! h;
    have :  (∀ p ∈ Δ, Γ ⊢! p) := finset_conj_iff!.mp $ conj₂'! h;
    apply finset_conj_iff!.mpr;
    intro q hq;
    cases Finset.mem_insert.mp hq <;> simp_all

@[tautology]
lemma insert_finset_conj! : Γ ⊢! (insert p Δ).conj ⟷ (p ⋏ Δ.conj) := by
  apply iff_intro'!;
  . apply dtr'!;
    apply insert_finset_conj'!.mp;
    deduct;
  . apply dtr'!;
    apply insert_finset_conj'!.mpr;
    deduct;

lemma list_dt! {Δ : List F} : (Γ ∪ Δ.toFinset ⊢! p) ↔ (Γ ⊢! (Δ.conj ⟶ p)) := by
  induction Δ generalizing Γ p with
  | nil =>
    simp [Finset.conj];
    constructor;
    . apply imply₁'!;
    . apply imp_top!;
  | cons q Δ ih =>
    simp;
    constructor;
    . intro h;
      have : Γ ⊢! List.conj Δ ⟶ q ⟶ p := ih.mp (by simpa using dtr'! h);
      have : Γ ⊢! List.conj Δ ⋏ q ⟶ p := impimp_to_conj'! (by assumption);
      exact imp_left_conj_comm'! this;
    . intro h;
      have : (insert q Γ) ⊢! ((List.conj Δ) ⟶ p) := dtl'! $ conj_to_impimp'! h;
      have : (insert q Γ ∪ ↑(List.toFinset Δ)) ⊢! p := ih.mpr (by simpa using this);
      have e : (insert q Γ ∪ ↑(List.toFinset Δ) = insert q (Γ ∪ {a | a ∈ Δ})) := by aesop;
      rw [e] at this;
      assumption;

lemma finset_dt! : (Γ ∪ Δ ⊢! p) ↔ (Γ ⊢! (Δ.conj ⟶ p)) := by
  have : (Γ ∪ Δ.toList.toFinset ⊢! p) ↔ (Γ ⊢! (Δ.toList.conj ⟶ p)) := list_dt!;
  simpa [Finset.toList_toFinset];

lemma finset_union_conj'! : (Γ ⊢! (Δ₁ ∪ Δ₂).conj) ↔ (Γ ⊢! (Δ₁.conj ⋏ Δ₂.conj)) := by
  constructor;
  . intro h;
    have hu := finset_conj_iff!.mp h;
    have : Γ ⊢! Δ₁.conj := by
      apply finset_conj_iff!.mpr;
      intro p hp; exact hu p (by simp_all);
    have : Γ ⊢! Δ₂.conj := by
      apply finset_conj_iff!.mpr;
      intro p hp; exact hu p (by aesop);
    exact conj₃'! (by assumption) (by assumption);
  . intro h;
    have : ∀ p ∈ Δ₁, Γ ⊢! p := finset_conj_iff!.mp $ conj₁'! h;
    have : ∀ p ∈ Δ₂, Γ ⊢! p := finset_conj_iff!.mp $ conj₂'! h;
    apply finset_conj_iff!.mpr;
    intro p hp;
    cases Finset.mem_union.mp hp <;> simp_all;

lemma finset_union_conj! : Γ ⊢! ((Δ₁ ∪ Δ₂).conj ⟷ Δ₁.conj ⋏ Δ₂.conj) := by
  apply iff_intro'!;
  . apply dtr'!;
    apply finset_union_conj'!.mp
    exact axm! (by simp)
  . apply dtr'!;
    apply finset_union_conj'!.mpr
    exact axm! (by simp)

end Finset

end Hilbert

end LO
