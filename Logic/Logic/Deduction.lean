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
  dtr : Bew (insert p Γ) q → Bew Γ (p ⟶ q)

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

variable [hM : Minimal Bew] [HasDT Bew]
-- variable [HasEFQ Bew] [HasDNE Bew] [HasLEM Bew]
variable {Γ Γ₁ Γ₂ : Set F} {p q r : F}

macro "tautology" : attr =>
  `(attr|aesop 8 safe (rule_sets := [$(Lean.mkIdent `Deduction):ident]))

macro "inference" : attr =>
  `(attr|aesop unsafe (rule_sets := [$(Lean.mkIdent `Deduction):ident]))

@[inference]
def modus_ponens (d₁ : Γ₁ ⊢ p ⟶ q) (d₂ : Γ₂ ⊢ p) : (Γ₁ ∪ Γ₂) ⊢ q := HasModusPonens.modus_ponens d₁ d₂
infixl:90 "⨀" => modus_ponens

 @[inference]
lemma modus_ponens! (d₁ : Γ₁ ⊢! p ⟶ q) (d₂ : Γ₂ ⊢! p) : Γ₁ ∪ Γ₂ ⊢! q := ⟨d₁.some ⨀ d₂.some⟩
infixl:90 "⨀" => modus_ponens!

@[inference, aesop 4 safe forward (rule_sets := [Deduction])]
def modus_ponens₂ (d₁ : Γ ⊢ p ⟶ q) (d₂ : Γ ⊢ p) : Γ ⊢ q := by simpa using d₁ ⨀ d₂
infixl:90 "⨀" => modus_ponens₂

@[inference, aesop 4 safe forward (rule_sets := [Deduction])]
lemma modus_ponens₂! (d₁ : Γ ⊢! (p ⟶ q)) (d₂ : Γ ⊢! p) : Γ ⊢! q := by simpa using modus_ponens! d₁ d₂
infixl:90 "⨀" => modus_ponens₂!

open Lean.Parser.Tactic (config)

macro "deduct" (config)? : tactic =>
  `(tactic| aesop (rule_sets := [$(Lean.mkIdent `Deduction):ident]) (config := { terminal := false }))

macro "deduct?" (config)? : tactic =>
  `(tactic| aesop? (rule_sets := [$(Lean.mkIdent `Deduction):ident]) (config := { terminal := false }))

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

@[inference, aesop 2 safe forward (rule_sets := [Deduction])]
def efq' [HasEFQ Bew] (h : Γ ⊢ ⊥) : Γ ⊢ p := by deduct

@[inference, aesop 2 safe forward (rule_sets := [Deduction])]
lemma efq'! [HasEFQ Bew] (h : Γ ⊢! ⊥) : Γ ⊢! p := ⟨efq' h.some⟩

@[tautology]
def lem [HasLEM Bew] : Γ ⊢ p ⋎ ~p := by apply HasLEM.lem

@[inference, aesop 2 safe forward (rule_sets := [Deduction])]
def axm' (h : p ∈ Γ) : Γ ⊢ p := Deduction.axm h

@[inference, aesop 2 safe forward (rule_sets := [Deduction])]
lemma axm! {Γ : Set F} {f : F} (h : f ∈ Γ) : Γ ⊢! f := ⟨axm' h⟩

@[inference, aesop 2 safe forward (rule_sets := [Deduction])]
def weakening' (h : Γ₁ ⊆ Γ₂) (d : Γ₁ ⊢ p) : Γ₂ ⊢ p := Deduction.weakening' h d

@[inference, aesop 2 safe forward (rule_sets := [Deduction])]
lemma weakening! (h : Γ₁ ⊆ Γ₂) (d : Γ₁ ⊢! p) : Γ₂ ⊢! p := ⟨weakening' h d.some⟩

@[inference, aesop 2 safe forward (rule_sets := [Deduction])]
def weakening'_empty (d : ∅ ⊢ p) : Γ ⊢ p := by deduct

@[inference, aesop 2 safe forward (rule_sets := [Deduction])]
lemma weakening'_empty! (d : ∅ ⊢! p) : Γ ⊢! p := ⟨weakening'_empty d.some⟩

@[inference] def imply₁' (h : Γ ⊢ p) : Γ ⊢ (q ⟶ p) := by deduct
@[inference] lemma imply₁'! (d : Γ ⊢! p) : Γ ⊢! (q ⟶ p) := ⟨imply₁' d.some⟩

@[inference] def imply₂' (d₁ : Γ ⊢ (p ⟶ q ⟶ r)) (d₂ : Γ ⊢ (p ⟶ q)) (d₃ : Γ ⊢ p) : Γ ⊢ r := by deduct
@[inference] lemma imply₂'! {Γ : Set F} {p q r : F} (d₁ : Γ ⊢! (p ⟶ q ⟶ r)) (d₂ : Γ ⊢! (p ⟶ q)) (d₃ : Γ ⊢! p) : Γ ⊢! r := ⟨imply₂' d₁.some d₂.some d₃.some⟩

@[inference] def conj₁' (d : Γ ⊢ p ⋏ q) : Γ ⊢ p := by deduct
lemma conj₁'! (d : Γ ⊢! (p ⋏ q)) : Γ ⊢! p := ⟨conj₁' d.some⟩

@[inference] def conj₂' (d : Γ ⊢ p ⋏ q) : Γ ⊢ q := by deduct
lemma conj₂'! (d : Γ ⊢! (p ⋏ q)) : Γ ⊢! q := ⟨conj₂' d.some⟩

@[inference] def conj₃' (d₁ : Γ ⊢ p) (d₂: Γ ⊢ q) : Γ ⊢ (p ⋏ q) := conj₃ ⨀ d₁ ⨀ d₂
lemma conj₃'! (d₁ : Γ ⊢! p) (d₂: Γ ⊢! q) : Γ ⊢! (p ⋏ q) := ⟨conj₃' d₁.some d₂.some⟩

@[inference]
def disj₁' (d : Γ ⊢ p) : Γ ⊢ (p ⋎ q) := by deduct
lemma disj₁'! (d : Γ ⊢! p) : Γ ⊢! (p ⋎ q) := ⟨disj₁' d.some⟩

@[inference]
def disj₂' (d : Γ ⊢ q) : Γ ⊢ (p ⋎ q) := by deduct
lemma disj₂'! (d : Γ ⊢! q) : Γ ⊢! (p ⋎ q) := ⟨disj₂' d.some⟩

@[inference]
def disj₃' (d₁ : Γ ⊢ (p ⟶ r)) (d₂ : Γ ⊢ (q ⟶ r)) (d₃ : Γ ⊢ (p ⋎ q)) : Γ ⊢ r := disj₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
lemma disj₃'! {Γ : Set F} {p q r : F} (d₁ : Γ ⊢! (p ⟶ r)) (d₂ : Γ ⊢! (q ⟶ r)) (d₃ : Γ ⊢! (p ⋎ q)) : Γ ⊢! r := ⟨disj₃' d₁.some d₂.some d₃.some⟩

def dtl (h : Γ ⊢ p ⟶ q) : (insert p Γ) ⊢ q := modus_ponens₂ (weakening' (by simp) h) (by deduct)
lemma dtl! (d : Γ ⊢! (p ⟶ q)) : (insert p Γ) ⊢! q := ⟨dtl d.some⟩

lemma dtl_not! : ((insert p Γ) ⊬! q) → (Γ ⊬! (p ⟶ q)) := by
  contrapose;
  simp [Undeducible, Deducible];
  intro d;
  exact ⟨dtl d⟩

attribute [aesop [unsafe forward (rule_sets := [Deduction])]]
  dtl
  dtl!
  dtl_not!

def dtr (h : (insert p Γ) ⊢ q) : Γ ⊢ p ⟶ q := HasDT.dtr h
lemma dtr! (d : (insert p Γ) ⊢! q) : Γ ⊢! (p ⟶ q) := ⟨dtr d.some⟩

lemma dtr_not! : (Γ ⊬! (p ⟶ q)) → ((insert p Γ) ⊬! q) := by
  contrapose;
  simp [Undeducible, Deducible];
  intro d;
  exact ⟨dtr d⟩

attribute [aesop [unsafe forward (rule_sets := [Deduction])]]
  dtr
  dtr!
  dtr_not!

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
  apply dtr;
  deduct;

def iff_mp' (d : Γ ⊢ p ⟷ q) : Γ ⊢ (p ⟶ q) := by deduct
lemma iff_mp'! (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (p ⟶ q) := ⟨iff_mp' d.some⟩

def iff_mpr' (d : Γ ⊢ p ⟷ q) : Γ ⊢ (q ⟶ p) := by deduct
lemma iff_mpr'! (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (q ⟶ p) := ⟨iff_mpr' d.some⟩

def iff_right' (dpq : Γ ⊢ (p ⟷ q)) (dp : Γ ⊢ p) : Γ ⊢ q := iff_mp' dpq ⨀ dp
lemma iff_right'! (dpq : Γ ⊢! (p ⟷ q)) (dp : Γ ⊢! p) : Γ ⊢! q := ⟨iff_right' dpq.some dp.some⟩

def iff_left' (dpq : Γ ⊢ (p ⟷ q)) (dq : Γ ⊢ q) : Γ ⊢ p := iff_mpr' dpq ⨀ dq
lemma iff_left'! (dpq : Γ ⊢! (p ⟷ q)) (dq : Γ ⊢! q) : Γ ⊢! p := ⟨iff_left' dpq.some dq.some⟩

attribute [inference, aesop [safe forward (rule_sets := [Deduction])]]
  iff_mp'
  iff_mp'!
  iff_mpr'
  iff_mpr'!
  iff_right'
  iff_right'!
  iff_left'
  iff_left'!

@[inference] def iff_intro' (dpq : Γ ⊢ p ⟶ q) (dqp : Γ ⊢ q ⟶ p) : Γ ⊢ p ⟷ q := by deduct
@[inference] lemma iff_intro! (dpq : Γ ⊢! (p ⟶ q)) (dqp : Γ ⊢! (q ⟶ p)) : Γ ⊢! (p ⟷ q) := ⟨iff_intro' dpq.some dqp.some⟩

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

def imp_trans' (h₁ : Γ ⊢ p ⟶ q) (h₂ : Γ ⊢ q ⟶ r) : Γ ⊢ p ⟶ r := by
  apply dtr;
  have : (insert p Γ) ⊢ p := by deduct;
  have : (insert p Γ) ⊢ q := by deduct;
  have : (insert p Γ) ⊢ r := modus_ponens₂ (weakening' (by simp) h₂) (by assumption);
  assumption

lemma imp_trans'! {Γ : Set F} {p q r : F} (h₁ : Γ ⊢! (p ⟶ q)) (h₂ : Γ ⊢! (q ⟶ r)) : Γ ⊢! (p ⟶ r) := ⟨imp_trans' h₁.some h₂.some⟩

attribute [inference, aesop [safe forward (rule_sets := [Deduction])]]
  imp_trans'
  imp_trans'!

@[tautology]
def dni : Γ ⊢ (p ⟶ ~~p) := by
  simp [NegDefinition.neg]
  apply dtr;
  apply dtr;
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
  apply dtr;
  apply dtr;
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
  deduct;

@[inference]
lemma contra₁'! (d : Γ ⊢! (p ⟶ ~q)) : Γ ⊢! (q ⟶ ~p) := ⟨contra₁' d.some⟩

@[tautology] def contra₁ : Γ ⊢ ((p ⟶ ~q) ⟶ (q ⟶ ~p)) := by deduct;
@[tautology] lemma contra₁! : Γ ⊢! ((p ⟶ ~q) ⟶ (q ⟶ ~p)) := ⟨contra₁⟩

@[inference] def neg_iff' (d : Γ ⊢ (p ⟷ q)) : Γ ⊢ (~p ⟷ ~q) := iff_intro' (by deduct) (by deduct)
@[inference] lemma neg_iff'! (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (~p ⟷ ~q) := ⟨neg_iff' d.some⟩

@[inference]
def contra₂' [HasDNE Bew] (h : Γ ⊢ (~p ⟶ q)) : Γ ⊢ (~q ⟶ p) := by
  have : Γ ⊢ (~q ⟶ ~~p) := by deduct;
  have : Γ ⊢ (~~p ⟶ p) := by deduct;
  deduct;

@[inference]
lemma contra₂'! [HasDNE Bew] (d : Γ ⊢! (~p ⟶ q)) : Γ ⊢! (~q ⟶ p) := ⟨contra₂' d.some⟩

@[tautology] def contra₂ [HasDNE Bew] : Γ ⊢ ((~p ⟶ q) ⟶ (~q ⟶ p)) := by deduct;
@[tautology] lemma contra₂! [HasDNE Bew] : Γ ⊢! ((~p ⟶ q) ⟶ (~q ⟶ p)) := ⟨contra₂⟩

@[inference]
def contra₃' [HasDNE Bew] (h : Γ ⊢ (~p ⟶ ~q)) : Γ ⊢ (q ⟶ p) := by
  have : Γ ⊢ ~~q ⟶ p := by deduct
  have : Γ ⊢ q ⟶ ~~q := by deduct
  deduct;

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
  apply dtr;
  apply dtr;
  have d : (insert q (insert p Γ)) ⊢ p ⟶ q := by deduct;
  simpa using h ⨀ d;

@[inference]
def disj_dn_elim' [HasDNE Bew] (d : Γ ⊢ ~~p ⋎ ~~q) : Γ ⊢ (p ⋎ q) := disj₃'
  (by apply dtr; apply disj₁'; deduct)
  (by apply dtr; apply disj₂'; deduct)
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
  apply dtr;
  exact disj₃' dnp dnq (by deduct);

@[tautology] def conj_neg : Γ ⊢ (~p ⋏ ~q) ⟶ (~(p ⋎ q)) := by deduct;

@[tautology]
def neg_conj [HasDNE Bew] : Γ ⊢ (~(p ⋏ q)) ⟶ (~p ⋎ ~q) := by
  apply contra₂';
  apply dtr;
  exact conj₃' (by apply dtl; deduct) (by apply dtl; deduct);

@[inference] def neg_conj' [HasDNE Bew] (h : Γ ⊢ ~(p ⋏ q)) : Γ ⊢ ~p ⋎ ~q := neg_conj ⨀ h
@[inference] lemma neg_conj'! [HasDNE Bew] (h : Γ ⊢! (~(p ⋏ q))) : Γ ⊢! (~p ⋎ ~q) := ⟨neg_conj' h.some⟩

@[tautology]
def neg_disj [HasDNE Bew] : Γ ⊢ ~(p ⋎ q) ⟶ (~p ⋏ ~q) := by
  apply contra₃';
  apply dtr;
  apply dni';
  exact disj_dn_elim' $ neg_conj' $ (by deduct)

@[inference] def neg_disj' [HasDNE Bew] (h : Γ ⊢ ~(p ⋎ q)) : Γ ⊢ ~p ⋏ ~q := neg_disj ⨀ h

@[inference]
def imp_eq_mpr' [HasEFQ Bew] (h : Γ ⊢ ~p ⋎ q) : Γ ⊢ p ⟶ q := by
  apply dtr;
  have d : (insert p Γ) ⊢ (~p ⟶ q) := by
    apply dtr;
    have hp : (insert (~p) $ insert p Γ) ⊢ p := by deduct
    have hnp : (insert (~p) $ insert p Γ) ⊢ p ⟶ ⊥ := by simpa using axm' (by simp [NegDefinition.neg]);
    exact efq' $ hnp ⨀ hp;
  exact disj₃' d (by deduct) (weakening' (by deduct) h);

@[inference] lemma imp_eq_mpr'! [HasEFQ Bew] (h : Γ ⊢! (~p ⋎ q)) : Γ ⊢! (p ⟶ q) := ⟨imp_eq_mpr' h.some⟩

@[tautology] def imp_eq_mpr [HasEFQ Bew] : Γ ⊢ (~p ⋎ q) ⟶ (p ⟶ q) := by apply dtr; deduct;
@[tautology] lemma imp_eq_mpr! [HasEFQ Bew] : Γ ⊢! (~p ⋎ q) ⟶ (p ⟶ q) := ⟨imp_eq_mpr⟩

@[tautology]
def imp_eq_mp [HasDNE Bew] : Γ ⊢ ((p ⟶ q) ⟶ (~p ⋎ q)) := by
  apply contra₃';
  apply dtr;
  have : (insert (~(~p ⋎ q)) Γ) ⊢ ~~p ⋏ ~q := neg_disj' $ axm' (by simp);
  have : (insert (~(~p ⋎ q)) Γ) ⊢ p := dne' $ conj₁' (by assumption)
  have : (insert (~(~p ⋎ q)) Γ) ⊢ ~q := conj₂' (by assumption)
  sorry;

@[tautology] lemma imp_eq_mp! [HasDNE Bew] : Γ ⊢! ((p ⟶ q) ⟶ (~p ⋎ q)) := ⟨imp_eq_mp⟩

@[inference] def imp_eq_mp' [HasDNE Bew] (h : Γ ⊢ p ⟶ q) : Γ ⊢ (~p ⋎ q) := imp_eq_mp ⨀ h
@[inference] lemma imp_eq_mp'! [HasDNE Bew] (h : Γ ⊢! (p ⟶ q) ) : Γ ⊢! (~p ⋎ q) := ⟨imp_eq_mp' h.some⟩

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
    exact dtr $ disj₁' this;
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

def iff_left_top' (d : Γ ⊢ (⊤ ⟷ p)) : Γ ⊢ p := by deduct;
lemma iff_left_top! (d : Γ ⊢! (⊤ ⟷ p)) : Γ ⊢! p := ⟨iff_left_top' d.some⟩

def iff_right_top' (d : Γ ⊢ (p ⟷ ⊤)) : Γ ⊢ p := by deduct;
lemma iff_right_top! (d : Γ ⊢! (p ⟷ ⊤)) : Γ ⊢! p := ⟨iff_right_top' d.some⟩

def iff_trans' (h₁ : Γ ⊢ (p ⟷ q)) (h₂ : Γ ⊢ (q ⟷ r)) : Γ ⊢ (p ⟷ r) := by
  apply iff_intro';
  . exact imp_trans' (iff_mp' h₁) (iff_mp' h₂);
  . exact imp_trans' (iff_mpr' h₂) (iff_mpr' h₁);

lemma iff_trans'! (h₁ : Γ ⊢! (p ⟷ q)) (h₂ : Γ ⊢! (q ⟷ r)) : Γ ⊢! (p ⟷ r) := ⟨iff_trans' h₁.some h₂.some⟩

attribute [inference, aesop safe forward (rule_sets := [Deduction])]
  iff_left_top'
  iff_left_top!
  iff_right_top'
  iff_right_top!
  iff_trans'
  iff_trans'!

@[tautology] def equiv_dn [HasDNE Bew] : Γ ⊢ p ⟷ ~~p := by deduct
@[tautology] lemma equiv_dn! [HasDNE Bew] : Γ ⊢! p ⟷ ~~p := ⟨equiv_dn⟩

instance [HasDNE Bew] : HasEFQ Bew where
  efq Γ p := by
    have h₁ : (insert ⊥ Γ) ⊢ (⊥ ⟶ (p ⟶ ⊥) ⟶ ⊥) := imply₁
    have h₂ : (insert ⊥ Γ) ⊢ (((p ⟶ ⊥) ⟶ ⊥) ⟶ p) := by
      have : (insert ⊥ Γ) ⊢ (~~p ⟶ p) := dne
      simpa [NegDefinition.neg]
    exact dtr $ h₂ ⨀ (h₁ ⨀ (axm (by simp)));

instance [HasDNE Bew] : Intuitionistic Bew where

instance [HasDNE Bew] : HasLEM Bew where
  lem Γ p := by apply disj_dn_elim'; deduct;

section Finset

variable {Δ Δ₁ Δ₂ : Finset F}

lemma finset_dt! : (Γ ∪ Δ ⊢! p) ↔ (Γ ⊢! (Δ.conj ⟶ p)) := by
  induction Δ using Finset.cons_induction generalizing Γ with
  | empty =>
    simp [Finset.conj];
    constructor;
    . intro h; exact imply₁'! h;
    . intro h; exact imp_top! h;
  | @cons p Δ h IH => sorry;

lemma finset_union_conj'! : (Γ ⊢! (Δ₁ ∪ Δ₂).conj) ↔ (Γ ⊢! (Δ₁.conj ⋏ Δ₂.conj)) := by
  sorry

lemma finset_union_conj! : Γ ⊢! ((Δ₁ ∪ Δ₂).conj ⟷ Δ₁.conj ⋏ Δ₂.conj) := by
  apply iff_intro!;
  . apply dtr!;
    apply finset_union_conj'!.mp
    exact axm! (by simp)
  . apply dtr!;
    apply finset_union_conj'!.mpr
    exact axm! (by simp)

@[inference]
lemma finset_union_disj'! : (Γ ⊢! (Δ₁ ∪ Δ₂).disj) ↔ (Γ ⊢! (Δ₁.disj ⋎ Δ₂.disj)) := by
  sorry;

lemma finset_union_disj! : Γ ⊢! ((Δ₁ ∪ Δ₂).disj ⟷ Δ₁.disj ⋎ Δ₂.disj) := by
  apply iff_intro!;
  . apply dtr!;
    apply finset_union_disj'!.mp
    deduct;
  . apply dtr!;
    apply finset_union_disj'!.mpr
    deduct;

lemma finset_conj_iff! : (Γ ⊢! Δ.conj) ↔ (∀ p ∈ Δ, Γ ⊢! p) := by
  induction Δ using Finset.cons_induction generalizing Γ with
  | empty => simp [Finset.conj]; deduct;
  | @cons p Δ hp IH =>
    have := @IH (insert p Γ);
    constructor;
    . sorry;
    . sorry;

end Finset

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
  exact hConsis $ modus_ponens₂! h₂ h₁;

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
    have : Γ ⊢ ~~p := by simpa [NegDefinition.neg] using (dtr h.some);
    exact ⟨(dne' this)⟩
  . intro h;
    have : Γ ⊢ ((p ⟶ ⊥) ⟶ ⊥) := by simpa [NegDefinition.neg]  using dni' h.some
    exact ⟨by simpa [NegDefinition.neg] using (dtl this)⟩;

lemma consistent_iff_insert_neg [HasDNE Bew] : Consistent Bew (insert (~p) Γ) ↔ (Γ ⊬! p) := (inconsistent_iff_insert_neg).not

lemma consistent_either {Γ : Set F} (hConsis : Consistent Bew Γ) (p) : (Consistent Bew (insert p Γ)) ∨ (Consistent Bew (insert (~p) Γ)) := by
  by_contra hC; simp [Undeducible, not_or, Consistent, NegDefinition.neg] at hC;
  have ⟨Δ₁, hΔ₁, ⟨dΔ₁⟩⟩ := inconsistent_insert hC.1;
  have ⟨Δ₂, hΔ₂, ⟨dΔ₂⟩⟩ := inconsistent_insert hC.2;
  exact consistent_subset_undeducible_falsum hConsis (by aesop) ⟨(dtr dΔ₂) ⨀ (dtr dΔ₁)⟩;

end Consistency

end Hilbert

end LO
