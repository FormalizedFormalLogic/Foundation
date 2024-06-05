import Logic.Vorspiel.Vorspiel

/-!
# Logic Symbols

This file defines structure that has logical connectives $\top, \bot, \land, \lor, \to, \lnot$
and their homomorphisms.

## Main Definitions
* `LO.LogicalConnective` is defined so that `LO.LogicalConnective F` is a type that has logical connectives $\top, \bot, \land, \lor, \to, \lnot$.
* `LO.LogicalConnective.Hom` is defined so that `f : F →ˡᶜ G` is a homomorphism from `F` to `G`, i.e.,
a function that preserves logical connectives.

-/

namespace LO

@[notation_class] class SigmaSymbol (α : Type*) where
  sigma : α

@[notation_class] class PiSymbol (α : Type*) where
  pi : α

@[notation_class] class DeltaSymbol (α : Type*) where
  delta : α

notation "𝚺" => SigmaSymbol.sigma

notation "𝚷" => PiSymbol.pi

notation "𝚫" => DeltaSymbol.delta

attribute [match_pattern] SigmaSymbol.sigma PiSymbol.pi DeltaSymbol.delta

inductive Polarity := | sigma | pi

namespace Polarity

instance : SigmaSymbol Polarity := ⟨sigma⟩

instance : PiSymbol Polarity := ⟨pi⟩

def alt : Polarity → Polarity
  | 𝚺 => 𝚷
  | 𝚷 => 𝚺

@[simp] lemma eq_sigma : sigma = 𝚺 := rfl

@[simp] lemma eq_pi : pi = 𝚷 := rfl

@[simp] lemma alt_sigma : alt 𝚺 = 𝚷 := rfl

@[simp] lemma alt_pi : alt 𝚷 = 𝚺 := rfl

@[simp] lemma alt_alt (Γ : Polarity) : Γ.alt.alt = Γ := by rcases Γ <;> simp

end Polarity

inductive SigmaPiDelta := | sigma | pi | delta

namespace SigmaPiDelta

instance : SigmaSymbol SigmaPiDelta := ⟨sigma⟩

instance : PiSymbol SigmaPiDelta := ⟨pi⟩

instance : DeltaSymbol SigmaPiDelta := ⟨delta⟩

def alt : SigmaPiDelta → SigmaPiDelta
  | 𝚺 => 𝚷
  | 𝚷 => 𝚺
  | 𝚫 => 𝚫

@[simp] lemma eq_sigma : sigma = 𝚺 := rfl

@[simp] lemma eq_pi : pi = 𝚷 := rfl

@[simp] lemma eq_delta : delta = 𝚫 := rfl

@[simp] lemma alt_sigma : alt 𝚺 = 𝚷 := rfl

@[simp] lemma alt_pi : alt 𝚷 = 𝚺 := rfl

@[simp] lemma alt_delta : alt 𝚫 = 𝚫 := rfl

@[simp] lemma alt_alt (Γ : SigmaPiDelta) : Γ.alt.alt = Γ := by rcases Γ <;> simp

end SigmaPiDelta

section logicNotation

@[notation_class] class Tilde (α : Type*) where
  tilde : α → α

@[notation_class] class Arrow (α : Type*) where
  arrow : α → α → α

@[notation_class] class Wedge (α : Type*) where
  wedge : α → α → α

@[notation_class] class Vee (α : Type*) where
  vee : α → α → α

class LogicalConnective (α : Type*)
  extends Top α, Bot α, Tilde α, Arrow α, Wedge α, Vee α

@[notation_class] class UnivQuantifier (α : ℕ → Type*) where
  univ : ∀ {n}, α (n + 1) → α n

@[notation_class] class ExQuantifier (α : ℕ → Type*) where
  ex : ∀ {n}, α (n + 1) → α n

@[notation_class] class UnivQuantifier₂ (α : ℕ → ℕ → Type*) where
  univ₂₁ : ∀ {m n}, α (m + 1) n → α m n
  univ₂₂ : ∀ {m n}, α m (n + 1) → α m n

@[notation_class] class ExQuantifier₂ (α : ℕ → ℕ → Type*) where
  ex₂₁ : ∀ {m n}, α (m + 1) n → α m n
  ex₂₂ : ∀ {m n}, α m (n + 1) → α m n

prefix:75 "~" => Tilde.tilde

infixr:60 " ⟶ " => Arrow.arrow

infixr:69 " ⋏ " => Wedge.wedge

infixr:68 " ⋎ " => Vee.vee

prefix:64 "∀' " => UnivQuantifier.univ

prefix:64 "∃' " => ExQuantifier.ex

prefix:64 "∀¹ " => UnivQuantifier₂.univ₂₁
prefix:64 "∀² " => UnivQuantifier₂.univ₂₂

prefix:64 "∃¹ " => ExQuantifier₂.ex₂₁
prefix:64 "∃² " => ExQuantifier₂.ex₂₂

attribute [match_pattern]
  Tilde.tilde
  Arrow.arrow
  Wedge.wedge
  Vee.vee
  UnivQuantifier.univ
  ExQuantifier.ex
  UnivQuantifier₂.univ₂₁
  UnivQuantifier₂.univ₂₂
  ExQuantifier₂.ex₂₁
  ExQuantifier₂.ex₂₂

section UnivQuantifier

variable {α : ℕ → Type*} [UnivQuantifier α]

def univClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => univClosure (∀' a)

prefix:64 "∀* " => univClosure

@[simp] lemma univClosure_zero (a : α 0) : ∀* a = a := rfl

lemma univClosure_succ {n} (a : α (n + 1)) : ∀* a = ∀* ∀' a := rfl

def univItr : (k : ℕ) → α (n + k) → α n
  | 0,     a => a
  | k + 1, a => univItr k (∀' a)

notation "∀^[" k "] " p:64 => univItr k p

@[simp] lemma univItr_zero (a : α n) : ∀^[0] a = a := rfl

@[simp] lemma univItr_one (a : α (n + 1)) : ∀^[1] a = ∀' a := rfl

lemma univItr_succ {k} (a : α (n + (k + 1))) : ∀^[k + 1] a = ∀^[k] (∀' a) := rfl

end UnivQuantifier

section ExQuantifier

variable {α : ℕ → Type*} [ExQuantifier α]

def exClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => exClosure (∃' a)

prefix:64 "∃* " => exClosure

@[simp] lemma exClosure_zero (a : α 0) : ∃* a = a := rfl

lemma exClosure_succ {n} (a : α (n + 1)) : ∃* a = ∃* ∃' a := rfl

def exItr : (k : ℕ) → α (n + k) → α n
  | 0,     a => a
  | k + 1, a => exItr k (∃' a)

notation "∃^[" k "] " p:64 => exItr k p

@[simp] lemma exItr_zero (a : α n) : ∃^[0] a = a := rfl

@[simp] lemma exItr_one (a : α (n + 1)) : ∃^[1] a = ∃' a := rfl

lemma exItr_succ {k} (a : α (n + (k + 1))) : ∃^[k + 1] a = ∃^[k] (∃' a) := rfl

end ExQuantifier

section UnivQuantifier₂

section

variable {α : ℕ → Type*} [UnivQuantifier α] [ExQuantifier α]

def quant : Polarity → α (n + 1) → α n
  | 𝚺, p => ∃' p
  | 𝚷, p => ∀' p

@[simp] lemma quant_sigma (p : α (n + 1)) : quant 𝚺 p = ∃' p := rfl

@[simp] lemma quant_pi (p : α (n + 1)) : quant 𝚷 p = ∀' p := rfl

end

variable {α : ℕ → ℕ → Type*} [UnivQuantifier₂ α]

def univClosure₂₁ : {m n : ℕ} → α m n → α 0 n
  | 0,     _, a => a
  | _ + 1, _, a => univClosure₂₁ (∀¹ a)

def univClosure₂₂ : {m n : ℕ} → α m n → α m 0
  | _, 0,     a => a
  | _, _ + 1, a => univClosure₂₂ (∀² a)

@[simp] lemma univClosure₂₁_zero {n} (a : α 0 n) : univClosure₂₁ a = a := rfl

lemma univClosure₂₁_succ {m n} (a : α (m + 1) n) : univClosure₂₁ a = univClosure₂₁ (∀¹ a) := rfl

@[simp] lemma univClosure₂₂_zero {m} (a : α m 0) : univClosure₂₂ a = a := rfl

lemma univClosure₂₂_succ {m n} (a : α m (n + 1)) : univClosure₂₂ a = univClosure₂₂ (∀² a) := rfl

end UnivQuantifier₂

section ExQuantifier₂

variable {α : ℕ → ℕ → Type*} [ExQuantifier₂ α]

def exClosure₂₁ : {m n : ℕ} → α m n → α 0 n
  | 0,     _, a => a
  | _ + 1, _, a => exClosure₂₁ (∃¹ a)

def exClosure₂₂ : {m n : ℕ} → α m n → α m 0
  | _, 0,     a => a
  | _, _ + 1, a => exClosure₂₂ (∃² a)

@[simp] lemma exClosure₂₁_zero {n} (a : α 0 n) : exClosure₂₁ a = a := rfl

lemma exClosure₂₁_succ {m n} (a : α (m + 1) n) : exClosure₂₁ a = exClosure₂₁ (∃¹ a) := rfl

@[simp] lemma exClosure₂₂_zero {m} (a : α m 0) : exClosure₂₂ a = a := rfl

lemma exClosure₂₂_succ {m n} (a : α m (n + 1)) : exClosure₂₂ a = exClosure₂₂ (∃² a) := rfl

end ExQuantifier₂

end logicNotation

class DeMorgan (F : Type*) [LogicalConnective F] where
  verum           : ~(⊤ : F) = ⊥
  falsum          : ~(⊥ : F) = ⊤
  imply (p q : F) : (p ⟶ q) = ~p ⋎ q
  and (p q : F)   : ~(p ⋏ q) = ~p ⋎ ~q
  or (p q : F)    : ~(p ⋎ q) = ~p ⋏ ~q
  neg (p : F)     : ~~p = p

attribute [simp] DeMorgan.verum DeMorgan.falsum DeMorgan.and DeMorgan.or DeMorgan.neg

class NegDefinition (F : Type*) [LogicalConnective F] where
  neg {p : F} : ~p = p ⟶ ⊥

namespace LogicalConnective

section
variable {α : Type*} [LogicalConnective α]

@[match_pattern] def iff (a b : α) := (a ⟶ b) ⋏ (b ⟶ a)

infix:61 " ⟷ " => LogicalConnective.iff

end

@[reducible]
instance PropLogicSymbols : LogicalConnective Prop where
  top := True
  bot := False
  tilde := Not
  arrow := fun P Q => (P → Q)
  wedge := And
  vee := Or

@[simp] lemma Prop.top_eq : ⊤ = True := rfl

@[simp] lemma Prop.bot_eq : ⊥ = False := rfl

@[simp] lemma Prop.neg_eq (p : Prop) : ~ p = ¬p := rfl

@[simp] lemma Prop.arrow_eq (p q : Prop) : (p ⟶ q) = (p → q) := rfl

@[simp] lemma Prop.and_eq (p q : Prop) : (p ⋏ q) = (p ∧ q) := rfl

@[simp] lemma Prop.or_eq (p q : Prop) : (p ⋎ q) = (p ∨ q) := rfl

@[simp] lemma Prop.iff_eq (p q : Prop) : (p ⟷ q) = (p ↔ q) := by simp[LogicalConnective.iff, iff_iff_implies_and_implies]

instance : DeMorgan Prop where
  verum := by simp
  falsum := by simp
  imply := fun _ _ => by simp[imp_iff_not_or]
  and := fun _ _ => by simp[-not_and, not_and_or]
  or := fun _ _ => by simp[not_or]
  neg := fun _ => by simp

class HomClass (F : Type*) (α β : outParam Type*) [LogicalConnective α] [LogicalConnective β] [FunLike F α β] where
  map_top : ∀ (f : F), f ⊤ = ⊤
  map_bot : ∀ (f : F), f ⊥ = ⊥
  map_neg : ∀ (f : F) (p : α), f (~ p) = ~f p
  map_imply : ∀ (f : F) (p q : α), f (p ⟶ q) = f p ⟶ f q
  map_and : ∀ (f : F) (p q : α), f (p ⋏ q) = f p ⋏ f q
  map_or  : ∀ (f : F) (p q : α), f (p ⋎ q) = f p ⋎ f q

attribute [simp] HomClass.map_top HomClass.map_bot HomClass.map_neg HomClass.map_imply HomClass.map_and HomClass.map_or

namespace HomClass

variable (F : Type*) (α β : outParam Type*) [LogicalConnective α] [LogicalConnective β] [FunLike F α β]
variable [HomClass F α β]
variable (f : F) (a b : α)

instance : CoeFun F (fun _ => α → β) := ⟨DFunLike.coe⟩

@[simp] lemma map_iff : f (a ⟷ b) = f a ⟷ f b := by simp[LogicalConnective.iff]

end HomClass

variable (α β γ : Type*) [LogicalConnective α] [LogicalConnective β] [LogicalConnective γ]

structure Hom where
  toTr : α → β
  map_top' : toTr ⊤ = ⊤
  map_bot' : toTr ⊥ = ⊥
  map_neg' : ∀ p, toTr (~ p) = ~toTr p
  map_imply' : ∀ p q, toTr (p ⟶ q) = toTr p ⟶ toTr q
  map_and' : ∀ p q, toTr (p ⋏ q) = toTr p ⋏ toTr q
  map_or'  : ∀ p q, toTr (p ⋎ q) = toTr p ⋎ toTr q

infix:25 " →ˡᶜ " => Hom

namespace Hom
variable {α β γ}

instance : FunLike (α →ˡᶜ β) α β where
  coe := toTr
  coe_injective' := by intro f g h; rcases f; rcases g; simp; exact h

instance : CoeFun (α →ˡᶜ β) (fun _ => α → β) := DFunLike.hasCoeToFun

@[ext] lemma ext (f g : α →ˡᶜ β) (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

instance : HomClass (α →ˡᶜ β) α β where
  map_top := map_top'
  map_bot := map_bot'
  map_neg := map_neg'
  map_imply := map_imply'
  map_and := map_and'
  map_or := map_or'

variable (f : α →ˡᶜ β) (a b : α)

protected def id : α →ˡᶜ α where
  toTr := id
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp

@[simp] lemma app_id (a : α) : LogicalConnective.Hom.id a = a := rfl

def comp (g : β →ˡᶜ γ) (f : α →ˡᶜ β) : α →ˡᶜ γ where
  toTr := g ∘ f
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp

@[simp] lemma app_comp (g : β →ˡᶜ γ) (f : α →ˡᶜ β) (a : α) :
     g.comp f a = g (f a) := rfl

end Hom

section quantifier

variable {α : ℕ → Type*} [(i : ℕ) → LogicalConnective (α i)] [UnivQuantifier α] [ExQuantifier α]

def ball (p : α (n + 1)) (q : α (n + 1)) : α n := ∀' (p ⟶ q)

def bex (p : α (n + 1)) (q : α (n + 1)) : α n := ∃' (p ⋏ q)

notation:64 "∀[" p "] " q => ball p q

notation:64 "∃[" p "] " q => bex p q

end quantifier

class AndOrClosed {F} [LogicalConnective F] (C : F → Prop) where
  verum  : C ⊤
  falsum : C ⊥
  and {f g : F} : C f → C g → C (f ⋏ g)
  or  {f g : F} : C f → C g → C (f ⋎ g)

class Closed {F} [LogicalConnective F] (C : F → Prop) extends AndOrClosed C where
  not {f : F} : C f → C (~f)
  imply {f g : F} : C f → C g → C (f ⟶ g)

attribute [simp] AndOrClosed.verum AndOrClosed.falsum

end LogicalConnective

end LO

open LO

namespace Matrix

section And

variable {α : Type*}
variable [LogicalConnective α] [LogicalConnective β]

def conj : {n : ℕ} → (Fin n → α) → α
  | 0,     _ => ⊤
  | _ + 1, v => v 0 ⋏ conj (vecTail v)

@[simp] lemma conj_nil (v : Fin 0 → α) : conj v = ⊤ := rfl

@[simp] lemma conj_cons {a : α} {v : Fin n → α} : conj (a :> v) = a ⋏ conj v := rfl

@[simp] lemma conj_hom_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
  (f : F) (v : Fin n → α) : f (conj v) = ∀ i, f (v i) := by
  induction' n with n ih <;> simp[conj]
  · simp[ih]; constructor
    · intro ⟨hz, hs⟩ i; cases i using Fin.cases; { exact hz }; { exact hs _ }
    · intro h; exact ⟨h 0, fun i => h _⟩

lemma hom_conj [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) : f (conj v) = conj (f ∘ v) := by
  induction' n with n ih <;> simp[*, conj]

lemma hom_conj' [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) : f (conj v) = conj fun i => f (v i) := hom_conj f v

end And

end Matrix

namespace List

section

variable {α : Type*} [LogicalConnective α]

def conj : List α → α
  | []      => ⊤
  | a :: as => a ⋏ as.conj

@[simp] lemma conj_nil : conj (α := α) [] = ⊤ := rfl

@[simp] lemma conj_cons {a : α} {as : List α} : conj (a :: as) = a ⋏ as.conj := rfl

lemma map_conj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (l : List α) : f l.conj ↔ ∀ a ∈ l, f a := by
  induction l <;> simp[*]

lemma map_conj_append [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (l₁ l₂ : List α) : f (l₁ ++ l₂).conj ↔ f (l₁.conj ⋏ l₂.conj) := by
  induction l₁ <;> induction l₂ <;> aesop;

def disj : List α → α
  | []      => ⊥
  | a :: as => a ⋎ as.disj

@[simp] lemma disj_nil : disj (α := α) [] = ⊥ := rfl

@[simp] lemma disj_cons {a : α} {as : List α} : disj (a :: as) = a ⋎ as.disj := rfl

lemma map_disj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (l : List α) : f l.disj ↔ ∃ a ∈ l, f a := by
  induction l <;> simp[*]

lemma map_disj_append [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (l₁ l₂ : List α) : f (l₁ ++ l₂).disj ↔ f (l₁.disj ⋎ l₂.disj) := by
  induction l₁ <;> induction l₂ <;> aesop;

end


section

variable {F : Type u} [LogicalConnective F]
variable {p q : F}

/-- Remark: `[p].conj' = p ≠ p ⋏ ⊤ = [p].conj` -/
def conj' : List F → F
| [] => ⊤
| [p] => p
| p :: q :: rs => p ⋏ (q :: rs).conj'

@[simp] lemma conj'_nil : conj' (F := F) [] = ⊤ := rfl

@[simp] lemma conj'_singleton : [p].conj' = p := rfl

@[simp] lemma conj'_doubleton : [p, q].conj' = p ⋏ q := rfl

@[simp] lemma conj'_cons_nonempty {a : F} {as : List F} (h : as ≠ []) : (a :: as).conj' = a ⋏ as.conj' := by
  cases as with
  | nil => contradiction;
  | cons q rs => simp [List.conj']

/-- Remark: `[p].disj = p ≠ p ⋎ ⊥ = [p].disj` -/
def disj' : List F → F
| [] => ⊥
| [p] => p
| p :: q :: rs => p ⋎ (q :: rs).disj'

@[simp] lemma disj'_nil : disj' (F := F) [] = ⊥ := rfl

@[simp] lemma disj'_singleton : [p].disj' = p := rfl

@[simp] lemma disj'_doubleton : [p, q].disj' = p ⋎ q := rfl

@[simp] lemma disj'_cons_nonempty {a : F} {as : List F} (h : as ≠ []) : (a :: as).disj' = a ⋎ as.disj' := by
  cases as with
  | nil => contradiction;
  | cons q rs => simp [List.disj']

lemma induction_with_singleton
  {motive : List F → Prop}
  (hnil : motive [])
  (hsingle : ∀ a, motive [a])
  (hcons : ∀ a as, as ≠ [] → motive as → motive (a :: as)) : ∀ as, motive as := by
  intro as;
  induction as with
  | nil => exact hnil;
  | cons a as ih => cases as with
    | nil => exact hsingle a;
    | cons b bs => exact hcons a (b :: bs) (by simp) ih;

end


end List

namespace Finset

section

variable [LogicalConnective α] [DecidableEq α]

noncomputable def conj (s : Finset α) : α := s.toList.conj
prefix:80 "⋀" => Finset.conj

lemma map_conj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (s : Finset α) : f s.conj ↔ ∀ a ∈ s, f a := by
  simpa using List.map_conj f s.toList

lemma map_conj_union [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (s₁ s₂ : Finset α) : f (s₁ ∪ s₂).conj ↔ f (s₁.conj ⋏ s₂.conj) := by
  simp [map_conj];
  constructor;
  . intro h;
    constructor;
    . intro a ha;
      exact h a (Or.inl ha);
    . intro a ha;
      exact h a (Or.inr ha);
  . intro ⟨h₁, h₂⟩ a ha;
    cases ha <;> simp_all;

noncomputable def disj (s : Finset α) : α := s.toList.disj
prefix:80 "⋁" => Finset.disj

lemma map_disj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (s : Finset α) : f s.disj ↔ ∃ a ∈ s, f a := by
  simpa using List.map_disj f s.toList

lemma map_disj_union [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (s₁ s₂ : Finset α) : f (s₁ ∪ s₂).disj ↔ f (s₁.disj ⋎ s₂.disj) := by
  simp [map_disj];
  constructor;
  . rintro ⟨a, h₁ | h₂, hb⟩;
    . left; use a;
    . right; use a;
  . rintro (⟨a₁, h₁⟩ | ⟨a₂, h₂⟩);
    . use a₁; simp_all;
    . use a₂; simp_all;

end

end Finset
