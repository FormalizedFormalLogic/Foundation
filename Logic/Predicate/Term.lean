import Logic.Predicate.Language

variable (L : Language.{u}) (L₁ L₂ L₃ : Language)

inductive SubTerm (μ : Type v) (n : ℕ)
  | fixedVar : Fin n → SubTerm μ n
  | freeVar  : μ → SubTerm μ n
  | func : ∀ {k}, L.func k → (Fin k → SubTerm μ n) → SubTerm μ n

prefix:max "&" => SubTerm.freeVar
prefix:max "#" => SubTerm.fixedVar

variable (μ : Type v) (μ₁ : Type v₁) (μ₂ : Type v₂) (μ₃ : Type v₃)

@[reducible] def Term := SubTerm L μ 0

@[reducible] def SyntacticSubTerm (n : ℕ) := SubTerm L ℕ n

@[reducible] def SyntacticTerm := SyntacticSubTerm L 0

namespace SubTerm
variable {μ μ₁ μ₂ μ₃}

@[reducible] def func! (k) (f : L.func k) (v : Fin k → SubTerm L μ n) := func f v

variable {L}

variable [∀ k, ToString (L.func k)] [∀ k, ToString (L.rel k)] [ToString μ]

def toStr : SubTerm L μ n → String
  | #x       => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x       => "z_{" ++ toString x ++ "}"
  | func f v => "{" ++ toString f ++ "} \\left(" ++ String.funFin_toStr (fun i => toStr (v i)) ++ "\\right)"

instance : ToString (SubTerm L μ n) := ⟨toStr⟩

variable {n n₁ n₂ n₃ m m₁ m₂ m₃ : ℕ}

def bind (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) :
    SubTerm L μ₁ n₁ → SubTerm L μ₂ n₂
  | (#x)       => fixed x    
  | (&x)       => free x
  | (func f v) => func f (fun i => (v i).bind fixed free)

def map (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) : SubTerm L μ₁ n₁ → SubTerm L μ₂ n₂ :=
  bind (fun n => #(fixed n)) (fun m => &(free m))

def subst (t : SubTerm L μ n) : SubTerm L μ (n + 1) →  SubTerm L μ n :=
  bind (fixedVar <: t) freeVar

def fixedSucc : SubTerm L μ n → SubTerm L μ (n + 1) :=
  map Fin.succ id

section bind
variable (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂)

@[simp] lemma bind_freeVar (m : μ₁) : (&m : SubTerm L μ₁ n₁).bind fixed free = free m := rfl

@[simp] lemma bind_fixedVar (n : Fin n₁) : (#n : SubTerm L μ₁ n₁).bind fixed free = fixed n := rfl

@[simp] lemma bind_func {k} (f : L.func k) (v : Fin k → SubTerm L μ₁ n₁) :
    (func f v).bind fixed free = func f (fun i => (v i).bind fixed free) := rfl

end bind

lemma bind_bind
  (fixed₁ : Fin n₁ → SubTerm L μ₂ n₂) (free₁ : μ₁ → SubTerm L μ₂ n₂)
  (fixed₂ : Fin n₂ → SubTerm L μ₃ n₃) (free₂ : μ₂ → SubTerm L μ₃ n₃) (t : SubTerm L μ₁ n₁) :
    (t.bind fixed₁ free₁).bind fixed₂ free₂ = t.bind (fun n => (fixed₁ n).bind fixed₂ free₂) (fun m => (free₁ m).bind fixed₂ free₂) :=
  by induction t <;> simp[*]

section map
variable (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂)

@[simp] lemma map_freeVar (m : μ₁) : (&m : SubTerm L μ₁ n₁).map fixed free = &(free m) := rfl

@[simp] lemma map_fixedVar (n : Fin n₁) : (#n : SubTerm L μ₁ n₁).map fixed free = #(fixed n) := rfl

@[simp] lemma map_func {k} (f : L.func k) (v : Fin k → SubTerm L μ₁ n₁) :
    (func f v).map fixed free = func f (fun i => (v i).map fixed free) := rfl

end map

lemma map_map
  (fixed₁ : Fin n₁ → Fin n₂) (free₁ : μ₁ → μ₂)
  (fixed₂ : Fin n₂ → Fin n₃) (free₂ : μ₂ → μ₃) (t : SubTerm L μ₁ n₁) :
    (t.map fixed₁ free₁).map fixed₂ free₂ = t.map (fixed₂ ∘ fixed₁) (free₂ ∘ free₁) :=
  bind_bind _ _ _ _ _

@[simp] lemma map_id (t) : @map L μ μ n n id id t = t :=
  by induction t <;> simp[*]

@[simp] lemma fixedSucc_fixedVar (x : Fin n) : fixedSucc (#x : SubTerm L μ n) = #(Fin.succ x) := rfl

@[simp] lemma fixedSucc_freeVar (x : μ) : fixedSucc (&x : SubTerm L μ n) = &x := rfl

section Syntactic

/-
  #0 #1 ... #(n - 1) &0 &1 ...
   ↓shift
  #0 #1 ... #(n - 1) &1 &2 &3 ...
-/

def shift : SyntacticSubTerm L n → SyntacticSubTerm L n :=
  map id Nat.succ

def shift_le (s : ℕ) : SyntacticSubTerm L n → SyntacticSubTerm L n :=
  map id (fun m => m + s)

/- 
  #0 #1 ... #(n - 1) #n &0 &1 ...
   ↓push           ↑pull
  #0 #1 ... #(n - 1) &0 &1 &2 ...
 -/

def push : SyntacticSubTerm L (n + 1) → SyntacticSubTerm L n :=
  bind (fixedVar <: &0) (fun m => &(Nat.succ m))

def pull : SyntacticSubTerm L n → SyntacticSubTerm L (n + 1) :=
  bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ freeVar)

@[simp] lemma shift_fixedVar (x : Fin n) : shift (#x : SyntacticSubTerm L n) = #x := rfl

@[simp] lemma shift_freeVar (x : ℕ) : shift (&x : SyntacticSubTerm L n) = &(x + 1) := rfl

@[simp] lemma shift_func {k} (f : L.func k) (v : Fin k → SyntacticSubTerm L n) :
    shift (func f v) = func f (fun i => shift (v i)) := rfl

lemma shift_Injective : Function.Injective (@shift L n) :=
  Function.LeftInverse.injective (g := map id Nat.pred)
    (by intros p; simp[shift, map_map, Function.comp]; exact map_id _)

@[simp] lemma push_fixedVar_castSucc (x : Fin n) : push (#(Fin.castSucc x) : SyntacticSubTerm L (n + 1)) = #x := by simp[push]

@[simp] lemma push_fixedVar_last : push (#(Fin.last n) : SyntacticSubTerm L (n + 1)) = &0 := by simp[push]

@[simp] lemma push_freeVar (x : ℕ) : push (&x : SyntacticSubTerm L (n + 1)) = &(x + 1) := by simp[push]

@[simp] lemma push_func {k} (f : L.func k) (v : Fin k → SyntacticSubTerm L (n + 1)) :
    push (func f v) = func f (fun i => push $ v i) := by simp[push]

@[simp] lemma pull_fixedVar (x : Fin n) : pull (#x : SyntacticSubTerm L n) = #(Fin.castSucc x) := by simp[pull]

@[simp] lemma pull_freeVar_zero : pull (&0 : SyntacticSubTerm L n) = #(Fin.last n) := by simp[pull]

@[simp] lemma pull_freeVar_succ (x : ℕ) : pull (&(x + 1) : SyntacticSubTerm L n) = &x := by simp[pull]

@[simp] lemma pull_func {k} (f : L.func k) (v : Fin k → SyntacticSubTerm L n) :
    pull (func f v) = func f (fun i => pull $ v i) := by simp[pull]

end Syntactic

variable {L : Language} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

def langf : SubTerm L μ n → Finset (Σ k, L.func k)
  | #_       => ∅
  | &_       => ∅
  | func f v => insert ⟨_, f⟩ $ Finset.bunionᵢ Finset.univ (fun i => langf (v i))

variable [DecidableEq μ]

def hasDecEq : (t u : SubTerm L μ n) → Decidable (Eq t u)
  | #x,                   #y                   => by simp; exact decEq x y
  | #_,                   &_                   => isFalse SubTerm.noConfusion
  | #_,                   func _ _             => isFalse SubTerm.noConfusion
  | &_,                   #_                   => isFalse SubTerm.noConfusion
  | &x,                   &y                   => by simp; exact decEq x y
  | &_,                   func _ _             => isFalse SubTerm.noConfusion
  | func _ _,             #_                   => isFalse SubTerm.noConfusion
  | func _ _,             &_                   => isFalse SubTerm.noConfusion
  | @func L μ _ k₁ r₁ v₁, @func L μ _ k₂ r₂ v₂ => by
      by_cases e : k₁ = k₂
      · rcases e with rfl
        exact match decEq r₁ r₂ with
        | isTrue h => by simp[h]; exact Fin.decFinfun _ _ (fun i => hasDecEq (v₁ i) (v₂ i))
        | isFalse h => isFalse (by simp[h])
      · exact isFalse (by simp[e])

instance : DecidableEq (SubTerm L μ n) := hasDecEq

end SubTerm

namespace Language

namespace Hom
variable {L L₁ L₂ L₃} {μ} (Φ : Hom L₁ L₂)

def onTerm (Φ : Hom L₁ L₂) : SubTerm L₁ μ n → SubTerm L₂ μ n
  | #x               => #x
  | &x               => &x
  | SubTerm.func f v => SubTerm.func (Φ.onFunc f) (fun i => onTerm Φ (v i))

@[simp] lemma onTerm_fixedVar (x : Fin n) : Φ.onTerm (#x : SubTerm L₁ μ n) = #x := rfl

@[simp] lemma onTerm_freeVar (x : μ) : Φ.onTerm (&x : SubTerm L₁ μ n) = &x := rfl

@[simp] lemma onTerm_func {k} (f : L₁.func k) (v : Fin k → SubTerm L₁ μ n) :
    Φ.onTerm (SubTerm.func f v) = SubTerm.func (Φ.onFunc f) (fun i => onTerm Φ (v i)) := rfl

end Hom

end Language


