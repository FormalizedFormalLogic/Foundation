import Logic.Vorspiel.Vorspiel
import Mathlib.Data.Finset.Basic

structure Language where
  func : Nat → Type u
  rel  : Nat → Type u

variable (L : Language.{u})

inductive SubTerm (μ : Type v) (n : ℕ)
  | fixedVar : Fin n → SubTerm μ n
  | freeVar  : μ → SubTerm μ n
  | func : ∀ {k}, L.func k → (Fin k → SubTerm μ n) → SubTerm μ n

prefix:max "&" => SubTerm.freeVar
prefix:max "#" => SubTerm.fixedVar

inductive SubFormula (μ : Type v) : ℕ → Type (max u v) where
  | verum  {n} : SubFormula μ n
  | falsum {n} : SubFormula μ n
  | rel    {n} : ∀ {k}, L.rel k → (Fin k → SubTerm L μ n) → SubFormula μ n
  | nrel   {n} : ∀ {k}, L.rel k → (Fin k → SubTerm L μ n) → SubFormula μ n
  | and    {n} : SubFormula μ n → SubFormula μ n → SubFormula μ n
  | or     {n} : SubFormula μ n → SubFormula μ n → SubFormula μ n
  | all    {n} : SubFormula μ (n + 1) → SubFormula μ n
  | ex     {n} : SubFormula μ (n + 1) → SubFormula μ n

variable (μ : Type v) (μ₁ : Type v₁) (μ₂ : Type v₂) (μ₃ : Type v₃)

@[reducible] def Term := SubFormula L μ 0

@[reducible] def Formula := SubFormula L μ 0

@[reducible] def Sentence := Formula L Empty

-- Syntactic ... : 証明で使用する項と論理式
@[reducible] def SyntacticSubTerm (n : ℕ) := SubTerm L ℕ n

@[reducible] def SyntacticTerm := SyntacticSubTerm L 0

@[reducible] def SyntacticSubFormula (n : ℕ) := SubFormula L ℕ n

@[reducible] def SyntacticFormula := SyntacticSubFormula L 0

variable {L μ μ₁ μ₂ μ₃}

namespace SubTerm

variable (L)

@[reducible] def func! (k) (f : L.func k) (v : Fin k → SubTerm L μ n) := func f v

variable {L}

variable [∀ k, ToString (L.func k)] [∀ k, ToString (L.rel k)] [ToString μ]

def toStr : SubTerm L μ n → String
  | #x       => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x       => "z_{" ++ toString x ++ "}"
  | func f v => "{" ++ toString f ++ "} \\left(" ++ String.funFin_toStr (fun i => toStr (v i)) ++ "\\right)"

instance : ToString (SubTerm L μ n) := ⟨toStr⟩

end SubTerm

namespace SubFormula
variable {n n₁ n₂ : ℕ}

def neg {n} : SubFormula L μ n → SubFormula L μ n
  | verum    => falsum
  | falsum   => verum
  | rel r v  => nrel r v
  | nrel r v => rel r v
  | and p q  => or (neg p) (neg q)
  | or p q   => and (neg p) (neg q)
  | all p    => ex (neg p)
  | ex p     => all (neg p)

def imp (p q : SubFormula L μ n) : SubFormula L μ n := or (neg p) q

instance : HasLogicSymbols (SubFormula L μ n) where
  neg := neg
  arrow := imp
  and := and
  or := or
  top := verum
  bot := falsum

instance : HasUniv (SubFormula L μ) := ⟨all⟩
instance : HasEx (SubFormula L μ) := ⟨ex⟩

@[simp] lemma neg_top : ¬'(⊤ : SubFormula L μ n) = ⊥ := rfl

@[simp] lemma neg_bot : ¬'(⊥ : SubFormula L μ n) = ⊤ := rfl

@[simp] lemma neg_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) : ¬'(rel r v) = nrel r v := rfl

@[simp] lemma neg_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) : ¬'(nrel r v) = rel r v := rfl

@[simp] lemma neg_and (p q : SubFormula L μ n) : ¬'(p ⋏ q) = ¬'p ⋎ ¬'q := rfl

@[simp] lemma neg_or (p q : SubFormula L μ n) : ¬'(p ⋎ q) = ¬'p ⋏ ¬'q := rfl

@[simp] lemma neg_all (p : SubFormula L μ (n + 1)) : ¬'(∀' p) = ∃' ¬'p := rfl

@[simp] lemma neg_ex (p : SubFormula L μ (n + 1)) : ¬'(∃' p) = ∀' ¬'p := rfl

lemma neg_eq (p : SubFormula L μ n) : ¬'p = neg p := rfl

lemma imp_eq (p q : SubFormula L μ n) : p ⟶ q = ¬'p ⋎ q := rfl

@[simp] lemma all_inj (p q : SubFormula L μ (n + 1)) : ∀' p = ∀' q ↔ p = q :=
  by simp[HasUniv.univ]

@[simp] lemma ex_inj (p q : SubFormula L μ (n + 1)) : ∃' p = ∃' q ↔ p = q :=
  by simp[HasEx.ex]

variable (L)

@[reducible] def rel! (k) (r : L.rel k) (v : Fin k → SubTerm L μ n) := rel r v

variable {L}

@[elab_as_elim]
def cases' {C : ∀ n, SubFormula L μ n → Sort _}
  (hverum  : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel    : ∀ {n l : ℕ} (r : L.rel l) (v : Fin l → SubTerm L μ n), C n (rel r v))
  (hnrel   : ∀ {n l : ℕ} (r : L.rel l) (v : Fin l → SubTerm L μ n), C n (nrel r v))
  (hand    : ∀ {n : ℕ} (p q : SubFormula L μ n), C n (p ⋏ q))
  (hor     : ∀ {n : ℕ} (p q : SubFormula L μ n), C n (p ⋎ q))
  (hall    : ∀ {n : ℕ} (p : SubFormula L μ (n + 1)), C n (∀' p))
  (hex     : ∀ {n : ℕ} (p : SubFormula L μ (n + 1)), C n (∃' p)) :
    ∀ {n : ℕ} (p : SubFormula L μ n), C n p
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and p q  => hand p q
  | _, or p q   => hor p q
  | _, all p    => hall p
  | _, ex p     => hex p

@[elab_as_elim]
def rec' {C : ∀ n, SubFormula L μ n → Sort _}
  (hverum  : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel    : ∀ {n l : ℕ} (r : L.rel l) (v : Fin l → SubTerm L μ n), C n (rel r v))
  (hnrel   : ∀ {n l : ℕ} (r : L.rel l) (v : Fin l → SubTerm L μ n), C n (nrel r v))
  (hand    : ∀ {n : ℕ} (p q : SubFormula L μ n), C n p → C n q → C n (p ⋏ q))
  (hor     : ∀ {n : ℕ} (p q : SubFormula L μ n), C n p → C n q → C n (p ⋎ q))
  (hall    : ∀ {n : ℕ} (p : SubFormula L μ (n + 1)), C (n + 1) p → C n (∀' p))
  (hex     : ∀ {n : ℕ} (p : SubFormula L μ (n + 1)), C (n + 1) p → C n (∃' p)) :
    ∀ {n : ℕ} (p : SubFormula L μ n), C n p
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and p q  => hand p q (rec' hverum hfalsum hrel hnrel hand hor hall hex p) (rec' hverum hfalsum hrel hnrel hand hor hall hex q)
  | _, or p q   => hor p q (rec' hverum hfalsum hrel hnrel hand hor hall hex p) (rec' hverum hfalsum hrel hnrel hand hor hall hex q)
  | _, all p    => hall p (rec' hverum hfalsum hrel hnrel hand hor hall hex p)
  | _, ex p     => hex p (rec' hverum hfalsum hrel hnrel hand hor hall hex p)

variable [∀ k, ToString (L.func k)] [∀ k, ToString (L.rel k)] [ToString μ]

def toStr : ∀ {n}, SubFormula L μ n → String
  | _, ⊤            => "\\top"
  | _, ⊥            => "\\bot"
  | _, rel r v      => "{" ++ toString r ++ "} \\left(" ++ String.funFin_toStr (fun i => toString (v i)) ++ "\\right)"
  | _, nrel r v     => "\\cancel{" ++ toString r ++ "} \\left(" ++ String.funFin_toStr (fun i => toString (v i)) ++ "\\right)"
  | _, p ⋏ q        => toStr p ++ " \\land " ++ toStr q
  | _, p ⋎ q        => toStr p ++ " \\lor " ++ toStr q
  | _, @all _ _ n p => "\\forall x_{" ++ toString n ++ "} \\left[" ++ toStr p ++ "\\right]"
  | _, @ex _ _ n p  => "\\exists x_{" ++ toString n ++ "} \\left[" ++ toStr p ++ "\\right]"

instance : ToString (SubFormula L μ n) := ⟨toStr⟩

end SubFormula

namespace SubTerm
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

@[simp] lemma bind_function {k} (f : L.func k) (v : Fin k → SubTerm L μ₁ n₁) :
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

@[simp] lemma map_function {k} (f : L.func k) (v : Fin k → SubTerm L μ₁ n₁) :
    (func f v).map fixed free = func f (fun i => (v i).map fixed free) := rfl

lemma map_map
  (fixed₁ : Fin n₁ → Fin n₂) (free₁ : μ₁ → μ₂)
  (fixed₂ : Fin n₂ → Fin n₃) (free₂ : μ₂ → μ₃) (t : SubTerm L μ₁ n₁) :
    (t.map fixed₁ free₁).map fixed₂ free₂ = t.map (fixed₂ ∘ fixed₁) (free₂ ∘ free₁) :=
  bind_bind _ _ _ _ _

end map

@[simp] lemma fixedSucc_fixedVar (x : Fin n) : fixedSucc (#x : SubTerm L μ n) = #(Fin.succ x) := rfl

@[simp] lemma fixedSucc_freeVar (x : μ) : fixedSucc (&x : SubTerm L μ n) = &x := rfl

section syntactic

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
  bind (fun x => #(Fin.castSucc x)) (fun x => match x with | 0 => #(Fin.last n) | x + 1 => &x)

@[simp] lemma push_fixedVar_castSucc (x : Fin n) : push (#(Fin.castSucc x) : SyntacticSubTerm L (n + 1)) = #x := by simp[push]

@[simp] lemma push_fixedVar_last : push (#(Fin.last n) : SyntacticSubTerm L (n + 1)) = &0 := by simp[push]

@[simp] lemma push_freeVar (x : ℕ) : push (&x : SyntacticSubTerm L (n + 1)) = &(x + 1) := by simp[push]

@[simp] lemma push_function {k} (f : L.func k) (v : Fin k → SyntacticSubTerm L (n + 1)) :
    push (func f v) = func f (fun i => push $ v i) := by simp[push]

@[simp] lemma pull_fixedVar (x : Fin n) : pull (#x : SyntacticSubTerm L n) = #(Fin.castSucc x) := by simp[pull]

@[simp] lemma pull_freeVar_zero : pull (&0 : SyntacticSubTerm L n) = #(Fin.last n) := by simp[pull]

@[simp] lemma pull_freeVar_succ (x : ℕ) : pull (&(x + 1) : SyntacticSubTerm L n) = &x := by simp[pull]

@[simp] lemma pull_function {k} (f : L.func k) (v : Fin k → SyntacticSubTerm L n) :
    pull (func f v) = func f (fun i => pull $ v i) := by simp[pull]

end syntactic

end SubTerm

namespace SubFormula
variable {n n₁ n₂ n₃ m m₁ m₂ m₃ : ℕ}

/-
section hom
variable {A : ℕ → Type _} [∀ n, HasLogicSymbols (A n)] [HasUniv A] [HasEx A] 

def hom' (param : ℕ → Sort _)
  (homRel  : ∀ {n}, ∀ {k}, L.rel k → (Fin k → SubTerm L μ n) → A n)
  (homNrel : ∀ {n}, ∀ {k},L.rel k → (Fin k → SubTerm L μ n) → A n) :
    ∀ {n}, SubFormula L μ n → A n
  | _, _, ⊤ => ⊤
  | _, _, ⊥ => ⊥
  | _, w, rel r v => homRel w r v
  | _, w, nrel r v => homNrel w r v
  | _, w, p ⋏ q => hom' param @homRel @homNrel w p ⋏ hom' param @homRel @homNrel w q
  | _, w, p ⋎ q => hom' param @homRel @homNrel w p ⋎ hom' param @homRel @homNrel w q
  | _, w, ∀' p  => ∀' hom' param @homRel @homNrel w p
end hom
-/

def bind' : ∀ {n₁ n₂}, (fixed : Fin n₁ → SubTerm L μ₂ n₂) → (free : μ₁ → SubTerm L μ₂ n₂) →
    SubFormula L μ₁ n₁ → SubFormula L μ₂ n₂
  | _, _, _,    _,     ⊤          => ⊤
  | _, _, _,    _,     ⊥          => ⊥
  | _, _, fixed, free, (rel r v)  => rel r (SubTerm.bind fixed free ∘ v)
  | _, _, fixed, free, (nrel r v) => nrel r (SubTerm.bind fixed free ∘ v)
  | _, _, fixed, free, (p ⋏ q)    => bind' fixed free p ⋏ bind' fixed free q
  | _, _, fixed, free, (p ⋎ q)    => bind' fixed free p ⋎ bind' fixed free q
  | _, _, fixed, free, (∀' p)     => ∀' bind' (Fin.cases #0 $ SubTerm.fixedSucc ∘ fixed) (SubTerm.fixedSucc ∘ free) p
  | _, _, fixed, free, (∃' p)     => ∃' bind' (Fin.cases #0 $ SubTerm.fixedSucc ∘ fixed) (SubTerm.fixedSucc ∘ free) p

lemma bind'_neg {n₁ n₂} (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (p) :
    bind' fixed free (¬'p) = ¬'bind' fixed free p :=
  by induction p using rec' generalizing n₂ <;> simp[*, bind', ←neg_eq]

def bind (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) : SubFormula L μ₁ n₁ →L SubFormula L μ₂ n₂ where
  toFun := bind' fixed free
  map_top' := by simp[bind']
  map_bot' := by simp[bind']
  map_and' := by simp[bind']
  map_or' := by simp[bind']
  map_neg' := by simp[bind'_neg]
  map_imp' := by simp[imp_eq, bind'_neg, ←neg_eq, bind']

def map (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) : SubFormula L μ₁ n₁ →L SubFormula L μ₂ n₂ :=
  bind (fun n => #(fixed n)) (fun m => &(free m))

def subst (t : SubTerm L μ n) : SubFormula L μ (n + 1) →  SubFormula L μ n :=
  bind (SubTerm.fixedVar <: t) SubTerm.freeVar

section bind
variable (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂)

@[simp] lemma bind_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    bind fixed free (rel r v) = rel r (fun i => (v i).bind fixed free) := rfl

@[simp] lemma bind_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    bind fixed free (nrel r v) = nrel r (fun i => (v i).bind fixed free) := rfl

@[simp] lemma bind_all (p : SubFormula L μ₁ (n₁ + 1)) :
    bind fixed free (∀' p) = ∀' bind (#0 :> SubTerm.fixedSucc ∘ fixed) (SubTerm.fixedSucc ∘ free) p := rfl

@[simp] lemma bind_ex (p : SubFormula L μ₁ (n₁ + 1)) :
    bind fixed free (∃' p) = ∃' bind (#0 :> SubTerm.fixedSucc ∘ fixed) (SubTerm.fixedSucc ∘ free) p := rfl

end bind

lemma bind_bind
  (fixed₁ : Fin n₁ → SubTerm L μ₂ n₂) (free₁ : μ₁ → SubTerm L μ₂ n₂)
  (fixed₂ : Fin n₂ → SubTerm L μ₃ n₃) (free₂ : μ₂ → SubTerm L μ₃ n₃) (p : SubFormula L μ₁ n₁) :
    bind fixed₂ free₂ (bind fixed₁ free₁ p) = bind (fun n => (fixed₁ n).bind fixed₂ free₂) (fun m => (free₁ m).bind fixed₂ free₂) p := by
  induction p using rec' generalizing n₂ n₃ <;> simp[*, SubTerm.bind_bind] <;>
  { congr
    refine funext (Fin.cases (by simp) (by simp[SubTerm.fixedSucc, SubTerm.map, SubTerm.bind_bind]))
    refine funext (by simp[SubTerm.fixedSucc, SubTerm.map, SubTerm.bind_bind]) }

lemma bind_comp_bind
  (fixed₁ : Fin n₁ → SubTerm L μ₂ n₂) (free₁ : μ₁ → SubTerm L μ₂ n₂)
  (fixed₂ : Fin n₂ → SubTerm L μ₃ n₃) (free₂ : μ₂ → SubTerm L μ₃ n₃) :
    (bind fixed₂ free₂).comp (bind fixed₁ free₁) = bind (fun n => (fixed₁ n).bind fixed₂ free₂) (fun m => (free₁ m).bind fixed₂ free₂) :=
  by ext p; simp[bind_bind]

section map
variable (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂)

@[simp] lemma map_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    map fixed free (rel r v) = rel r (fun i => (v i).map fixed free) := rfl

@[simp] lemma map_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    map fixed free (nrel r v) = nrel r (fun i => (v i).map fixed free) := rfl

@[simp] lemma map_all (p : SubFormula L μ₁ (n₁ + 1)) :
    map fixed free (∀' p) = ∀' map (0 :> Fin.succ ∘ fixed) free p :=
  by simp[map]; congr; exact funext (Fin.cases (by simp) (by simp))

@[simp] lemma map_ex (p : SubFormula L μ₁ (n₁ + 1)) :
    map fixed free (∃' p) = ∃' map (0 :> Fin.succ ∘ fixed) free p :=
  by simp[map]; congr; exact funext (Fin.cases (by simp) (by simp))

end map

lemma map_map
  (fixed₁ : Fin n₁ → Fin n₂) (free₁ : μ₁ → μ₂)
  (fixed₂ : Fin n₂ → Fin n₃) (free₂ : μ₂ → μ₃) (p : SubFormula L μ₁ n₁) :
    map fixed₂ free₂ (map fixed₁ free₁ p) = map (fixed₂ ∘ fixed₁) (free₂ ∘ free₁) p :=
  bind_bind _ _ _ _ _

section syntactic

def shift : SyntacticSubFormula L n →L SyntacticSubFormula L n :=
  map id Nat.succ

def push : SyntacticSubFormula L (n + 1) →L SyntacticSubFormula L n :=
  bind (SubTerm.fixedVar <: &0) (fun m => &(Nat.succ m))

def pull : SyntacticSubFormula L n →L SyntacticSubFormula L (n + 1) :=
  bind (fun x => #(Fin.castSucc x)) (fun x => match x with | 0 => #(Fin.last n) | x + 1 => &x)

@[simp] lemma shift_rel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) :
    shift (rel r v) = rel r (fun i => SubTerm.shift $ v i) := rfl

@[simp] lemma shift_nrel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) :
    shift (nrel r v) = nrel r (fun i => SubTerm.shift $ v i) := rfl

@[simp] lemma shift_all (p : SyntacticSubFormula L (n + 1)) :
    shift (∀' p) = ∀' shift p  := by simp[shift]; congr; exact funext (Fin.cases (by simp) (by simp))

@[simp] lemma shift_ex (p : SyntacticSubFormula L (n + 1)) :
    shift (∃' p) = ∃' shift p  := by simp[shift]; congr; exact funext (Fin.cases (by simp) (by simp))

@[simp] lemma push_rel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L (n + 1)) :
    push (rel r v) = rel r (fun i => SubTerm.push $ v i) := rfl

@[simp] lemma push_nrel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L (n + 1)) :
    push (nrel r v) = nrel r (fun i => SubTerm.push $ v i) := rfl

@[simp] lemma push_all (p : SyntacticSubFormula L (n + 1 + 1)) :
    push (∀' p) = ∀' push p  := by
  simp[push]; congr; exact funext (Fin.cases (by simp) (Fin.lastCases (by simp) (by simp; simp[Fin.succ_castSucc])))

@[simp] lemma push_ex (p : SyntacticSubFormula L (n + 1 + 1)) :
    push (∃' p) = ∃' push p  := by
  simp[push]; congr; exact funext (Fin.cases (by simp) (Fin.lastCases (by simp) (by simp; simp[Fin.succ_castSucc])))

@[simp] lemma pull_rel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) :
    pull (rel r v) = rel r (fun i => SubTerm.pull $ v i) := rfl

@[simp] lemma pull_nrel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) :
    pull (nrel r v) = nrel r (fun i => SubTerm.pull $ v i) := rfl

@[simp] lemma pull_all (p : SyntacticSubFormula L (n + 1)) :
    pull (∀' p) = ∀' pull p := by
  simp[pull]; congr
  · exact funext (Fin.cases (by simp) (by simp[Fin.succ_castSucc])) 
  · exact funext (Nat.rec (by simp) (by simp))

@[simp] lemma pull_ex (p : SyntacticSubFormula L (n + 1)) :
    pull (∃' p) = ∃' pull p := by
  simp[pull]; congr
  · exact funext (Fin.cases (by simp) (by simp[Fin.succ_castSucc])) 
  · exact funext (Nat.rec (by simp) (by simp))

end syntactic

end SubFormula