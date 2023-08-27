import Logic.Predicate.Language

namespace FirstOrder

inductive SubTerm (L : ℕ → Type u) (μ : Type v) (n : ℕ)
  | bvar : Fin n → SubTerm L μ n
  | fvar : μ → SubTerm L μ n
  | func : ∀ {arity}, L arity → (Fin arity → SubTerm L μ n) → SubTerm L μ n

scoped prefix:max "&" => SubTerm.fvar
scoped prefix:max "#" => SubTerm.bvar

abbrev Term (L : ℕ → Type u) (μ : Type v) := SubTerm L μ 0

abbrev SyntacticSubTerm (L : ℕ → Type u) (n : ℕ) := SubTerm L ℕ n

abbrev SyntacticTerm (L : ℕ → Type u) := SyntacticSubTerm L 0

namespace SubTerm

variable
  {L L' : ℕ → Type u} {L₁ : ℕ → Type u₁} {L₂ : ℕ → Type u₂}
  {μ μ' : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}

instance [Inhabited μ] : Inhabited (SubTerm L μ n) := ⟨&default⟩

section ToString

variable [∀ k, ToString (L k)] [ToString μ]

def toStr : SubTerm L μ n → String
  | #x                        => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x                        => "z_{" ++ toString x ++ "}"
  | func (arity := 0) c _     => toString c
  | func (arity := _ + 1) f v => "{" ++ toString f ++ "} \\left(" ++ String.vecToStr (fun i => toStr (v i)) ++ "\\right)"

instance : Repr (SubTerm L μ n) := ⟨fun t _ => toStr t⟩

instance : ToString (SubTerm L μ n) := ⟨toStr⟩

end ToString

section Decidable

variable [∀ k, DecidableEq (L k)] [DecidableEq μ]

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
        | isTrue h => by simp[h]; exact Matrix.decVec _ _ (fun i => hasDecEq (v₁ i) (v₂ i))
        | isFalse h => isFalse (by simp[h])
      · exact isFalse (by simp[e])

instance : DecidableEq (SubTerm L μ n) := hasDecEq

end Decidable

abbrev func! (k) (f : L k) (v : Fin k → SubTerm L μ n) := func f v

end SubTerm

structure Rew (L : ℕ → Type u) (μ₁ : Type ν₁) (n₁ : ℕ) (μ₂ : Type ν₂) (n₂ : ℕ) where
  toFun : SubTerm L μ₁ n₁ → SubTerm L μ₂ n₂
  func' : ∀ {k} (f : L k) (v : Fin k → SubTerm L μ₁ n₁), toFun (SubTerm.func f v) = SubTerm.func f (fun i => toFun (v i))

abbrev SyntacticRew (L : ℕ → Type u) (n₁ n₂ : ℕ) := Rew L ℕ n₁ ℕ n₂

namespace Rew

open SubTerm
variable
  {L L' : ℕ → Type u} {L₁ : ℕ → Type u₁} {L₂ : ℕ → Type u₂} {L₃ : ℕ → Type u₃}
  {μ μ' : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}
variable (ω : Rew L μ₁ n₁ μ₂ n₂)

instance : FunLike (Rew L μ₁ n₁ μ₂ n₂) (SubTerm L μ₁ n₁) (fun _ => SubTerm L μ₂ n₂) where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by rcases f; rcases g; simp; exact h

instance : CoeFun (Rew L μ₁ n₁ μ₂ n₂) (fun _ => SubTerm L μ₁ n₁ → SubTerm L μ₂ n₂) := FunLike.hasCoeToFun

protected lemma func {k} (f : L k) (v : Fin k → SubTerm L μ₁ n₁) :
    ω (func f v) = func f (fun i => ω (v i)) := ω.func' f v

lemma func'' {k} (f : L k) (v : Fin k → SubTerm L μ₁ n₁) :
    ω (func f v) = func f (ω ∘ v) := ω.func' f v

@[simp] lemma func0 (f : L 0) (v : Fin 0 → SubTerm L μ₁ n₁) :
    ω (func f v) = func f ![] := by simp[Rew.func]

@[simp] lemma func1 (f : L 1) (t : SubTerm L μ₁ n₁) :
    ω (func f ![t]) = func f ![ω t] := by simp[Matrix.constant_eq_singleton, Rew.func]

@[simp] lemma func2 (f : L 2) (t₁ t₂ : SubTerm L μ₁ n₁) :
    ω (func f ![t₁, t₂]) = func f ![ω t₁, ω t₂] := by simp[Rew.func]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma func3 (f : L 3) (t₁ t₂ t₃ : SubTerm L μ₁ n₁) :
    ω (func f ![t₁, t₂, t₃]) = func f ![ω t₁, ω t₂, ω t₃] := by
  simp[Rew.func]; funext i; induction' i using Fin.induction with i <;> simp; induction' i using Fin.induction with i <;> simp

@[ext] lemma ext (ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂) (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : ∀ x, ω₁ &x = ω₂ &x) : ω₁ = ω₂ := by
  apply FunLike.ext ω₁ ω₂; intro t
  induction t <;> simp[*, ω₁.func, ω₂.func]

lemma ext' {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} (h : ω₁ = ω₂) (t) : ω₁ t = ω₂ t := by simp[h]

protected def id : Rew L μ n μ n where
  toFun := id
  func' := fun _ _ => rfl

@[simp] lemma id_app (t : SubTerm L μ n) : Rew.id t = t := rfl

protected def comp (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) : Rew L μ₁ n₁ μ₃ n₃ where
  toFun := fun t => ω₂ (ω₁ t)
  func' := fun f v => by simp[func'']; rfl

lemma comp_app (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) (t : SubTerm L μ₁ n₁) :
    (ω₂.comp ω₁) t = ω₂ (ω₁ t) := rfl

def bindAux (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂) : SubTerm L μ₁ n₁ → SubTerm L μ₂ n₂
  | (#x)       => b x    
  | (&x)       => e x
  | (func f v) => func f (fun i => bindAux b e (v i))

def bind (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂) : Rew L μ₁ n₁ μ₂ n₂ where
  toFun := bindAux b e
  func' := fun _ _ => rfl

abbrev rewrite (f : μ₁ → SubTerm L μ₂ n) : Rew L μ₁ n μ₂ n := bind SubTerm.bvar f

def map (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) : Rew L μ₁ n₁ μ₂ n₂ :=
  bind (fun n => #(b n)) (fun m => &(e m))

def substs {n'} (v : Fin n → SubTerm L μ n') : Rew L μ n μ n' :=
  bind v fvar

def emb {o : Type v₁} [h : IsEmpty o] {μ : Type v₂} {n} : Rew L o n μ n := map id h.elim'

def bShift : Rew L μ n μ (n + 1) :=
  map Fin.succ id

def castLe {n n' : ℕ} (h : n ≤ n') : Rew L μ n μ n' :=
  map (Fin.castLe h) id

def q (ω : Rew L μ₁ n₁ μ₂ n₂) : Rew L μ₁ (n₁ + 1) μ₂ (n₂ + 1) := 
  bind (#0 :> bShift ∘ ω ∘ bvar) (bShift ∘ ω ∘ fvar)

lemma eq_id_of_eq {ω : Rew L μ n μ n} (hb : ∀ x, ω #x = #x) (he : ∀ x, ω &x = &x) (t) : ω t = t := by
  have : ω = Rew.id := by ext <;> simp[*]
  simp[this]

section bind

variable (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂)

@[simp] lemma bind_fvar (m : μ₁) : bind b e (&m : SubTerm L μ₁ n₁) = e m := rfl

@[simp] lemma bind_bvar (n : Fin n₁) : bind b e (#n : SubTerm L μ₁ n₁) = b n := rfl

lemma eq_bind (ω : Rew L μ₁ n₁ μ₂ n₂) : ω = bind (ω ∘ bvar) (ω ∘ fvar) := by
  ext t; induction t ; simp[Rew.func'']; funext; simp[*]

end bind

section map

variable (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂)

@[simp] lemma map_fvar (m : μ₁) : map b e (&m : SubTerm L μ₁ n₁) = &(e m) := rfl

@[simp] lemma map_bvar (n : Fin n₁) : map b e (#n : SubTerm L μ₁ n₁) = #(b n) := rfl

@[simp] lemma map_id : map (L := L) (id : Fin n → Fin n) (id : μ → μ) = Rew.id := by ext <;> simp

lemma map_inj {b : Fin n₁ → Fin n₂} {e : μ₁ → μ₂} (hb : Function.Injective b) (he : Function.Injective e) :
    Function.Injective $ map (L := L) b e
  | #x,                    t => by cases t <;> simp[Rew.func]; intro h; exact hb h
  | &x,                    t => by cases t <;> simp[Rew.func]; intro h; exact he h
  | func (arity := k) f v, t => by
    cases t <;> simp[*, Rew.func]
    case func =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact map_inj hb he (congr_fun h i)

end map

section emb

variable {o : Type v₂} [IsEmpty o]

@[simp] lemma emb_bvar (x : Fin n) : emb (μ := μ) (#x : SubTerm L o n) = #x := rfl

end emb

section bShift

@[simp] lemma bShift_bvar (x : Fin n) : bShift (#x : SubTerm L μ n) = #(Fin.succ x) := rfl

@[simp] lemma bShift_fvar (x : μ) : bShift (&x : SubTerm L μ n) = &x := rfl

@[simp] lemma leftConcat_bShift_comp_bvar :
    (#0 :> bShift ∘ bvar : Fin (n + 1) → SubTerm L μ (n + 1)) = bvar :=
  funext (Fin.cases (by simp) (by simp))

@[simp] lemma bShift_comp_fvar :
    (bShift ∘ fvar : μ → SubTerm L μ (n + 1)) = fvar :=
  funext (by simp)

end bShift

section substs

variable {n'} (w : Fin n → SubTerm L μ n')

@[simp] lemma substs_bvar (x : Fin n) : substs w #x = w x :=
  by simp[substs]

@[simp] lemma substs_fvar (x : μ) : substs w &x = &x :=
  by simp[substs]

@[simp] lemma substs_zero (w : Fin 0 → Term L μ) : substs w = Rew.id :=
  by ext x <;> simp; { exact Fin.elim0 x }

lemma substs_comp_substs {l k} (v : Fin l → SubTerm L μ k) (w : Fin k → SubTerm L μ n) :
    (substs w).comp (substs v) = substs (substs w ∘ v) :=
  by ext <;> simp[comp_app]

end substs

section castLe

@[simp] lemma castLe_bvar {n'} (h : n ≤ n') (x : Fin n) : castLe h (#x : SubTerm L μ n) = #(Fin.castLe h x) := rfl

@[simp] lemma castLe_fvar {n'} (h : n ≤ n') (x : μ) : castLe h (&x : SubTerm L μ n) = &x := rfl

end castLe

section q

variable (ω : Rew L μ₁ n₁ μ₂ n₂)

@[simp] lemma q_bvar_zero : ω.q #0 = #0 := by simp[Rew.q]

@[simp] lemma q_bvar_succ (i : Fin n₁) : ω.q #(i.succ) = bShift (ω #i) := by simp[Rew.q]

@[simp] lemma q_fvar (x : μ₁) : ω.q &x = bShift (ω &x) := by simp[Rew.q]

@[simp] lemma q_comp_bShift : ω.q.comp bShift = bShift.comp ω := by
  ext x <;> simp[comp_app]

@[simp] lemma q_comp_bShift_app (t : SubTerm L μ₁ n₁) : ω.q (bShift t) = bShift (ω t) := by
  have := ext' (ω.q_comp_bShift) t; simpa only [comp_app] using this

@[simp] lemma q_id : (Rew.id : Rew L μ n μ n).q = Rew.id := by ext x; { cases x using Fin.cases <;> simp }; { simp }

lemma q_comp (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) :
    (Rew.comp ω₂ ω₁).q = ω₂.q.comp ω₁.q := by ext x; { cases x using Fin.cases <;> simp[comp_app] }; { simp[comp_app] }

lemma q_bind (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂) :
    (bind b e).q = bind (#0 :> bShift ∘ b) (bShift ∘ e) := by ext x; { cases x using Fin.cases <;> simp }; { simp }

lemma q_map (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) :
    (map (L := L) b e).q = map (0 :> Fin.succ ∘ b) e := by ext x; { cases x using Fin.cases <;> simp }; { simp }

@[simp] lemma q_emb {o : Type v₁} [e : IsEmpty o] {n} :
    (emb (L := L) (o := o) (μ := μ₂) (n := n)).q = emb := by ext x; { cases x using Fin.cases <;> simp }; { exact e.elim x }

lemma q_substs (w : Fin n → SubTerm L μ n') :
    (substs w).q = substs (#0 :> bShift ∘ w) := by ext x; { cases x using Fin.cases <;> simp }; { simp }

end q

section Syntactic

/-
  #0 #1 ... #(n - 1) &0 &1 ...
   ↓shift
  #0 #1 ... #(n - 1) &1 &2 &3 ...
-/

def shift : SyntacticRew L n n := map id Nat.succ

/- 
  #0 #1 ... #(n - 1) #n &0 &1 ...
   ↓free           ↑fix
  #0 #1 ... #(n - 1) &0 &1 &2 ...
 -/

def free : SyntacticRew L (n + 1) n := bind (bvar <: &0) (fun m => &(Nat.succ m))

def fix : SyntacticRew L n (n + 1) := bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ fvar)

abbrev rewrite1 (t : SyntacticSubTerm L n) : SyntacticRew L n n := bind SubTerm.bvar (t :>ₙ fvar)

section shift

@[simp] lemma shift_bvar (x : Fin n) : shift (#x : SyntacticSubTerm L n) = #x := rfl

@[simp] lemma shift_fvar (x : ℕ) : shift (&x : SyntacticSubTerm L n) = &(x + 1) := rfl

lemma shift_func {k} (f : L k) (v : Fin k → SyntacticSubTerm L n) :
    shift (func f v) = func f (fun i => shift (v i)) := rfl

lemma shift_Injective : Function.Injective (@shift L n) :=
  Function.LeftInverse.injective (g := map id Nat.pred)
    (by intros p; simp[←comp_app]; apply eq_id_of_eq <;> simp[comp_app])

end shift

section free

@[simp] lemma free_bvar_castSucc (x : Fin n) : free (#(Fin.castSucc x) : SyntacticSubTerm L (n + 1)) = #x := by simp[free]

@[simp] lemma free_bvar_castSucc_zero : free (#0 : SyntacticSubTerm L (n + 1 + 1)) = #0 := free_bvar_castSucc 0

@[simp] lemma free_bvar_last : free (#(Fin.last n) : SyntacticSubTerm L (n + 1)) = &0 := by simp[free]

@[simp] lemma free_bvar_last_zero : free (#0 : SyntacticSubTerm L 1) = &0 := free_bvar_last

@[simp] lemma free_fvar (x : ℕ) : free (&x : SyntacticSubTerm L (n + 1)) = &(x + 1) := by simp[free]

end free

section fix

@[simp] lemma fix_bvar (x : Fin n) : fix (#x : SyntacticSubTerm L n) = #(Fin.castSucc x) := by simp[fix]

@[simp] lemma fix_fvar_zero : fix (&0 : SyntacticSubTerm L n) = #(Fin.last n) := by simp[fix]

@[simp] lemma fix_fvar_succ (x : ℕ) : fix (&(x + 1) : SyntacticSubTerm L n) = &x := by simp[fix]

end fix

@[simp] lemma free_comp_fix : (free (L := L) (n := n)).comp fix = Rew.id := by
  ext x <;> simp[comp_app]; { cases x <;> simp }

@[simp] lemma fix_comp_free : (fix (L := L) (n := n)).comp free = Rew.id := by
  ext x <;> simp[comp_app]; { cases x using Fin.lastCases <;> simp }

@[simp] lemma bShift_free_eq_shift : (free (L := L) (n := 0)).comp bShift = shift := by
  ext x <;> simp[comp_app]; { exact Fin.elim0 x }

lemma bShift_comp_substs (v : Fin n₁ → SubTerm L μ₂ n₂) :
  bShift.comp (substs v) = substs (bShift ∘ v) := by ext x <;> simp[comp_app]

lemma shift_comp_substs (v : Fin n₁ → SyntacticSubTerm L n₂) :
  shift.comp (substs v) = (substs (shift ∘ v)).comp shift := by ext x <;> simp[comp_app]

lemma shift_comp_substs1 (t : SyntacticSubTerm L n₂) :
  shift.comp (substs ![t]) = (substs ![shift t]).comp shift := by ext x <;> simp[comp_app]

@[simp] lemma rewrite_comp_emb {o : Type v₁} [e : IsEmpty o] (f : μ₂ → SubTerm L μ₃ n) :
  (rewrite f).comp emb = (emb : Rew L o n μ₃ n) := by ext x <;> simp[comp_app]; { exact IsEmpty.elim e x }

@[simp] lemma shift_comp_emb {o : Type v₁} [e : IsEmpty o] :
  shift.comp emb = (emb : Rew L o n ℕ n) := by ext x <;> simp[comp_app]; { exact IsEmpty.elim e x }

lemma rewrite_comp_free_eq_substs (t : SyntacticTerm L) :
    (rewrite (t :>ₙ SubTerm.fvar)).comp free = substs ![t] := by ext x <;> simp[comp_app, Fin.eq_zero]

lemma rewrite_comp_shift_eq_substs (t : SyntacticTerm L) :
    (rewrite (t :>ₙ SubTerm.fvar)).comp shift = Rew.id := by ext x <;> simp[comp_app]

lemma substs_mbar_zero_comp_shift_eq_free :
    (substs (L := L) ![&0]).comp shift = free := by ext x <;> simp[comp_app, Fin.eq_zero]

lemma free_comp_substs_eq_substs_comp_shift {n'} (w : Fin n' → SyntacticSubTerm Lf (n + 1)) :
    free.comp (substs w) = (substs (free ∘ w)).comp shift :=
  by ext x <;> simp[comp_app]

section q

variable (ω : SyntacticRew L n₁ n₂)

@[simp] lemma q_shift : (shift (L := L) (n := n)).q = shift := by ext x; { cases x using Fin.cases <;> simp }; { simp }

@[simp] lemma q_free : (free (L := L) (n := n)).q = free := by
  ext x; { cases' x using Fin.cases with x <;> simp; { cases x using Fin.lastCases <;> simp[Fin.succ_castSucc] } }; { simp }

@[simp] lemma q_fix : (fix (L := L) (n := n)).q = fix := by
  ext x; { cases x using Fin.cases <;> simp[Fin.succ_castSucc] }; { cases x <;> simp }

end q

end Syntactic

end Rew

scoped syntax (name := substsNotation) "[→ " term,* "]" : term

scoped macro_rules
  | `([→ $terms:term,*]) => `(Rew.substs ![$terms,*])

@[app_unexpander Rew.substs]
def substsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ ![$terms,*]) => `([→ $terms,*])
  | _ => throw ()

scoped notation "⇑" => Rew.shift

namespace SubTerm

open Rew

variable
  {L L' : ℕ → Type u} {L₁ : ℕ → Type u₁} {L₂ : ℕ → Type u₂}
  {μ μ' : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}

def fvarList : SubTerm L μ n → List μ
  | #_       => []
  | &x       => [x]
  | func _ v => List.join $ Matrix.toList (fun i => fvarList (v i))

abbrev fvar? (t : SubTerm L μ n) (x : μ) : Prop := x ∈ t.fvarList

@[simp] lemma fvarList_bvar : fvarList (#x : SubTerm L μ n) = [] := rfl

@[simp] lemma fvarList_fvar : fvarList (&x : SubTerm L μ n) = [x] := rfl

@[simp] lemma mem_fvarList_func {k} {f : L k} {v : Fin k → SubTerm L μ n} :
    x ∈ (func f v).fvarList ↔ ∃ i, x ∈ (v i).fvarList :=
  by simp[fvarList]

lemma bind_eq_of_funEqOn (b : Fin n₁ → SubTerm L μ₂ n₂) (e₁ e₂ : μ₁ → SubTerm L μ₂ n₂) (t : SubTerm L μ₁ n₁)
  (h : Function.funEqOn t.fvar? e₁ e₂) :
    bind b e₁ t = bind b e₂ t := by
  induction t <;> simp[Rew.func]
  case fvar => simpa[fvar?, Function.funEqOn] using h
  case func k f v ih =>
    funext i
    exact ih i (h.of_subset $ by simp[fvar?]; intro x hx; exact ⟨i, hx⟩)

section lang

variable [∀ k, DecidableEq (L k)]

def lang : SubTerm L μ n → Finset (Σ k, L k)
  | #_       => ∅
  | &_       => ∅
  | func f v => insert ⟨_, f⟩ $ Finset.bunionᵢ Finset.univ (fun i => lang (v i))

@[simp] lemma lang_func {k} (f : L k) (v : Fin k → SubTerm L μ n) :
    ⟨k, f⟩ ∈ (func f v).lang := by simp[lang]

lemma lang_func_ss {k} (f : L k) (v : Fin k → SubTerm L μ n) (i) :
    (v i).lang ⊆ (func f v).lang :=
  by intros x; simp[lang]; intros h; exact Or.inr ⟨i, h⟩

end lang

section lMap

variable (Φ : ⦃k : ℕ⦄ → L₁ k → L₂ k)

def lMap (Φ : ⦃k : ℕ⦄ → L₁ k → L₂ k) : SubTerm L₁ μ n → SubTerm L₂ μ n
  | #x       => #x
  | &x       => &x
  | func f v => func (Φ f) (fun i => lMap Φ (v i))

@[simp] lemma lMap_bvar (x : Fin n) : (#x : SubTerm L₁ μ n).lMap Φ = #x := rfl

@[simp] lemma lMap_fvar (x : μ) : (&x : SubTerm L₁ μ n).lMap Φ = &x := rfl

lemma lMap_func {k} (f : L₁ k) (v : Fin k → SubTerm L₁ μ n) :
    (func f v).lMap Φ = func (Φ f) (fun i => lMap Φ (v i)) := rfl

lemma lMap_bind (b : Fin n₁ → SubTerm L₁ μ₂ n₂) (e : μ₁ → SubTerm L₁ μ₂ n₂) (t) :
    (bind b e t).lMap Φ = bind (fun x => (b x).lMap Φ) (fun x => (e x).lMap Φ) (t.lMap Φ) :=
  by induction t <;> simp[*, lMap_func, Rew.func]

lemma lMap_map (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) (t) :
    (map b e t).lMap Φ = map b e (t.lMap Φ) :=
  by simp[map, lMap_bind]

lemma lMap_bShift (t : SubTerm L₁ μ₁ n) : (bShift t).lMap Φ = bShift (t.lMap Φ) :=
  by simp[bShift, lMap_map]

lemma lMap_shift (t : SyntacticSubTerm L₁ n) : (shift t).lMap Φ = shift (t.lMap Φ) :=
  by simp[shift, lMap_map]

lemma lMap_free (t : SyntacticSubTerm L₁ (n + 1)) : (free t).lMap Φ = free (t.lMap Φ) :=
  by simp[free, lMap_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma lMap_fix (t : SyntacticSubTerm L₁ n) : (fix t).lMap Φ = fix (t.lMap Φ) :=
  by simp[fix, lMap_bind]; congr; funext x; cases x <;> simp

end lMap

structure Operator (L : ℕ → Type u) (ι : Type w) where
  operator : {μ : Type v} → {n : ℕ} → (ι → SubTerm L μ n) → SubTerm L μ n
  rew_operator : ∀ {μ μ' n₁ n₂} (ω : Rew L μ n₁ μ' n₂) (v : ι → SubTerm L μ n₁),
    ω (operator v) = operator (fun i => ω (v i))

abbrev Const (L : ℕ → Type u) := Operator.{u,v,0} L Empty

abbrev Monadic (L : ℕ → Type u) := Operator L Unit

abbrev Finitary (L : ℕ → Type u) (n : ℕ) := Operator L (Fin n)

def Operator.const (c : Const L) : SubTerm L μ n := c.operator Empty.elim

instance : Coe (Const L) (SubTerm L μ n) := ⟨Operator.const⟩

section natLit

open Language

variable [hz : Zero L] [ho : One L] [ha : Add L]

-- (((((t + 1) + 1) + 1) + 1) ... )
def addOnes (t : SubTerm L μ n) : ℕ → SubTerm L μ n
  | 0     => t
  | z + 1 => func Language.Add.add ![addOnes t z, func Language.One.one ![]]

@[simp] lemma addOnes_zero (t : SubTerm L μ n) : addOnes t 0 = t := rfl

@[simp] lemma addOnes_succ (t : SubTerm L μ n) (z : ℕ) :
  addOnes t (z + 1) = func Language.Add.add ![addOnes t z, func Language.One.one ![]] := rfl

lemma Rew.addOnes (ω : Rew L μ₁ n₁ μ₂ n₂) (t : SubTerm L μ₁ n₁) (z : ℕ) :
    ω (t.addOnes z) = (ω t).addOnes z := by induction z <;> simp[*]

-- (((((1 + 1) + 1) + 1) + 1) ... ) 
def natLit' : ℕ → SubTerm L μ n
  | 0     => func Language.Zero.zero ![]
  | z + 1 => addOnes (func Language.One.one ![]) z

variable (L)

def natLit (z : ℕ) : Const L where
  operator := fun _ => natLit' z
  rew_operator := by intros; cases z <;> simp[natLit', Rew.addOnes, Matrix.empty_eq]

variable {L}

abbrev sNatLit (z : ℕ) : SyntacticSubTerm L n := natLit L z

lemma natLit_zero : (natLit L 0 : SubTerm L μ n) = func Language.Zero.zero ![] := by rfl

lemma natLit_one : (natLit L 1 : SubTerm L μ n) = func Language.One.one ![] := by rfl

lemma natLit_succ (z : ℕ) (neZero : z ≠ 0) :
    (natLit L (.succ z) : SubTerm L μ n) = func Language.Add.add ![natLit L z, natLit L 1] := by
  cases z
  · contradiction
  · simp[natLit, natLit', Operator.const]

end natLit

end SubTerm

namespace Rew

open SubTerm

variable
  {L L' : ℕ → Type u} {L₁ : ℕ → Type u₁} {L₂ : ℕ → Type u₂}
  {μ μ' : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}
variable (ω : Rew L μ n₁ μ' n₂)

protected lemma operator (o : Operator L ι) (v : ι → SubTerm L μ n₁) :
    ω (o.operator v) = o.operator (fun i => ω (v i)) := by rw[ω.eq_bind]; exact o.rew_operator _ _

protected lemma operator' (o : Operator L ι) (v : ι → SubTerm L μ n₁) :
    ω (o.operator v) = o.operator (ω ∘ v) := ω.operator o v

@[simp] lemma finitary0 (o : Finitary L 0) (v : Fin 0 → SubTerm L μ n₁) :
    ω (o.operator v) = o.operator ![] := by simp[ω.operator', Matrix.empty_eq]

@[simp] lemma finitary1 (o : Finitary L 1) (t : SubTerm L μ n₁) :
    ω (o.operator ![t]) = o.operator ![ω t] := by simp[ω.operator']

@[simp] lemma finitary2 (o : Finitary L 2) (t₁ t₂ : SubTerm L μ n₁) :
    ω (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp[ω.operator']

@[simp] lemma finitary3 (o : Finitary L 3) (t₁ t₂ t₃ : SubTerm L μ n₁) :
    ω (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp[ω.operator']

@[simp] protected lemma const (c : Const L) : ω c = c :=
  by simpa[Operator.const, Empty.eq_elim] using c.rew_operator ω Empty.elim

end Rew

end FirstOrder
