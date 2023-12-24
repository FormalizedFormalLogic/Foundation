import Logic.FirstOrder.Basic.Language

namespace LO

namespace FirstOrder

inductive Semiterm (L : Language.{u}) (μ : Type v) (n : ℕ)
  | bvar : Fin n → Semiterm L μ n
  | fvar : μ → Semiterm L μ n
  | func : ∀ {arity}, L.Func arity → (Fin arity → Semiterm L μ n) → Semiterm L μ n

scoped prefix:max "&" => Semiterm.fvar
scoped prefix:max "#" => Semiterm.bvar

abbrev Term (L : Language.{u}) (μ : Type v) := Semiterm L μ 0

abbrev SyntacticSemiterm (L : Language.{u}) (n : ℕ) := Semiterm L ℕ n

abbrev SyntacticTerm (L : Language.{u}) := SyntacticSemiterm L 0

namespace Semiterm

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {μ μ' : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}

instance [Inhabited μ] : Inhabited (Semiterm L μ n) := ⟨&default⟩

section ToString

variable [∀ k, ToString (L.Func k)] [ToString μ]

def toStr : Semiterm L μ n → String
  | #x                        => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x                        => "z_{" ++ toString x ++ "}"
  | func (arity := 0) c _     => toString c
  | func (arity := _ + 1) f v => "{" ++ toString f ++ "} \\left(" ++ String.vecToStr (fun i => toStr (v i)) ++ "\\right)"

instance : Repr (Semiterm L μ n) := ⟨fun t _ => toStr t⟩

instance : ToString (Semiterm L μ n) := ⟨toStr⟩

end ToString

section Decidable

variable [∀ k, DecidableEq (L.Func k)] [DecidableEq μ]

def hasDecEq : (t u : Semiterm L μ n) → Decidable (Eq t u)
  | #x,                   #y                   => by simp; exact decEq x y
  | #_,                   &_                   => isFalse Semiterm.noConfusion
  | #_,                   func _ _             => isFalse Semiterm.noConfusion
  | &_,                   #_                   => isFalse Semiterm.noConfusion
  | &x,                   &y                   => by simp; exact decEq x y
  | &_,                   func _ _             => isFalse Semiterm.noConfusion
  | func _ _,             #_                   => isFalse Semiterm.noConfusion
  | func _ _,             &_                   => isFalse Semiterm.noConfusion
  | @func L μ _ k₁ r₁ v₁, @func L μ _ k₂ r₂ v₂ => by
      by_cases e : k₁ = k₂
      · rcases e with rfl
        exact match decEq r₁ r₂ with
        | isTrue h => by simp[h]; exact Matrix.decVec _ _ (fun i => hasDecEq (v₁ i) (v₂ i))
        | isFalse h => isFalse (by simp[h])
      · exact isFalse (by simp[e])

instance : DecidableEq (Semiterm L μ n) := hasDecEq

end Decidable

abbrev func! (k) (f : L.Func k) (v : Fin k → Semiterm L μ n) := func f v

end Semiterm

structure Rew (L : Language.{u}) (μ₁ : Type ν₁) (n₁ : ℕ) (μ₂ : Type ν₂) (n₂ : ℕ) where
  toFun : Semiterm L μ₁ n₁ → Semiterm L μ₂ n₂
  func' : ∀ {k} (f : L.Func k) (v : Fin k → Semiterm L μ₁ n₁), toFun (Semiterm.func f v) = Semiterm.func f (fun i => toFun (v i))

abbrev SyntacticRew (L : Language.{u}) (n₁ n₂ : ℕ) := Rew L ℕ n₁ ℕ n₂

namespace Rew

open Semiterm
variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {μ μ' : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}
variable (ω : Rew L μ₁ n₁ μ₂ n₂)

instance : FunLike (Rew L μ₁ n₁ μ₂ n₂) (Semiterm L μ₁ n₁) (fun _ => Semiterm L μ₂ n₂) where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by rcases f; rcases g; simp; exact h

instance : CoeFun (Rew L μ₁ n₁ μ₂ n₂) (fun _ => Semiterm L μ₁ n₁ → Semiterm L μ₂ n₂) := FunLike.hasCoeToFun

protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L μ₁ n₁) :
    ω (func f v) = func f (fun i => ω (v i)) := ω.func' f v

lemma func'' {k} (f : L.Func k) (v : Fin k → Semiterm L μ₁ n₁) :
    ω (func f v) = func f (ω ∘ v) := ω.func' f v

@[simp] lemma func0 (f : L.Func 0) (v : Fin 0 → Semiterm L μ₁ n₁) :
    ω (func f v) = func f ![] := by simp[Rew.func, Matrix.empty_eq]

@[simp] lemma func1 (f : L.Func 1) (t : Semiterm L μ₁ n₁) :
    ω (func f ![t]) = func f ![ω t] := by simp[Matrix.constant_eq_singleton, Rew.func]

@[simp] lemma func2 (f : L.Func 2) (t₁ t₂ : Semiterm L μ₁ n₁) :
    ω (func f ![t₁, t₂]) = func f ![ω t₁, ω t₂] := by simp[Rew.func]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma func3 (f : L.Func 3) (t₁ t₂ t₃ : Semiterm L μ₁ n₁) :
    ω (func f ![t₁, t₂, t₃]) = func f ![ω t₁, ω t₂, ω t₃] := by
  simp[Rew.func]; funext i; induction' i using Fin.induction with i <;> simp; induction' i using Fin.induction with i <;> simp

@[ext] lemma ext (ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂) (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : ∀ x, ω₁ &x = ω₂ &x) : ω₁ = ω₂ := by
  apply FunLike.ext ω₁ ω₂; intro t
  induction t <;> simp[*, ω₁.func, ω₂.func]

lemma ext' {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} (h : ω₁ = ω₂) (t) : ω₁ t = ω₂ t := by simp[h]

protected def id : Rew L μ n μ n where
  toFun := id
  func' := fun _ _ => rfl

@[simp] lemma id_app (t : Semiterm L μ n) : Rew.id t = t := rfl

protected def comp (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) : Rew L μ₁ n₁ μ₃ n₃ where
  toFun := fun t => ω₂ (ω₁ t)
  func' := fun f v => by simp[func'']; rfl

lemma comp_app (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) (t : Semiterm L μ₁ n₁) :
    (ω₂.comp ω₁) t = ω₂ (ω₁ t) := rfl

@[simp] lemma id_comp (ω : Rew L μ₁ n₁ μ₂ n₂) : Rew.id.comp ω = ω := by ext <;> simp[comp_app]

@[simp] lemma comp_id (ω : Rew L μ₁ n₁ μ₂ n₂) : ω.comp Rew.id = ω := by ext <;> simp[comp_app]

def bindAux (b : Fin n₁ → Semiterm L μ₂ n₂) (e : μ₁ → Semiterm L μ₂ n₂) : Semiterm L μ₁ n₁ → Semiterm L μ₂ n₂
  | (#x)       => b x
  | (&x)       => e x
  | (func f v) => func f (fun i => bindAux b e (v i))

def bind (b : Fin n₁ → Semiterm L μ₂ n₂) (e : μ₁ → Semiterm L μ₂ n₂) : Rew L μ₁ n₁ μ₂ n₂ where
  toFun := bindAux b e
  func' := fun _ _ => rfl

def rewrite (f : μ₁ → Semiterm L μ₂ n) : Rew L μ₁ n μ₂ n := bind Semiterm.bvar f

def rewriteMap (e : μ₁ → μ₂) : Rew L μ₁ n μ₂ n := bind Semiterm.bvar (fun m => &(e m))

def map (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) : Rew L μ₁ n₁ μ₂ n₂ :=
  bind (fun n => #(b n)) (fun m => &(e m))

def substs {n'} (v : Fin n → Semiterm L μ n') : Rew L μ n μ n' :=
  bind v fvar

def emb {o : Type v₁} [h : IsEmpty o] {μ : Type v₂} {n} : Rew L o n μ n := map id h.elim'

def bShift : Rew L μ n μ (n + 1) :=
  map Fin.succ id

def bShiftAdd (m : ℕ) : Rew L μ n μ (n + m) :=
  map (Fin.addNat · m) id

def castLE {n n' : ℕ} (h : n ≤ n') : Rew L μ n μ n' :=
  map (Fin.castLE h) id

protected def q (ω : Rew L μ₁ n₁ μ₂ n₂) : Rew L μ₁ (n₁ + 1) μ₂ (n₂ + 1) :=
  bind (#0 :> bShift ∘ ω ∘ bvar) (bShift ∘ ω ∘ fvar)

lemma eq_id_of_eq {ω : Rew L μ n μ n} (hb : ∀ x, ω #x = #x) (he : ∀ x, ω &x = &x) (t) : ω t = t := by
  have : ω = Rew.id := by ext <;> simp[*]
  simp[this]

def qpow (ω : Rew L μ₁ n₁ μ₂ n₂) : (k : ℕ) → Rew L μ₁ (n₁ + k) μ₂ (n₂ + k)
  | 0     => ω
  | k + 1 => (ω.qpow k).q

@[simp] lemma qpow_zero (ω : Rew L μ₁ n₁ μ₂ n₂) : qpow ω 0 = ω := rfl

@[simp] lemma qpow_succ (ω : Rew L μ₁ n₁ μ₂ n₂) (k : ℕ) : qpow ω (k + 1) = (ω.qpow k).q := rfl

section bind

variable (b : Fin n₁ → Semiterm L μ₂ n₂) (e : μ₁ → Semiterm L μ₂ n₂)

@[simp] lemma bind_fvar (m : μ₁) : bind b e (&m : Semiterm L μ₁ n₁) = e m := rfl

@[simp] lemma bind_bvar (n : Fin n₁) : bind b e (#n : Semiterm L μ₁ n₁) = b n := rfl

lemma eq_bind (ω : Rew L μ₁ n₁ μ₂ n₂) : ω = bind (ω ∘ bvar) (ω ∘ fvar) := by
  ext t; induction t ; simp[Rew.func'']; funext; simp[*]

@[simp] lemma bind_eq_id_of_zero (f : Fin 0 → Semiterm L μ₂ 0) : bind f fvar = Rew.id := by { ext x <;> simp; exact Fin.elim0 x }

end bind

section map

variable (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂)

@[simp] lemma map_fvar (m : μ₁) : map b e (&m : Semiterm L μ₁ n₁) = &(e m) := rfl

@[simp] lemma map_bvar (n : Fin n₁) : map b e (#n : Semiterm L μ₁ n₁) = #(b n) := rfl

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

section rewrite

variable (f : μ₁ → Semiterm L μ₂ n)

@[simp] lemma rewrite_fvar (x : μ₁) : rewrite f &x = f x := rfl

@[simp] lemma rewrite_bvar (x : Fin n) : rewrite e (#x : Semiterm L μ₁ n) = #x := rfl

lemma rewrite_comp_rewrite (v : μ₂ → Semiterm L μ₃ n) (w : μ₁ → Semiterm L μ₂ n) :
    (rewrite v).comp (rewrite w) = rewrite (rewrite v ∘ w) :=
  by ext <;> simp[comp_app]

@[simp] lemma rewrite_eq_id : (rewrite Semiterm.fvar : Rew L μ n μ n) = Rew.id := by ext <;> simp

end rewrite

section rewriteMap

variable (e : μ₁ → μ₂)

@[simp] lemma rewriteMap_fvar (x : μ₁) : rewriteMap e (&x : Semiterm L μ₁ n) = &(e x) := rfl

@[simp] lemma rewriteMap_bvar (x : Fin n) : rewriteMap e (#x : Semiterm L μ₁ n) = #x := rfl

@[simp] lemma rewriteMap_id : rewriteMap (L := L) (n := n) (id : μ → μ) = Rew.id := by ext <;> simp

end rewriteMap

section emb

variable {o : Type v₂} [IsEmpty o]

@[simp] lemma emb_bvar (x : Fin n) : emb (μ := μ) (#x : Semiterm L o n) = #x := rfl

@[simp] lemma emb_eq_id : (emb : Rew L o n o n) = Rew.id := by ext x <;> simp; exact isEmptyElim x

end emb

section bShift

@[simp] lemma bShift_bvar (x : Fin n) : bShift (#x : Semiterm L μ n) = #(Fin.succ x) := rfl

@[simp] lemma bShift_fvar (x : μ) : bShift (&x : Semiterm L μ n) = &x := rfl

@[simp] lemma leftConcat_bShift_comp_bvar :
    (#0 :> bShift ∘ bvar : Fin (n + 1) → Semiterm L μ (n + 1)) = bvar :=
  funext (Fin.cases (by simp) (by simp))

@[simp] lemma bShift_comp_fvar :
    (bShift ∘ fvar : μ → Semiterm L μ (n + 1)) = fvar :=
  funext (by simp)

end bShift

section bShiftAdd

@[simp] lemma bShiftAdd_bvar (m) (x : Fin n) : bShiftAdd m (#x : Semiterm L μ n) = #(Fin.addNat x m) := rfl

@[simp] lemma bShiftAdd_fvar (m) (x : μ) : bShiftAdd m (&x : Semiterm L μ n) = &x := rfl

end bShiftAdd

section substs

variable {n'} (w : Fin n → Semiterm L μ n')

@[simp] lemma substs_bvar (x : Fin n) : substs w #x = w x :=
  by simp[substs]

@[simp] lemma substs_fvar (x : μ) : substs w &x = &x :=
  by simp[substs]

@[simp] lemma substs_zero (w : Fin 0 → Term L μ) : substs w = Rew.id :=
  by ext x <;> simp; { exact Fin.elim0 x }

lemma substs_comp_substs (v : Fin l → Semiterm L μ k) (w : Fin k → Semiterm L μ n) :
    (substs w).comp (substs v) = substs (substs w ∘ v) :=
  by ext <;> simp[comp_app]

@[simp] lemma substs_eq_id : (substs Semiterm.bvar : Rew L μ n μ n) = Rew.id := by ext <;> simp

end substs

section castLE

@[simp] lemma castLe_bvar {n'} (h : n ≤ n') (x : Fin n) : castLE h (#x : Semiterm L μ n) = #(Fin.castLE h x) := rfl

@[simp] lemma castLe_fvar {n'} (h : n ≤ n') (x : μ) : castLE h (&x : Semiterm L μ n) = &x := rfl

@[simp] lemma castLe_eq_id {h} : (castLE h : Rew L μ n μ n) = Rew.id := by ext <;> simp

end castLE

section q

variable (ω : Rew L μ₁ n₁ μ₂ n₂)

@[simp] lemma q_bvar_zero : ω.q #0 = #0 := by simp[Rew.q]

@[simp] lemma q_bvar_succ (i : Fin n₁) : ω.q #(i.succ) = bShift (ω #i) := by simp[Rew.q]

@[simp] lemma q_fvar (x : μ₁) : ω.q &x = bShift (ω &x) := by simp[Rew.q]

@[simp] lemma q_comp_bShift : ω.q.comp bShift = bShift.comp ω := by
  ext x <;> simp[comp_app]

@[simp] lemma q_comp_bShift_app (t : Semiterm L μ₁ n₁) : ω.q (bShift t) = bShift (ω t) := by
  have := ext' (ω.q_comp_bShift) t; simpa only [comp_app] using this

@[simp] lemma q_id : (Rew.id : Rew L μ n μ n).q = Rew.id := by ext x; { cases x using Fin.cases <;> simp }; { simp }

@[simp] lemma qpow_id {k} : (Rew.id : Rew L μ n μ n).qpow k = Rew.id := by induction k <;> simp[*]

lemma q_comp (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) :
    (Rew.comp ω₂ ω₁).q = ω₂.q.comp ω₁.q := by ext x; { cases x using Fin.cases <;> simp[comp_app] }; { simp[comp_app] }

lemma qpow_comp (k) (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) :
    (Rew.comp ω₂ ω₁).qpow k = (ω₂.qpow k).comp (ω₁.qpow k) := by induction k <;> simp[*, q_comp]

lemma q_bind (b : Fin n₁ → Semiterm L μ₂ n₂) (e : μ₁ → Semiterm L μ₂ n₂) :
    (bind b e).q = bind (#0 :> bShift ∘ b) (bShift ∘ e) := by ext x; { cases x using Fin.cases <;> simp }; { simp }

lemma q_map (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) :
    (map (L := L) b e).q = map (0 :> Fin.succ ∘ b) e := by ext x; { cases x using Fin.cases <;> simp }; { simp }

lemma q_rewrite (f : μ₁ → Semiterm L μ₂ n) :
    (rewrite f).q = rewrite (bShift ∘ f) := by ext x; { cases x using Fin.cases <;> simp[rewriteMap] }; { simp }

@[simp] lemma q_rewriteMap (e : μ₁ → μ₂) :
    (rewriteMap (L := L) (n := n) e).q = rewriteMap e := by ext x; { cases x using Fin.cases <;> simp[rewriteMap] }; { simp }

@[simp] lemma q_emb {o : Type v₁} [e : IsEmpty o] {n} :
    (emb (L := L) (o := o) (μ := μ₂) (n := n)).q = emb := by ext x; { cases x using Fin.cases <;> simp }; { exact e.elim x }

@[simp] lemma qpow_emb {o : Type v₁} [e : IsEmpty o] {n k} :
    (emb (L := L) (o := o) (μ := μ₂) (n := n)).qpow k = emb := by induction k <;> simp[*]

@[simp] lemma q_castLE {n n'} (h : n ≤ n') :
    (castLE h : Rew L μ n μ n').q = castLE (Nat.add_le_add_right h 1) := by
  ext x <;> simp; cases x using Fin.cases <;> simp

@[simp] lemma qpow_castLE {n n'} (h : n ≤ n') :
    (castLE h : Rew L μ n μ n').qpow k = castLE (Nat.add_le_add_right h k) := by
  induction k <;> simp[*]

lemma q_substs (w : Fin n → Semiterm L μ n') :
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

abbrev rewrite1 (t : SyntacticSemiterm L n) : SyntacticRew L n n := bind Semiterm.bvar (t :>ₙ fvar)

section shift

@[simp] lemma shift_bvar (x : Fin n) : shift (#x : SyntacticSemiterm L n) = #x := rfl

@[simp] lemma shift_fvar (x : ℕ) : shift (&x : SyntacticSemiterm L n) = &(x + 1) := rfl

lemma shift_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    shift (func f v) = func f (fun i => shift (v i)) := rfl

lemma shift_Injective : Function.Injective (@shift L n) :=
  Function.LeftInverse.injective (g := map id Nat.pred)
    (by intros p; simp[←comp_app]; apply eq_id_of_eq <;> simp[comp_app])

end shift

section free

@[simp] lemma free_bvar_castSucc (x : Fin n) : free (#(Fin.castSucc x) : SyntacticSemiterm L (n + 1)) = #x := by simp[free]

@[simp] lemma free_bvar_castSucc_zero : free (#0 : SyntacticSemiterm L (n + 1 + 1)) = #0 := free_bvar_castSucc 0

@[simp] lemma free_bvar_last : free (#(Fin.last n) : SyntacticSemiterm L (n + 1)) = &0 := by simp[free]

@[simp] lemma free_bvar_last_zero : free (#0 : SyntacticSemiterm L 1) = &0 := free_bvar_last

@[simp] lemma free_fvar (x : ℕ) : free (&x : SyntacticSemiterm L (n + 1)) = &(x + 1) := by simp[free]

end free

section fix

@[simp] lemma fix_bvar (x : Fin n) : fix (#x : SyntacticSemiterm L n) = #(Fin.castSucc x) := by simp[fix]

@[simp] lemma fix_fvar_zero : fix (&0 : SyntacticSemiterm L n) = #(Fin.last n) := by simp[fix]

@[simp] lemma fix_fvar_succ (x : ℕ) : fix (&(x + 1) : SyntacticSemiterm L n) = &x := by simp[fix]

end fix

@[simp] lemma free_comp_fix : (free (L := L) (n := n)).comp fix = Rew.id := by
  ext x <;> simp[comp_app]; { cases x <;> simp }

@[simp] lemma fix_comp_free : (fix (L := L) (n := n)).comp free = Rew.id := by
  ext x <;> simp[comp_app]; { cases x using Fin.lastCases <;> simp }

@[simp] lemma bShift_free_eq_shift : (free (L := L) (n := 0)).comp bShift = shift := by
  ext x <;> simp[comp_app]; { exact Fin.elim0 x }

lemma bShift_comp_substs (v : Fin n₁ → Semiterm L μ₂ n₂) :
  bShift.comp (substs v) = substs (bShift ∘ v) := by ext x <;> simp[comp_app]

lemma shift_comp_substs (v : Fin n₁ → SyntacticSemiterm L n₂) :
  shift.comp (substs v) = (substs (shift ∘ v)).comp shift := by ext x <;> simp[comp_app]

lemma shift_comp_substs1 (t : SyntacticSemiterm L n₂) :
  shift.comp (substs ![t]) = (substs ![shift t]).comp shift := by ext x <;> simp[comp_app]

@[simp] lemma rewrite_comp_emb {o : Type v₁} [e : IsEmpty o] (f : μ₂ → Semiterm L μ₃ n) :
  (rewrite f).comp emb = (emb : Rew L o n μ₃ n) := by ext x <;> simp[comp_app]; { exact IsEmpty.elim e x }

@[simp] lemma shift_comp_emb {o : Type v₁} [e : IsEmpty o] :
  shift.comp emb = (emb : Rew L o n ℕ n) := by ext x <;> simp[comp_app]; { exact IsEmpty.elim e x }

lemma rewrite_comp_free_eq_substs (t : SyntacticTerm L) :
    (rewrite (t :>ₙ Semiterm.fvar)).comp free = substs ![t] := by ext x <;> simp[comp_app, Fin.eq_zero]

lemma rewrite_comp_shift_eq_id (t : SyntacticTerm L) :
    (rewrite (t :>ₙ Semiterm.fvar)).comp shift = Rew.id := by ext x <;> simp[comp_app]

@[simp] lemma substs_mbar_zero_comp_shift_eq_free :
    (substs (L := L) ![&0]).comp shift = free := by ext x <;> simp[comp_app, Fin.eq_zero]

@[simp] lemma substs_comp_bShift_eq_id (v : Fin 1 → Semiterm L μ 0) :
    (substs (L := L) v).comp bShift = Rew.id := by ext x <;> simp[comp_app]; exact Fin.elim0 x

lemma free_comp_substs_eq_substs_comp_shift {n'} (w : Fin n' → SyntacticSemiterm Lf (n + 1)) :
    free.comp (substs w) = (substs (free ∘ w)).comp shift :=
  by ext x <;> simp[comp_app]

@[simp] lemma fix_free_app (t : SyntacticSemiterm L (n + 1)) : fix (free t) = t := by simp[←comp_app]

@[simp] lemma free_fix_app (t : SyntacticSemiterm L n) : free (fix t) = t := by simp[←comp_app]

@[simp] lemma free_bShift_app (t : SyntacticSemiterm L 0) : free (bShift t) = shift t := by simp[←comp_app]

@[simp] lemma substs_bShift_app (v : Fin 1 → Semiterm L μ 0) : substs v (bShift t) = t := by simp[←comp_app]

lemma rewrite_comp_fix_eq_substs (t) :
    ((rewrite (t :>ₙ (&·))).comp free : SyntacticRew L 1 0) = substs ![t] := by
  ext x <;> simp[comp_app, Fin.eq_zero]

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

namespace Semiterm

open Rew

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {μ μ' : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}

def fvarList : Semiterm L μ n → List μ
  | #_       => []
  | &x       => [x]
  | func _ v => List.join $ Matrix.toList (fun i => fvarList (v i))

abbrev fvar? (t : Semiterm L μ n) (x : μ) : Prop := x ∈ t.fvarList

@[simp] lemma fvarList_bvar : fvarList (#x : Semiterm L μ n) = [] := rfl

@[simp] lemma fvarList_fvar : fvarList (&x : Semiterm L μ n) = [x] := rfl

@[simp] lemma mem_fvarList_func {k} {f : L.Func k} {v : Fin k → Semiterm L μ n} :
    x ∈ (func f v).fvarList ↔ ∃ i, x ∈ (v i).fvarList :=
  by simp[fvarList]

@[simp] lemma fvarList_empty {o : Type w} [e : IsEmpty o] {t : Semiterm L o n} : fvarList t = [] := by
  induction t <;> simp[List.eq_nil_iff_forall_not_mem]
  case fvar x => exact IsEmpty.elim e x

@[simp] lemma fvarList_emb {o : Type w} [e : IsEmpty o] {t : Semiterm L o n} : fvarList (Rew.emb t : Semiterm L μ n) = [] := by
  induction t <;> simp[*, List.eq_nil_iff_forall_not_mem, Rew.func]
  case fvar x => { exact IsEmpty.elim' e x }

lemma rew_eq_of_funEqOn (ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂) (t : Semiterm L μ₁ n₁)
  (hb : ∀ x, ω₁ #x = ω₂ #x)
  (he : Function.funEqOn t.fvar? (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) :
    ω₁ t = ω₂ t := by
  induction t <;> try simp[Rew.func, hb]
  case fvar => simpa[fvar?, Function.funEqOn] using he
  case func k f v ih =>
    funext i
    exact ih i (he.of_subset $ by simp[fvar?]; intro x hx; exact ⟨i, hx⟩)

/-
lemma bind_eq_of_funEqOn (b : Fin n₁ → Semiterm L μ₂ n₂) (e₁ e₂ : μ₁ → Semiterm L μ₂ n₂) (t : Semiterm L μ₁ n₁)
  (h : Function.funEqOn t.fvar? e₁ e₂) :
    bind b e₁ t = bind b e₂ t := by
  induction t <;> simp[Rew.func]
  case fvar => simpa[fvar?, Function.funEqOn] using h
  case func k f v ih =>
    funext i
    exact ih i (h.of_subset $ by simp[fvar?]; intro x hx; exact ⟨i, hx⟩)
-/

section lMap

variable (Φ : L₁ →ᵥ L₂)

def lMap (Φ : L₁ →ᵥ L₂) : Semiterm L₁ μ n → Semiterm L₂ μ n
  | #x       => #x
  | &x       => &x
  | func f v => func (Φ.func f) (fun i => lMap Φ (v i))

@[simp] lemma lMap_bvar (x : Fin n) : (#x : Semiterm L₁ μ n).lMap Φ = #x := rfl

@[simp] lemma lMap_fvar (x : μ) : (&x : Semiterm L₁ μ n).lMap Φ = &x := rfl

lemma lMap_func {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ μ n) :
    (func f v).lMap Φ = func (Φ.func f) (fun i => lMap Φ (v i)) := rfl

lemma lMap_bind (b : Fin n₁ → Semiterm L₁ μ₂ n₂) (e : μ₁ → Semiterm L₁ μ₂ n₂) (t) :
    lMap Φ (bind b e t) = bind (lMap Φ ∘ b) (lMap Φ ∘ e) (t.lMap Φ) :=
  by induction t <;> simp[*, lMap_func, Rew.func]

lemma lMap_map (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) (t) :
    (map b e t).lMap Φ = map b e (t.lMap Φ) :=
  by simp[map, lMap_bind, Function.comp]

lemma lMap_bShift (t : Semiterm L₁ μ₁ n) : (bShift t).lMap Φ = bShift (t.lMap Φ) :=
  by simp[bShift, lMap_map]

lemma lMap_shift (t : SyntacticSemiterm L₁ n) : (shift t).lMap Φ = shift (t.lMap Φ) :=
  by simp[shift, lMap_map]

lemma lMap_free (t : SyntacticSemiterm L₁ (n + 1)) : (free t).lMap Φ = free (t.lMap Φ) :=
  by simp[free, lMap_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma lMap_fix (t : SyntacticSemiterm L₁ n) : (fix t).lMap Φ = fix (t.lMap Φ) :=
  by simp[fix, lMap_bind]; congr; funext x; cases x <;> simp

end lMap

structure Operator (L : Language.{u}) (n : ℕ) where
  term : Semiterm L Empty n

abbrev Const (L : Language.{u}) := Operator L 0

def Semiterm.fn {k} (f : L.Func k) : Operator L k := ⟨Semiterm.func f (#·)⟩

namespace Operator

def equiv : Operator L n ≃ Semiterm L Empty n where
  toFun := Operator.term
  invFun := Operator.mk
  left_inv := by intro _; simp
  right_inv := by intro _; simp

def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L μ n) : Semiterm L μ n :=
  Rew.substs v (Rew.emb o.term)

def const (c : Const L) : Semiterm L μ n := c.operator ![]

instance : Coe (Const L) (Semiterm L μ n) := ⟨Operator.const⟩

def comp (o : Operator L k) (w : Fin k → Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

lemma operator_comp (o : Operator L k) (w : Fin k → Operator L l) (v : Fin l → Semiterm L μ n) :
  (o.comp w).operator v = o.operator (fun x => (w x).operator v) := by
    simp[operator, comp, ←Rew.comp_app]; congr 1
    ext <;> simp[Rew.comp_app]; contradiction

def bvar (x : Fin n) : Operator L n := ⟨#x⟩

lemma operator_bvar (x : Fin k) (v : Fin k → Semiterm L μ n) : (bvar x).operator v = v x := by
  simp[operator, bvar]

-- f.operator ![ ... f.operator ![f.operator ![z, t 0], t 1], ... ,t (n-1)]
def foldr (f : Operator L 2) (z : Operator L k) : List (Operator L k) → Operator L k
  | []      => z
  | o :: os => f.comp ![foldr f z os, o]

@[simp] lemma foldr_nil (f : Operator L 2) (z : Operator L k) : f.foldr z [] = z := rfl

@[simp] lemma operator_foldr_cons (f : Operator L 2) (z : Operator L k) (o : Operator L k) (os : List (Operator L k))
  (v : Fin k → Semiterm L μ n) :
    (f.foldr z (o :: os)).operator v = f.operator ![(f.foldr z os).operator v, o.operator v] := by
  simp[foldr, operator_comp, Matrix.fun_eq_vec₂]

def iterr (f : Operator L 2) (z : Const L) : (n : ℕ) → Operator L n
  | 0     => z
  | _ + 1 => f.foldr (bvar 0) (List.ofFn fun x => bvar x.succ)

@[simp] lemma iterr_zero (f : Operator L 2) (z : Const L) : f.iterr z 0 = z := rfl

section numeral

protected class Zero (L : Language) where
  zero : Semiterm.Const L

protected class One (L : Language) where
  one : Semiterm.Const L

protected class Add (L : Language) where
  add : Semiterm.Operator L 2

protected class Mul (L : Language) where
  mul : Semiterm.Operator L 2

protected class Sub (L : Language) where
  sub : Semiterm.Operator L 2

protected class Div (L : Language) where
  div : Semiterm.Operator L 2

protected class Star (L : Language) where
  star : Semiterm.Const L

instance [L.Zero] : Operator.Zero L := ⟨⟨Semiterm.func Language.Zero.zero ![]⟩⟩

instance [L.One] : Operator.One L := ⟨⟨Semiterm.func Language.One.one ![]⟩⟩

instance [L.Add] : Operator.Add L := ⟨⟨Semiterm.func Language.Add.add Semiterm.bvar⟩⟩

instance [L.Mul] : Operator.Mul L := ⟨⟨Semiterm.func Language.Mul.mul Semiterm.bvar⟩⟩

instance [L.Star] : Operator.Star L := ⟨⟨Semiterm.func Language.Star.star ![]⟩⟩

lemma Zero.term_eq [L.Zero] : (@Zero.zero L _).term = Semiterm.func Language.Zero.zero ![] := rfl

lemma One.term_eq [L.One] : (@One.one L _).term = Semiterm.func Language.One.one ![] := rfl

lemma Add.term_eq [L.Add] : (@Add.add L _).term = Semiterm.func Language.Add.add Semiterm.bvar := rfl

lemma Mul.term_eq [L.Mul] : (@Mul.mul L _).term = Semiterm.func Language.Mul.mul Semiterm.bvar := rfl

lemma Star.term_eq [L.Star] : (@Star.star L _).term = Semiterm.func Language.Star.star ![] := rfl

open Language Semiterm

def numeral (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L] : ℕ → Const L
  | 0     => Zero.zero
  | n + 1 => Add.add.foldr One.one (List.replicate n One.one)

variable [hz : Operator.Zero L] [ho : Operator.One L] [ha : Operator.Add L]

lemma numeral_zero : numeral L 0 = Zero.zero := by rfl

lemma numeral_one : numeral L 1 = One.one := by rfl

lemma numeral_succ (hz : z ≠ 0) : numeral L (z + 1) = Operator.Add.add.comp ![numeral L z, One.one] := by
  simp[numeral]
  cases' z with z
  · simp at hz
  · simp[Operator.foldr]

lemma numeral_add_two : numeral L (z + 2) = Operator.Add.add.comp ![numeral L (z + 1), One.one] :=
  numeral_succ (by simp)

abbrev godelNumber (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L]
    {α : Type*} [Primcodable α] (a : α) : Semiterm.Const L :=
  Semiterm.Operator.numeral L (Encodable.encode a)

end numeral

end Operator

end Semiterm

namespace Rew

open Semiterm

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {μ μ' : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}
variable (ω : Rew L μ₁ n₁ μ₂ n₂)

protected lemma operator (o : Operator L k) (v : Fin k → Semiterm L μ₁ n₁) :
    ω (o.operator v) = o.operator (fun i => ω (v i)) := by
  simp[Operator.operator, ←comp_app]; congr 1
  ext <;> simp[comp_app]; try contradiction

protected lemma operator' (o : Operator L k) (v : Fin k → Semiterm L μ₁ n₁) :
    ω (o.operator v) = o.operator (ω ∘ v) := ω.operator o v

@[simp] lemma finitary0 (o : Operator L 0) (v : Fin 0 → Semiterm L μ₁ n₁) :
    ω (o.operator v) = o.operator ![] := by simp[ω.operator', Matrix.empty_eq]

@[simp] lemma finitary1 (o : Operator L 1) (t : Semiterm L μ₁ n₁) :
    ω (o.operator ![t]) = o.operator ![ω t] := by simp[ω.operator']

@[simp] lemma finitary2 (o : Operator L 2) (t₁ t₂ : Semiterm L μ₁ n₁) :
    ω (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp[ω.operator']

@[simp] lemma finitary3 (o : Operator L 3) (t₁ t₂ t₃ : Semiterm L μ₁ n₁) :
    ω (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp[ω.operator']

@[simp] protected lemma const (c : Const L) : ω c = c :=
  by simp[Operator.const, Empty.eq_elim]

end Rew

end FirstOrder

end LO
