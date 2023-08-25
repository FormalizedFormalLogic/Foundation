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

structure Hom (L : ℕ → Type u) (μ₁ : Type ν₁) (n₁ : ℕ) (μ₂ : Type ν₂) (n₂ : ℕ) where
  toFun : SubTerm L μ₁ n₁ → SubTerm L μ₂ n₂
  func' : ∀ {k} (f : L k) (v : Fin k → SubTerm L μ₁ n₁), toFun (func f v) = func f (fun i => toFun (v i))

abbrev SyntacticHom (L : ℕ → Type u) (n₁ n₂ : ℕ) := Hom L ℕ n₁ ℕ n₂

namespace Hom

variable (ω : Hom L μ₁ n₁ μ₂ n₂)

instance : FunLike (Hom L μ₁ n₁ μ₂ n₂) (SubTerm L μ₁ n₁) (fun _ => SubTerm L μ₂ n₂) where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by rcases f; rcases g; simp; exact h

instance : CoeFun (Hom L μ₁ n₁ μ₂ n₂) (fun _ => SubTerm L μ₁ n₁ → SubTerm L μ₂ n₂) := ⟨Hom.toFun⟩

-- hide Hom.toFun
open Lean PrettyPrinter Delaborator SubExpr in
@[app_unexpander toFun]
def unexpsnderToFun : Unexpander
  | `($_ $h $x) => `($h $x)
  | _           => throw ()

@[ext] lemma ext (ω₁ ω₂ : Hom L μ₁ n₁ μ₂ n₂) (h : ∀ t, ω₁ t = ω₂ t) : ω₁ = ω₂ := FunLike.ext ω₁ ω₂ h

protected lemma func {k} (f : L k) (v : Fin k → SubTerm L μ₁ n₁) :
    ω (func f v) = func f (fun i => ω (v i)) := ω.func' f v

lemma func'' {k} (f : L k) (v : Fin k → SubTerm L μ₁ n₁) :
    ω (func f v) = func f (ω ∘ v) := ω.func' f v

@[simp] lemma func0 (f : L 0) (v : Fin 0 → SubTerm L μ₁ n₁) :
    ω (func f v) = func f ![] := by simp[Hom.func]

@[simp] lemma func1 (f : L 1) (t : SubTerm L μ₁ n₁) :
    ω (func f ![t]) = func f ![ω t] := by simp[Matrix.constant_eq_singleton, Hom.func]

@[simp] lemma func2 (f : L 2) (t₁ t₂ : SubTerm L μ₁ n₁) :
    ω (func f ![t₁, t₂]) = func f ![ω t₁, ω t₂] := by simp[Hom.func]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma func3 (f : L 3) (t₁ t₂ t₃ : SubTerm L μ₁ n₁) :
    ω (func f ![t₁, t₂, t₃]) = func f ![ω t₁, ω t₂, ω t₃] := by
  simp[Hom.func]; funext i; induction' i using Fin.induction with i <;> simp; induction' i using Fin.induction with i <;> simp 

end Hom

def bindAux (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂) : SubTerm L μ₁ n₁ → SubTerm L μ₂ n₂
  | (#x)       => b x    
  | (&x)       => e x
  | (func f v) => func f (fun i => (v i).bindAux b e)

def bind (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂) : Hom L μ₁ n₁ μ₂ n₂ where
  toFun := bindAux b e
  func' := fun _ _ => rfl

abbrev rewrite (f : μ₁ → SubTerm L μ₂ n) : SubTerm L μ₁ n → SubTerm L μ₂ n := bind SubTerm.bvar f

abbrev rewrite1 (t : SyntacticSubTerm L n) : SyntacticSubTerm L n → SyntacticSubTerm L n := bind SubTerm.bvar (t :>ₙ fvar)

def map (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) : Hom L μ₁ n₁ μ₂ n₂ :=
  bind (fun n => #(b n)) (fun m => &(e m))

def substs {n'} (v : Fin n → SubTerm L μ n') : Hom L μ n μ n' :=
  bind v fvar

scoped[FirstOrder] notation "ᵀ⟦→ " v "⟧" => SubTerm.substs v
scoped[FirstOrder] notation "ᵀ⟦↦ " t "⟧" => SubTerm.substs ![t]

def emb {o : Type w} [h : IsEmpty o] : Hom L o n μ n := map id h.elim'

def bShift : Hom L μ n μ (n + 1) :=
  map Fin.succ id

def castLe {n n' : ℕ} (h : n ≤ n') : Hom L μ n μ n' :=
  map (Fin.castLe h) id

section bind

variable (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂)

@[simp] lemma bind_fvar (m : μ₁) : bind b e (&m : SubTerm L μ₁ n₁) = e m := rfl

@[simp] lemma bind_bvar (n : Fin n₁) : bind b e (#n : SubTerm L μ₁ n₁) = b n := rfl

@[simp] lemma bind_fbar' : bind b e ∘ fvar = e := by funext x; simp

@[simp] lemma bind_bbar' : bind b e ∘ bvar = b := by funext x; simp

lemma bind_bind
  (b₁ : Fin n₁ → SubTerm L μ₂ n₂) (e₁ : μ₁ → SubTerm L μ₂ n₂)
  (b₂ : Fin n₂ → SubTerm L μ₃ n₃) (e₂ : μ₂ → SubTerm L μ₃ n₃) (t : SubTerm L μ₁ n₁) :
    bind b₂ e₂ (bind b₁ e₁ t) = bind (fun n => bind b₂ e₂ (b₁ n)) (fun m => bind b₂ e₂ (e₁ m)) t :=
  by induction t <;> simp[*, Hom.func]

lemma bind_bind'
  (b₁ : Fin n₁ → SubTerm L μ₂ n₂) (e₁ : μ₁ → SubTerm L μ₂ n₂)
  (b₂ : Fin n₂ → SubTerm L μ₃ n₃) (e₂ : μ₂ → SubTerm L μ₃ n₃) (t : SubTerm L μ₁ n₁) :
    bind b₂ e₂ (bind b₁ e₁ t) = bind (bind b₂ e₂ ∘ b₁) (bind b₂ e₂ ∘ e₁) t :=
  bind_bind _ _ _ _ _

@[simp] lemma bind_id (t) : bind (L := L) (μ₁ := μ) (n₁ := n) bvar fvar t = t :=
  by induction t <;> simp[*, Hom.func]

@[simp] lemma bind_id_zero (f : Fin 0 → SubTerm L μ 0) (t) : bind (L := L) (μ₁ := μ) (n₁ := 0) f fvar t = t :=
  by simpa[eq_finZeroElim] using bind_id t

lemma bind_id_of_eq {b : Fin n → SubTerm L μ n} {e : μ → SubTerm L μ n}
  (hb : ∀ x, b x = #x) (he : ∀ x, e x = &x) (t) : bind b e t = t := by
  have e₁ : bvar = b := by funext x; simp[hb]
  have e₂ : fvar = e := by funext x; simp[he]
  exact e₁ ▸ e₂ ▸ bind_id t

lemma Hom.eq_bind (ω : Hom L μ₁ n₁ μ₂ n₂) : ω = bind (ω ∘ bvar) (ω ∘ fvar) := by
  ext t; induction t <;> simp[Hom.func'']; funext; simp[*]

end bind

section map

variable (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂)

@[simp] lemma map_fvar (m : μ₁) : map b e (&m : SubTerm L μ₁ n₁) = &(e m) := rfl

@[simp] lemma map_bvar (n : Fin n₁) : map b e (#n : SubTerm L μ₁ n₁) = #(b n) := rfl

@[simp] lemma map_fvar' : map (L := L) b e ∘ fvar = fvar ∘ e := rfl

@[simp] lemma map_bvar' : map (L := L) b e ∘ bvar = bvar ∘ b := rfl

lemma map_map
  (b₁ : Fin n₁ → Fin n₂) (e₁ : μ₁ → μ₂)
  (b₂ : Fin n₂ → Fin n₃) (e₂ : μ₂ → μ₃) (t : SubTerm L μ₁ n₁) :
    map b₂ e₂ (map b₁ e₁ t) = map (b₂ ∘ b₁) (e₂ ∘ e₁) t :=
  bind_bind _ _ _ _ _

@[simp] lemma map_id (t) : @map L μ μ n n id id t = t :=
  by induction t <;> simp[*, Hom.func]

lemma map_inj {b : Fin n₁ → Fin n₂} {e : μ₁ → μ₂} (hb : Function.Injective b) (he : Function.Injective e) :
    Function.Injective $ map (L := L) b e
  | #x,                    t => by cases t <;> simp[Hom.func]; intro h; exact hb h
  | &x,                    t => by cases t <;> simp[Hom.func]; intro h; exact he h
  | func (arity := k) f v, t => by
    cases t <;> simp[*, Hom.func]
    case func =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact map_inj hb he (congr_fun h i)

end map

section emb

variable {o : Type w} [IsEmpty o]

@[simp] lemma emb_bvar (x : Fin n) : emb (μ := μ) (#x : SubTerm L o n) = #x := rfl

end emb

section bShift

@[simp] lemma bShift_bvar (x : Fin n) : bShift (#x : SubTerm L μ n) = #(Fin.succ x) := rfl

@[simp] lemma bShift_fvar (x : μ) : bShift (&x : SubTerm L μ n) = &x := rfl

lemma bShift_func {k} (f : L k) (v : Fin k → SubTerm L μ n) :
  bShift (func f v) = func f (fun i => bShift (v i)) := rfl

@[simp] lemma leftConcat_bShift_comp_bvar :
    (#0 :> bShift ∘ bvar : Fin (n + 1) → SubTerm L μ (n + 1)) = bvar :=
  funext (Fin.cases (by simp) (by simp))

@[simp] lemma bShift_comp_fvar :
    (bShift ∘ fvar : μ → SubTerm L μ (n + 1)) = fvar :=
  funext (by simp)

end bShift

section substs

variable {n'} (w : Fin n → SubTerm L μ n')

@[simp] lemma substs_zero (w : Fin 0 → SubTerm L μ 0) (t : SubTerm L μ 0) : substs w t = t :=
  by simp[substs]

@[simp] lemma substs_bvar (x : Fin n) : substs w #x = w x :=
  by simp[substs]

@[simp] lemma substs_fvar (x : μ) : substs w &x = &x :=
  by simp[substs]

lemma substs_substs {l k} (v : Fin l → SubTerm L μ k) (w : Fin k → SubTerm L μ n) (t) :
    substs w (substs v t) = substs (substs w ∘ v) t :=
  by simp[substs, bind_bind, Function.comp]

end substs

@[simp] lemma castLe_bvar {n'} (h : n ≤ n') (x : Fin n) : castLe h (#x : SubTerm L μ n) = #(Fin.castLe h x) := rfl

@[simp] lemma castLe_fvar {n'} (h : n ≤ n') (x : μ) : castLe h (&x : SubTerm L μ n) = &x := rfl

lemma castLe_func {n'} (h : n ≤ n') {k} (f : L k) (v : Fin k → SubTerm L μ n) :
    castLe h (func f v) = func f (fun i => castLe h (v i)) := rfl

section Syntactic

/-
  #0 #1 ... #(n - 1) &0 &1 ...
   ↓shift
  #0 #1 ... #(n - 1) &1 &2 &3 ...
-/

def shift : SyntacticHom L n n := map id Nat.succ

/- 
  #0 #1 ... #(n - 1) #n &0 &1 ...
   ↓free           ↑fix
  #0 #1 ... #(n - 1) &0 &1 &2 ...
 -/

def free : SyntacticHom L (n + 1) n := bind (bvar <: &0) (fun m => &(Nat.succ m))

def fix : SyntacticHom L n (n + 1) := bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ fvar)

section shift

@[simp] lemma shift_bvar (x : Fin n) : shift (#x : SyntacticSubTerm L n) = #x := rfl

@[simp] lemma shift_fvar (x : ℕ) : shift (&x : SyntacticSubTerm L n) = &(x + 1) := rfl

lemma shift_func {k} (f : L k) (v : Fin k → SyntacticSubTerm L n) :
    shift (func f v) = func f (fun i => shift (v i)) := rfl

lemma shift_Injective : Function.Injective (@shift L n) :=
  Function.LeftInverse.injective (g := map id Nat.pred)
    (by intros p; simp[shift, map_map, Function.comp]; exact map_id _)

end shift

section free

@[simp] lemma free_bvar_castSucc (x : Fin n) : free (#(Fin.castSucc x) : SyntacticSubTerm L (n + 1)) = #x := by simp[free]

@[simp] lemma free_bvar_last : free (#(Fin.last n) : SyntacticSubTerm L (n + 1)) = &0 := by simp[free]

@[simp] lemma free_bvar_last_zero : free (#0 : SyntacticSubTerm L 1) = &0 := free_bvar_last

@[simp] lemma free_fvar (x : ℕ) : free (&x : SyntacticSubTerm L (n + 1)) = &(x + 1) := by simp[free]

end free

section fix

@[simp] lemma fix_bvar (x : Fin n) : fix (#x : SyntacticSubTerm L n) = #(Fin.castSucc x) := by simp[fix]

@[simp] lemma fix_fvar_zero : fix (&0 : SyntacticSubTerm L n) = #(Fin.last n) := by simp[fix]

@[simp] lemma fix_fvar_succ (x : ℕ) : fix (&(x + 1) : SyntacticSubTerm L n) = &x := by simp[fix]

end fix

@[simp] lemma free_fix (t : SyntacticSubTerm L n) : free (fix t) = t :=
  by simp[free, fix, bind_bind]; exact bind_id_of_eq (by simp) (by intro x; cases x <;> simp) t

@[simp] lemma fix_free (t : SyntacticSubTerm L (n + 1)) : fix (free t) = t :=
  by simp[free, fix, bind_bind]; exact bind_id_of_eq (by intro x; cases x using Fin.lastCases <;> simp) (by simp) t

@[simp] lemma bShift_free_eq_shift (t : SyntacticTerm L) : free (bShift t) = shift t :=
  by simp[free, bShift, shift, map, bind_bind, eq_finZeroElim]

lemma substs_eq_substs1 (w : Fin (n + 1) → SyntacticTerm L) (t : SyntacticSubTerm L (n + 1)) :
    substs w t = substs ![w $ Fin.last n] (fix $ substs (shift ∘ w ∘ Fin.castSucc) $ free t) :=
  by simp[substs, free, fix, bind_bind]; congr; funext x; cases x using Fin.lastCases <;> simp[shift, map, bind_bind]

end Syntactic

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
  induction t <;> simp[Hom.func]
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
  by induction t <;> simp[*, lMap_func, Hom.func]

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
  bind_operator : ∀ {μ μ' n₁ n₂} (b : Fin n₁ → SubTerm L μ' n₂) (e : μ → SubTerm L μ' n₂) (v : ι → SubTerm L μ n₁),
    bind b e (operator v) = operator (fun i => bind b e (v i))

abbrev Const (L : ℕ → Type u) := Operator.{u,v,0} L Empty

abbrev Monadic (L : ℕ → Type u) := Operator L Unit

abbrev Finitary (L : ℕ → Type u) (n : ℕ) := Operator L (Fin n)

namespace Operator

variable {ι : Type w}

def const (c : Const L) : SubTerm L μ n := c.operator Empty.elim

instance : Coe (Const L) (SubTerm L μ n) := ⟨const⟩

lemma bind_const (b : Fin n₁ → SubTerm L μ' n₂) (e : μ → SubTerm L μ' n₂) (c : Const L) :
    bind b e c = c :=
  by simpa[const, Empty.eq_elim] using c.bind_operator b e Empty.elim

end Operator

namespace Hom

variable (ω : Hom L μ n₁ μ' n₂)

protected lemma operator (o : Operator L ι) (v : ι → SubTerm L μ n₁) :
    ω (o.operator v) = o.operator (fun i => ω (v i)) := by rw[ω.eq_bind]; exact o.bind_operator _ _ _

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

@[simp] protected lemma const (c : Const L) :
    ω c = c := by rw[ω.eq_bind]; exact Operator.bind_const _ _ _

end Hom

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

lemma Hom.addOnes (ω : Hom L μ₁ n₁ μ₂ n₂) (t : SubTerm L μ₁ n₁) (z : ℕ) :
    ω (t.addOnes z) = (ω t).addOnes z := by induction z <;> simp[*]

-- (((((1 + 1) + 1) + 1) + 1) ... ) 
def natLit' : ℕ → SubTerm L μ n
  | 0     => func Language.Zero.zero ![]
  | z + 1 => addOnes (func Language.One.one ![]) z

variable (L)

def natLit (z : ℕ) : Const L where
  operator := fun _ => natLit' z
  bind_operator := by intros; cases z <;> simp[natLit', Hom.addOnes, Matrix.empty_eq]

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

end FirstOrder
