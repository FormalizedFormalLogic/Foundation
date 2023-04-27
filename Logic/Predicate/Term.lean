import Logic.Predicate.Language

variable (L : Language.{u}) (L₁ L₂ L₃ : Language)

inductive SubTerm (μ : Type v) (n : ℕ)
  | bvar : Fin n → SubTerm μ n
  | fvar : μ → SubTerm μ n
  | func : ∀ {arity}, L.func arity → (Fin arity → SubTerm μ n) → SubTerm μ n

prefix:max "&" => SubTerm.fvar
prefix:max "#" => SubTerm.bvar

variable (μ : Type v) (μ₁ : Type v₁) (μ₂ : Type v₂) (μ₃ : Type v₃)

abbrev Term := SubTerm L μ 0

abbrev SyntacticSubTerm (n : ℕ) := SubTerm L ℕ n

abbrev SyntacticTerm := SyntacticSubTerm L 0

namespace SubTerm
variable {μ μ₁ μ₂ μ₃}

instance [Inhabited μ] : Inhabited (SubTerm L μ n) := ⟨&default⟩

abbrev func! (k) (f : L.func k) (v : Fin k → SubTerm L μ n) := func f v

variable {L}

variable [∀ k, ToString (L.func k)] [∀ k, ToString (L.rel k)] [ToString μ]

def toStr : SubTerm L μ n → String
  | #x                        => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x                        => "z_{" ++ toString x ++ "}"
  | func (arity := 0) c _     => toString c
  | func (arity := _ + 1) f v => "{" ++ toString f ++ "} \\left(" ++ String.vecToStr (fun i => toStr (v i)) ++ "\\right)"

instance : Repr (SubTerm L μ n) := ⟨fun t _ => toStr t⟩

instance : ToString (SubTerm L μ n) := ⟨toStr⟩

variable {n n₁ n₂ n₃ m m₁ m₂ m₃ : ℕ}

def bind (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) :
    SubTerm L μ₁ n₁ → SubTerm L μ₂ n₂
  | (#x)       => bound x    
  | (&x)       => free x
  | (func f v) => func f (fun i => (v i).bind bound free)

def map (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) : SubTerm L μ₁ n₁ → SubTerm L μ₂ n₂ :=
  bind (fun n => #(bound n)) (fun m => &(free m))

def subst (t : SubTerm L μ n) : SubTerm L μ (n + 1) → SubTerm L μ n :=
  bind (bvar <: t) fvar

def emb : SubTerm L PEmpty n → SubTerm L μ n := map id PEmpty.elim

def bShift : SubTerm L μ n → SubTerm L μ (n + 1) :=
  map Fin.succ id

def castLe {n n' : ℕ} (h : n ≤ n') : SubTerm L μ n → SubTerm L μ n' :=
  map (Fin.castLe h) id

section bind
variable (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂)

@[simp] lemma bind_fvar (m : μ₁) : (&m : SubTerm L μ₁ n₁).bind bound free = free m := rfl

@[simp] lemma bind_bvar (n : Fin n₁) : (#n : SubTerm L μ₁ n₁).bind bound free = bound n := rfl

lemma bind_func {k} (f : L.func k) (v : Fin k → SubTerm L μ₁ n₁) :
    (func f v).bind bound free = func f (fun i => (v i).bind bound free) := rfl

end bind

lemma bind_bind
  (bound₁ : Fin n₁ → SubTerm L μ₂ n₂) (free₁ : μ₁ → SubTerm L μ₂ n₂)
  (bound₂ : Fin n₂ → SubTerm L μ₃ n₃) (free₂ : μ₂ → SubTerm L μ₃ n₃) (t : SubTerm L μ₁ n₁) :
    (t.bind bound₁ free₁).bind bound₂ free₂ = t.bind (fun n => (bound₁ n).bind bound₂ free₂) (fun m => (free₁ m).bind bound₂ free₂) :=
  by induction t <;> simp[*, bind_func]

@[simp] lemma bind_id (t) : bind (L := L) (μ₁ := μ) (n₁ := n) bvar fvar t = t :=
  by induction t <;> simp[*, bind_func]

@[simp] lemma bind_id_zero (f : Fin 0 → SubTerm L μ 0) (t) : bind (L := L) (μ₁ := μ) (n₁ := 0) f fvar t = t :=
  by simpa[eq_finZeroElim] using bind_id t

lemma bind_id_of_eq (hbound : ∀ x, bound x = #x) (hfree : ∀ x, free x = &x) (t) : @bind L μ μ n n bound free t = t :=
  by
  have e₁ : bvar = bound := by funext x; simp[hbound]
  have e₂ : fvar = free := by funext x; simp[hfree]
  exact e₁ ▸ e₂ ▸ bind_id t

section map
variable (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂)

@[simp] lemma map_fvar (m : μ₁) : (&m : SubTerm L μ₁ n₁).map bound free = &(free m) := rfl

@[simp] lemma map_bvar (n : Fin n₁) : (#n : SubTerm L μ₁ n₁).map bound free = #(bound n) := rfl

lemma map_func {k} (f : L.func k) (v : Fin k → SubTerm L μ₁ n₁) :
    (func f v).map bound free = func f (fun i => (v i).map bound free) := rfl

end map

lemma map_map
  (bound₁ : Fin n₁ → Fin n₂) (free₁ : μ₁ → μ₂)
  (bound₂ : Fin n₂ → Fin n₃) (free₂ : μ₂ → μ₃) (t : SubTerm L μ₁ n₁) :
    (t.map bound₁ free₁).map bound₂ free₂ = t.map (bound₂ ∘ bound₁) (free₂ ∘ free₁) :=
  bind_bind _ _ _ _ _

@[simp] lemma map_id (t) : @map L μ μ n n id id t = t :=
  by induction t <;> simp[*, map_func]

lemma map_inj {bound : Fin n₁ → Fin n₂} {free : μ₁ → μ₂} (hb : Function.Injective bound) (hf : Function.Injective free) :
    Function.Injective $ map (L := L) bound free
  | #x,                    t => by cases t <;> simp[map_func]; intro h; exact hb h
  | &x,                    t => by cases t <;> simp[map_func]; intro h; exact hf h
  | func (arity := k) f v, t => by
    cases t <;> simp[*, map_func]
    case func =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact map_inj hb hf (congr_fun h i)

@[simp] lemma bShift_bvar (x : Fin n) : bShift (#x : SubTerm L μ n) = #(Fin.succ x) := rfl

@[simp] lemma bShift_fvar (x : μ) : bShift (&x : SubTerm L μ n) = &x := rfl

lemma bShift_func {k} (f : L.func k) (v : Fin k → SubTerm L μ n) :
  bShift (func f v) = func f (fun i => bShift (v i)) := rfl

@[simp] lemma leftConcat_bShift_comp_bvar :
    (#0 :> bShift ∘ bvar : Fin (n + 1) → SubTerm L μ (n + 1)) = bvar :=
  funext (Fin.cases (by simp) (by simp))

@[simp] lemma bShift_comp_fvar :
    (bShift ∘ fvar : μ → SubTerm L μ (n + 1)) = fvar :=
  funext (by simp)

@[simp] lemma subst_bvar_last (s : SubTerm L μ n) : subst s #(Fin.last n) = s :=
  by simp[subst]

@[simp] lemma subst_bvar_castSucc (s : SubTerm L μ n) (x : Fin n) : subst s #(Fin.castSucc x) = #x :=
  by simp[subst]

@[simp] lemma subst_fvar (s : SubTerm L μ n) (x : μ) : subst s &x = &x :=
  by simp[subst]

lemma subst_func (s : SubTerm L μ n) {k} (f : L.func k) (v : Fin k → SubTerm L μ (n + 1)) :
    subst s (func f v) = func f (fun i => subst s (v i)) :=
  by simp[subst, bind_func]

@[simp] lemma castLe_bvar {n'} (h : n ≤ n') (x : Fin n) : castLe h (#x : SubTerm L μ n) = #(Fin.castLe h x) := rfl

@[simp] lemma castLe_fvar {n'} (h : n ≤ n') (x : μ) : castLe h (&x : SubTerm L μ n) = &x := rfl

lemma castLe_func {n'} (h : n ≤ n') {k} (f : L.func k) (v : Fin k → SubTerm L μ n) :
    castLe h (func f v) = func f (fun i => castLe h (v i)) := rfl

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
   ↓free           ↑fix
  #0 #1 ... #(n - 1) &0 &1 &2 ...
 -/

def free : SyntacticSubTerm L (n + 1) → SyntacticSubTerm L n :=
  bind (bvar <: &0) (fun m => &(Nat.succ m))

def fix : SyntacticSubTerm L n → SyntacticSubTerm L (n + 1) :=
  bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ fvar)

@[simp] lemma shift_bvar (x : Fin n) : shift (#x : SyntacticSubTerm L n) = #x := rfl

@[simp] lemma shift_fvar (x : ℕ) : shift (&x : SyntacticSubTerm L n) = &(x + 1) := rfl

@[simp] lemma shift_func {k} (f : L.func k) (v : Fin k → SyntacticSubTerm L n) :
    shift (func f v) = func f (fun i => shift (v i)) := rfl

lemma shift_Injective : Function.Injective (@shift L n) :=
  Function.LeftInverse.injective (g := map id Nat.pred)
    (by intros p; simp[shift, map_map, Function.comp]; exact map_id _)

@[simp] lemma free_bvar_castSucc (x : Fin n) : free (#(Fin.castSucc x) : SyntacticSubTerm L (n + 1)) = #x := by simp[free]

@[simp] lemma free_bvar_last : free (#(Fin.last n) : SyntacticSubTerm L (n + 1)) = &0 := by simp[free]

@[simp] lemma free_fvar (x : ℕ) : free (&x : SyntacticSubTerm L (n + 1)) = &(x + 1) := by simp[free]

lemma free_func {k} (f : L.func k) (v : Fin k → SyntacticSubTerm L (n + 1)) :
    free (func f v) = func f (fun i => free $ v i) := by simp[free, bind_func]

@[simp] lemma fix_bvar (x : Fin n) : fix (#x : SyntacticSubTerm L n) = #(Fin.castSucc x) := by simp[fix]

@[simp] lemma fix_fvar_zero : fix (&0 : SyntacticSubTerm L n) = #(Fin.last n) := by simp[fix]

@[simp] lemma fix_fvar_succ (x : ℕ) : fix (&(x + 1) : SyntacticSubTerm L n) = &x := by simp[fix]

lemma fix_func {k} (f : L.func k) (v : Fin k → SyntacticSubTerm L n) :
    fix (func f v) = func f (fun i => fix $ v i) := by simp[fix, bind_func]

@[simp] lemma free_fix (t : SyntacticSubTerm L n) : free (fix t) = t :=
  by simp[free, fix, bind_bind]; exact bind_id_of_eq (by simp) (by intro x; cases x <;> simp) t

@[simp] lemma fix_free (t : SyntacticSubTerm L (n + 1)) : fix (free t) = t :=
  by simp[free, fix, bind_bind]; exact bind_id_of_eq (by intro x; cases x using Fin.lastCases <;> simp) (by simp) t

lemma bShift_free_eq_shift (t : SyntacticTerm L) : free (bShift t) = shift t :=
  by simp[free, bShift, shift, map, bind_bind, eq_finZeroElim]

end Syntactic

def fvarList : SubTerm L μ n → List μ
  | #_       => []
  | &x       => [x]
  | func _ v => List.join $ Matrix.toList (fun i => fvarList (v i))

abbrev fvar? (t : SubTerm L μ n) (x : μ) : Prop := x ∈ t.fvarList

@[simp] lemma fvarList_bvar : fvarList (#x : SubTerm L μ n) = [] := rfl

@[simp] lemma fvarList_fvar : fvarList (&x : SubTerm L μ n) = [x] := rfl

@[simp] lemma mem_fvarList_func {k} {f : L.func k} {v : Fin k → SubTerm L μ n} :
    x ∈ (func f v).fvarList ↔ ∃ i, x ∈ (v i).fvarList :=
  by simp[fvarList]

lemma bind_eq_of_funEqOn (bound : Fin n₁ → SubTerm L μ₂ n₂) (free₁ free₂ : μ₁ → SubTerm L μ₂ n₂) (t : SubTerm L μ₁ n₁)
  (h : Function.funEqOn t.fvar? free₁ free₂) :
    t.bind bound free₁ = t.bind bound free₂ := by
  induction t <;> simp[bind_func]
  case fvar => simpa[fvar?, Function.funEqOn] using h
  case func k f v ih =>
    funext i
    exact ih i (h.of_subset $ by simp[fvar?]; intro x hx; exact ⟨i, hx⟩)

variable [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

def languageFunc : SubTerm L μ n → Finset (Σ k, L.func k)
  | #_       => ∅
  | &_       => ∅
  | func f v => insert ⟨_, f⟩ $ Finset.bunionᵢ Finset.univ (fun i => languageFunc (v i))

@[simp] lemma languageFunc_func {k} (f : L.func k) (v : Fin k → SubTerm L μ n) :
    ⟨k, f⟩ ∈ (func f v).languageFunc := by simp[languageFunc]

lemma languageFunc_func_ss {k} (f : L.func k) (v : Fin k → SubTerm L μ n) (i) :
    (v i).languageFunc ⊆ (func f v).languageFunc :=
  by intros x; simp[languageFunc]; intros h; exact Or.inr ⟨i, h⟩

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
        | isTrue h => by simp[h]; exact Matrix.decVec _ _ (fun i => hasDecEq (v₁ i) (v₂ i))
        | isFalse h => isFalse (by simp[h])
      · exact isFalse (by simp[e])

instance : DecidableEq (SubTerm L μ n) := hasDecEq

end SubTerm

namespace Language

namespace Hom
variable {L L₁ L₂ L₃} {μ} (Φ : Hom L₁ L₂)

def onSubTerm (Φ : Hom L₁ L₂) : SubTerm L₁ μ n → SubTerm L₂ μ n
  | #x               => #x
  | &x               => &x
  | SubTerm.func f v => SubTerm.func (Φ.onFunc f) (fun i => onSubTerm Φ (v i))

@[simp] lemma onSubTerm_bvar (x : Fin n) : Φ.onSubTerm (#x : SubTerm L₁ μ n) = #x := rfl

@[simp] lemma onSubTerm_fvar (x : μ) : Φ.onSubTerm (&x : SubTerm L₁ μ n) = &x := rfl

lemma onSubTerm_func {k} (f : L₁.func k) (v : Fin k → SubTerm L₁ μ n) :
    Φ.onSubTerm (SubTerm.func f v) = SubTerm.func (Φ.onFunc f) (fun i => onSubTerm Φ (v i)) := rfl

end Hom

end Language

namespace SubTerm
open Language.Hom
section
variable {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂) {μ₁ μ₂ : Type _} {n₁ n₂ : ℕ}

lemma onSubTerm_bind (bound : Fin n₁ → SubTerm L₁ μ₂ n₂) (free : μ₁ → SubTerm L₁ μ₂ n₂) (t) :
    Φ.onSubTerm (bind bound free t) = bind (fun x => Φ.onSubTerm (bound x)) (fun x => Φ.onSubTerm (free x)) (Φ.onSubTerm t) :=
  by induction t <;> simp[*, onSubTerm_func, bind_func]

lemma onSubTerm_map (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (t) :
    Φ.onSubTerm (map bound free t) = map bound free (Φ.onSubTerm t) :=
  by simp[map, onSubTerm_bind]

lemma onSubTerm_subst (u) (t : SubTerm L₁ μ (n + 1)) :
    Φ.onSubTerm (subst u t) = subst (Φ.onSubTerm u) (Φ.onSubTerm t) :=
  by simp[subst, onSubTerm_bind, Matrix.comp_vecConsLast, Function.comp]

lemma onSubTerm_bShift (t : SubTerm L₁ μ₁ n) : Φ.onSubTerm (bShift t) = bShift (Φ.onSubTerm t) :=
  by simp[bShift, onSubTerm_map]

lemma onSubTerm_shift (t : SyntacticSubTerm L₁ n) : Φ.onSubTerm (shift t) = shift (Φ.onSubTerm t) :=
  by simp[shift, onSubTerm_map]

lemma onSubTerm_free (t : SyntacticSubTerm L₁ (n + 1)) : Φ.onSubTerm (free t) = free (Φ.onSubTerm t) :=
  by simp[free, onSubTerm_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma onSubTerm_fix (t : SyntacticSubTerm L₁ n) : Φ.onSubTerm (fix t) = fix (Φ.onSubTerm t) :=
  by simp[fix, onSubTerm_bind]; congr; funext x; cases x <;> simp

end

section
open Language
variable {L : Language} [∀ k, DecidableEq (L.func k)] {μ n}

def toSubLanguage' (pf : ∀ k, L.func k → Prop) (pr : ∀ k, L.rel k → Prop) : ∀ t : SubTerm L μ n,
    (∀ k f, ⟨k, f⟩ ∈ t.languageFunc → pf k f) → SubTerm (subLanguage L pf pr) μ n
  | #x,                _ => #x
  | &x,                _ => &x
  | func (arity := k) f v, h => func ⟨f, h k f (by simp)⟩
      (fun i => toSubLanguage' pf pr (v i) (fun k' f' h' => h k' f' (languageFunc_func_ss f v i h')))

@[simp] lemma onSubTerm_toSubLanguage' (pf : ∀ k, L.func k → Prop) (pr : ∀ k, L.rel k → Prop)
  (t : SubTerm L μ n) (h : ∀ k f, ⟨k, f⟩ ∈ t.languageFunc → pf k f) :
    L.ofSubLanguage.onSubTerm (t.toSubLanguage' pf pr h) = t :=
  by induction t <;> simp[*, toSubLanguage', onSubTerm_func]

end

structure Abbrev (ι : Type w) where
  func : {μ : Type v} → {n : ℕ} → (ι → SubTerm L μ n) → SubTerm L μ n
  bind_func : ∀ {μ₁ μ₂ n₁ n₂} (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (v : ι → SubTerm L μ₁ n₁),
    bind bound free (func v) = func (fun i => bind bound free (v i))

abbrev Const := Abbrev.{u,v,0} L Empty

abbrev Monadic := Abbrev L Unit

abbrev Finitary (n : ℕ) := Abbrev L (Fin n)

namespace Abbrev
variable {ι : Type w} {L : Language.{u}} {μ : Type v} {n : ℕ}

def const (c : Const L) : SubTerm L μ n := c.func Empty.elim

instance : Coe (Const L) (SubTerm L μ n) := ⟨const⟩

@[simp] lemma bind_const (c : Const L) {μ₁ μ₂ n₁ n₂} (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) :
    bind bound free c = c :=
  by simpa[const, Empty.eq_elim] using c.bind_func bound free Empty.elim

@[simp] lemma map_const (c : Const L) {μ₁ μ₂ : Type v} {n₁ n₂} (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) :
    map bound free (c : SubTerm L μ₁ n₁) = c := by simp[map]

@[simp] lemma subst_const (t : SubTerm L μ n) (c : Const L) :
    subst t c = c := by simp[subst]

@[simp] lemma emb_const (c : Const L) :
    emb (L := L) (μ := μ) (n := n) (c : SubTerm L PEmpty n) = c := by simp[emb]

@[simp] lemma shift_const (c : Const L) :
    shift (c : SyntacticSubTerm L n) = c := by simp[shift]

@[simp] lemma bShift_const (c : Const L) :
    bShift (c : SubTerm L μ (n + 1)) = c := by simp[bShift]

@[simp] lemma free_const (c : Const L) :
    free (L := L) (n := n) c = c := by simp[free]

lemma map_func (f : Abbrev L ι) {μ₁ μ₂ : Type v} {n₁ n₂} (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂)
  (v : ι → SubTerm L μ₁ n₁) :
    map bound free (f.func v) = f.func (fun i => map bound free (v i)) := f.bind_func _ _ _

lemma subst_func (t : SubTerm L μ n) (f : Abbrev L ι) (v : ι → SubTerm L μ (n + 1)) :
    subst t (f.func v) = f.func (fun i => subst t (v i)) := f.bind_func _ _ _

lemma emb_func (f : Abbrev L ι) (v : ι → SubTerm L PEmpty n) :
    emb (μ := μ) (f.func v) = f.func (fun i => emb (v i)) := f.bind_func _ _ _

lemma shift_func (f : Abbrev L ι) (v : ι → SyntacticSubTerm L n) :
    shift (f.func v) = f.func (fun i => shift (v i)) := f.bind_func _ _ _

lemma bShift_func (f : Abbrev L ι) (v : ι → SyntacticSubTerm L (n + 1)) :
    bShift (f.func v) = f.func (fun i => bShift (v i)) := f.bind_func _ _ _

lemma free_func (f : Abbrev L ι) (v : ι → SyntacticSubTerm L (n + 1)) :
    free (f.func v) = f.func (fun i => free (v i)) := f.bind_func _ _ _

end Abbrev

section natLit

open Language
variable {L}
variable [hz : L.Zero] [ho : L.One] [ha : L.Add] {μ : Type v} {μ₁ μ₂} {n : ℕ} {n₁ n₂}

def addOnes (t : SubTerm L μ n) : ℕ → SubTerm L μ n
  | 0     => t
  | z + 1 => func Language.Add.add ![addOnes t z, func Language.One.one ![]]

@[simp] lemma addOnes_zero (t : SubTerm L μ n) : addOnes t 0 = t := rfl

@[simp] lemma addOnes_succ (t : SubTerm L μ n) (z : ℕ) :
  addOnes t (z + 1) = func Language.Add.add ![addOnes t z, func Language.One.one ![]] := rfl

lemma bind_addOnes (t : SubTerm L μ₁ n₁) (z : ℕ) (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) :
    bind bound free (t.addOnes z) = (t.bind bound free).addOnes z := by
  induction z <;> simp[*, bind_func, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

-- (((((1 + 1) + 1) + 1) + 1) ...) 
def natLit' : ℕ → SubTerm L μ n
  | 0                 => func Language.Zero.zero ![]
  | z + 1             => addOnes (func Language.One.one ![]) z

variable (L)

def natLit (z : ℕ) : Const L where
  func := fun _ => natLit' z
  bind_func := by intros; cases z <;> simp[natLit', bind_func, bind_addOnes, Matrix.empty_eq]

variable {L}

abbrev sNatLit (z : ℕ) : SyntacticSubTerm L n := natLit L z

lemma natLit_zero : (natLit L 0 : SubTerm L μ n) = func Language.Zero.zero ![] := by rfl

lemma natLit_one : (natLit L 1 : SubTerm L μ n) = func Language.One.one ![] := by rfl

lemma natLit_succ (z : ℕ) (neZero : z ≠ 0) :
    (natLit L (.succ z) : SubTerm L μ n) = func Language.Add.add ![natLit L z, natLit L 1] := by
  cases z
  · contradiction
  · simp[natLit, natLit', Abbrev.const]

end natLit

declare_syntax_cat subterm
syntax:max "#" num : subterm
syntax:max "&" term:max : subterm
syntax:max "!" term:max : subterm
syntax num : subterm
syntax:70 "const" term:max : subterm
syntax:70 "func¹" term "/[" subterm:0 "]" : subterm
syntax:70 "func²" term "/[" subterm:0 "," subterm:0 "]" : subterm
syntax:50 subterm:50 "+" subterm:51 : subterm
syntax:60 subterm:60 "*" subterm:61 : subterm
syntax:65 subterm:65 "^" subterm:66 : subterm
syntax "(" subterm ")" : subterm

syntax "T“" subterm "”" : term

macro_rules
  | `(T“ # $n:num ”)                                     => `(#$n)
  | `(T“ & $n:term ”)                                    => `(&$n)
  | `(T“ ! $t:term ”)                                    => `($t)
  | `(T“ $n:num ”)                                       => `((natLit _ $n).const)
  | `(T“ const $d:term ”)                                => `(func $d ![])
  | `(T“ func¹ $d:term /[ $t:subterm ] ”)                => `(func $d ![T“$t”])
  | `(T“ func² $d:term /[ $t₁:subterm , $t₂:subterm ] ”) => `(func $d ![T“$t₁”, T“$t₂”])
  | `(T“ $t:subterm + $u:subterm ”)                      => `(func Language.Add.add ![T“$t”, T“$u”])
  | `(T“ $t:subterm * $u:subterm ”)                      => `(func Language.Mul.mul ![T“$t”, T“$u”])
  | `(T“ $t:subterm ^ $u:subterm ”)                      => `(func Language.Pow.pow ![T“$t”, T“$u”])
  | `(T“ ( $x ) ”)                                       => `(T“$x”)

#reduce (T“ func² Language.ORingFunc.mul /[&2 + &0, const Language.ORingFunc.zero]” : SubTerm Language.oring ℕ 8)
#reduce (T“(&2 + 0) * 2” : SubTerm Language.oring ℕ 8)

end SubTerm