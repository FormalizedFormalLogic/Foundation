import Logic.FirstOrder.Formula

universe u v

namespace Language

protected def empty : Language.{u} where
  func := fun _ => PEmpty
  rel  := fun _ => PEmpty

instance : Inhabited Language := ⟨Language.empty⟩

inductive GraphFunc : ℕ → Type
  | start : GraphFunc 0
  | terminal : GraphFunc 0

inductive GraphRel : ℕ → Type
  | equal : GraphRel 2
  | le : GraphRel 2

def graph : Language where
  func := GraphFunc
  rel := GraphRel

inductive BinaryRel : ℕ → Type
  | isone : BinaryRel 1
  | equal : BinaryRel 2
  | le : BinaryRel 2

def binary : Language where
  func := fun _ => Empty
  rel := BinaryRel

inductive EqRel : ℕ → Type
  | equal : EqRel 2



def equal : Language where
  func := fun _ => Empty
  rel := EqRel

instance (k) : ToString (equal.func k) := ⟨fun _ => ""⟩
instance (k) : ToString (equal.rel k) := ⟨fun _ => "\\mathrm{Equal}"⟩

structure Hom (L₁ L₂ : Language) where
  onFunc : {k : ℕ} → L₁.func k → L₂.func k
  onRel : {k : ℕ} → L₁.rel k → L₂.rel k

namespace Hom
variable (L L₁ L₂ L₃ : Language) (Φ : Hom L₁ L₂)

protected def id : Hom L L where
  onFunc := id
  onRel := id

variable {L L₁ L₂ L₃} {μ : Type _} {n : ℕ}

def onTerm (Φ : Hom L₁ L₂) : SubTerm L₁ μ n → SubTerm L₂ μ n
  | #x               => #x
  | &x               => &x
  | SubTerm.func f v => SubTerm.func (Φ.onFunc f) (fun i => onTerm Φ (v i))

@[simp] lemma onTerm_fixedVar (x : Fin n) : Φ.onTerm (#x : SubTerm L₁ μ n) = #x := rfl

@[simp] lemma onTerm_freeVar (x : μ) : Φ.onTerm (&x : SubTerm L₁ μ n) = &x := rfl

@[simp] lemma onTerm_func {k} (f : L₁.func k) (v : Fin k → SubTerm L₁ μ n) :
    Φ.onTerm (SubTerm.func f v) = SubTerm.func (Φ.onFunc f) (fun i => onTerm Φ (v i)) := rfl

def onFormula' (Φ : Hom L₁ L₂) : ∀ {n}, SubFormula L₁ μ n → SubFormula L₂ μ n
  | _, ⊤                   => ⊤ 
  | _, ⊥                   => ⊥ 
  | _, SubFormula.rel r v  => SubFormula.rel (Φ.onRel r) (fun i => Φ.onTerm (v i))
  | _, SubFormula.nrel r v => SubFormula.nrel (Φ.onRel r) (fun i => Φ.onTerm (v i))
  | _, p ⋏ q               => Φ.onFormula' p ⋏ Φ.onFormula' q
  | _, p ⋎ q               => Φ.onFormula' p ⋎ Φ.onFormula' q
  | _, ∀' p                => ∀' Φ.onFormula' p
  | _, ∃' p                => ∃' Φ.onFormula' p

lemma onFormula'_neg {n} (p : SubFormula L₁ μ n) :
    Φ.onFormula' (¬'p) = ¬' Φ.onFormula' p :=
  by induction p using SubFormula.rec' <;> simp[*, onFormula', ←SubFormula.neg_eq]

def onFormula (Φ : Hom L₁ L₂) {n} : SubFormula L₁ μ n →L SubFormula L₂ μ n where
  toFun := Φ.onFormula'
  map_top' := by simp[onFormula']
  map_bot' := by simp[onFormula']
  map_and' := by simp[onFormula']
  map_or'  := by simp[onFormula']
  map_neg' := by simp[onFormula'_neg]
  map_imp' := by simp[SubFormula.imp_eq, onFormula'_neg, ←SubFormula.neg_eq, onFormula']

@[simp] lemma onFormula_rel {k} (r : L₁.rel k) (v : Fin k → SubTerm L₁ μ n) :
    Φ.onFormula (SubFormula.rel r v) = SubFormula.rel (Φ.onRel r) (fun i => Φ.onTerm (v i)) := rfl

lemma onFormula_nrel {k} (r : L₁.rel k) (v : Fin k → SubTerm L₁ μ n) :
    Φ.onFormula (SubFormula.nrel r v) = SubFormula.nrel (Φ.onRel r) (fun i => Φ.onTerm (v i)) := rfl

lemma onFormula_all (p : SubFormula L₁ μ (n + 1)) :
    Φ.onFormula (∀' p) = ∀' Φ.onFormula p := rfl

lemma onFormula_ex (p : SubFormula L₁ μ (n + 1)) :
    Φ.onFormula (∃' p) = ∃' Φ.onFormula p := rfl

end Hom

def subLanguage (L : Language) (pfunc : ∀ k, Language.func L k → Prop) (prel : ∀ k, L.rel k → Prop) : Language where
  func := fun k => Subtype (pfunc k)
  rel  := fun k => Subtype (prel k)

end Language

variable {L : Language} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

namespace SubTerm

noncomputable def langf : SubTerm L μ n → Finset (Σ k, L.func k)
  | #_       => ∅
  | &_       => ∅
  | func f v => insert ⟨_, f⟩ $ Finset.bunionᵢ Finset.univ (fun i => langf (v i))

end SubTerm

namespace SubFormula

noncomputable def langf : ∀ {n}, SubFormula L μ n → Finset (Σ k, L.func k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  _ v => Finset.bunionᵢ Finset.univ (fun i => SubTerm.langf (v i))
  | _, nrel _ v => Finset.bunionᵢ Finset.univ (fun i => SubTerm.langf (v i))
  | _, p ⋏ q    => langf p ∪ langf q 
  | _, p ⋎ q    => langf p ∪ langf q 
  | _, ∀' p     => langf p 
  | _, ∃' p     => langf p 

noncomputable def langr : ∀ {n}, SubFormula L μ n → Finset (Σ k, L.rel k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  r _ => {⟨_, r⟩}
  | _, nrel r _ => {⟨_, r⟩}
  | _, p ⋏ q    => langr p ∪ langr q 
  | _, p ⋎ q    => langr p ∪ langr q 
  | _, ∀' p     => langr p 
  | _, ∃' p     => langr p 

def lang (p : SubFormula L μ n) : Language :=
  Language.subLanguage L (fun k f => ⟨k, f⟩ ∈ langf p) (fun k r => ⟨k, r⟩ ∈ langr p) 

end SubFormula