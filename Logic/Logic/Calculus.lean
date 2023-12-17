import Logic.Logic.System

namespace LO

class OneSided (F : Type u) where
  Derivation : List F → Type u

class TwoSided (F : Type u) where
  Derivation : List F → List F → Type u

prefix: 45 " ⊢¹ " => OneSided.Derivation

infix: 45 " ⊢² " => TwoSided.Derivation

class Tait (F : Type u) [LogicSymbol F] extends OneSided F where
  verum (Δ : List F)         : ⊢¹ ⊤ :: Δ
  and {p q : F} {Δ : List F} : ⊢¹ p :: Δ → ⊢¹ q :: Δ → ⊢¹ p ⋏ q :: Δ
  or {p q : F} {Δ : List F}  : ⊢¹ p :: q :: Δ → ⊢¹ p ⋎ q :: Δ
  wk {Δ Δ' : List F}         : ⊢¹ Δ → Δ ⊆ Δ' → ⊢¹ Δ'
  em {p} {Δ : List F}        : p ∈ Δ → ~p ∈ Δ → ⊢¹ Δ

class Tait.Cut (F : Type u) [LogicSymbol F] [Tait F] where
  cut {Δ : List F} {p} : ⊢¹ p :: Δ → ⊢¹ ~p :: Δ → ⊢¹ Δ

class Gentzen (F : Type u) [LogicSymbol F] extends TwoSided F where
  verum (Γ Δ : List F)                : Γ ⊢² ⊤ :: Δ
  falsum (Γ Δ : List F)               : ⊥ :: Γ ⊢² Δ
  negLeft {p : F} {Γ Δ : List F}      : Γ ⊢² p :: Δ → ~p :: Γ ⊢² Δ
  negRight {p : F} {Γ Δ : List F}     : p :: Γ ⊢² Δ → Γ ⊢² ~p :: Δ
  andLeft {p q : F} {Γ Δ : List F}    : p :: q :: Γ ⊢² Δ → p ⋏ q :: Γ ⊢² Δ
  andRight {p q : F} {Γ Δ : List F}   : Γ ⊢² p :: Δ → Γ ⊢² q :: Δ → Γ ⊢² p ⋏ q :: Δ
  orLeft {p q : F} {Γ Δ : List F}     : p :: Γ ⊢² Δ → q :: Γ ⊢² Δ → p ⋎ q :: Γ ⊢² Δ
  orRight {p q : F} {Γ Δ : List F}    : Γ ⊢² p :: q :: Δ → Γ ⊢² p ⋎ q :: Δ
  implyLeft {p q : F} {Γ Δ : List F}  : Γ ⊢² p :: Δ → q :: Γ ⊢² Δ → (p ⟶ q) :: Γ ⊢² Δ
  implyRight {p q : F} {Γ Δ : List F} : p :: Γ ⊢² q :: Δ → Γ ⊢² (p ⟶ q) :: Δ
  wk {Γ Γ' Δ Δ' : List F}             : Γ ⊢² Δ → Γ ⊆ Γ' → Δ ⊆ Δ' → Γ' ⊢² Δ'
  em {p} {Γ Δ : List F}               : p ∈ Γ → p ∈ Δ → Γ ⊢² Δ

class Gentzen.Cut (F : Type u) [LogicSymbol F] [Gentzen F] where
  cut {Γ Δ : List F} {p} : Γ ⊢² p :: Δ → p :: Γ ⊢² Δ → Γ ⊢² Δ

class LawfulGentzen (F : Type u) [LogicSymbol F] [System F] extends Gentzen F where
  toProof₁ {Γ} {T : Set F} {p : F} : Γ ⊢² [p] → (∀ q ∈ Γ, T ⊢ q) → T ⊢ p

variable {F : Type*} [LogicSymbol F]

namespace OneSided

variable [OneSided F] {Γ Δ : List F}

protected abbrev cast (d : ⊢¹ Δ) (e : Δ = Γ) : ⊢¹ Γ := cast (congrArg _ e) d

end OneSided

namespace Tait

variable [DeMorgan F] [Tait F]

variable {Γ Δ : List F}

instance : TwoSided F where
  Derivation := fun Γ Δ => ⊢¹ Γ.map (~·) ++ Δ

def ofConsLeft {p : F} {Γ Δ : List F} (b : p :: Γ ⊢² Δ) :
    ⊢¹ ~p :: (Γ.map (~·) ++ Δ) := wk b (by simp)

def ofConsRight {p : F} {Γ Δ : List F} (b : Γ ⊢² p :: Δ) :
    ⊢¹ p :: (Γ.map (~·) ++ Δ) :=
  wk b (by
    simp
    exact ⟨List.subset_cons_of_subset _ (List.subset_append_left _ _),
      List.subset_cons_of_subset _ (List.subset_append_right _ _)⟩)

def ofConsRight₂ {p q : F} {Γ Δ : List F} (b : Γ ⊢² p :: q :: Δ) :
    ⊢¹ p :: q :: (Γ.map (~·) ++ Δ) :=
  wk b (by
    simp
    exact ⟨List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $ List.subset_append_left _ _,
      List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $ List.subset_append_right _ _⟩)

def ofConsLeftRight {p q : F} {Γ Δ : List F} (b : p :: Γ ⊢² q :: Δ) :
    ⊢¹ ~p :: q :: (Γ.map (~·) ++ Δ) :=
  wk b (by
    simp
    exact ⟨List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $ List.subset_append_left _ _,
      List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $ List.subset_append_right _ _⟩)

def toConsLeft {p : F} {Γ Δ : List F}
    (b : ⊢¹ ~p :: (Γ.map (~·) ++ Δ)) :
    p :: Γ ⊢² Δ := wk b (by simp)

def toConsRight {p : F} {Γ Δ : List F}
    (b : ⊢¹ p :: (Γ.map (~·) ++ Δ)) :
    Γ ⊢² p :: Δ :=
  wk b (by
    simp
    exact List.subset_append_of_subset_right _ (List.subset_cons _ _))

instance : Gentzen F where
  verum := fun _ _ => toConsRight (verum _)
  falsum := fun _ _ => toConsLeft (by simpa using verum _)
  negLeft := fun b => toConsLeft (OneSided.cast (ofConsRight b) (by simp))
  negRight := fun b => toConsRight (OneSided.cast (ofConsLeft b) (by simp))
  andLeft := fun b => OneSided.cast (or b) (by simp)
  andRight := fun bp bq =>
    toConsRight (OneSided.cast (and (ofConsRight bp) (ofConsRight bq)) (by simp))
  orLeft := fun bp bq =>
    toConsLeft (OneSided.cast (and (ofConsLeft bp) (ofConsLeft bq)) (by simp))
  orRight := fun b => toConsRight (OneSided.cast (or $ ofConsRight₂ b) (by simp))
  implyLeft := fun bp bq =>
    toConsLeft (OneSided.cast (and (ofConsRight bp) (ofConsLeft bq)) (by simp[DeMorgan.imply]))
  implyRight := fun b =>
    toConsRight (OneSided.cast (or $ ofConsLeftRight b) (by simp[DeMorgan.imply]))
  wk := fun b hΓ hΔ => wk b (by
    simp
    exact ⟨List.subset_append_of_subset_left _ $ List.map_subset _ hΓ,
      List.subset_append_of_subset_right _ $ hΔ⟩)
  em := fun {p} _ _ hΓ hΔ => em (p := p)
    (List.mem_append.mpr $ .inr $ hΔ)
    (List.mem_append.mpr $ .inl $ List.mem_map_of_mem (~·) hΓ)

variable [Tait.Cut F]

instance : Gentzen.Cut F := ⟨fun d d' => Cut.cut (ofConsRight d) (ofConsLeft d')⟩

end Tait

namespace Gentzen

variable [Gentzen F]

def wkLeft {Γ Γ' Δ : List F} (d : Γ ⊢² Δ) (ss : Γ ⊆ Γ') : Γ' ⊢² Δ := wk d ss (by simp)

def wkRight {Γ Δ Δ' : List F} (d : Γ ⊢² Δ) (ss : Δ ⊆ Δ') : Γ ⊢² Δ' := wk d (by simp) ss

structure DerivationM (T : Set F) (Γ : List F) where
  antecedent : List F
  antecedent_ss : ∀ p ∈ antecedent, p ∈ T
  bew : antecedent ⊢² Γ

infix: 45 " ⊢²' " => DerivationM

variable {T : Set F} {Γ Δ E : List F}

def DerivationM.weakening {T U : Set F} {Γ : List F} (b : T ⊢²' Γ) (h : T ⊆ U) : U ⊢²' Γ where
  antecedent := b.antecedent
  antecedent_ss := fun p hp => h (b.antecedent_ss p hp)
  bew := b.bew


def proofOfDerivation {Γ Δ} (d : Γ ⊢² Δ) (ss : ∀ p ∈ Γ, p ∈ T) : T ⊢²' Δ where
  antecedent := Γ
  antecedent_ss := ss
  bew := d

variable [Gentzen.Cut F]

def Cut.cut' {Γ₁ Γ₂ Δ₁ Δ₂ : List F} (d₁ : Γ₁ ⊢² p :: Δ₁) (d₂ : p :: Γ₂ ⊢² Δ₂) : Γ₁ ++ Γ₂ ⊢² Δ₁ ++ Δ₂ :=
  let d₁ : Γ₁ ++ Γ₂ ⊢² p :: (Δ₁ ++ Δ₂) := wk d₁ (by simp) (List.cons_subset_cons _ $ by simp)
  let d₂ : p :: (Γ₁ ++ Γ₂) ⊢² Δ₁ ++ Δ₂ := wk d₂ (List.cons_subset_cons _ $ by simp) (by simp)
  Cut.cut d₁ d₂

namespace DerivationM

def wk (b : T ⊢²' Γ) (ss : Γ ⊆ Γ') : T ⊢²' Γ' where
  antecedent := b.antecedent
  antecedent_ss := b.antecedent_ss
  bew := wkRight b.bew ss

def cut (b : T ⊢²' p :: Γ) (b' : T ⊢²' ~p :: Γ) : T ⊢²' Γ where
  antecedent := b.antecedent ++ b'.antecedent
  antecedent_ss := by
    simp
    rintro p (hp | hp)
    · exact b.antecedent_ss _ hp
    · exact b'.antecedent_ss _ hp
  bew :=
    let d : b.antecedent ++ b'.antecedent ⊢² p :: Γ := wkLeft b.bew (by simp)
    let d' : b.antecedent ++ b'.antecedent ⊢² ~p :: Γ := wkLeft b'.bew (by simp)
    Cut.cut d' (negLeft d)

def cut' (b : T ⊢²' p :: Γ) (b' : T ⊢²' ~p :: Δ) : T ⊢²' Γ ++ Δ where
  antecedent := b.antecedent ++ b'.antecedent
  antecedent_ss := by
    simp
    rintro p (hp | hp)
    · exact b.antecedent_ss _ hp
    · exact b'.antecedent_ss _ hp
  bew := by
    let d : b.antecedent ++ b'.antecedent ⊢² p :: Γ := wkLeft b.bew (by simp)
    let d' : b.antecedent ++ b'.antecedent ⊢² ~p :: Δ := wkLeft b'.bew (by simp)
    exact Gentzen.wk (Cut.cut' d' (negLeft d)) (by simp) (by simp)

end DerivationM

variable (F)

def system : System F where
  Bew := fun T p => T ⊢²' [p]
  axm := fun {T p} h =>
    ⟨[p], by simpa,
      em (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl)⟩
  weakening' := fun ss b => b.weakening ss

variable {F}

def toProof :
    letI := system F
    {Γ Δ : List F} → Γ ⊢² Δ → (∀ q ∈ Γ, T ⊢ q) → T ⊢²' Δ
  | [],     _, d, _ => proofOfDerivation d (by simp)
  | q :: Γ, Δ, d, h =>
    let bn : T ⊢²' ~q :: Δ := toProof (negRight d) (fun q hq => h q (by simp[hq]))
    let b : T ⊢²' [q] := h q (by simp)
    b.cut' bn

instance : letI := system F; LawfulGentzen F :=
  letI := system F; ⟨toProof⟩

end Gentzen

namespace LawfulGentzen

variable [System F] [LawfulGentzen F]

def toProofOfNil {p : F} (b : [] ⊢² [p]) (T : Set F) : T ⊢ p :=
  toProof₁ b (by intro q h; exact False.elim ((List.mem_nil_iff q).mp h))

lemma toProof₁! {Γ} {T : Set F} {p : F} (b : Γ ⊢² [p]) (H : ∀ q ∈ Γ, T ⊢! q) : T ⊢! p :=
  ⟨toProof₁ b (fun q hq => (H q hq).toProof)⟩

end LawfulGentzen

end LO
