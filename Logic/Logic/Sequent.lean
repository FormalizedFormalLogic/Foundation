import Logic.Logic.HilbertStyle.Basic

/-!
# SequentCalc calculus and variants

-/

namespace LO

class SequentCalc {F : outParam Type*} (L R : outParam Type*) [Collection F L] [Precollection F R] (C : Type*) where
  Sqt : C → L → R → Type*

notation:45 Δ:45 " ⟹[" 𝓒 "] " Γ:46 => SequentCalc.Sqt 𝓒 Δ Γ

namespace SequentCalc

variable {F : Type*} {L R : Type*} [Collection F L] [Precollection F R] {C : Type*} [SequentCalc L R C]

scoped infixr:60 " ∷ " => Cons.cons

scoped infixr:50 " ⊹ " => Tie.tie

abbrev SingleConseq (𝓒 : C) (Γ : L) (p : F) := Γ ⟹[𝓒] {p}

notation:45 Γ:45 " ⟹[" 𝓒 "]. " p:46 => SingleConseq 𝓒 Γ p

abbrev SingleAntecedent (𝓒 : C) (p : F) (Γ : R) := {p} ⟹[𝓒] Γ

notation:45 p:45 " .⟹[" 𝓒 "] " Γ:46 => SingleAntecedent 𝓒 p Γ

abbrev SingleAntecedentConseq (𝓒 : C) (p q : F) := {p} ⟹[𝓒] {q}

notation:45 p:45 " .⟹[" 𝓒 "]. " q:46 => SingleAntecedentConseq 𝓒 p q

class Id (𝓒 : C) where
  id (p) : p .⟹[𝓒]. p

class ICut (𝓒 : C) where
  icut {Γ p Δ} : Γ ⟹[𝓒]. p → p ∷ Γ ⟹[𝓒] Δ → Γ ⟹[𝓒] Δ

class Weakening (𝓒 : C) where
  wk {Γ₁ Γ₂ Δ₁ Δ₂} : Γ₁ ⊆ Γ₂ → Δ₁ ⊆ Δ₂ → Γ₁ ⟹[𝓒] Δ₁ → Γ₂ ⟹[𝓒] Δ₂

export Weakening (wk)

section

variable {𝓒 : C} [Weakening 𝓒]

def wkL {Γ₁ Γ₂ Δ} (h : Γ₁ ⊆ Γ₂) : Γ₁ ⟹[𝓒] Δ → Γ₂ ⟹[𝓒] Δ := wk h (by rfl)

def wkR {Γ Δ₁ Δ₂} (h : Δ₁ ⊆ Δ₂) : Γ ⟹[𝓒] Δ₁ → Γ ⟹[𝓒] Δ₂ := wk (by rfl) h

def closed [Id 𝓒] {Γ Δ} (p : F) : p ∈ Γ → p ∈ Δ → Γ ⟹[𝓒] Δ := fun hΓ hΔ ↦ wk (by simpa) (by simpa) (Id.id p)

def ICut.icut' [ICut 𝓒] {Γ p Δ} : Γ ⟹[𝓒]. p → p .⟹[𝓒] Δ → Γ ⟹[𝓒] Δ := fun d₁ d₂ ↦
  ICut.icut d₁ (wkL (by simp) d₂)

end

variable [LogicalConnective F]

class LJ (𝓒 : C) extends Id 𝓒, Weakening 𝓒 where
  verum (Γ)            : Γ ⟹[𝓒]. ⊤
  falsum               : ⊥ .⟹[𝓒] ∅
  negLeft {Γ p}        : Γ ⟹[𝓒]. p → ~p ∷ Γ ⟹[𝓒] ∅
  negRight {Γ p}       : p ∷ Γ ⟹[𝓒] ∅ → Γ ⟹[𝓒]. ~p
  andLeft₁ {Γ p q r}   : p ∷ Γ ⟹[𝓒]. r → p ⋏ q ∷ Γ ⟹[𝓒]. r
  andLeft₂ {Γ p q r}   : q ∷ Γ ⟹[𝓒]. r → p ⋏ q ∷ Γ ⟹[𝓒]. r
  andRight {Γ p q}     : Γ ⟹[𝓒]. p → Γ ⟹[𝓒]. q → Γ ⟹[𝓒]. p ⋏ q
  orLeft {Γ p q r}     : p ∷ Γ ⟹[𝓒]. r → q ∷ Γ ⟹[𝓒]. r → p ⋎ q ∷ Γ ⟹[𝓒]. r
  orRight₁ {Γ p q}     : Γ ⟹[𝓒]. p → Γ ⟹[𝓒]. p ⋎ q
  orRight₂ {Γ p q}     : Γ ⟹[𝓒]. q → Γ ⟹[𝓒]. p ⋎ q
  implyLeft {Γ p q r}  : Γ ⟹[𝓒]. p → q ∷ Γ ⟹[𝓒]. r → (p ⟶ q) ∷ Γ ⟹[𝓒]. r
  implyRight {Γ p q}   : p ∷ Γ ⟹[𝓒]. q → Γ ⟹[𝓒]. p ⟶ q

section LJ

variable {𝓒 : C} [LJ 𝓒]

def LJ.verum' (h : ⊤ ∈ Δ) : Γ ⟹[𝓒] Δ := wkR (by simp[h]) (LJ.verum Γ)

-- def ICut.cut' [ICut 𝓒] {Γ Δ : L} (d₁ : Γ ⟹[𝓒]. p) (d₂ : p ∷ Δ ⟹[𝓒]. q) : Γ ∷+ Δ ⟹[𝓒]. q := by {  }

def explosion {Γ Δ} (h : ⊥ ∈ Γ) : Γ ⟹[𝓒] Δ := wk (by simp [h]) (by simp) LJ.falsum

def iefq (Γ p) : Γ ⟹[𝓒]. ⊥ ⟶ p := LJ.implyRight <| explosion (by simp)

def imdp [ICut 𝓒] {Γ p q} (dAB : Γ ⟹[𝓒]. p ⟶ q) (dA : Γ ⟹[𝓒]. p) : Γ ⟹[𝓒]. q :=
  let d : (p ⟶ q) ∷ p ∷ Γ ⟹[𝓒]. q := LJ.implyLeft (wkL (by simp) dA) (closed q (by simp) (by simp))
  let d : p ∷ Γ ⟹[𝓒]. q := ICut.icut (wkL (by simp) dAB) d
  ICut.icut dA d

end LJ

section Axiomatized

variable (C)

class Axiomatized [Precollection F C] where
  prfAxm {𝓒 : C} {p} : p ∈ 𝓒 → ∅ ⟹[𝓒]. p
  weakening {𝓒 𝓓 : C} (h : 𝓒 ⊆ 𝓓) {Γ Δ} : Γ ⟹[𝓒] Δ → Γ ⟹[𝓓] Δ

alias byAxm := Axiomatized.prfAxm
alias wkAxm := Axiomatized.weakening

variable [Precollection F C] [Axiomatized C]

instance system : System F C where
  Prf (𝓒 p) := ∅ ⟹[𝓒]. p

variable {C}

def ofProof {𝓒 : C} {p} (d : 𝓒 ⊢ p) : ∅ ⟹[𝓒]. p := d

def toProof {𝓒 : C} {p} (d : ∅ ⟹[𝓒]. p) : 𝓒 ⊢ p := d

variable (C)

instance [(𝓒 : C) → LJ 𝓒] [(𝓒 : C) → ICut 𝓒] : System.DeductiveExplosion C where
  dexp {_ d p} := imdp (iefq ∅ p) (ofProof d)

instance : System.Axiomatized C where
  prfAxm {𝓒 p h} := SequentCalc.Axiomatized.prfAxm (by simpa using h)
  weakening {p 𝓒 𝓓 h b} := SequentCalc.Axiomatized.weakening h b

variable (𝓒 : C) [LogicalConnective F] [LJ 𝓒] [ICut 𝓒]

instance : System.ModusPonens 𝓒 where
  mdp := imdp

variable {𝓒}

lemma inconsistent_iff_nonmpty :
    System.Inconsistent 𝓒 ↔ Nonempty (∅ ⟹[𝓒] ∅) := by
  constructor
  · intro h; exact ⟨ICut.icut' (h ⊥).get LJ.falsum⟩
  · rintro ⟨b⟩ p; exact ⟨toProof <| wkR (by simp) b⟩

lemma consistent_iff_isEmpty :
    System.Consistent 𝓒 ↔ IsEmpty (∅ ⟹[𝓒] ∅) := by
  simpa [System.not_inconsistent_iff_consistent] using not_iff_not.mpr (inconsistent_iff_nonmpty (𝓒 := 𝓒))

end Axiomatized

end SequentCalc

namespace SequentCalc

variable {F : Type*} {L : Type*} [Collection F L] {r : Type*} [SequentCalc L L C] [LogicalConnective F]

class Cut (𝓒 : C) where
  cut {Γ p Δ} : Γ ⟹[𝓒] p ∷ Δ → p ∷ Γ ⟹[𝓒] Δ → Γ ⟹[𝓒] Δ

def Cut.cut' {𝓒 : C} [Weakening 𝓒] [Cut 𝓒]
    {Γ₁ Γ₂ Δ₁ Δ₂ : L} {p} (d₁ : Γ₁ ⟹[𝓒] p ∷ Δ₁) (d₂ : p ∷ Γ₂ ⟹[𝓒] Δ₂) : Γ₁ ⊹ Γ₂ ⟹[𝓒] Δ₁ ⊹ Δ₂ :=
  let d₁ : Γ₁ ⊹ Γ₂ ⟹[𝓒] p ∷ (Δ₁ ⊹ Δ₂) := wk (by simp) (Collection.cons_subset_cons_iff <| by simp) d₁
  let d₂ : p ∷ (Γ₁ ⊹ Γ₂) ⟹[𝓒] Δ₁ ⊹ Δ₂ := wk (Collection.cons_subset_cons_iff <| by simp) (by simp) d₂
  Cut.cut d₁ d₂

class LK (𝓒 : C) extends Id 𝓒, Weakening 𝓒 where
  verum (Γ Δ)          : Γ ⟹[𝓒] ⊤ ∷ Δ
  falsum (Γ Δ)         : ⊥ ∷ Γ ⟹[𝓒] Δ
  negLeft {p Γ Δ}      : Γ ⟹[𝓒] p ∷ Δ → ~p ∷ Γ ⟹[𝓒] Δ
  negRight {p Γ Δ}     : p ∷ Γ ⟹[𝓒] Δ → Γ ⟹[𝓒] ~p ∷ Δ
  andLeft {p q Γ Δ}    : p ∷ q ∷ Γ ⟹[𝓒] Δ → p ⋏ q ∷ Γ ⟹[𝓒] Δ
  andRight {p q Γ Δ}   : Γ ⟹[𝓒] p ∷ Δ → Γ ⟹[𝓒] q ∷ Δ → Γ ⟹[𝓒] p ⋏ q ∷ Δ
  orLeft {p q Γ Δ}     : p ∷ Γ ⟹[𝓒] Δ → q ∷ Γ ⟹[𝓒] Δ → p ⋎ q ∷ Γ ⟹[𝓒] Δ
  orRight {p q Γ Δ}    : Γ ⟹[𝓒] p ∷ q ∷ Δ → Γ ⟹[𝓒] p ⋎ q ∷ Δ
  implyLeft {p q Γ Δ}  : Γ ⟹[𝓒] p ∷ Δ → q ∷ Γ ⟹[𝓒] Δ → (p ⟶ q) ∷ Γ ⟹[𝓒] Δ
  implyRight {p q Γ Δ} : p ∷ Γ ⟹[𝓒] q ∷ Δ → Γ ⟹[𝓒] (p ⟶ q) ∷ Δ

variable {𝓒 : C}

section

variable [Weakening 𝓒]

def ofSingleton {Γ p} (d : Γ ⟹[𝓒]. p) : Γ ⟹[𝓒] p ∷ ∅ := wkR (Precollection.subset_iff.mpr <| by simp) d

def ofCons {Γ p} (d : Γ ⟹[𝓒] p ∷ ∅) : Γ ⟹[𝓒]. p := wkR (Precollection.subset_iff.mpr <| by simp) d

end

section LK

variable (𝓒) [LK 𝓒]

instance : LJ 𝓒 where
  verum (Γ) := ofCons (LK.verum Γ ∅)
  falsum := wkL (by simp) (LK.falsum ∅ ∅)
  negLeft {Γ p} (d) := LK.negLeft (ofSingleton d)
  negRight {Γ p} (d) := ofCons <| LK.negRight d
  andLeft₁ {Γ p q r} (d) := ofCons <| LK.andLeft <| wkL (Precollection.subset_iff.mpr <| by aesop) (ofSingleton d)
  andLeft₂ {Γ p q r} (d) := ofCons <| LK.andLeft <| wkL (Precollection.subset_iff.mpr <| by aesop) (ofSingleton d)
  andRight {Γ p q} (dA dB) := ofCons <| LK.andRight (ofSingleton dA) (ofSingleton dB)
  orLeft {Γ p q r} (dA dB) := ofCons <| LK.orLeft (ofSingleton dA) (ofSingleton dB)
  orRight₁ {Γ p q} (d) := ofCons <| LK.orRight <| wkR (Precollection.subset_iff.mpr <| by aesop) (ofSingleton d)
  orRight₂ {Γ p q} (d) := ofCons <| LK.orRight <| wkR (Precollection.subset_iff.mpr <| by aesop) (ofSingleton d)
  implyLeft {Γ p q r} (dA dB) := ofCons <| LK.implyLeft
    (wkR (Precollection.subset_iff.mpr <| by aesop) (ofSingleton dA))
    (ofSingleton dB)
  implyRight {Γ p q} (d) := ofCons <| LK.implyRight <| ofSingleton d

variable {𝓒} [Cut 𝓒]

def elimNegLeft {p} (b : ~p ∷ Γ ⟹[𝓒] Δ) : Γ ⟹[𝓒] p ∷ Δ :=
  let d : p ∷ Γ ⟹[𝓒] p ∷ Δ := closed p (by simp) (by simp)
  Cut.cut (LK.negRight d) (wkR (by simp) b)

def elimNegRight {p} (b : Γ ⟹[𝓒] ~p ∷ Δ) : p ∷ Γ ⟹[𝓒] Δ :=
  let d : p ∷ Γ ⟹[𝓒] p ∷ Δ := closed p (by simp) (by simp)
  Cut.cut (wkL (by simp) b) (LK.negLeft d)

def elimImplyRight {p q} (b : Γ ⟹[𝓒] (p ⟶ q) ∷ Δ) : p ∷ Γ ⟹[𝓒] q ∷ Δ :=
  let d : (p ⟶ q) ∷ p ∷ Γ ⟹[𝓒] q ∷ Δ :=
    LK.implyLeft (closed p (by simp) (by simp)) (closed q (by simp) (by simp))
  wk (Precollection.subset_iff_set_subset_set.mpr <| by simp)
    (Precollection.subset_iff_set_subset_set.mpr <| by simp) (Cut.cut' b d)

end LK

end SequentCalc

abbrev SequentCalcL (F R C : Type*) [Precollection F R] := SequentCalc (List F) R C

abbrev SequentCalcLL (F C : Type*) := SequentCalc (List F) (List F) C

namespace SequentCalc

variable {F C : Type*} [LogicalConnective F] [SequentCalcLL F C]

variable {𝓒 : C} [LK 𝓒]

def rotateL {Γ Δ : List F} {p} (d : Γ ++ [p] ⟹[𝓒] Δ) : p :: Γ ⟹[𝓒] Δ := wkL (by simp) d

def rotateR {Γ Δ : List F} {p} (d : Γ ⟹[𝓒] Δ ++ [p]) : Γ ⟹[𝓒] p :: Δ := wkR (by simp) d



end SequentCalc
