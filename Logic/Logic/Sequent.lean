import Logic.Logic.HilbertStyle.Basic

/-!
# Sequent calculus and variants

-/

namespace LO

scoped infixr:60 " ∷ " => Cons.cons

scoped infixr:50 " ⊹ " => Tie.tie

class SequentCalc₁ {F : outParam Type*} (R : outParam Type*) [Precollection F R] (S : Type*) where
  Sqt : S → R → Type*

notation:45 "⊢[" 𝓢 "] " Γ:46 => SequentCalc₁.Sqt 𝓢 Γ

class SequentCalc₂ {F : outParam Type*} (L R : outParam Type*) [Collection F L] [Precollection F R] (S : Type*) where
  Sqt : S → L → R → Type*

notation:45 Δ:45 " ⟹[" 𝓢 "] " Γ:46 => SequentCalc₂.Sqt 𝓢 Δ Γ

namespace SequentCalc₁

variable {F R S : Type*} [LogicalConnective F] [Collection F L] [SequentCalc₁ L S]

abbrev SingleConseq (𝓢 : S) (p : F) := ⊢[𝓢] {p}

notation:45 "⊢[" 𝓢 "]. " Γ:46 => SingleConseq 𝓢 Γ

class Weakening (𝓢 : S) where
  wk {Δ Γ : L} : Γ ⊆ Δ → ⊢[𝓢] Γ → ⊢[𝓢] Δ

class EM (𝓢 : S) where
  em {p Δ} : p ∈ Δ → ~p ∈ Δ → ⊢[𝓢] Δ

class Tait (𝓢 : S) extends Weakening 𝓢, EM 𝓢 where
  verum       : ⊢[𝓢]. ⊤
  and {p q Γ} : ⊢[𝓢] p ∷ Γ → ⊢[𝓢] q ∷ Γ → ⊢[𝓢] p ⋏ q ∷ Γ
  or {p q Γ}  : ⊢[𝓢] p ∷ q ∷ Γ → ⊢[𝓢] p ⋎ q ∷ Γ

class OCut (𝓢 : S) where
  cut {p Γ} : ⊢[𝓢] p ∷ Γ → ⊢[𝓢] ~p ∷ Γ → ⊢[𝓢] Γ

instance : System F S := ⟨(⊢[·]. ·)⟩

end SequentCalc₁

namespace SequentCalc₂

variable {F : Type*} {L R : Type*} [Collection F L] [Precollection F R] {S : Type*} [SequentCalc₂ L R S]

abbrev SingleConseq (𝓢 : S) (Γ : L) (p : F) := Γ ⟹[𝓢] {p}

notation:45 Γ:45 " ⟹[" 𝓢 "]. " p:46 => SingleConseq 𝓢 Γ p

abbrev SingleAntecedent (𝓢 : S) (p : F) (Γ : R) := {p} ⟹[𝓢] Γ

notation:45 p:45 " .⟹[" 𝓢 "] " Γ:46 => SingleAntecedent 𝓢 p Γ

abbrev SingleAntecedentConseq (𝓢 : S) (p q : F) := {p} ⟹[𝓢] {q}

notation:45 p:45 " .⟹[" 𝓢 "]. " q:46 => SingleAntecedentConseq 𝓢 p q

instance system : System F S where
  Prf (𝓢 p) := ∅ ⟹[𝓢]. p

class Id (𝓢 : S) where
  id (p) : p .⟹[𝓢]. p

class ICut (𝓢 : S) where
  icut {Γ p Δ} : Γ ⟹[𝓢]. p → p ∷ Γ ⟹[𝓢] Δ → Γ ⟹[𝓢] Δ

class Weakening (𝓢 : S) where
  wk {Γ₁ Γ₂ Δ₁ Δ₂} : Γ₁ ⊆ Γ₂ → Δ₁ ⊆ Δ₂ → Γ₁ ⟹[𝓢] Δ₁ → Γ₂ ⟹[𝓢] Δ₂

export Weakening (wk)

section

variable {𝓢 : S} [Weakening 𝓢]

def wkL {Γ₁ Γ₂ Δ} (h : Γ₁ ⊆ Γ₂) : Γ₁ ⟹[𝓢] Δ → Γ₂ ⟹[𝓢] Δ := wk h (by rfl)

def wkR {Γ Δ₁ Δ₂} (h : Δ₁ ⊆ Δ₂) : Γ ⟹[𝓢] Δ₁ → Γ ⟹[𝓢] Δ₂ := wk (by rfl) h

def closed [Id 𝓢] {Γ Δ} (p : F) : p ∈ Γ → p ∈ Δ → Γ ⟹[𝓢] Δ := fun hΓ hΔ ↦ wk (by simpa) (by simpa) (Id.id p)

def ICut.icut' [ICut 𝓢] {Γ p Δ} : Γ ⟹[𝓢]. p → p .⟹[𝓢] Δ → Γ ⟹[𝓢] Δ := fun d₁ d₂ ↦
  ICut.icut d₁ (wkL (by simp) d₂)

end

variable [LogicalConnective F]

class LJ (𝓢 : S) extends Id 𝓢, Weakening 𝓢 where
  verum (Γ)            : Γ ⟹[𝓢]. ⊤
  falsum               : ⊥ .⟹[𝓢] ∅
  negLeft {Γ p}        : Γ ⟹[𝓢]. p → ~p ∷ Γ ⟹[𝓢] ∅
  negRight {Γ p}       : p ∷ Γ ⟹[𝓢] ∅ → Γ ⟹[𝓢]. ~p
  andLeft₁ {Γ p q r}   : p ∷ Γ ⟹[𝓢]. r → p ⋏ q ∷ Γ ⟹[𝓢]. r
  andLeft₂ {Γ p q r}   : q ∷ Γ ⟹[𝓢]. r → p ⋏ q ∷ Γ ⟹[𝓢]. r
  andRight {Γ p q}     : Γ ⟹[𝓢]. p → Γ ⟹[𝓢]. q → Γ ⟹[𝓢]. p ⋏ q
  orLeft {Γ p q r}     : p ∷ Γ ⟹[𝓢]. r → q ∷ Γ ⟹[𝓢]. r → p ⋎ q ∷ Γ ⟹[𝓢]. r
  orRight₁ {Γ p q}     : Γ ⟹[𝓢]. p → Γ ⟹[𝓢]. p ⋎ q
  orRight₂ {Γ p q}     : Γ ⟹[𝓢]. q → Γ ⟹[𝓢]. p ⋎ q
  implyLeft {Γ p q r}  : Γ ⟹[𝓢]. p → q ∷ Γ ⟹[𝓢]. r → (p ⟶ q) ∷ Γ ⟹[𝓢]. r
  implyRight {Γ p q}   : p ∷ Γ ⟹[𝓢]. q → Γ ⟹[𝓢]. p ⟶ q

section LJ

variable {𝓢 : S} [LJ 𝓢]

def verum (h : ⊤ ∈ Δ) : Γ ⟹[𝓢] Δ := wkR (by simp[h]) (LJ.verum Γ)

-- def ICut.cut' [ICut 𝓢] {Γ Δ : L} (d₁ : Γ ⟹[𝓢]. p) (d₂ : p ∷ Δ ⟹[𝓢]. q) : Γ ∷+ Δ ⟹[𝓢]. q := by {  }

def explosion {Γ Δ} (h : ⊥ ∈ Γ) : Γ ⟹[𝓢] Δ := wk (by simp [h]) (by simp) LJ.falsum

def iefq (Γ p) : Γ ⟹[𝓢]. ⊥ ⟶ p := LJ.implyRight <| explosion (by simp)

def imdp [ICut 𝓢] {Γ p q} (dAB : Γ ⟹[𝓢]. p ⟶ q) (dA : Γ ⟹[𝓢]. p) : Γ ⟹[𝓢]. q :=
  let d : (p ⟶ q) ∷ p ∷ Γ ⟹[𝓢]. q := LJ.implyLeft (wkL (by simp) dA) (closed q (by simp) (by simp))
  let d : p ∷ Γ ⟹[𝓢]. q := ICut.icut (wkL (by simp) dAB) d
  ICut.icut dA d

end LJ

section Axiomatized

variable (S)

class Axiomatized [Precollection F S] where
  prfAxm {𝓢 : S} {p} : p ∈ 𝓢 → ∅ ⟹[𝓢]. p
  weakening {𝓢 𝓓 : S} (h : 𝓢 ⊆ 𝓓) {Γ Δ} : Γ ⟹[𝓢] Δ → Γ ⟹[𝓓] Δ

alias byAxm := Axiomatized.prfAxm
alias wkAxm := Axiomatized.weakening

variable [Precollection F S] [Axiomatized S]

variable {S}

def ofProof {𝓢 : S} {p} (d : 𝓢 ⊢ p) : ∅ ⟹[𝓢]. p := d

def toProof {𝓢 : S} {p} (d : ∅ ⟹[𝓢]. p) : 𝓢 ⊢ p := d

variable (S)

instance [(𝓢 : S) → LJ 𝓢] [(𝓢 : S) → ICut 𝓢] : System.DeductiveExplosion S where
  dexp {_ d p} := imdp (iefq ∅ p) (ofProof d)

instance : System.Axiomatized S where
  prfAxm {𝓢 p h} := SequentCalc₂.Axiomatized.prfAxm (by simpa using h)
  weakening {p 𝓢 𝓓 h b} := SequentCalc₂.Axiomatized.weakening h b

variable {S}

variable (𝓢 : S) [LogicalConnective F] [LJ 𝓢] [ICut 𝓢]

instance : System.ModusPonens 𝓢 where
  mdp := imdp

variable {𝓢}

lemma inconsistent_iff_nonmpty :
    System.Inconsistent 𝓢 ↔ Nonempty (∅ ⟹[𝓢] ∅) := by
  constructor
  · intro h; exact ⟨ICut.icut' (h ⊥).get LJ.falsum⟩
  · rintro ⟨b⟩ p; exact ⟨toProof <| wkR (by simp) b⟩

lemma consistent_iff_isEmpty :
    System.Consistent 𝓢 ↔ IsEmpty (∅ ⟹[𝓢] ∅) := by
  simpa [System.not_inconsistent_iff_consistent] using not_iff_not.mpr (inconsistent_iff_nonmpty (𝓢 := 𝓢))

variable (S)

class StrongCut where
  strongCut {𝓢 𝓓 : S} {Γ Δ} : 𝓓 ⊢* 𝓢 → Γ ⟹[𝓢] Δ → Γ ⟹[𝓓] Δ

end Axiomatized

section Deduction

variable (S)

variable [Cons F S]

class Deduction where
  ofInsert {𝓢 : S} {Γ p Δ} : Γ ⟹[p ∷ 𝓢] Δ → p ∷ Γ ⟹[𝓢] Δ
  inv {𝓢 : S} {Γ p Δ} : p ∷ Γ ⟹[𝓢] Δ → Γ ⟹[p ∷ 𝓢] Δ

end Deduction

end SequentCalc₂

namespace SequentCalc₂

variable {F : Type*} {L : Type*} [Collection F L] {r : Type*} [SequentCalc₂ L L S] [LogicalConnective F]

class Cut (𝓢 : S) where
  cut {Γ p Δ} : Γ ⟹[𝓢] p ∷ Δ → p ∷ Γ ⟹[𝓢] Δ → Γ ⟹[𝓢] Δ

def Cut.cut' {𝓢 : S} [Weakening 𝓢] [Cut 𝓢]
    {Γ₁ Γ₂ Δ₁ Δ₂ : L} {p} (d₁ : Γ₁ ⟹[𝓢] p ∷ Δ₁) (d₂ : p ∷ Γ₂ ⟹[𝓢] Δ₂) : Γ₁ ⊹ Γ₂ ⟹[𝓢] Δ₁ ⊹ Δ₂ :=
  let d₁ : Γ₁ ⊹ Γ₂ ⟹[𝓢] p ∷ (Δ₁ ⊹ Δ₂) := wk (by simp) (Collection.cons_subset_cons_iff <| by simp) d₁
  let d₂ : p ∷ (Γ₁ ⊹ Γ₂) ⟹[𝓢] Δ₁ ⊹ Δ₂ := wk (Collection.cons_subset_cons_iff <| by simp) (by simp) d₂
  Cut.cut d₁ d₂

class LK (𝓢 : S) extends Id 𝓢, Weakening 𝓢 where
  verum (Γ Δ)          : Γ ⟹[𝓢] ⊤ ∷ Δ
  falsum (Γ Δ)         : ⊥ ∷ Γ ⟹[𝓢] Δ
  negLeft {p Γ Δ}      : Γ ⟹[𝓢] p ∷ Δ → ~p ∷ Γ ⟹[𝓢] Δ
  negRight {p Γ Δ}     : p ∷ Γ ⟹[𝓢] Δ → Γ ⟹[𝓢] ~p ∷ Δ
  andLeft {p q Γ Δ}    : p ∷ q ∷ Γ ⟹[𝓢] Δ → p ⋏ q ∷ Γ ⟹[𝓢] Δ
  andRight {p q Γ Δ}   : Γ ⟹[𝓢] p ∷ Δ → Γ ⟹[𝓢] q ∷ Δ → Γ ⟹[𝓢] p ⋏ q ∷ Δ
  orLeft {p q Γ Δ}     : p ∷ Γ ⟹[𝓢] Δ → q ∷ Γ ⟹[𝓢] Δ → p ⋎ q ∷ Γ ⟹[𝓢] Δ
  orRight {p q Γ Δ}    : Γ ⟹[𝓢] p ∷ q ∷ Δ → Γ ⟹[𝓢] p ⋎ q ∷ Δ
  implyLeft {p q Γ Δ}  : Γ ⟹[𝓢] p ∷ Δ → q ∷ Γ ⟹[𝓢] Δ → (p ⟶ q) ∷ Γ ⟹[𝓢] Δ
  implyRight {p q Γ Δ} : p ∷ Γ ⟹[𝓢] q ∷ Δ → Γ ⟹[𝓢] (p ⟶ q) ∷ Δ

variable {𝓢 : S}

section

variable [Weakening 𝓢]

def ofSingleton {Γ p} (d : Γ ⟹[𝓢]. p) : Γ ⟹[𝓢] p ∷ ∅ := wkR (Precollection.subset_iff.mpr <| by simp) d

def ofCons {Γ p} (d : Γ ⟹[𝓢] p ∷ ∅) : Γ ⟹[𝓢]. p := wkR (Precollection.subset_iff.mpr <| by simp) d

end

section LK

variable (𝓢) [LK 𝓢]

instance : LJ 𝓢 where
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

variable {𝓢} [Cut 𝓢]

def elimNegLeft {p} (b : ~p ∷ Γ ⟹[𝓢] Δ) : Γ ⟹[𝓢] p ∷ Δ :=
  let d : p ∷ Γ ⟹[𝓢] p ∷ Δ := closed p (by simp) (by simp)
  Cut.cut (LK.negRight d) (wkR (by simp) b)

def elimNegRight {p} (b : Γ ⟹[𝓢] ~p ∷ Δ) : p ∷ Γ ⟹[𝓢] Δ :=
  let d : p ∷ Γ ⟹[𝓢] p ∷ Δ := closed p (by simp) (by simp)
  Cut.cut (wkL (by simp) b) (LK.negLeft d)

def elimImplyRight {p q} (b : Γ ⟹[𝓢] (p ⟶ q) ∷ Δ) : p ∷ Γ ⟹[𝓢] q ∷ Δ :=
  let d : (p ⟶ q) ∷ p ∷ Γ ⟹[𝓢] q ∷ Δ :=
    LK.implyLeft (closed p (by simp) (by simp)) (closed q (by simp) (by simp))
  wk (Precollection.subset_iff_set_subset_set.mpr <| by simp)
    (Precollection.subset_iff_set_subset_set.mpr <| by simp) (Cut.cut' b d)

end LK

end SequentCalc₂

abbrev SequentCalcL (F R S : Type*) [Precollection F R] := SequentCalc₂ (List F) R S

abbrev SequentCalcLL (F S : Type*) := SequentCalc₂ (List F) (List F) S

namespace SequentCalc₂

variable {F S : Type*} [LogicalConnective F] [SequentCalcLL F S]

variable {𝓢 : S} [LK 𝓢]

def rotateL {Γ Δ : List F} {p} (d : Γ ++ [p] ⟹[𝓢] Δ) : p :: Γ ⟹[𝓢] Δ := wkL (by simp) d

def rotateR {Γ Δ : List F} {p} (d : Γ ⟹[𝓢] Δ ++ [p]) : Γ ⟹[𝓢] p :: Δ := wkR (by simp) d



end SequentCalc₂
