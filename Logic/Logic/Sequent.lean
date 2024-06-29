import Logic.Logic.System

/-!
# TwosidedCalc calculus and variants

-/

namespace LO

class TwosidedCalc {F : outParam Type*} (L R : outParam Type*) [Collection F L] [Precollection F R] (C : Type*) where
  Sqt : C → L → R → Type*

notation:45 Δ:45 " ⟹[" 𝓒 "] " Γ:46 => TwosidedCalc.Sqt 𝓒 Δ Γ

namespace TwosidedCalc

variable {F : Type*} {L R : Type*} [Collection F L] [Precollection F R] {C : Type*} [TwosidedCalc L R C]

scoped infixr:60 " ∷ " => Cons.cons

scoped infixr:50 " ⊹ " => Tie.tie

abbrev SingleConseq (𝓒 : C) (Γ : L) (A : F) := Γ ⟹[𝓒] {A}

notation:45 Γ:45 " ⟹[" 𝓒 "]. " A:46 => SingleConseq 𝓒 Γ A

abbrev SingleAntecedent (𝓒 : C) (A : F) (Γ : R) := {A} ⟹[𝓒] Γ

notation:45 A:45 " .⟹[" 𝓒 "] " Γ:46 => SingleAntecedent 𝓒 A Γ

abbrev SingleAntecedentConseq (𝓒 : C) (A B : F) := {A} ⟹[𝓒] {B}

notation:45 A:45 " .⟹[" 𝓒 "]. " B:46 => SingleAntecedentConseq 𝓒 A B

class Id (𝓒 : C) where
  id (A) : A .⟹[𝓒]. A

class ICut (𝓒 : C) where
  icut {Γ A Δ} : Γ ⟹[𝓒]. A → A ∷ Δ ⟹[𝓒] Λ → Γ ⟹[𝓒] Λ

class Weakening (𝓒 : C) where
  wk {Γ₁ Γ₂ Δ₁ Δ₂} : Γ₁ ⊆ Γ₂ → Δ₁ ⊆ Δ₂ → Γ₁ ⟹[𝓒] Δ₁ → Γ₂ ⟹[𝓒] Δ₂

export Weakening (wk)

section

variable {𝓒 : C} [Weakening 𝓒]

def wkL {Γ₁ Γ₂ Δ} (h : Γ₁ ⊆ Γ₂) : Γ₁ ⟹[𝓒] Δ → Γ₂ ⟹[𝓒] Δ := wk h (by rfl)

def wkR {Γ Δ₁ Δ₂} (h : Δ₁ ⊆ Δ₂) : Γ ⟹[𝓒] Δ₁ → Γ ⟹[𝓒] Δ₂ := wk (by rfl) h

def closed [Id 𝓒] {Γ Δ} (A : F) : A ∈ Γ → A ∈ Δ → Γ ⟹[𝓒] Δ := fun hΓ hΔ ↦ wk (by simpa) (by simpa) (Id.id A)

end

variable [LogicalConnective F]

class LJ (𝓒 : C) extends Id 𝓒, Weakening 𝓒 where
  verum (Γ)            : Γ ⟹[𝓒]. ⊤
  falsum               : ⊥ .⟹[𝓒] ∅
  negLeft {Γ A}        : Γ ⟹[𝓒]. A → ~A ∷ Γ ⟹[𝓒] ∅
  negRight {Γ A}       : A ∷ Γ ⟹[𝓒] ∅ → Γ ⟹[𝓒]. ~A
  andLeft₁ {Γ A B C}   : A ∷ Γ ⟹[𝓒]. C → A ⋏ B ∷ Γ ⟹[𝓒]. C
  andLeft₂ {Γ A B C}   : B ∷ Γ ⟹[𝓒]. C → A ⋏ B ∷ Γ ⟹[𝓒]. C
  andRight {Γ A B}     : Γ ⟹[𝓒]. A → Γ ⟹[𝓒]. B → Γ ⟹[𝓒]. A ⋏ B
  orLeft {Γ A B C}     : A ∷ Γ ⟹[𝓒]. C → B ∷ Γ ⟹[𝓒]. C → A ⋎ B ∷ Γ ⟹[𝓒]. C
  orRight₁ {Γ A B}     : Γ ⟹[𝓒]. A → Γ ⟹[𝓒]. A ⋎ B
  orRight₂ {Γ A B}     : Γ ⟹[𝓒]. B → Γ ⟹[𝓒]. A ⋎ B
  implyLeft {Γ A B C}  : Γ ⟹[𝓒]. A → B ∷ Γ ⟹[𝓒]. C → (A ⟶ B) ∷ Γ ⟹[𝓒]. C
  implyRight {Γ A B}   : A ∷ Γ ⟹[𝓒]. B → Γ ⟹[𝓒]. (A ⟶ B)

section LJ

variable {𝓒 : C} [LJ 𝓒]

def LJ.verum' (h : ⊤ ∈ Δ) : Γ ⟹[𝓒] Δ := wkR (by simp[h]) (LJ.verum Γ)

-- def ICut.cut' [ICut 𝓒] {Γ Δ : L} (d₁ : Γ ⟹[𝓒]. A) (d₂ : A ∷ Δ ⟹[𝓒]. B) : Γ ∷+ Δ ⟹[𝓒]. B := by {  }

end LJ

end TwosidedCalc

namespace TwosidedCalc

variable {F : Type*} {L : Type*} [Collection F L] {C : Type*} [TwosidedCalc L L C] [LogicalConnective F]

class Cut (𝓒 : C) where
  cut {Γ Δ Λ} : Γ ⟹[𝓒] Δ → Δ ⟹[𝓒] Λ → Γ ⟹[𝓒] Λ

class LK (𝓒 : C) extends Id 𝓒, Weakening 𝓒 where
  verum (Γ Δ)          : Γ ⟹[𝓒] ⊤ ∷ Δ
  falsum (Γ Δ)         : ⊥ ∷ Γ ⟹[𝓒] Δ
  negLeft {A Γ Δ}      : Γ ⟹[𝓒] A ∷ Δ → ~A ∷ Γ ⟹[𝓒] Δ
  negRight {A Γ Δ}     : A ∷ Γ ⟹[𝓒] Δ → Γ ⟹[𝓒] ~A ∷ Δ
  andLeft {A B Γ Δ}    : A ∷ B ∷ Γ ⟹[𝓒] Δ → A ⋏ B ∷ Γ ⟹[𝓒] Δ
  andRight {A B Γ Δ}   : Γ ⟹[𝓒] A ∷ Δ → Γ ⟹[𝓒] B ∷ Δ → Γ ⟹[𝓒] A ⋏ B ∷ Δ
  orLeft {A B Γ Δ}     : A ∷ Γ ⟹[𝓒] Δ → B ∷ Γ ⟹[𝓒] Δ → A ⋎ B ∷ Γ ⟹[𝓒] Δ
  orRight {A B Γ Δ}    : Γ ⟹[𝓒] A ∷ B ∷ Δ → Γ ⟹[𝓒] A ⋎ B ∷ Δ
  implyLeft {A B Γ Δ}  : Γ ⟹[𝓒] A ∷ Δ → B ∷ Γ ⟹[𝓒] Δ → (A ⟶ B) ∷ Γ ⟹[𝓒] Δ
  implyRight {A B Γ Δ} : A ∷ Γ ⟹[𝓒] B ∷ Δ → Γ ⟹[𝓒] (A ⟶ B) ∷ Δ

variable {𝓒 : C}

section

variable [Weakening 𝓒]

def ofSingleton {Γ A} (d : Γ ⟹[𝓒]. A) : Γ ⟹[𝓒] A ∷ ∅ := wkR (Precollection.subset_iff.mpr <| by simp) d

def ofCons {Γ A} (d : Γ ⟹[𝓒] A ∷ ∅) : Γ ⟹[𝓒]. A := wkR (Precollection.subset_iff.mpr <| by simp) d

end

section LK

variable (𝓒) [LK 𝓒]

instance : LJ 𝓒 where
  verum (Γ) := ofCons (LK.verum Γ ∅)
  falsum := wkL (by simp) (LK.falsum ∅ ∅)
  negLeft {Γ A} (d) := LK.negLeft (ofSingleton d)
  negRight {Γ A} (d) := ofCons <| LK.negRight d
  andLeft₁ {Γ A B C} (d) := ofCons <| LK.andLeft <| wkL (Precollection.subset_iff.mpr <| by aesop) (ofSingleton d)
  andLeft₂ {Γ A B C} (d) := ofCons <| LK.andLeft <| wkL (Precollection.subset_iff.mpr <| by aesop) (ofSingleton d)
  andRight {Γ A B} (dA dB) := ofCons <| LK.andRight (ofSingleton dA) (ofSingleton dB)
  orLeft {Γ A B C} (dA dB) := ofCons <| LK.orLeft (ofSingleton dA) (ofSingleton dB)
  orRight₁ {Γ A B} (d) := ofCons <| LK.orRight <| wkR (Precollection.subset_iff.mpr <| by aesop) (ofSingleton d)
  orRight₂ {Γ A B} (d) := ofCons <| LK.orRight <| wkR (Precollection.subset_iff.mpr <| by aesop) (ofSingleton d)
  implyLeft {Γ A B C} (dA dB) := ofCons <| LK.implyLeft
    (wkR (Precollection.subset_iff.mpr <| by aesop) (ofSingleton dA))
    (ofSingleton dB)
  implyRight {Γ A B} (d) := ofCons <| LK.implyRight <| ofSingleton d

end LK

end TwosidedCalc
