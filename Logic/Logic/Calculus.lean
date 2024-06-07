import Logic.Logic.System

/-!
# Sequent calculus and variants

This file defines a characterization of Tait style calculus and Gentzen style calculus.

## Main Definitions
* `LO.Tait`
* `LO.Gentzen`

-/

namespace LO

class OneSided (F : Type u) where
  Derivation : List F → Type u

class TwoSided (F : Type u) where
  Derivation : List F → List F → Type u

prefix: 45 " ⊢¹ " => OneSided.Derivation

infix: 45 " ⊢² " => TwoSided.Derivation

abbrev OneSided.Derivable [OneSided F] (Δ : List F) : Prop := Nonempty (⊢¹ Δ)

abbrev TwoSided.Derivable [TwoSided F] (Γ Δ : List F) : Prop := Nonempty (Γ ⊢² Δ)

prefix: 45 " ⊢¹! " => OneSided.Derivable

infix: 45 " ⊢²! " => TwoSided.Derivable

class Tait (F : Type u) [LogicalConnective F] extends OneSided F where
  verum (Δ : List F)         : ⊢¹ ⊤ :: Δ
  and {p q : F} {Δ : List F} : ⊢¹ p :: Δ → ⊢¹ q :: Δ → ⊢¹ p ⋏ q :: Δ
  or {p q : F} {Δ : List F}  : ⊢¹ p :: q :: Δ → ⊢¹ p ⋎ q :: Δ
  wk {Δ Δ' : List F}         : ⊢¹ Δ → Δ ⊆ Δ' → ⊢¹ Δ'
  em {p} {Δ : List F}        : p ∈ Δ → ~p ∈ Δ → ⊢¹ Δ

class Tait.Cut (F : Type u) [LogicalConnective F] [Tait F] where
  cut {Δ : List F} {p} : ⊢¹ p :: Δ → ⊢¹ ~p :: Δ → ⊢¹ Δ

class Gentzen (F : Type u) [LogicalConnective F] extends TwoSided F where
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
  closed (p) {Γ Δ : List F}               : p ∈ Γ → p ∈ Δ → Γ ⊢² Δ

class Gentzen.Cut (F : Type u) [LogicalConnective F] [Gentzen F] where
  cut {Γ Δ : List F} {p} : Γ ⊢² p :: Δ → p :: Γ ⊢² Δ → Γ ⊢² Δ

class LawfulTwoSided (S : Type*) {F : Type*} [LogicalConnective F] [System F S] [TwoSided F] where
  toProof₁ {Γ} {𝓢 : S} {p : F} : Γ ⊢² [p] → (∀ q ∈ Γ, 𝓢 ⊢ q) → 𝓢 ⊢ p

variable {F : Type*} [LogicalConnective F]

namespace LawfulTwoSided

variable [System F S] [TwoSided F] [LawfulTwoSided S]

def toProofOfNil {p : F} (b : [] ⊢² [p]) (𝓢 : S) : 𝓢 ⊢ p :=
  toProof₁ b (by intro q h; exact False.elim ((List.mem_nil_iff q).mp h))

lemma toProof₁! {Γ} {𝓢 : S} {p : F} (b : Γ ⊢² [p]) (H : ∀ q ∈ Γ, 𝓢 ⊢! q) : 𝓢 ⊢! p :=
  ⟨toProof₁ b (fun q hq => (H q hq).get)⟩

end LawfulTwoSided

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
  closed := fun p _ _ hΓ hΔ => em (p := p)
    (List.mem_append.mpr $ .inr $ hΔ)
    (List.mem_append.mpr $ .inl $ List.mem_map_of_mem (~·) hΓ)

variable [Tait.Cut F]

instance : Gentzen.Cut F := ⟨fun d d' => Cut.cut (ofConsRight d) (ofConsLeft d')⟩

def equiv : Γ ⊢² Δ ≃ ⊢¹ Γ.map (~·) ++ Δ := Equiv.refl _

def tauto (b : ⊢¹ Δ) : Γ ⊢² Δ := wk b (by simp)

end Tait

namespace Gentzen

variable [Gentzen F] [Gentzen.Cut F] {Γ Δ E : List F}

def wkLeft {Γ Γ' Δ : List F} (d : Γ ⊢² Δ) (ss : Γ ⊆ Γ') : Γ' ⊢² Δ := wk d ss (by simp)

def wkRight {Γ Δ Δ' : List F} (d : Γ ⊢² Δ) (ss : Δ ⊆ Δ') : Γ ⊢² Δ' := wk d (by simp) ss

def rotateLeft {Γ Δ : List F} {p} (d : Γ ++ [p] ⊢² Δ) : p :: Γ ⊢² Δ := Gentzen.wkLeft d (by simp)

def rotateRight {Γ Δ : List F} {p} (d : Γ ⊢² Δ ++ [p]) : Γ ⊢² p :: Δ := Gentzen.wkRight d (by simp)

def wkL {Γ' Δ : List F} (Γ) (ss : Γ ⊆ Γ') (d : Γ ⊢² Δ) : Γ' ⊢² Δ := wk d ss (by simp)

def wkR {Γ Δ' : List F} (Δ) (ss : Δ ⊆ Δ') (d : Γ ⊢² Δ) : Γ ⊢² Δ' := wk d (by simp) ss

def verum' (h : ⊤ ∈ Δ) : Γ ⊢² Δ := wkRight (verum Γ Δ) (by simp[h])

def Cut.cut' {Γ₁ Γ₂ Δ₁ Δ₂ : List F} (d₁ : Γ₁ ⊢² p :: Δ₁) (d₂ : p :: Γ₂ ⊢² Δ₂) : Γ₁ ++ Γ₂ ⊢² Δ₁ ++ Δ₂ :=
  let d₁ : Γ₁ ++ Γ₂ ⊢² p :: (Δ₁ ++ Δ₂) := wk d₁ (by simp) (List.cons_subset_cons _ $ by simp)
  let d₂ : p :: (Γ₁ ++ Γ₂) ⊢² Δ₁ ++ Δ₂ := wk d₂ (List.cons_subset_cons _ $ by simp) (by simp)
  Cut.cut d₁ d₂

def ofNegLeft {p} (b : ~p :: Γ ⊢² Δ) : Γ ⊢² p :: Δ :=
  let d : p :: Γ ⊢² p :: Δ :=
    Gentzen.wk (show [p] ⊢² [p] from closed _ (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl))
      (by simp) (by simp)
  Cut.cut (negRight d) (wkRight b (by simp))

def ofNegRight {p} (b : Γ ⊢² ~p :: Δ) : p :: Γ ⊢² Δ :=
  let d : p :: Γ ⊢² p :: Δ :=
    Gentzen.wk (show [p] ⊢² [p] from closed _ (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl))
      (by simp) (by simp)
  Cut.cut (wkLeft b (by simp)) (negLeft d)

def ofImplyRight {p q} (b : Γ ⊢² (p ⟶ q) :: Δ) : p :: Γ ⊢² q :: Δ :=
  let d : (p ⟶ q) :: p :: Γ ⊢² q :: Δ :=
    implyLeft (closed p (by simp) (by simp)) (closed q (by simp) (by simp))
  wk (Cut.cut' b d) (by simp) (by simp)

def modusPonens {p q} (b₁ : Γ ⊢² (p ⟶ q) :: Δ) (b₂ : Γ ⊢² p :: Δ) : Γ ⊢² q :: Δ :=
  wk (Cut.cut' b₂ (ofImplyRight b₁)) (by simp) (by simp)

variable {S : Type*} [Collection F S]

structure Disjconseq (𝓣 : S) (Γ : List F) where
  antecedent : List F
  subset : ∀ p ∈ antecedent, p ∈ 𝓣
  derivation : antecedent ⊢² Γ

infix: 45 " ⊢' " => Disjconseq

def DisjconseqEquivDerivation {𝓣 : S} :
    𝓣 ⊢' Γ ≃ (Δ : {Δ : List F // ∀ π ∈ Δ, π ∈ 𝓣}) × Δ ⊢² Γ where
  toFun := fun b => ⟨⟨b.antecedent, b.subset⟩, b.derivation⟩
  invFun := fun p => ⟨p.1, p.1.prop, p.2⟩
  left_inv := fun b => by simp
  right_inv := fun b => by simp

def Disjconseq.weakening {𝓣 U : S} {Γ : List F} (b : 𝓣 ⊢' Γ) (h : 𝓣 ⊆ U) : U ⊢' Γ where
  antecedent := b.antecedent
  subset := fun p hp => Collection.subset_iff.mp h _ (b.subset p hp)
  derivation := b.derivation

def toDisjconseq {𝓣 : S} {Γ Δ} (d : Γ ⊢² Δ) (ss : ∀ p ∈ Γ, p ∈ 𝓣) : 𝓣 ⊢' Δ where
  antecedent := Γ
  subset := ss
  derivation := d

namespace Disjconseq

variable {𝓣 : S}

def wk' {S S'} [Collection F S] [Collection F S'] {𝓣 : S} {𝓣' : S'}
    (H : Collection.set 𝓣 ⊆ Collection.set 𝓣') {Γ} : 𝓣 ⊢' Γ → 𝓣' ⊢' Γ := fun d ↦
  ⟨d.antecedent, fun p hp ↦ H (d.subset p hp), d.derivation⟩

def tauto {Δ} (d : [] ⊢² Δ) : 𝓣 ⊢' Δ := toDisjconseq d (by simp)

def wk (b : 𝓣 ⊢' Γ) (ss : Γ ⊆ Γ') : 𝓣 ⊢' Γ' where
  antecedent := b.antecedent
  subset := b.subset
  derivation := wkRight b.derivation ss

def cut (b : 𝓣 ⊢' p :: Γ) (b' : 𝓣 ⊢' ~p :: Γ) : 𝓣 ⊢' Γ where
  antecedent := b.antecedent ++ b'.antecedent
  subset := by
    simp
    rintro p (hp | hp)
    · exact b.subset _ hp
    · exact b'.subset _ hp
  derivation :=
    let d : b.antecedent ++ b'.antecedent ⊢² p :: Γ := wkLeft b.derivation (by simp)
    let d' : b.antecedent ++ b'.antecedent ⊢² ~p :: Γ := wkLeft b'.derivation (by simp)
    Cut.cut d' (negLeft d)

def cut' (b : 𝓣 ⊢' p :: Γ) (b' : 𝓣 ⊢' ~p :: Δ) : 𝓣 ⊢' Γ ++ Δ where
  antecedent := b.antecedent ++ b'.antecedent
  subset := by
    simp
    rintro p (hp | hp)
    · exact b.subset _ hp
    · exact b'.subset _ hp
  derivation := by
    let d : b.antecedent ++ b'.antecedent ⊢² p :: Γ := wkLeft b.derivation (by simp)
    let d' : b.antecedent ++ b'.antecedent ⊢² ~p :: Δ := wkLeft b'.derivation (by simp)
    exact Gentzen.wk (Cut.cut' d' (negLeft d)) (by simp) (by simp)

def verum (Γ : List F) : 𝓣 ⊢' ⊤ :: Γ := ⟨[], by simp, Gentzen.verum _ _⟩

def verum' (h : ⊤ ∈ Γ) : 𝓣 ⊢' Γ := wk (verum Γ) (by simp[h])

def and (bp : 𝓣 ⊢' p :: Δ) (bq : 𝓣 ⊢' q :: Δ) : 𝓣 ⊢' p ⋏ q :: Δ where
  antecedent := bp.antecedent ++ bq.antecedent
  subset := by
    simp
    rintro p (hp | hp)
    · exact bp.subset _ hp
    · exact bq.subset _ hp
  derivation := Gentzen.andRight
      (Gentzen.wkLeft bp.derivation (List.subset_append_left _ _))
      (Gentzen.wkLeft bq.derivation (List.subset_append_right _ _))

def or (b : 𝓣 ⊢' p :: q :: Δ) : 𝓣 ⊢' p ⋎ q :: Δ where
  antecedent := b.antecedent
  subset := b.subset
  derivation := Gentzen.orRight b.derivation

def deduction [DecidableEq F] {p} (b : cons p 𝓣 ⊢' Δ) : 𝓣 ⊢' ~p :: Δ where
  antecedent := b.antecedent.filter (· ≠ p)
  subset := by
    simp[List.mem_filter]
    intro q hq ne
    simpa[ne] using b.subset q hq
  derivation := negRight (wkLeft b.derivation $ by
    intro q hq
    by_cases e : q = p <;> simp[List.mem_filter, hq, e])

def deductionNeg [DecidableEq F] {p} (b : cons (~p) 𝓣 ⊢' Δ) : 𝓣 ⊢' p :: Δ where
  antecedent := b.antecedent.filter (· ≠ ~p)
  subset := by
    simp[List.mem_filter]
    intro q hq ne
    simpa[ne] using b.subset q hq
  derivation := ofNegLeft (wkLeft b.derivation $ by
    intro q hq
    by_cases e : q = ~p <;> simp[List.mem_filter, hq, e])

end Disjconseq

variable (F S)

instance : System F S := ⟨(· ⊢' [·])⟩

variable {F S}

instance : System.Axiomatized S where
  prfAxm := fun {𝓣 f} hf ↦
    ⟨[f], by simpa, closed _ (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl)⟩
  weakening := fun ss b => b.weakening ss

def toProof {𝓣 : S} : {Γ Δ : List F} → Γ ⊢² Δ → (∀ q ∈ Γ, 𝓣 ⊢ q) → 𝓣 ⊢' Δ
  | [],     _, d, _ => toDisjconseq d (by simp)
  | q :: Γ, Δ, d, h =>
    let bn : 𝓣 ⊢' ~q :: Δ := toProof (negRight d) (fun q hq => h q (by simp[hq]))
    let b : 𝓣 ⊢' [q] := h q (by simp)
    b.cut' bn

instance : LawfulTwoSided S := ⟨toProof⟩

def of {p : F} (b : [] ⊢² [p]) {𝓣 : S} : 𝓣 ⊢ p := ⟨[], by simp, b⟩

instance strongCut (S T) [Collection F S] [Collection F T] :
    System.StrongCut S T := ⟨fun dU dp ↦ toProof dp.derivation (fun q hq => dU <| dp.subset q hq)⟩

def proofEquivDerivation {𝓣 : S} {p : F} :
    𝓣 ⊢ p ≃ (Δ : {Δ : List F // ∀ π ∈ Δ, π ∈ 𝓣}) × Δ ⊢² [p] :=
  DisjconseqEquivDerivation

lemma provable_iff {𝓣 : S} {p : F} :
    𝓣 ⊢! p ↔ ∃ Δ : List F, (∀ π ∈ Δ, π ∈ 𝓣) ∧ Δ ⊢²! [p] :=
  ⟨by rintro ⟨b⟩; rcases proofEquivDerivation b with ⟨Δ, d⟩; exact ⟨Δ, Δ.prop, ⟨d⟩⟩,
   by rintro ⟨Δ, h, ⟨d⟩⟩; exact ⟨proofEquivDerivation.symm ⟨⟨Δ, h⟩, d⟩⟩⟩

instance deductiveExplosion : System.DeductiveExplosion S := ⟨fun {𝓢} b p ↦
  let t : 𝓢 ⊢ ~⊥ := ⟨[], by simp, Gentzen.negRight (Gentzen.falsum _ _)⟩
  let b : 𝓢 ⊢' [] := Disjconseq.cut' b t
  Disjconseq.wk b (by simp)⟩

instance compact : System.Compact S where
  φ := fun b ↦ b.antecedent.toCollection
  φPrf := fun b ↦ ⟨b.antecedent, by intro p; simp, b.derivation⟩
  φ_subset := by intro 𝓣 p b; simpa [Collection.subset_iff] using b.subset
  φ_finite := by intro 𝓣 p b; simp

variable {𝓣 : S}

lemma consistent_iff_isEmpty :
    System.Consistent 𝓣 ↔ IsEmpty (𝓣 ⊢' []) :=
  ⟨by contrapose
      simp [System.Consistent, System.not_consistent_iff_inconsistent, System.inconsistent_iff_provable_bot]
      intro b; exact ⟨b.wk (by simp)⟩,
   by contrapose
      simp [System.Consistent, System.not_consistent_iff_inconsistent, System.inconsistent_iff_provable_bot]
      rintro ⟨Δ, h, d⟩
      have : Δ ⊢² [] := Cut.cut d (falsum _ _)
      exact ⟨toDisjconseq this h⟩⟩

lemma inconsistent_iff_nonempty :
    System.Inconsistent 𝓣 ↔ Nonempty (𝓣 ⊢' []) := by
  simp [←System.not_consistent_iff_inconsistent, consistent_iff_isEmpty]

lemma provable_iff_inconsistent {p} :
    𝓣 ⊢! p ↔ System.Inconsistent (cons (~p) 𝓣) :=
  ⟨by rintro ⟨⟨Δ, h, d⟩⟩
      simp [inconsistent_iff_nonempty]
      exact ⟨⟨~p :: Δ, by simp; intro q hq; right; exact h q hq, negLeft d⟩⟩,
   by letI := Classical.typeDecidableEq F
      simp [inconsistent_iff_nonempty]
      exact fun b ↦ ⟨b.deductionNeg⟩⟩

lemma refutable_iff_inconsistent {p} :
    𝓣 ⊢! ~p ↔ System.Inconsistent (cons p 𝓣) :=
  ⟨by rintro ⟨⟨Δ, h, d⟩⟩
      simp [inconsistent_iff_nonempty]
      exact ⟨⟨p :: Δ, by simp; intro q hq; right; exact h q hq, ofNegRight d⟩⟩,
   by letI := Classical.typeDecidableEq F
      simp [inconsistent_iff_nonempty]
      exact fun b ↦ ⟨b.deduction⟩⟩

lemma consistent_insert_iff_not_refutable {p}  :
    System.Consistent (cons p 𝓣) ↔ 𝓣 ⊬! ~p := by
  simp [System.Unprovable, refutable_iff_inconsistent, System.not_inconsistent_iff_consistent]

lemma inconsistent_of_provable_and_refutable {p}
    (bp : 𝓣 ⊢ p) (br : 𝓣 ⊢ ~p) : System.Inconsistent 𝓣 :=
  System.not_consistent_iff_inconsistent.mp <| fun A => by
    have : 𝓣 ⊢' [] := Disjconseq.cut bp br
    exact (consistent_iff_isEmpty.mp A).false this

lemma inconsistent_of_provable_and_refutable! {p}
    (bp : 𝓣 ⊢! p) (br : 𝓣 ⊢! ~p) : System.Inconsistent 𝓣 := by
  rcases bp with ⟨bp⟩; rcases br with ⟨br⟩
  exact inconsistent_of_provable_and_refutable bp br

section

variable {S S' : Type*} [Collection F S] [Collection F S']

def wk' {𝓣 : S} {𝓣' : S'} (H : Collection.set 𝓣 ⊆ Collection.set 𝓣') {p} : 𝓣 ⊢ p → 𝓣' ⊢ p := Disjconseq.wk' H

def wk'! {𝓣 : S} {𝓣' : S'} (H : Collection.set 𝓣 ⊆ Collection.set 𝓣') {p} : 𝓣 ⊢! p → 𝓣' ⊢! p := by
  rintro ⟨b⟩; exact ⟨wk' H b⟩

def le_of_subset {𝓣 : S} {𝓣' : S'} (H : Collection.set 𝓣 ⊆ Collection.set 𝓣') : 𝓣 ≤ₛ 𝓣' := fun _ ↦ wk'! H

end

@[simp] lemma consistent_theory_iff_consistent :
    System.Consistent (System.theory 𝓣) ↔ System.Consistent 𝓣 :=
  ⟨fun h ↦ h.of_le (le_of_subset <| by simp [Set.subset_def]; intro p hp; exact System.Axiomatized.provable_axm  𝓣 hp),
   fun consis ↦ System.consistent_iff_unprovable_bot.mpr <| by
      rintro h
      have : System.Inconsistent 𝓣 := System.inconsistent_iff_provable_bot.mpr <| System.StrongCut.cut! (by simp) h
      exact System.not_inconsistent_iff_consistent.mpr consis this⟩

end Gentzen

end LO
