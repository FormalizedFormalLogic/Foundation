import Logic.Logic.System
import Logic.Logic.HilbertStyle

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

class LawfulTwoSided (S : Type*) {F : Type*} [LogicalConnective F] [System S F] [TwoSided F] where
  toProof₁ {Γ} {𝓢 : S} {p : F} : Γ ⊢² [p] → (∀ q ∈ Γ, 𝓢 ⊢ q) → 𝓢 ⊢ p

variable {F : Type*} [LogicalConnective F]

namespace LawfulTwoSided

variable [System S F] [TwoSided F] [LawfulTwoSided S]

def toProofOfNil {p : F} (b : [] ⊢² [p]) (𝓢 : S) : 𝓢 ⊢ p :=
  toProof₁ b (by intro q h; exact False.elim ((List.mem_nil_iff q).mp h))

lemma toProof₁! {Γ} {𝓢 : S} {p : F} (b : Γ ⊢² [p]) (H : ∀ q ∈ Γ, 𝓢 ⊢! q) : 𝓢 ⊢! p :=
  ⟨toProof₁ b (fun q hq => (H q hq).prf)⟩

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

structure Disjconseq (T : Set F) (Γ : List F) where
  antecedent : List F
  subset : ∀ p ∈ antecedent, p ∈ T
  derivation : antecedent ⊢² Γ

infix: 45 " ⊢' " => Disjconseq

def DisjconseqEquivDerivation {T : Set F} :
    T ⊢' Γ ≃ (Δ : {Δ : List F // ∀ π ∈ Δ, π ∈ T}) × Δ ⊢² Γ where
  toFun := fun b => ⟨⟨b.antecedent, b.subset⟩, b.derivation⟩
  invFun := fun p => ⟨p.1, p.1.prop, p.2⟩
  left_inv := fun b => by simp
  right_inv := fun b => by simp

def Disjconseq.weakening {T U : Set F} {Γ : List F} (b : T ⊢' Γ) (h : T ⊆ U) : U ⊢' Γ where
  antecedent := b.antecedent
  subset := fun p hp => h (b.subset p hp)
  derivation := b.derivation

def toDisjconseq {T : Set F} {Γ Δ} (d : Γ ⊢² Δ) (ss : ∀ p ∈ Γ, p ∈ T) : T ⊢' Δ where
  antecedent := Γ
  subset := ss
  derivation := d

namespace Disjconseq

variable {T : Set F}

def tauto {Δ} (d : [] ⊢² Δ) : T ⊢' Δ := toDisjconseq d (by simp)

def wk (b : T ⊢' Γ) (ss : Γ ⊆ Γ') : T ⊢' Γ' where
  antecedent := b.antecedent
  subset := b.subset
  derivation := wkRight b.derivation ss

def cut (b : T ⊢' p :: Γ) (b' : T ⊢' ~p :: Γ) : T ⊢' Γ where
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

def cut' (b : T ⊢' p :: Γ) (b' : T ⊢' ~p :: Δ) : T ⊢' Γ ++ Δ where
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

def verum (Γ : List F) : T ⊢' ⊤ :: Γ := ⟨[], by simp, Gentzen.verum _ _⟩

def verum' (h : ⊤ ∈ Γ) : T ⊢' Γ := wk (verum Γ) (by simp[h])

def and (bp : T ⊢' p :: Δ) (bq : T ⊢' q :: Δ) : T ⊢' p ⋏ q :: Δ where
  antecedent := bp.antecedent ++ bq.antecedent
  subset := by
    simp
    rintro p (hp | hp)
    · exact bp.subset _ hp
    · exact bq.subset _ hp
  derivation := Gentzen.andRight
      (Gentzen.wkLeft bp.derivation (List.subset_append_left _ _))
      (Gentzen.wkLeft bq.derivation (List.subset_append_right _ _))

def or (b : T ⊢' p :: q :: Δ) : T ⊢' p ⋎ q :: Δ where
  antecedent := b.antecedent
  subset := b.subset
  derivation := Gentzen.orRight b.derivation

def deduction [DecidableEq F] {p} (b : insert p T ⊢' Δ) : T ⊢' ~p :: Δ where
  antecedent := b.antecedent.filter (· ≠ p)
  subset := by
    simp[List.mem_filter]
    intro q hq ne
    simpa[ne] using b.subset q hq
  derivation := negRight (wkLeft b.derivation $ by
    intro q hq
    by_cases e : q = p <;> simp[List.mem_filter, hq, e])

def deductionNeg [DecidableEq F] {p} (b : insert (~p) T ⊢' Δ) : T ⊢' p :: Δ where
  antecedent := b.antecedent.filter (· ≠ ~p)
  subset := by
    simp[List.mem_filter]
    intro q hq ne
    simpa[ne] using b.subset q hq
  derivation := ofNegLeft (wkLeft b.derivation $ by
    intro q hq
    by_cases e : q = ~p <;> simp[List.mem_filter, hq, e])

end Disjconseq

instance : System (Theory F) F := ⟨(· ⊢' [·])⟩

instance : System.Axiomatized (Theory F) where
  axm := Theory.set
  prfAxm := fun T f hf ↦
    ⟨[f], by simpa, closed _ (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl)⟩
  weakening := fun ss b => b.weakening ss

@[simp] lemma axm_eq (T : Theory F) : System.Axiomatized.axm T = T.set := rfl

def toProof {T : Theory F} : {Γ Δ : List F} → Γ ⊢² Δ → (∀ q ∈ Γ, T ⊢ q) → System.Axiomatized.axm T ⊢' Δ
  | [],     _, d, _ => toDisjconseq d (by simp)
  | q :: Γ, Δ, d, h =>
    let bn : T ⊢' ~q :: Δ := toProof (negRight d) (fun q hq => h q (by simp[hq]))
    let b : T ⊢' [q] := h q (by simp)
    b.cut' bn

instance : LawfulTwoSided (Theory F) := ⟨toProof⟩

instance : System.StrongCut (Theory F) := ⟨fun dU dp ↦ toProof dp.derivation (fun q hq => dU <| dp.subset q hq)⟩

def proofEquivDerivation {T : Theory F} {p : F} :
    T ⊢ p ≃ (Δ : {Δ : List F // ∀ π ∈ Δ, π ∈ T}) × Δ ⊢² [p] :=
  DisjconseqEquivDerivation

lemma provable_iff {T : Theory F} {p : F} :
    T ⊢! p ↔ ∃ Δ : List F, (∀ π ∈ Δ, π ∈ T) ∧ Δ ⊢²! [p] :=
  ⟨by rintro ⟨b⟩; rcases proofEquivDerivation b with ⟨Δ, d⟩; exact ⟨Δ, Δ.prop, ⟨d⟩⟩,
   by rintro ⟨Δ, h, ⟨d⟩⟩; exact ⟨proofEquivDerivation.symm ⟨⟨Δ, h⟩, d⟩⟩⟩

instance (T : Theory F) : System.ModusPonens T := ⟨
  fun {p q} ↦ by
    rintro ⟨Γ₁, h₁, d₁⟩ ⟨Γ₂, h₂, d₂⟩
    let d₃ : Γ₁ ++ Γ₂ ⊢² [q] := modusPonens (wkLeft d₁ (by simp)) (wkLeft d₂ (by simp))
    exact ⟨Γ₁ ++ Γ₂, by simp; rintro p (hp | hp); { exact h₁ p hp }; { exact h₂ p hp }, d₃⟩⟩

instance (T : Theory F) : System.EFQ T := ⟨fun p ↦ ⟨[], by simp, implyRight (falsum _ _)⟩⟩

instance : System.DeductiveExplosion (Theory F) := ⟨fun b p ↦ System.EFQ.efq p ⨀ b⟩

instance : System.Compact (Theory F) where
  φ := fun b ↦ {p | p ∈ b.antecedent}
  φPrf := fun b ↦ ⟨b.antecedent, by intro p; simp, b.derivation⟩
  φ_subset := by intro T p b q; simp; exact b.subset q
  φ_finite := by intro T p b; simp [System.Finite]

variable {T : Theory F}

lemma consistent_iff_isEmpty :
    System.Consistent T ↔ IsEmpty (T.set ⊢' []) :=
  ⟨by contrapose
      simp [System.Consistent, System.not_consistent_iff_inconsistent, System.inconsistent_iff_provable_bot]
      intro b; exact ⟨b.wk (by simp)⟩,
   by contrapose
      simp [System.Consistent, System.not_consistent_iff_inconsistent, System.inconsistent_iff_provable_bot]
      rintro ⟨Δ, h, d⟩
      have : Δ ⊢² [] := Cut.cut d (falsum _ _)
      exact ⟨toDisjconseq this h⟩⟩

lemma inconsistent_iff_nonempty :
    System.Inconsistent T ↔ Nonempty (T.set ⊢' []) := by
  simp [←System.not_consistent_iff_inconsistent, consistent_iff_isEmpty]

lemma provable_iff_inconsistent {p} :
    T ⊢! p ↔ System.Inconsistent (insert (~p) T) :=
  ⟨by rintro ⟨⟨Δ, h, d⟩⟩
      simp [inconsistent_iff_nonempty]
      exact ⟨⟨~p :: Δ, by simp; intro q hq; right; exact h q hq, negLeft d⟩⟩,
   by letI := Classical.typeDecidableEq F
      simp [inconsistent_iff_nonempty]
      exact fun b ↦ ⟨b.deductionNeg⟩⟩

lemma refutable_iff_inconsistent {p} :
    T ⊢! ~p ↔ System.Inconsistent (insert p T) :=
  ⟨by rintro ⟨⟨Δ, h, d⟩⟩
      simp [inconsistent_iff_nonempty]
      exact ⟨⟨p :: Δ, by simp; intro q hq; right; exact h q hq, ofNegRight d⟩⟩,
   by letI := Classical.typeDecidableEq F
      simp [inconsistent_iff_nonempty]
      exact fun b ↦ ⟨b.deduction⟩⟩

lemma consistent_insert_iff_not_refutable {p}  :
    System.Consistent (insert p T) ↔ T ⊬! ~p := by
  simp [System.Unprovable, refutable_iff_inconsistent, System.not_inconsistent_iff_consistent]

lemma inconsistent_of_provable_and_refutable {p}
    (bp : T ⊢ p) (br : T ⊢ ~p) : System.Inconsistent T :=
  System.not_consistent_iff_inconsistent.mp <| fun A => by
    have : T.set ⊢' [] := Disjconseq.cut bp br
    exact (consistent_iff_isEmpty.mp A).false this

lemma inconsistent_of_provable_and_refutable! {p}
    (bp : T ⊢! p) (br : T ⊢! ~p) : System.Inconsistent T := by
  rcases bp with ⟨bp⟩; rcases br with ⟨br⟩
  exact inconsistent_of_provable_and_refutable bp br

@[simp] lemma consistent_theory_iff_consistent :
    System.Consistent (System.theory T).theory ↔ System.Consistent T :=
  ⟨fun h ↦ h.of_subset (System.Axiomatized.provable_axm _),
   fun consis ↦ System.consistent_iff_unprovable_bot.mpr <| by
      rintro h
      have : System.Inconsistent T := System.inconsistent_iff_provable_bot.mpr <| System.StrongCut.cut! (by simp) h
      exact System.not_inconsistent_iff_consistent.mpr consis this⟩

end Gentzen

end LO
