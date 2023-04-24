import Logic.Predicate.FirstOrder.Calculus

universe u v

namespace FirstOrder

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

variable (T : Theory L) {μ : Type v}

open SubFormula

def SequentList.fvarList (l : List $ SubFormula L μ n) : List μ :=
  l.bind SubFormula.fvarList

def fleshVar (C : List $ SyntacticFormula L) : ℕ := (SequentList.fvarList C).sup

structure ProofArrow (T : Theory L) (P : List (SyntacticFormula L)) (p : SyntacticFormula L) where
  leftHand : List (Sentence L)
  hleftHand : ∀ σ ∈ leftHand, σ ∈ T
  derivation : DerivationList (p :: ((leftHand.map emb ++ P).map (~·)))

namespace ProofArrow
open DerivationCutRestricted
variable {Δ Γ : List (SyntacticFormula L)}

def byAxiom {σ} (h : σ ∈ T) : ProofArrow T Δ (emb σ) where
  leftHand := [σ]
  hleftHand := by simp[h]
  derivation := em (p := emb σ) (by simp) (by simp)

def trans {p q} (b₁ : ProofArrow T Δ p) (b₂ : ProofArrow T (p :: Δ) q) : ProofArrow T Δ q where
  leftHand := b₁.leftHand ++ b₂.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ); exact b₁.hleftHand _ hσ; exact b₂.hleftHand _ hσ
  derivation :=
    (cutCut (p := p)
      (Δ := ((b₁.leftHand.map emb ++ Δ).map (~·)).toFinset)
      (Γ := insert q ((b₂.leftHand.map emb ++ Δ).map (~·)).toFinset)
      (b₁.derivation.cast (by simp))
      (b₂.derivation.cast (by simp[Finset.Insert.comm]))).cast
        (by simp[Finset.union_self, Finset.union_comm (Δ.map (~·)).toFinset])

def assumption {p} (h : p ∈ Δ) : ProofArrow T Δ p where
  leftHand := []
  hleftHand := by simp
  derivation := em (p := p) (by simp) (by simp[h]; exact Or.inr ⟨p, h, rfl⟩)

def weakening (h : Δ ⊆ Γ) {p} (b : ProofArrow T Δ p) : ProofArrow T Γ p where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation := b.derivation.weakening
    (by simp; exact Finset.insert_subset_insert _ $
      Finset.union_subset_union (by rfl) (by simp[Finset.subset_iff]; intro q hq; exact ⟨q, h hq, rfl⟩))

def contradiction (p) {q} (b₁ : ProofArrow T Δ p) (b₂ : ProofArrow T Δ (~p)) : ProofArrow T Δ q where
  leftHand := b₁.leftHand ++ b₂.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ); exact b₁.hleftHand _ hσ; exact b₂.hleftHand _ hσ
  derivation :=
    let Γ := (((b₁.leftHand ++ b₂.leftHand).map emb ++ Δ).map (~·)).toFinset
    have b₁₁ : ⊢ᶜ insert p Γ := b₁.derivation.weakening
      (by simp; exact Finset.insert_subset_insert _ (Finset.union_subset_union (by rfl) (Finset.subset_union_right _ _)))
    have b₂₁ : ⊢ᶜ insert (~p) Γ := b₂.derivation.weakening
      (by simp; exact Finset.insert_subset_insert _ (Finset.subset_union_right _ _))
    (cutCut b₁₁ b₂₁).weakening (by simp[Finset.subset_insert])

def trivial : ProofArrow T Δ ⊤ := ⟨[], by simp, verum _ (by simp)⟩

def explode {p} (b : ProofArrow T Δ ⊥) : ProofArrow T Δ p where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have b₁ : ⊢ᶜ (insert ⊥ $ insert p Γ) := b.derivation.weakening (by simp; exact Finset.insert_subset_insert _ (Finset.subset_insert _ _))
    have b₂ : ⊢ᶜ (insert ⊤ $ insert p Γ) := verum _ (by simp)
    (cutCut b₁ b₂).cast (by simp)

def intro {p q} (b : ProofArrow T (p :: Δ) q) : ProofArrow T Δ (p ⟶ q) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    have : ⊢ᶜ (insert (~p) $ insert q ((b.leftHand.map emb ++ Δ).map (~·)).toFinset) :=
      b.derivation.cast (by simp[Finset.Insert.comm])
    (or _ _ _ this).cast (by simp[SubFormula.imp_eq])

def modusPonens {p q} (b₁ : ProofArrow T Δ (p ⟶ q)) (b₂ : ProofArrow T Δ p) : ProofArrow T Δ q where
  leftHand := b₁.leftHand ++ b₂.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ); exact b₁.hleftHand _ hσ; exact b₂.hleftHand _ hσ
  derivation :=
    let Γ := (((b₁.leftHand ++ b₂.leftHand).map emb ++ Δ).map (~·)).toFinset
    have b₁₁ : ⊢ᶜ insert (~p ⋎ q) Γ := b₁.derivation.weakening
      (by simp[SubFormula.imp_eq]; exact Finset.insert_subset_insert _ (Finset.union_subset_union (by rfl) (Finset.subset_union_right _ _)))
    have b₂₁ : ⊢ᶜ insert p Γ := b₂.derivation.weakening
      (by simp; exact (Finset.insert_subset_insert _ $ by
        rw[←Finset.union_assoc]; exact Finset.union_subset_union (Finset.subset_union_right _ _) (by rfl)))
    have : ⊢ᶜ (insert (p ⋏ ~q) $ insert q Γ) := and _ _ _
      (b₂₁.weakening (by simp[Finset.Insert.comm]; exact Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      (em (p := q) (by simp) (by simp))
    (cutCut (Δ := Γ) (Γ := insert q Γ) b₁₁ (this.cast (by simp))).cast (by simp)

def split {p q} (b₁ : ProofArrow T Δ p) (b₂ : ProofArrow T Δ q) : ProofArrow T Δ (p ⋏ q) where
  leftHand := b₁.leftHand ++ b₂.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ); exact b₁.hleftHand _ hσ; exact b₂.hleftHand _ hσ
  derivation :=
    let Γ := (((b₁.leftHand ++ b₂.leftHand).map emb ++ Δ).map (~·)).toFinset
    have b₁₁ : ⊢ᶜ insert p Γ := b₁.derivation.weakening
      (by simp[SubFormula.imp_eq]; exact Finset.insert_subset_insert _ (Finset.union_subset_union (by rfl) (Finset.subset_union_right _ _)))
    have b₂₁ : ⊢ᶜ insert q Γ := b₂.derivation.weakening
      (by simp; exact (Finset.insert_subset_insert _ $ by
        rw[←Finset.union_assoc]; exact Finset.union_subset_union (Finset.subset_union_right _ _) (by rfl)))
    (and _ _ _ b₁₁ b₂₁).cast (by simp)

def andLeft {p q} (b : ProofArrow T Δ (p ⋏ q)) : ProofArrow T Δ p where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have b₁ : ⊢ᶜ insert (p ⋏ q) Γ := b.derivation.cast (by simp)
    have b₂ : ⊢ᶜ (insert (~p ⋎ ~q) $ insert p Γ) := or _ _ _ (em (p := p) (by simp) (by simp))
    (cutCut (Δ := Γ) (Γ := insert p Γ) b₁ (b₂.cast (by simp))).cast (by simp)

def andRight {p q} (b : ProofArrow T Δ (p ⋏ q)) : ProofArrow T Δ q where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have b₁ : ⊢ᶜ insert (p ⋏ q) Γ := b.derivation.cast (by simp)
    have b₂ : ⊢ᶜ (insert (~p ⋎ ~q) $ insert q Γ) := or _ _ _ (em (p := q) (by simp) (by simp))
    (cutCut (Δ := Γ) (Γ := insert q Γ) b₁ (b₂.cast (by simp))).cast (by simp)

def orLeft {p q} (b : ProofArrow T Δ p) : ProofArrow T Δ (p ⋎ q) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have : ⊢ᶜ (insert p $ insert q Γ) := b.derivation.weakening (by simp[Finset.Insert.comm p, Finset.subset_insert])
    (or _ _ _ this).cast (by simp)

def orRight {p q} (b : ProofArrow T Δ q) : ProofArrow T Δ (p ⋎ q) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have : ⊢ᶜ (insert p $ insert q Γ) := b.derivation.weakening (by simp[Finset.subset_insert])
    (or _ _ _ this).cast (by simp)

def cases {p q r} (b₀ : ProofArrow T Δ (p ⋎ q)) (b₁ : ProofArrow T (p :: Δ) r) (b₂ : ProofArrow T (q :: Δ) r) : ProofArrow T Δ r where
  leftHand := b₀.leftHand ++ b₁.leftHand ++ b₂.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ | hσ); exact b₀.hleftHand _ hσ; exact b₁.hleftHand _ hσ; exact b₂.hleftHand _ hσ
  derivation :=
    let Γ := (((b₀.leftHand ++ b₁.leftHand ++ b₂.leftHand).map emb ++ Δ).map (~·)).toFinset
    have b₀₁ : ⊢ᶜ insert (p ⋎ q) Γ := b₀.derivation.weakening (by
      simp[SubFormula.imp_eq]; exact Finset.insert_subset_insert _
        (Finset.union_subset_union (by rfl) (by rw[←Finset.union_assoc]; exact Finset.subset_union_right _ _)))
    have b₁₁ : ⊢ᶜ (insert (~p) $ insert r Γ) := b₁.derivation.weakening
      (by simp[Finset.Insert.comm]; exact (Finset.insert_subset_insert _ $ Finset.insert_subset_insert _ $
        Finset.union_subset
          (fun x hx => by simp only [Finset.mem_union]; exact Or.inr $ Or.inl hx)
          (fun x hx => by simp only [Finset.mem_union]; exact Or.inr $ Or.inr $ Or.inr hx)))
    have b₂₁ : ⊢ᶜ (insert (~q) $ insert r Γ) := b₂.derivation.weakening
      (by simp[Finset.Insert.comm]; exact (Finset.insert_subset_insert _ $ Finset.insert_subset_insert _ $
        Finset.union_subset
          (fun x hx => by simp only [Finset.mem_union]; exact Or.inr $ Or.inr $ Or.inl hx)
          (fun x hx => by simp only [Finset.mem_union]; exact Or.inr $ Or.inr $ Or.inr hx)))  
    have b₃ : ⊢ᶜ (insert (~(p ⋎ q)) $ insert r Γ) := and _ _ _ b₁₁ b₂₁
    (cutCut b₀₁ b₃).cast (by simp)

def generalize {p} (b : ProofArrow T (Δ.map shift) (free p)) : ProofArrow T Δ (∀' p) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    (DerivationCutRestricted.all Γ p
      (b.derivation.cast $ by simp[shifts_eq_image, Finset.image_union, ←List.toFinset_map, Function.comp])).cast (by simp)

def specialize (t) {p} (b : ProofArrow T Δ (∀' p)) : ProofArrow T Δ (subst t p) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have : ⊢ᶜ (insert (∃' ~p) $ insert (subst t p) Γ) := ex _ t (~p) (em (p := subst t p) (by simp) (by simp))
    (cutCut (Δ := Γ) (Γ := insert (subst t p) Γ) (p := ∀' p) (b.derivation.cast $ by simp) this).cast (by simp)

def useInstance (t) {p} (b : ProofArrow T Δ (subst t p)) : ProofArrow T Δ (∃' p) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    (ex Γ t p $ b.derivation.cast $ by simp).cast (by simp)

def exCases {p q} (b₀ : ProofArrow T Δ (∃' p)) (b₁ : ProofArrow T (free p :: Δ.map shift) (shift q)) : ProofArrow T Δ q where
  leftHand := b₀.leftHand ++ b₁.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ); exact b₀.hleftHand _ hσ; exact b₁.hleftHand _ hσ
  derivation :=
    let Γ := (((b₀.leftHand ++ b₁.leftHand).map emb ++ Δ).map (~·)).toFinset
    have b₀₁ : ⊢ᶜ insert (∃' p) Γ := b₀.derivation.weakening
      (by simp[SubFormula.imp_eq]; exact Finset.insert_subset_insert _ (Finset.union_subset_union (by rfl) (Finset.subset_union_right _ _)))
    have b₁₁ : ⊢ᶜ (insert (free $ ~p) $ shifts $ insert q Γ) := b₁.derivation.weakening
      (by simp[shifts_insert, Finset.Insert.comm]; exact
        (Finset.insert_subset_insert _ $ Finset.insert_subset_insert _ $ by
          simp[shifts_eq_image, Finset.image_union, ←List.toFinset_map, Function.comp, Finset.subset_union_right]))
    have b₁₂ : ⊢ᶜ (insert (~(∃' p)) $ insert q Γ) :=
      DerivationCutRestricted.all (insert q Γ) (~p) (b₁₁.cast (by simp))
    (cutCut b₀₁ b₁₂).cast (by simp)

end ProofArrow

variable (T : Theory L)

inductive Deduction : List (SyntacticFormula L) → SyntacticFormula L → Type u
  | tauto {Δ p} : ProofArrow T Δ p → Deduction Δ p
  | axm {Δ σ} :
    σ ∈ T → Deduction Δ (emb σ)
  | wekening {Δ Γ p} :
    Δ ⊆ Γ → Deduction Δ p → Deduction Γ p    
  | have {Δ p q} :
    Deduction Δ p → Deduction (p :: Δ) q → Deduction Δ q
  | assumption {Δ p} :
    p ∈ Δ → Deduction Δ p
  | contradiction {Δ} (p) {q} :
    Deduction Δ p → Deduction Δ (~p) → Deduction Δ q
  -- ⊤ - right
  | trivial {Δ} : Deduction Δ ⊤
  -- ⊥ - left
  | explode {Δ p} : Deduction Δ ⊥ → Deduction Δ p
  -- → right
  | intro {Δ p q} : Deduction (p :: Δ) q → Deduction Δ (p ⟶ q) 
  -- → left
  | mdp {Δ p q} :
    Deduction Δ (p ⟶ q) → Deduction Δ p → Deduction Δ q
  -- ∧ right
  | split {Δ p q} :
    Deduction Δ p → Deduction Δ q →Deduction Δ (p ⋏ q)
  -- ∧ left
  | andLeft {Δ p q} :
    Deduction Δ (p ⋏ q) → Deduction Δ p
  | andRight {Δ p q} :
    Deduction Δ (p ⋏ q) → Deduction Δ q
  -- ∨ right
  | orLeft {Δ p q} :
    Deduction Δ p → Deduction Δ (p ⋎ q)
  | orRight {Δ p q} :
    Deduction Δ q → Deduction Δ (p ⋎ q)
  -- ∨ left
  | cases {Δ p q r} :
    Deduction Δ (p ⋎ q) → Deduction (p :: Δ) r → Deduction (q :: Δ) r → Deduction Δ r
  -- ∀ right
  | generalize {Δ} {p} :
    Deduction (Δ.map shift) (free p) → Deduction Δ (∀' p)
  -- ∀ left
  | specialize (t) {Δ p} :
    Deduction Δ (∀' p) → Deduction Δ (subst t p)
  -- ∃ right
  | use (t) {Δ p} :
    Deduction Δ (subst t p) → Deduction Δ (∃' p)
  -- ∃ left
  | exCases {Δ p q} :
    Deduction Δ (∃' p) → Deduction (free p :: Δ.map shift) (shift q) → Deduction Δ q

notation Δ " ⟹[" T "] " p => Deduction T Δ p

open Qq

inductive DeductionCode (L : Q(Language.{u})) : Type
  | have    : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | assumption : DeductionCode L
  | contradiction : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | trivial : DeductionCode L
  | explode : DeductionCode L → DeductionCode L
  | intro : DeductionCode L → DeductionCode L
  | mdp   : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L  
  | split : DeductionCode L → DeductionCode L → DeductionCode L
  -- TODO
  | cases : (e₁ e₂ : Q(SyntacticFormula $L)) → DeductionCode L → DeductionCode L → DeductionCode L → DeductionCode L
  | generalize : DeductionCode L → DeductionCode L
  -- TODO
  | exCases :  Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L
  | since : Syntax → DeductionCode L
  | missing : DeductionCode L

end FirstOrder
