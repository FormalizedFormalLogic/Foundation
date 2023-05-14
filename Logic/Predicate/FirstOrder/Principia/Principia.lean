import Logic.Predicate.FirstOrder.Calculus
import Logic.Predicate.FirstOrder.Eq

universe u v

namespace FirstOrder

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

variable (T : Theory L) {μ : Type v}

open SubFormula

def SequentList.fvarList (l : List $ SubFormula L μ n) : List μ :=
  l.bind SubFormula.fvarList

def fleshVar (C : List $ SyntacticFormula L) : ℕ := (SequentList.fvarList C).sup

structure ProofArrow (T : Theory L) (Δ : List (SyntacticFormula L)) (p : SyntacticFormula L) where
  leftHand : List (Sentence L)
  hleftHand : ∀ σ ∈ leftHand, σ ∈ T
  derivationList : DerivationList (p :: ((leftHand.map emb ++ Δ).map (~·)))

variable {T}

noncomputable def Proof.toProofArrow {σ : Sentence L} (b : T ⊢ σ) : ProofArrow T [] (emb σ) where
  leftHand := b.leftHand.toList.map (~·)
  hleftHand := by
    simp; intro σ hσ 
    have : ∃ τ ∈ T, ~τ = σ := by simpa using b.hleftHand hσ
    rcases this with ⟨τ, hτ, rfl⟩; simp[hτ]
  derivationList := b.derivation.cast (by simp[DerivationList, Function.comp, List.toFinset_map])

namespace ProofArrow
open DerivationCutRestricted
variable {Δ Γ : List (SyntacticFormula L)}

def derivation (b : ProofArrow T Δ p) : ⊢ᶜ (p :: ((b.leftHand.map emb ++ Δ).map (~·))).toFinset := b.derivationList

def toProof {σ : Sentence L} (b : ProofArrow T [] (emb σ)) : T ⊢ σ where
  leftHand := b.leftHand.toFinset.image (~·)
  hleftHand := by simp[Set.subset_def]; intro σ hσ; exact ⟨σ, b.hleftHand σ hσ, rfl⟩
  derivation := b.derivation.cast (by simp[List.toFinset_map, Finset.image_image, Function.comp])

def cast {p p'} (b : ProofArrow T Δ p) (h : p = p') : ProofArrow T Δ p' :=
  h ▸ b

def cast' {Δ Δ' p p'} (b : ProofArrow T Δ p) (hΔ : Δ = Δ') (hp : p = p') : ProofArrow T Δ' p' :=
  hΔ ▸ hp ▸ b

protected def rewrite (f : ℕ → SyntacticTerm L) {p} (b : ProofArrow T Δ p) :
    ProofArrow T (Δ.map $ rewrite f) (rewrite f p) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList := (b.derivation.rewriteCut f).cast (by
    simp[shifts_eq_image, Finset.image_union, List.toFinset_map, Finset.image_image]; congr
    · funext p; simp[SubFormula.rewrite, SubFormula.emb, SubFormula.map, SubFormula.bind_bind]; congr; funext; contradiction
    · funext p; simp)

protected def shift {p} (b : ProofArrow T Δ p) : ProofArrow T (Δ.map shift) (shift p) := b.rewrite _

def byAxiom {σ} (h : σ ∈ T) : ProofArrow T Δ (emb σ) where
  leftHand := [σ]
  hleftHand := by simp[h]
  derivationList := em (p := emb σ) (by simp) (by simp)

def trans {p q} (b₁ : ProofArrow T Δ p) (b₂ : ProofArrow T (p :: Δ) q) : ProofArrow T Δ q where
  leftHand := b₁.leftHand ++ b₂.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ); exact b₁.hleftHand _ hσ; exact b₂.hleftHand _ hσ
  derivationList :=
    (cutCut (p := p)
      (Δ := ((b₁.leftHand.map emb ++ Δ).map (~·)).toFinset)
      (Γ := insert q ((b₂.leftHand.map emb ++ Δ).map (~·)).toFinset)
      (b₁.derivationList.cast (by simp))
      (b₂.derivationList.cast (by simp[Finset.Insert.comm]))).cast
        (by simp[Finset.union_self, Finset.union_comm (Δ.map (~·)).toFinset])

def assumption {p} (h : p ∈ Δ) : ProofArrow T Δ p where
  leftHand := []
  hleftHand := by simp
  derivationList := em (p := p) (by simp) (by simp[h])

def weakening' {p q} (h : ~p :: Δ ⊆ ~q :: Γ) (b : ProofArrow T Δ p) : ProofArrow T Γ q where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList := b.derivationList.weakening
    (by intro x; simp[Function.comp, List.toFinset_map]
        rintro (rfl | h | ⟨y, hy, rfl⟩)
        · have : x = q ∨ ~x ∈ Γ := by simpa using @h (~x) (by simp);
          rcases this with (rfl | h) <;> simp
          exact Or.inr (Or.inr ⟨~x, h, by simp⟩)
        · exact Or.inr (Or.inl h)
        · have : y = ~q ∨ y ∈ Γ := by simpa using @h y (by simp[hy])
          rcases this with (rfl | h) <;> simp[*])

def weakening {p} (h : Δ ⊆ Γ) (b : ProofArrow T Δ p) : ProofArrow T Γ p := 
  b.weakening' (List.cons_subset_cons _ h)

def contradiction {p} (q) (b₁ : ProofArrow T Δ p) (b₂ : ProofArrow T Δ (~p)) : ProofArrow T Δ q where
  leftHand := b₁.leftHand ++ b₂.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ); exact b₁.hleftHand _ hσ; exact b₂.hleftHand _ hσ
  derivationList :=
    let Γ := (((b₁.leftHand ++ b₂.leftHand).map emb ++ Δ).map (~·)).toFinset
    have b₁₁ : ⊢ᶜ insert p Γ := b₁.derivationList.weakening
      (by simp; exact Finset.insert_subset_insert _ (Finset.union_subset_union (by rfl) (Finset.subset_union_right _ _)))
    have b₂₁ : ⊢ᶜ insert (~p) Γ := b₂.derivationList.weakening
      (by simp; exact Finset.insert_subset_insert _ (Finset.subset_union_right _ _))
    (cutCut b₁₁ b₂₁).weakening (by simp[Finset.subset_insert])

def trivial : ProofArrow T Δ ⊤ := ⟨[], by simp, verum _ (by simp)⟩

def explode {p} (b : ProofArrow T Δ ⊥) : ProofArrow T Δ p where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have b₁ : ⊢ᶜ (insert ⊥ $ insert p Γ) := b.derivationList.weakening (by simp; exact Finset.insert_subset_insert _ (Finset.subset_insert _ _))
    have b₂ : ⊢ᶜ (insert ⊤ $ insert p Γ) := verum _ (by simp)
    (cutCut b₁ b₂).cast (by simp)

def intro {p q} (b : ProofArrow T (p :: Δ) q) : ProofArrow T Δ (p ⟶ q) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList :=
    have : ⊢ᶜ (insert (~p) $ insert q ((b.leftHand.map emb ++ Δ).map (~·)).toFinset) :=
      b.derivationList.cast (by simp[Finset.Insert.comm])
    (or _ _ _ this).cast (by simp[SubFormula.imp_eq])

def absurd {p} (b : ProofArrow T (p :: Δ) ⊥) : ProofArrow T Δ (~p) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have b₁ : ⊢ᶜ (insert ⊥ $ insert (~p) Γ) := b.derivationList.cast (by simp)
    have b₂ : ⊢ᶜ (insert ⊤ $ insert (~p) Γ) := verum _ (by simp)
    (cutCut b₁ b₂).cast (by simp)

def modusPonens {p q} (b₁ : ProofArrow T Δ (p ⟶ q)) (b₂ : ProofArrow T Δ p) : ProofArrow T Δ q where
  leftHand := b₁.leftHand ++ b₂.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ); exact b₁.hleftHand _ hσ; exact b₂.hleftHand _ hσ
  derivationList :=
    let Γ := (((b₁.leftHand ++ b₂.leftHand).map emb ++ Δ).map (~·)).toFinset
    have b₁₁ : ⊢ᶜ insert (~p ⋎ q) Γ := b₁.derivationList.weakening
      (by simp[SubFormula.imp_eq]; exact Finset.insert_subset_insert _ (Finset.union_subset_union (by rfl) (Finset.subset_union_right _ _)))
    have b₂₁ : ⊢ᶜ insert p Γ := b₂.derivationList.weakening
      (by simp; exact (Finset.insert_subset_insert _ $ by
        rw[←Finset.union_assoc]; exact Finset.union_subset_union (Finset.subset_union_right _ _) (by rfl)))
    have : ⊢ᶜ (insert (p ⋏ ~q) $ insert q Γ) := and _ _ _
      (b₂₁.weakening (by simp[Finset.Insert.comm]; exact Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      (em (p := q) (by simp) (by simp))
    (cutCut (Δ := Γ) (Γ := insert q Γ) b₁₁ (this.cast (by simp))).cast (by simp)

def split {p q} (b₁ : ProofArrow T Δ p) (b₂ : ProofArrow T Δ q) : ProofArrow T Δ (p ⋏ q) where
  leftHand := b₁.leftHand ++ b₂.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ); exact b₁.hleftHand _ hσ; exact b₂.hleftHand _ hσ
  derivationList :=
    let Γ := (((b₁.leftHand ++ b₂.leftHand).map emb ++ Δ).map (~·)).toFinset
    have b₁₁ : ⊢ᶜ insert p Γ := b₁.derivationList.weakening
      (by simp[SubFormula.imp_eq]; exact Finset.insert_subset_insert _ (Finset.union_subset_union (by rfl) (Finset.subset_union_right _ _)))
    have b₂₁ : ⊢ᶜ insert q Γ := b₂.derivationList.weakening
      (by simp; exact (Finset.insert_subset_insert _ $ by
        rw[←Finset.union_assoc]; exact Finset.union_subset_union (Finset.subset_union_right _ _) (by rfl)))
    (and _ _ _ b₁₁ b₂₁).cast (by simp)

def splits : {k : ℕ} → {p : Fin k → SyntacticFormula L} → ((i : Fin k) → ProofArrow T Δ (p i)) →
    ProofArrow T Δ (Matrix.conj p)
  | 0,     _, _ => trivial
  | _ + 1, p, b => split (b 0) (splits (p := Matrix.vecTail p) (fun i => b i.succ))

def andLeft {p q} (b : ProofArrow T Δ (p ⋏ q)) : ProofArrow T Δ p where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have b₁ : ⊢ᶜ insert (p ⋏ q) Γ := b.derivationList.cast (by simp)
    have b₂ : ⊢ᶜ (insert (~p ⋎ ~q) $ insert p Γ) := or _ _ _ (em (p := p) (by simp) (by simp))
    (cutCut (Δ := Γ) (Γ := insert p Γ) b₁ (b₂.cast (by simp))).cast (by simp)

def andRight {p q} (b : ProofArrow T Δ (p ⋏ q)) : ProofArrow T Δ q where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have b₁ : ⊢ᶜ insert (p ⋏ q) Γ := b.derivationList.cast (by simp)
    have b₂ : ⊢ᶜ (insert (~p ⋎ ~q) $ insert q Γ) := or _ _ _ (em (p := q) (by simp) (by simp))
    (cutCut (Δ := Γ) (Γ := insert q Γ) b₁ (b₂.cast (by simp))).cast (by simp)

def destruct {p q r} (b₀ : ProofArrow T Δ (p ⋏ q)) (b : ProofArrow T (p :: q :: Δ) r) : ProofArrow T Δ r :=
  have : ProofArrow T Δ p := b₀.trans (andLeft (q := q) $ assumption $ by simp)
  have b' : ProofArrow T (q :: Δ) r := (this.weakening (by simp)).trans b
  have : ProofArrow T Δ q := b₀.trans (andRight (p := p) $ assumption $ by simp)
  this.trans b'

def byConj : {n : ℕ} → (p : Fin n → SyntacticFormula L) →
    (b : ProofArrow T Δ (Matrix.conj p)) → (i : Fin n) → ProofArrow T Δ (p i)
  | 0,     p, _ => fun i => by have : False := finZeroElim (α := fun _ => False) i; contradiction
  | n + 1, p, b => Fin.cases (andLeft b) (byConj (Matrix.vecTail p) (b.andRight))

def orLeft {p q} (b : ProofArrow T Δ p) : ProofArrow T Δ (p ⋎ q) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have : ⊢ᶜ (insert p $ insert q Γ) := b.derivationList.weakening (by simp[Finset.Insert.comm p, Finset.subset_insert])
    (or _ _ _ this).cast (by simp)

def orRight {p q} (b : ProofArrow T Δ q) : ProofArrow T Δ (p ⋎ q) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have : ⊢ᶜ (insert p $ insert q Γ) := b.derivationList.weakening (by simp[Finset.subset_insert])
    (or _ _ _ this).cast (by simp)

def cases {p q r} (b₀ : ProofArrow T Δ (p ⋎ q)) (b₁ : ProofArrow T (p :: Δ) r) (b₂ : ProofArrow T (q :: Δ) r) : ProofArrow T Δ r where
  leftHand := b₀.leftHand ++ b₁.leftHand ++ b₂.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ | hσ); exact b₀.hleftHand _ hσ; exact b₁.hleftHand _ hσ; exact b₂.hleftHand _ hσ
  derivationList :=
    let Γ := (((b₀.leftHand ++ b₁.leftHand ++ b₂.leftHand).map emb ++ Δ).map (~·)).toFinset
    have b₀₁ : ⊢ᶜ insert (p ⋎ q) Γ := b₀.derivationList.weakening (by
      simp[SubFormula.imp_eq]; exact Finset.insert_subset_insert _
        (Finset.union_subset_union (by rfl) (by rw[←Finset.union_assoc]; exact Finset.subset_union_right _ _)))
    have b₁₁ : ⊢ᶜ (insert (~p) $ insert r Γ) := b₁.derivationList.weakening
      (by simp[Finset.Insert.comm]; exact (Finset.insert_subset_insert _ $ Finset.insert_subset_insert _ $
        Finset.union_subset
          (fun x hx => by simp only [Finset.mem_union]; exact Or.inr $ Or.inl hx)
          (fun x hx => by simp only [Finset.mem_union]; exact Or.inr $ Or.inr $ Or.inr hx)))
    have b₂₁ : ⊢ᶜ (insert (~q) $ insert r Γ) := b₂.derivationList.weakening
      (by simp[Finset.Insert.comm]; exact (Finset.insert_subset_insert _ $ Finset.insert_subset_insert _ $
        Finset.union_subset
          (fun x hx => by simp only [Finset.mem_union]; exact Or.inr $ Or.inr $ Or.inl hx)
          (fun x hx => by simp only [Finset.mem_union]; exact Or.inr $ Or.inr $ Or.inr hx)))  
    have b₃ : ⊢ᶜ (insert (~(p ⋎ q)) $ insert r Γ) := and _ _ _ b₁₁ b₂₁
    (cutCut b₀₁ b₃).cast (by simp)

def generalize {p} (b : ProofArrow T (Δ.map shift) (free p)) : ProofArrow T Δ (∀' p) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    (DerivationCutRestricted.all Γ p
      (b.derivationList.cast $ by simp[shifts_eq_image, Finset.image_union, ←List.toFinset_map, Function.comp])).cast (by simp)

def specialize (t) {p} (b : ProofArrow T Δ (∀' p)) : ProofArrow T Δ (⟦↦ t⟧ p) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    have : ⊢ᶜ (insert (∃' ~p) $ insert (⟦↦ t⟧ p) Γ) := ex _ t (~p) (em (p := ⟦↦ t⟧ p) (by simp) (by simp))
    (cutCut (Δ := Γ) (Γ := insert (⟦↦ t⟧ p) Γ) (p := ∀' p) (b.derivationList.cast $ by simp) this).cast (by simp)

def specializes : {n : ℕ} → (v : Fin n → SyntacticTerm L) → {p : SyntacticSubFormula L n} →
    ProofArrow T Δ (univClosure p) → ProofArrow T Δ (substs v p)
  | 0,     v, p, b => b.cast (by simp)
  | n + 1, v, p, b =>
    have : ProofArrow T Δ (∀' substs (#(Fin.last 0) :> SubTerm.bShift ∘ v ∘ Fin.succ) p) :=
      specializes (v ∘ Fin.succ) b
    (specialize (v 0) this).cast
      (by simp[SubFormula.substs, SubFormula.bind_bind]; congr
          funext i; cases i using Fin.cases <;> simp[SubTerm.bShift, SubTerm.map, SubTerm.bind_bind])

def useInstance (t) {p} (b : ProofArrow T Δ (⟦↦ t⟧ p)) : ProofArrow T Δ (∃' p) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivationList :=
    let Γ := ((b.leftHand.map emb ++ Δ).map (~·)).toFinset
    (ex Γ t p $ b.derivationList.cast $ by simp).cast (by simp)

def exCases {p q} (b₀ : ProofArrow T Δ (∃' p)) (b₁ : ProofArrow T (free p :: Δ.map shift) (shift q)) : ProofArrow T Δ q where
  leftHand := b₀.leftHand ++ b₁.leftHand
  hleftHand := by simp; rintro σ (hσ | hσ); exact b₀.hleftHand _ hσ; exact b₁.hleftHand _ hσ
  derivationList :=
    let Γ := (((b₀.leftHand ++ b₁.leftHand).map emb ++ Δ).map (~·)).toFinset
    have b₀₁ : ⊢ᶜ insert (∃' p) Γ := b₀.derivationList.weakening
      (by simp[SubFormula.imp_eq]; exact Finset.insert_subset_insert _ (Finset.union_subset_union (by rfl) (Finset.subset_union_right _ _)))
    have b₁₁ : ⊢ᶜ (insert (free $ ~p) $ shifts $ insert q Γ) := b₁.derivationList.weakening
      (by simp[shifts_insert, Finset.Insert.comm]; exact
        (Finset.insert_subset_insert _ $ Finset.insert_subset_insert _ $ by
          simp[shifts_eq_image, Finset.image_union, ←List.toFinset_map, Function.comp, Finset.subset_union_right]))
    have b₁₂ : ⊢ᶜ (insert (~(∃' p)) $ insert q Γ) :=
      DerivationCutRestricted.all (insert q Γ) (~p) (b₁₁.cast (by simp))
    (cutCut b₀₁ b₁₂).cast (by simp)

section Eq
variable [L.Eq] [EqTheory T]
open SubTerm SubFormula Theory Eq

def eqRefl (t : SyntacticTerm L) : ProofArrow T Δ (“ᵀ!t = ᵀ!t”) :=
  have b : ProofArrow T Δ (“∀ #0 = #0”) := (byAxiom (EqTheory.eq Theory.Eq.refl)).cast (by simp)
  (specialize t b).cast (by simp)

def eqSymm {t₁ t₂ : SyntacticTerm L} (b : ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₂”) : ProofArrow T Δ “ᵀ!t₂ = ᵀ!t₁” :=
  have : ProofArrow T Δ “∀ ∀ (#1 = #0 → #0 = #1)” :=
    (byAxiom (EqTheory.eq Theory.Eq.symm)).cast (by simp)
  have : ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₂ → ᵀ!t₂ = ᵀ!t₁” := (this.specializes ![t₂, t₁]).cast (by simp)
  this.modusPonens  b

def eqTrans {t₁ t₂ t₃ : SyntacticTerm L} (b₁ : ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₂”) (b₂ : ProofArrow T Δ “ᵀ!t₂ = ᵀ!t₃”) :
    ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₃” :=
  have : ProofArrow T Δ “∀ ∀ ∀ (#2 = #1 → #1 = #0 → #2 = #0)” :=
    (byAxiom (EqTheory.eq Theory.Eq.trans)).cast (by simp)
  have : ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₂ → ᵀ!t₂ = ᵀ!t₃ → ᵀ!t₁ = ᵀ!t₃” := (this.specializes ![t₃, t₂, t₁]).cast (by simp)
  (this.modusPonens b₁).modusPonens b₂

def termExt : (t : SyntacticSubTerm L n) → (v₁ v₂ : Fin n → SyntacticTerm L) →
    ((i : Fin n) → ProofArrow T Δ “ᵀ!(v₁ i) = ᵀ!(v₂ i)”) → ProofArrow T Δ “ᵀ!(t.substs v₁) = ᵀ!(t.substs v₂)”
  | #x,       _,  _,  b => b x
  | &x,       _,  _,  _ => eqRefl &x
  | func f v, v₁, v₂, b =>
    have : ProofArrow T Δ
      “∀* ((⋀ i, ᵀ!(varSumInL i) = ᵀ!(varSumInR i)) →
      ᵀ!(func f varSumInL) = ᵀ!(func f varSumInR))” :=
    (byAxiom (EqTheory.eq (Theory.Eq.funcExt f))).cast (by simp[vecEq, Matrix.hom_conj']; rfl)    
    have : ProofArrow T Δ
      “(⋀ i, ᵀ!((v i).substs v₁) = ᵀ!((v i).substs v₂)) → ᵀ!(func f fun i => (v i).substs v₁) = ᵀ!(func f fun i => (v i).substs v₂)” :=
      by simpa [Matrix.hom_conj', substs_func] using
        this.specializes (Matrix.vecAppend rfl (fun i => (v i).substs v₁) (fun i => (v i).substs v₂))
    this.modusPonens (splits fun i => termExt (v i) v₁ v₂ b)

private def negImply {p q : SyntacticFormula L} (b : ProofArrow T Δ (p ⟶ q)) : ProofArrow T Δ (~q ⟶ ~p) :=
  (b.trans $ intro $ absurd $ trans (p := q) (modusPonens (p := p) (assumption $ by simp) (assumption $ by simp)) $
    contradiction (p := q) ⊥ (assumption $ by simp) (assumption $ by simp))

private def relExtAux {n} {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) (v₁ v₂ : Fin n → SyntacticTerm L)
  (b : (i : Fin n) → ProofArrow T Δ “ᵀ!(v₁ i) = ᵀ!(v₂ i)”) : ProofArrow T Δ (⟦→ v₁ ⟧ (rel r v) ⟶ ⟦→ v₂ ⟧ (rel r v)) :=
  have : ProofArrow T Δ
    “∀* ((⋀ i, ᵀ!(varSumInL i) = ᵀ!(varSumInR i)) → (!(rel r varSumInL) → !(rel r varSumInR)))” :=
  (byAxiom (EqTheory.eq (Theory.Eq.relExt r))).cast (by simp[vecEq, Matrix.hom_conj']; rfl)    
  have : ProofArrow T Δ “(⋀ i, ᵀ!((v i).substs v₁) = ᵀ!((v i).substs v₂)) →
    !(rel r fun i => (v i).substs v₁) → !(rel r fun i => (v i).substs v₂)” :=
  by simpa [Matrix.hom_conj', substs_func, substs_rel _ r] using
    this.specializes (Matrix.vecAppend rfl (fun i => (v i).substs v₁) (fun i => (v i).substs v₂))
  this.modusPonens (splits fun i => termExt (v i) v₁ v₂ b)

-- 不要だが計算を軽くするために`noncomputable`をつけている
noncomputable def formulaExtAux : {Δ : List (SyntacticFormula L)} → {n : ℕ} → (p : SyntacticSubFormula L n) → (v₁ v₂ : Fin n → SyntacticTerm L) →
    ((i : Fin n) → ProofArrow T Δ “ᵀ!(v₁ i) = ᵀ!(v₂ i)”) → ProofArrow T Δ (⟦→ v₁⟧ p ⟶ ⟦→ v₂⟧ p)
  | Δ, _, ⊤,        v₁, v₂, _ => (intro $ assumption $ by simp)
  | Δ, _, ⊥,        v₁, v₂, _ => (intro $ assumption $ by simp)
  | Δ, _, rel r v,  v₁, v₂, b => relExtAux r v v₁ v₂ b
  | Δ, _, nrel r v, v₁, v₂, b => (relExtAux r v v₂ v₁ (fun i => eqSymm (b i))).negImply
  | Δ, _, p ⋏ q,    v₁, v₂, b =>
    have bp : ProofArrow T Δ (⟦→ v₁⟧ p ⟶ ⟦→ v₂⟧ p) := formulaExtAux p v₁ v₂ b
    have bq : ProofArrow T Δ (⟦→ v₁⟧ q ⟶ ⟦→ v₂⟧ q) := formulaExtAux q v₁ v₂ b
    (intro $ split
      (modusPonens (bp.weakening $ by simp) (andLeft (q := ⟦→ v₁⟧ q) $ assumption $ by simp))
      (modusPonens (bq.weakening $ by simp) (andRight (p := ⟦→ v₁⟧ p) $ assumption $ by simp)))
  | Δ, _, p ⋎ q,    v₁, v₂, b =>
    have bp : ProofArrow T Δ (⟦→ v₁⟧ p ⟶ ⟦→ v₂⟧ p) := formulaExtAux p v₁ v₂ b
    have bq : ProofArrow T Δ (⟦→ v₁⟧ q ⟶ ⟦→ v₂⟧ q) := formulaExtAux q v₁ v₂ b
    (intro $ cases (p := ⟦→ v₁⟧ p) (q := ⟦→ v₁⟧ q) (assumption $ by simp)
      (orLeft $ modusPonens (bp.weakening $ List.subset_cons_of_subset _ $ by simp) $ assumption $ by simp)
      (orRight $ modusPonens (bq.weakening $ List.subset_cons_of_subset _ $ by simp) $ assumption $ by simp))
  | Δ, _, ∀' p,     v₁, v₂, b =>
    let Δ' := (∀' shift (⟦→ #0 :> bShift ∘ v₁⟧ p)) :: Δ.map shift.toFun
    let v₁' := fun i => (#0 :> bShift ∘ v₁ $ i).free
    let v₂' := fun i => (#0 :> bShift ∘ v₂ $ i).free
    have b' : (i : Fin _) → ProofArrow T Δ' (“ᵀ!(v₁' i) = ᵀ!(v₂' i)”) :=
      Fin.cases (eqRefl _) (fun i => ((b i).shift.weakening (by simp)).cast (by simp))
    have bp : ProofArrow T Δ' (⟦→ v₁'⟧ $ shift p) :=
      (specialize &0 (p := shift (⟦→ #0 :> bShift ∘ v₁⟧ p)) $ assumption $ by simp).cast (by simp[←free_substs_eq_substs_shift])
    have : ProofArrow T Δ' (⟦→ v₂'⟧ $ shift p) := modusPonens (formulaExtAux (shift p) v₁' v₂' b') bp
    have : ProofArrow T Δ (∀' ⟦→ #0 :> bShift ∘ v₁⟧ p ⟶ ∀' ⟦→ #0 :> bShift ∘ v₂⟧ p) :=
      (intro $ generalize $ this.cast' (by simp) (by simp[substs_all, free_substs_eq_substs_shift]))
    this.cast (by simp[substs_all])
  | Δ, _, ∃' p,     v₁, v₂, b =>
    let Δ' := ⟦→ fun i => ((#0 :> bShift ∘ v₁) i).free⟧ (shift p) :: (∃' shift (⟦→ #0 :> bShift ∘ v₁⟧ p)) :: Δ.map shift.toFun
    let v₁' := fun i => (#0 :> bShift ∘ v₁ $ i).free
    let v₂' := fun i => (#0 :> bShift ∘ v₂ $ i).free
    have b' : (i : Fin _) → ProofArrow T Δ' (“ᵀ!(v₁' i) = ᵀ!(v₂' i)”) :=
      Fin.cases (eqRefl _) (fun i => ((b i).shift.weakening $ List.subset_cons_of_subset _ $ by simp).cast (by simp))
    have ih : ProofArrow T Δ' (⟦→ v₁'⟧ (shift p) ⟶ ⟦→ v₂'⟧ (shift p)) := formulaExtAux (Δ := Δ') (shift p) v₁' v₂' b'
    have : ProofArrow T Δ' (∃' SubFormula.shift (⟦→ #0 :> bShift ∘ v₂⟧ p)) :=
      (useInstance &0 $ (ih.modusPonens (assumption $ by simp)).cast (by simp[free_substs_eq_substs_shift]))
    have : ProofArrow T Δ (∃' ⟦→ #0 :> bShift ∘ v₁⟧ p ⟶ ∃' ⟦→ #0 :> bShift ∘ v₂⟧ p) :=
      (intro $ exCases (p := ⟦→ #0 :> bShift ∘ v₁⟧ p) (assumption $ by simp) (this.cast' (by simp[free_substs_eq_substs_shift]) (by simp)))
    this.cast (by simp[substs_ex])
  termination_by formulaExtAux p _ _ _ => p.complexity

noncomputable def formulaExt (p : SyntacticSubFormula L n) (v₁ v₂ : Fin n → SyntacticTerm L) 
  (b : (i : Fin n) → ProofArrow T Δ “ᵀ!(v₁ i) = ᵀ!(v₂ i)”) (d : ProofArrow T Δ (⟦→ v₂⟧ p)) :
    ProofArrow T Δ (⟦→ v₁⟧ p) :=
  (formulaExtAux p v₂ v₁ (fun i => (b i).eqSymm)).modusPonens d

noncomputable def rewriteEq {p : SyntacticSubFormula L 1} {t₁ t₂ : SyntacticTerm L}
  (b : ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₂”) (d : ProofArrow T Δ (⟦↦ t₂⟧ p)) :
    ProofArrow T Δ (⟦↦ t₁⟧ p) :=
  ((formulaExtAux p ![t₂] ![t₁] (fun i => b.eqSymm.cast $ by simp)).modusPonens
    (d.cast $ by simp)).cast (by simp)

end Eq

end ProofArrow

variable (T)
variable [L.Eq] [EqTheory T]

inductive Principia : List (SyntacticFormula L) → SyntacticFormula L → Type u
  | tauto {Δ p} : ProofArrow T Δ p → Principia Δ p
  | axm {Δ σ} :
    σ ∈ T → Principia Δ (emb σ)
  | weakening' {Δ Γ p q} :
    ~p :: Δ ⊆ ~q :: Γ → Principia Δ p → Principia Γ q
  | rewrite (f : ℕ → SyntacticTerm L) {p} :
    Principia Δ p → Principia (Δ.map $ rewrite f) (rewrite f p)    
  | trans {Δ p q} :
    Principia Δ p → Principia (p :: Δ) q → Principia Δ q
  | assumption {Δ p} :
    p ∈ Δ → Principia Δ p
  | contradiction {Δ p} (q) :
    Principia Δ p → Principia Δ (~p) → Principia Δ q
  -- ⊤ - right
  | trivial {Δ} : Principia Δ ⊤
  -- ⊥ - left
  | explode {Δ p} : Principia Δ ⊥ → Principia Δ p
  -- → right
  | intro {Δ p q} : Principia (p :: Δ) q → Principia Δ (p ⟶ q)
  -- → left
  | modusPonens {Δ p q} :
    Principia Δ (p ⟶ q) → Principia Δ p → Principia Δ q
  -- ∧ right
  | split {Δ p q} :
    Principia Δ p → Principia Δ q →Principia Δ (p ⋏ q)
  -- ∧ left
  | andLeft {Δ p q} :
    Principia Δ (p ⋏ q) → Principia Δ p
  | andRight {Δ p q} :
    Principia Δ (p ⋏ q) → Principia Δ q
  -- ∨ right
  | orLeft {Δ p q} :
    Principia Δ p → Principia Δ (p ⋎ q)
  | orRight {Δ p q} :
    Principia Δ q → Principia Δ (p ⋎ q)
  -- ∨ left
  | cases {Δ p q r} :
    Principia Δ (p ⋎ q) → Principia (p :: Δ) r → Principia (q :: Δ) r → Principia Δ r
  -- ∀ right
  | generalize {Δ} {p} :
    Principia (Δ.map shift) (free p) → Principia Δ (∀' p)
  -- ∀ left
  | specialize (t) {Δ p} :
    Principia Δ (∀' p) → Principia Δ (⟦↦ t⟧ p)
  -- ∃ right
  | useInstance (t) {Δ p} :
    Principia Δ (⟦↦ t⟧ p) → Principia Δ (∃' p)
  -- ∃ left
  | exCases {Δ p q} :
    Principia Δ (∃' p) → Principia (free p :: Δ.map shift) (shift q) → Principia Δ q
  -- =
  | eqRefl {Δ} (t) :
    Principia Δ “ᵀ!t = ᵀ!t”
  | eqSymm {Δ t₁ t₂} :
    Principia Δ “ᵀ!t₁ = ᵀ!t₂” → Principia Δ “ᵀ!t₂ = ᵀ!t₁”
  | eqTrans {Δ t₁ t₂ t₃} :
    Principia Δ “ᵀ!t₁ = ᵀ!t₂” → Principia Δ “ᵀ!t₂ = ᵀ!t₃” → Principia Δ “ᵀ!t₁ = ᵀ!t₃”
  | rewriteEq {Δ} {p : SyntacticSubFormula L 1} {t₁ t₂ : SyntacticTerm L} :
    Principia Δ “ᵀ!t₁ = ᵀ!t₂” → Principia Δ (⟦↦ t₂⟧ p) → Principia Δ (⟦↦ t₁⟧ p)

notation Δ:0 " ⟹[" T "] " p => Principia T Δ p

variable {T}

namespace Principia
open ProofArrow

def toStr : {Δ : List (SyntacticFormula L)} → {p : SyntacticFormula L} → (Δ ⟹[T] p) → String
  | _, _, tauto _               => "tauto"
  | _, _, axm _                 => "axiom"
  | _, _, weakening' _ d        => "weakening\n" ++ d.toStr
  | _, _, rewrite _ d           => "rewrite\n" ++ d.toStr
  | _, _, trans c₁ c₂           => "have: {\n" ++ c₁.toStr ++ "\n}\n" ++ c₂.toStr
  | _, _, assumption _          => "assumption"
  | _, _, contradiction _ c₁ c₂ => "contradiction: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"
  | _, _, trivial               => "trivial"
  | _, _, explode c             => "explode" ++ c.toStr
  | _, _, intro c               => "intro\n" ++ c.toStr
  | _, _, modusPonens c₁ c₂     => "have: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"
  | _, _, split c₁ c₂           => "∧ split: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"
  | _, _, andLeft c             => "∧ left\n" ++ c.toStr
  | _, _, andRight c            => "∧ right\n" ++ c.toStr
  | _, _, orLeft c              => "∨ left\n" ++ c.toStr
  | _, _, orRight c             => "∨ right\n" ++ c.toStr
  | _, _, cases c₀ c₁ c₂        => "∨ split: {\n" ++ c₀.toStr ++ "\n}\nor left: {\n" ++ c₁.toStr ++ "\n}\nor right: {\n" ++ c₂.toStr ++ "\n}"
  | _, _, generalize c          => "generalize\n" ++ c.toStr
  | _, _, specialize _ c        => "specialize\n" ++ c.toStr
  | _, _, useInstance _ c       => "use\n" ++ c.toStr
  | _, _, exCases c₀ c₁         => "∃ cases: {\n" ++ c₀.toStr ++ "\n}\n" ++ c₁.toStr
  | _, _, eqRefl _              => "refl"
  | _, _, eqSymm c              => "symmetry" ++ c.toStr
  | _, _, eqTrans c₁ c₂         => "trans: {\n" ++ c₁.toStr ++ "\n}\n and: {\n" ++ c₂.toStr ++ "\n}"
  | _, _, rewriteEq c₁ c₂       => "rewrite: {\n" ++ c₁.toStr ++ "\n}\n" ++ c₂.toStr

instance : Repr (Δ ⟹[T] p) := ⟨fun b _ => b.toStr⟩

instance : ToString (Δ ⟹[T] p) := ⟨toStr⟩

noncomputable def toProofArrow : {Δ : List (SyntacticFormula L)} → {p : SyntacticFormula L} →
    (Δ ⟹[T] p) → ProofArrow T Δ p
  | _, _, tauto d               => d
  | _, _, axm h                 => ProofArrow.byAxiom h
  | _, _, weakening' h d        => d.toProofArrow.weakening' h
  | _, _, rewrite f d           => d.toProofArrow.rewrite f
  | _, _, trans d₁ d₂           => d₁.toProofArrow.trans (d₂.toProofArrow)
  | _, _, assumption h          => ProofArrow.assumption h
  | _, _, contradiction _ d₁ d₂ => d₁.toProofArrow.contradiction _ d₂.toProofArrow
  | _, _, trivial               => ProofArrow.trivial
  | _, _, explode d             => d.toProofArrow.explode
  | _, _, intro d               => d.toProofArrow.intro
  | _, _, modusPonens d₁ d₂     => d₁.toProofArrow.modusPonens d₂.toProofArrow
  | _, _, split d₁ d₂           => d₁.toProofArrow.split d₂.toProofArrow
  | _, _, andLeft d             => d.toProofArrow.andLeft
  | _, _, andRight d            => d.toProofArrow.andRight
  | _, _, orLeft d              => d.toProofArrow.orLeft
  | _, _, orRight d             => d.toProofArrow.orRight
  | _, _, cases d₀ d₁ d₂        => d₀.toProofArrow.cases d₁.toProofArrow d₂.toProofArrow
  | _, _, generalize d          => d.toProofArrow.generalize
  | _, _, specialize t d        => d.toProofArrow.specialize t
  | _, _, useInstance t d       => d.toProofArrow.useInstance t
  | _, _, exCases d₀ d₁         => d₀.toProofArrow.exCases d₁.toProofArrow
  | _, _, eqRefl t              => ProofArrow.eqRefl t
  | _, _, eqSymm d              => d.toProofArrow.eqSymm
  | _, _, eqTrans d₁ d₂         => d₁.toProofArrow.eqTrans d₂.toProofArrow
  | _, _, rewriteEq d₀ d₁       => d₀.toProofArrow.rewriteEq d₁.toProofArrow

noncomputable def toProof {σ : Sentence L} :
    ([] ⟹[T] emb σ) → T ⊢ σ := fun b => b.toProofArrow.toProof

def cast {Δ p p'} (h : p = p') (b : Δ ⟹[T] p) : Δ ⟹[T] p' := h ▸ b 

def cast' {Δ Δ' p p'} (hΔ : Δ = Δ') (hp : p = p') (b : Δ ⟹[T] p) : Δ' ⟹[T] p' :=
  hΔ ▸ hp ▸ b

def axmOfEq (σ : Sentence L) (hp : emb σ = p) (hσ : σ ∈ T) : Δ ⟹[T] p := by rw[←hp]; exact axm hσ

end Principia

noncomputable def Proof.toPrincipia {σ : Sentence L} :
    T ⊢ σ → ([] ⟹[T] emb σ) := fun b => Principia.tauto (Proof.toProofArrow b)

end FirstOrder
