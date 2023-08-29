import Logic.Predicate.FirstOrder.Basic.Calculus

namespace LO

namespace FirstOrder

open SubFormula

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

namespace SubFormula

def isVType : {n : ℕ} → SubFormula L μ n → Bool
  | _, rel _ _  => true
  | _, nrel _ _ => true
  | _, ⊤        => true
  | _, ⊥        => true
  | _, _ ⋏ _    => false
  | _, _ ⋎ _    => true
  | _, ∀' _     => false
  | _, ∃' _     => true

lemma ne_and_of_isVType {p q r : SubFormula L μ n} (h : isVType p) : p ≠ q ⋏ r := by rintro rfl; simp[isVType] at h

lemma ne_all_of_isVType {p : SubFormula L μ n} {q} (h : isVType p) : p ≠ ∀' q := by rintro rfl; simp[isVType] at h

@[simp] lemma isVType_shift_iff {p : SyntacticSubFormula L n} : isVType (Rew.shiftl p) = isVType p := by
  induction p using rec' <;> simp[Rew.rel, Rew.nrel, isVType]

lemma isVType_neg_true_of_eq_false {p : SyntacticSubFormula L n} : isVType p = false → isVType (~p) = true := by
  induction p using rec' <;> simp[Rew.rel, Rew.nrel, isVType]

end SubFormula

namespace DerivationCutRestricted

variable {P : SyntacticFormula L → Prop} (hP : ∀ f p, P p → P (Rew.rewritel f p)) {Δ Δ₁ Δ₂ Γ : Sequent L}

def andInversion₁Aux : {Δ : Sequent L} → (d : ⊢ᶜ[P] Δ) → (p q : SyntacticFormula L) → ⊢ᶜ[P] insert p (Δ.erase (p ⋏ q))
  | _, axL Δ r v hpos hneg, p, q => axL _ r v (by simp[hpos]) (by simp[hneg])
  | _, verum Δ h,           p, q => verum _ (by simp[h])
  | _, and Δ p' q' dp dq,   p, q => by
    by_cases e : p' = p ∧ q' = q
    · simp[e]; exact (andInversion₁Aux dp p q).weakening
        (by simp[Finset.subset_iff]; rintro x hx (rfl | hΔ); { exact Or.inl e.1 }; { exact Or.inr ⟨hx, hΔ⟩ })
    · have ne : p' ⋏ q' ≠ p ⋏ q := by simp[e]
      have dp : ⊢ᶜ[P] (insert p' $ insert p (Δ.erase (p ⋏ q))) :=
        (andInversion₁Aux dp p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      have dq : ⊢ᶜ[P] (insert q' $ insert p (Δ.erase (p ⋏ q))) :=
        (andInversion₁Aux dq p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      exact (and _ _ _ dp dq).cast (by simp[Finset.erase_insert_of_ne ne, Finset.Insert.comm p])
  | _, or Δ r s d,          p, q =>
    have : ⊢ᶜ[P] (insert r $ insert s $ insert p $ Δ.erase (p ⋏ q)) :=
      (andInversion₁Aux d p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | rfl | hhx) <;> simp[*])
    (or _ _ _ this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm p])
  | _, all Δ r d,           p, q =>
    have : ⊢ᶜ[P] insert (Rew.freel r) (shifts $ insert p $ Δ.erase (p ⋏ q)) :=
      (andInversion₁Aux d (Rew.shiftl p) (Rew.shiftl q)).weakening
        (by simp[shifts_insert, shifts_erase, Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (all _ _ this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm p])
  | _, ex Δ t r d,          p, q =>
    have : ⊢ᶜ[P] insert ([→ t].hom r) (insert p $ Δ.erase (p ⋏ q)) :=
      (andInversion₁Aux d p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (ex _ t r this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm p])
  | _, cut Δ Γ r hr dΔ dΓ,  p, q =>
    have dΔ : ⊢ᶜ[P] (insert r $ insert p $ Δ.erase (p ⋏ q)) :=
      (andInversion₁Aux dΔ p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    have dΓ : ⊢ᶜ[P] (insert (~r) $ insert p $ Γ.erase (p ⋏ q)) :=
      (andInversion₁Aux dΓ p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (cut _ _ r hr dΔ dΓ).cast (by simp[Finset.erase_union])

def andInversion₁ {p q} (d : ⊢ᶜ[P] insert (p ⋏ q) Δ) : ⊢ᶜ[P] insert p Δ := 
  (andInversion₁Aux d p q).weakening (by simp; exact Finset.insert_subset_insert _ (Finset.erase_subset _ _))

def andInversion₂Aux : {Δ : Sequent L} → ⊢ᶜ[P] Δ → (p q : SyntacticFormula L) → ⊢ᶜ[P] insert q (Δ.erase (p ⋏ q))
  | _, axL Δ r v hpos hneg, p, q => axL _ r v (by simp[hpos]) (by simp[hneg])
  | _, verum Δ h,           p, q => verum _ (by simp[h])
  | _, and Δ p' q' dp dq,   p, q => by
    by_cases e : p' = p ∧ q' = q
    · simp[e]; exact (andInversion₂Aux dq p q).weakening
        (by simp[Finset.subset_iff]; rintro x hx (rfl | hΔ); { exact Or.inl e.2 }; { exact Or.inr ⟨hx, hΔ⟩ })
    · have ne : p' ⋏ q' ≠ p ⋏ q := by simp[e]
      have dp : ⊢ᶜ[P] (insert p' $ insert q (Δ.erase (p ⋏ q))) :=
        (andInversion₂Aux dp p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      have dq : ⊢ᶜ[P] (insert q' $ insert q (Δ.erase (p ⋏ q))) :=
        (andInversion₂Aux dq p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      exact (and _ _ _ dp dq).cast (by simp[Finset.erase_insert_of_ne ne, Finset.Insert.comm q])
  | _, or Δ r s d,          p, q =>
    have : ⊢ᶜ[P] (insert r $ insert s $ insert q $ Δ.erase (p ⋏ q)) :=
      (andInversion₂Aux d p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | rfl | hhx) <;> simp[*])
    (or _ _ _ this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm q])
  | _, all Δ r d,           p, q =>
    have : ⊢ᶜ[P] insert (Rew.freel r) (shifts $ insert q $ Δ.erase (p ⋏ q)) :=
      (andInversion₂Aux d (Rew.shiftl p) (Rew.shiftl q)).weakening
        (by simp[shifts_insert, shifts_erase, Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (all _ _ this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm q])
  | _, ex Δ t r d,          p, q =>
    have : ⊢ᶜ[P] insert ([→ t].hom r) (insert q $ Δ.erase (p ⋏ q)) :=
      (andInversion₂Aux d p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (ex _ t r this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm q])
  | _, cut Δ Γ r hr dΔ dΓ,  p, q =>
    have dΔ : ⊢ᶜ[P] (insert r $ insert q $ Δ.erase (p ⋏ q)) :=
      (andInversion₂Aux dΔ p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    have dΓ : ⊢ᶜ[P] (insert (~r) $ insert q $ Γ.erase (p ⋏ q)) :=
      (andInversion₂Aux dΓ p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (cut _ _ r hr dΔ dΓ).cast (by simp[Finset.erase_union])

def andInversion₂ {p q} (d : ⊢ᶜ[P] insert (p ⋏ q) Δ) : ⊢ᶜ[P] insert q Δ := 
  (andInversion₂Aux d p q).weakening (by simp; exact Finset.insert_subset_insert _ (Finset.erase_subset _ _))

def allInversionAux : {Δ : Sequent L} → ⊢ᶜ[P] Δ →
    (p : SyntacticSubFormula L 1) → (t : SyntacticTerm L) → ⊢ᶜ[P] insert ([→ t].hom p) (Δ.erase (∀' p))
  | _, axL Δ r v hpos hneg, p, t => axL _ r v (by simp[hpos]) (by simp[hneg])
  | _, verum Δ h,           p, t => verum _ (by simp[h])
  | _, and Δ r s dr ds,     p, t =>
      have dr : ⊢ᶜ[P] (insert r $ insert ([→ t].hom p) $ Δ.erase (∀' p)) :=
        (allInversionAux dr p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      have ds : ⊢ᶜ[P] (insert s $ insert ([→ t].hom p) $ Δ.erase (∀' p)) :=
        (allInversionAux ds p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      (and _ _ _ dr ds).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm])
  | _, or Δ r s d,          p, t =>
      have : ⊢ᶜ[P] (insert r $ insert s $ insert ([→ t].hom p) $ Δ.erase (∀' p)) :=
        (allInversionAux d p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | rfl | hhx) <;> simp[*])
      (or _ _ _ this).weakening (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm])
  | _, all Δ p' d,          p, t => by
      by_cases e : p' = p
      · simp[e]
        let d' : ⊢ᶜ[P] insert ([→ t].hom p) Δ :=
          (d.rewrite hP (t :>ₙ SubTerm.fvar)).cast
            (by simp[shifts_eq_image, Finset.image_image, Function.comp, e,
                  ←Rew.hom_comp_app, Rew.rewrite_comp_free_eq_substs, Rew.rewrite_comp_shift_eq_id]; )
        have : d'.length = d.length := by simp
        exact (allInversionAux d' p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      · have ne : ∀' p' ≠ ∀' p := by simpa using e
        have : ⊢ᶜ[P] (insert (Rew.freel p') $ shifts $ insert ([→ t].hom p) $ Δ.erase (∀' p)) :=
          (allInversionAux d (Rew.shift.hom p) (Rew.shift t)).weakening (by
            simp[←Rew.hom_comp_app, Rew.shift_comp_substs1, shifts_insert, shifts_erase, Finset.subset_iff];
            rintro x hhx (rfl | hx) <;> simp[*]; exact Or.inr (Or.inr hhx))
        exact (all _ p' this).cast (by simp[Finset.erase_insert_of_ne ne, Finset.Insert.comm])
  | _, ex Δ u q d,          p, t =>
    have : ⊢ᶜ[P] (insert ([→ u].hom q) $ insert ([→ t].hom p) $ Δ.erase (∀' p)) :=
      (allInversionAux d p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    ((ex _ u q this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm]))
  | _, cut Δ Γ r hr dΔ dΓ,  p, t =>
    have dΔ : ⊢ᶜ[P] (insert r $ insert ([→ t].hom p) $ Δ.erase (∀' p)) :=
      (allInversionAux dΔ p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    have dΓ : ⊢ᶜ[P] (insert (~r) $ insert ([→ t].hom p) $ Γ.erase (∀' p)) :=
      (allInversionAux dΓ p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (cut _ _ r hr dΔ dΓ).cast (by simp[Finset.erase_union])
  termination_by allInversionAux _ d _ _ => d.length

def allInversion (d : ⊢ᶜ[P] insert (∀' p) Δ) (t) : ⊢ᶜ[P] insert ([→ t].hom p) Δ :=
  (allInversionAux hP d p t).weakening (by simp; exact Finset.insert_subset_insert _ (Finset.erase_subset _ _))

def allInversionClx {i} (d : ⊢ᶜ[< i] insert (∀' p) Δ) (t) : ⊢ᶜ[< i] insert ([→ t].hom p) Δ :=
  allInversion (by simp) d t

def falsumElimAux : {Δ : Sequent L} → ⊢ᶜ[P] Δ → ⊢ᶜ[P] Δ.erase ⊥
  | _, axL Δ r v hpos hneg => axL _ r v (by simp[hpos]) (by simp[hneg])
  | _, verum Δ h           => verum _ (by simp[h])
  | _, and Δ p q dp dq     =>
    have dp : ⊢ᶜ[P] insert p (Δ.erase ⊥) := dp.falsumElimAux.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    have dq : ⊢ᶜ[P] insert q (Δ.erase ⊥) := dq.falsumElimAux.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (and _ p q dp dq).cast (by simp[Finset.erase_insert_of_ne])
  | _, or Δ p q d          =>
    have : ⊢ᶜ[P] (insert p $ insert q $ Δ.erase ⊥) :=
      d.falsumElimAux.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (or _ _ _ this).cast (by simp[Finset.erase_insert_of_ne])
  | _, all Δ p d           =>
    have : ⊢ᶜ[P] (insert (Rew.freel p) (shifts $ Δ.erase ⊥)) :=
      d.falsumElimAux.weakening
        (by {simp[Finset.subset_iff, shifts_eq_image]; rintro x hx (rfl | ⟨y, hy, rfl⟩); { exact Or.inl rfl }; { exact Or.inr ⟨y, ⟨by rintro rfl; contradiction, hy⟩, rfl⟩ } } )
    (all _ _ this).cast (by simp[Finset.erase_insert_of_ne])
  | _, ex Δ t p d          =>
    have : ⊢ᶜ[P] (insert ([→ t].hom p) $ Δ.erase ⊥) := d.falsumElimAux.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (ex _ t p this).cast (by simp[Finset.erase_insert_of_ne])
  | _, cut Δ Γ p hp dΔ dΓ  =>
    have dΔ : ⊢ᶜ[P] (insert p $ Δ.erase ⊥) := dΔ.falsumElimAux.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    have dΓ : ⊢ᶜ[P] (insert (~p) $ Γ.erase ⊥) := dΓ.falsumElimAux.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (cut _ _ p hp dΔ dΓ).cast (by simp[Finset.erase_union])

def falsumElim (d : ⊢ᶜ[P] insert ⊥ Δ) : ⊢ᶜ[P] Δ := d.falsumElimAux.weakening (by simp; exact Finset.erase_subset _ _)

def reductionAux {i} : {Δ : Sequent L} →
    ⊢ᶜ[< i] Δ → {p : SyntacticFormula L} → p.isVType = true → p.complexity ≤ i →
    {Γ : Sequent L} → ⊢ᶜ[< i] insert (~p) Γ → ⊢ᶜ[< i] Δ.erase p ∪ Γ
  | _, axL Δ r v hpos hneg,  p, _,  _,  Γ, dΓ => by
    by_cases e₁ : p = rel r v
    · exact dΓ.weakening (by simp[e₁, hpos, hneg, Finset.subset_iff]; intro x hx; exact Or.inr hx) 
    · by_cases e₂ : p = nrel r v
      · exact dΓ.weakening (by simp[e₂, hpos, hneg, Finset.subset_iff]; intro x hx; exact Or.inr hx)
      · exact axL _ r v (by simp[Ne.symm e₁, hpos]) (by simp[Ne.symm e₂, hneg])
  | _, verum Δ h,            p, _,  _,  Γ, dΓ => by
    by_cases e : p = ⊤
    · have : ⊢ᶜ[< i] insert ⊥ Γ := dΓ.cast (by simp[e])
      have : ⊢ᶜ[< i] Γ := this.falsumElim
      exact this.weakening (Finset.subset_union_right _ _)
    · exact verum _ (by simp[Ne.symm e, h])
  | _, and Δ r s dr ds,     p, tp, hp, Γ, dΓ => by
    have e : p ≠ r ⋏ s := ne_and_of_isVType tp
    have dr : ⊢ᶜ[< i] insert r (Δ.erase p ∪ Γ) :=
      (reductionAux dr tp hp dΓ).weakening (by simp[Finset.subset_iff]; rintro x (⟨hxp, (rfl | hhxp)⟩ | hhx) <;> simp[*])
    have ds : ⊢ᶜ[< i] insert s (Δ.erase p ∪ Γ) :=
      (reductionAux ds tp hp dΓ).weakening (by simp[Finset.subset_iff]; rintro x (⟨hxp, (rfl | hhxp)⟩ | hhx) <;> simp[*])
    exact (and _ _ _ dr ds).cast (by simp[Finset.erase_insert_of_ne (Ne.symm e)])
  | _, all Δ q d,            p, tp, hp, Γ, dΓ => by
    have e : p ≠ ∀' q := ne_all_of_isVType tp
    have : ⊢ᶜ[< i] (insert (~Rew.shiftl p) (shifts Γ)) := (dΓ.shift (by simp)).cast (by simp[shifts_insert])
    have : ⊢ᶜ[< i] insert (Rew.freel q) (shifts $ Δ.erase p ∪ Γ) :=
      (reductionAux d (by simp[tp]) (by simp[hp]) this).weakening
        (by simp[Finset.subset_iff]; rintro x (⟨hx, (rfl | hhx)⟩ | hhx);
            · simp[*]
            · simp[shifts_eq_image] at hhx ⊢; rcases hhx with ⟨y, hy, rfl⟩; exact Or.inr ⟨y, Or.inl ⟨by rintro rfl; contradiction, hy⟩, rfl⟩
            · simp[shifts_eq_image] at hhx ⊢; rcases hhx with ⟨y, hy, rfl⟩; exact Or.inr ⟨y, Or.inr hy, rfl⟩)
    have : ⊢ᶜ[< i] insert (∀' q) (Δ.erase p ∪ Γ) := all _ _ this
    exact this.cast (by simp[Finset.erase_insert_of_ne (Ne.symm e)])
  | _, or Δ r s d,           p, tp, hp, Γ, dΓ => by
    by_cases e : p = r ⋎ s
    · have hrs : r.complexity < i ∧ s.complexity < i := by simpa[e, Nat.succ_le] using hp
      have d₁ : ⊢ᶜ[< i] (insert r $ insert s $ (Δ.erase (r ⋎ s)) ∪ Γ) :=
        (reductionAux d tp hp dΓ).cast (by simp[e, Finset.erase_insert_of_ne])
      have dΓ₁ : ⊢ᶜ[< i] insert (~r) Γ := (dΓ.cast (by simp[e])).andInversion₁ (q := ~s)
      have dΓ₂ : ⊢ᶜ[< i] insert (~s) Γ := (dΓ.cast (by simp[e])).andInversion₂ (p := ~r)
      have d₃ : ⊢ᶜ[< i] (insert s $ (Δ.erase (r ⋎ s)) ∪ Γ) :=
        (cut (insert s $ (Δ.erase (r ⋎ s)) ∪ Γ) Γ r hrs.1 d₁ dΓ₁).cast (by simp)
      have : ⊢ᶜ[< i] (Δ.erase (r ⋎ s)) ∪ Γ :=
        (cut ((Δ.erase (r ⋎ s)) ∪ Γ) Γ s hrs.2 d₃ dΓ₂).cast (by simp)
      exact this.cast (by simp[e])
    · have : ⊢ᶜ[< i] (insert r $ insert s $ (Δ.erase p) ∪ Γ) :=
        (reductionAux d tp hp dΓ).weakening (by simp[Finset.subset_iff]; rintro x (⟨hx, (rfl | rfl | hhx)⟩ | hx) <;> simp[*])
      have : ⊢ᶜ[< i] (insert (r ⋎ s) $ (Δ.erase p) ∪ Γ) := or _ _ _ this
      exact this.cast (by simp[e, Finset.erase_insert_of_ne (Ne.symm e)])
  | _, ex Δ t q d₁,          p, tp, hp, Γ, d₂ => by
    by_cases e : p = ∃' q
    · have d₁₁ : ⊢ᶜ[< i] (insert ([→ t].hom q) $ (Δ.erase (∃' q) ∪ Γ)) :=
        (reductionAux d₁ tp hp d₂).cast (by simp[e, Finset.erase_insert_of_ne])
      have d₂₁ : ⊢ᶜ[< i] (insert (~[→ t].hom q) Γ) :=
        by simpa using allInversionClx (p := ~q) (by simpa[e] using d₂) t
      have : ⊢ᶜ[< i] Δ.erase (∃' q) ∪ Γ :=
        (cut (Δ.erase (∃' q) ∪ Γ) Γ ([→ t].hom q)
          (by simp; exact Nat.succ_le.mp (by simpa[e] using hp)) d₁₁ d₂₁).cast (by simp)
      exact this.cast (by simp[e])
    · have : ⊢ᶜ[< i] (insert ([→ t].hom q) $ Δ.erase p ∪ Γ) :=
        (reductionAux d₁ tp hp d₂).weakening (by simp[Finset.subset_iff]; rintro x (⟨hxp, (rfl | hhxp)⟩ | hhx) <;> simp[*])
      have : ⊢ᶜ[< i] (insert (∃' q) $ Δ.erase p ∪ Γ) := ex _ t q this
      exact this.cast (by simp[Finset.erase_insert_of_ne (Ne.symm e)])
  | _, cut Δ₁ Δ₂ r hr d₁ d₂, p, tp, hp, Γ, dΓ =>
    have d₁₁ : ⊢ᶜ[< i] (insert r $ Δ₁.erase p ∪ Γ) :=
      (reductionAux d₁ tp hp dΓ).weakening (by simp[Finset.subset_iff]; rintro x (⟨hx, (rfl | hhx)⟩ | hx) <;> simp[*])
    have d₂₁ : ⊢ᶜ[< i] (insert (~r) $ Δ₂.erase p ∪ Γ) :=
      (reductionAux d₂ tp hp dΓ).weakening (by simp[Finset.subset_iff]; rintro x (⟨hx, (rfl | hhx)⟩ | hx) <;> simp[*])
    have : ⊢ᶜ[< i] (Δ₁ ∪ Δ₂).erase p ∪ Γ :=
      (cut (Δ₁.erase p ∪ Γ) (Δ₂.erase p ∪ Γ) r hr d₁₁ d₂₁).cast (by rw[←Finset.union_union_distrib_right, Finset.erase_union])
    this

def reduction {i} {p} (hp : p.complexity ≤ i) : ⊢ᶜ[< i] insert p Δ → ⊢ᶜ[< i] insert (~p) Γ → ⊢ᶜ[< i] Δ ∪ Γ := fun dΔ dΓ => by
  cases tp : p.isVType
  · have : (~p).isVType = true := isVType_neg_true_of_eq_false tp
    exact (reductionAux dΓ this (by simp[hp]) (Γ := Δ) (dΔ.cast (by simp))).weakening
      (by simp[Finset.union_comm]; exact Finset.union_subset_union (by rfl) (Finset.erase_subset _ _))
  · exact (reductionAux dΔ tp hp dΓ).weakening (Finset.union_subset_union (by simp; exact Finset.erase_subset _ _) (by rfl))

def elimination {i} : {Δ : Sequent L} → ⊢ᶜ[< i + 1] Δ → ⊢ᶜ[< i] Δ
  | _, axL Δ r v hpos hneg => axL Δ r v hpos hneg
  | _, verum Δ h           => verum Δ h
  | _, and Δ p q dp dq     => and Δ p q dp.elimination dq.elimination
  | _, or Δ p q d          => or Δ p q d.elimination
  | _, all Δ p d           => all Δ p d.elimination
  | _, ex Δ t p d          => ex Δ t p d.elimination
  | _, cut _ _ _ hp dΔ dΓ  => reduction (Nat.lt_add_one_iff.mp hp) dΔ.elimination dΓ.elimination

def hauptsatzClx : {i : ℕ} → ⊢ᶜ[< i] Δ → ⊢ᵀ Δ
  | 0,     d => d.cutWeakening (by simp)
  | i + 1, d => d.elimination.hauptsatzClx

def toClx : {Δ : Sequent L} → ⊢ᶜ Δ → (i : ℕ) × ⊢ᶜ[< i] Δ
  | _, axL Δ r v hpos hneg => ⟨0, axL Δ r v hpos hneg⟩
  | _, verum Δ h           => ⟨0, verum Δ h⟩
  | _, and Δ p q dp dq     => ⟨max dp.toClx.1 dq.toClx.1, and Δ p q (dp.toClx.2.ofLe (by simp)) (dq.toClx.2.ofLe (by simp))⟩
  | _, or Δ p q d          => ⟨d.toClx.1, or Δ p q d.toClx.2⟩
  | _, all Δ p d           => ⟨d.toClx.1, all Δ p d.toClx.2⟩
  | _, ex Δ t p d          => ⟨d.toClx.1, ex Δ t p d.toClx.2⟩
  | _, cut Δ Γ p _ dΔ dΓ   =>
    ⟨max (max dΔ.toClx.1 dΓ.toClx.1) p.complexity.succ, cut Δ Γ  p (by simp) (dΔ.toClx.2.ofLe (by simp)) (dΓ.toClx.2.ofLe (by simp))⟩

def hauptsatz : ⊢ᶜ Δ → ⊢ᵀ Δ := fun d => hauptsatzClx d.toClx.2

end DerivationCutRestricted

end FirstOrder

end LO
