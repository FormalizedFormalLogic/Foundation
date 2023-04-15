import Logic.Predicate.FirstOrder.Calculus

universe u v

namespace FirstOrder
open SubFormula

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

namespace Derivation

variable {Δ Δ₁ Δ₂ Γ : Sequent L}

def andInversion₁Aux : {Δ : Sequent L} → (d : ⊢ᵀ Δ) → (p q : SyntacticFormula L) → ⊢ᵀ insert p (Δ.erase (p ⋏ q))
  | _, axL Δ r v hpos hneg, p, q => axL _ r v (by simp[hpos]) (by simp[hneg])
  | _, verum Δ h,           p, q => verum _ (by simp[h])
  | _, and Δ p' q' dp dq,   p, q => by
      by_cases e : p' = p ∧ q' = q
      · simp[e]; exact (andInversion₁Aux dp p q).weakening
          (by simp[Finset.subset_iff]; rintro x hx (rfl | hΔ); { exact Or.inl e.1 }; { exact Or.inr ⟨hx, hΔ⟩ })
      · have ne : p' ⋏ q' ≠ p ⋏ q := by simp[e]
        have dp : ⊢ᵀ (insert p' $ insert p (Δ.erase (p ⋏ q))) :=
          (andInversion₁Aux dp p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
        have dq : ⊢ᵀ (insert q' $ insert p (Δ.erase (p ⋏ q))) :=
          (andInversion₁Aux dq p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
        exact (and _ _ _ dp dq).cast (by simp[Finset.erase_insert_of_ne ne, Finset.Insert.comm p])
  | _, or Δ r s d,          p, q => by
      have : ⊢ᵀ (insert r $ insert s $ insert p $ Δ.erase (p ⋏ q)) :=
        (andInversion₁Aux d p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | rfl | hhx) <;> simp[*])
      exact (or _ _ _ this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm p])
  | _, all Δ r d,           p, q => by
      have : ⊢ᵀ insert (free r) (shifts $ insert p $ Δ.erase (p ⋏ q)) :=
        (andInversion₁Aux d (shift p) (shift q)).weakening
          (by simp[shifts_insert, shifts_erase, Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      exact (all _ _ this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm p])
  | _, ex Δ t r d,          p, q => by
      have : ⊢ᵀ insert (subst t r) (insert p $ Δ.erase (p ⋏ q)) := (andInversion₁Aux d p q).weakening
        (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      exact (ex _ t r this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm p])

def andInversion₁ {p q} (d : ⊢ᵀ insert (p ⋏ q) Δ) : ⊢ᵀ insert p Δ := 
  (andInversion₁Aux d p q).weakening (by simp; exact Finset.insert_subset_insert _ (Finset.erase_subset _ _))

def andInversion₂Aux : {Δ : Sequent L} → (d : ⊢ᵀ Δ) → (p q : SyntacticFormula L) → ⊢ᵀ insert q (Δ.erase (p ⋏ q))
  | _, axL Δ r v hpos hneg, p, q => axL _ r v (by simp[hpos]) (by simp[hneg])
  | _, verum Δ h,           p, q => verum _ (by simp[h])
  | _, and Δ p' q' dp dq,   p, q => by
      by_cases e : p' = p ∧ q' = q
      · simp[e]; exact (andInversion₂Aux dq p q).weakening
          (by simp[Finset.subset_iff]; rintro x hx (rfl | hΔ); { exact Or.inl e.2 }; { exact Or.inr ⟨hx, hΔ⟩ })
      · have ne : p' ⋏ q' ≠ p ⋏ q := by simp[e]
        have dp : ⊢ᵀ (insert p' $ insert q (Δ.erase (p ⋏ q))) :=
          (andInversion₂Aux dp p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
        have dq : ⊢ᵀ (insert q' $ insert q (Δ.erase (p ⋏ q))) :=
          (andInversion₂Aux dq p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
        exact (and _ _ _ dp dq).cast (by simp[Finset.erase_insert_of_ne ne, Finset.Insert.comm q])
  | _, or Δ r s d,          p, q => by
      have : ⊢ᵀ (insert r $ insert s $ insert q $ Δ.erase (p ⋏ q)) :=
        (andInversion₂Aux d p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | rfl | hhx) <;> simp[*])
      exact (or _ _ _ this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm q])
  | _, all Δ r d,           p, q => by
      have : ⊢ᵀ insert (free r) (shifts $ insert q $ Δ.erase (p ⋏ q)) :=
        (andInversion₂Aux d (shift p) (shift q)).weakening
          (by simp[shifts_insert, shifts_erase, Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      exact (all _ _ this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm q])
  | _, ex Δ t r d,          p, q => by
      have : ⊢ᵀ insert (subst t r) (insert q $ Δ.erase (p ⋏ q)) :=
        (andInversion₂Aux d p q).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      exact (ex _ t r this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm q])

def andInversion₂ {p q} (d : ⊢ᵀ insert (p ⋏ q) Δ) : ⊢ᵀ insert q Δ := 
  (andInversion₂Aux d p q).weakening (by simp; exact Finset.insert_subset_insert _ (Finset.erase_subset _ _))

def allInversionAux : {Δ : Sequent L} → (d : ⊢ᵀ Δ) →
    (p : SyntacticSubFormula L 1) → (t : SyntacticTerm L) → ⊢ᵀ insert (subst t p) (Δ.erase (∀' p))
  | _, axL Δ r v hpos hneg, p, t => axL _ r v (by simp[hpos]) (by simp[hneg])
  | _, verum Δ h,           p, t => verum _ (by simp[h])
  | _, and Δ r s dr ds,     p, t => by
      have dr : ⊢ᵀ (insert r $ insert (subst t p) $ Δ.erase (∀' p)) :=
        (allInversionAux dr p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      have ds : ⊢ᵀ (insert s $ insert (subst t p) $ Δ.erase (∀' p)) :=
        (allInversionAux ds p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      exact (and _ _ _ dr ds).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm])
  | _, or Δ r s d,          p, t => by
      have : ⊢ᵀ (insert r $ insert s $ insert (subst t p) $ Δ.erase (∀' p)) :=
        (allInversionAux d p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | rfl | hhx) <;> simp[*])
      exact (or _ _ _ this).weakening (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm])
  | _, all Δ p' d,          p, t => by
      by_cases e : p' = p
      · simp[e]
        let d' : ⊢ᵀ insert (subst t p) Δ :=
          (d.onBind (t :>ₙ SubTerm.fvar)).cast (by simp[bind₀_free_eq_subst, bind₀_shift_eq_self, shifts_eq_image, Finset.image_image, Function.comp, e])
        have : d'.length = d.length := by simp
        exact (allInversionAux d' p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
      · have ne : ∀' p' ≠ ∀' p := by simpa using e
        have : ⊢ᵀ (insert (free p') $ shifts $ insert (subst t p) $ Δ.erase (∀' p)) :=
          (allInversionAux d (shift p) t.shift).weakening (by
            simp[shift_subst, shifts_insert, shifts_erase, Finset.subset_iff]; rintro x hx (rfl | hx) <;> simp[*])
        exact (all _ p' this).cast (by simp[Finset.erase_insert_of_ne ne, Finset.Insert.comm])
  | _, ex Δ u q d,          p, t => by
    have : ⊢ᵀ (insert (subst u q) $ insert (subst t p) $ Δ.erase (∀' p)) :=
      (allInversionAux d p t).weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    exact ((ex _ u q this).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm]))
  termination_by allInversionAux _ d _ _ => d.length

def allInversion (d : ⊢ᵀ insert (∀' p) Δ) (t) : ⊢ᵀ insert (subst t p) Δ :=
  (allInversionAux d p t).weakening (by simp; exact Finset.insert_subset_insert _ (Finset.erase_subset _ _))

end Derivation

end FirstOrder
