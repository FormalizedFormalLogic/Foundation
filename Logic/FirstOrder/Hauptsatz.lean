import Logic.FirstOrder.Basic

namespace LO

namespace FirstOrder

open Subformula

variable {L : Language.{u}} [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)]

namespace Subformula

def isVType : {n : ℕ} → Subformula L μ n → Bool
  | _, rel _ _  => true
  | _, nrel _ _ => true
  | _, ⊤        => true
  | _, ⊥        => true
  | _, _ ⋏ _    => false
  | _, _ ⋎ _    => true
  | _, ∀' _     => false
  | _, ∃' _     => true

lemma ne_and_of_isVType {p q r : Subformula L μ n} (h : isVType p) : p ≠ q ⋏ r := by rintro rfl; simp[isVType] at h

lemma ne_all_of_isVType {p : Subformula L μ n} {q} (h : isVType p) : p ≠ ∀' q := by rintro rfl; simp[isVType] at h

@[simp] lemma isVType_shift_iff {p : SyntacticSubformula L n} : isVType (Rew.shift.hom p) = isVType p := by
  induction p using rec' <;> simp[Rew.rel, Rew.nrel, isVType]

lemma isVType_neg_true_of_eq_false {p : SyntacticSubformula L n} : isVType p = false → isVType (~p) = true := by
  induction p using rec' <;> simp[Rew.rel, Rew.nrel, isVType]

end Subformula

namespace DerivationCR

variable {P : SyntacticFormula L → Prop} (hP : ∀ f p, P p → P ((Rew.rewrite f).hom p)) {Δ Δ₁ Δ₂ Γ : Sequent L}

def andInversion₁Aux : {Δ : Sequent L} → (d : ⊢ᶜ[P] Δ) → (p q : SyntacticFormula L) → ⊢ᶜ[P] p :: Δ.remove (p ⋏ q)
  | _, @axL _ _ Δ _ r v,       p, q => axL' r v (by simp[List.mem_remove_iff]) (by simp[List.mem_remove_iff])
  | _, @verum _ _ Δ,           p, q => verum' (by simp[List.mem_remove_iff])
  | _, @and _ _ Δ p' q' dp dq, p, q => by
    by_cases e : p = p' ∧ q = q'
    · exact (andInversion₁Aux dp p q).weakening
        (by rcases e with ⟨rfl, rfl⟩
            simp[List.subset_def, List.mem_remove_iff]
            intros; simp[*])
    · have ne : p ⋏ q ≠ p' ⋏ q' := by simpa[-not_and] using e
      have dp : ⊢ᶜ[P] (p' :: p :: (Δ.remove (p ⋏ q))) :=
        (andInversion₁Aux dp p q).weakening (by
          simp[List.subset_def, List.mem_remove_iff]
          intros; simp[*])
      have dq : ⊢ᶜ[P] (q' :: p :: (Δ.remove (p ⋏ q))) :=
        (andInversion₁Aux dq p q).weakening (by
          simp[List.subset_def, List.mem_remove_iff]
          intros; simp[*])
      exact (and dp dq).weakening (by
        simp[List.subset_def, List.mem_remove_iff, -not_and]
        constructor
        · right; simpa using Ne.symm ne
        · intros; simp[*])
  | _, @or _ _ Δ r s d,        p, q =>
    have : ⊢ᶜ[P] (r :: s :: p :: Δ.remove (p ⋏ q)) :=
      (andInversion₁Aux d p q).weakening (by
        simp[List.subset_def, List.mem_remove_iff]
        intros; simp[*])
    (or this).wk (by
      simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, @all _ _ Δ r d,         p, q =>
    have : ⊢ᶜ[P] Rew.free.hom r :: (shifts $ p :: Δ.remove (p ⋏ q)) :=
      (andInversion₁Aux d (Rew.shift.hom p) (Rew.shift.hom q)).weakening (by
        simp[shifts]
        exact (List.Perm.subset_congr_right (List.Perm.swap _ _ _)).mp
          (List.subset_cons_of_subset _ $
            subset_trans (List.remove_cons_subset_cons_remove _ _ _) $
              List.cons_subset_cons _ $ subset_trans (by simp) (List.remove_map_substet_map_remove _ _ _)))
    (all this).wk ((List.Perm.subset_congr_left (List.Perm.swap _ _ _)).mp $
      List.cons_subset_cons _ $ by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, @ex _ _ Δ r t d,        p, q =>
    have : ⊢ᶜ[P] r/[t] :: p :: Δ.remove (p ⋏ q) :=
      (andInversion₁Aux d p q).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (ex t this).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, @wk _ _ Δ Γ d ss,       p, q =>
    (andInversion₁Aux d p q).weakening
      (List.cons_subset_cons _ $ List.remove_subset_remove _ ss)
  | _, @cut _ _ Δ r hr d dn,   p, q =>
    have d : ⊢ᶜ[P] r :: p :: Δ.remove (p ⋏ q) :=
      (andInversion₁Aux d p q).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have dn : ⊢ᶜ[P] (~r) :: p :: Δ.remove (p ⋏ q) :=
      (andInversion₁Aux dn p q).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    cut hr d dn

def andInversion₁ {p q} (d : ⊢ᶜ[P] p ⋏ q :: Δ) : ⊢ᶜ[P] p :: Δ :=
  (andInversion₁Aux d p q).weakening (by simp[List.remove]; exact List.subset_cons_of_subset _ (List.remove_subset _ _))

def andInversion₂Aux : {Δ : Sequent L} → (d : ⊢ᶜ[P] Δ) → (p q : SyntacticFormula L) → ⊢ᶜ[P] q :: Δ.remove (p ⋏ q)
  | _, @axL _ _ Δ _ r v,       p, q => axL' r v (by simp[List.mem_remove_iff]) (by simp[List.mem_remove_iff])
  | _, @verum _ _ Δ,           p, q => verum' (by simp[List.mem_remove_iff])
  | _, @and _ _ Δ p' q' dp dq, p, q => by
    by_cases e : p = p' ∧ q = q'
    · exact (andInversion₂Aux dq p q).weakening
        (by rcases e with ⟨rfl, rfl⟩
            simp[List.subset_def, List.mem_remove_iff]
            intros; simp[*])
    · have ne : p ⋏ q ≠ p' ⋏ q' := by simpa[-not_and] using e
      have dp : ⊢ᶜ[P] (p' :: q :: (Δ.remove (p ⋏ q))) :=
        (andInversion₂Aux dp p q).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      have dq : ⊢ᶜ[P] (q' :: q :: (Δ.remove (p ⋏ q))) :=
        (andInversion₂Aux dq p q).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      exact (and dp dq).weakening (by
        simp[List.subset_def, List.mem_remove_iff, -not_and]
        constructor
        · right; simpa using Ne.symm ne
        · intros; simp[*])
  | _, @or _ _ Δ r s d,        p, q =>
    have : ⊢ᶜ[P] (r :: s :: q :: Δ.remove (p ⋏ q)) :=
      (andInversion₂Aux d p q).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (or this).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, @all _ _ Δ r d,         p, q =>
    have : ⊢ᶜ[P] Rew.free.hom r :: (shifts $ q :: Δ.remove (p ⋏ q)) :=
      (andInversion₂Aux d (Rew.shift.hom p) (Rew.shift.hom q)).weakening (by
        simp[shifts]
        exact (List.Perm.subset_congr_right (List.Perm.swap _ _ _)).mp
          (List.subset_cons_of_subset _ $
            subset_trans (List.remove_cons_subset_cons_remove _ _ _) $
              List.cons_subset_cons _ $ subset_trans (by simp) (List.remove_map_substet_map_remove _ _ _)))
    (all this).wk ((List.Perm.subset_congr_left (List.Perm.swap _ _ _)).mp $
      List.cons_subset_cons _ $ by
        simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, @ex _ _ Δ r t d,        p, q =>
    have : ⊢ᶜ[P] r/[t] :: q :: Δ.remove (p ⋏ q) :=
      (andInversion₂Aux d p q).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (ex t this).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, @wk _ _ Δ Γ d ss,       p, q =>
    (andInversion₂Aux d p q).weakening
      (List.cons_subset_cons _ $ List.remove_subset_remove _ ss)
  | _, @cut _ _ Δ r hr d dn,   p, q =>
    have d : ⊢ᶜ[P] r :: q :: Δ.remove (p ⋏ q) :=
      (andInversion₂Aux d p q).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have dn : ⊢ᶜ[P] (~r) :: q :: Δ.remove (p ⋏ q) :=
      (andInversion₂Aux dn p q).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    cut hr d dn

def andInversion₂ {p q} (d : ⊢ᶜ[P] p ⋏ q :: Δ) : ⊢ᶜ[P] q :: Δ :=
  (andInversion₂Aux d p q).weakening (by simp[List.remove]; exact List.subset_cons_of_subset _ (List.remove_subset _ _))

def allInversionAux : {Δ : Sequent L} → ⊢ᶜ[P] Δ →
    (p : SyntacticSubformula L 1) → (t : SyntacticTerm L) → ⊢ᶜ[P] p/[t] :: Δ.remove (∀' p)
  | _, @axL _ _ Δ _ r v,     p, t => axL' r v (by simp[List.mem_remove_iff]) (by simp[List.mem_remove_iff])
  | _, @verum _ _ Δ,         p, t => verum' (by simp[List.mem_remove_iff])
  | _, @and _ _ Δ r s dr ds, p, t =>
      have dr : ⊢ᶜ[P] r :: p/[t] :: Δ.remove (∀' p) :=
        (allInversionAux dr p t).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      have ds : ⊢ᶜ[P] (s :: p/[t] :: Δ.remove (∀' p)) :=
        (allInversionAux ds p t).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      (and dr ds).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, @or _ _ Δ r s d,      p, t =>
      have : ⊢ᶜ[P] (r :: s :: p/[t] :: Δ.remove (∀' p)) :=
        (allInversionAux d p t).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      (or this).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, @all _ _ Δ p' d,      p, t => by
      by_cases e : p' = p
      · simp[e]
        let d' : ⊢ᶜ[P] p/[t] :: Δ :=
          (d.rewrite hP (t :>ₙ Subterm.fvar)).cast
            (by simp[e, shifts, Function.comp, ←Rew.hom_comp_app,
                  Rew.rewrite_comp_free_eq_substs, Rew.rewrite_comp_shift_eq_id])
        have : d'.length = d.length := by simp
        exact (allInversionAux d' p t).weakening (by
          rw[List.remove_cons_of_ne]; simp; exact Subformula.ne_of_ne_complexity (by simp))
      · have : ⊢ᶜ[P] (Rew.free.hom p' :: shifts (p/[t] :: Δ.remove (∀' p))) :=
          (allInversionAux d (Rew.shift.hom p) (Rew.shift t)).weakening
          (by simp[shifts, ←Rew.hom_comp_app, Rew.shift_comp_substs1]
              exact subset_trans (List.remove_cons_subset_cons_remove _ _ _)
                (List.cons_subset_cons _ $ List.subset_cons_of_subset _ $
                subset_trans (by simp) $ List.remove_map_substet_map_remove _ _ _))
        exact (all this).wk (by simp[List.subset_def, List.mem_remove_iff, e]; intros; simp[*])
  | _, @ex _ _ Δ q u d,      p, t =>
    have : ⊢ᶜ[P] q/[u] :: p/[t] :: Δ.remove (∀' p) :=
      (allInversionAux d p t).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (ex u this).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, @wk _ _ Δ Γ d ss,  p, t =>
    (allInversionAux d p t).weakening
      (List.cons_subset_cons _ $ List.remove_subset_remove _ ss)
  | _, @cut _ _ Δ r hr d dn, p, t =>
    have d : ⊢ᶜ[P] r :: p/[t] :: Δ.remove (∀' p) :=
      (allInversionAux d p t).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have dn : ⊢ᶜ[P] ((~r) :: p/[t] :: Δ.remove (∀' p)) :=
      (allInversionAux dn p t).weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    cut hr d dn
  termination_by allInversionAux _ d _ _ => d.length

def allInversion (d : ⊢ᶜ[P] (∀' p) :: Δ) (t) : ⊢ᶜ[P] p/[t] :: Δ :=
  (allInversionAux hP d p t).weakening (by simp; exact List.subset_cons_of_subset _ (List.remove_subset _ _))

def allInversionClx {i} (d : ⊢ᶜ[< i] (∀' p) :: Δ) (t) : ⊢ᶜ[< i] p/[t] :: Δ :=
  allInversion (by simp) d t

def falsumElimAux : {Δ : Sequent L} → ⊢ᶜ[P] Δ → ⊢ᶜ[P] Δ.remove ⊥
  | _, @axL _ _ Δ _ r v     => axL' r v (by simp[List.mem_remove_iff]) (by simp[List.mem_remove_iff])
  | _, @verum _ _ Δ         => verum' (by simp[List.mem_remove_iff])
  | _, @and _ _ Δ p q dp dq =>
    have dp : ⊢ᶜ[P] p :: (Δ.remove ⊥) := dp.falsumElimAux.weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have dq : ⊢ᶜ[P] q :: (Δ.remove ⊥) := dq.falsumElimAux.weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (and dp dq).cast (by rw[List.remove_cons_of_ne]; simp)
  | _, @or _ _ Δ p q d      =>
    have : ⊢ᶜ[P] p :: q :: Δ.remove ⊥ :=
      d.falsumElimAux.weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (or this).cast (by rw[List.remove_cons_of_ne]; simp)
  | _, @all _ _ Δ p d       =>
    have : ⊢ᶜ[P] Rew.free.hom p :: (shifts $ Δ.remove ⊥) :=
      d.falsumElimAux.weakening
        (subset_trans (List.remove_cons_subset_cons_remove _ _ _) $ List.cons_subset_cons _ $
          subset_trans (by simp[shifts]) $ List.remove_map_substet_map_remove _ _ _)
    (all this).cast (by rw[List.remove_cons_of_ne]; simp)
  | _, @ex _ _ Δ p t d      =>
    have : ⊢ᶜ[P] p/[t] :: Δ.remove ⊥ := d.falsumElimAux.weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (ex t this).cast (by rw[List.remove_cons_of_ne]; simp)
  | _, @wk _ _ Δ Γ d ss     => d.falsumElimAux.weakening (List.remove_subset_remove _ ss)
  | _, @cut _ _ Δ p hp d dn =>
    have d : ⊢ᶜ[P] p :: Δ.remove ⊥ := d.falsumElimAux.weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have dn : ⊢ᶜ[P] (~p) :: Δ.remove ⊥ := dn.falsumElimAux.weakening (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    cut hp d dn

def falsumElim (d : ⊢ᶜ[P] ⊥ :: Δ) : ⊢ᶜ[P] Δ := d.falsumElimAux.weakening (by simp; exact List.remove_subset _ _)

def reductionAux {i} : {Δ : Sequent L} →
    ⊢ᶜ[< i] Δ → {p : SyntacticFormula L} → p.isVType = true → p.complexity ≤ i →
    {Γ : Sequent L} → ⊢ᶜ[< i] (~p) :: Γ → ⊢ᶜ[< i] Δ.remove p ++ Γ
  | _, @axL _ _ Δ _ r v,  p, _,  _,  Γ, dΓ => by
    by_cases e₁ : p = rel r v
    · exact dΓ.weakening (by simp[e₁, List.mem_remove_iff])
    · by_cases e₂ : p = nrel r v
      · exact dΓ.weakening (by simp[e₂, List.mem_remove_iff])
      · exact axL' r v (by simp[Ne.symm e₁, List.mem_remove_iff]) (by simp[Ne.symm e₂, List.mem_remove_iff])
  | _, @verum _ _ Δ,            p, _,  _,  Γ, dΓ => by
    by_cases e : p = ⊤
    · have : ⊢ᶜ[< i] ⊥ :: Γ := dΓ.cast (by simp[e])
      have : ⊢ᶜ[< i] Γ := this.falsumElim
      exact this.weakening (by simp)
    · exact verum' (by simp[List.mem_remove_iff, Ne.symm e])
  | _, @and _ _ Δ r s dr ds,     p, tp, hp, Γ, dΓ => by
    have e : p ≠ r ⋏ s := ne_and_of_isVType tp
    have dr : ⊢ᶜ[< i] r :: (Δ.remove p ++ Γ) :=
      (reductionAux dr tp hp dΓ).weakening (by
        rw[←List.cons_append]
        apply List.append_subset_append
        simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have ds : ⊢ᶜ[< i] s :: (Δ.remove p ++ Γ) :=
      (reductionAux ds tp hp dΓ).weakening (by
        rw[←List.cons_append]
        apply List.append_subset_append
        simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    exact (and dr ds).cast (by rw[List.remove_cons_of_ne _ (Ne.symm e), List.cons_append])
  | _, @all _ _ Δ q d,            p, tp, hp, Γ, dΓ => by
    have e : p ≠ ∀' q := ne_all_of_isVType tp
    have : ⊢ᶜ[< i] ~Rew.shift.hom p :: shifts Γ := (dΓ.shift (by simp)).cast (by simp[shifts_cons])
    have : ⊢ᶜ[< i] Rew.free.hom q :: shifts (Δ.remove p ++ Γ) :=
      (reductionAux d (by simp[tp]) (by simp[hp]) this).weakening
        (by simp[shifts]
            constructor
            · exact subset_trans (List.remove_cons_subset_cons_remove _ _ _)
                (List.cons_subset_cons _ $
                  List.subset_append_of_subset_left _ $ List.remove_map_substet_map_remove _ _ _)
            · rw[←List.cons_append]
              exact List.subset_append_right _ _)
    have : ⊢ᶜ[< i] (∀' q) :: (Δ.remove p ++ Γ) := all this
    exact this.cast (by rw[List.remove_cons_of_ne _ (Ne.symm e), List.cons_append])
  | _, @or _ _ Δ r s d,           p, tp, hp, Γ, dΓ => by
    by_cases e : p = r ⋎ s
    · have hrs : r.complexity < i ∧ s.complexity < i := by simpa[e, Nat.succ_le] using hp
      have d₁  : ⊢ᶜ[< i] r :: s :: Δ.remove (r ⋎ s) ++ Γ :=
        (reductionAux d tp hp dΓ).cast (by
          rw[e, List.remove_cons_of_ne _ (show r ≠ r ⋎ s from (Subformula.ne_of_ne_complexity $ by simp)),
            List.remove_cons_of_ne _ (show s ≠ r ⋎ s from (Subformula.ne_of_ne_complexity $ by simp))])
      have dΓ₁ : ⊢ᶜ[< i] (~r) :: Γ := (dΓ.cast (by simp[e])).andInversion₁ (q := ~s)
      have dΓ₂ : ⊢ᶜ[< i] (~s) :: Γ := (dΓ.cast (by simp[e])).andInversion₂ (p := ~r)
      have d₃  : ⊢ᶜ[< i] s :: Δ.remove (r ⋎ s) ++ Γ :=
        cut hrs.1 d₁ (dΓ₁.wk $ List.cons_subset_cons _ $ List.subset_append_right _ _)
      have : ⊢ᶜ[< i] (Δ.remove (r ⋎ s)) ++ Γ :=
        cut hrs.2 d₃ (dΓ₂.wk $ List.cons_subset_cons _ $ List.subset_append_right _ _)
      exact this.cast (by simp[e])
    · have : ⊢ᶜ[< i] r :: s :: (Δ.remove p ++ Γ) :=
        (reductionAux d tp hp dΓ).weakening (by
          rw[←List.cons_append, ←List.cons_append]
          exact List.append_subset_append
            (subset_trans (List.remove_cons_subset_cons_remove _ _ _) $
              List.cons_subset_cons _ $ List.remove_cons_subset_cons_remove _ _ _))
      have : ⊢ᶜ[< i] r ⋎ s :: (Δ.remove p ++ Γ) := or this
      exact this.cast (by rw[List.remove_cons_of_ne _ (Ne.symm e), List.cons_append])
  | _, @ex _ _ Δ q t d₁,          p, tp, hp, Γ, d₂ => by
    by_cases e : p = ∃' q
    · have d₁₁ : ⊢ᶜ[< i] q/[t] :: (Δ.remove (∃' q) ++ Γ) :=
        (reductionAux d₁ tp hp d₂).cast (by
          rw[←List.cons_append]; congr 1
          rw[e, List.remove_cons_of_ne]; exact Subformula.ne_of_ne_complexity (by simp))
      have d₂₁ : ⊢ᶜ[< i] (~q/[t]) :: Γ :=
        (allInversionClx (p := ~q) (by simpa[e] using d₂) t).cast (by simp)
      have : ⊢ᶜ[< i] Δ.remove (∃' q) ++ Γ :=
        cut (by simp; exact Nat.succ_le.mp (by simpa[e] using hp))
          d₁₁ (d₂₁.wk $ List.cons_subset_cons _ $ List.subset_append_right _ _)
      exact this.cast (by simp[e])
    · have : ⊢ᶜ[< i] q/[t] :: (Δ.remove p ++ Γ) :=
        (reductionAux d₁ tp hp d₂).weakening (by
          rw[←List.cons_append]
          exact List.append_subset_append (List.remove_cons_subset_cons_remove _ _ _))
      have : ⊢ᶜ[< i] (∃' q) :: (Δ.remove p ++ Γ) := ex t this
      exact this.cast (by rw[List.remove_cons_of_ne _ (Ne.symm e), List.cons_append])
  | _, @wk _ _ Δ Δ' d ss, p, tp, hp, Γ, dΓ => (reductionAux d tp hp dΓ).wk (List.append_subset_append $ List.remove_subset_remove _ $ ss)
  | _, @cut _ _ Δ r hr d dn, p, tp, hp, Γ, dΓ =>
    have d₁ : ⊢ᶜ[< i] r :: (Δ.remove p ++ Γ) :=
      (reductionAux d tp hp dΓ).weakening (by
        rw[←List.cons_append]
        exact List.append_subset_append (List.remove_cons_subset_cons_remove _ _ _))
    have dn₁ : ⊢ᶜ[< i] (~r) :: (Δ.remove p ++ Γ) :=
      (reductionAux dn tp hp dΓ).weakening (by
        rw[←List.cons_append]
        exact List.append_subset_append (List.remove_cons_subset_cons_remove _ _ _))
    cut hr d₁ dn₁

def reduction {i} {p} (hp : p.complexity ≤ i) : ⊢ᶜ[< i] p :: Δ → ⊢ᶜ[< i] (~p) :: Δ → ⊢ᶜ[< i] Δ := fun dp dn => by
  cases tp : p.isVType
  · have : (~p).isVType = true := isVType_neg_true_of_eq_false tp
    exact (reductionAux (p := ~p) dn this (by simp[hp]) (Γ := Δ) (dp.cast $ by simp)).weakening
      (by simp; exact List.remove_subset _ _)
  · exact (reductionAux dp tp hp dn).weakening (by simp; exact List.remove_subset _ _)

def elimination {i} : {Δ : Sequent L} → ⊢ᶜ[< i + 1] Δ → ⊢ᶜ[< i] Δ
  | _, axL Δ r v    => axL Δ r v
  | _, verum Δ      => verum Δ
  | _, and dp dq    => and dp.elimination dq.elimination
  | _, or d         => or d.elimination
  | _, all d        => all d.elimination
  | _, ex t d       => ex t d.elimination
  | _, wk d ss      => d.elimination.wk ss
  | _, cut hp dΔ dΓ => reduction (Nat.lt_add_one_iff.mp hp) dΔ.elimination dΓ.elimination

def hauptsatzClx : {i : ℕ} → ⊢ᶜ[< i] Δ → ⊢ᵀ Δ
  | 0,     d => d.cutWeakening (by simp)
  | i + 1, d => d.elimination.hauptsatzClx

def toClx : {Δ : Sequent L} → ⊢ᶜ Δ → (i : ℕ) × ⊢ᶜ[< i] Δ
  | _, axL Δ r v            => ⟨0, axL Δ r v⟩
  | _, verum Δ              => ⟨0, verum Δ⟩
  | _, and dp dq            => ⟨max dp.toClx.1 dq.toClx.1, and (dp.toClx.2.ofLe (by simp)) (dq.toClx.2.ofLe (by simp))⟩
  | _, or d                 => ⟨d.toClx.1, or d.toClx.2⟩
  | _, all d                => ⟨d.toClx.1, all d.toClx.2⟩
  | _, ex t d               => ⟨d.toClx.1, ex t d.toClx.2⟩
  | _, wk d ss              => ⟨d.toClx.1, wk d.toClx.2 ss⟩
  | _, @cut _ _ _ p _ dp dn =>
    ⟨max (max dp.toClx.1 dn.toClx.1) p.complexity.succ, cut (by simp) (dp.toClx.2.ofLe (by simp)) (dn.toClx.2.ofLe (by simp))⟩

def hauptsatz : ⊢ᶜ Δ → ⊢ᵀ Δ := fun d => hauptsatzClx d.toClx.2

lemma iff_cut {L :Language} {Δ : Sequent L} : Nonempty (⊢ᵀ Δ) ↔ Nonempty (⊢ᶜ Δ) :=
  haveI := Classical.typeDecidableEq
  ⟨by rintro ⟨d⟩; exact ⟨cutWeakeningCut d⟩, by rintro ⟨d⟩; exact ⟨d.hauptsatz⟩⟩

end DerivationCR

end FirstOrder

end LO
