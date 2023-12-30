import Logic.FirstOrder.Basic

namespace LO

namespace FirstOrder

open Semiformula

variable {L : Language.{u}} [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)]

namespace Semiformula

def isVType : {n : ℕ} → Semiformula L μ n → Bool
  | _, rel _ _  => true
  | _, nrel _ _ => true
  | _, ⊤        => true
  | _, ⊥        => true
  | _, _ ⋏ _    => false
  | _, _ ⋎ _    => true
  | _, ∀' _     => false
  | _, ∃' _     => true

lemma ne_and_of_isVType {p q r : Semiformula L μ n} (h : isVType p) : p ≠ q ⋏ r := by rintro rfl; simp[isVType] at h

lemma ne_all_of_isVType {p : Semiformula L μ n} {q} (h : isVType p) : p ≠ ∀' q := by rintro rfl; simp[isVType] at h

@[simp] lemma isVType_shift_iff {p : SyntacticSemiformula L n} : isVType (Rew.shift.hom p) = isVType p := by
  induction p using rec' <;> simp[Rew.rel, Rew.nrel, isVType]

lemma isVType_neg_true_of_eq_false {p : SyntacticSemiformula L n} : isVType p = false → isVType (~p) = true := by
  induction p using rec' <;> simp[Rew.rel, Rew.nrel, isVType]

end Semiformula

namespace Derivation

variable {C : Set (SyntacticFormula L)} (hC : ∀ f p, p ∈ C → (Rew.rewrite f).hom p ∈ C) {Δ Δ₁ Δ₂ Γ : Sequent L}

abbrev Restricted (C : Set (SyntacticFormula L)) (Δ : Sequent L) := {d : ⊢¹ Δ // CutRestricted C d}

scoped notation :45 "⊢ᶜ[" C "] " Γ:45 => Restricted C Γ

abbrev RestrictedComplexity (c : ℕ) (Δ : Sequent L) := ⊢ᶜ[{p | p.complexity < c}] Δ

scoped notation :45 "⊢ᶜ[< " c "] " Γ:45 => RestrictedComplexity c Γ

namespace Restricted

@[simp] lemma cutRestricted (d : ⊢ᶜ[C] Δ) : CutRestricted C (d : ⊢¹ Δ) := d.prop

def axL' {k} (r : L.Rel k) (v) (hp : Semiformula.rel r v ∈ Δ) (hn : Semiformula.nrel r v ∈ Δ) :
    ⊢ᶜ[C] Δ := ⟨Derivation.axL' r v hp hn, by simp[Derivation.axL']⟩

def verum' (h : ⊤ ∈ Δ) : ⊢ᶜ[C] Δ := ⟨Derivation.verum' h, by simp[Derivation.verum']⟩

def and (dp : ⊢ᶜ[C] p :: Δ) (dq : ⊢ᶜ[C] q :: Δ) : ⊢ᶜ[C] p ⋏ q :: Δ := ⟨Derivation.and dp.val dq.val, by simp⟩

def or (d : ⊢ᶜ[C] p :: q :: Δ) : ⊢ᶜ[C] p ⋎ q :: Δ := ⟨Derivation.or d.val, by simp⟩

def all {p} (d : ⊢ᶜ[C] Rew.free.hom p :: shifts Δ) : ⊢ᶜ[C] (∀' p) :: Δ := ⟨Derivation.all d.val, by simp⟩

def ex {p} (t) (d : ⊢ᶜ[C] p/[t] :: Δ) : ⊢ᶜ[C] (∃' p) :: Δ := ⟨Derivation.ex t d.val, by simp⟩

def wk (d : ⊢ᶜ[C] Γ) (h : Γ ⊆ Δ) : ⊢ᶜ[C] Δ := ⟨d.val.wk h, by simp⟩

def cut (dp : ⊢ᶜ[C] p :: Δ) (dn : ⊢ᶜ[C] ~p :: Δ) (h : p ∈ C) : ⊢ᶜ[C] Δ := ⟨Derivation.cut dp.val dn.val, by simp[h]⟩

def rewrite (f : ℕ → SyntacticTerm L) (d : ⊢ᶜ[C] Δ) : ⊢ᶜ[C] Δ.map (Rew.rewrite f).hom :=
  ⟨Derivation.rewrite d f, CutRestricted.rewrite hC f (by simp)⟩

def shifts (d : ⊢ᶜ[C] Δ) : ⊢ᶜ[C] shifts Δ := d.rewrite hC _

abbrev cast (d : ⊢ᶜ[C] Γ) (e : Γ = Δ) : ⊢ᶜ[C] Δ := ⟨Derivation.cast d e, by simp⟩

@[simp] lemma length_rewrite (f : ℕ → SyntacticTerm L) (d : ⊢ᶜ[C] Δ) : length (d.rewrite hC f).val = length d.val := by
  simp[rewrite]

def ofSubset {C C' : Set (SyntacticFormula L)} {Δ} (h : C ⊆ C') (d : ⊢ᶜ[C] Δ) : ⊢ᶜ[C'] Δ := ⟨d, d.cutRestricted.of_subset h⟩

end Restricted

def RestrictedComplexity.ofLe {i j : ℕ} (hij : i ≤ j) (d : ⊢ᶜ[< i] Δ) : ⊢ᶜ[< j] Δ := d.ofSubset (by simp; intro _ h; exact lt_of_lt_of_le h hij)

def andInversion₁Aux : {Δ : Sequent L} → ⊢ᶜ[C] Δ → (p q : SyntacticFormula L) → ⊢ᶜ[C] p :: Δ.remove (p ⋏ q)
  | _, ⟨@axL _ Δ _ r v, _⟩,       p, q =>
    Restricted.axL' r v (by simp[List.mem_remove_iff]) (by simp[List.mem_remove_iff])
  | _, ⟨@verum _ Δ, _⟩,           p, q =>
    Restricted.verum' (by simp[List.mem_remove_iff])
  | _, ⟨@and _ Δ p' q' dp dq, H⟩, p, q => by
    have H : CutRestricted C dp ∧ CutRestricted C dq := by simpa using H
    by_cases e : p = p' ∧ q = q'
    · exact (andInversion₁Aux ⟨dp, H.1⟩ p q).wk
        (by rcases e with ⟨rfl, rfl⟩; simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    · have ne : p ⋏ q ≠ p' ⋏ q' := by simpa[-not_and] using e
      have dp : ⊢ᶜ[C] (p' :: p :: (Δ.remove (p ⋏ q))) :=
        (andInversion₁Aux ⟨dp, H.1⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      have dq : ⊢ᶜ[C] (q' :: p :: (Δ.remove (p ⋏ q))) :=
        (andInversion₁Aux ⟨dq, H.2⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      exact (dp.and dq).wk (by
        simp[List.subset_def, List.mem_remove_iff, -not_and]
        constructor
        · right; simpa using Ne.symm ne
        · intros; simp[*])
  | _, ⟨@or _ Δ r s d, H⟩,        p, q =>
    have H : CutRestricted C d := by simpa using H
    have : ⊢ᶜ[C] (r :: s :: p :: Δ.remove (p ⋏ q)) :=
      (andInversion₁Aux ⟨d, H⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    this.or.wk (by
      simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, ⟨@all _ Δ r d, H⟩,         p, q =>
    have H : CutRestricted C d := by simpa using H
    have : ⊢ᶜ[C] Rew.free.hom r :: shifts (p :: Δ.remove (p ⋏ q)) :=
      (andInversion₁Aux ⟨d, H⟩ (Rew.shift.hom p) (Rew.shift.hom q)).wk (by
        simp[shifts]
        exact (List.Perm.subset_congr_right (List.Perm.swap _ _ _)).mp
          (List.subset_cons_of_subset _ $
            subset_trans (List.remove_cons_subset_cons_remove _ _ _) $
              List.cons_subset_cons _ $ subset_trans (by simp) (List.remove_map_substet_map_remove _ _ _)))
    this.all.wk ((List.Perm.subset_congr_left (List.Perm.swap _ _ _)).mp $
      List.cons_subset_cons _ $ by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, ⟨@ex _ Δ r t d, H⟩,        p, q =>
    have H : CutRestricted C d := by simpa using H
    have : ⊢ᶜ[C] r/[t] :: p :: Δ.remove (p ⋏ q) :=
      (andInversion₁Aux ⟨d, H⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (this.ex t).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, ⟨@wk _ Δ Γ d ss, H⟩,       p, q =>
    have H : CutRestricted C d := by simpa using H
    (andInversion₁Aux ⟨d, H⟩ p q).wk
      (List.cons_subset_cons _ $ List.remove_subset_remove _ ss)
  | _, ⟨@cut _ Δ r d dn, H⟩,      p, q =>
    have H : r ∈ C ∧ CutRestricted C d ∧ CutRestricted C dn := by simpa using H
    have d : ⊢ᶜ[C] r :: p :: Δ.remove (p ⋏ q) :=
      (andInversion₁Aux ⟨d, H.2.1⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have dn : ⊢ᶜ[C] (~r) :: p :: Δ.remove (p ⋏ q) :=
      (andInversion₁Aux ⟨dn, H.2.2⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    d.cut dn H.1
  termination_by andInversion₁Aux _ d _ _ => length d.val

def andInversion₁ {p q} (d : ⊢ᶜ[C] p ⋏ q :: Δ) : ⊢ᶜ[C] p :: Δ :=
  (andInversion₁Aux d p q).wk (by simp[List.remove]; exact List.subset_cons_of_subset _ (List.remove_subset _ _))

def andInversion₂Aux : {Δ : Sequent L} → ⊢ᶜ[C] Δ → (p q : SyntacticFormula L) → ⊢ᶜ[C] q :: Δ.remove (p ⋏ q)
  | _, ⟨@axL _ Δ _ r v, _⟩,       p, q =>
    Restricted.axL' r v (by simp[List.mem_remove_iff]) (by simp[List.mem_remove_iff])
  | _, ⟨@verum _ Δ, _⟩,           p, q =>
    Restricted.verum' (by simp[List.mem_remove_iff])
  | _, ⟨@and _ Δ p' q' dp dq, H⟩, p, q => by
    have H : CutRestricted C dp ∧ CutRestricted C dq := by simpa using H
    by_cases e : p = p' ∧ q = q'
    · exact (andInversion₂Aux ⟨dq, H.2⟩ p q).wk
        (by rcases e with ⟨rfl, rfl⟩; simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    · have ne : p ⋏ q ≠ p' ⋏ q' := by simpa[-not_and] using e
      have dp : ⊢ᶜ[C] (p' :: q :: (Δ.remove (p ⋏ q))) :=
        (andInversion₂Aux ⟨dp, H.1⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      have dq : ⊢ᶜ[C] (q' :: q :: (Δ.remove (p ⋏ q))) :=
        (andInversion₂Aux ⟨dq, H.2⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      exact (dp.and dq).wk (by
        simp[List.subset_def, List.mem_remove_iff, -not_and]
        constructor
        · right; simpa using Ne.symm ne
        · intros; simp[*])
  | _, ⟨@or _ Δ r s d, H⟩,        p, q =>
    have H : CutRestricted C d := by simpa using H
    have : ⊢ᶜ[C] (r :: s :: q :: Δ.remove (p ⋏ q)) :=
      (andInversion₂Aux ⟨d, H⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    this.or.wk (by
      simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, ⟨@all _ Δ r d, H⟩,         p, q =>
    have H : CutRestricted C d := by simpa using H
    have : ⊢ᶜ[C] Rew.free.hom r :: shifts (q :: Δ.remove (p ⋏ q)) :=
      (andInversion₂Aux ⟨d, H⟩ (Rew.shift.hom p) (Rew.shift.hom q)).wk (by
        simp[shifts]
        exact (List.Perm.subset_congr_right (List.Perm.swap _ _ _)).mp
          (List.subset_cons_of_subset _ $
            subset_trans (List.remove_cons_subset_cons_remove _ _ _) $
              List.cons_subset_cons _ $ subset_trans (by simp) (List.remove_map_substet_map_remove _ _ _)))
    this.all.wk ((List.Perm.subset_congr_left (List.Perm.swap _ _ _)).mp $
      List.cons_subset_cons _ $ by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, ⟨@ex _ Δ r t d, H⟩,        p, q =>
    have H : CutRestricted C d := by simpa using H
    have : ⊢ᶜ[C] r/[t] :: q :: Δ.remove (p ⋏ q) :=
      (andInversion₂Aux ⟨d, H⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (this.ex t).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, ⟨@wk _ Δ Γ d ss, H⟩,       p, q =>
    have H : CutRestricted C d := by simpa using H
    (andInversion₂Aux ⟨d, H⟩ p q).wk
      (List.cons_subset_cons _ $ List.remove_subset_remove _ ss)
  | _, ⟨@cut _ Δ r d dn, H⟩,      p, q =>
    have H : r ∈ C ∧ CutRestricted C d ∧ CutRestricted C dn := by simpa using H
    have d : ⊢ᶜ[C] r :: q :: Δ.remove (p ⋏ q) :=
      (andInversion₂Aux ⟨d, H.2.1⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have dn : ⊢ᶜ[C] (~r) :: q :: Δ.remove (p ⋏ q) :=
      (andInversion₂Aux ⟨dn, H.2.2⟩ p q).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    d.cut dn H.1
  termination_by andInversion₂Aux _ d _ _ => length d.val

def andInversion₂ {p q} (d : ⊢ᶜ[C] p ⋏ q :: Δ) : ⊢ᶜ[C] q :: Δ :=
  (andInversion₂Aux d p q).wk (by simp[List.remove]; exact List.subset_cons_of_subset _ (List.remove_subset _ _))

def allInversionAux : {Δ : Sequent L} → ⊢ᶜ[C] Δ →
    (p : SyntacticSemiformula L 1) → (t : SyntacticTerm L) → ⊢ᶜ[C] p/[t] :: Δ.remove (∀' p)
  | _, ⟨@axL _ Δ _ r v, _⟩,     p, t => Restricted.axL' r v (by simp[List.mem_remove_iff]) (by simp[List.mem_remove_iff])
  | _, ⟨@verum _ Δ, _⟩,         p, t => Restricted.verum' (by simp[List.mem_remove_iff])
  | _, ⟨@and _ Δ r s dr ds, H⟩, p, t =>
      have H : CutRestricted C dr ∧ CutRestricted C ds := by simpa using H
      have dr : ⊢ᶜ[C] r :: p/[t] :: Δ.remove (∀' p) :=
        (allInversionAux ⟨dr, H.1⟩ p t).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      have ds : ⊢ᶜ[C] (s :: p/[t] :: Δ.remove (∀' p)) :=
        (allInversionAux ⟨ds, H.2⟩ p t).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      (dr.and ds).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, ⟨@or _ Δ r s d, H⟩,      p, t =>
      have H : CutRestricted C d := by simpa using H
      have : ⊢ᶜ[C] (r :: s :: p/[t] :: Δ.remove (∀' p)) :=
        (allInversionAux ⟨d, H⟩ p t).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
      this.or.wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, ⟨@all _ Δ p' d, H⟩,      p, t => by
      have H : CutRestricted C d := by simpa using H
      by_cases e : p' = p
      · simp[e]
        let d' : ⊢ᶜ[C] p/[t] :: Δ :=
          (Restricted.rewrite hC (t :>ₙ Semiterm.fvar) ⟨d, H⟩).cast
            (by simp[e, shifts, Function.comp, ←Rew.hom_comp_app,
                  Rew.rewrite_comp_free_eq_substs, Rew.rewrite_comp_shift_eq_id])
        exact (allInversionAux d' p t).wk (by
          rw[List.remove_cons_of_ne]; simp; exact Semiformula.ne_of_ne_complexity (by simp))
      · have : ⊢ᶜ[C] (Rew.free.hom p' :: shifts (p/[t] :: Δ.remove (∀' p))) :=
          (allInversionAux ⟨d, H⟩ (Rew.shift.hom p) (Rew.shift t)).wk
          (by simp[shifts, ←Rew.hom_comp_app, Rew.shift_comp_substs1]
              exact subset_trans (List.remove_cons_subset_cons_remove _ _ _)
                (List.cons_subset_cons _ $ List.subset_cons_of_subset _ $
                subset_trans (by simp) $ List.remove_map_substet_map_remove _ _ _))
        exact this.all.wk (by simp[List.subset_def, List.mem_remove_iff, e]; intros; simp[*])
  | _, ⟨@ex _ Δ q u d, H⟩,      p, t =>
    have H : CutRestricted C d := by simpa using H
    have : ⊢ᶜ[C] q/[u] :: p/[t] :: Δ.remove (∀' p) :=
      (allInversionAux ⟨d, H⟩ p t).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (this.ex u).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
  | _, ⟨@wk _ Δ Γ d ss, H⟩,     p, t =>
    have H : CutRestricted C d := by simpa using H
    (allInversionAux ⟨d, H⟩ p t).wk
      (List.cons_subset_cons _ $ List.remove_subset_remove _ ss)
  | _, ⟨@cut _ Δ r d dn, H⟩, p, t =>
    have H : r ∈ C ∧ CutRestricted C d ∧ CutRestricted C dn := by simpa using H
    have d : ⊢ᶜ[C] r :: p/[t] :: Δ.remove (∀' p) :=
      (allInversionAux ⟨d, H.2.1⟩ p t).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have dn : ⊢ᶜ[C] ((~r) :: p/[t] :: Δ.remove (∀' p)) :=
      (allInversionAux ⟨dn, H.2.2⟩ p t).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    d.cut dn H.1
  termination_by allInversionAux _ d _ _ => length d.val

def allInversion (d : ⊢ᶜ[C] (∀' p) :: Δ) (t) : ⊢ᶜ[C] p/[t] :: Δ :=
  (allInversionAux hC d p t).wk (by simp; exact List.subset_cons_of_subset _ (List.remove_subset _ _))

def falsumElimAux : {Δ : Sequent L} → ⊢ᶜ[C] Δ → ⊢ᶜ[C] Δ.remove ⊥
  | _, ⟨@axL _ Δ _ r v, _⟩     => Restricted.axL' r v (by simp[List.mem_remove_iff]) (by simp[List.mem_remove_iff])
  | _, ⟨@verum _ Δ, _⟩         => Restricted.verum' (by simp[List.mem_remove_iff])
  | _, ⟨@and _ Δ p q dp dq, H⟩  =>
    have H : CutRestricted C dp ∧ CutRestricted C dq := by simpa using H
    have dp : ⊢ᶜ[C] p :: (Δ.remove ⊥) := (falsumElimAux ⟨dp, H.1⟩).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have dq : ⊢ᶜ[C] q :: (Δ.remove ⊥) := (falsumElimAux ⟨dq, H.2⟩).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (dp.and dq).cast (by rw[List.remove_cons_of_ne]; simp)
  | _, ⟨@or _ Δ p q d, H⟩      =>
    have : ⊢ᶜ[C] p :: q :: Δ.remove ⊥ :=
      (falsumElimAux ⟨d, by simpa using H⟩).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    this.or.cast (by rw[List.remove_cons_of_ne]; simp)
  | _, ⟨@all _ Δ p d, H⟩       =>
    have : ⊢ᶜ[C] Rew.free.hom p :: (shifts $ Δ.remove ⊥) :=
      (falsumElimAux ⟨d, by simpa using H⟩).wk
        (subset_trans (List.remove_cons_subset_cons_remove _ _ _) $ List.cons_subset_cons _ $
          subset_trans (by simp[shifts]) $ List.remove_map_substet_map_remove _ _ _)
    this.all.cast (by rw[List.remove_cons_of_ne]; simp)
  | _, ⟨@ex _ Δ p t d, H⟩      =>
    have H : CutRestricted C d := by simpa using H
    have : ⊢ᶜ[C] p/[t] :: Δ.remove ⊥ := (falsumElimAux ⟨d, H⟩).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    (this.ex t).cast (by rw[List.remove_cons_of_ne]; simp)
  | _, ⟨@wk _ Δ Γ d ss, H⟩     => (falsumElimAux ⟨d, by simpa using H⟩).wk (List.remove_subset_remove _ ss)
  | _, ⟨@cut _ Δ p d dn, H⟩ =>
    have H : p ∈ C ∧ CutRestricted C d ∧ CutRestricted C dn := by simpa using H
    have d : ⊢ᶜ[C] p :: Δ.remove ⊥ := (falsumElimAux ⟨d, H.2.1⟩).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have dn : ⊢ᶜ[C] (~p) :: Δ.remove ⊥ := (falsumElimAux ⟨dn, H.2.2⟩).wk (by simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    d.cut dn H.1
  termination_by falsumElimAux _ d => length d.val

def falsumElim (d : ⊢ᶜ[C] ⊥ :: Δ) : ⊢ᶜ[C] Δ := (falsumElimAux d).wk (by simp; exact List.remove_subset _ _)

def reductionAux {i} : {Δ : Sequent L} →
    ⊢ᶜ[< i] Δ → {p : SyntacticFormula L} → p.isVType = true → p.complexity ≤ i →
    {Γ : Sequent L} → ⊢ᶜ[< i] (~p) :: Γ → ⊢ᶜ[< i] Δ.remove p ++ Γ
  | _, ⟨@axL _ Δ _ r v, _⟩,     p, _,  _,  Γ, dΓ => by
    by_cases e₁ : p = rel r v
    · exact dΓ.wk (by simp[e₁, List.mem_remove_iff])
    · by_cases e₂ : p = nrel r v
      · exact dΓ.wk (by simp[e₂, List.mem_remove_iff])
      · exact Restricted.axL' r v (by simp[Ne.symm e₁, List.mem_remove_iff]) (by simp[Ne.symm e₂, List.mem_remove_iff])
  | _, ⟨@verum _ Δ, _⟩,         p, _,  _,  Γ, dΓ => by
    by_cases e : p = ⊤
    · have : ⊢ᶜ[< i] ⊥ :: Γ := dΓ.cast (by simp[e])
      have : ⊢ᶜ[< i] Γ := falsumElim this
      exact this.wk (by simp)
    · exact Restricted.verum' (by simp[List.mem_remove_iff, Ne.symm e])
  | _, ⟨@and _ Δ r s dr ds, H⟩, p, tp, hp, Γ, dΓ => by
    have H : CutRestricted {p | p.complexity < i} dr ∧ CutRestricted {p | p.complexity < i} ds := by simpa using H
    have e : p ≠ r ⋏ s := ne_and_of_isVType tp
    have dr : ⊢ᶜ[< i] r :: (Δ.remove p ++ Γ) :=
      (reductionAux ⟨dr, H.1⟩ tp hp dΓ).wk (by
        rw[←List.cons_append]
        apply List.append_subset_append
        simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    have ds : ⊢ᶜ[< i] s :: (Δ.remove p ++ Γ) :=
      (reductionAux ⟨ds, H.2⟩ tp hp dΓ).wk (by
        rw[←List.cons_append]
        apply List.append_subset_append
        simp[List.subset_def, List.mem_remove_iff]; intros; simp[*])
    exact (dr.and ds).cast (by rw[List.remove_cons_of_ne _ (Ne.symm e), List.cons_append])
  | _, ⟨@all _ Δ q d, H⟩,       p, tp, hp, Γ, dΓ => by
    have e : p ≠ ∀' q := ne_all_of_isVType tp
    have : ⊢ᶜ[< i] ~Rew.shift.hom p :: shifts Γ := (dΓ.shifts (by simp)).cast (by simp[shifts_cons])
    have : ⊢ᶜ[< i] Rew.free.hom q :: shifts (Δ.remove p ++ Γ) :=
      (reductionAux ⟨d, by simpa using H⟩ (by simp[tp]) (by simp[hp]) this).wk
        (by simp[shifts]
            constructor
            · exact subset_trans (List.remove_cons_subset_cons_remove _ _ _)
                (List.cons_subset_cons _ $
                  List.subset_append_of_subset_left _ $ List.remove_map_substet_map_remove _ _ _)
            · rw[←List.cons_append]
              exact List.subset_append_right _ _)
    have : ⊢ᶜ[< i] (∀' q) :: (Δ.remove p ++ Γ) := this.all
    exact this.cast (by rw[List.remove_cons_of_ne _ (Ne.symm e), List.cons_append])
  | _, ⟨@or _ Δ r s d, H⟩,      p, tp, hp, Γ, dΓ => by
    by_cases e : p = r ⋎ s
    · have hrs : r.complexity < i ∧ s.complexity < i := by simpa[e, Nat.succ_le] using hp
      have d₁  : ⊢ᶜ[< i] r :: s :: Δ.remove (r ⋎ s) ++ Γ :=
        (reductionAux ⟨d, by simpa using H⟩ tp hp dΓ).cast (by
          rw[e, List.remove_cons_of_ne _ (show r ≠ r ⋎ s from (Semiformula.ne_of_ne_complexity $ by simp)),
            List.remove_cons_of_ne _ (show s ≠ r ⋎ s from (Semiformula.ne_of_ne_complexity $ by simp))])
      have dΓ₁ : ⊢ᶜ[< i] (~r) :: Γ := andInversion₁ (q := ~s) (dΓ.cast (by simp[e]))
      have dΓ₂ : ⊢ᶜ[< i] (~s) :: Γ := andInversion₂ (p := ~r) (dΓ.cast (by simp[e]))
      have d₃  : ⊢ᶜ[< i] s :: Δ.remove (r ⋎ s) ++ Γ :=
        d₁.cut (dΓ₁.wk $ List.cons_subset_cons _ $ List.subset_append_right _ _) hrs.1
      have : ⊢ᶜ[< i] (Δ.remove (r ⋎ s)) ++ Γ :=
        d₃.cut (dΓ₂.wk $ List.cons_subset_cons _ $ List.subset_append_right _ _) hrs.2
      exact this.cast (by simp[e])
    · have : ⊢ᶜ[< i] r :: s :: (Δ.remove p ++ Γ) :=
        (reductionAux ⟨d, by simpa using H⟩ tp hp dΓ).wk (by
          rw[←List.cons_append, ←List.cons_append]
          exact List.append_subset_append
            (subset_trans (List.remove_cons_subset_cons_remove _ _ _) $
              List.cons_subset_cons _ $ List.remove_cons_subset_cons_remove _ _ _))
      have : ⊢ᶜ[< i] r ⋎ s :: (Δ.remove p ++ Γ) := this.or
      exact this.cast (by rw[List.remove_cons_of_ne _ (Ne.symm e), List.cons_append])
  | _, ⟨@ex _ Δ q t d₁, H⟩,     p, tp, hp, Γ, d₂ => by
    by_cases e : p = ∃' q
    · have d₁₁ : ⊢ᶜ[< i] q/[t] :: (Δ.remove (∃' q) ++ Γ) :=
        (reductionAux ⟨d₁, by simpa using H⟩ tp hp d₂).cast (by
          rw[←List.cons_append]; congr 1
          rw[e, List.remove_cons_of_ne]; exact Semiformula.ne_of_ne_complexity (by simp))
      have d₂₁ : ⊢ᶜ[< i] (~q/[t]) :: Γ :=
        (allInversion (p := ~q) (by simp) (by simpa[e] using d₂) t).cast (by simp)
      have : ⊢ᶜ[< i] Δ.remove (∃' q) ++ Γ :=
        d₁₁.cut (d₂₁.wk $ List.cons_subset_cons _ $ List.subset_append_right _ _)
          (by simp; exact Nat.succ_le.mp (by simpa[e] using hp))
      exact this.cast (by simp[e])
    · have : ⊢ᶜ[< i] q/[t] :: (Δ.remove p ++ Γ) :=
        (reductionAux ⟨d₁, by simpa using H⟩ tp hp d₂).wk (by
          rw[←List.cons_append]
          exact List.append_subset_append (List.remove_cons_subset_cons_remove _ _ _))
      have : ⊢ᶜ[< i] (∃' q) :: (Δ.remove p ++ Γ) := this.ex t
      exact this.cast (by rw[List.remove_cons_of_ne _ (Ne.symm e), List.cons_append])
  | _, ⟨@wk _ Δ Δ' d ss, H⟩,    p, tp, hp, Γ, dΓ =>
    (reductionAux ⟨d, by simpa using H⟩ tp hp dΓ).wk (List.append_subset_append $ List.remove_subset_remove _ $ ss)
  | _, ⟨@cut _ Δ r d dn, H⟩, p, tp, hp, Γ, dΓ =>
    have H : r.complexity < i ∧ CutRestricted {p | p.complexity < i} d ∧ CutRestricted {p | p.complexity < i} dn := by simpa using H
    have d₁ : ⊢ᶜ[< i] r :: (Δ.remove p ++ Γ) :=
      (reductionAux ⟨d, H.2.1⟩ tp hp dΓ).wk (by
        rw[←List.cons_append]
        exact List.append_subset_append (List.remove_cons_subset_cons_remove _ _ _))
    have dn₁ : ⊢ᶜ[< i] (~r) :: (Δ.remove p ++ Γ) :=
      (reductionAux ⟨dn, H.2.2⟩ tp hp dΓ).wk (by
        rw[←List.cons_append]
        exact List.append_subset_append (List.remove_cons_subset_cons_remove _ _ _))
    d₁.cut dn₁ H.1
  termination_by reductionAux d _ _ _ _ _ => length d.val

def reduction {i} {p} (hp : p.complexity ≤ i) : ⊢ᶜ[< i] p :: Δ → ⊢ᶜ[< i] (~p) :: Δ → ⊢ᶜ[< i] Δ := fun dp dn => by
  cases tp : p.isVType
  · have : (~p).isVType = true := isVType_neg_true_of_eq_false tp
    exact (reductionAux (p := ~p) dn this (by simp[hp]) (Γ := Δ) (dp.cast $ by simp)).wk
      (by simp; exact List.remove_subset _ _)
  · exact (reductionAux dp tp hp dn).wk (by simp; exact List.remove_subset _ _)

def elimination {i} : {Δ : Sequent L} → ⊢ᶜ[< i + 1] Δ → ⊢ᶜ[< i] Δ
  | _, ⟨axL Δ r v, _⟩       => Restricted.axL' r v (by simp) (by simp)
  | _, ⟨verum Δ, _⟩         => Restricted.verum' (by simp)
  | _, ⟨and dp dq, H⟩       =>
    have H : CutRestricted {p | p.complexity < i + 1} dp ∧ CutRestricted {p | p.complexity < i + 1} dq := by simpa using H
    (elimination ⟨dp, H.1⟩).and (elimination ⟨dq, H.2⟩)
  | _, ⟨or d, H⟩            => (elimination ⟨d, by simpa using H⟩).or
  | _, ⟨all d, H⟩           => (elimination ⟨d, by simpa using H⟩).all
  | _, ⟨ex t d, H⟩          => (elimination ⟨d, by simpa using H⟩).ex
  | _, ⟨wk d ss, H⟩         => (elimination ⟨d, by simpa using H⟩).wk ss
  | _, ⟨@cut _ _ p d dn, H⟩ =>
    have H : p.complexity < i + 1 ∧
      CutRestricted {p | p.complexity < i + 1} d ∧ CutRestricted {p | p.complexity < i + 1} dn := by simpa using H
    reduction (Nat.lt_add_one_iff.mp H.1) (elimination ⟨d, H.2.1⟩) (elimination ⟨dn, H.2.2⟩)
  termination_by elimination d => length d.val

def hauptsatzClx : {i : ℕ} → ⊢ᶜ[< i] Δ → { d : ⊢¹ Δ // CutFree d }
  | 0,     d => ⟨d.val, by simpa using d.prop⟩
  | i + 1, d => hauptsatzClx (elimination d)

def toClx : {Δ : Sequent L} → ⊢¹ Δ → (i : ℕ) × ⊢ᶜ[< i] Δ
  | _, axL Δ r v        => ⟨0, ⟨axL Δ r v, by simp⟩⟩
  | _, verum Δ          => ⟨0, ⟨verum Δ, by simp⟩⟩
  | _, and dp dq        => ⟨max dp.toClx.1 dq.toClx.1, (dp.toClx.2.ofLe (by simp)).and (dq.toClx.2.ofLe (by simp))⟩
  | _, or d             => ⟨d.toClx.1, d.toClx.2.or⟩
  | _, all d            => ⟨d.toClx.1, d.toClx.2.all⟩
  | _, ex t d           => ⟨d.toClx.1, d.toClx.2.ex t⟩
  | _, wk d ss          => ⟨d.toClx.1, d.toClx.2.wk ss⟩
  | _, @cut _ _ p dp dn =>
    ⟨max (max dp.toClx.1 dn.toClx.1) p.complexity.succ, (dp.toClx.2.ofLe (by simp)).cut (dn.toClx.2.ofLe (by simp)) (by simp)⟩

def hauptsatz : ⊢¹ Δ → { d : ⊢¹ Δ // CutFree d } := fun d => hauptsatzClx d.toClx.2

lemma iff_cut {L : Language} {Δ : Sequent L} : Nonempty { d : ⊢¹ Δ // CutFree d } ↔ ⊢¹! Δ :=
  haveI := Classical.typeDecidableEq
  ⟨by rintro ⟨d⟩; exact ⟨d⟩, by rintro ⟨d⟩; exact ⟨hauptsatz d⟩⟩

end Derivation

end FirstOrder

end LO
