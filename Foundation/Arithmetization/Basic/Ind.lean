import Foundation.Arithmetization.Basic.PeanoMinus


noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V]

section


variable [V ⊧ₘ* 𝐏𝐀⁻]

section neg

variable (Γ : Polarity) (m : ℕ) [V ⊧ₘ* Theory.InductionScheme ℒₒᵣ (Arith.Hierarchy Γ m)]

lemma induction {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (P := P) (C := Hierarchy Γ m) (by
    rcases hP with ⟨φ, hp⟩
    haveI : Inhabited V := Classical.inhabited_of_nonempty'

    exact ⟨φ.val.enumarateFVar, (Rew.rewriteMap φ.val.idxOfFVar) ▹ φ.val, by simp [hp],
      by  intro x; simp [Semiformula.eval_rewriteMap]
          have : (Semiformula.Evalm V ![x] fun x ↦ φ.val.enumarateFVar (φ.val.idxOfFVar x)) φ.val ↔ (Semiformula.Evalm V ![x] id) φ.val :=
            Semiformula.eval_iff_of_funEqOn _ (by
              intro x hx; simp [Semiformula.enumarateFVar_idxOfFVar (Semiformula.mem_fvarList_iff_fvar?.mpr hx)])
          simp [this, hp.df.iff]⟩)
    zero succ

lemma order_induction {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using induction
  · exact Γ
  · exact m
  · suffices Γ-[m].BoldfacePred fun x => ∀ y < x, P y by exact this
    exact HierarchySymbol.Boldface.ball_blt (by simp) (hP.retraction ![0])
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => exact inferInstance

private lemma neg_induction {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using induction
    · exact Γ
    · exact m
    · suffices Γ-[m].BoldfacePred fun x => x ≤ a → P (a - x) by exact this
      apply HierarchySymbol.Boldface.imp
      · apply HierarchySymbol.Boldface.bcomp₂ (by definability) (by definability)
      · apply HierarchySymbol.Boldface.bcomp₁ (by definability)
    case zero =>
      intro _; simpa using ha
    case succ x IH =>
      intro hx
      have : P (a - x) := IH (le_of_add_le_left hx)
      exact (not_imp_not.mp <| nsucc (a - (x + 1))) (by
        rw [←sub_sub, sub_add_self_of_le]
        · exact this
        · exact le_tsub_of_add_le_left hx)
    case inst => exact inferInstance
  have : P 0 := by simpa using this a (by rfl)
  contradiction

lemma models_InductionScheme_alt : V ⊧ₘ* Theory.InductionScheme ℒₒᵣ (Arith.Hierarchy Γ.alt m) := by
  simp [Theory.InductionOnHierarchy, Theory.InductionScheme]
  rintro _ φ hp rfl
  simp [models_iff, succInd, Semiformula.eval_rew_q,
    Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton]
  intro v H0 Hsucc x
  have : Semiformula.Evalm V ![0] v φ →
    (∀ x, Semiformula.Evalm V ![x] v φ → Semiformula.Evalm V ![x + 1] v φ) →
      ∀ x, Semiformula.Evalm V ![x] v φ := by
    simpa using
      neg_induction Γ m (P := λ x ↦ ¬Semiformula.Evalm V ![x] v φ)
        (.mkPolarity (∼(Rew.rewriteMap v ▹ φ)) (by simpa using hp)
        (by intro x; simp [←Matrix.fun_eq_vec_one, Semiformula.eval_rewriteMap]))
  exact this H0 Hsucc x

instance : V ⊧ₘ* Theory.InductionScheme ℒₒᵣ (Arith.Hierarchy Γ.alt m) := models_InductionScheme_alt Γ m

lemma least_number {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using induction
    · exact Γ.alt
    · exact m
    · suffices Γ.alt-[m].BoldfacePred fun z ↦ ∀ w < z, ¬P w by exact this
      apply HierarchySymbol.Boldface.ball_blt (by definability)
      apply HierarchySymbol.Boldface.not
      apply HierarchySymbol.Boldface.bcomp₁ (hP := by simpa using hP) (by definability)
    case zero => simp
    case succ x IH =>
      intro w hx hw
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hx) with (hx | rfl)
      · exact IH w hx hw
      · have : ∃ v < w, P v := A w hw
        rcases this with ⟨v, hvw, hv⟩
        exact IH v hvw hv
    case inst => exact inferInstance
  exact this (x + 1) x (by simp) h

end neg

section

variable (Γ : SigmaPiDelta) (m : ℕ) [V ⊧ₘ* Theory.InductionScheme ℒₒᵣ (Arith.Hierarchy 𝚺 m)]

lemma succ_induction_sigma {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  match Γ with
  | 𝚺 => induction 𝚺 m hP zero succ
  | 𝚷 =>
    haveI : V ⊧ₘ* Theory.InductionScheme ℒₒᵣ (Arith.Hierarchy 𝚷 m) := models_InductionScheme_alt 𝚺 m
    induction 𝚷 m hP zero succ
  | 𝚫 => induction 𝚺 m hP.of_delta zero succ

lemma order_induction_sigma {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  match Γ with
  | 𝚺 => order_induction 𝚺 m hP ind
  | 𝚷 =>
    haveI : V ⊧ₘ* Theory.InductionScheme ℒₒᵣ (Arith.Hierarchy 𝚷 m) := models_InductionScheme_alt 𝚺 m
    order_induction 𝚷 m hP ind
  | 𝚫 => order_induction 𝚺 m hP.of_delta ind

lemma least_number_sigma {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  match Γ with
  | 𝚺 => least_number 𝚺 m hP h
  | 𝚷 =>
    haveI : V ⊧ₘ* Theory.InductionScheme ℒₒᵣ (Arith.Hierarchy 𝚷 m) := models_InductionScheme_alt 𝚺 m
    least_number 𝚷 m hP h
  | 𝚫 => least_number 𝚺 m hP.of_delta h

end

instance [V ⊧ₘ* Theory.InductionScheme ℒₒᵣ (Arith.Hierarchy 𝚺 m)] :
    V ⊧ₘ* Theory.InductionScheme ℒₒᵣ (Arith.Hierarchy Γ m) := by
  rcases Γ
  · exact inferInstance
  · exact models_InductionScheme_alt 𝚺 m

end

def mod_IOpen_of_mod_InductionOnHierarchy (Γ n) [V ⊧ₘ* 𝐈𝐍𝐃Γ n] : V ⊧ₘ* 𝐈open :=
  ModelsTheory.of_ss (U := 𝐈𝐍𝐃Γ n) inferInstance
    (Set.union_subset_union_right _ (InductionScheme_subset Hierarchy.of_open))

def mod_ISigma_of_le {n₁ n₂} (h : n₁ ≤ n₂) [V ⊧ₘ* 𝐈𝚺 n₂] : V ⊧ₘ* 𝐈𝚺 n₁ :=
  ModelsTheory.of_ss inferInstance (ISigma_subset_mono h)

instance [V ⊧ₘ* 𝐈open] : V ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_add_left V 𝐏𝐀⁻ (Theory.InductionScheme _ Semiformula.Open)

instance [V ⊧ₘ* 𝐈𝚺₀] : V ⊧ₘ* 𝐈open := mod_IOpen_of_mod_InductionOnHierarchy 𝚺 0

instance [V ⊧ₘ* 𝐈𝚺₁] : V ⊧ₘ* 𝐈𝚺₀ := mod_ISigma_of_le (show 0 ≤ 1 from by simp)

instance [V ⊧ₘ* 𝐈𝚺 n] : V ⊧ₘ* 𝐈𝚷 n :=
  haveI : V ⊧ₘ* 𝐏𝐀⁻ := models_PeanoMinus_of_models_InductionOnHierarchy 𝚺 n
  inferInstance

instance [V ⊧ₘ* 𝐈𝚷 n] : V ⊧ₘ* 𝐈𝚺 n :=
  haveI : V ⊧ₘ* 𝐏𝐀⁻ := Arith.models_PeanoMinus_of_models_InductionOnHierarchy 𝚷 n
  by simp [*]; simpa [Theory.IPi] using models_InductionScheme_alt (V := V) 𝚷 n

lemma models_ISigma_iff_models_IPi {n} : V ⊧ₘ* 𝐈𝚺 n ↔ V ⊧ₘ* 𝐈𝚷 n :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance [V ⊧ₘ* 𝐈𝚺 n] : V ⊧ₘ* 𝐈𝐍𝐃Γ n :=
  match Γ with
  | 𝚺 => inferInstance
  | 𝚷 => inferInstance

@[elab_as_elim] lemma ISigma0.succ_induction [V ⊧ₘ* 𝐈𝚺₀]
    {P : V → Prop} (hP : 𝚺₀.BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction 𝚺 0 hP zero succ

@[elab_as_elim] lemma ISigma1.sigma1_succ_induction [V ⊧ₘ* 𝐈𝚺₁]
    {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction 𝚺 1 hP zero succ

@[elab_as_elim] lemma ISigma1.pi1_succ_induction [V ⊧ₘ* 𝐈𝚺₁]
    {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction 𝚷 1 hP zero succ

@[elab_as_elim] lemma ISigma0.order_induction [V ⊧ₘ* 𝐈𝚺₀]
    {P : V → Prop} (hP : 𝚺₀-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction 𝚺 0 hP ind

@[elab_as_elim] lemma ISigma1.sigma1_order_induction [V ⊧ₘ* 𝐈𝚺₁]
    {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction 𝚺 1 hP ind

@[elab_as_elim] lemma ISigma1.pi1_order_induction [V ⊧ₘ* 𝐈𝚺₁]
    {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction 𝚷 1 hP ind

lemma ISigma0.least_number [V ⊧ₘ* 𝐈𝚺₀] {P : V → Prop} (hP : 𝚺₀-Predicate P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  least_number 𝚺 0 hP h

@[elab_as_elim] lemma ISigma1.sigma1_succ_induction [V ⊧ₘ* 𝐈𝚺₁] (Γ)
    {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := succ_induction_sigma Γ 1 hP zero succ

@[elab_as_elim] lemma ISigma1.sigma1_order_induction [V ⊧ₘ* 𝐈𝚺₁] (Γ)
    {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := order_induction_sigma Γ 1 hP ind

end LO.Arith

end
