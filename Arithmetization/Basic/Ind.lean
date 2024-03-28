import Arithmetization.Basic.PeanoMinus

namespace LO.FirstOrder

attribute [simp] Theory.Mod.modelsTheory

namespace Arith

namespace Theory

variable {L : Language} [L.ORing] {C C' : Semiformula L ℕ 1 → Prop}

lemma mem_indScheme_of_mem {p : Semiformula L ℕ 1} (hp : C p) :
    ∀ᶠ* succInd p ∈ indScheme L C := by
  simp [indScheme]; exact ⟨p, hp, rfl⟩

lemma mem_iOpen_of_qfree {p : Semiformula L ℕ 1} (hp : p.Open) :
    ∀ᶠ* succInd p ∈ indScheme L Semiformula.Open := by
  exact ⟨p, hp, rfl⟩

lemma indScheme_subset (h : ∀ {p : Semiformula L ℕ 1},  C p → C' p) : indScheme L C ⊆ indScheme L C' := by
  intro _; simp [indScheme]; rintro p hp rfl; exact ⟨p, h hp, rfl⟩

notation "𝐈𝚫₀" => iSigma 0

notation "𝐈𝚺₁" => iSigma 1

notation "𝐈𝚷₁" => iPi 1

lemma iSigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈𝚺 s₁ ⊆ 𝐈𝚺 s₂ :=
  Set.union_subset_union_right _ (Theory.indScheme_subset (fun H ↦ H.mono h))

end Theory

noncomputable section

namespace Model

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M]

section

variable [𝐏𝐀⁻.Mod M] {L : Language} [L.ORing] [Structure L M] [Structure.ORing L M] [Structure.Monotone L M]

section IndScheme

variable {C : Semiformula L ℕ 1 → Prop} [(Theory.indScheme L C).Mod M]

lemma induction_eval {p : Semiformula L ℕ 1} (hp : C p) (v) :
    Semiformula.Eval! M ![0] v p →
    (∀ x, Semiformula.Eval! M ![x] v p → Semiformula.Eval! M ![x + 1] v p) →
    ∀ x, Semiformula.Eval! M ![x] v p := by
  have : M ⊧ₘ (∀ᶠ* succInd p) :=
    Theory.Mod.models (T := Theory.indScheme _ C) M (by simpa using Theory.mem_indScheme_of_mem hp)
  simp [models_iff, succInd, Semiformula.eval_substs,
    Semiformula.eval_rew_q Rew.toS, Function.comp, Matrix.constant_eq_singleton] at this
  exact this v

variable (L)

@[elab_as_elim]
lemma induction {P : M → Prop}
    (hP : ∃ e : ℕ → M, ∃ p : Semiformula L ℕ 1, C p ∧ ∀ x, P x ↔ Semiformula.Eval! M ![x] e p) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨e, p, Cp, hp⟩; simpa [←hp] using induction_eval (M := M) Cp e

end IndScheme

section neg

variable (Γ : Polarity) (s : ℕ) [(Theory.indScheme L (Arith.Hierarchy Γ s)).Mod M]

@[elab_as_elim]
lemma hierarchy_induction {P : M → Prop} (hP : DefinablePred L Γ s P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (P := P) (C := Hierarchy Γ s) (L := L) (by
    rcases hP with ⟨p, hp⟩
    haveI : Inhabited M := Classical.inhabited_of_nonempty'
    exact ⟨p.val.fvEnumInv, (Rew.rewriteMap p.val.fvEnum).hom p.val, by simp [hp],
      by  intro x; simp [Semiformula.eval_rewriteMap]
          have : (Semiformula.Eval! M ![x] fun x => p.val.fvEnumInv (p.val.fvEnum x)) p.val ↔ (Semiformula.Eval! M ![x] id) p.val :=
            Semiformula.eval_iff_of_funEqOn _ (by intro x hx; simp [Semiformula.fvEnumInv_fvEnum hx])
          simp [this, hp.eval]⟩)
    zero succ

@[elab_as_elim]
lemma hierarchy_order_induction {P : M → Prop} (hP : DefinablePred L Γ s P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using hierarchy_induction
  · exact Γ
  · exact s
  · suffices DefinablePred L Γ s fun x => ∀ y < x, P y by exact this
    exact Definable.ball_lt (L := L) (by simp) (Definable.comp₁ (by simp))
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => exact inferInstance
  case inst => exact inferInstance

private lemma hierarchy_neg_induction {P : M → Prop} (hP : DefinablePred L Γ s P)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using hierarchy_induction
    · exact Γ
    · exact s
    · suffices DefinablePred L Γ s fun x => x ≤ a → P (a - x) by exact this
      definability
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
    case inst => exact inferInstance
  have : P 0 := by simpa using this a (by rfl)
  contradiction

lemma models_indH_alt : M ⊧ₘ* Theory.indScheme L (Arith.Hierarchy Γ.alt s) := by
  simp [Theory.indH, Theory.indScheme]
  rintro _ p hp rfl
  simp [models_iff, succInd, Semiformula.eval_rew_q,
    Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton]
  intro v H0 Hsucc x
  have : Semiformula.Eval! M ![0] v p →
    (∀ x, Semiformula.Eval! M ![x] v p → Semiformula.Eval! M ![x + 1] v p) →
      ∀ x, Semiformula.Eval! M ![x] v p := by
    simpa using
      hierarchy_neg_induction Γ s (P := λ x ↦ ¬Semiformula.Eval! M ![x] v p)
        ⟨⟨~(Rew.rewriteMap v).hom p, by simpa using hp⟩,
          by intro x; simp [←Matrix.constant_eq_singleton', Semiformula.eval_rewriteMap]⟩
  exact this H0 Hsucc x

instance : (Theory.indScheme L (Arith.Hierarchy Γ.alt s)).Mod M := ⟨models_indH_alt Γ s⟩

lemma hierarchy_least_number {P : M → Prop} (hP : DefinablePred L Γ s P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using hierarchy_induction
    · exact Γ.alt
    · exact s
    · suffices DefinablePred L (Polarity.alt Γ) s fun z => ∀ w < z, ¬P w by exact this
      definability
    case zero => simp
    case succ x IH =>
      intro w hx hw
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hx) with (hx | rfl)
      · exact IH w hx hw
      · have : ∃ v < w, P v := A w hw
        rcases this with ⟨v, hvw, hv⟩
        exact IH v hvw hv
    case inst => exact inferInstance
    case inst => exact inferInstance
  exact this (x + 1) x (by simp) h

end neg

instance [(Theory.indScheme L (Arith.Hierarchy Σ s)).Mod M] :
    (Theory.indScheme L (Arith.Hierarchy Γ s)).Mod M := by
  rcases Γ
  · exact inferInstance
  · exact ⟨models_indH_alt Σ s⟩

end

def mod_iOpen_of_mod_indH (Γ s) [(𝐈𝐍𝐃Γ s).Mod M] : 𝐈open.Mod M :=
  Theory.Mod.of_ss (T₁ := 𝐈𝐍𝐃Γ s) M (Set.union_subset_union_right _ (Theory.indScheme_subset Hierarchy.of_open))

def mod_iSigma_of_le {s₁ s₂} (h : s₁ ≤ s₂) [(𝐈𝚺 s₂).Mod M] : (𝐈𝚺 s₁).Mod M :=
  Theory.Mod.of_ss M (Theory.iSigma_subset_mono h)

instance [𝐈open.Mod M] : 𝐏𝐀⁻.Mod M := Theory.Mod.of_add_left M 𝐏𝐀⁻ (Theory.indScheme _ Semiformula.Open)

instance [𝐈𝚺₀.Mod M] : 𝐈open.Mod M := mod_iOpen_of_mod_indH Σ 0

instance [𝐈𝚺₁.Mod M] : 𝐈𝚺₀.Mod M := mod_iSigma_of_le (show 0 ≤ 1 from by simp)

instance [(𝐈𝚺 ν).Mod M] : (𝐈𝐍𝐃 Γ ν).Mod M := by
  rcases Γ
  · exact inferInstance
  · haveI : 𝐏𝐀⁻.Mod M := Arith.mod_peanoMinus_of_mod_indH (Γ := Σ) (ν := ν)
    exact inferInstance

instance [(𝐈𝚷 ν).Mod M] : (𝐈𝚺 ν).Mod M :=
  haveI : 𝐏𝐀⁻.Mod M := Arith.mod_peanoMinus_of_mod_indH (Γ := Π) (ν := ν)
  Theory.Mod.of_models (by simpa [Theory.iPi] using models_indH_alt (M := M) Π ν)

@[elab_as_elim] lemma hierarchy_induction_oRing_sigma₀ [𝐈𝚺₀.Mod M]
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ Σ 0 P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := hierarchy_induction Σ 0 hP zero succ

@[elab_as_elim] lemma hierarchy_induction_oRing_sigma₁ [𝐈𝚺₁.Mod M]
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ Σ 1 P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := hierarchy_induction Σ 1 hP zero succ

@[elab_as_elim] lemma hierarchy_order_induction_oRing_sigma₀ [𝐈𝚺₀.Mod M]
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ Σ 0 P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  hierarchy_order_induction Σ 0 hP ind

@[elab_as_elim] lemma hierarchy_order_induction_oRing_sigma₁ [𝐈𝚺₁.Mod M]
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ Σ 1 P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  hierarchy_order_induction Σ 1 hP ind

lemma least_number_oRing_sigma₀ [𝐈𝚺₀.Mod M] {P : M → Prop} (hP : DefinablePred ℒₒᵣ Σ 0 P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  hierarchy_least_number Σ 0 hP h

end Model

end

end Arith

end LO.FirstOrder
