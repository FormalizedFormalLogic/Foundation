import Arithmetization.Basic.PeanoMinus

namespace LO.FirstOrder

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

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M]

section

variable [M ⊧ₘ* 𝐏𝐀⁻] {L : Language} [L.ORing] [Structure L M] [Structure.ORing L M] [Structure.Monotone L M]

section IndScheme

variable {C : Semiformula L ℕ 1 → Prop} [M ⊧ₘ* Theory.indScheme L C]

private lemma induction_eval {p : Semiformula L ℕ 1} (hp : C p) (v) :
    Semiformula.Evalm M ![0] v p →
    (∀ x, Semiformula.Evalm M ![x] v p → Semiformula.Evalm M ![x + 1] v p) →
    ∀ x, Semiformula.Evalm M ![x] v p := by
  have : M ⊧ₘ (∀ᶠ* succInd p) :=
    ModelsTheory.models (T := Theory.indScheme _ C) M (by simpa using Theory.mem_indScheme_of_mem hp)
  simp [models_iff, succInd, Semiformula.eval_substs,
    Semiformula.eval_rew_q Rew.toS, Function.comp, Matrix.constant_eq_singleton] at this
  exact this v

variable (L)

@[elab_as_elim]
lemma induction {P : M → Prop}
    (hP : ∃ e : ℕ → M, ∃ p : Semiformula L ℕ 1, C p ∧ ∀ x, P x ↔ Semiformula.Evalm M ![x] e p) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨e, p, Cp, hp⟩; simpa [←hp] using induction_eval (M := M) Cp e

end IndScheme

section neg

variable (Γ : Polarity) (m : ℕ) [M ⊧ₘ* Theory.indScheme L (Arith.Hierarchy Γ m)]

@[elab_as_elim]
lemma induction_h {P : M → Prop} (hP : DefinablePred L (Γ, m) P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (P := P) (C := Hierarchy Γ m) (L := L) (by
    rcases hP with ⟨p, hp⟩
    haveI : Inhabited M := Classical.inhabited_of_nonempty'
    exact ⟨p.val.fvEnumInv, (Rew.rewriteMap p.val.fvEnum).hom p.val, by simp [hp],
      by  intro x; simp [Semiformula.eval_rewriteMap]
          have : (Semiformula.Evalm M ![x] fun x => p.val.fvEnumInv (p.val.fvEnum x)) p.val ↔ (Semiformula.Evalm M ![x] id) p.val :=
            Semiformula.eval_iff_of_funEqOn _ (by intro x hx; simp [Semiformula.fvEnumInv_fvEnum hx])
          simp [this, hp.df.iff]⟩)
    zero succ

@[elab_as_elim]
lemma order_induction_h {P : M → Prop} (hP : DefinablePred L (Γ, m) P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using induction_h
  · exact Γ
  · exact m
  · suffices DefinablePred L (Γ, m) fun x => ∀ y < x, P y by exact this
    exact Definable.ball_lt₀ (L := L) (by simp) (hP.retraction ![0])
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => exact inferInstance
  case inst => exact inferInstance

private lemma neg_induction_h {P : M → Prop} (hP : DefinablePred L (Γ, m) P)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using induction_h
    · exact Γ
    · exact m
    · suffices DefinablePred L (Γ, m) fun x => x ≤ a → P (a - x) by exact this
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

lemma models_indScheme_alt : M ⊧ₘ* Theory.indScheme L (Arith.Hierarchy Γ.alt m) := by
  simp [Theory.indH, Theory.indScheme]
  rintro _ p hp rfl
  simp [models_iff, succInd, Semiformula.eval_rew_q,
    Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton]
  intro v H0 Hsucc x
  have : Semiformula.Evalm M ![0] v p →
    (∀ x, Semiformula.Evalm M ![x] v p → Semiformula.Evalm M ![x + 1] v p) →
      ∀ x, Semiformula.Evalm M ![x] v p := by
    simpa using
      neg_induction_h (L := L) Γ m (P := λ x ↦ ¬Semiformula.Evalm M ![x] v p)
        (.mkPolarity (~(Rew.rewriteMap v).hom p) (by simpa using hp)
        (by intro x; simp [←Matrix.constant_eq_singleton', Semiformula.eval_rewriteMap]))
  exact this H0 Hsucc x

instance : M ⊧ₘ* Theory.indScheme L (Arith.Hierarchy Γ.alt m) := models_indScheme_alt Γ m

lemma least_number_h {P : M → Prop} (hP : DefinablePred L (Γ, m) P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using induction_h
    · exact Γ.alt
    · exact m
    · suffices DefinablePred L (Γ.alt, m) fun z ↦ ∀ w < z, ¬P w by exact this
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

section

variable (L)

variable (Γ : SigmaPiDelta) (m : ℕ) [M ⊧ₘ* Theory.indScheme L (Arith.Hierarchy 𝚺 m)]

lemma induction_hh {P : M → Prop} (hP : DefinablePred L (Γ, m) P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  match Γ with
  | 𝚺 => induction_h 𝚺 m hP zero succ
  | 𝚷 =>
    haveI : M ⊧ₘ* Theory.indScheme L (Arith.Hierarchy 𝚷 m) := models_indScheme_alt 𝚺 m
    induction_h 𝚷 m hP zero succ
  | 𝚫 => induction_h 𝚺 m hP.of_delta zero succ

lemma order_induction_hh {P : M → Prop} (hP : DefinablePred L (Γ, m) P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  match Γ with
  | 𝚺 => order_induction_h 𝚺 m hP ind
  | 𝚷 =>
    haveI : M ⊧ₘ* Theory.indScheme L (Arith.Hierarchy 𝚷 m) := models_indScheme_alt 𝚺 m
    order_induction_h 𝚷 m hP ind
  | 𝚫 => order_induction_h 𝚺 m hP.of_delta ind

lemma least_number_hh {P : M → Prop} (hP : DefinablePred L (Γ, m) P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  match Γ with
  | 𝚺 => least_number_h 𝚺 m hP h
  | 𝚷 =>
    haveI : M ⊧ₘ* Theory.indScheme L (Arith.Hierarchy 𝚷 m) := models_indScheme_alt 𝚺 m
    least_number_h 𝚷 m hP h
  | 𝚫 => least_number_h 𝚺 m hP.of_delta h

end

instance [M ⊧ₘ* Theory.indScheme L (Arith.Hierarchy 𝚺 m)] :
    M ⊧ₘ* Theory.indScheme L (Arith.Hierarchy Γ m) := by
  rcases Γ
  · exact inferInstance
  · exact models_indScheme_alt 𝚺 m

end

def mod_iOpen_of_mod_indH (Γ n) [M ⊧ₘ* 𝐈𝐍𝐃Γ n] : M ⊧ₘ* 𝐈open :=
  ModelsTheory.of_ss (U := 𝐈𝐍𝐃Γ n) inferInstance
    (Set.union_subset_union_right _ (Theory.indScheme_subset Hierarchy.of_open))

def mod_iSigma_of_le {n₁ n₂} (h : n₁ ≤ n₂) [M ⊧ₘ* 𝐈𝚺 n₂] : M ⊧ₘ* 𝐈𝚺 n₁ :=
  ModelsTheory.of_ss inferInstance (Theory.iSigma_subset_mono h)

instance [M ⊧ₘ* 𝐈open] : M ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_add_left M 𝐏𝐀⁻ (Theory.indScheme _ Semiformula.Open)

instance [M ⊧ₘ* 𝐈𝚺₀] : M ⊧ₘ* 𝐈open := mod_iOpen_of_mod_indH 𝚺 0

instance [M ⊧ₘ* 𝐈𝚺₁] : M ⊧ₘ* 𝐈𝚺₀ := mod_iSigma_of_le (show 0 ≤ 1 from by simp)

instance [M ⊧ₘ* 𝐈𝚺 n] : M ⊧ₘ* 𝐈𝚷 n :=
  haveI : M ⊧ₘ* 𝐏𝐀⁻ := Arith.models_peanoMinus_of_models_indH 𝚺 n
  inferInstance

instance [M ⊧ₘ* 𝐈𝚷 n] : M ⊧ₘ* 𝐈𝚺 n :=
  haveI : M ⊧ₘ* 𝐏𝐀⁻ := Arith.models_peanoMinus_of_models_indH 𝚷 n
  by simp [*]; simpa [Theory.iPi] using models_indScheme_alt (L := ℒₒᵣ) (M := M) 𝚷 n

lemma models_iSigma_iff_models_iPi {n} : M ⊧ₘ* 𝐈𝚺 n ↔ M ⊧ₘ* 𝐈𝚷 n :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance [M ⊧ₘ* 𝐈𝚺 n] : M ⊧ₘ* 𝐈𝐍𝐃Γ n :=
  match Γ with
  | 𝚺 => inferInstance
  | 𝚷 => inferInstance

@[elab_as_elim] lemma induction_iSigmaZero [M ⊧ₘ* 𝐈𝚺₀]
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ 𝚺₀ P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction_h 𝚺 0 hP zero succ

@[elab_as_elim] lemma induction_iSigmaOne [M ⊧ₘ* 𝐈𝚺₁]
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ 𝚺₁ P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction_h 𝚺 1 hP zero succ

@[elab_as_elim] lemma induction_iPiOne [M ⊧ₘ* 𝐈𝚺₁]
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ 𝚷₁ P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction_h 𝚷 1 hP zero succ

@[elab_as_elim] lemma order_induction_iSigmaZero [M ⊧ₘ* 𝐈𝚺₀]
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ 𝚺₀ P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h 𝚺 0 hP ind

@[elab_as_elim] lemma order_induction_iSigmaOne [M ⊧ₘ* 𝐈𝚺₁]
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ 𝚺₁ P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h 𝚺 1 hP ind

@[elab_as_elim] lemma order_induction_piOne [M ⊧ₘ* 𝐈𝚺₁]
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ 𝚷₁ P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h 𝚷 1 hP ind

lemma least_number_iSigmaZero [M ⊧ₘ* 𝐈𝚺₀] {P : M → Prop} (hP : DefinablePred ℒₒᵣ 𝚺₀ P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  least_number_h 𝚺 0 hP h

@[elab_as_elim] lemma induction_h_iSigmaOne [M ⊧ₘ* 𝐈𝚺₁] (Γ)
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ (Γ, 1) P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction_hh ℒₒᵣ Γ 1 hP zero succ

@[elab_as_elim] lemma order_induction_h_iSigmaOne [M ⊧ₘ* 𝐈𝚺₁] (Γ)
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ (Γ, 1) P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := order_induction_hh ℒₒᵣ Γ 1 hP ind

end Model

end

end Arith

end LO.FirstOrder
