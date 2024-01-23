import Arithmetization.PAminus

namespace LO.FirstOrder

namespace Arith

namespace Theory

variable {L : Language} [L.ORing] {C C' : Semiformula L ℕ 1 → Prop}

lemma mem_IndScheme_of_mem {p : Semiformula L ℕ 1} (hp : C p) :
    ∀ᶠ* succInd p ∈ IndScheme C := by
  simp[IndScheme]; exact ⟨p, hp, rfl⟩

lemma mem_Iopen_of_qfree {p : Semiformula L ℕ 1} (hp : p.Open) :
    ∀ᶠ* succInd p ∈ IOpen L := by
  simp [IOpen]; exact ⟨p, hp, rfl⟩

lemma IndScheme_subset (h : ∀ {p : Semiformula L ℕ 1},  C p → C' p) : IndScheme C ⊆ IndScheme C' := by
  intro _; simp [IndScheme]; rintro p hp rfl; exact ⟨p, h hp, rfl⟩

variable (L)

abbrev IHierarchy (b : VType) (k : ℕ) : Theory L := IndScheme (Arith.Hierarchy b k)

notation "𝐈𝚪" => IHierarchy ℒₒᵣ

abbrev IPi (k : ℕ) : Theory L := IndScheme (Arith.Hierarchy Π k)

prefix:max "𝐈𝚷 " => ISigma ℒₒᵣ

abbrev ISigma₀ := ISigma L 0

notation "𝐈𝚺₀" => ISigma₀ ℒₒᵣ

abbrev ISigma₁ := ISigma L 1

notation "𝐈𝚺₁" => ISigma₁ ℒₒᵣ

abbrev IPi₀ := IPi L 0

notation "𝐈𝚷₀" => IPi₀ ℒₒᵣ

abbrev IPi₁ := IPi L 1

notation "𝐈𝚷₁" => IPi₁ ℒₒᵣ

end Theory

noncomputable section

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [𝐏𝐀⁻.Mod M]

namespace Model

section IndScheme

variable {C : Semiformula ℒₒᵣ ℕ 1 → Prop}
  [(Theory.IndScheme C).Mod M]

lemma induction_eval {p : Semiformula ℒₒᵣ ℕ 1} (hp : C p) (v) :
    Semiformula.Eval! M ![0] v p →
    (∀ x, Semiformula.Eval! M ![x] v p → Semiformula.Eval! M ![x + 1] v p) →
    ∀ x, Semiformula.Eval! M ![x] v p := by
  have : M ⊧ₘ (∀ᶠ* succInd p) :=
    Theory.Mod.models (T := Theory.IndScheme C) M (by simpa [Theory.IOpen] using Theory.mem_IndScheme_of_mem hp)
  simp [models_iff, succInd, Semiformula.eval_substs,
    Semiformula.eval_rew_q Rew.toS, Function.comp, Matrix.constant_eq_singleton] at this
  exact this v

@[elab_as_elim]
lemma induction {P : M → Prop}
    (hP : ∃ e : ℕ → M, ∃ p : Semiformula ℒₒᵣ ℕ 1, C p ∧ ∀ x, P x ↔ Semiformula.Eval! M ![x] e p) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨e, p, Cp, hp⟩; simpa [←hp] using induction_eval (M := M) Cp e

end IndScheme

section ISigma

section Theory

lemma iSigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈𝚺 s₁ ⊆ 𝐈𝚺 s₂ :=
  Theory.IndScheme_subset (fun H ↦ H.mono h)

def mod_IOpen_of_mod_IHierarchy (b s) [(𝐈𝚪 b s).Mod M] : 𝐈open.Mod M :=
  Theory.Mod.of_ss M (show 𝐈open ⊆ 𝐈𝚪 b s from Theory.IndScheme_subset Hierarchy.Open)

def mod_ISigma_of_le {s₁ s₂} (h : s₁ ≤ s₂) [(𝐈𝚺 s₂).Mod M] : (𝐈𝚺 s₁).Mod M :=
  Theory.Mod.of_ss M (iSigma_subset_mono h)

instance [𝐈𝚺₀.Mod M] : 𝐈open.Mod M := mod_IOpen_of_mod_IHierarchy Σ 0

instance [𝐈𝚺₁.Mod M] : 𝐈open.Mod M := mod_IOpen_of_mod_IHierarchy Σ 1

instance [𝐈𝚺₁.Mod M] : 𝐈𝚺₀.Mod M := mod_ISigma_of_le (show 0 ≤ 1 from by simp)

variable (b : VType) (s : ℕ) [(𝐈𝚪 b s).Mod M]

@[elab_as_elim]
lemma hierarchy_induction {P : M → Prop} (hP : DefinablePred b s P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (P := P) (C := Hierarchy b s) (by
    rcases hP with ⟨p, hp⟩
    haveI : Inhabited M := Classical.inhabited_of_nonempty'
    exact ⟨p.val.fvEnumInv', (Rew.rewriteMap p.val.fvEnum').hom p.val, by simp [hp],
      by  intro x; simp [Semiformula.eval_rewriteMap]
          have : (Semiformula.Eval! M ![x] fun x => p.val.fvEnumInv' (p.val.fvEnum' x)) p.val ↔ (Semiformula.Eval! M ![x] id) p.val :=
            Semiformula.eval_iff_of_funEqOn _ (by intro x hx; simp [Semiformula.fvEnumInv'_fvEnum' _ hx])
          simp [this, hp.eval]⟩)
    zero succ

@[elab_as_elim] lemma hierarchy_induction_sigma₀ [𝐈𝚺₀.Mod M] {P : M → Prop} (hP : DefinablePred Σ 0 P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := hierarchy_induction Σ 0 hP zero succ

@[elab_as_elim] lemma hierarchy_induction_sigma₁ [𝐈𝚺₁.Mod M] {P : M → Prop} (hP : DefinablePred Σ 1 P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := hierarchy_induction Σ 1 hP zero succ

@[elab_as_elim]
lemma hierarchy_order_induction {P : M → Prop} (hP : DefinablePred b s P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  suffices : ∀ x, ∀ y < x, P y
  · intro x; exact this (x + 1) x (by simp)
  intro x; induction x using hierarchy_induction
  · exact b
  · exact s
  · definability
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => exact inferInstance

@[elab_as_elim] lemma hierarchy_order_induction_sigma₀ [𝐈𝚺₀.Mod M] {P : M → Prop} (hP : DefinablePred Σ 0 P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := hierarchy_order_induction Σ 0 hP ind

@[elab_as_elim] lemma hierarchy_order_induction_sigma₁ [𝐈𝚺₁.Mod M] {P : M → Prop} (hP : DefinablePred Σ 1 P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := hierarchy_order_induction Σ 1 hP ind

lemma hierarchy_neg_induction {P : M → Prop} (hP : DefinablePred b s P)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using hierarchy_induction
    · exact b
    · exact s
    · definability
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

lemma models_IHierarchy_alt : M ⊧ₘ* 𝐈𝚪 b.alt s := by
  intro p
  simp [Theory.IHierarchy, Theory.IndScheme]
  rintro p hp rfl
  simp [models_iff, succInd, Semiformula.eval_rew_q,
    Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton]
  intro v H0 Hsucc x
  have : Semiformula.Eval! M ![0] v p →
    (∀ x, Semiformula.Eval! M ![x] v p → Semiformula.Eval! M ![x + 1] v p) →
      ∀ x, Semiformula.Eval! M ![x] v p := by
    simpa using
      hierarchy_neg_induction b s (P := λ x ↦ ¬Semiformula.Eval! M ![x] v p)
        ⟨⟨~(Rew.rewriteMap v).hom p, by simpa using hp⟩,
          by intro x; simp [←Matrix.constant_eq_singleton', Semiformula.eval_rewriteMap]⟩
  exact this H0 Hsucc x

def hierarchy_mod_alt : (𝐈𝚪 b.alt s).Mod M := ⟨models_IHierarchy_alt b s⟩

variable {b s}

instance [𝐈𝚺₀.Mod M] : 𝐈𝚷₀.Mod M := hierarchy_mod_alt Σ 0

instance [𝐈𝚷₀.Mod M] : 𝐈𝚺₀.Mod M := hierarchy_mod_alt Π 0

end Theory

end ISigma

end Model

end

end Arith

end LO.FirstOrder
