import Arithmetization.PAminus

namespace LO.FirstOrder

namespace Arith

namespace Theory

variable {L : Language} [L.ORing] {C C' : {n : ℕ} → (Semiformula L (Fin n) 1 → Prop)}

lemma mem_IndScheme_of_mem {p : Semiformula L (Fin n) 1} (hp : C p) :
    ∀ᵤ* succInd p ∈ IndScheme C := by
  simp[IndScheme, Formula.univClosure, Semiformula.univClosure_inj]
  exact ⟨n, p, hp, rfl⟩

lemma mem_Iopen_of_qfree {p : Semiformula L (Fin n) 1} (hp : p.Open) :
    ∀ᵤ* succInd p ∈ IOpen L := by
  simp[IndScheme, Formula.univClosure, Semiformula.univClosure_inj]
  exact ⟨n, p, hp, rfl⟩

lemma IndScheme_subset (h : ∀ {n} {p : Semiformula L (Fin n) 1},  C p → C' p) : IndScheme C ⊆ IndScheme C' := by
  intro _; simp [IndScheme]; rintro n p hp rfl; exact ⟨n, p, h hp, rfl⟩

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

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace Model

section IndScheme

variable {C : {n : ℕ} → (Semiformula ℒₒᵣ (Fin n) 1 → Prop)}
  [(Theory.IndScheme C).Mod M]

lemma induction_eval {n} {p : Semiformula ℒₒᵣ (Fin n) 1} (hp : C p) (v) :
    Semiformula.Eval! M ![0] v p →
    (∀ x, Semiformula.Eval! M ![x] v p → Semiformula.Eval! M ![x + 1] v p) →
    ∀ x, Semiformula.Eval! M ![x] v p := by
  have : M ⊧ₘ (∀ᵤ* succInd p) :=
    Theory.Mod.models (T := Theory.IndScheme C) M (by simpa [Theory.IOpen] using Theory.mem_IndScheme_of_mem hp)
  simp [models_iff, succInd, Semiformula.eval_substs,
    Semiformula.eval_rew_q Rew.toS, Function.comp, Matrix.constant_eq_singleton] at this
  exact this v

lemma induction {n} (P : (Fin n → M) → M → Prop)
    (hP : ∃ p : Semiformula ℒₒᵣ (Fin n) 1, C p ∧ ∀ v x, P v x ↔ Semiformula.Eval! M ![x] v p) (v) :
    P v 0 → (∀ x, P v x → P v (x + 1)) → ∀ x, P v x := by
  rcases hP with ⟨p, Cp, hp⟩; simpa [hp] using induction_eval Cp v

lemma induction₀ {P : M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ (Fin 0) 1, C p ∧ ∀ x, P x ↔ Semiformula.Eval! M ![x] ![] p) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨p, Cp, hp⟩
  exact induction (C := C) (n := 0) (fun _ x ↦ P x) ⟨p, Cp, fun _ x ↦ by simpa [Matrix.empty_eq] using hp x ⟩ ![]

lemma induction₁ {P : M → M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ (Fin 1) 1, C p ∧ ∀ x a, P a x ↔ Semiformula.Eval! M ![x] ![a] p) (a) :
    P a 0 → (∀ x, P a x → P a (x + 1)) → ∀ x, P a x := by
  rcases hP with ⟨p, Cp, hp⟩
  exact induction (C := C) (n := 1) (fun v x ↦ P (v 0) x)
    ⟨p, Cp, fun v x ↦ by simpa [Matrix.constant_eq_singleton, ←Matrix.constant_eq_singleton'] using hp x (v 0) ⟩ ![a]

lemma induction₂ {P : M → M → M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ (Fin 2) 1, C p ∧ ∀ x a b, P a b x ↔ Semiformula.Eval! M ![x] ![a, b] p) (a b) :
    P a b 0 → (∀ x, P a b x → P a b (x + 1)) → ∀ x, P a b x := by
  rcases hP with ⟨p, Cp, hp⟩
  exact induction (C := C) (n := 2) (fun v x ↦ P (v 0) (v 1) x)
    ⟨p, Cp, fun v x ↦ by simpa [Matrix.constant_eq_singleton, ←Matrix.fun_eq_vec₂] using hp x (v 0) (v 1) ⟩ ![a, b]

lemma induction₃ {P : M → M → M → M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ (Fin 3) 1, C p ∧ ∀ x a b c, P a b c x ↔ Semiformula.Eval! M ![x] ![a, b, c] p) (a b c) :
    P a b c 0 → (∀ x, P a b c x → P a b c (x + 1)) → ∀ x, P a b c x := by
  rcases hP with ⟨p, Cp, hp⟩
  exact induction (C := C) (n := 3) (fun v x ↦ P (v 0) (v 1) (v 2) x)
    ⟨p, Cp, fun v x ↦ by simpa [Matrix.constant_eq_singleton, ←Matrix.fun_eq_vec₃] using hp x (v 0) (v 1) (v 2)⟩ ![a, b, c]

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

variable (M)
variable (b : VType) (s : ℕ) [(𝐈𝚪 b s).Mod M]

lemma hierarchy_induction {n} (P : (Fin n → M) → M → Prop)
    (hP : ∃ p : Semisentence ℒₒᵣ (n + 1), Hierarchy b s p ∧ ∀ v x, P v x ↔ Semiformula.PVal! M (x :> v) p) (v) :
    P v 0 → (∀ x, P v x → P v (x + 1)) → ∀ x, P v x :=
  induction P (C := Hierarchy b s) (by
    rcases hP with ⟨p, hp, hp_iff⟩
    exact ⟨(Rew.bind (#0 :> (&·)) Empty.elim).hom p, by simp [hp],
      by intro v x; simp [Semiformula.eval_rew, Function.comp, Matrix.comp_vecCons', Empty.eq_elim, hp_iff]⟩) v

lemma hierarchy_induction₀ (P : M → Prop)
    (hP : ∃ p : SentenceHierarchy b s ℒₒᵣ 1, DefinedPred b s P p) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨p, hp⟩
  exact hierarchy_induction M b s (n := 0) (fun _ x ↦ P x)
    ⟨(Rew.rewrite Empty.elim).hom p.val, by simp,
     by intro v x; simp [Semiformula.eval_rewrite, Empty.eq_elim, hp.pval]⟩ ![]

lemma hierarchy_order_induction {n} (P : (Fin n → M) → M → Prop)
    (hP : ∃ p, Hierarchy (L := ℒₒᵣ) b s p ∧ ∀ v x, P v x ↔ Semiformula.Eval! M ![x] v p) (v) :
    (∀ x, (∀ y < x, P v y) → P v x) → ∀ x, P v x := by
  intro H
  rcases hP with ⟨p, hp, hp_iff⟩
  have : (∀ y < 0, P v y) → (∀ x, (∀ y < x, P v y) → ∀ y < x + 1, P v y) → ∀ x, ∀ y < x, P v y :=
    induction (λ v x ↦ ∀ y < x, P v y) (C := Hierarchy b s)
      ⟨“∀[#0 < #1] !p [#0]”, by simp [hp],
       λ v x ↦ by simp [Semiformula.eval_substs, Matrix.constant_eq_singleton, ←hp_iff]⟩ v
  have : ∀ x, ∀ y < x, P v y := this (by simp) (by
    intro x hx y hy
    have : y ≤ x := le_iff_lt_succ.mpr hy
    rcases show y < x ∨ y = x from lt_or_eq_of_le this  with (lt | rfl)
    · exact hx y lt
    · exact H y hx)
  intro x; exact this (x + 1) x (lt_add_one x)

lemma hierarchy_order_induction₀ (P : M → Prop)
    (hP : ∃ p : SentenceHierarchy b s ℒₒᵣ 1, DefinedPred b s P p) :
    (∀ x, (∀ y < x, P y) → P x) → ∀ x, P x := by
  rcases hP with ⟨p, hp⟩
  exact hierarchy_order_induction M b s (n := 0) (fun _ x ↦ P x)
    ⟨(Rew.rewrite Empty.elim).hom p.val, by simp,
     by intro v x; simp [Semiformula.eval_rewrite, Empty.eq_elim, hp.pval]⟩ ![]

lemma hierarchy_order_induction₁ (P : M → M → Prop)
    (hP : ∃ p : SentenceHierarchy b s ℒₒᵣ 2, DefinedRel b s P p) (a) :
    (∀ x, (∀ y < x, P a y) → P a x) → ∀ x, P a x := by
  rcases hP with ⟨p, hp⟩
  exact hierarchy_order_induction M b s (n := 1) (fun v x ↦ P (v 0) x)
    ⟨(Rew.bind ![&0, #0] Empty.elim).hom p.val, by simp,
     by intro v x; simp [Semiformula.eval_rew, Empty.eq_elim, hp.pval]⟩ ![a]

lemma hierarchy_order_induction₂ (P : M → M → M → Prop)
    (hP : ∃ p : SentenceHierarchy b s ℒₒᵣ 3, Arith.Defined b s (λ v ↦ P (v 0) (v 1) (v 2)) p) (a₁ a₂) :
    (∀ x, (∀ y < x, P a₁ a₂ y) → P a₁ a₂ x) → ∀ x, P a₁ a₂ x := by
  rcases hP with ⟨p, hp⟩
  simpa using hierarchy_order_induction M b s (n := 2) (fun v x ↦ P (v 0) (v 1) x)
    ⟨(Rew.bind ![&0, &1, #0] Empty.elim).hom p.val, by simp,
     by intro v x; simp [Semiformula.eval_rew, Empty.eq_elim, hp.pval]⟩ ![a₁, a₂]

lemma hierarchy_order_induction₃ (P : M → M → M → M → Prop)
    (hP : ∃ p : SentenceHierarchy b s ℒₒᵣ 4, Arith.Defined b s (λ v ↦ P (v 0) (v 1) (v 2) (v 3)) p) (a₁ a₂ a₃) :
    (∀ x, (∀ y < x, P a₁ a₂ a₃ y) → P a₁ a₂ a₃ x) → ∀ x, P a₁ a₂ a₃ x := by
  rcases hP with ⟨p, hp⟩
  simpa using hierarchy_order_induction M b s (n := 3) (fun v x ↦ P (v 0) (v 1) (v 2) x)
    ⟨(Rew.bind ![&0, &1, &2, #0] Empty.elim).hom p.val, by simp,
     by intro v x; simp [Semiformula.eval_rew, Empty.eq_elim, hp.pval]⟩ ![a₁, a₂, a₃]

lemma hierarchy_neg_induction {n} (P : (Fin n → M) → M → Prop)
    (hP : ∃ p : Semisentence ℒₒᵣ (n + 1), Hierarchy b s p ∧ ∀ v x, P v x ↔ Semiformula.PVal! M (x :> v) p) (v) :
    ¬P v 0 → (∀ x, ¬P v x → ¬P v (x + 1)) → ∀ x, ¬P v x := by
  intro H0 Hsucc x hx
  have := hierarchy_induction M b s (λ v x ↦ x ≤ v 0 → P (Matrix.vecTail v) (v 0 ∸ x))
    (by rcases hP with ⟨p, hp, hp_iff⟩
        exact ⟨“#0 ≤ #1 → ∃[#0 < #2 + 1] (!msubdef [#0, #2, #1] ∧ !((Rew.substs (#0 :> (#·.succ.succ.succ))).hom p))”,
          by simp [hp],
          by intro v x
             simp [Matrix.vecHead, Matrix.vecTail, Semiformula.eval_substs, Function.comp,
               Matrix.comp_vecCons', Matrix.constant_eq_singleton, ←hp_iff, msub_defined.pval]
             apply imp_congr_right; intro _
             exact ⟨by intro H; exact ⟨v 0 ∸ x, by simp [H, ←le_iff_lt_succ]⟩,
                    by rintro ⟨r, _, rfl, H⟩; exact H⟩⟩) (x :> v)
  simp at this
  have : P v x →
    (∀ y, (y ≤ x → P v (x ∸ y)) → y + 1 ≤ x → P v (x ∸ (y + 1))) →
    ∀ y ≤ x, P v (x ∸ y) := by simpa using this
  have : ∀ y ≤ x, P v (x ∸ y) := this hx (by
    intro y hy le; simp [←msub_msub]
    by_contra hs
    exact Hsucc _ hs (by
      rw [msub_add_self_of_le]
      · exact hy (le_of_add_le_left le)
      exact pos_iff_one_le.mp (pos_msub_iff_lt.mpr $ lt_iff_succ_le.mpr le)))
  have : P v 0 := by simpa using this x (by rfl)
  contradiction

lemma models_IHierarchy_alt : M ⊧ₘ* 𝐈𝚪 b.alt s := by
  intro p
  simp [Theory.IHierarchy, Theory.IndScheme]
  rintro n p hp rfl
  simp [models_iff, Formula.univClosure, succInd, Semiformula.eval_rew_q,
    Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton]
  intro v H0 Hsucc x
  have : Semiformula.Eval! M ![0] v p →
    (∀ x, Semiformula.Eval! M ![x] v p → Semiformula.Eval! M ![x + 1] v p) →
      ∀ x, Semiformula.Eval! M ![x] v p := by
    simpa using
      hierarchy_neg_induction M b s (λ v x ↦ ¬Semiformula.Eval! M ![x] v p)
        ⟨~(Rew.bind ![#0] (#·.succ)).hom p, by simp [hp],
          by intro v x; simp [Semiformula.eval_rew, Function.comp, Matrix.constant_eq_singleton]⟩ v
  exact this H0 Hsucc x

def hierarchy_mod_alt : (𝐈𝚪 b.alt s).Mod M := ⟨models_IHierarchy_alt M b s⟩

variable {M b s}

instance [𝐈𝚺₀.Mod M] : 𝐈𝚷₀.Mod M := hierarchy_mod_alt M Σ 0

instance [𝐈𝚷₀.Mod M] : 𝐈𝚺₀.Mod M := hierarchy_mod_alt M Π 0

end Theory

end ISigma

end Model

end

end Arith

end LO.FirstOrder
