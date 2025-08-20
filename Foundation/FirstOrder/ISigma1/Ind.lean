import Foundation.FirstOrder.ISigma1.HFS

/-!
# Various induction-related principles in $\mathsf{I}\Sigma_n$
-/

namespace LO.ISigma1

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

@[elab_as_elim] lemma sigma1_pos_succ_induction
    {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (zero : P 0) (one : P 1) (succ : ∀ x, P (x + 1) → P (x + 2)) : ∀ x, P x := by
  have : ∀ x, P (x + 1) := by
    intro x
    induction x using ISigma1.sigma1_succ_induction
    · definability
    case zero => simpa
    case succ x ih =>
      simpa [add_assoc, one_add_one_eq_two] using succ x ih
  intro x
  rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
  · exact zero
  · exact this x

open HierarchySymbol

theorem bounded_all_sigma1_order_induction {f : V → V → V} (hf : 𝚺₁-Function₂ f) {P : V → V → Prop} (hP : 𝚺₁-Relation P)
    (ind : ∀ x y, (∀ x' < x, ∀ y' ≤ f x y, P x' y') → P x y) : ∀ x y, P x y := by
  have maxf : ∀ x y, ∃ m, ∀ x' ≤ x, ∀ y' ≤ y, f x' y' ≤ m := by
    intro x y
    rcases sigma₁_replacement₂ hf (under (x + 1)) (under (y + 1)) |>.exists with ⟨m, hm⟩
    exact ⟨m, fun x' hx' y' hy' ↦
      le_of_lt <| lt_of_mem <| hm (f x' y') |>.mpr
        ⟨x', by simpa [lt_succ_iff_le] using hx', y', by simpa [lt_succ_iff_le] using hy', rfl⟩⟩
  intro x y
  have : ∀ k ≤ x, ∃ W, Seq W ∧ k + 1 = lh W ∧
      ⟪0, y⟫ ∈ W ∧
      ∀ l < k, ∀ m < W, ∀ m' < W, ⟪l, m⟫ ∈ W → ⟪l + 1, m'⟫ ∈ W → ∀ x' ≤ x - l, ∀ y' ≤ m, f x' y' ≤ m' := by
    intro k hk
    induction k using ISigma1.sigma1_succ_induction
    · apply Boldface.imp (Boldface.comp₂ (by definability) (by definability))
      apply Boldface.ex
      apply Boldface.and (Boldface.comp₁ (by definability))
      apply Boldface.and
        (Boldface.comp₂
          (BoldfaceFunction.comp₂ (.var _) (.const _))
          (BoldfaceFunction.comp₁ (.var _)))
      apply Boldface.and
        (Boldface.comp₂ (.var 0) (by definability))
      apply Boldface.ball_lt (.var _)
      apply Boldface.ball_lt (.var _)
      apply Boldface.ball_lt (.var _)
      apply Boldface.imp
        (Boldface.comp₂ (.var _) (BoldfaceFunction.comp₂ (.var _) (.var _)))
      apply Boldface.imp
        (Boldface.comp₂ (.var _) (BoldfaceFunction.comp₂ (BoldfaceFunction.comp₂ (.var _) (.const _)) (.var _)))
      apply Boldface.ball_le
        (Boldface.comp₂
          (.var _)
          (BoldfaceFunction.comp₂ (.const _) (.var _)))
      apply Boldface.ball_le (.var _)
      apply Boldface.comp₂
        (BoldfaceFunction.comp₂
          (.var _) (.var _)) (.var _)
    case zero => exact ⟨!⟦y⟧, by simp⟩
    case succ k ih =>
      rcases ih (le_trans le_self_add hk) with ⟨W, SW, hkW, hW₀, hWₛ⟩
      let m₀ := SW.nth (show k < lh W by simp [←hkW])
      have : ∃ m₁, ∀ x' ≤ x - k, ∀ y' ≤ m₀, f x' y' ≤ m₁ := maxf (x - k) m₀
      rcases this with ⟨m₁, hm₁⟩
      exact ⟨W ⁀' m₁, SW.seqCons m₁, by simp [SW, hkW], Seq.subset_seqCons _ _ hW₀, by
        intro l hl m _ m' _ hm hm' x' hx' y' hy'
        rcases show l ≤ k from lt_succ_iff_le.mp hl with (rfl | hl)
        · have hmm₀ : m = m₀ :=
            SW.isMapping.uniq (by simpa [mem_seqCons_iff, ←hkW] using hm) (by simp [m₀])
          have hm'm₁ : m' = m₁ := by
            simpa [SW, hkW, mem_seqCons_iff] using hm'
          simpa [hm'm₁] using hm₁ x' hx' y' (by simp [←hmm₀, hy'])
        · have Hm : ⟪l, m⟫ ∈ W := Seq.mem_seqCons_iff_of_lt (by simpa [←hkW]) |>.mp hm
          have Hm' : ⟪l + 1, m'⟫ ∈ W := Seq.mem_seqCons_iff_of_lt (by simpa [←hkW]) |>.mp hm'
          exact hWₛ l hl m (lt_of_mem_rng Hm) m' (lt_of_mem_rng Hm') Hm Hm' x' hx' y' hy'⟩
  rcases this x (by rfl) with ⟨W, SW, hxW, hW₀, hWₛ⟩
  have : ∀ i ≤ x, ∀ m < W, ⟪x - i, m⟫ ∈ W → ∀ x' ≤ i, ∀ y' ≤ m, P x' y' := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · apply Boldface.imp
        (Boldface.comp₂ (.var _) (.const _))
      apply Boldface.ball_lt (.const _)
      apply Boldface.imp
        (Boldface.comp₂
          (.const _)
          (BoldfaceFunction.comp₂
            (BoldfaceFunction.comp₂
              (.const _) (.var _)) (.var _)))
      apply Boldface.ball_le (.var _)
      apply Boldface.ball_le (.var _)
      apply Boldface.comp₂ (.var _) (.var _)
    case zero =>
      intro _ _ _ _ _ h y' _
      rcases nonpos_iff_eq_zero.mp h
      exact ind 0 y' (by simp)
    case succ i ih' =>
      intro hi m _ hm x' hx' y' hy'
      have ih : ∀ m < W, ⟪x - i, m⟫ ∈ W → ∀ x' ≤ i, ∀ y' ≤ m, P x' y' := ih' (le_trans le_self_add hi)
      refine ind x' y' ?_
      intro x'' hx'' y'' hy''
      let m₁ := SW.nth (show x - i < lh W by simp [←hxW, lt_succ_iff_le])
      have : f x' y' ≤ m₁ :=
        hWₛ (x - (i + 1)) (tsub_lt_iff_left hi |>.mpr (by simp)) m (lt_of_mem_rng hm) m₁ (by simp [m₁]) hm
          (by rw [←PeanoMinus.sub_sub, sub_add_self_of_le (show 1 ≤ x - i from le_tsub_of_add_le_left hi)]; simp [m₁])
          x' (by simp [tsub_tsub_cancel_of_le hi, hx']) y' hy'
      exact ih m₁ (by simp [m₁]) (by simp [m₁]) x'' (lt_succ_iff_le.mp (lt_of_lt_of_le hx'' hx')) y'' (le_trans hy'' this)
  exact this x (by rfl) y (lt_of_mem_rng hW₀) (by simpa using hW₀) x (by rfl) y (by rfl)

lemma bounded_all_sigma1_order_induction' {f : V → V} (hf : 𝚺₁-Function₁ f) {P : V → V → Prop} (hP : 𝚺₁-Relation P)
    (ind : ∀ x y, (∀ x' < x, ∀ y' ≤ f y, P x' y') → P x y) : ∀ x y, P x y :=
  have : 𝚺₁-Function₂ (fun _ ↦ f) := BoldfaceFunction.comp₁ (by simp)
  bounded_all_sigma1_order_induction this hP ind

lemma bounded_all_sigma1_order_induction₂ {fy fz : V → V → V → V}
    (hfy : 𝚺₁-Function₃ fy) (hfz : 𝚺₁-Function₃ fz) {P : V → V → V → Prop} (hP : 𝚺₁-Relation₃ P)
    (ind : ∀ x y z, (∀ x' < x, ∀ y' ≤ fy x y z, ∀ z' ≤ fz x y z, P x' y' z') → P x y z) :
    ∀ x y z, P x y z := by
  let Q : V → V → Prop := fun x w ↦ P x (π₁ w) (π₂ w)
  have hQ : 𝚺₁-Relation Q := by
    apply Boldface.comp₃ (.var _)
      (BoldfaceFunction.comp₁ (.var _))
      (BoldfaceFunction.comp₁ (.var _))
  let f : V → V → V := fun x w ↦ ⟪fy x (π₁ w) (π₂ w), fz x (π₁ w) (π₂ w)⟫
  have hf : 𝚺₁-Function₂ f := by
    simp only [f]
    apply BoldfaceFunction.comp₂
    · apply BoldfaceFunction.comp₃ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
    · apply BoldfaceFunction.comp₃ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
  intro x y z
  simpa [Q] using bounded_all_sigma1_order_induction hf hQ (fun x w ih ↦
    ind x (π₁ w) (π₂ w) (fun x' hx' y' hy' z' hz' ↦ by simpa [Q] using ih x' hx' ⟪y', z'⟫ (pair_le_pair hy' hz')))
    x ⟪y, z⟫

lemma bounded_all_sigma1_order_induction₃ {fy fz fw : V → V → V → V → V}
    (hfy : 𝚺₁-Function₄ fy) (hfz : 𝚺₁-Function₄ fz) (hfw : 𝚺₁-Function₄ fw) {P : V → V → V → V → Prop} (hP : 𝚺₁-Relation₄ P)
    (ind : ∀ x y z w, (∀ x' < x, ∀ y' ≤ fy x y z w, ∀ z' ≤ fz x y z w, ∀ w' ≤ fw x y z w, P x' y' z' w') → P x y z w) :
    ∀ x y z w, P x y z w := by
  let Q : V → V → Prop := fun x v ↦ P x (π₁ v) (π₁ (π₂ v)) (π₂ (π₂ v))
  have hQ : 𝚺₁-Relation Q := by
    apply Boldface.comp₄
      (.var _)
      (BoldfaceFunction.comp₁ <| .var _)
      (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
      (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
  let f : V → V → V := fun x v ↦
    ⟪fy x (π₁ v) (π₁ (π₂ v)) (π₂ (π₂ v)), fz x (π₁ v) (π₁ (π₂ v)) (π₂ (π₂ v)), fw x (π₁ v) (π₁ (π₂ v)) (π₂ (π₂ v))⟫
  have hf : 𝚺₁-Function₂ f := by
    simp only [f]
    apply BoldfaceFunction.comp₂
    · apply BoldfaceFunction.comp₄
        (.var _)
        (BoldfaceFunction.comp₁ <| .var _)
        (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
        (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
    · apply BoldfaceFunction.comp₂
      · apply BoldfaceFunction.comp₄
          (.var _)
          (BoldfaceFunction.comp₁ <| .var _)
          (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
          (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
      · apply BoldfaceFunction.comp₄
          (.var _)
          (BoldfaceFunction.comp₁ <| .var _)
          (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
          (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
  intro x y z w
  have := bounded_all_sigma1_order_induction hf hQ (fun x v ih ↦
    ind x (π₁ v) (π₁ (π₂ v)) (π₂ (π₂ v)) (fun x' hx' y' hy' z' hz' w' hw' ↦ by
      simpa [Q] using ih x' hx' ⟪y', z', w'⟫ (pair_le_pair hy' <| pair_le_pair hz' hw')))
    x ⟪y, z, w⟫
  simpa [Q] using this

lemma measured_bounded_sigma1_order_induction {m : V → V} {f : V → V} {P : V → Prop}
    (hm : 𝚺₁-Function₁ m) (hf : 𝚺₁-Function₁ f) (hP : 𝚺₁-Predicate P)
    (H : ∀ a, (∀ b ≤ f a, m b < m a → P b) → P a) : ∀ a, P a := by
  let Q : V → V → Prop := fun k x ↦ m x ≤ k → P x
  have hQ : 𝚺₁-Relation Q := by unfold Q; definability
  have : ∀ x y, Q x y := bounded_all_sigma1_order_induction' hf hQ fun k a ih hm ↦
    H a fun b hb hba ↦ ih (m b) (lt_of_le_of_lt' hm hba) b hb (by rfl)
  intro a
  exact this (m a) a (by rfl)

end LO.ISigma1

namespace LO.Induction

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1

variable {V : Type*} [ORingStruc V]

variable (m : ℕ) [Fact (1 ≤ m)] [V ⊧ₘ* 𝐈𝐍𝐃𝚺 m]

lemma sigma_or_pi_succ_induction {P Q : V → Prop} (hP : 𝚺-[m]-Predicate P) (hQ : 𝚷-[m]-Predicate Q)
    (zero : P 0 ∨ Q 0) (succ : ∀ x, P x ∨ Q x → P (x + 1) ∨ Q (x + 1)) : ∀ x, P x ∨ Q x := by
  haveI : V ⊧ₘ* 𝐈𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  intro a
  have : ∃ p < Exp.exp (a + 1), ∀ x ≤ a, x ∈ p ↔ P x := by
    simpa [lt_succ_iff_le] using finset_comprehension hP (a + 1)
  rcases this with ⟨p, _, hp⟩
  have : ∃ q < Exp.exp (a + 1), ∀ x ≤ a, x ∈ q ↔ Q x := by
    simpa [lt_succ_iff_le] using finset_comprehension hQ (a + 1)
  rcases this with ⟨q, _, hq⟩
  have : ∀ x ≤ a, x ∈ p ∨ x ∈ q := by
    intro x hx
    induction x using ISigma1.sigma1_succ_induction
    · clear hp hq zero succ
      definability
    case zero => simpa [hp, hq] using zero
    case succ x ih =>
      have hx' : x ≤ a := le_trans le_self_add hx
      have : P x ∨ Q x := by simpa [hp x hx', hq x hx'] using ih hx'
      simpa [hp (x + 1) hx, hq (x + 1) hx] using succ x this
  have := this a (by rfl)
  simpa [hp, hq] using this

lemma sigma_or_pi_order_induction {P Q : V → Prop} (hP : 𝚺-[m]-Predicate P) (hQ : 𝚷-[m]-Predicate Q)
    (ind : ∀ x, (∀ y < x, P y ∨ Q y) → P x ∨ Q x) : ∀ x, P x ∨ Q x := by
  haveI : V ⊧ₘ* 𝐈𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  intro a
  have : ∃ p < Exp.exp (a + 1), ∀ x ≤ a, x ∈ p ↔ P x := by
    simpa [lt_succ_iff_le] using finset_comprehension hP (a + 1)
  rcases this with ⟨p, _, hp⟩
  have : ∃ q < Exp.exp (a + 1), ∀ x ≤ a, x ∈ q ↔ Q x := by
    simpa [lt_succ_iff_le] using finset_comprehension hQ (a + 1)
  rcases this with ⟨q, _, hq⟩
  have : ∀ x ≤ a, x ∈ p ∨ x ∈ q := by
    intro x hx
    induction x using ISigma1.sigma1_order_induction
    · clear hp hq ind
      apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.imp
      · simp_all only [SigmaPiDelta.alt_sigma, Fin.isValue]
        apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.comp₂
        · simp [Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
        · simp [HierarchySymbol.BoldfaceFunction.const]
      · apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.or
        · apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.comp₂
          · simp
          · simp
        · apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.comp₂
          · simp
          · simp
    case ind z ih =>
      have : P z ∨ Q z :=
        ind z (fun y hy ↦ by
          have hya : y ≤ a := le_trans (le_of_lt hy) hx
          have : y ∈ p ∨ y ∈ q := ih y hy hya
          simpa [hp, hq, hya] using this)
      simpa [hp, hq, hx] using this
  simpa [hp, hq] using this a (by rfl)

end LO.Induction
