import Arithmetization.PAminus

namespace LO.FirstOrder

namespace Arith

namespace Theory

variable {L : Language} [L.ORing] {C : {n : ℕ} → Set (Semiformula L (Fin n) 1)}

lemma mem_IndScheme_of_mem {p : Semiformula L (Fin n) 1} (hp : p ∈ C) :
    ∀ᵤ* succInd p ∈ IndScheme C := by
  simp[IndScheme, Formula.univClosure, Semiformula.univClosure_inj]
  exact ⟨n, p, hp, rfl⟩

lemma mem_Iopen_of_qfree {p : Semiformula L (Fin n) 1} (hp : p.qfree) :
    ∀ᵤ* succInd p ∈ IndSchemeOpen L := by
  simp[IndScheme, Formula.univClosure, Semiformula.univClosure_inj]
  exact ⟨n, p, hp, rfl⟩

end Theory

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

open PAminus.Model

namespace IndScheme.Model

variable {C : {n : ℕ} → Set (Semiformula ℒₒᵣ (Fin n) 1)}
  [(Theory.IndScheme C).Mod M]

lemma induction_eval {n} {p : Semiformula ℒₒᵣ (Fin n) 1} (hp : p ∈ C) (v) :
    Semiformula.Eval! M ![0] v p →
    (∀ x, Semiformula.Eval! M ![x] v p → Semiformula.Eval! M ![x + 1] v p) →
    ∀ x, Semiformula.Eval! M ![x] v p := by
  have : M ⊧ₘ (∀ᵤ* succInd p) := Theory.Mod.models (T := Theory.IndScheme C) M (by simpa [Theory.IndSchemeOpen] using Theory.mem_IndScheme_of_mem hp)
  simp [models_iff, succInd, Semiformula.eval_substs, Semiformula.eval_rew_q Rew.toS, Function.comp, Matrix.constant_eq_singleton] at this
  exact this v

lemma induction {n} (P : (Fin n → M) → M → Prop) (hP : ∃ p ∈ @C n, ∀ v x, P v x ↔ Semiformula.Eval! M ![x] v p) (v) :
    P v 0 → (∀ x, P v x → P v (x + 1)) → ∀ x, P v x := by
  rcases hP with ⟨p, Cp, hp⟩; simpa [hp] using induction_eval Cp v

lemma induction₀ {P : M → Prop}
    (hP : ∃ p ∈ @C 0, ∀ x, P x ↔ Semiformula.Eval! M ![x] ![] p) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨p, Cp, hp⟩
  exact induction (C := C) (n := 0) (fun _ x ↦ P x) ⟨p, Cp, fun _ x ↦ by simpa [Matrix.empty_eq] using hp x ⟩ ![]

lemma induction₁ {P : M → M → Prop}
    (hP : ∃ p ∈ @C 1, ∀ x y, P y x ↔ Semiformula.Eval! M ![x] ![y] p) (y) :
    P y 0 → (∀ x, P y x → P y (x + 1)) → ∀ x, P y x := by
  rcases hP with ⟨p, Cp, hp⟩
  exact induction (C := C) (n := 1) (fun v x ↦ P (v 0) x)
    ⟨p, Cp, fun v x ↦ by simpa [Matrix.constant_eq_singleton, ←Matrix.constant_eq_singleton'] using hp x (v 0) ⟩ ![y]

lemma induction₂ {P : M → M → M → Prop}
    (hP : ∃ p ∈ @C 2, ∀ x y z, P z y x ↔ Semiformula.Eval! M ![x] ![y, z] p) (z y) :
    P z y 0 → (∀ x, P z y x → P z y (x + 1)) → ∀ x, P z y x := by
  rcases hP with ⟨p, Cp, hp⟩
  exact induction (C := C) (n := 2) (fun v x ↦ P (v 1) (v 0) x)
    ⟨p, Cp, fun v x ↦ by simpa [Matrix.constant_eq_singleton, ←Matrix.fun_eq_vec₂] using hp x (v 0) (v 1) ⟩ ![y, z]

lemma induction₃ {P : M → M → M → M → Prop}
    (hP : ∃ p ∈ @C 3, ∀ x y z w, P w z y x ↔ Semiformula.Eval! M ![x] ![y, z, w] p) (w z y) :
    P w z y 0 → (∀ x, P w z y x → P w z y (x + 1)) → ∀ x, P w z y x := by
  rcases hP with ⟨p, Cp, hp⟩
  exact induction (C := C) (n := 3) (fun v x ↦ P (v 2) (v 1) (v 0) x)
    ⟨p, Cp, fun v x ↦ by simpa [Matrix.constant_eq_singleton, ←Matrix.fun_eq_vec₃] using hp x (v 0) (v 1) (v 2)⟩ ![y, z, w]

lemma induction₄ {P : M → M → M → M → M → Prop}
    (hP : ∃ p ∈ @C 4, ∀ x y z w v, P v w z y x ↔ Semiformula.Eval! M ![x] ![y, z, w, v] p) (v w z y) :
    P v w z y 0 → (∀ x, P v w z y x → P v w z y (x + 1)) → ∀ x, P v w z y x := by
  rcases hP with ⟨p, Cp, hp⟩
  exact induction (C := C) (n := 4) (fun v x ↦ P (v 3) (v 2) (v 1) (v 0) x)
    ⟨p, Cp, fun v x ↦ by simpa [Matrix.constant_eq_singleton, ←Matrix.fun_eq_vec₄] using hp x (v 0) (v 1) (v 2) (v 3)⟩ ![y, z, w, v]

end IndScheme.Model

namespace IOpen.Model

variable [𝐈open.Mod M]

lemma induction₂ {P : M → M → M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ (Fin 2) 1, p.qfree ∧ (∀ x y z, P z y x ↔ Semiformula.Eval! M ![x] ![y, z] p)) (z y) :
    P z y 0 → (∀ x, P z y x → P z y (x + 1)) → ∀ x, P z y x :=
  IndScheme.Model.induction₂ (C := Semiformula.qfree) (by simpa) z y

lemma remainder (x : M) {y} (hy : 0 < y) : ∃! u, ∃ v < y, x = y * u + v := by
  have : ∃! u, y * u ≤ x ∧ x < y * (u + 1) := by
    have : ∃ u, y * u ≤ x ∧ x < y * (u + 1) := by
      have : (∃ u, x < y * u) → (∃ u, y * u ≤ x ∧ x < y * (u + 1)) := by
        have : (∀ u, y * u ≤ x → y * (u + 1) ≤ x) → ∀ u, y * u ≤ x :=
          by simpa using (induction₂ (P := λ x y u ↦ y * u ≤ x) ⟨“&0 * #0 ≤ &1”, by simp, by simp⟩ x y)
        simpa using not_imp_not.mpr this
      have hx : x < y * (x + 1) := by
        have : x + 0 < y * x + y :=
          add_lt_add_of_le_of_lt (le_mul_self_of_pos_left hy) hy
        simpa [mul_add] using this
      exact this ⟨_, hx⟩
    rcases this with ⟨u, hu⟩
    exact ExistsUnique.intro u hu (by
      intro u' hu'
      by_contra ne
      wlog lt : u < u'
      · exact this x hy u' hu' u hu (Ne.symm ne) (Ne.lt_of_le ne (by simpa using lt))
      have : x < x := by calc
        x < y * (u + 1) := hu.2
        _ ≤ y * u'      := (mul_le_mul_left hy).mpr (lt_iff_succ_le.mp lt)
        _ ≤ x           := hu'.1
      exact LT.lt.false this)
  have iff : ∀ u, (∃ v < y, x = y * u + v) ↔ (y * u ≤ x ∧ x < y * (u + 1)) := by
    intro u; constructor
    · rintro ⟨v, hv, rfl⟩
      simp [mul_add, hv]
    · intro h
      let v := x -̇ y * u
      have e : x = y*u + v := by simp [msub_add_left h.1]
      have : v < y := by
        by_contra hyv
        have hyv : y ≤ v := by simpa using hyv
        have : x < x := by calc
          x < y * (u + 1) := h.2
          _ ≤ y * u + v   := by simpa [mul_add] using hyv
          _ = x           := e.symm
        exact LT.lt.false this
      exact ⟨v, this, e⟩
  exact (exists_unique_congr iff).mpr this

section ediv

lemma ediv_existsUnique (x y : M) : ∃! u, (0 < y → ∃ v < y, x = y * u + v) ∧ (y = 0 → u = 0) := by
  have : 0 ≤ y := by exact _root_.zero_le y
  rcases this with (rfl | hy) <;> simp [*]
  · simpa [pos_iff_ne_zero.mp hy] using remainder x hy

/-- Euclidean division -/
def ediv (x y : M) : M := Classical.choose! (ediv_existsUnique x y)

infix:70 " /ₑ " => ediv

lemma ediv_spec_of_pos (x : M) (h : 0 < y) : ∃ v < y, x = y * (x /ₑ y) + v :=
  (Classical.choose!_spec (ediv_existsUnique x y)).1 h

@[simp] lemma ediv_spec_zero (x : M) : x /ₑ 0 = 0 :=
  (Classical.choose!_spec (ediv_existsUnique x 0)).2 (by simp)

lemma ediv_graph {x y z : M} : z = x /ₑ y ↔ ((0 < y → ∃ v < y, x = y * z + v) ∧ (y = 0 → z = 0)) :=
  Classical.choose!_eq_iff _

lemma ediv_definable : Σᴬ[0]-Function₂ (λ x y : M ↦ x /ₑ y) :=
  ⟨“(0 < #2 → ∃[#0 < #3] (#2 = #3 * #1 + #0)) ∧ (#2 = 0 → #0 = 0)”,
    by simp[Hierarchy.pi_zero_iff_sigma_zero], by intro v; simp[ediv_graph]; rfl⟩

lemma ediv_spec_of_pos' (x : M) (h : 0 < y) : ∃ v < y, x = (x /ₑ y) * y + v := by
  simpa [_root_.mul_comm] using ediv_spec_of_pos x h

@[simp] lemma mul_ediv_le (x y : M) : y * (x /ₑ y) ≤ x := by
  have : 0 ≤ y := by exact _root_.zero_le y
  rcases this with (rfl | hy) <;> simp [*]
  rcases ediv_spec_of_pos x hy with ⟨v, _, e⟩
  simpa [← e] using show y * (x /ₑ y) ≤ y * (x /ₑ y) + v from le_self_add

@[simp] lemma ediv_le (x y : M) : x /ₑ y ≤ x := by
  have : 0 ≤ y := by exact _root_.zero_le y
  rcases this with (rfl | hy) <;> simp [*]
  have : 1 * (x /ₑ y) ≤ y * (x /ₑ y) := mul_le_mul_of_nonneg_right (le_iff_lt_succ.mpr (by simp[hy])) (by simp)
  simpa using le_trans this (mul_ediv_le x y)

lemma ediv_polybounded : PolyBounded₂ (λ x y : M ↦ x /ₑ y) := ⟨#0, λ _ ↦ by simp⟩

@[simp] lemma ediv_mul_le (x y : M) : x /ₑ y * y ≤ x := by rw [_root_.mul_comm]; exact mul_ediv_le _ _

lemma lt_mul_ediv (x : M) {y} (hy : 0 < y) : x < y * (x /ₑ y + 1) := by
  rcases ediv_spec_of_pos x hy with ⟨v, hv, e⟩
  calc x = y * (x /ₑ y) + v := e
       _ < y * (x /ₑ y + 1) := by simp [mul_add, hv]

@[simp] lemma ediv_one (x : M) : x /ₑ 1 = x :=
  le_antisymm (by simp) (le_iff_lt_succ.mpr $ by simpa using lt_mul_ediv x one_pos)

lemma ediv_mul_add (x : M) {y r} (hy : 0 < y) (hr : r < y) : (x * y + r) /ₑ y = x := by
  rcases ediv_spec_of_pos (x * y + r) hy with ⟨v, hv, e⟩
  symm; apply eq_of_le_of_not_lt
  · have : x * y < ((x * y + r) /ₑ y + 1) * y := calc
      x * y ≤ x * y + r                  := le_self_add
      _     = ((x * y + r) /ₑ y) * y + v := by simpa [@mul_comm _ _ y] using e
      _     < ((x * y + r) /ₑ y + 1) * y := by simp [add_mul, hv]
    exact le_iff_lt_succ.mpr <| lt_of_mul_lt_mul_of_nonneg_right this (by simp)
  · intro H
    have : ((x * y + r) /ₑ y) * y < (x + 1) * y := calc
      ((x * y + r) /ₑ y) * y ≤ x * y + r   := by simp
      _                      < (x + 1) * y := by simp [add_mul, hr]
    have : (x * y + r) /ₑ y ≤ x := le_iff_lt_succ.mpr ((mul_lt_mul_right hy).mp this)
    have : x < x := lt_of_lt_of_le H this
    exact LT.lt.false this

lemma ediv_mul_add_self (x : M) {y z} (hy : 0 < y) : (x + z * y) /ₑ y = x /ₑ y + z := by
  rcases ediv_spec_of_pos' x hy with ⟨r, hr, ex⟩
  simpa [add_mul, add_right_comm, ← ex] using ediv_mul_add (x /ₑ y + z) hy hr

@[simp] lemma ediv_mul_left (x : M) {y} (hy : 0 < y) : (x * y) /ₑ y = x := by
  simpa using ediv_mul_add x hy hy

@[simp] lemma ediv_mul_right (x : M) {y} (hy : 0 < y) : (y * x) /ₑ y = x := by
  simpa [_root_.mul_comm] using ediv_mul_add x hy hy

@[simp] lemma ediv_eq_zero_of_lt (y : M) {x} (h : x < y) : x /ₑ y = 0 := by
  simpa using ediv_mul_add 0 (pos_of_gt h) h

@[simp] lemma ediv_self {x : M} (hx : 0 < x) : x /ₑ x = 1 := by
  simpa using ediv_mul_left 1 hx

@[simp] lemma zero_ediv (x : M) : 0 /ₑ x = 0 := by
  have : 0 ≤ x := by exact _root_.zero_le x
  rcases this with (rfl | hy) <;> simp [*]

@[simp] lemma ediv_mul' (x : M) {y} (hy : 0 < y) : (y * x) /ₑ y = x := by simp [_root_.mul_comm, hy]

end ediv

section cpair

def cpair (x y : M) : M := ((x + y) * (x + y + 1)) /ₑ 2 + y

notation "⟨" x " ; " y "⟩" => cpair x y

lemma cpair_graph {x y z : M} :
    z = ⟨x ; y⟩ ↔ ∃ r < 2, (x + y) * (x + y + 1) + 2 * y = 2 * z + r := by
  simp [cpair, ediv_graph, ←ediv_mul_add_self, _root_.mul_comm]

lemma cpair_definable : Σᴬ[0]-Function₂ (λ x y : M ↦ ⟨x ; y⟩) := by
  let cpair : Semisentence ℒₒᵣ 3 := “∃[#0 < 2] (#2 + #3) * (#2 + #3 + 1) + 2 * #3 = 2 * #1 + #0”
  exact ⟨cpair, by simp[Hierarchy.pi_zero_iff_sigma_zero], by
    intro v; simp [Matrix.vecHead, Matrix.vecTail, Matrix.constant_eq_singleton, cpair_graph]⟩

lemma cpair_polybounded : PolyBounded₂ (λ x y : M ↦ ⟨x ; y⟩) :=
  ⟨ᵀ“(#0 + #1) * (#0 + #1 + 1) + #1 * 2”, λ _ ↦ by simp[cpair, ←ediv_mul_add_self]⟩

end cpair

end IOpen.Model

end

end Arith

end LO.FirstOrder
