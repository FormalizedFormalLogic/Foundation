import Foundation.FirstOrder.Arith.PeanoMinus

namespace LO

namespace FirstOrder

namespace Arith

section

variable {L : Language} [L.LT]

inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L μ n → Prop
  | zero {Γ p}                                : DeltaZero p → StrictHierarchy Γ s p
  | sigma {s n} {p : Semiformula L μ (n + 1)} : StrictHierarchy 𝚷 s p → StrictHierarchy 𝚺 (s + 1) (∃' p)
  | pi {s n} {p : Semiformula L μ (n + 1)}    : StrictHierarchy 𝚺 s p → StrictHierarchy 𝚷 (s + 1) (∀' p)
  | ex {s n} {p : Semiformula L μ (n + 1)}    : StrictHierarchy 𝚺 (s + 1) p → StrictHierarchy 𝚺 (s + 1) (∃' p)
  | all {s n} {p : Semiformula L μ (n + 1)}   : StrictHierarchy 𝚷 (s + 1) p → StrictHierarchy 𝚷 (s + 1) (∀' p)

lemma DeltaZero.of_open {p : Semiformula L μ n} : p.Open → DeltaZero p := Hierarchy.of_open

namespace StrictHierarchy

lemma rew {p : Semiformula L μ₁ n₁} (h : StrictHierarchy Γ s p) (ω : Rew L μ₁ n₁ μ₂ n₂) :
    StrictHierarchy Γ s (ω.hom p) := by
  induction h generalizing μ₂ n₂ <;> try simp
  case zero h => exact zero <| (Hierarchy.rew_iff (ω := ω)).mpr h
  case sigma ih => exact (ih ω.q).sigma
  case pi ih => exact (ih ω.q).pi
  case ex ih => exact (ih ω.q).ex
  case all ih => exact (ih ω.q).all

lemma rew_iff {p : Semiformula L μ₁ n₁} (ω : Rew L μ₁ n₁ μ₂ n₂) :
    StrictHierarchy Γ s (ω.hom p) ↔ StrictHierarchy Γ s p :=
  ⟨by
    generalize hq : ω.hom p = q
    intro h;
    induction h generalizing n₁ <;> try simp [Rew.eq_ball_iff, Rew.eq_bex_iff, Rew.eq_all_iff, Rew.eq_ex_iff] at hq ⊢
    case zero q h =>
      rcases hq; exact zero (Hierarchy.rew_iff.mp h)
    case sigma h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).sigma
    case pi h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).pi
    case ex h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).ex
    case all ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).all,
  fun h ↦ h.rew ω⟩

lemma succ {Γ} {p : Semiformula L μ₁ n₁} (h : StrictHierarchy Γ s p) :
    StrictHierarchy Γ (s + 1) p := by
  induction h
  case zero h => exact zero h
  case sigma ih => exact ih.sigma
  case pi ih => exact ih.pi
  case ex ih => exact ih.ex
  case all ih => exact ih.all

lemma zero_iff_delta_zero {Γ} {p : Semiformula L μ n} :
    StrictHierarchy Γ 0 p ↔ DeltaZero p := by
  constructor
  · rintro ⟨h⟩; exact h
  · intro h; exact zero h

end StrictHierarchy

end

end Arith
