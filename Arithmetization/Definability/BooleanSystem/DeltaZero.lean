import Arithmetization.Definability.BooleanSystem.Open

namespace LO.Arith

open FirstOrder

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐏𝐀⁻]

def DeltaZero.Lightface : BoundedSystem V where
  VecPr {k} (R) := Definable ℒₒᵣ (Arith.Hierarchy 𝚺 0) R
  verum {k} := ⟨⊤, by simp, by intro v; simp⟩
  and {k P Q} := by
    rintro ⟨p, hp, hP⟩; rintro ⟨q, hq, hQ⟩
    refine ⟨p ⋏ q, by simp [hp, hq], by intro v; simp [hP v, hQ v]⟩
  not {k P} := by
    rintro ⟨p, hp, hP⟩
    exact ⟨~p, by simp [Arith.Hierarchy.pi_zero_iff_sigma_zero, hp], by intro v; simp [hP v]⟩
  equal := ⟨“x y | x = y”, by simp, by intro v; simp⟩
  replace {k l P} := by
    rintro ⟨p, hp, hP⟩ f
    refine ⟨Rew.substs (fun x ↦ #(f x)) |>.hom p, by simp [hp], by intro v; simp [hP.iff]⟩
  Polynomial {k} (f) := ∃ t : Semiterm ℒₒᵣ Empty k, f = t.valbm V
  polynomial_comp {l k F f} := by
    rintro ⟨T, rfl⟩ ht
    choose t ht using ht
    rcases funext ht
    exact ⟨Rew.substs t T, by ext v; simp [Semiterm.val_substs]⟩
  polynomial_replace {k l _} := by
    rintro ⟨t, rfl⟩ f; exact ⟨Rew.substs (fun x ↦ #(f x)) t, by ext v; simp [Semiterm.val_substs]⟩
  polynomial_monotone {k _} := by
    rintro ⟨t, rfl⟩ v w h
    apply Structure.Monotone.term_monotone
    · exact h
    · simp
  polynomial_nth {k i} := ⟨#i, by simp⟩
  ball_poly {k f P} := by
    rintro ⟨t, rfl⟩ ⟨p, hp, hP⟩
    exact ⟨“∀ x <⁺ !t ⋯, !p x ⋯”, by simp [hp], by intro v; simp [Semiterm.val_substs, hP.iff]⟩
  lessThan := ⟨“x y | x < y”, by simp, by intro v; simp⟩

notation "𝛥₀[" V "]" => DeltaZero.Lightface (V := V)

notation "𝛥₀" => DeltaZero.Lightface

instance : 𝛥₀[V].Arithmetical where
  zero := ⟨⟨“x | x = 0”, by simp, by intro; simp [Function.Graphᵥ]⟩, 0, ⟨‘0’, by ext v; simp⟩, by intro; simp⟩
  one := ⟨⟨“x | x = 1”, by simp, by intro; simp [Function.Graphᵥ]⟩, 1, ⟨‘1’, by ext v; simp⟩, by intro; simp⟩
  add := ⟨⟨“z x y | z = x + y”, by simp, by intro v; simp [Function.Graphᵥ]⟩, fun v ↦ v 0 + v 1, ⟨‘#0 + #1’, by ext v; simp⟩, by simp⟩
  mul := ⟨⟨“z x y | z = x * y”, by simp, by intro v; simp [Function.Graphᵥ]⟩, fun v ↦ v 0 * v 1, ⟨‘#0 * #1’, by ext v; simp⟩, by simp⟩

def DeltaZero.Boldface : BoundedSystem V where
  VecPr {k} (R) := DefinableWithParam ℒₒᵣ (Arith.Hierarchy 𝚺 0) R
  verum {k} := ⟨⊤, by simp, by intro v; simp⟩
  and {k P Q} := by
    rintro ⟨p, hp, hP⟩; rintro ⟨q, hq, hQ⟩
    refine ⟨p ⋏ q, by simp [hp, hq], by intro v; simp [hP v, hQ v]⟩
  not {k P} := by
    rintro ⟨p, hp, hP⟩
    exact ⟨~p, by simp [Arith.Hierarchy.pi_zero_iff_sigma_zero, hp], by intro v; simp [hP v]⟩
  equal := ⟨“x y | x = y”, by simp, by intro v; simp⟩
  replace {k l P} := by
    rintro ⟨p, hp, hP⟩ f
    refine ⟨Rew.substs (fun x ↦ #(f x)) |>.hom p, by simp [hp], by intro v; simp [hP.iff]⟩
  Polynomial {k} (f) := ∃ t : Semiterm ℒₒᵣ V k, f = fun v ↦ t.valm V v id
  polynomial_comp {l k F f} := by
    rintro ⟨T, rfl⟩ ht
    choose t ht using ht
    rcases funext ht
    exact ⟨Rew.substs t T, by ext v; simp [Semiterm.val_substs]⟩
  polynomial_replace {k l _} := by
    rintro ⟨t, rfl⟩ f; exact ⟨Rew.substs (fun x ↦ #(f x)) t, by ext v; simp [Semiterm.val_substs]⟩
  polynomial_monotone {k _} := by
    rintro ⟨t, rfl⟩ v w h
    apply Structure.Monotone.term_monotone
    · exact h
    · simp
  polynomial_nth {k i} := ⟨#i, by simp⟩
  ball_poly {k f P} := by
    rintro ⟨t, rfl⟩ ⟨p, hp, hP⟩
    exact ⟨“∀ x <⁺ !t ⋯, !p x ⋯”, by simp [hp], by intro v; simp [Semiterm.val_substs, hP.iff]⟩
  lessThan := ⟨“x y | x < y”, by simp, by intro v; simp⟩

notation "𝜟₀" => DeltaZero.Boldface

notation "𝜟₀[" V "]" => DeltaZero.Boldface (V := V)

instance : 𝜟₀[V].Arithmetical where
  zero := ⟨⟨“x | x = 0”, by simp, by intro; simp [Function.Graphᵥ]⟩, 0, ⟨‘0’, by ext v; simp⟩, by intro; simp⟩
  one := ⟨⟨“x | x = 1”, by simp, by intro; simp [Function.Graphᵥ]⟩, 1, ⟨‘1’, by ext v; simp⟩, by intro; simp⟩
  add := ⟨⟨“z x y | z = x + y”, by simp, by intro v; simp [Function.Graphᵥ]⟩, fun v ↦ v 0 + v 1, ⟨‘#0 + #1’, by ext v; simp⟩, by simp⟩
  mul := ⟨⟨“z x y | z = x * y”, by simp, by intro v; simp [Function.Graphᵥ]⟩, fun v ↦ v 0 * v 1, ⟨‘#0 * #1’, by ext v; simp⟩, by simp⟩

instance : 𝜟₀[V].Boldface where
  const (z) := ⟨⟨“x | x = &z”, by simp, by intro v; simp [Function.Graphᵥ]⟩, fun _ ↦ z, ⟨&z, by simp⟩, by simp⟩

section

example : 𝛥₀.Rel₃ fun x y z : V ↦ x = 32 → ¬y < z ∧ ∀ w < x + 2 * z, w < x := by definability?

example (c : V) : 𝜟₀.Rel₃ fun x y z : V ↦ x = 32 → ¬y < z ∧ ∀ w < x + z, c < x := by definability

end

namespace LO.Arith
