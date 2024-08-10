import Arithmetization.Definability.BooleanSystem.Basic

namespace LO.Arith

open FirstOrder

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐏𝐀⁻]

def Open.Lightface : BooleanSystem V where
  VecPr {k} (R) := Definable ℒₒᵣ Semiformula.Open R
  verum {k} := ⟨⊤, by simp, by intro v; simp⟩
  and {k P Q} := by
    rintro ⟨p, hp, hP⟩; rintro ⟨q, hq, hQ⟩
    refine ⟨p ⋏ q, by simp [hp, hq], by intro v; simp [hP v, hQ v]⟩
  not {k P} := by
    rintro ⟨p, hp, hP⟩
    exact ⟨~p, by simp [hp], by intro v; simp [hP v]⟩
  equal := ⟨“x y | x = y”, by simp, by intro v; simp⟩
  replace {k l P} := by
    rintro ⟨p, hp, hP⟩ f
    refine ⟨Rew.substs (fun x ↦ #(f x)) |>.hom p, by simp [hp], by intro v; simp [hP.iff]⟩

def Open.Boldface : BooleanSystem V where
  VecPr {k} (R) := DefinableWithParam ℒₒᵣ Semiformula.Open R
  verum {k} := ⟨⊤, by simp, by intro v; simp⟩
  and {k P Q} := by
    rintro ⟨p, hp, hP⟩; rintro ⟨q, hq, hQ⟩
    refine ⟨p ⋏ q, by simp [hp, hq], by intro v; simp [hP v, hQ v]⟩
  not {k P} := by
    rintro ⟨p, hp, hP⟩
    exact ⟨~p, by simp [hp], by intro v; simp [hP v]⟩
  equal := ⟨“x y | x = y”, by simp, by intro v; simp⟩
  replace {k l P} := by
    rintro ⟨p, hp, hP⟩ f
    refine ⟨Rew.substs (fun x ↦ #(f x)) |>.hom p, by simp [hp], by intro v; simp [hP.iff]⟩

namespace LO.Arith
