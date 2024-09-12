import Logic.Propositional.Classical.Basic
import Logic.IntProp

namespace LO.Propositional

variable {α : Type*}

namespace IntProp

@[simp]
def Formula.toClassical : IntProp.Formula α → Classical.Formula α
  | .atom a => Classical.Formula.atom a
  | ⊤              => ⊤
  | ⊥              => ⊥
  | ~p             => ~p.toClassical
  | p ⋏ q          => p.toClassical ⋏ q.toClassical
  | p ⋎ q          => p.toClassical ⋎ q.toClassical
  | p ➝ q          => p.toClassical ➝ q.toClassical

instance : Coe (Formula α) (Classical.Formula α) := ⟨Formula.toClassical⟩

instance : Coe (Theory α) (Classical.Theory α) := ⟨(Formula.toClassical '' ·)⟩

/-
def Deduction.toClassical {T : Theory α} {p} : T ⊢ p → (T : Classical.Theory α) ⊢! p
  | axm h                      => Deduction.axm! (Set.mem_image_of_mem _ h)
  | @modusPonens _ _ p q b₁ b₂ => by
      let b₁' : (T : Classical.Theory α) ⊢! p ➝ q := Deducible.toClassical b₁
      let b₂' : (T : Classical.Theory α) ⊢! p := Deducible.toClassical b₂
      exact b₁' ⨀ b₂'
  | verum _                    => by simp; prover
  | efq _ _                    => by simp; prover
  | imply₁ _ _ _               => by simp; prover
  | imply₂ _ _ _ _             => by simp; prover
  | and₁ _ _ _                => by simp; prover
  | and₂ _ _ _                => by simp; prover
  | and₃ _ _ _                => by simp; prover
  | or₁ _ _ _                => by simp; prover
  | or₂ _ _ _                => by simp; prover
  | or₃ _ _ _ _              => by simp; prover
-/

end IntProp

namespace Classical

@[simp]
def Formula.toIntProp : Formula α → IntProp.Formula α
  | Formula.atom a  => IntProp.Formula.atom a
  | Formula.natom a => ~IntProp.Formula.atom a
  | ⊤               => ⊤
  | ⊥               => ⊥
  | p ⋏ q           => p.toIntProp ⋏ q.toIntProp
  | p ⋎ q           => p.toIntProp ⋎ q.toIntProp

instance : Coe (Formula α) (IntProp.Formula α) := ⟨Formula.toIntProp⟩

instance : Coe (Theory α) (IntProp.Theory α) := ⟨(Formula.toIntProp '' ·)⟩

variable [DecidableEq α] [Encodable α]

-- lemma Deducible.toClassical {T : Theory α} {p} : T ⊢! p → (T : Intuitionistic.Theory α) ⊢! ~~p := sorry

end Classical

end LO.Propositional
