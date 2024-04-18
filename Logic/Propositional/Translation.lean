import Logic.Propositional.Classical.Basic
import Logic.Propositional.Basic

namespace LO.Propositional

variable {α : Type*}

namespace Basic

@[simp]
def Formula.toClassical : Basic.Formula α → Classical.Formula α
  | .atom a => Classical.Formula.atom a
  | ⊤              => ⊤
  | ⊥              => ⊥
  | p ⋏ q          => p.toClassical ⋏ q.toClassical
  | p ⋎ q          => p.toClassical ⋎ q.toClassical
  | p ⟶ q          => p.toClassical ⟶ q.toClassical

instance : Coe (Formula α) (Classical.Formula α) := ⟨Formula.toClassical⟩

instance : Coe (Theory α) (Classical.Theory α) := ⟨(Formula.toClassical '' ·)⟩

/-
def Deduction.toClassical {T : Theory α} {p} : T ⊢ p → (T : Classical.Theory α) ⊢! p
  | axm h                      => Deduction.axm! (Set.mem_image_of_mem _ h)
  | @modusPonens _ _ p q b₁ b₂ => by
      let b₁' : (T : Classical.Theory α) ⊢! p ⟶ q := Deducible.toClassical b₁
      let b₂' : (T : Classical.Theory α) ⊢! p := Deducible.toClassical b₂
      exact b₁' ⨀ b₂'
  | verum _                    => by simp; prover
  | efq _ _                    => by simp; prover
  | imply₁ _ _ _               => by simp; prover
  | imply₂ _ _ _ _             => by simp; prover
  | conj₁ _ _ _                => by simp; prover
  | conj₂ _ _ _                => by simp; prover
  | conj₃ _ _ _                => by simp; prover
  | disj₁ _ _ _                => by simp; prover
  | disj₂ _ _ _                => by simp; prover
  | disj₃ _ _ _ _              => by simp; prover
-/

end Basic

namespace Classical

@[simp]
def Formula.toBasic : Formula α → Basic.Formula α
  | Formula.atom a  => Basic.Formula.atom a
  | Formula.natom a => ~Basic.Formula.atom a
  | ⊤               => ⊤
  | ⊥               => ⊥
  | p ⋏ q           => p.toBasic ⋏ q.toBasic
  | p ⋎ q           => p.toBasic ⋎ q.toBasic

instance : Coe (Formula α) (Basic.Formula α) := ⟨Formula.toBasic⟩

instance : Coe (Theory α) (Basic.Theory α) := ⟨(Formula.toBasic '' ·)⟩

variable [DecidableEq α] [Encodable α]

-- lemma Deducible.toClassical {T : Theory α} {p} : T ⊢! p → (T : Intuitionistic.Theory α) ⊢! ~~p := sorry

end Classical

end LO.Propositional
