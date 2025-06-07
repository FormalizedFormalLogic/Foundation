import Foundation.Modal.Entailment.KT
import Foundation.Modal.Entailment.K5

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.S5 𝓢]

-- MEMO: need more simple proof
def diabox_box : 𝓢 ⊢ ◇□φ ➝ □φ := by
  have : 𝓢 ⊢ ◇(∼φ) ➝ □◇(∼φ) := axiomFive;
  have : 𝓢 ⊢ ∼□◇(∼φ) ➝ ∼◇(∼φ) := contra this;
  have : 𝓢 ⊢ ∼□◇(∼φ) ➝ □φ := C_trans this boxDuality_mpr;
  refine C_trans ?_ this;
  refine C_trans diaDuality_mp $ ?_
  apply contra;
  apply implyBoxDistribute';
  refine C_trans diaDuality_mp ?_;
  apply contra;
  apply implyBoxDistribute';
  apply dni;
@[simp] lemma diabox_box! : 𝓢 ⊢! ◇□φ ➝ □φ := ⟨diabox_box⟩

def diabox_box' (h : 𝓢 ⊢ ◇□φ) : 𝓢 ⊢ □φ := diabox_box ⨀ h
lemma diabox_box'! (h : 𝓢 ⊢! ◇□φ) : 𝓢 ⊢! □φ := ⟨diabox_box' h.some⟩

def rm_diabox : 𝓢 ⊢ ◇□φ ➝ φ := C_trans diabox_box axiomT
@[simp] lemma rm_diabox! : 𝓢 ⊢! ◇□φ ➝ φ := ⟨rm_diabox⟩

def rm_diabox' (h : 𝓢 ⊢ ◇□φ) : 𝓢 ⊢ φ := rm_diabox ⨀ h
lemma rm_diabox'! (h : 𝓢 ⊢! ◇□φ) : 𝓢 ⊢! φ := ⟨rm_diabox' h.some⟩

end LO.Modal.Entailment
