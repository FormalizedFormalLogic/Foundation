import Logic.Logic.System

namespace LO

namespace System
variable {F : Type u} [LogicSymbol F] [𝓑 : System F]

class Intuitionistic (F : Type u) [LogicSymbol F] [System F] where
  verum       (T : Set F)             : T ⊢ ⊤
  modusPonens {T : Set F} {p q : F}   : T ⊢ p ⟶ q → T ⊢ p → T ⊢ q
  imply₁      (T : Set F) (p q : F)   : T ⊢ p ⟶ q ⟶ p
  imply₂      (T : Set F) (p q r : F) : T ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁       (T : Set F) (p q : F)   : T ⊢ p ⋏ q ⟶ p
  conj₂       (T : Set F) (p q : F)   : T ⊢ p ⋏ q ⟶ q
  conj₃       (T : Set F) (p q : F)   : T ⊢ p ⟶ q ⟶ p ⋏ q
  disj₁       (T : Set F) (p q : F)   : T ⊢ p ⟶ p ⋎ q
  disj₂       (T : Set F) (p q : F)   : T ⊢ q ⟶ p ⋎ q
  disj₃       (T : Set F) (p q r : F) : T ⊢ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r
  neg₁        (T : Set F) (p q : F)   : T ⊢ (p ⟶ q) ⟶ (p ⟶ ~q) ⟶ ~p
  neg₂        (T : Set F) (p q : F)   : T ⊢ p ⟶ ~p ⟶ q

class IntuitionisticNC (F : Type u) [LogicSymbol F] [System F] where
  verum       (T : Set F)             : T ⊢! ⊤
  modusPonens {T : Set F} {p q : F}   : T ⊢! p ⟶ q → T ⊢! p → T ⊢! q
  imply₁      (T : Set F) (p q : F)   : T ⊢! p ⟶ q ⟶ p
  imply₂      (T : Set F) (p q r : F) : T ⊢! (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁       (T : Set F) (p q : F)   : T ⊢! p ⋏ q ⟶ p
  conj₂       (T : Set F) (p q : F)   : T ⊢! p ⋏ q ⟶ q
  conj₃       (T : Set F) (p q : F)   : T ⊢! p ⟶ q ⟶ p ⋏ q
  disj₁       (T : Set F) (p q : F)   : T ⊢! p ⟶ p ⋎ q
  disj₂       (T : Set F) (p q : F)   : T ⊢! q ⟶ p ⋎ q
  disj₃       (T : Set F) (p q r : F) : T ⊢! (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r
  neg₁        (T : Set F) (p q : F)   : T ⊢! (p ⟶ q) ⟶ (p ⟶ ~q) ⟶ ~p
  neg₂        (T : Set F) (p q : F)   : T ⊢! p ⟶ ~p ⟶ q

variable {Struc : Type w → Type v} [𝓢 : Semantics F Struc]

instance [LO.Complete F] : IntuitionisticNC F where
  verum := fun T =>
    Complete.consequence_iff_provable.mp (fun M _ _ _ => by simp)
  modusPonens := fun {T p q} b₁ b₂ =>
    Complete.consequence_iff_provable.mp (fun M _ s hM => by
      rcases b₁ with ⟨b₁⟩; rcases b₂ with ⟨b₂⟩
      have : s ⊧ₛ p → s ⊧ₛ q := by simpa using Sound.models_of_proof hM b₁
      exact this (Sound.models_of_proof hM b₂))
  imply₁ := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a _ => a)
  imply₂ := fun T p q r => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a b c => a c (b c))
  conj₁  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a _ => a)
  conj₂  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp)
  conj₃  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a b => ⟨a, b⟩)
  disj₁  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simpa using Or.inl)
  disj₂  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simpa using Or.inr)
  disj₃  := fun T p q r => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simpa using Or.rec)
  neg₁   := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a b c => (b c) (a c))
  neg₂   := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a b => (b a).elim)

end System

end LO
