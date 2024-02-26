import Logic.Logic.System

namespace LO

namespace System
variable {F : Type u} [LogicSymbol F] [𝓑 : System F]

class Intuitionistic (F : Type u) [LogicSymbol F] [System F] where
  modus_ponens {T : Set F} {p q : F}   : T ⊢! p ⟶ q → T ⊢! p → T ⊢! q
  verum       (T : Set F)             : T ⊢! ⊤
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

variable {α : Type*} [𝓢 : Semantics F α]

instance [LO.Complete F] : Intuitionistic F where
  modus_ponens := fun {T p q} b₁ b₂ =>
    Complete.consequence_iff_provable.mp (fun a hM => by
      rcases b₁ with ⟨b₁⟩; rcases b₂ with ⟨b₂⟩
      have : a ⊧ p → a ⊧ q := by simpa using Sound.models_of_proof hM b₁
      exact this (Sound.models_of_proof hM b₂))
  verum  := fun T => Complete.consequence_iff_provable.mp (fun _ _ => by simp)
  imply₁ := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ => by simp; exact fun a _ => a)
  imply₂ := fun T p q r => Complete.consequence_iff_provable.mp (fun _ _ => by simp; exact fun a b c => a c (b c))
  conj₁  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ => by simp; exact fun a _ => a)
  conj₂  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ => by simp)
  conj₃  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ => by simp; exact fun a b => ⟨a, b⟩)
  disj₁  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ => by simpa using Or.inl)
  disj₂  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ => by simpa using Or.inr)
  disj₃  := fun T p q r => Complete.consequence_iff_provable.mp (fun _ _ => by simpa using Or.rec)
  neg₁   := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ => by simp; exact fun a b c => (b c) (a c))
  neg₂   := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ => by simp; exact fun a b => (b a).elim)

namespace Intuitionistic

variable [Intuitionistic F] {T : Set F}

scoped infixl:90 " ⨀ " => modus_ponens

@[simp] lemma imp_id (p : F) : T ⊢! p ⟶ p := (imply₂ T p (p ⟶ p) p) ⨀ (imply₁ T p (p ⟶ p)) ⨀ (imply₁ T p p)

@[simp] lemma hyp_right {p : F} (h : T ⊢! p) (q) : T ⊢! q ⟶ p := imply₁ T p q ⨀ h

lemma imp_trans {p q r : F} (hp : T ⊢! p ⟶ q) (hq : T ⊢! q ⟶ r) : T ⊢! p ⟶ r :=
  imply₂ T p q r ⨀ hyp_right hq p ⨀ hp

lemma and_split {p q : F} (hp : T ⊢! p) (hq : T ⊢! q) : T ⊢! p ⋏ q := (conj₃ T p q) ⨀ hp ⨀ hq

lemma and_left {p q : F} (h : T ⊢! p ⋏ q) : T ⊢! p := conj₁ T p q ⨀ h

lemma and_right {p q : F} (h : T ⊢! p ⋏ q) : T ⊢! q := conj₂ T p q ⨀ h

lemma iff_refl (p : F) : T ⊢! p ⟷ p := and_split (imp_id p) (imp_id p)

lemma iff_symm {p q : F} (h : T ⊢! p ⟷ q) : T ⊢! q ⟷ p := and_split (and_right h) (and_left h)

lemma iff_trans {p q r : F} (hp : T ⊢! p ⟷ q) (hq : T ⊢! q ⟷ r) : T ⊢! p ⟷ r :=
  and_split (imp_trans (and_left hp) (and_left hq)) (imp_trans (and_right hq) (and_right hp))

end Intuitionistic

end System

end LO
