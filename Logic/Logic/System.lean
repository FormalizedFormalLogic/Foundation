import Logic.Logic.Semantics

namespace LO

variable {F : Type u} [LogicSymbol F]

/- Deduction System of F -/

class System (F : Type u) [LogicSymbol F] where
  Bew : Set F → F → Type u
  axm : ∀ {f}, f ∈ T → Bew T f
  weakening' : ∀ {T U f}, T ⊆ U → Bew T f → Bew U f

namespace System
variable [𝓑 : System F]

instance : HasTurnstile F (Type u) := ⟨𝓑.Bew⟩

def BewTheory (T U : Set F) : Type u := {f : F} → f ∈ U → T ⊢ f

infix:45 " ⊢* " => System.BewTheory

def BewTheoryEmpty (T : Set F) : T ⊢* ∅ := fun h => by contradiction

def BewTheory.ofSubset {T U : Set F} (h : U ⊆ T) : T ⊢* U := fun hf => axm (h hf)

def BewTheory.refl (T : Set F) : T ⊢* T := axm

def Consistent (T : Set F) : Prop := IsEmpty (T ⊢ ⊥)

def weakening {T U : Set F} {f : F} (b : T ⊢ f) (ss : T ⊆ U) : U ⊢ f := weakening' ss b

lemma Consistent.of_subset {T U : Set F} (h : Consistent U) (ss : T ⊆ U) : Consistent T := ⟨fun b => h.false (weakening b ss)⟩

lemma inConsistent_of_proof {T : Set F} (b : T ⊢ ⊥) : ¬Consistent T := by simp[Consistent]; exact ⟨b⟩

abbrev Provable (T : Set F) (f : F) : Prop := Nonempty (T ⊢ f)

infix:45 " ⊢! " => System.Provable

abbrev Unprovable (T : Set F) (f : F) : Prop := IsEmpty (T ⊢ f)

infix:45 " ⊬ " => System.Unprovable

lemma unprovable_iff_not_provable {T : Set F} {f : F} : T ⊬ f ↔ ¬T ⊢! f := by simp[System.Unprovable]

protected def Complete (T : Set F) : Prop := ∀ f, (T ⊢! f) ∨ (T ⊢! ~f)

def Independent (T : Set F) (f : F) : Prop := T ⊬ f ∧ T ⊬ ~f

lemma incomplete_iff_exists_independent {T : Set F} :
    ¬System.Complete T ↔ ∃ f, Independent T f := by simp[System.Complete, not_or, Independent]

class Subtheory (T U : Set F) where
  sub : {f : F} → T ⊢ f → U ⊢ f

class Equivalent (T U : Set F) where
  ofLeft : {f : F} → T ⊢ f → U ⊢ f
  ofRight : {f : F} → U ⊢ f → T ⊢ f

namespace Subtheory

variable (T U T₁ T₂ T₃ : Set F)

@[refl] instance : Subtheory T T := ⟨id⟩

@[trans] protected def trans [Subtheory T₁ T₂] [Subtheory T₂ T₃] : Subtheory T₁ T₃ :=
  ⟨fun {f} b => sub (sub b : T₂ ⊢ f)⟩

def ofSubset (h : T ⊆ U) : Subtheory T U := ⟨fun b => weakening b h⟩

end Subtheory

namespace Equivalent

variable (T U T₁ T₂ T₃ : Set F)

@[refl] instance : Equivalent T T := ⟨id, id⟩

@[symm] instance [Equivalent T U] : Equivalent U T := ⟨ofRight, ofLeft⟩

@[trans] protected def trans [Equivalent T₁ T₂] [Equivalent T₂ T₃] : Equivalent T₁ T₃ :=
  ⟨fun {f} b => ofLeft (ofLeft b : T₂ ⊢ f), fun {f} b => ofRight (ofRight b : T₂ ⊢ f)⟩

end Equivalent

end System

def System.hom [System F] {G : Type u} [LogicSymbol G] (F : G →L F) : System G where
  Bew := fun T g => F '' T ⊢ F g
  axm := fun h => System.axm (Set.mem_image_of_mem F h)
  weakening' := fun h => by simp; exact System.weakening' (Set.image_subset F h)

variable (F)
variable [LogicSymbol F] [𝓑 : System F] {Struc : Type w → Type v} [𝓢 : Semantics F Struc]

class Sound where
  sound : ∀ {T : Set F} {p : F}, T ⊢ p → T ⊨ p

class SoundOn (M : Type w) (s : Struc M) (H : Set F) where
  sound : ∀ {T : Set F} {p : F}, p ∈ H → T ⊢ p → s ⊧ₛ p

class Complete extends Sound F where
  complete : ∀ {T : Set F} {p : F}, T ⊨ p → T ⊢ p

variable {F}

namespace Sound

variable [Sound F]
variable {M : Type w} [Inhabited M] {s : Struc M}

lemma sound' {T : Set F} {f : F} : T ⊢! f → T ⊨ f := by rintro ⟨b⟩; exact sound b

lemma not_provable_of_countermodel {T : Set F} {p : F}
  (hT : s ⊧ₛ* T) (hp : ¬s ⊧ₛ p) : IsEmpty (T ⊢ p) :=
  ⟨fun b => by have : s ⊧ₛ p := Sound.sound b M s hT; contradiction⟩

lemma consistent_of_model {T : Set F}
  (hT : s ⊧ₛ* T) : System.Consistent T :=
  not_provable_of_countermodel (p := ⊥) hT (by simp)

lemma consistent_of_satisfiable {T : Set F} : Semantics.Satisfiableₛ T → System.Consistent T := by
  rintro ⟨M, _, s, h⟩; exact consistent_of_model h

lemma models_of_proof {T : Set F} {f} (h : s ⊧ₛ* T) (b : T ⊢ f) : s ⊧ₛ f :=
  Sound.sound b M s h

lemma modelsTheory_of_proofTheory {T U : Set F} (h : s ⊧ₛ* T) (b : T ⊢* U) : s ⊧ₛ* U :=
  fun _ hf => models_of_proof h (b hf)

end Sound

namespace Complete

variable [Complete F]

lemma satisfiableₛ_iff_consistent {T : Set F} : Semantics.Satisfiableₛ T ↔ System.Consistent T :=
  ⟨Sound.consistent_of_satisfiable,
   by contrapose; intro h
      have : T ⊨ ⊥
      { intro M i s hM; have : Semantics.Satisfiableₛ T := ⟨M, i, s, hM⟩; contradiction }
      have : T ⊢ ⊥ := complete this
      exact System.inConsistent_of_proof this⟩

lemma not_satisfiable_iff_inconsistent {T : Set F} : ¬Semantics.Satisfiableₛ T ↔ T ⊢! ⊥ := by
  simp[satisfiableₛ_iff_consistent, System.Consistent]

lemma consequence_iff_provable {T : Set F} {f : F} : T ⊨ f ↔ T ⊢! f :=
⟨fun h => ⟨complete h⟩, by rintro ⟨b⟩; exact Sound.sound b⟩

end Complete

namespace System

variable [LO.Complete F]

def ofSemanticsSubtheory {T₁ T₂ : Set F} (h : Semantics.Subtheory T₁ T₂) : System.Subtheory T₁ T₂ :=
  ⟨fun hf => Complete.complete (h (Sound.sound hf))⟩

end System

namespace Semantics

variable [LO.Complete F]

lemma ofSystemSubtheory (T₁ T₂ : Set F) [System.Subtheory T₁ T₂] : Semantics.Subtheory T₁ T₂ :=
  fun hf => (Sound.sound $ System.Subtheory.sub $ Complete.complete hf)

end Semantics

class OneSided (F : Type*) [LogicSymbol F] where
  Derivation : List F → Type*
  verum (Δ : List F) : Derivation (⊤ :: Δ)
  and {p q : F} {Δ : List F} : Derivation (p :: Δ) → Derivation (q :: Δ) → Derivation (p ⋏ q :: Δ)
  or {p q : F} {Δ : List F} : Derivation (p :: q :: Δ) → Derivation (p ⋎ q :: Δ)
  wk {Δ Γ : List F} : Derivation Δ → Δ ⊆ Γ → Derivation Γ
  em {p} {Δ : List F} (hp : ~p ∈ Δ) : Derivation (p :: Δ)

scoped prefix:45 "⊢ᴸ " => OneSided.Derivation

class LawfulOneSided (F : Type*) [LogicSymbol F] [System F] extends OneSided F where
  toProofEmpty {p : F} : ⊢ᴸ [p] → ∅ ⊢ p

namespace LawfulOneSided

variable {F : Type*} [LogicSymbol F] [System F] [LawfulOneSided F]

def toProof {p : F} (b : ⊢ᴸ [p]) (T : Set F) : T ⊢ p :=
  System.weakening (toProofEmpty b) (Set.empty_subset T)

end LawfulOneSided

class TwoSided (F : Type*) where
  Derivation : List F → List F → Type*

infix: 45 " ⊢ᴳ " => TwoSided.Derivation

class Gentzen (F : Type u) [LogicSymbol F] extends TwoSided F where
  verum (Γ Δ : List F)                : Γ ⊢ᴳ ⊤ :: Δ
  falsum (Γ Δ : List F)               : ⊥ :: Γ ⊢ᴳ Δ
  negLeft {p : F} {Γ Δ : List F}      : Γ ⊢ᴳ p :: Δ → ~p :: Γ ⊢ᴳ Δ
  negRight {p : F} {Γ Δ : List F}     : p :: Γ ⊢ᴳ Δ → Γ ⊢ᴳ ~p :: Δ
  andLeft {p q : F} {Γ Δ : List F}    : p :: q :: Γ ⊢ᴳ Δ → p ⋏ q :: Γ ⊢ᴳ Δ
  andRight {p q : F} {Γ Δ : List F}   : Γ ⊢ᴳ p :: Δ → Γ ⊢ᴳ q :: Δ → Γ ⊢ᴳ p ⋏ q :: Δ
  orLeft {p q : F} {Γ Δ : List F}     : p :: Γ ⊢ᴳ Δ → q :: Γ ⊢ᴳ Δ → p ⋎ q :: Γ ⊢ᴳ Δ
  orRight {p q : F} {Γ Δ : List F}    : Γ ⊢ᴳ p :: q :: Δ → Γ ⊢ᴳ p ⋎ q :: Δ
  implyLeft {p q : F} {Γ Δ : List F}  : Γ ⊢ᴳ p :: Δ → q :: Γ ⊢ᴳ Δ → (p ⟶ q) :: Γ ⊢ᴳ Δ
  implyRight {p q : F} {Γ Δ : List F} : p :: Γ ⊢ᴳ q :: Δ → Γ ⊢ᴳ (p ⟶ q) :: Δ
  wk {Γ Γ' Δ Δ' : List F} : Γ ⊢ᴳ Δ → Γ ⊆ Γ' → Δ ⊆ Δ' → Γ' ⊢ᴳ Δ'
  em {p} {Γ Δ : List F} (hΓ : p ∈ Γ) (hΔ : p ∈ Δ) : Γ ⊢ᴳ Δ

class LawfulGentzen (F : Type u) [LogicSymbol F] [System F] extends Gentzen F where
  toProofEmpty {p : F} : [] ⊢ᴳ [p] → ∅ ⊢ p

namespace LawfulGentzen

variable {F : Type*} [LogicSymbol F] [System F] [LawfulGentzen F]

def toProof {p : F} (b : [] ⊢ᴳ [p]) (T : Set F) : T ⊢ p :=
  System.weakening (toProofEmpty b) (Set.empty_subset T)

end LawfulGentzen

end LO
