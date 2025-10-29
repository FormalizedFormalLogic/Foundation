import Foundation.InterpretabilityLogic.Veltman.Logic.IL.Soundness

namespace LO.InterpretabilityLogic

variable {α : Type*} [DecidableEq α]
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

open Modal (Kripke.Frame Kripke.Model)

namespace Formula

def subformula : Formula α → Finset (Formula α)
  | atom a => {atom a}
  | ⊥      => {⊥}
  | φ ➝ ψ => {φ ➝ ψ} ∪ subformula φ ∪ subformula ψ
  | □φ     => {□φ} ∪ subformula φ
  | φ ▷ ψ  => {φ ▷ ψ} ∪ subformula φ ∪ subformula ψ

@[simp, grind]
lemma mem_self_subformula {φ : Formula α} : φ ∈ φ.subformula := by
  induction φ <;> simp_all [subformula, Finset.mem_union, Finset.mem_singleton]


def complement : Formula α → Formula α
  | ∼φ => φ
  | φ  => ∼φ
prefix:80 "-" => complement

end Formula


namespace FormulaFinset

variable {Φ Φ₁ Φ₂ : FormulaFinset α}

class SubformulaClosed (Φ : FormulaFinset α) where
  subfml_closed : ∀ φ ∈ Φ, φ.subformula ⊆ Φ


class Adequate (Φ : FormulaFinset α) extends Φ.SubformulaClosed where
  compl_closed : ∀ φ ∈ Φ, -φ ∈ Φ
  mem_top_rhd_top : ⊤ ▷ ⊤ ∈ Φ
  mem_part₁ : ∀ {φ ψ}, (φ ▷ ψ) ∈ Φ → (□-φ) ∈ Φ ∧ (□-ψ) ∈ Φ
  mem_part₂ : ∀ {φ₁ ψ₁ φ₂ ψ₂},
    (φ₁ ▷ ψ₁) ∈ Φ → (φ₂ ▷ ψ₂) ∈ Φ →
    ∀ ξ₁ ∈ [φ₁, ψ₁, φ₂, ψ₂],
    ∀ ξ₂ ∈ [φ₁, ψ₁, φ₂, ψ₂],
    (ξ₁ ▷ ξ₂) ∈ Φ

attribute [simp] Adequate.mem_top_rhd_top



def Consistent (𝓢 : S) (Φ : FormulaFinset α) : Prop := Φ *⊬[𝓢] ⊥
def Inconsistent (𝓢 : S) (Φ : FormulaFinset α) : Prop := ¬Consistent 𝓢 Φ

def Maximal (𝓢 : S) (Φ : FormulaFinset α) := ∀ Ψ, Φ ⊂ Ψ → Inconsistent 𝓢 Ψ

end FormulaFinset

section

def AdequateSet (α) [DecidableEq α] := { Φ : FormulaFinset α // Φ.Adequate }

def MaximalConsistentSet (𝓢 : S) (Φ : AdequateSet α) := { Ψ : FormulaFinset α // Ψ ⊆ Φ.1 ∧ Ψ.Maximal 𝓢 ∧ Ψ.Consistent 𝓢 }

variable {Φ} {Γ Δ Θ : MaximalConsistentSet 𝓢 Φ}

structure ILSuccessor (Γ Δ : MaximalConsistentSet 𝓢 Φ) : Prop where
  prop1 : (∀ φ ∈ Γ.1.prebox, φ ∈ Δ.1 ∧ □φ ∈ Δ.1)
  prop2 : (∃ φ ∈ Δ.1.prebox, □φ ∉ Γ.1)
infix:80 " < " => ILSuccessor

structure ILCriticalSuccessor (χ : { χ : Formula α // χ ∈ Φ.1}) (Γ Δ : MaximalConsistentSet 𝓢 Φ) extends Γ < Δ where
  prop3 : ∀ φ, φ ▷ χ.1 ∈ Γ.1 → -φ ∈ Δ.1 ∧ □-φ ∈ Δ.1
notation Γ:max " <[" χ "] " Δ:max => ILCriticalSuccessor χ Γ Δ

lemma claim1 (hΓΔ : Γ <[χ] Δ) (hΔΘ : Δ < Θ) : Γ <[χ] Θ where
  prop1 := by
    intro φ hφ;
    apply hΔΘ.prop1 φ;
    simpa using hΓΔ.prop1 _ hφ |>.2;
  prop2 := by
    rcases hΔΘ.prop2 with ⟨φ, hφ, h⟩;
    use φ;
    constructor;
    . assumption;
    . contrapose! h;
      apply hΓΔ.prop1 φ ?_ |>.2;
      simpa;
  prop3 := by
    intro φ hφ;
    rcases hΓΔ.prop3 φ hφ with ⟨h₁, h₂⟩;
    apply hΔΘ.prop1;
    simpa;

lemma claim3 (h₁ : ∼(φ ▷ χ.1) ∈ Γ.1) : ∃ Δ : MaximalConsistentSet 𝓢 Φ, (Γ <[χ] Δ) ∧ φ ∈ Δ.1 := by
  have : (φ ▷ χ.1) ∈ Φ.1 := Φ.2.compl_closed (∼(φ ▷ χ.1)) $ Γ.2.1 h₁;
  have : □-φ ∈ Φ.1 := Φ.2.mem_part₁ this |>.1;
  have : □-φ ∉ Γ.1 := by
    by_contra hC;
    sorry;
  let Δ₀ : FormulaFinset _ :=
    {φ, □-φ} ∪
    Γ.1.prebox ∪
    Γ.1.prebox.box ∪
    ((Γ.1.preimage (λ ξ => ξ ▷ χ.1) (by simp)) |>.image (λ ξ => -ξ)) ∪
    ((Γ.1.preimage (λ ξ => ξ ▷ χ.1) (by simp)) |>.image (λ ξ => □-ξ))
  have Δ₀_consis : Δ₀.Consistent 𝓢 := by sorry;
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : MaximalConsistentSet 𝓢 Φ, Δ₀ ⊆ Δ.1 := by
    sorry;
  use Δ;
  constructor;
  . exact {
      prop1 := by
        intro ψ hψ;
        simp at hψ;
        constructor;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; left; left; right;
          simpa;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; left; right;
          simpa;
      prop2 := by
        use (-φ);
        constructor;
        . suffices □-φ ∈ Δ.1 by simpa;
          apply hΔ;
          simp [Δ₀];
        . assumption;
      prop3 := by
        intro ψ hψ;
        constructor;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; right;
          suffices ∃ ξ, (ξ ▷ χ.1 ∈ Γ.1) ∧ -ξ = -ψ by simpa;
          use ψ;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          right;
          suffices ∃ ξ, (ξ ▷ χ.1 ∈ Γ.1) ∧ -ξ = -ψ by simpa;
          use ψ;
    }
  . apply hΔ;
    simp [Δ₀];

lemma claim4 (h₁ : (φ ▷ ψ) ∈ Γ.1) (h₂ : φ ∈ Δ.1) (h₃ : Γ <[χ] Δ)
  : ∃ Δ' : MaximalConsistentSet 𝓢 Φ, (Γ <[χ] Δ') ∧ ψ ∈ Δ'.1 ∧ □(-ψ) ∈ Δ'.1 := by
  have : □-ψ ∉ Γ.1 := by
    by_contra hC;
    sorry;
  let Δ₀ : FormulaFinset _ :=
    {ψ, □-ψ} ∪
    Γ.1.prebox ∪
    Γ.1.prebox.box ∪
    ((Γ.1.preimage (λ ξ => ξ ▷ χ) (by simp)) |>.image (λ ξ => -ξ)) ∪
    ((Γ.1.preimage (λ ξ => ξ ▷ χ) (by simp)) |>.image (λ ξ => □-ξ))

  have Δ₀_consis : Δ₀.Consistent 𝓢 := by sorry;
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : MaximalConsistentSet 𝓢 Φ, Δ₀ ⊆ Δ.1 := by
    sorry;
  use Δ;
  refine ⟨?_, ?_, ?_⟩;
  . exact {
      prop1 := by
        intro ψ hψ;
        simp at hψ;
        constructor;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; left; left; right;
          simpa;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; left; right;
          simpa;
      prop2 := by
        use (-ψ);
        constructor;
        . suffices □-ψ ∈ Δ.1 by simpa;
          apply hΔ;
          simp [Δ₀];
        . assumption;
      prop3 := by
        intro ψ hψ;
        constructor;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; right;
          suffices ∃ ξ, (ξ ▷ χ.1 ∈ Γ.1) ∧ -ξ = -ψ by simpa;
          use ψ;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          right;
          suffices ∃ ξ, (ξ ▷ χ.1 ∈ Γ.1) ∧ -ξ = -ψ by simpa;
          use ψ;
    }
  . apply hΔ; simp [Δ₀];
  . apply hΔ; simp [Δ₀];

end

open Veltman

namespace Veltman

variable {α : Type*} [DecidableEq α]
variable [Entailment S (Formula ℕ)]
variable {𝓢 : S} {Γ : MaximalConsistentSet 𝓢 Φ}

protected inductive ILMiniCanonicalModel.IsWorld (Γ : MaximalConsistentSet 𝓢 Φ) : MaximalConsistentSet 𝓢 Φ → List { φ // φ ∈ Φ.1 } → Prop
  | i₁              : ILMiniCanonicalModel.IsWorld Γ Γ []
  | i₂ {Δ Δ'} {τ}   : ILMiniCanonicalModel.IsWorld Γ Δ τ → Δ < Δ' → ILMiniCanonicalModel.IsWorld Γ Δ' τ
  | i₃ {Δ Δ'} {τ χ} : ILMiniCanonicalModel.IsWorld Γ Δ τ → Δ <[χ] Δ' → ILMiniCanonicalModel.IsWorld Γ Δ' (τ ++ [χ])

def ILMiniCanonicalModel (Γ : MaximalConsistentSet 𝓢 Φ) : Veltman.Model where
  toKripkeFrame := {
    World := { P : (MaximalConsistentSet 𝓢 Φ) × (List _) // ILMiniCanonicalModel.IsWorld Γ P.1 P.2 }
    world_nonempty := ⟨⟨(Γ, []), ILMiniCanonicalModel.IsWorld.i₁⟩⟩
    Rel X Y := ∃ χ, X.1.1 <[χ] Y.1.1 ∧ (∃ τ, Y.1.2 = X.1.2 ++ [χ] ++ τ)
  }
  S X U V :=
    X ≺ U.1 ∧
    X ≺ V.1 ∧
    (∃ χ, (∃ τ, U.1.1.2 = X.1.2 ++ [χ] ++ τ) ∧ (∃ τ, V.1.1.2 = X.1.2 ++ [χ] ++ τ))
  Val X p := (.atom p) ∈ X.1.1.1

instance : (ILMiniCanonicalModel Γ).IsFiniteGL where
  world_finite := by sorry
  trans X Y Z := by
    rintro ⟨χ₁, RXY, ⟨τ₁, hτ₁⟩⟩ ⟨χ₂, RYZ, ⟨τ₂, hτ₂⟩⟩;
    use χ₁;
    constructor;
    . exact claim1 RXY RYZ.1;
    . use τ₁ ++ [χ₂] ++ τ₂;
      simp [hτ₂, hτ₁];
  irrefl := by
    rintro _ ⟨_, _, ⟨_, hτ⟩⟩;
    simp at hτ;

instance : (ILMiniCanonicalModel Γ).IsIL where
  S_refl X := by
    constructor;
    rintro ⟨U, RXU⟩;
    refine ⟨RXU, RXU, ?_⟩;
    . rcases RXU with ⟨χ, RχXU, ⟨τ, hτ⟩⟩;
      tauto;
  S_trans X := by
    constructor;
    rintro ⟨U, RXU⟩ ⟨V, RXV⟩ ⟨W, RXW⟩ ⟨_, _, ⟨χ₁, ⟨⟨τ₁₁, hτ₁₁⟩, ⟨τ₁₂, hτ₁₂⟩⟩⟩⟩ ⟨_, _, ⟨χ₂, ⟨τ₂₁, hτ₂₁⟩, ⟨τ₂₂, hτ₂₂⟩⟩⟩;
    refine ⟨RXU, RXW, ?_⟩;
    simp_all;
  S_IL := by
    rintro X ⟨U, RXU⟩ ⟨V, RXV⟩ ⟨_, _, ⟨_, _⟩⟩;
    refine ⟨RXU, RXV, ?_⟩;
    rcases RXU with ⟨ξ, _, ⟨_, _⟩⟩;
    use ξ;
    simp_all;

instance : (ILMiniCanonicalModel Γ).IsFiniteIL where

open Formula.Veltman

lemma ILMiniCanonicalModel.truthlemma {X : ILMiniCanonicalModel Γ} (hφ : φ ∈ Φ.1) : X ⊧ φ ↔ φ ∈ X.1.1.1 := by
  induction φ generalizing X with
  | hfalsum => sorry;
  | hatom a => tauto;
  | himp φ ψ ihφ ihψ =>
    have := ihφ (X := X) (by sorry);
    have := ihψ (X := X) (by sorry);
    sorry;
  | hbox φ ih =>
    have := ih (X := X) (by sorry);
    sorry;
  | hrhd φ ψ ihφ ihψ =>
    let ψ : { χ // χ ∈ Φ.1} := ⟨ψ, by sorry⟩;
    suffices (∀ U : {V // X ≺ V}, U.1 ⊧ φ → ∃ V : {V // X ≺ V}, (ILMiniCanonicalModel Γ).S X U V ∧ V.1 ⊧ ψ.1) ↔ φ ▷ ψ ∈ X.1.1.1 by tauto
    constructor;
    . contrapose!;
      intro h;
      replace h : ∼(φ ▷ ψ) ∈ X.1.1.1 := by sorry;
      obtain ⟨Δ, hΔ₁, hΔ₂⟩ := claim3 h;
      use ⟨⟨⟨Δ, X.1.2 ++ [ψ]⟩, IsWorld.i₃ X.2 hΔ₁⟩, ⟨ψ, by simpa⟩⟩;
      constructor;
      . apply ihφ (by sorry) |>.mpr;
        simpa;
      . rintro V ⟨_, ⟨χ, hχXV, _⟩, h⟩;
        apply ihψ (by sorry) |>.not.mpr;
        have := hχXV.prop3 χ (by sorry) |>.1;
        sorry;
    . rintro h ⟨U, ⟨χ, hχXU, τ, eU₂⟩⟩ hU;
      replace hU := ihφ (by sorry) |>.mp hU;
      obtain ⟨Δ, hΔ₁, hΔ₂, hΔ₃⟩ := claim4 h hU hχXU;
      use ⟨⟨⟨Δ, X.1.2 ++ [χ]⟩, IsWorld.i₃ X.2 hΔ₁⟩, ⟨χ, by simpa⟩⟩;
      constructor;
      . refine ⟨?_, ?_, ?_⟩;
        . use χ; tauto;
        . use χ; simpa;
        . use χ;
          constructor;
          . use τ;
          . use []; simp;
      . apply ihψ (by sorry) |>.mpr;
        simpa;

end Veltman

open Formula.Veltman in
instance IL.Veltman.finite_complete : Complete InterpretabilityLogic.IL Veltman.FrameClass.FiniteIL := by
  constructor;
  intro φ;
  contrapose!
  intro hφ;
  apply not_validOnFrameClass_of_exists_model_world;
  let Φ : AdequateSet ℕ := ⟨{-φ}, by sorry⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : MaximalConsistentSet (InterpretabilityLogic.IL) Φ, {-φ} ⊆ Γ.1 := by sorry;
  use ILMiniCanonicalModel Γ, ⟨⟨Γ, []⟩, ILMiniCanonicalModel.IsWorld.i₁⟩;
  constructor;
  . apply Set.mem_setOf_eq.mpr;
    infer_instance;
  . apply ILMiniCanonicalModel.truthlemma (by sorry) |>.not.mpr;
    sorry;

end LO.InterpretabilityLogic
