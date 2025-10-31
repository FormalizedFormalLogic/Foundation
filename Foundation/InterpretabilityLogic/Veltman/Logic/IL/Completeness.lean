import Foundation.InterpretabilityLogic.Veltman.Logic.IL.Soundness
import Foundation.InterpretabilityLogic.Formula.Subformula
import Foundation.InterpretabilityLogic.Formula.Complement
import Foundation.Propositional.CMCF

namespace LO.InterpretabilityLogic

variable {α : Type*} [DecidableEq α]
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

open Modal (Kripke.Frame Kripke.Model)

namespace FormulaFinset

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

namespace Adequate

variable {Φ : FormulaFinset α} [Φ.Adequate]

@[grind ⇒] lemma mem_imp (h : φ ➝ ψ ∈ Φ) : φ ∈ Φ ∧ ψ ∈ Φ := SubformulaClosed.mem_imp h
@[grind ⇒] lemma mem_box (h : □φ ∈ Φ) : φ ∈ Φ := SubformulaClosed.mem_box h
@[grind ⇒] lemma mem_rhd (h : φ ▷ ψ ∈ Φ) : φ ∈ Φ ∧ ψ ∈ Φ := SubformulaClosed.mem_rhd h

end Adequate

end FormulaFinset



section

def AdequateSet (α) [DecidableEq α] := { Φ : FormulaFinset α // Φ.Adequate }

namespace AdequateSet

variable {Φ : AdequateSet α}

@[grind ⇒] lemma mem_imp (h : φ ➝ ψ ∈ Φ.1) : φ ∈ Φ.1 ∧ ψ ∈ Φ.1 := Φ.2.mem_imp h
@[grind ⇒] lemma mem_box (h : □φ ∈ Φ.1) : φ ∈ Φ.1 := Φ.2.mem_box h
@[grind ⇒] lemma mem_rhd (h : φ ▷ ψ ∈ Φ.1) : φ ∈ Φ.1 ∧ ψ ∈ Φ.1 := Φ.2.mem_rhd h

end AdequateSet


open Finset.LO
open LO.ComplementMaximalConsistentFinset

-- def MaximalConsistentSet (𝓢 : S) (Φ : AdequateSet α) := { Ψ : FormulaFinset α // Ψ ⊆ Φ.1 ∧ Ψ.Maximal 𝓢 ∧ Ψ.Consistent 𝓢 }

variable {Φ : AdequateSet α} {Γ Δ Θ : { Γ : ComplementMaximalConsistentFinset 𝓢 Φ.1 // Γ.1 ⊆ Φ.1 }}

structure ILSuccessor (Γ Δ : { Γ : ComplementMaximalConsistentFinset 𝓢 Φ.1 // Γ.1 ⊆ Φ.1 }) : Prop where
  prop1 : (∀ φ ∈ Γ.1.1.prebox, φ ∈ Δ.1 ∧ □φ ∈ Δ.1)
  prop2 : (∃ φ ∈ Δ.1.1.prebox, □φ ∉ Γ.1)
infix:80 " ≺ " => ILSuccessor

structure ILCriticalSuccessor (χ : { χ : Formula α // χ ∈ Φ.1}) (Γ Δ : { Γ : ComplementMaximalConsistentFinset 𝓢 Φ.1 // Γ.1 ⊆ Φ.1 }) extends Γ ≺ Δ where
  prop3 : ∀ φ, φ ▷ χ.1 ∈ Γ.1 → -φ ∈ Δ.1 ∧ □-φ ∈ Δ.1
notation Γ:max " ≺[" χ "] " Δ:max => ILCriticalSuccessor χ Γ Δ

lemma claim1 (hΓΔ : Γ ≺[χ] Δ) (hΔΘ : Δ ≺ Θ) : Γ ≺[χ] Θ where
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

open LO.InterpretabilityLogic.Entailment
open LO.Entailment
open LO.Modal.Entailment

omit [DecidableEq α] in
lemma claim2_1 [Entailment.IL 𝓢] : 𝓢 ⊢ (φ ⋎ ◇φ) ▷ φ := by
  apply (J3 (𝓢 := 𝓢)) ⨀ ?_ ⨀ ?_;
  . -- TODO: 𝓢 ⊢ φ ▷ φ
    apply J1 (𝓢 := 𝓢) ⨀ (nec! C!_id);
  . apply J5;

lemma claim2_2 [Entailment.IL 𝓢] : 𝓢 ⊢ φ ▷ (φ ⋏ □(∼φ)) := by
  apply rhd_trans ?_ claim2_1;
  apply rhd_of_lc;
  apply nec!;
  suffices 𝓢 ⊢ ∼◇(φ ⋏ □(∼φ)) ➝ □(∼φ) by cl_prover [this]
  apply C!_replace (CN!_of_CN!_left INLNM) axiomL!;
  apply box_regularity!;
  cl_prover;

lemma claim3 [Entailment.IL 𝓢] (h₁ : ∼(φ ▷ χ.1) ∈ Γ.1) : ∃ Δ, (Γ ≺[χ] Δ) ∧ φ ∈ Δ.1 := by
  have : (φ ▷ χ.1) ∈ Φ.1 := Φ.2.compl_closed (∼(φ ▷ χ.1)) $ Γ.2 h₁;
  have : □-φ ∈ Φ.1 := Φ.2.mem_part₁ this |>.1;
  have : □-φ ∉ Γ.1 := by
    by_contra hC;
    replace hC : Γ *⊢[𝓢] □-φ := ComplementMaximalConsistentFinset.membership_iff (by simpa) |>.mp hC;
    apply ComplementMaximalConsistentFinset.iff_mem_compl (by simpa) |>.mpr $ Formula.complement.rhd_def ▸ h₁;
    apply ComplementMaximalConsistentFinset.membership_iff (by simpa) |>.mpr;
    apply (show Γ *⊢[𝓢] □(φ ➝ χ.1) ➝ (φ ▷ χ.1) by exact Entailment.Context.of! $ J1) ⨀ ?_;
    apply (Entailment.Context.of! $ ?_) ⨀ hC;
    apply box_regularity!;
    apply C!_trans $ C_of_E_mpr! $ compl_equiv;
    exact CNC!;
  let Ξ₁ := Γ.1.1.prebox;
  let Ξ₂ := (Γ.1.1.preimage (λ ξ => ξ ▷ χ.1) (by simp));
  let Δ₁ : FormulaFinset _ := {φ, □-φ}
  let Δ₂ : FormulaFinset _ := Ξ₁
  let Δ₃ : FormulaFinset _ := Ξ₁.box
  let Δ₄ : FormulaFinset _ := Ξ₂.image (λ ξ => -ξ)
  let Δ₅ : FormulaFinset _ := Ξ₂.image (λ ξ => □(-ξ))
  let Δ : FormulaFinset _ := Δ₁ ∪ Δ₂ ∪ Δ₃ ∪ Δ₄ ∪ Δ₅
  have Δ_consis : Consistent 𝓢 Δ := by
    by_contra!;
    obtain ⟨Θ, hΘ₁, H⟩ := def_inconsistent.mp this;
    replace H : Δ *⊢[𝓢] ⊥ := Context.weakening! hΘ₁ H;
    rw [show Δ = ((Δ₂ ∪ Δ₃) ∪ Δ₁ ∪ (Δ₄ ∪ Δ₅)) by grind] at H;
    replace H : 𝓢 ⊢ (Δ₂ ∪ Δ₃).conj ⋏ Δ₁.conj ➝ Finset.conj (Δ₄ ∪ Δ₅) ➝ ⊥ :=
      C!_trans CKFconjFconjUnion! $ CK!_iff_CC!.mp $ C!_trans CKFconjFconjUnion! $ FConj_DT.mpr H;
    replace H : 𝓢 ⊢ (Δ₂ ∪ Δ₃).conj ➝ (Δ₁.conj ➝ (∼(Δ₄ ∪ Δ₅).conj)) := by cl_prover [H];
    replace H : 𝓢 ⊢ □Δ₂.conj ➝ □(Δ₁.conj ➝ ∼(Δ₄ ∪ Δ₅).conj) := C!_trans ?_ $ box_regularity! H;
    replace H : 𝓢 ⊢ □Δ₂.conj ➝ Δ₁.conj ▷ ∼(Δ₄ ∪ Δ₅).conj := C!_trans H J1;
    replace H : 𝓢 ⊢ □Δ₂.conj ➝ ((φ ⋏ □(∼φ)) ▷ (Ξ₂.disj ⋎ ◇Ξ₂.disj)) := by sorry;
    replace H : 𝓢 ⊢ □Δ₂.conj ➝ (φ ▷ Ξ₂.disj) := by
      have H₁ : 𝓢 ⊢ ((φ ⋏ □(∼φ)) ▷ (Ξ₂.disj ⋎ ◇Ξ₂.disj)) ➝ ((Ξ₂.disj ⋎ ◇Ξ₂.disj) ▷ Ξ₂.disj) ➝ ((φ ⋏ □(∼φ)) ▷ Ξ₂.disj) := J2
      have H₂ : 𝓢 ⊢ (φ ▷ (φ ⋏ □(∼φ))) ➝ ((φ ⋏ □(∼φ)) ▷ Ξ₂.disj) ➝ (φ ▷ Ξ₂.disj) := J2
      have H₃ : 𝓢 ⊢ (Ξ₂.disj ⋎ ◇Ξ₂.disj) ▷ Ξ₂.disj := claim2_1
      have H₄ : 𝓢 ⊢ φ ▷ (φ ⋏ □(∼φ)) := claim2_2;
      cl_prover [H, H₁, H₂, H₃, H₄]
    replace H : 𝓢 ⊢ (□Δ₂.conj ⋏ (Ξ₂.image (λ ξ => ξ ▷ χ.1)).conj) ➝ (φ ▷ χ.1) := by
      have H₁ : 𝓢 ⊢ (Ξ₂.image (λ ξ => ξ ▷ χ.1)).conj ➝ (Ξ₂.disj ▷ χ) := by sorry
      have H₂ : 𝓢 ⊢ (φ ▷ Ξ₂.disj) ➝ (Ξ₂.disj ▷ χ) ➝ (φ ▷ χ) := J2;
      cl_prover [H, H₁, H₂];
    replace H := H ⨀ ?_;
    . sorry;
    . sorry;
    . sorry;
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : ComplementMaximalConsistentFinset 𝓢 Φ.1, Δ ⊆ Ω.1 := ComplementMaximalConsistentFinset.lindenbaum Δ_consis;
  sorry;
  /-
  use ⟨Δ, by sorry⟩;
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
  -/

lemma claim4 (h₁ : (φ ▷ ψ) ∈ Γ.1) (h₂ : φ ∈ Δ.1) (h₃ : Γ ≺[χ] Δ)
  : ∃ Δ', (Γ ≺[χ] Δ') ∧ ψ ∈ Δ'.1 ∧ □(-ψ) ∈ Δ'.1 := by
  have : □-ψ ∉ Γ.1 := by
    by_contra hC;
    sorry;
  let Δ₀ : FormulaFinset _ :=
    {ψ, □-ψ} ∪
    Γ.1.1.prebox ∪
    Γ.1.1.prebox.box ∪
    ((Γ.1.1.preimage (λ ξ => ξ ▷ χ) (by simp)) |>.image (λ ξ => -ξ)) ∪
    ((Γ.1.1.preimage (λ ξ => ξ ▷ χ) (by simp)) |>.image (λ ξ => □-ξ))

  have Δ₀_consis : Consistent 𝓢 Δ := by sorry;
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ComplementMaximalConsistentFinset 𝓢 Φ.1, Δ₀ ⊆ Δ.1 := by
    sorry;
  use ⟨Δ, by sorry⟩;
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
variable {Φ : AdequateSet _} {𝓢 : S} {Γ : { Γ : ComplementMaximalConsistentFinset 𝓢 Φ.1 // Γ.1 ⊆ Φ.1 }}

protected inductive ILMiniCanonicalModel.IsWorld (Γ : { Γ : ComplementMaximalConsistentFinset 𝓢 Φ.1 // Γ.1 ⊆ Φ.1 })
  : { Γ : ComplementMaximalConsistentFinset 𝓢 Φ.1 // Γ.1 ⊆ Φ.1 } × List { φ // φ ∈ Φ.1 } → Prop
  | i₁              : ILMiniCanonicalModel.IsWorld Γ ⟨Γ, []⟩
  | i₂ {Δ Δ'} {τ}   : ILMiniCanonicalModel.IsWorld Γ ⟨Δ, τ⟩ → Δ < Δ' → ILMiniCanonicalModel.IsWorld Γ ⟨Δ', τ⟩
  | i₃ {Δ Δ'} {τ χ} : ILMiniCanonicalModel.IsWorld Γ ⟨Δ, τ⟩ → Δ ≺[χ] Δ' → ILMiniCanonicalModel.IsWorld Γ ⟨Δ', (τ ++ [χ])⟩

def ILMiniCanonicalModel (Γ : { Γ : ComplementMaximalConsistentFinset 𝓢 Φ.1 // Γ.1 ⊆ Φ.1 }) : Veltman.Model where
  toKripkeFrame := {
    World := { P // ILMiniCanonicalModel.IsWorld Γ P }
    world_nonempty := ⟨⟨(Γ, []), ILMiniCanonicalModel.IsWorld.i₁⟩⟩
    Rel X Y := ∃ χ, X.1.1 ≺[χ] Y.1.1 ∧ (∃ τ, Y.1.2 = X.1.2 ++ [χ] ++ τ)
  }
  S X U V :=
    X ≺ U.1 ∧
    X ≺ V.1 ∧
    (∃ χ, (∃ τ, U.1.1.2 = X.1.2 ++ [χ] ++ τ) ∧ (∃ τ, V.1.1.2 = X.1.2 ++ [χ] ++ τ))
  Val X p := (.atom p) ∈ X.1.1.1

instance : (ILMiniCanonicalModel Γ).IsFiniteGL where
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
  world_finite := by
    simp [ILMiniCanonicalModel];
    sorry

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

lemma ILMiniCanonicalModel.truthlemma [Entailment.IL 𝓢] {X : ILMiniCanonicalModel Γ} (hφ : φ ∈ Φ.1) : X ⊧ φ ↔ φ ∈ X.1.1.1 := by
  induction φ generalizing X with
  | hfalsum => sorry;
  | hatom a => tauto;
  | himp φ ψ ihφ ihψ =>
    suffices φ ∈ X.1.1.1 → ψ ∈ X.1.1.1 ↔ φ ➝ ψ ∈ X.1.1.1 by simpa [Satisfies, (ihφ (X := X) (by grind)), ihψ (X := X) (by grind)];
    sorry;
  | hbox φ ih =>
    have := ih (X := X) (by grind);
    sorry;
  | hrhd φ ψ ihφ ihψ =>
    let ψ : { χ // χ ∈ Φ.1} := ⟨ψ, by grind⟩;
    suffices (∀ U : {V // X ≺ V}, U.1 ⊧ φ → ∃ V : {V // X ≺ V}, (ILMiniCanonicalModel Γ).S X U V ∧ V.1 ⊧ ψ.1) ↔ φ ▷ ψ ∈ X.1.1.1 by tauto
    constructor;
    . contrapose!;
      intro h;
      replace h : ∼(φ ▷ ψ) ∈ X.1.1.1 := by sorry;
      obtain ⟨Δ, hΔ₁, hΔ₂⟩ := claim3 h;
      use ⟨⟨⟨Δ, X.1.2 ++ [ψ]⟩, IsWorld.i₃ X.2 hΔ₁⟩, ⟨ψ, by simpa⟩⟩;
      constructor;
      . apply ihφ (by grind) |>.mpr;
        simpa;
      . rintro V ⟨_, ⟨χ, hχXV, _⟩, h⟩;
        apply ihψ (by grind) |>.not.mpr;
        have := hχXV.prop3 χ (by sorry) |>.1;
        sorry;
    . rintro h ⟨U, ⟨χ, hχXU, τ, eU₂⟩⟩ hU;
      replace hU := ihφ (by grind) |>.mp hU;
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
      . apply ihψ (by grind) |>.mpr;
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
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ComplementMaximalConsistentFinset (InterpretabilityLogic.IL) Φ.1, {-φ} ⊆ Γ.1 := ComplementMaximalConsistentFinset.lindenbaum (by sorry)
  use ILMiniCanonicalModel ⟨Γ, by sorry⟩, ⟨⟨⟨Γ, _⟩, []⟩, ILMiniCanonicalModel.IsWorld.i₁⟩;
  constructor;
  . apply Set.mem_setOf_eq.mpr;
    infer_instance;
  . apply ILMiniCanonicalModel.truthlemma (by sorry) |>.not.mpr;
    simp;
    sorry;

end LO.InterpretabilityLogic
