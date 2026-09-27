module
public import Foundation.Propositional.Entailment.Int

@[expose] public section

namespace FFL.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev DNE := ∼∼φ 🡒 φ

protected abbrev LEM := φ ⋎ ∼φ

protected abbrev Peirce := ((φ 🡒 ψ) 🡒 φ) 🡒 φ

protected abbrev ElimContra := (∼ψ 🡒 ∼φ) 🡒 (φ 🡒 ψ)

end FFL.Axioms

namespace FFL.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomDNE (𝓢 : S) where
  dne {φ : F} : 𝓢 ⊢ Axioms.DNE φ
export HasAxiomDNE (dne)

attribute [simp] dne

@[grind ⇒] lemma of_NN [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼∼φ) : 𝓢 ⊢ φ := dne ⨀ b

section

variable [LogicalNeutral F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomDNE 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomDNE Γ := ⟨of dne⟩

end FiniteContext

namespace Context

instance [Entailment.HasAxiomDNE 𝓢] (Γ : Context F 𝓢) : HasAxiomDNE Γ := ⟨of dne⟩

end Context

end

class HasAxiomLEM (𝓢 : S) where
  lem {φ : F} : 𝓢 ⊢ Axioms.LEM φ
export HasAxiomLEM (lem)

attribute [simp] lem

section

variable [LogicalNeutral F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomLEM 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomLEM Γ := ⟨of lem⟩

end FiniteContext

namespace Context

instance [Entailment.HasAxiomLEM 𝓢] (Γ : Context F 𝓢) : HasAxiomLEM Γ := ⟨of lem⟩

end Context

end

class HasAxiomPeirce (𝓢 : S) where
  peirce {φ ψ : F} : 𝓢 ⊢ Axioms.Peirce φ ψ
export HasAxiomPeirce (peirce)

attribute [simp] peirce

section

variable [LogicalNeutral F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomPeirce 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomPeirce Γ := ⟨of peirce⟩

end FiniteContext

namespace Context

instance [Entailment.HasAxiomPeirce 𝓢] (Γ : Context F 𝓢) : HasAxiomPeirce Γ := ⟨of peirce⟩

end Context

end

class HasAxiomElimContra (𝓢 : S) where
  elim_contra {φ ψ : F} : 𝓢 ⊢ Axioms.ElimContra φ ψ
export HasAxiomElimContra (elim_contra)

attribute [simp] elim_contra

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F]
         {S : Type*} [Entailment S F]
         {𝓢 : S}
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

protected class Cl (𝓢 : S) extends Entailment.Minimal 𝓢, Entailment.HasAxiomDNE 𝓢

variable [Entailment.Cl 𝓢]

namespace FiniteContext
instance (Γ : FiniteContext F 𝓢) : Entailment.Cl Γ where
end FiniteContext

namespace Context
instance (Γ : Context F 𝓢) : Entailment.Cl Γ where
end Context

open NegationEquiv
open FiniteContext
open List

omit [DecidableEq F] in
open scoped Classical in
@[simp] lemma dn : 𝓢 ⊢ φ 🡘 ∼∼φ := E_intro dni dne

omit [DecidableEq F] in
open scoped Classical in
lemma A_of_ANNNN (d : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢ φ ⋎ ψ :=
  of_C_of_C_of_A (C_trans dne or₁) (C_trans dne or₂) d

omit [DecidableEq F] in
open scoped Classical in
lemma CN_of_CN_left (b : 𝓢 ⊢ ∼φ 🡒 ψ) : 𝓢 ⊢ ∼ψ 🡒 φ := C_trans (contra b) dne

omit [DecidableEq F] in
open scoped Classical in
@[simp] lemma CCNCN' : 𝓢 ⊢ (∼φ 🡒 ψ) 🡒 (∼ψ 🡒 φ) := deduct' <| CN_of_CN_left FiniteContext.id

omit [DecidableEq F] in
open scoped Classical in
lemma C_of_CNN (b : 𝓢 ⊢ ∼φ 🡒 ∼ψ) : 𝓢 ⊢ ψ 🡒 φ := C_trans dni (CN_of_CN_left b)

omit [DecidableEq F] in
open scoped Classical in
@[simp] lemma CCNNC : 𝓢 ⊢ (∼φ 🡒 ∼ψ) 🡒 (ψ 🡒 φ) := deduct' <| C_of_CNN FiniteContext.id

omit [DecidableEq F] in
open scoped Classical in
lemma EN_of_EN_right (h : 𝓢 ⊢ φ 🡘 ∼ψ) : 𝓢 ⊢ ∼φ 🡘 ψ := by
  apply E_intro;
  · apply CN_of_CN_left <| K_right h;
  · apply CN_of_CN_right <| K_left h;

omit [DecidableEq F] in
open scoped Classical in
lemma EN_of_EN_left (h : 𝓢 ⊢ ∼φ 🡘 ψ) : 𝓢 ⊢ φ 🡘 ∼ψ := E_symm <| EN_of_EN_right <| E_symm h

omit [DecidableEq F] in
open scoped Classical in
lemma ECCOO : 𝓢 ⊢ φ 🡘 ((φ 🡒 ⊥) 🡒 ⊥) := E_trans dn ENNCCOO

omit [DecidableEq F] in
open scoped Classical in
@[simp] lemma CNKANN : 𝓢 ⊢ ∼(φ ⋏ ψ) 🡒 (∼φ ⋎ ∼ψ) := by
  apply CN_of_CN_left;
  apply deduct';
  exact K_replace (KNN_of_NA <| FiniteContext.id) dne dne;

omit [DecidableEq F] in
open scoped Classical in
lemma ANN_of_NK (b : 𝓢 ⊢ ∼(φ ⋏ ψ)) : 𝓢 ⊢ ∼φ ⋎ ∼ψ := CNKANN ⨀ b

omit [DecidableEq F] in
open scoped Classical in
lemma AN_of_C (d : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ ∼φ ⋎ ψ := by
  apply of_NN;
  apply N_of_CO;
  apply deduct';
  have d₁ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼∼φ ⋏ ∼ψ := KNN_of_NA <| FiniteContext.id;
  have d₂ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼φ 🡒 ⊥ := CO_of_N <| K_left d₁;
  have d₃ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼φ := (of (Γ := [∼(∼φ ⋎ ψ)]) <| contra d) ⨀ (K_right d₁);
  exact d₂ ⨀ d₃;

omit [DecidableEq F] in
open scoped Classical in
lemma CCAN : 𝓢 ⊢ (φ 🡒 ψ) 🡒 (∼φ ⋎ ψ) := by
  apply deduct';
  apply AN_of_C;
  exact FiniteContext.by_axm;

omit [DecidableEq F] in
open scoped Classical in
instance : HasAxiomEFQ 𝓢 where
  efq {φ} := by
    apply C_of_CNN;
    exact C_trans (K_left neg_equiv) <| C_trans (C_swap implyK) (K_right neg_equiv);

omit [DecidableEq F] in
open scoped Classical in
instance : Entailment.Int 𝓢 where

omit [DecidableEq F] in
open scoped Classical in
instance : HasAxiomElimContra 𝓢 where
  elim_contra {φ ψ} := by
    apply deduct';
    have : [∼ψ 🡒 ∼φ] ⊢[𝓢] ∼ψ 🡒 ∼φ := FiniteContext.by_axm;
    exact C_of_CNN this;

omit [DecidableEq F] in
open scoped Classical in
instance : HasAxiomLEM 𝓢 := ⟨A_of_ANNNN <| AN_of_C dni⟩

omit [DecidableEq F] in
open scoped Classical in
lemma CNC_of_C_of_CN (hpq : 𝓢 ⊢ φ 🡒 ψ) (hpnr : 𝓢 ⊢ φ 🡒 ∼ξ) : 𝓢 ⊢ φ 🡒 ∼(ψ 🡒 ξ) :=
  deduct' <| (contra <| CCAN) ⨀
    (NA_of_KNN <| K_intro (dni' <| of' hpq ⨀ FiniteContext.by_axm)
      (of' hpnr ⨀ FiniteContext.by_axm))

omit [DecidableEq F] in
open scoped Classical in
theorem of_A_of_N (b : 𝓢 ⊢ φ ⋎ ψ) (d : 𝓢 ⊢ ∼φ) : 𝓢 ⊢ ψ := A_cases (C_of_CNN (dhyp d)) (C_id) b

omit [DecidableEq F] in
open scoped Classical in
theorem ECAN : 𝓢 ⊢ (φ 🡒 ψ) 🡘 (∼φ ⋎ ψ) := E_intro CCAN (deduct' (A_cases CNC implyK by_axm₀))

section

omit [DecidableEq F] in
open scoped Classical in
@[simp]
lemma CNDisj₂NConj₂ {Γ : List F} : 𝓢 ⊢ ∼⋁(Γ.map (∼·)) 🡒 ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons,
      List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    suffices 𝓢 ⊢ ∼(∼φ ⋎ ∼∼⋁List.map (fun x ↦ ∼x) Γ) 🡒 φ ⋏ ⋀Γ by
      apply C_trans ?_ this;
      apply contra;
      apply CAA_of_C_right;
      exact dne;
    apply C_trans CNAKNN ?_;
    apply CKK_of_C_of_C;
    · exact dne;
    · exact C_trans dne ih;

lemma CNFdisj₂NFconj₂ {Γ : Finset F} : 𝓢 ⊢ ∼(Γ.image (∼·)).disj 🡒 Γ.conj := by
  apply C_replace ?_ ?_ <| CNDisj₂NConj₂ (Γ := Γ.toList);
  · apply contra;
    apply left_Disj₂_intro;
    intro ψ hψ;
    apply right_Fdisj_intro;
    simpa using hψ;
  · simp;

end

section consistency

omit [Entailment.Cl 𝓢]

variable [AdjunctiveSet F S] [Axiomatized S] [Deduction S] [∀ 𝓢 : S, Entailment.Cl 𝓢]

omit [DecidableEq F] in
open scoped Classical in
lemma provable_iff_inconsistent_adjoin {φ : F} :
    𝓢 ⊢ φ ↔ Inconsistent (adjoin (∼φ) 𝓢) := by
  constructor
  · intro h
    apply inconsistent_of_provable_of_unprovable (φ := φ)
    · exact Axiomatized.to_adjoin h
    · exact Axiomatized.adjoin _ _
  · intro h
    have : 𝓢 ⊢ ∼φ 🡒 ⊥ := Deduction.ofInsert (h _)
    refine of_NN <| N_iff_CO.mpr this

omit [DecidableEq F] in
open scoped Classical in
lemma unprovable_iff_consistent_adjoin {φ : F} :
    𝓢 ⊬ φ ↔ Consistent (adjoin (∼φ) 𝓢) := by
  simpa using provable_iff_inconsistent_adjoin.not

omit [DecidableEq F] in
instance deductiveExplosion : Entailment.DeductiveExplosion S := inferInstance

end consistency

section

omit [DecidableEq F] in
open scoped Classical in
instance : HasAxiomPeirce 𝓢 where
  peirce {φ ψ} := by
    apply of_C_of_C_of_A implyK ?_ lem;
    apply deduct';
    apply deduct;
    refine (FiniteContext.by_axm (φ := (φ 🡒 ψ) 🡒 φ)) ⨀ ?_;
    apply deduct;
    apply efq_of_mem_either (φ := φ);
    · simp;
    · simp;

omit [DecidableEq F] in
open scoped Classical in
instance : HasAxiomEFQ 𝓢 := inferInstance

omit [DecidableEq F] in
open scoped Classical in
instance : Entailment.Int 𝓢 where

end

section

variable {G T : Type*} [Entailment T G] [LogicalConnective G] [LogicalNeutral G] {𝓣 : T}

abbrev Cl.ofEquiv (𝓢 : S) [Entailment.Cl 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : ∀ φ, 𝓢 ⊢ f φ ↔ 𝓣 ⊢ φ) :
    Entailment.Cl 𝓣 where
  mdp {φ ψ} dpq dp := (e ψ).mp <| (by simpa using (e (φ 🡒 ψ)).mpr dpq) ⨀ (e φ).mpr dp
  neg_equiv := (e _).mp (by simp)
  verum := (e _).mp (by simp)
  implyK := (e _).mp (by simp)
  implyS := (e _).mp (by simp)
  and₁ := (e _).mp (by simp)
  and₂ := (e _).mp (by simp)
  and₃ := (e _).mp (by simp)
  or₁ := (e _).mp (by simp)
  or₂ := (e _).mp (by simp)
  or₃ := (e _).mp (by simp)
  dne := (e _).mp (by simp)

end

section

variable {S F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F] [Entailment S F]
         {𝓢 : S} [Entailment.Int 𝓢]

open FiniteContext

instance [HasAxiomLEM 𝓢] : HasAxiomDNE 𝓢 where
  dne {φ} := by
    apply deduct';
    exact of_C_of_C_of_A C_id (by
      apply deduct;
      have nnp : [∼φ, ∼∼φ] ⊢[𝓢] ∼φ 🡒 ⊥ := CO_of_N <| FiniteContext.by_axm;
      have np : [∼φ, ∼∼φ] ⊢[𝓢] ∼φ := FiniteContext.by_axm;
      exact of_O <| nnp ⨀ np;
    ) <| of lem;

instance [HasAxiomLEM 𝓢] : Entailment.Cl 𝓢 where

end

end FFL.Entailment

end
