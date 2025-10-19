import Foundation.Propositional.Entailment.Int.Basic

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev DNE := ∼∼φ ➝ φ

protected abbrev ElimContra := (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment F S]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomDNE (𝓢 : S)  where
  dne {φ : F} : 𝓢 ⊢! Axioms.DNE φ
export HasAxiomDNE (dne)

@[simp] lemma dne! [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼φ ➝ φ  := ⟨dne⟩

def of_NN [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼∼φ) : 𝓢 ⊢! φ := dne ⨀ b
lemma of_NN! [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ ∼∼φ) : 𝓢 ⊢ φ := ⟨of_NN h.some⟩


class HasAxiomElimContra (𝓢 : S)  where
  elimContra {φ ψ : F} : 𝓢 ⊢! Axioms.ElimContra φ ψ
export HasAxiomElimContra (elimContra)

@[simp] lemma elim_contra! [HasAxiomElimContra 𝓢] : 𝓢 ⊢ (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)  := ⟨elimContra⟩


protected class Cl (𝓢 : S) extends Entailment.Minimal 𝓢, Entailment.HasAxiomDNE 𝓢


section

variable [LogicalConnective F] [Entailment F S] [Entailment.Minimal 𝓢]

namespace FiniteContext

variable {Γ Δ E : List F}

instance [Entailment.HasAxiomDNE 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomDNE Γ := ⟨of dne⟩

instance [Entailment.Cl 𝓢] (Γ : FiniteContext F 𝓢) : Entailment.Cl Γ where

end FiniteContext


namespace Context

instance [Entailment.HasAxiomDNE 𝓢] (Γ : Context F 𝓢) : HasAxiomDNE Γ := ⟨of dne⟩

instance [DecidableEq F] [Entailment.Cl 𝓢] (Γ : Context F 𝓢) : Entailment.Cl Γ where

end Context

end



section

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Cl 𝓢]
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open List

def dn : 𝓢 ⊢! φ ⭤ ∼∼φ := E_intro dni dne
@[simp] lemma dn! : 𝓢 ⊢ φ ⭤ ∼∼φ := ⟨dn⟩

def A_of_ANNNN (d : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢! φ ⋎ ψ := of_C_of_C_of_A (C_trans dne or₁) (C_trans dne or₂) d
omit [DecidableEq F] in lemma A!_of_ANNNN! (d : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢ φ ⋎ ψ := ⟨A_of_ANNNN d.some⟩

def CN_of_CN_left (b : 𝓢 ⊢! ∼φ ➝ ψ) : 𝓢 ⊢! ∼ψ ➝ φ := C_trans (contra b) dne
lemma CN!_of_CN!_left (b : 𝓢 ⊢ ∼φ ➝ ψ) : 𝓢 ⊢ ∼ψ ➝ φ := ⟨CN_of_CN_left b.some⟩

def CCNCN' : 𝓢 ⊢! (∼φ ➝ ψ) ➝ (∼ψ ➝ φ) := deduct' $ CN_of_CN_left FiniteContext.id
@[simp] lemma CCNCN'! : 𝓢 ⊢ (∼φ ➝ ψ) ➝ (∼ψ ➝ φ) := ⟨CCNCN'⟩


def C_of_CNN (b : 𝓢 ⊢! ∼φ ➝ ∼ψ) : 𝓢 ⊢! ψ ➝ φ := C_trans dni (CN_of_CN_left b)
lemma C!_of_CNN! (b : 𝓢 ⊢ ∼φ ➝ ∼ψ) : 𝓢 ⊢ ψ ➝ φ := ⟨C_of_CNN b.some⟩

instance : HasAxiomElimContra 𝓢 where
  elimContra {φ ψ} := by
    apply deduct';
    have : [∼ψ ➝ ∼φ] ⊢[𝓢]! ∼ψ ➝ ∼φ := FiniteContext.byAxm;
    exact C_of_CNN this;


def CCNNC : 𝓢 ⊢! (∼φ ➝ ∼ψ) ➝ (ψ ➝ φ) :=  deduct' $ C_of_CNN FiniteContext.id
@[simp] lemma CCNNC! : 𝓢 ⊢ (∼φ ➝ ∼ψ) ➝ (ψ ➝ φ) := ⟨CCNNC⟩

def EN_of_EN_right (h : 𝓢 ⊢! φ ⭤ ∼ψ) : 𝓢 ⊢! ∼φ ⭤ ψ := by
  apply E_intro;
  . apply CN_of_CN_left $  K_right h;
  . apply CN_of_CN_right $  K_left h;
lemma EN!_of_EN!_right (h : 𝓢 ⊢ φ ⭤ ∼ψ) : 𝓢 ⊢ ∼φ ⭤ ψ := ⟨EN_of_EN_right h.some⟩

def EN_of_EN_left (h : 𝓢 ⊢! ∼φ ⭤ ψ) : 𝓢 ⊢! φ ⭤ ∼ψ := E_symm $ EN_of_EN_right $ E_symm h
lemma EN!_of_EN!_left (h : 𝓢 ⊢ ∼φ ⭤ ψ) : 𝓢 ⊢ φ ⭤ ∼ψ := ⟨EN_of_EN_left h.some⟩

def ECCOO : 𝓢 ⊢! φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := E_trans dn ENNCCOO
lemma ECCOO! : 𝓢 ⊢ φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := ⟨ECCOO⟩


def CNKANN : 𝓢 ⊢! ∼(φ ⋏ ψ) ➝ (∼φ ⋎ ∼ψ) := by
  apply CN_of_CN_left;
  apply deduct';
  exact K_replace (KNN_of_NA $ FiniteContext.id) dne dne;
@[simp] lemma CNKANN! : 𝓢 ⊢ ∼(φ ⋏ ψ) ➝ (∼φ ⋎ ∼ψ) := ⟨CNKANN⟩

def ANN_of_NK (b : 𝓢 ⊢! ∼(φ ⋏ ψ)) : 𝓢 ⊢! ∼φ ⋎ ∼ψ := CNKANN ⨀ b
lemma ANN!_of_NK! (b : 𝓢 ⊢ ∼(φ ⋏ ψ)) : 𝓢 ⊢ ∼φ ⋎ ∼ψ := ⟨ANN_of_NK b.some⟩

def AN_of_C (d : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼φ ⋎ ψ := by
  apply of_NN;
  apply N_of_CO;
  apply deduct';
  have d₁ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼∼φ ⋏ ∼ψ := KNN_of_NA $ FiniteContext.id;
  have d₂ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼φ ➝ ⊥ := CO_of_N $ K_left d₁;
  have d₃ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼φ := (of (Γ := [∼(∼φ ⋎ ψ)]) $ contra d) ⨀ (K_right d₁);
  exact d₂ ⨀ d₃;
lemma AN!_of_C! (d : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼φ ⋎ ψ := ⟨AN_of_C d.some⟩

def CCAN : 𝓢 ⊢! (φ ➝ ψ) ➝ (∼φ ⋎ ψ) := by
  apply deduct';
  apply AN_of_C;
  exact FiniteContext.byAxm;
lemma CCAN! : 𝓢 ⊢ (φ ➝ ψ) ➝ ∼φ ⋎ ψ := ⟨CCAN⟩

instance : HasAxiomEFQ 𝓢 where
  efq {φ} := by
    apply C_of_CNN;
    exact C_trans (K_left negEquiv) $ C_trans (C_swap imply₁) (K_right negEquiv);

instance : Entailment.Cl 𝓢 where
instance Cl.toInt (𝓢 : S) [Entailment.Cl 𝓢] : Entailment.Int 𝓢 where


lemma not_imply_prem''! (hpq : 𝓢 ⊢ φ ➝ ψ) (hpnr : 𝓢 ⊢ φ ➝ ∼ξ) : 𝓢 ⊢ φ ➝ ∼(ψ ➝ ξ) :=
  deduct'! $ (contra! $ CCAN!) ⨀ (NA!_of_KNN! $ K!_intro (dni'! $ of'! hpq ⨀ (by_axm!)) (of'! hpnr ⨀ (by_axm!)))

def ofAOfN (b : 𝓢 ⊢! φ ⋎ ψ) (d : 𝓢 ⊢! ∼φ) : 𝓢 ⊢! ψ := A_cases (C_of_CNN (dhyp d)) (C_id) b

def of_a!_of_n! (b : 𝓢 ⊢ φ ⋎ ψ) (d : 𝓢 ⊢ ∼φ) : 𝓢 ⊢ ψ := ⟨ofAOfN b.get d.get⟩

def ECAN : 𝓢 ⊢! (φ ➝ ψ) ⭤ (∼φ ⋎ ψ) := E_intro CCAN (deduct' (A_cases CNC imply₁ byAxm₀))
def ECAN! : 𝓢 ⊢ (φ ➝ ψ) ⭤ (∼φ ⋎ ψ) := ⟨ECAN⟩



section

@[simp]
lemma CNDisj₂NConj₂! {Γ : List F} : 𝓢 ⊢ ∼⋁(Γ.map (∼·)) ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons, List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    suffices 𝓢 ⊢ ∼(∼φ ⋎ ∼∼⋁List.map (fun x ↦ ∼x) Γ) ➝ φ ⋏ ⋀Γ by
      apply C!_trans ?_ this;
      apply contra!;
      apply CAA!_of_C!_right;
      exact dne!;
    apply C!_trans CNAKNN! ?_;
    apply CKK!_of_C!_of_C!;
    . exact dne!;
    . exact C!_trans dne! ih;

lemma CNFdisj₂NFconj₂! {Γ : Finset F} : 𝓢 ⊢ ∼(Γ.image (∼·)).disj ➝ Γ.conj := by
  apply C!_replace ?_ ?_ $ CNDisj₂NConj₂! (Γ := Γ.toList);
  . apply contra!;
    apply left_Disj₂!_intro;
    intro ψ hψ;
    apply right_Fdisj!_intro;
    simpa using hψ;
  . simp;

end


section consistency

variable [AdjunctiveSet F S] [Axiomatized S] [Deduction S] [∀ 𝓢 : S, Entailment.Cl 𝓢]

omit [Entailment.Cl 𝓢] in
lemma provable_iff_inconsistent_adjoin {φ : F} :
    𝓢 ⊢ φ ↔ Inconsistent (adjoin (∼φ) 𝓢) := by
  constructor
  · intro h
    apply inconsistent_of_provable_of_unprovable (φ := φ)
    · exact Axiomatized.to_adjoin h
    · exact Axiomatized.adjoin! _ _
  · intro h
    have : 𝓢 ⊢ ∼φ ➝ ⊥ := Deduction.of_insert! (h _)
    refine of_NN! <| N!_iff_CO!.mpr this

end consistency

end


end LO.Entailment
