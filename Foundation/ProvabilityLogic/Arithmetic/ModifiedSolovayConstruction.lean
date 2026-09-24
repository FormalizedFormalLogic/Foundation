module

public import Foundation.ProvabilityLogic.Arithmetic.ModifiedSolovaySentences
public import Foundation.ProvabilityLogic.Arithmetic.SolovaySentences

/-!
# Construction of modified Solovay sentences
-/

@[expose] public section

noncomputable section

open FFL.Entailment

namespace FFL.FirstOrder.Arithmetic.Bootstrapping.ModifiedSolovaySentences

open ProvabilityLogic Kripke Kripke.Model Kripke.Model.World

section comparison

variable {V : Type*} [ORingStructure V]

/-- A witness of `P` appears no later than any witness of `Q`. -/
def WitnessLE (P Q : V → Prop) : Prop := ∃ w, P w ∧ ∀ v < w, ¬Q v

/-- A witness of `P` appears strictly before any witness of `Q`. -/
def WitnessLT (P Q : V → Prop) : Prop := ∃ w, P w ∧ ∀ v ≤ w, ¬Q v

def cmpLE (P : 𝚺₁.Semisentence 2) (Q : 𝚷₁.Semisentence 2) : 𝚺₁.Semisentence 2 := .mkSigma
  “a b. ∃ w, !P.val w a ∧ ∀ v < w, ¬!Q.val v b”

def cmpLT (P : 𝚺₁.Semisentence 2) (Q : 𝚷₁.Semisentence 2) : 𝚺₁.Semisentence 2 := .mkSigma
  “a b. ∃ w, !P.val w a ∧ ∀ v <⁺ w, ¬!Q.val v b”

@[simp] lemma val_cmpLE {P : 𝚺₁.Semisentence 2} {Q : 𝚷₁.Semisentence 2} {a b : V} :
    V ⊧/![a, b] (cmpLE P Q).val ↔
      WitnessLE (fun w ↦ V ⊧/![w, a] P.val) (fun w ↦ V ⊧/![w, b] Q.val) := by
  simp [cmpLE, WitnessLE]

@[simp] lemma val_cmpLT [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {P : 𝚺₁.Semisentence 2} {Q : 𝚷₁.Semisentence 2} {a b : V} :
    V ⊧/![a, b] (cmpLT P Q).val ↔
      WitnessLT (fun w ↦ V ⊧/![w, a] P.val) (fun w ↦ V ⊧/![w, b] Q.val) := by
  simp [cmpLT, WitnessLT, Semiformula.ballLTSucc, lt_succ_iff_le]

variable {P Q : V → Prop}

lemma WitnessLE.exists : WitnessLE P Q → ∃ w, P w := fun ⟨w, hw, _⟩ ↦ ⟨w, hw⟩

lemma WitnessLE.not_witnessLT [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : WitnessLE P Q → ¬WitnessLT Q P := by
  rintro ⟨w, hw, h⟩ ⟨w', hw', h'⟩;
  rcases lt_or_ge w' w with hlt | hge;
  · exact h w' hlt hw';
  · exact h' w hge hw;

lemma exists_witnessFirst [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {ι : Type*} [Finite ι] (P : ι → V → Prop)
    (hP : ∀ i, 𝚺₁-Predicate (P i)) (o : ι → ℕ) (h : ∃ i w, P i w) :
    ∃ j, (∀ i, o i < o j → WitnessLT (P j) (P i)) ∧ ∀ i, o j ≤ o i → WitnessLE (P j) (P i) := by
  obtain ⟨i₀, w₀, h₀⟩ := h;
  obtain ⟨w, ⟨i₁, h₁⟩, hw⟩ : ∃ w, (∃ i, P i w) ∧ ∀ v < w, ¬∃ i, P i v :=
    InductionOnBroadHierarchy.least_number_sigma 𝚺 1 (P := fun w ↦ ∃ i, P i w)
      (HierarchySymbol.Definable.fintype_exs fun i ↦ hP i) (x := w₀) ⟨i₀, h₀⟩;
  obtain ⟨j, hj, hmin⟩ := (InvImage.wf o wellFounded_lt).has_min {i | P i w} ⟨i₁, h₁⟩;
  use j;
  and_intros;
  · intro i hi;
    use w, hj;
    intro v hv hv';
    rcases hv.lt_or_eq with hlt | rfl;
    · exact hw v hlt ⟨i, hv'⟩;
    · exact hmin i hv' hi;
  · exact fun i _ ↦ ⟨w, hj, fun v hv hv' ↦ hw v hv ⟨i, hv'⟩⟩;

end comparison

variable {κ α : Type*} [Nonempty κ] [DecidableEq α] {A : ProvabilityLogic.Formula α}

section stx

variable (T : ArithmeticTheory) [T.Δ₁] (X : StrongReflexiveCountermodel κ A) [Fintype X.World]
  [X.IsGL] (σ : ArithmeticSentence) (θ : 𝚺₀.Semisentence 1)

open Classical in
/-- The targets of the edges from `x`. -/
def Next (x : X.extendRoot.World) : Finset X.extendRoot.World :=
  {z | (x ≺ z ∧ z ≠ some X.u) ∨ (x = some X.root ∧ z = some X.u)}

omit [X.IsGL] in
variable {X} in
@[simp] lemma mem_next {x z : X.extendRoot.World} :
    z ∈ Next X x ↔ (x ≺ z ∧ z ≠ some X.u) ∨ (x = some X.root ∧ z = some X.u) := by
  simp [Next]

omit [X.IsGL] in
variable {X} in
lemma rel_of_mem_next {x z : X.extendRoot.World} (h : z ∈ Next X x) : x ≺ z := by
  rcases mem_next.mp h with h | ⟨rfl, rfl⟩;
  · exact h.1;
  · exact X.root_rel_u;

open Classical in
/-- A total order on the worlds of `X.extendRoot` in which `u` is the largest. -/
def ord (z : X.extendRoot.World) : ℕ :=
  if z = some X.u then Fintype.card X.extendRoot.World else Fintype.equivFin _ z

def prfNegSigma : 𝚺₁.Semisentence 2 := .mkSigma
  “w e. ∃ n, !(negGraph ℒₒᵣ) n e ∧ !(proof T).sigma w n”

def prfNegPi : 𝚷₁.Semisentence 2 := .mkPi
  “w e. ∀ n, !(negGraph ℒₒᵣ) n e → !(proof T).pi w n”

open Classical in
/-- The witnesses of the trigger of an edge into `z`. -/
def trigSigma (z : X.extendRoot.World) : 𝚺₁.Semisentence 2 :=
  if z = some X.u then .mkSigma “w e. !θ.val w” else prfNegSigma T

open Classical in
def trigPi (z : X.extendRoot.World) : 𝚷₁.Semisentence 2 :=
  if z = some X.u then .mkPi “w e. !θ.val w” else prfNegPi T

variable {n : ℕ} (t : X.extendRoot.World → ArithmeticSemiterm Empty n)

def stpAux (x y : X.extendRoot.World) : ArithmeticSemisentence n :=
  (⩕ z ∈ {z ∈ Next X x | ord X z < ord X y},
    (cmpLT (trigSigma T X θ y) (trigPi T X θ z)).val/[t y, t z]) ⋏
  (⩕ z ∈ {z ∈ Next X x | ord X y ≤ ord X z},
    (cmpLE (trigSigma T X θ y) (trigPi T X θ z)).val/[t y, t z])

def chainAux : List X.extendRoot.World → ArithmeticSemisentence n
  |          [] => ⊥
  |         [_] => ⊤
  | y :: x :: ε => chainAux (x :: ε) ⋏ stpAux T X θ t x y

/-- The sequences from the root `none` to `x` along the edges, listed from `x`. -/
abbrev EChain (x : X.extendRoot.World) :=
  {ε : List X.extendRoot.World // ε.ChainI (fun a b ↦ a ∈ Next X b) x none}

instance (x : X.extendRoot.World) : Finite (EChain X x) := by
  have : Finite {ε : List X.extendRoot.World // ε.ChainI (fun a b ↦ b ≺ a) x none} :=
    List.ChainI.finite_of_irreflexive_of_transitive
      (show Std.Irrefl (fun a b : X.extendRoot.World ↦ b ≺ a) from
        ⟨fun a ↦ Std.Irrefl.irrefl (r := X.extendRoot.Rel) a⟩)
      (show IsTrans _ (fun a b : X.extendRoot.World ↦ b ≺ a) from
        ⟨fun a b c hab hbc ↦ IsTrans.trans (r := X.extendRoot.Rel) c b a hbc hab⟩) x none;
  have mono {a b : X.extendRoot.World} {l : List X.extendRoot.World}
      (h : l.ChainI (fun a b ↦ a ∈ Next X b) a b) :
      l.ChainI (fun a b ↦ b ≺ a) a b := by
    induction h with
    | singleton => exact .singleton _
    | cons hR _ ih => exact .cons (rel_of_mem_next hR) ih;
  exact Finite.of_injective (fun ε : EChain X x ↦
    (⟨ε.1, mono ε.2⟩ : {ε : List X.extendRoot.World // ε.ChainI (fun a b ↦ b ≺ a) x none}))
    fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)

def hAux (x : X.extendRoot.World) : ArithmeticSemisentence n :=
  haveI := Fintype.ofFinite (EChain X x);
  ⩖ ε : EChain X x, chainAux T X θ t ε

open Classical in
def notTrigAux (z : X.extendRoot.World) : ArithmeticSemisentence n :=
  if z = some X.u then Rew.embSubsts ![] ▹ ∼σ else T.consistentWith.val/[t z]

def deltaAux (x : X.extendRoot.World) : ArithmeticSemisentence n :=
  hAux T X θ t x ⋏ ⩕ z ∈ Next X x, notTrigAux T X σ t z

/-- The modified Solovay sentences.

- [Bek90, §6 Theorem 2]
-/
def _root_.FFL.FirstOrder.Theory.modifiedSolovay (x : X.extendRoot.World) : ArithmeticSentence :=
  exclusiveMultifixedpoint
    (fun j ↦ deltaAux T X σ θ (fun z ↦ #(Fintype.equivFin _ z)) ((Fintype.equivFin _).symm j))
    (Fintype.equivFin _ x)

abbrev stp (x y : X.extendRoot.World) : ArithmeticSentence :=
  stpAux T X θ (fun z ↦ ⌜T.modifiedSolovay X σ θ z⌝) x y

abbrev chain (ε : List X.extendRoot.World) : ArithmeticSentence :=
  chainAux T X θ (fun z ↦ ⌜T.modifiedSolovay X σ θ z⌝) ε

abbrev h (x : X.extendRoot.World) : ArithmeticSentence :=
  hAux T X θ (fun z ↦ ⌜T.modifiedSolovay X σ θ z⌝) x

abbrev notTrig (z : X.extendRoot.World) : ArithmeticSentence :=
  notTrigAux T X σ (fun z ↦ ⌜T.modifiedSolovay X σ θ z⌝) z

lemma h_sigma_one (x : X.extendRoot.World) : Hierarchy 𝚺 1 (h T X σ θ x) := by
  sorry

lemma modifiedSolovay_diag (x : X.extendRoot.World) :
    𝗜𝚺₁ ⊢ T.modifiedSolovay X σ θ x 🡘 h T X σ θ x ⋏ ⩕ z ∈ Next X x, notTrig T X σ θ z := by
  sorry

end stx

section model

variable (T : ArithmeticTheory) [T.Δ₁] (X : StrongReflexiveCountermodel κ A) [Fintype X.World]
  [X.IsGL] (σ : ArithmeticSentence) (θ : 𝚺₀.Semisentence 1)
  (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Classical in
/-- `w` witnesses the trigger of an edge into `z`. -/
def Wit (z : X.extendRoot.World) (w : V) : Prop :=
  if z = some X.u then V ⊧/![w] θ.val else Proof T w (⌜∼T.modifiedSolovay X σ θ z⌝ : V)

open Classical in
/-- The trigger of an edge into `z` is pulled. -/
def Trig (z : X.extendRoot.World) : Prop :=
  if z = some X.u then V ⊧/![] σ else Provable T (⌜∼T.modifiedSolovay X σ θ z⌝ : V)

/-- The edge `x → y` is the one taken from `x`. -/
def Step (x y : X.extendRoot.World) : Prop :=
  y ∈ Next X x ∧
    (∀ z ∈ Next X x, ord X z < ord X y → WitnessLT (Wit T X σ θ V y) (Wit T X σ θ V z)) ∧
    (∀ z ∈ Next X x, ord X y ≤ ord X z → WitnessLE (Wit T X σ θ V y) (Wit T X σ θ V z))

abbrev Reach (x : X.extendRoot.World) : Prop := Relation.ReflTransGen (Step T X σ θ V) none x

def _root_.FFL.FirstOrder.Theory.ModifiedSolovay (x : X.extendRoot.World) : Prop :=
  Reach T X σ θ V x ∧ ∀ z ∈ Next X x, ¬Trig T X σ θ V z

variable {T X σ θ V}

@[simp] lemma val_h {x : X.extendRoot.World} : V ⊧/![] (h T X σ θ x) ↔ Reach T X σ θ V x := by
  sorry

@[simp] lemma val_modifiedSolovay {x : X.extendRoot.World} :
    V ⊧/![] (T.modifiedSolovay X σ θ x) ↔ T.ModifiedSolovay X σ θ V x := by
  sorry

lemma trig_iff_exists_wit (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) {z : X.extendRoot.World} :
    Trig T X σ θ V z ↔ ∃ w, Wit T X σ θ V z w := by
  sorry

lemma Step.exists_wit {x y : X.extendRoot.World} (h : Step T X σ θ V x y) :
    ∃ w, Wit T X σ θ V y w := by
  sorry

lemma Step.unique {x y₁ y₂ : X.extendRoot.World} (h₁ : Step T X σ θ V x y₁)
    (h₂ : Step T X σ θ V x y₂) : y₁ = y₂ := by
  sorry

lemma Reach.provable {x : X.extendRoot.World} (hx : x ≠ none) (hu : x ≠ some X.u)
    (h : Reach T X σ θ V x) : Provable T (⌜∼T.modifiedSolovay X σ θ x⌝ : V) := by
  sorry

lemma Reach.models_sigma (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val)
    (h : Reach T X σ θ V (some X.u)) : V ⊧/![] σ := by
  sorry

lemma Reach.disjunction (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) {x : X.extendRoot.World}
    (h : Reach T X σ θ V x) :
    T.ModifiedSolovay X σ θ V x ∨ ∃ y, x ≺ y ∧ T.ModifiedSolovay X σ θ V y := by
  sorry

lemma ModifiedSolovay.exclusive (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val)
    {x y : X.extendRoot.World} (ne : x ≠ y) :
    T.ModifiedSolovay X σ θ V x → ¬T.ModifiedSolovay X σ θ V y := by
  sorry

lemma ModifiedSolovay.consistent {x y : X.extendRoot.World} (hxy : x ≺ y) (hy : y ≠ some X.u)
    (h : T.ModifiedSolovay X σ θ V x) : ¬Provable T (⌜∼T.modifiedSolovay X σ θ y⌝ : V) := by
  sorry

lemma disjunctive (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) :
    ∃ x, T.ModifiedSolovay X σ θ V x := by
  sorry

end model

section

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {X : StrongReflexiveCountermodel κ A}
  [Fintype X.World] [X.IsGL] {σ : ArithmeticSentence} {θ : 𝚺₀.Semisentence 1}
  (hθσ : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val)
include hθσ

open Classical in
lemma provable_h_imp (x : X.extendRoot.World) :
    𝗜𝚺₁ ⊢ h T X σ θ x 🡒 T.modifiedSolovay X σ θ x ⋎
      ⩖ y ∈ {y : X.extendRoot.World | x ≺ y}, T.modifiedSolovay X σ θ y := by
  sorry

open Classical in
lemma ModifiedSolovay.provable_disjunction {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {x : X.extendRoot.World} (h : T.ModifiedSolovay X σ θ V x) :
    Provable T (⌜T.modifiedSolovay X σ θ x ⋎
      ⩖ y ∈ {y : X.extendRoot.World | x ≺ y}, T.modifiedSolovay X σ θ y⌝ : V) := by
  sorry

open Classical in
lemma ModifiedSolovay.box_disjunction {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {x : X.extendRoot.World} (hx : x ≠ none) (hu : x ≠ some X.u)
    (h : T.ModifiedSolovay X σ θ V x) :
    Provable T (⌜⩖ y ∈ {y : X.extendRoot.World | x ≺ y}, T.modifiedSolovay X σ θ y⌝ : V) := by
  sorry

lemma provable_not_sigma_imp : 𝗜𝚺₁ ⊢ ∼σ 🡒 ∼T.modifiedSolovay X σ θ (some X.u) := by
  sorry

omit hθσ in
lemma provable_provable_sigma_imp :
    𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 ∼T.modifiedSolovay X σ θ none := by
  sorry

end

end FFL.FirstOrder.Arithmetic.Bootstrapping.ModifiedSolovaySentences

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping ModifiedSolovaySentences ProvabilityLogic Kripke ProvabilityAbstraction

variable {κ α : Type*} [Nonempty κ] [DecidableEq α] {A : ProvabilityLogic.Formula α}

/-- Modified Solovay sentences for the standard provability predicate of `T` and a `𝚺₁`
sentence `σ`.

- [Bek90, §6 Theorem 2]
- [AB05, Lemma 51]
-/
def _root_.FFL.FirstOrder.Theory.standardProvability.modifiedSolovaySentences
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (X : StrongReflexiveCountermodel κ A)
    [Fintype X.World] [X.IsGL] {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    T.standardProvability.ModifiedSolovaySentences X σ :=
  have hex := ISigma1.exists_matrix_provable_of_sentence hσ;
  have hθσ : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      V ⊧/![] σ ↔ ∃ w, V ⊧/![w] hex.choose.val := fun V _ _ ↦ by
    simpa [models_iff] using
      consequence_iff.mp (Theory.Proof.sound hex.choose_spec) V inferInstance;
  { Λ := T.modifiedSolovay X σ hex.choose
    SC1 _ _ ne := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using! ModifiedSolovay.exclusive (hθσ V) ne
    SC2 _ _ hxy hy := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using! ModifiedSolovay.consistent hxy hy
    SC3 _ hx hu := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using! ModifiedSolovay.box_disjunction hθσ hx hu
    SC3r := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using!
        ModifiedSolovay.provable_disjunction hθσ (x := some X.u)
    SC4 := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using! disjunctive (hθσ V)
    SC5 := provable_provable_sigma_imp
    SC6 := provable_not_sigma_imp hθσ }

end FFL.FirstOrder.Arithmetic

end

end
