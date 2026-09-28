module

public import Foundation.FirstOrder.Syntax.Classical.Bounding
public import Foundation.FirstOrder.Syntax.Classical.Padding

/-!
# Bounded hierarchy over an initial class

`ℬ.HierarchyOn C Γ s φ` is the class `Γ_s(C)` generated from an initial class `C` by `⋏`, `⋎`,
`ℬ`-bounded quantifiers and alternating unbounded quantifiers. `ℬ.Hierarchy` takes
`C = ℬ.Closure`; `ℬ.StrictHierarchy` admits `ℬ`-bounded quantifiers only in the initial class.

## References

- [HP98]
-/

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language}
variable {ξ : Type*} {n m s : ℕ} {Γ Γ' : Polarity}

namespace Bounding

/-- The hierarchy `Γ_s(C)` over the initial class `C`, with bounded quantifiers from `ℬ`. -/
inductive HierarchyOn (ℬ : Bounding L) (C : {n : ℕ} → Semiformula L ξ n → Prop) :
    Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | initial (Γ : Polarity) (s n : ℕ) {φ : Semiformula L ξ n} : C φ → ℬ.HierarchyOn C Γ s φ
  | and {Γ : Polarity} {s n : ℕ} {φ ψ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s φ → ℬ.HierarchyOn C Γ s ψ → ℬ.HierarchyOn C Γ s (φ ⋏ ψ)
  | or {Γ : Polarity} {s n : ℕ} {φ ψ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s φ → ℬ.HierarchyOn C Γ s ψ → ℬ.HierarchyOn C Γ s (φ ⋎ ψ)
  | ball {Γ : Polarity} {s n : ℕ} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    R ∈ ℬ → t.Positive → ℬ.HierarchyOn C Γ s φ →
      ℬ.HierarchyOn C Γ s (∀¹[R.operator ![#0, t]] φ)
  | bexs {Γ : Polarity} {s n : ℕ} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    R ∈ ℬ → t.Positive → ℬ.HierarchyOn C Γ s φ →
      ℬ.HierarchyOn C Γ s (∃¹[R.operator ![#0, t]] φ)
  | exs {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.HierarchyOn C 𝚺 (s + 1) φ → ℬ.HierarchyOn C 𝚺 (s + 1) (∃¹ φ)
  | all {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.HierarchyOn C 𝚷 (s + 1) φ → ℬ.HierarchyOn C 𝚷 (s + 1) (∀¹ φ)
  | sigma {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.HierarchyOn C 𝚷 s φ → ℬ.HierarchyOn C 𝚺 (s + 1) (∃¹ φ)
  | pi {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.HierarchyOn C 𝚺 s φ → ℬ.HierarchyOn C 𝚷 (s + 1) (∀¹ φ)
  | dummy_sigma {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.HierarchyOn C 𝚷 (s + 1) φ → ℬ.HierarchyOn C 𝚺 (s + 1 + 1) (∀¹ φ)
  | dummy_pi {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.HierarchyOn C 𝚺 (s + 1) φ → ℬ.HierarchyOn C 𝚷 (s + 1 + 1) (∃¹ φ)

/-- The bounded hierarchy over the `ℬ`-bounded formulas. -/
abbrev Hierarchy (ℬ : Bounding L) : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop :=
  ℬ.HierarchyOn ℬ.Closure

/-- The strict hierarchy: `ℬ`-bounded formulas beneath unbounded quantifiers, `⋏` and `⋎`. -/
abbrev StrictHierarchy (ℬ : Bounding L) : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop :=
  HierarchyOn ℬ[L] ℬ.Closure

namespace InitialClass

variable (ℬ : Bounding L) (C : {n : ℕ} → Semiformula L ξ n → Prop)

/-- `C` contains `⊤`, `⊥` and the (negated) atomic formulas. -/
class HasAtoms : Prop where
  verum (n : ℕ) : C (⊤ : Semiformula L ξ n)
  falsum (n : ℕ) : C (⊥ : Semiformula L ξ n)
  rel {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : C (.rel r v)
  nrel {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : C (.nrel r v)

/-- `C` is closed under `⋏` and `⋎`, and under their components. -/
class AndOrIff : Prop where
  and_iff {n : ℕ} {φ ψ : Semiformula L ξ n} : C (φ ⋏ ψ) ↔ C φ ∧ C ψ
  or_iff {n : ℕ} {φ ψ : Semiformula L ξ n} : C (φ ⋎ ψ) ↔ C φ ∧ C ψ

/-- `C` is closed under negation. -/
class NegClosed : Prop where
  neg {n : ℕ} {φ : Semiformula L ξ n} : C φ → C (∼φ)

/-- `C` is closed under `ℬ`-bounded quantifiers, and under their matrices. -/
class BoundedIff : Prop where
  ball_iff {n : ℕ} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    R ∈ ℬ → t.Positive → (C (∀¹[R.operator ![#0, t]] φ) ↔ C φ)
  bexs_iff {n : ℕ} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    R ∈ ℬ → t.Positive → (C (∃¹[R.operator ![#0, t]] φ) ↔ C φ)

/-- The matrix of a quantified formula of `C` lies in `C`. -/
class RemoveQuantifier : Prop where
  of_all {n : ℕ} {φ : Semiformula L ξ (n + 1)} : C (∀¹ φ) → C φ
  of_exs {n : ℕ} {φ : Semiformula L ξ (n + 1)} : C (∃¹ φ) → C φ

/-- Every bounding operator of `ℬ` lies in `C`. -/
class Small : Prop where
  operator {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {n : ℕ}
    (v : Fin 2 → Semiterm L ξ n) : C (R.operator v)

variable {ℬ C}

instance : HasAtoms (ℬ.Closure : {n : ℕ} → Semiformula L ξ n → Prop) where
  verum := .verum
  falsum := .falsum
  rel := .rel
  nrel := .nrel

instance : AndOrIff (ℬ.Closure : {n : ℕ} → Semiformula L ξ n → Prop) where
  and_iff := Closure.and_iff
  or_iff := Closure.or_iff

instance : NegClosed (ℬ.Closure : {n : ℕ} → Semiformula L ξ n → Prop) where
  neg := Closure.neg

instance : BoundedIff ℬ (ℬ.Closure : {n : ℕ} → Semiformula L ξ n → Prop) where
  ball_iff := Closure.ball_iff
  bexs_iff := Closure.bexs_iff

instance [Small ℬ (ℬ.Closure : {n : ℕ} → Semiformula L ξ n → Prop)] :
    RemoveQuantifier (ℬ.Closure : {n : ℕ} → Semiformula L ξ n → Prop) where
  of_all h := by
    cases h;
    case ball _ hR _ _ _ hp => exact .or (Closure.neg (Small.operator hR _)) hp;
  of_exs h := by
    cases h;
    case bexs _ hR _ _ _ hp => exact .and (Small.operator hR _) hp;

instance : BoundedIff ℬ[L] C where
  ball_iff hR := absurd hR not_mem_strict
  bexs_iff hR := absurd hR not_mem_strict

instance : Small ℬ[L] C where
  operator hR := absurd hR not_mem_strict

instance [L.LT] [HasAtoms C] : Small ℬ[<, L] C where
  operator {R} hR {_} v := by
    rcases Set.mem_singleton_iff.mp hR with rfl;
    simpa [Semiformula.Operator.operator, Semiformula.Operator.LT.sentence_eq]
      using HasAtoms.rel (C := C) _ _;

instance [L.Mem] [HasAtoms C] : Small ℬ[∈, L] C where
  operator {R} hR {_} v := by
    rcases Set.mem_singleton_iff.mp hR with rfl;
    simpa [Semiformula.Operator.operator, Semiformula.Operator.Mem.sentence_eq]
      using HasAtoms.rel (C := C) _ _;

end InitialClass

namespace HierarchyOn

open InitialClass

variable {ℬ : Bounding L} {C : {n : ℕ} → Semiformula L ξ n → Prop}

section HasAtoms

variable [HasAtoms C]

@[simp] lemma verum (Γ s n) : ℬ.HierarchyOn C Γ s (⊤ : Semiformula L ξ n) :=
  initial Γ s n (HasAtoms.verum n)

@[simp] lemma falsum (Γ s n) : ℬ.HierarchyOn C Γ s (⊥ : Semiformula L ξ n) :=
  initial Γ s n (HasAtoms.falsum n)

@[simp] lemma rel (Γ s) {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    ℬ.HierarchyOn C Γ s (Semiformula.rel r v) :=
  initial Γ s n (HasAtoms.rel r v)

@[simp] lemma nrel (Γ s) {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    ℬ.HierarchyOn C Γ s (Semiformula.nrel r v) :=
  initial Γ s n (HasAtoms.nrel r v)

lemma of_open {φ : Semiformula L ξ n} : φ.Open → ℬ.HierarchyOn C Γ s φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp;
  | hfalsum => simp;
  | hrel => simp;
  | hnrel => simp;
  | hand _ _ ihφ ihψ => simpa using fun h₁ h₂ ↦ and (ihφ h₁) (ihψ h₂);
  | hor _ _ ihφ ihψ => simpa using fun h₁ h₂ ↦ or (ihφ h₁) (ihψ h₂);
  | hall => simp;
  | hexs => simp;

@[simp] lemma equal [L.Eq] {t u : Semiterm L ξ n} :
    ℬ.HierarchyOn C Γ s “!!t = !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Eq.sentence_eq];

@[simp] lemma lt [L.LT] {t u : Semiterm L ξ n} :
    ℬ.HierarchyOn C Γ s “!!t < !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.LT.sentence_eq];

@[simp] lemma le [L.Eq] [L.LT] {t u : Semiterm L ξ n} :
    ℬ.HierarchyOn C Γ s “!!t ≤ !!u” := by
  simpa [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.LE.sentence_eq] using or (equal (t := t) (u := u)) lt;

instance {k : ℕ} :
    LogicalConnective.AndOrClosed (ℬ.HierarchyOn C Γ s : Semiformula L ξ k → Prop) where
  verum := verum _ _ _
  falsum := falsum _ _ _
  and := and
  or := or

end HasAtoms

section monotone

variable {ℬ₁ ℬ₂ : Bounding L} {C₁ C₂ : {n : ℕ} → Semiformula L ξ n → Prop}

lemma monotone (hℬ : ℬ₁ ≤ ℬ₂) (hC : ∀ {n} {φ : Semiformula L ξ n}, C₁ φ → C₂ φ)
    {Γ s n} {φ : Semiformula L ξ n} : ℬ₁.HierarchyOn C₁ Γ s φ → ℬ₂.HierarchyOn C₂ Γ s φ
  | initial _ _ _ h => initial _ _ _ (hC h)
  | and hp hq => and (monotone hℬ hC hp) (monotone hℬ hC hq)
  | or hp hq => or (monotone hℬ hC hp) (monotone hℬ hC hq)
  | ball hR ht hp => ball (hℬ hR) ht (monotone hℬ hC hp)
  | bexs hR ht hp => bexs (hℬ hR) ht (monotone hℬ hC hp)
  | exs hp => exs (monotone hℬ hC hp)
  | all hp => all (monotone hℬ hC hp)
  | sigma hp => sigma (monotone hℬ hC hp)
  | pi hp => pi (monotone hℬ hC hp)
  | dummy_sigma hp => dummy_sigma (monotone hℬ hC hp)
  | dummy_pi hp => dummy_pi (monotone hℬ hC hp)

lemma mono_bounding (hℬ : ℬ₁ ≤ ℬ₂) {φ : Semiformula L ξ n} :
    ℬ₁.HierarchyOn C Γ s φ → ℬ₂.HierarchyOn C Γ s φ :=
  monotone hℬ id

lemma mono_initial (hC : ∀ {n} {φ : Semiformula L ξ n}, C₁ φ → C₂ φ) {φ : Semiformula L ξ n} :
    ℬ.HierarchyOn C₁ Γ s φ → ℬ.HierarchyOn C₂ Γ s φ :=
  monotone le_rfl hC

end monotone

lemma zero_eq_alt {φ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ 0 φ → ℬ.HierarchyOn C Γ.alt 0 φ := by
  generalize hz : 0 = z;
  rw [eq_comm] at hz;
  intro h;
  induction h <;> try (solve | simp at hz ⊢);
  case initial h => exact initial _ _ _ h;
  case and _ _ ihp ihq => exact and (ihp hz) (ihq hz);
  case or _ _ ihp ihq => exact or (ihp hz) (ihq hz);
  case ball hR pos _ ih => exact ball hR pos (ih hz);
  case bexs hR pos _ ih => exact bexs hR pos (ih hz);

lemma pi_zero_iff_sigma_zero {φ : Semiformula L ξ n} :
    ℬ.HierarchyOn C 𝚷 0 φ ↔ ℬ.HierarchyOn C 𝚺 0 φ :=
  ⟨zero_eq_alt, zero_eq_alt⟩

lemma zero_iff {Γ Γ'} {φ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ 0 φ ↔ ℬ.HierarchyOn C Γ' 0 φ := by
  rcases Γ <;> rcases Γ' <;> simp [pi_zero_iff_sigma_zero];

@[simp] lemma alt_zero_iff_zero {φ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ.alt 0 φ ↔ ℬ.HierarchyOn C Γ 0 φ := by
  rcases Γ <;> simp [pi_zero_iff_sigma_zero];

lemma zero_iff_initial [AndOrIff C] [BoundedIff ℬ C] {Γ} {φ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ 0 φ ↔ C φ :=
  ⟨go, initial Γ 0 n⟩
where
  go {Γ n} {φ : Semiformula L ξ n} : ℬ.HierarchyOn C Γ 0 φ → C φ
    | initial _ _ _ h => h
    | and hp hq => AndOrIff.and_iff.mpr ⟨go hp, go hq⟩
    | or hp hq => AndOrIff.or_iff.mpr ⟨go hp, go hq⟩
    | ball hR ht hp => (BoundedIff.ball_iff hR ht).mpr (go hp)
    | bexs hR ht hp => (BoundedIff.bexs_iff hR ht).mpr (go hp)

lemma accum {Γ} {s : ℕ} :
    ∀ {n : ℕ} {φ : Semiformula L ξ n},
      ℬ.HierarchyOn C Γ s φ → ∀ Γ', ℬ.HierarchyOn C Γ' (s + 1) φ
  | _, _, initial _ _ _ h, Γ => initial Γ _ _ h
  | _, _,      and hp hq, _ => and (hp.accum _) (hq.accum _)
  | _, _,       or hp hq, _ => or (hp.accum _) (hq.accum _)
  | _, _, ball hR pos hp, _ => ball hR pos (hp.accum _)
  | _, _, bexs hR pos hp, _ => bexs hR pos (hp.accum _)
  | _, _,         all hp, Γ => by
    cases Γ;
    · exact hp.dummy_sigma;
    · exact (hp.accum 𝚷).all;
  | _, _,          exs hp, Γ => by
    cases Γ;
    · exact (hp.accum 𝚺).exs;
    · exact hp.dummy_pi;
  | _, _,       sigma hp, Γ => by
    cases Γ;
    · exact ((hp.accum 𝚺).accum 𝚺).exs;
    · exact (hp.accum 𝚺).dummy_pi;
  | _, _,          pi hp, Γ => by
    cases Γ;
    · exact (hp.accum 𝚷).dummy_sigma;
    · exact ((hp.accum 𝚷).accum 𝚷).all;
  | _, _, dummy_sigma hp, Γ => by
    cases Γ;
    · exact (hp.accum 𝚷).dummy_sigma;
    · exact ((hp.accum 𝚷).accum 𝚷).all;
  | _, _,    dummy_pi hp, Γ => by
    cases Γ;
    · exact ((hp.accum 𝚺).accum 𝚺).exs;
    · exact (hp.accum 𝚺).dummy_pi;

lemma strict_mono {Γ s} {φ : Semiformula L ξ n}
    (hp : ℬ.HierarchyOn C Γ s φ) (Γ') {s'} (h : s < s') : ℬ.HierarchyOn C Γ' s' φ := by
  have : ∀ d, ℬ.HierarchyOn C Γ' (s + d + 1) φ := by
    intro d;
    induction d with
    | zero => simpa using hp.accum Γ';
    | succ d ih => simpa only [Nat.add_succ, add_zero] using ih.accum _;
  simpa [show s + (s' - s.succ) + 1 = s' from by
    simpa [Nat.succ_add] using Nat.add_sub_of_le h] using this (s' - s.succ);

lemma mono {Γ} {s s' : ℕ} {φ : Semiformula L ξ n}
    (hp : ℬ.HierarchyOn C Γ s φ) (h : s ≤ s') : ℬ.HierarchyOn C Γ s' φ := by
  rcases Nat.lt_or_eq_of_le h with (lt | rfl);
  · exact hp.strict_mono Γ lt;
  · assumption;

lemma of_zero {Γ Γ'} {s : ℕ} {φ : Semiformula L ξ n}
    (hp : ℬ.HierarchyOn C Γ 0 φ) : ℬ.HierarchyOn C Γ' s φ := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le s) with (rfl | pos);
  · exact zero_iff.mp hp;
  · exact strict_mono hp Γ' pos;

section AndOrIff

variable [AndOrIff C]

@[simp] lemma and_iff {φ ψ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (φ ⋏ ψ) ↔ ℬ.HierarchyOn C Γ s φ ∧ ℬ.HierarchyOn C Γ s ψ :=
  ⟨fun
    | initial _ _ _ h =>
      ⟨initial _ _ _ (AndOrIff.and_iff.mp h).1, initial _ _ _ (AndOrIff.and_iff.mp h).2⟩
    | and hp hq => ⟨hp, hq⟩,
    fun ⟨hp, hq⟩ => and hp hq⟩

@[simp] lemma or_iff {φ ψ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (φ ⋎ ψ) ↔ ℬ.HierarchyOn C Γ s φ ∧ ℬ.HierarchyOn C Γ s ψ :=
  ⟨fun
    | initial _ _ _ h =>
      ⟨initial _ _ _ (AndOrIff.or_iff.mp h).1, initial _ _ _ (AndOrIff.or_iff.mp h).2⟩
    | or hp hq => ⟨hp, hq⟩,
    fun ⟨hp, hq⟩ => or hp hq⟩

variable [HasAtoms C]

@[simp] lemma conj_iff {φ : Fin m → Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (Matrix.conj φ) ↔ ∀ i, ℬ.HierarchyOn C Γ s (φ i) := by
  induction m <;> simp [Matrix.conj, Matrix.vecTail, Fin.forall_fin_succ, *];

@[simp] lemma padding_iff {Γ s n k} {φ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (φ.padding k) ↔ ℬ.HierarchyOn C Γ s φ := by
  simp only [Semiformula.padding, and_iff, and_iff_left_iff_imp];
  intro h;
  induction k <;> simp [List.replicate_succ, *];

@[simp] lemma list_conj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    ℬ.HierarchyOn C Γ s (⋀l) ↔ ∀ φ ∈ l, ℬ.HierarchyOn C Γ s φ := by
  match l with
  |          [] => simp;
  |         [_] => simp;
  | ψ :: χ :: l => simp [list_conj₂_iff (l := χ :: l)];

@[simp] lemma list_disj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    ℬ.HierarchyOn C Γ s (⋁l) ↔ ∀ φ ∈ l, ℬ.HierarchyOn C Γ s φ := by
  match l with
  |          [] => simp;
  |         [_] => simp;
  | ψ :: χ :: l => simp [list_disj₂_iff (l := χ :: l)];

@[simp] lemma list_conj'_iff {Γ s n} {ι : Type*} {l : List ι}
    {φ : ι → Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (l.conj' φ) ↔ ∀ i ∈ l, ℬ.HierarchyOn C Γ s (φ i) := by
  simp [List.conj'];

@[simp] lemma list_disj'_iff {Γ s n} {ι : Type*} {l : List ι}
    {φ : ι → Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (l.disj' φ) ↔ ∀ i ∈ l, ℬ.HierarchyOn C Γ s (φ i) := by
  simp [List.disj'];

@[simp] lemma finset_conj'_iff {Γ s n} {ι : Type*} {t : Finset ι}
    {φ : ι → Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (t.conj' φ) ↔ ∀ i ∈ t, ℬ.HierarchyOn C Γ s (φ i) := by
  simp [Finset.conj'];

@[simp] lemma finset_disj'_iff {Γ s n} {ι : Type*} {t : Finset ι}
    {φ : ι → Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (t.disj' φ) ↔ ∀ i ∈ t, ℬ.HierarchyOn C Γ s (φ i) := by
  simp [Finset.disj'];

@[simp] lemma finset_uconj_iff {Γ s n} {ι : Type*} [Fintype ι]
    {φ : ι → Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (Finset.uconj φ) ↔ ∀ i, ℬ.HierarchyOn C Γ s (φ i) := by
  simp [Finset.uconj];

@[simp] lemma finset_udisj_iff {Γ s n} {ι : Type*} [Fintype ι]
    {φ : ι → Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (Finset.udisj φ) ↔ ∀ i, ℬ.HierarchyOn C Γ s (φ i) := by
  simp [Finset.udisj];

end AndOrIff

section NegClosed

variable [NegClosed C]

lemma neg {φ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s φ → ℬ.HierarchyOn C Γ.alt s (∼φ) := by
  intro h;
  induction h;
  case initial h => exact initial _ _ _ (NegClosed.neg h);
  case and ihp ihq => simpa using or ihp ihq;
  case or ihp ihq => simpa using and ihp ihq;
  case bexs hR pos _ ih => simpa only [Semiformula.neg_bexs] using ball hR pos ih;
  case ball hR pos _ ih => simpa only [Semiformula.neg_ball] using bexs hR pos ih;
  case exs ih => simpa using all ih;
  case all ih => simpa using exs ih;
  case sigma ih => simpa using pi ih;
  case pi ih => simpa using sigma ih;
  case dummy_pi ih => simpa using dummy_sigma ih;
  case dummy_sigma ih => simpa using dummy_pi ih;

@[simp] lemma neg_iff {φ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (∼φ) ↔ ℬ.HierarchyOn C Γ.alt s φ :=
  ⟨fun h ↦ by simpa using neg h, fun h ↦ by simpa using neg h⟩

variable [AndOrIff C]

@[simp] lemma imp_iff {φ ψ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (φ 🡒 ψ) ↔ ℬ.HierarchyOn C Γ.alt s φ ∧ ℬ.HierarchyOn C Γ s ψ := by
  simp [Semiformula.imp_eq];

lemma iff_iff {φ ψ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ s (φ 🡘 ψ) ↔
      (ℬ.HierarchyOn C Γ s φ ∧ ℬ.HierarchyOn C Γ.alt s φ ∧
        ℬ.HierarchyOn C Γ s ψ ∧ ℬ.HierarchyOn C Γ.alt s ψ) := by
  simp [Semiformula.iff_eq]; tauto;

@[simp] lemma iff_iff₀ {φ ψ : Semiformula L ξ n} :
    ℬ.HierarchyOn C Γ 0 (φ 🡘 ψ) ↔ ℬ.HierarchyOn C Γ 0 φ ∧ ℬ.HierarchyOn C Γ 0 ψ := by
  simp [Semiformula.iff_eq]; tauto;

instance [HasAtoms C] {k : ℕ} :
    LogicalConnective.Closed (ℬ.HierarchyOn C Γ 0 : Semiformula L ξ k → Prop) where
  not := by simp
  imply := by simp [Semiformula.imp_eq]; tauto

end NegClosed

section BoundedIff

variable [AndOrIff C] [BoundedIff ℬ C]

@[simp] lemma ball_iff {Γ s n} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (hR : R ∈ ℬ) (ht : t.Positive) :
    ℬ.HierarchyOn C Γ s (∀¹[R.operator ![#0, t]] φ) ↔ ℬ.HierarchyOn C Γ s φ := by
  constructor;
  · generalize hq : (∀¹[R.operator ![#0, t]] φ) = ψ;
    intro H;
    induction H <;> simp only [FFL.FirstOrder.ball, FFL.FirstOrder.bexs,
      Semiformula.all_inj, Semiformula.imp_inj, reduceCtorEq] at hq;
    case initial h =>
      rcases hq with rfl;
      exact initial _ _ _ ((BoundedIff.ball_iff hR ht).mp h);
    case ball hR' φ t pt hp ih =>
      rcases hq with ⟨_, rfl⟩;
      assumption;
    case all hp ih =>
      rcases hq with rfl;
      exact (or_iff.mp hp).2;
    case pi s _ _ hp ih =>
      rcases hq with rfl;
      exact (or_iff.mp hp).2.accum _;
    case dummy_sigma hp _ =>
      rcases hq with rfl;
      exact (or_iff.mp hp).2.accum _;
  · intro hp;
    exact hp.ball hR ht;

@[simp] lemma bexs_iff {Γ s n} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (hR : R ∈ ℬ) (ht : t.Positive) :
    ℬ.HierarchyOn C Γ s (∃¹[R.operator ![#0, t]] φ) ↔ ℬ.HierarchyOn C Γ s φ := by
  constructor;
  · generalize hq : (∃¹[R.operator ![#0, t]] φ) = ψ;
    intro H;
    induction H <;> simp only [FFL.FirstOrder.ball, FFL.FirstOrder.bexs,
      Semiformula.exs_inj, Semiformula.and_inj, reduceCtorEq] at hq;
    case initial h =>
      rcases hq with rfl;
      exact initial _ _ _ ((BoundedIff.bexs_iff hR ht).mp h);
    case bexs hR' φ t pt hp ih =>
      rcases hq with ⟨_, rfl⟩;
      assumption;
    case exs hp ih =>
      rcases hq with rfl;
      exact (and_iff.mp hp).2;
    case sigma s _ _ hp ih =>
      rcases hq with rfl;
      exact (and_iff.mp hp).2.accum _;
    case dummy_pi hp _ =>
      rcases hq with rfl;
      exact (and_iff.mp hp).2.accum _;
  · intro hp;
    exact hp.bexs hR ht;

end BoundedIff

section Small

variable [Small ℬ C]

@[simp] lemma operator {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {Γ s n}
    (v : Fin 2 → Semiterm L ξ n) : ℬ.HierarchyOn C Γ s (R.operator v) :=
  initial _ _ _ (Small.operator hR v)

variable [RemoveQuantifier C]

lemma remove_forall [NegClosed C] {φ : Semiformula L ξ (n + 1)} :
    ℬ.HierarchyOn C Γ s (∀¹ φ) → ℬ.HierarchyOn C Γ s φ := by
  intro h;
  rcases h;
  case initial h => exact initial _ _ _ (RemoveQuantifier.of_all h);
  case ball _ hR _ _ _ hp => exact or (initial _ _ _ (NegClosed.neg (Small.operator hR _))) hp;
  case all => assumption;
  case pi h => exact h.accum _;
  case dummy_sigma h => exact h.accum _;

lemma remove_exists {φ : Semiformula L ξ (n + 1)} :
    ℬ.HierarchyOn C Γ s (∃¹ φ) → ℬ.HierarchyOn C Γ s φ := by
  intro h;
  rcases h;
  case initial h => exact initial _ _ _ (RemoveQuantifier.of_exs h);
  case bexs _ hR _ _ _ hp => exact and (operator hR _) hp;
  case exs => assumption;
  case sigma h => exact h.accum _;
  case dummy_pi h => exact h.accum _;

@[simp] lemma all_iff [NegClosed C] {φ : Semiformula L ξ (n + 1)} :
    ℬ.HierarchyOn C 𝚷 (s + 1) (∀¹ φ) ↔ ℬ.HierarchyOn C 𝚷 (s + 1) φ :=
  ⟨remove_forall, all⟩

@[simp] lemma allItr_iff [NegClosed C] {k : ℕ} {φ : Semiformula L ξ (n + k)} :
    ℬ.HierarchyOn C 𝚷 (s + 1) (∀¹^[k] φ) ↔ ℬ.HierarchyOn C 𝚷 (s + 1) φ := by
  induction k <;> simp [allItr_succ, *];

@[simp] lemma sigma_iff {φ : Semiformula L ξ (n + 1)} :
    ℬ.HierarchyOn C 𝚺 (s + 1) (∃¹ φ) ↔ ℬ.HierarchyOn C 𝚺 (s + 1) φ :=
  ⟨remove_exists, exs⟩

@[simp] lemma exsItr_iff {k : ℕ} {φ : Semiformula L ξ (n + k)} :
    ℬ.HierarchyOn C 𝚺 (s + 1) (∃¹^[k] φ) ↔ ℬ.HierarchyOn C 𝚺 (s + 1) φ := by
  induction k <;> simp [exsItr_succ, *];

end Small

/-- A formalization-specific induction principle separating the preceding Π level. -/
lemma sigma_succ_induction {s : ℕ} {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hPi : ∀ n φ, ℬ.HierarchyOn C 𝚷 s φ → P n φ)
    (hAnd : ∀ n φ ψ,
      ℬ.HierarchyOn C 𝚺 (s + 1) φ → ℬ.HierarchyOn C 𝚺 (s + 1) ψ →
      P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ,
      ℬ.HierarchyOn C 𝚺 (s + 1) φ → ℬ.HierarchyOn C 𝚺 (s + 1) ψ →
      P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ R ∈ ℬ, ∀ n t φ,
      ℬ.HierarchyOn C 𝚺 (s + 1) φ → P (n + 1) φ →
      P n (∀¹[R.operator ![#0, Rew.bShift t]] φ))
    (hBexs : ∀ R ∈ ℬ, ∀ n t φ,
      ℬ.HierarchyOn C 𝚺 (s + 1) φ → P (n + 1) φ →
      P n (∃¹[R.operator ![#0, Rew.bShift t]] φ))
    (hExs : ∀ n φ, ℬ.HierarchyOn C 𝚺 (s + 1) φ → P (n + 1) φ → P n (∃¹ φ))
    (n φ) : ℬ.HierarchyOn C 𝚺 (s + 1) φ → P n φ := by
  generalize hΓ : (𝚺 : Polarity) = Γ;
  generalize hs : s + 1 = S;
  intro h;
  induction h with
  | initial _ _ _ h => exact hPi _ _ (initial _ _ _ h);
  | ball hR pos hp ih =>
    rcases hΓ with rfl;
    rcases hs with rfl;
    rcases Rew.positive_iff.mp pos with ⟨t, rfl⟩;
    exact hBall _ hR _ t _ hp (ih rfl rfl);
  | bexs hR pos hp ih =>
    rcases hΓ with rfl;
    rcases hs with rfl;
    rcases Rew.positive_iff.mp pos with ⟨t, rfl⟩;
    exact hBexs _ hR _ t _ hp (ih rfl rfl);
  | sigma hp _ =>
    injection hs with hs;
    subst hs;
    exact hExs _ _ (hp.accum _) (hPi _ _ hp);
  | dummy_sigma hp _ =>
    injection hs with hs;
    subst hs;
    exact hPi _ _ hp.all;
  | and | or | exs => grind;
  | all | pi | dummy_pi => simp at hΓ;

section rew

variable {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}

lemma rew_of {C₁ : {n : ℕ} → Semiformula L ξ₁ n → Prop} {C₂ : {n : ℕ} → Semiformula L ξ₂ n → Prop}
    (hC : ∀ {n₁ n₂} (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ}, C₁ φ → C₂ (ω ▹ φ))
    (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} :
    ℬ.HierarchyOn C₁ Γ s φ → ℬ.HierarchyOn C₂ Γ s (ω ▹ φ) := by
  intro h;
  induction h generalizing n₂;
  case initial h => exact initial _ _ _ (hC ω h);
  case and ihp ihq => simpa using and (ihp ω) (ihq ω);
  case or ihp ihq => simpa using or (ihp ω) (ihq ω);
  case ball hR pos _ ih => simpa using ball hR (by simpa using pos) (ih ω.q);
  case bexs hR pos _ ih => simpa using bexs hR (by simpa using pos) (ih ω.q);
  case exs ih => simpa using (ih ω.q).exs;
  case all ih => simpa using (ih ω.q).all;
  case sigma ih => simpa using (ih ω.q).sigma;
  case pi ih => simpa using (ih ω.q).pi;
  case dummy_pi ih => simpa using (ih ω.q).dummy_pi;
  case dummy_sigma ih => simpa using (ih ω.q).dummy_sigma;

lemma rew_iff_of [SymbolLike ℬ ξ₁ ξ₂]
    {C₁ : {n : ℕ} → Semiformula L ξ₁ n → Prop} {C₂ : {n : ℕ} → Semiformula L ξ₂ n → Prop}
    (hC : ∀ {n₁ n₂} (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ}, C₂ (ω ▹ φ) ↔ C₁ φ)
    {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    ℬ.HierarchyOn C₂ Γ s (ω ▹ φ) ↔ ℬ.HierarchyOn C₁ Γ s φ := by
  constructor;
  · generalize eq : ω ▹ φ = ψ;
    intro hq;
    induction hq generalizing φ n₁
      <;> try simp only [Semiformula.eq_ball_iff,
        Semiformula.eq_bexs_iff, Semiformula.eq_all_iff,
        Semiformula.eq_exs_iff, Semiformula.eq_and_iff, Semiformula.eq_or_iff,
        exists_and_left] at eq;
    case initial h => exact initial _ _ _ ((hC ω).mp (eq.symm ▸ h));
    case and ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩;
      exact and (ihp rfl) (ihq rfl);
    case or ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩;
      exact or (ihp rfl) (ihq rfl);
    case ball t hR pos _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩;
      obtain ⟨u, rfl, hu⟩ := Closure.operator_preimage (ℬ := ℬ) hR hχ pos;
      exact ball hR hu (ih hφ);
    case bexs t hR pos _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩;
      obtain ⟨u, rfl, hu⟩ := Closure.operator_preimage (ℬ := ℬ) hR hχ pos;
      exact bexs hR hu (ih hφ);
    case all ih => rcases eq with ⟨φ, rfl, rfl⟩; exact all (ih rfl);
    case exs ih => rcases eq with ⟨φ, rfl, rfl⟩; exact exs (ih rfl);
    case pi ih => rcases eq with ⟨φ, rfl, rfl⟩; exact pi (ih rfl);
    case sigma ih => rcases eq with ⟨φ, rfl, rfl⟩; exact sigma (ih rfl);
    case dummy_sigma ih => rcases eq with ⟨φ, rfl, rfl⟩; exact dummy_sigma (ih rfl);
    case dummy_pi ih => rcases eq with ⟨φ, rfl, rfl⟩; exact dummy_pi (ih rfl);
  · exact rew_of (fun ω _ h ↦ (hC ω).mpr h) ω;

variable {ℬ' : Bounding L}

lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} :
    ℬ.HierarchyOn ℬ'.Closure Γ s φ → ℬ.HierarchyOn ℬ'.Closure Γ s (ω ▹ φ) :=
  rew_of (fun ω _ h ↦ h.rew ω) ω

@[simp] lemma rew_iff [SymbolLike ℬ ξ₁ ξ₂] [SymbolLike ℬ' ξ₁ ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    ℬ.HierarchyOn ℬ'.Closure Γ s (ω ▹ φ) ↔ ℬ.HierarchyOn ℬ'.Closure Γ s φ :=
  rew_iff_of fun _ _ ↦ Closure.rew_iff

end rew

lemma exsClosure : {n : ℕ} → {φ : Semiformula L ξ n} →
    ℬ.HierarchyOn C 𝚺 (s + 1) φ → ℬ.HierarchyOn C 𝚺 (s + 1) (exsClosure φ)
  | 0, _, hp => hp
  | _ + 1, φ, hp => exsClosure (φ := ∃¹ φ) hp.exs

lemma allClosure : {n : ℕ} → {φ : Semiformula L ξ n} →
    ℬ.HierarchyOn C 𝚷 (s + 1) φ → ℬ.HierarchyOn C 𝚷 (s + 1) (∀¹* φ)
  | 0, _, hp => hp
  | _ + 1, _, hp => by rw [allClosure_succ]; exact allClosure hp.all

lemma toPrenex {j : ℕ} {φ : Semiformula L ξ (n + s)}
    (h : ℬ.HierarchyOn C (Γ.altItr s) j φ) :
    ℬ.HierarchyOn C Γ (j + s) (φ.toPrenex Γ s) := by
  induction s generalizing n j with
  | zero => simpa using h;
  | succ s ih =>
    rw [Polarity.altItr_succ] at h;
    change ℬ.HierarchyOn C Γ (j + (s + 1)) (Polarity.quantItr Γ (s + 1) φ);
    rw [Polarity.quantItr_succ', (show j + (s + 1) = (j + 1) + s by omega)];
    rcases hΓ : Γ.altItr s with _ | _;
    · apply ih;
      rw [hΓ] at h ⊢;
      exact h.sigma;
    · apply ih;
      rw [hΓ] at h ⊢;
      exact h.pi;

lemma toPrenex_of_initial {φ : Semiformula L ξ (n + s)} (h : C φ) :
    ℬ.HierarchyOn C Γ s (φ.toPrenex Γ s) := by
  simpa using toPrenex (Γ := Γ) (j := 0) (initial _ _ _ h);

end HierarchyOn

namespace Hierarchy

open InitialClass HierarchyOn

variable {ℬ : Bounding L}

lemma zero_iff_bounded {Γ} {φ : Semiformula L ξ n} : ℬ.Hierarchy Γ 0 φ ↔ ℬ.Closure φ :=
  zero_iff_initial

lemma sigma₁_induction [Small ℬ (ℬ.Closure : {n : ℕ} → Semiformula L ξ n → Prop)]
    {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hRel : ∀ n k (r : L.Rel k) (v : Fin k → Semiterm L ξ n), P n (.rel r v))
    (hNRel : ∀ n k (r : L.Rel k) (v : Fin k → Semiterm L ξ n), P n (.nrel r v))
    (hAnd : ∀ n φ ψ, ℬ.Hierarchy 𝚺 1 φ → ℬ.Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, ℬ.Hierarchy 𝚺 1 φ → ℬ.Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ R (_hR : R ∈ ℬ) n t φ, ℬ.Hierarchy 𝚺 1 φ → P (n + 1) φ →
      P n (∀¹[R.operator ![#0, Rew.bShift t]] φ))
    (hExs : ∀ n φ, ℬ.Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃¹ φ))
    (hOperator : ∀ R (_hR : R ∈ ℬ) n t, P (n + 1) (R.operator ![#0, Rew.bShift t]))
    (n φ) : ℬ.Hierarchy 𝚺 1 φ → P n φ
  | HierarchyOn.initial _ _ _ h => by
    rename_i φ₀;
    clear φ₀;
    induction h with
    | verum n => exact hVerum n;
    | falsum n => exact hFalsum n;
    | rel r v => exact hRel _ _ r v;
    | nrel r v => exact hNRel _ _ r v;
    | and hp hq ihp ihq =>
      exact hAnd _ _ _ (initial _ _ _ hp) (initial _ _ _ hq) ihp ihq;
    | or hp hq ihp ihq =>
      exact hOr _ _ _ (initial _ _ _ hp) (initial _ _ _ hq) ihp ihq;
    | ball hR ht hp ih =>
      obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
      exact hBall _ hR _ t _ (initial _ _ _ hp) ih;
    | bexs hR ht hp ih =>
      obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
      exact hExs _ _ (and (operator hR _) (initial _ _ _ hp))
        (hAnd _ _ _ (operator hR _) (initial _ _ _ hp) (hOperator _ hR _ t) ih);
  |                 HierarchyOn.and hp hq =>
    hAnd _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hq)
  |                  HierarchyOn.or hp hq =>
    hOr _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hq)
  |                HierarchyOn.ball hR pt hp => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩;
    exact hBall _ hR _ t _ hp
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp);
  |                 HierarchyOn.bexs hR pt hp => by
    apply hExs;
    · exact and (operator hR _) hp;
    · rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩;
      apply hAnd _ _ _ (operator hR _) hp (hOperator _ hR _ t)
        (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp);
  |         HierarchyOn.sigma (φ := φ) hp =>
    have : ℬ.Hierarchy 𝚺 1 φ := hp.accum _
    hExs _ _ this
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ this)
  |                    HierarchyOn.exs hp =>
    hExs _ _ hp
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)

end Hierarchy

namespace StrictHierarchy

open HierarchyOn

variable {ℬ : Bounding L}

lemma hierarchy {φ : Semiformula L ξ n} : ℬ.StrictHierarchy Γ s φ → ℬ.Hierarchy Γ s φ :=
  mono_bounding (strict_le ℬ)

lemma of_deltaZero {φ : Semiformula L ξ n} (h : ℬ.Hierarchy Γ' 0 φ) : ℬ.StrictHierarchy Γ s φ :=
  initial _ _ _ (Hierarchy.zero_iff_bounded.mp h)

lemma zero_iff_hierarchy {φ : Semiformula L ξ n} :
    ℬ.StrictHierarchy Γ 0 φ ↔ ℬ.Hierarchy Γ' 0 φ :=
  zero_iff_initial.trans Hierarchy.zero_iff_bounded.symm

end StrictHierarchy

end FFL.FirstOrder.Bounding

end
