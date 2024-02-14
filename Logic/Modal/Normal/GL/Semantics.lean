import Logic.Modal.Normal.Semantics

namespace LO.Modal.Normal

variable {α β : Type u} [Inhabited β]

open Formula

namespace AxiomL

variable (β) [Inhabited β]
variable (F: Frame α)

private lemma implies_transitive : (⊧ᴹ[F] (𝐋 : AxiomSet β)) → Transitive F := by
  contrapose;
  intro hT; simp [Transitive] at hT;
  obtain ⟨w₁, w₂, w₃, r₂₃, r₁₂, nr₁₃⟩ := hT;
  apply Theory.not_Frames;
  simp [AxiomL, AxiomL.set];
  existsi (λ w' _ => (w' ≠ w₂ ∧ w' ≠ w₃)), w₁, (atom default);
  constructor;
  . intro x hx h;
    by_cases hx₂ : x = w₂;
    . simp_all [hx₂]; simpa using h w₃ r₂₃;
    . by_cases hx₃ : x = w₃ <;> simp_all [hx₃];
  . existsi w₂;
    aesop;

private lemma implies_cwf  : (⊧ᴹ[F] (𝐋 : AxiomSet β)) → ConverseWellFounded F := by
  contrapose;
  intro hCF;
  obtain ⟨X, hX₁, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
  let V : Valuation α β := λ w _ => w ∉ X;
  let w := hX₁.some;
  let a : Formula β := atom default;
  apply Theory.not_Frames;
  simp [Theory.Satisfies, AxiomL.set, AxiomL, -Satisfies.box_def];
  existsi V, w, a;
  constructor;
  . simp only [Formula.Satisfies.box_def];
    intro x _;
    by_cases hxs : x ∈ X
    . obtain ⟨y, hy₁, hy₂⟩ := hX₂ x hxs;
      simp only [Formula.Satisfies.imp_def];
      left;
      simp;
      existsi y;
      constructor;
      . simpa [flip] using hy₂;
      . simpa;
    . aesop;
  . obtain ⟨w', hw'₁, hw'₂⟩ := hX₂ w (by apply Set.Nonempty.some_mem);
    simp;
    existsi w';
    constructor;
    . simpa [flip] using hw'₂;
    . simp_all;

private lemma impliedby : (Transitive F ∧ ConverseWellFounded F) → (⊧ᴹ[F] (𝐋 : AxiomSet β)) := by
  rintro ⟨hTrans, hWF⟩;
  simp [AxiomL, AxiomL.set];
  intro p V w;
  simp only [Formula.Satisfies.imp_def'];
  suffices (w ⊮ᴹ[⟨F, V⟩] □p) → (w ⊮ᴹ[⟨F, V⟩] □(□p ⟶ p)) by exact not_imp_not.mp this;

  intro h; simp [Unsatisfies] at h;
  obtain ⟨z, rwz, hz⟩ := h;
  obtain ⟨xm, ⟨hxm₁, hxm₂⟩⟩ := hWF.has_min ({ x | (F w x) ∧ (x ⊮ᴹ[⟨F, V⟩] p) }) (by existsi z; simp [rwz, hz]; exact hz)

  have h₁ : (xm ⊩ᴹ[⟨F, V⟩] □p) := by
    simp [Satisfies.box_def];
    intro y hy;
    have : F w y := hTrans (by simp_all) hy;
    by_contra hC;
    have := hxm₂ y ⟨(hTrans (by simp_all) hy), hC⟩;
    contradiction;
  have h₂ : (xm ⊮ᴹ[⟨F, V⟩] (□p ⟶ p)) := by
    simp only [Unsatisfies, Formula.Satisfies.imp_def', not_imp];
    constructor;
    . exact h₁
    . simp_all;
  have h₃ : w ⊮ᴹ[⟨F, V⟩] □(□p ⟶ p) := by
    simp [Unsatisfies, Satisfies.box_def, -Satisfies.imp_def'];
    existsi xm;
    constructor;
    . simp_all;
    . exact h₂;
  exact h₃;

lemma defines : (Transitive F ∧ ConverseWellFounded F) ↔ (⊧ᴹ[F] (𝐋 : AxiomSet β)) := ⟨
    by apply impliedby,
    by intro h; exact ⟨implies_transitive β F h, implies_cwf β F h⟩
  ⟩

end AxiomL


namespace LogicGL

@[instance]
lemma defines_trans_converseWellFounded : @FrameClassDefinability α β 𝐆𝐋 (λ F => (Transitive F ∧ ConverseWellFounded F)) := by
  intro F;
  simp [LogicGL, AxiomSetFrameClass.union];
  have := AxiomK.defines β F;
  have := AxiomL.defines β F;
  aesop;

@[instance]
lemma defines_finite_trans_irreflexive [Finite α] : @FrameClassDefinability α β 𝐆𝐋 (λ F => (Transitive F ∧ Irreflexive F)) := by
  intro F;
  simp;
  have hd := @defines_trans_converseWellFounded α β _;
  constructor;
  . intro h;
    obtain ⟨hTrans, hIrrefl⟩ := h;
    have hCWF := @Finite.converseWellFounded_of_trans_irrefl _ F _ ⟨hTrans⟩ ⟨hIrrefl⟩;
    exact hd.mp ⟨hTrans, hCWF⟩;
  . intro h;
    obtain ⟨hTrans, hCWF⟩ := hd.mpr h;
    have := ConverseWellFounded.iff_has_max.mp hCWF;
    exact ⟨hTrans, (
      by
        by_contra hIrrefl;
        simp [Irreflexive] at hIrrefl;
        obtain ⟨w, h⟩ := hIrrefl;
        have := this {w} (by simp);
        simp_all;
    )⟩

@[instance]
lemma existsTrivialFiniteFrame [Finite α] : Nonempty (𝔽((𝐆𝐋 : AxiomSet β)) : FrameClass α) := ⟨
  (λ _ _ => False),
  (by
    apply defines_finite_trans_irreflexive.mp;
    constructor;
    . simp [Transitive];
    . simp [Irreflexive];
  )
⟩

end LogicGL

end LO.Modal.Normal
