import Logic.Modal.Standard.PLoN.Semantics

namespace LO.Modal.Standard

namespace PLoN

open System Formula

variable {p : Formula α} {Λ : DeductionParameter α}

lemma sound (characterized : Λ.CharacterizedByPLoNFrameClass 𝔽) (d : Λ ⊢! p) : 𝔽 ⊧ p := by
  intro F hF;
  have := characterized hF;
  exact Semantics.RealizeSet.setOf_iff.mp this p d;

lemma sound_of_characterized (defines : Λ.CharacterizedByPLoNFrameClass 𝔽) : Sound Λ 𝔽 := ⟨sound defines⟩

lemma unprovable_bot_of_nonempty_frameclass (characterized : Λ.CharacterizedByPLoNFrameClass 𝔽) (nonempty : 𝔽.Nonempty) : Λ ⊬! ⊥ := by
  intro h;
  obtain ⟨⟨_, F⟩, hF⟩ := nonempty;
  simpa using sound characterized h hF;

lemma consistent_of_characterized (characterized : Λ.CharacterizedByPLoNFrameClass 𝔽) (nonempty : 𝔽.Nonempty) : System.Consistent Λ := by
  apply System.Consistent.of_unprovable;
  exact unprovable_bot_of_nonempty_frameclass characterized nonempty;


instance : Sound 𝐍 (AllFrameClass α) := sound_of_characterized N_characterized

instance : Sound 𝐍𝟒 (TransitiveFrameClass α) := sound_of_characterized N4_characterized

instance : Sound 𝐍(𝐑) (SerialFrameClass α) := sound_of_characterized NRosser_characterized

instance : Sound 𝐍𝟒(𝐑) (TransitiveSerialFrameClass α) := sound_of_characterized N4Rosser_characterized

instance : System.Consistent (𝐍 : DeductionParameter α) := consistent_of_characterized N_characterized AllFrameClass.nonempty

instance : System.Consistent (𝐍𝟒 : DeductionParameter α) := consistent_of_characterized N4_characterized TransitiveFrameClass.nonempty

instance : System.Consistent (𝐍(𝐑) : DeductionParameter α) := consistent_of_characterized NRosser_characterized SerialFrameClass.nonempty

instance : System.Consistent (𝐍𝟒(𝐑) : DeductionParameter α) := consistent_of_characterized N4Rosser_characterized TransitiveSerialFrameClass.nonempty

end PLoN

end LO.Modal.Standard
