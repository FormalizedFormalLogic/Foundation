#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let Logic(L) = $sans(#L)$
#let PL(T, U) = $upright("PL")(#T, #U)$
#let PA = $Theory("PA")$
#let TA = $Theory("TA")$
#let ISigma1 = $Theory(I)Sigma_1$
#let Rfn(G, T) = $upright("Rfn")_(#G)(#T)$
#let TOmega(T) = $#T + Rfn({square_(#T)^n bot | n in NN}, #T)$
#let TRfnSigma1(T) = $#T + Rfn(Sigma_1, #T)$

// Keys are the logics as pretty-printed by `lake exe zoo_provability_logic`; a logic with no entry
// here is drawn under its pretty-printed name.
#figure(caption: [Provability Logic Zoo], numbering: none)[
  #zoo(
    "./provability_logic.json",
    labels: (
      "𝐆𝐋": Logic("GL"),
      "𝐀": Logic("A"),
      "𝐃": Logic("D"),
      "𝐒": Logic("S"),
      "𝐆𝐫𝐳": Logic("Grz"),
      "𝗣𝗔.provabilityLogic": PL(PA, PA),
      "𝗣𝗔.provabilityLogicRelativeTo 𝗧𝗔": PL(PA, TA),
      "𝗜𝚺₁.provabilityLogicRelativeTo (𝗜𝚺₁ ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] 𝗜𝚺₁)":
        PL(ISigma1, TRfnSigma1(ISigma1)),
      "𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] 𝗣𝗔)":
        PL(PA, TRfnSigma1(PA)),
      "𝗜𝚺₁.provabilityLogicRelativeTo (𝗜𝚺₁ ∪ 𝗥𝗳𝗻[Set.range fun x => (↑(FFL.FirstOrder.Theory.standardProvability 𝗜𝚺₁))^[x] ⊥] 𝗜𝚺₁)":
        PL(ISigma1, TOmega(ISigma1)),
      "𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗥𝗳𝗻[Set.range fun x => (↑(FFL.FirstOrder.Theory.standardProvability 𝗣𝗔))^[x] ⊥] 𝗣𝗔)":
        PL(PA, TOmega(PA)),
    ),
    width: auto,
  )
]
