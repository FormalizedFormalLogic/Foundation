#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let Logic(L) = $sans(#L)$
#let PL(T, U) = $upright("PL")(#T, #U)$
#let PA = $Theory("PA")$
#let TA = $Theory("TA")$
#let ISigma1 = $Theory(I)Sigma_1$
#let Rfn(G, T) = $upright("Rfn")_(#T)(#G)$
#let TCon(T) = $#T + upright("Con")_(#T)^omega$
#let TIncon(T) = $#T + not upright("Con")_(#T)$
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
      "FFL.ProvabilityLogic.Logic.GLPlusBoxBot 1": $Logic("GL") + square bot$,
      "𝗣𝗔.provabilityLogic": PL(PA, PA),
      "𝗣𝗔.provabilityLogicRelativeTo 𝗧𝗔": PL(PA, TA),
      "(𝗣𝗔 ∪ FFL.FirstOrder.Theory.Incon 𝗣𝗔).provabilityLogic": PL(TIncon(PA), TIncon(PA)),
      "𝗜𝚺₁.provabilityLogicRelativeTo (𝗜𝚺₁ ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] 𝗜𝚺₁)": PL(ISigma1, TRfnSigma1(ISigma1)),
      "𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] 𝗣𝗔)": PL(PA, TRfnSigma1(PA)),
      "𝗜𝚺₁.provabilityLogicRelativeTo (𝗜𝚺₁ ∪ FFL.FirstOrder.Theory.Conω 𝗜𝚺₁)": PL(ISigma1, TCon(ISigma1)),
      "𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ FFL.FirstOrder.Theory.Conω 𝗣𝗔)": PL(PA, TCon(PA)),
    ),
    width: auto,
  )
]
