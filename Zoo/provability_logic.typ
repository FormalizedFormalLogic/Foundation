#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let Logic(L) = $sans(#L)$
#let PL(T, U) = $upright("PL")(#T, #U)$
#let PA = $Theory("PA")$
#let TA = $Theory("TA")$
#let ISigma1 = $Theory(I)Sigma_1$
#let TCon(T) = $#T + {"Con"_(#T)^n : n in omega}$

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
      "𝗜𝚺₁.provabilityLogicRelativeTo (𝗜𝚺₁ ∪ Set.range (FFL.FirstOrder.Theory.standardProvability 𝗜𝚺₁).conItr)": PL(
        ISigma1,
        TCon(ISigma1),
      ),
      "𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ Set.range (FFL.FirstOrder.Theory.standardProvability 𝗣𝗔).conItr)": PL(
        PA,
        TCon(PA),
      ),
    ),
    width: auto,
  )
]
