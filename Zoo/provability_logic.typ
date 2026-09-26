#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let Logic(L) = $sans(#L)$
#let PL(T, U) = $upright("PL")(#T, #U)$
#let PA = $Theory("PA")$
#let TA = $Theory("TA")$

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
    ),
    width: auto,
  )
]
