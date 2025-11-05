#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let arrows = json("./Propositional.json").map(((from, to, type)) => {
  if type == "ssub" {
    return strfmt("\"{}\" -> \"{}\"", to, from)
  } else if type == "sub" {
    return strfmt("\"{}\" -> \"{}\" [style=dashed] ", to, from)
  } else if type == "sorry" {
    return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", to, from)
  }
})

#figure(caption: [Propositional Logic Zoo], numbering: none)[
  #raw-render(
    raw(
      "
  digraph PropositionalLogicZoo {
    rankdir = RL;
    node [
      shape=none
      margin=0.1
      width=0
      height=0
    ]

    edge [
      style = solid
      arrowhead = vee
      arrowsize = 0.75
    ];
  "
        + arrows.join("\n")
        + "}",
    ),
    labels: (
      "LO.Propositional.Cl": $Logic("Cl")$,
      "LO.Propositional.Int": $Logic("Int")$,
      "LO.Propositional.KC": $Logic("KC")$,
      "LO.Propositional.KrieselPutnam": $Logic("KP")$,
      "LO.Propositional.LC": $Logic("LC")$,
    ),
    width: 640pt,
  )
]
