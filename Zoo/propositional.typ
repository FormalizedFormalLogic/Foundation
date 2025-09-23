#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let arrows = json("./propositional.json").map(((from, to, type)) => {
  if type == "ssub" {
    return strfmt("\"{}\" -> \"{}\"", from, to)
  } else if type == "sub" {
    return strfmt("\"{}\" -> \"{}\" [style=dashed] ", from, to)
  } else if type == "sorry" {
    return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", from, to)
  }
})

#figure(caption: [Propositional Logic Zoo], numbering: none)[
  #raw-render(
    raw(
      "
  digraph PropositionalLogicZoo {
    rankdir = LR;
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
    width: 240pt,
  )
]
