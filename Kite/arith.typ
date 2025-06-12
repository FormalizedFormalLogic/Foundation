#import "@preview/diagraph:0.3.1": *
#import "@preview/oxifmt:0.2.1": strfmt

#set page(width: auto, height: auto, margin: 24pt)

#let Logic(L) = $upright(bold(#L))$
#let Axiom(A) = $upright(sans(#A))$

#let arrows = json("./arith.json").map(((from, to, type)) => {
  if type == "ssub" {
    return strfmt("\"{}\" -> \"{}\"", from, to)
  } else if type == "sub" {
    return strfmt("\"{}\" -> \"{}\" [style=dashed] ", from, to)
  } else if type == "sorry" {
    return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", from, to)
  }
})

#figure(caption: [Kite of Arithmetic Theories], numbering: none)[
  #raw-render(
    raw(
      "
  digraph ModalLogicsKite {
    rankdir = BT;

    node [
      shape=none
      margin=0.1
      width=0
      height=0
    ]

    edge [
      style = solid
      arrowhead = vee
      arrowsize = 0.5
    ];
  "
        + arrows.join("\n")
        + "}",
    ),
    labels: (
      "𝐈Open": $Logic("IOpen")$,
      "𝐈𝚺₀ + 𝛀₁": $Logic(I Sigma_0 + Omega_1)$,
      "𝐈𝚺₀": $Logic(I Sigma_0)$,
      "𝐈𝚺₁": $Logic(I Sigma_1)$,
      "𝐏𝐀": $Logic("PA")$,
      "𝐏𝐀⁻": $Logic("PA"^-)$,
      "𝐑₀'": $Logic(R'_0)$,
      "𝐑₀": $Logic(R_0)$,
      "𝐓𝐀": $Logic("TA")$,
      "𝐄𝐐": $Logic("EQ")$,
    ),
    width: 240pt,
  )
]
