#import "@preview/diagraph:0.3.1": *
#import "@preview/oxifmt:0.2.1": strfmt

#set page(width: auto, height: auto, margin: 24pt)

#let Logic(L) = $upright(bold(#L))$
#let Axiom(A) = $upright(sans(#A))$
#let Rule(A) = $(upright(#A))$

#let arrows = json("./modal.json").map(((from, to, type)) => {
  if type == "ssub" {
    return strfmt("\"{}\" -> \"{}\"", from, to)
  } else if type == "sub" {
    return strfmt("\"{}\" -> \"{}\" [style=dashed] ", from, to)
  } else if type == "eq" {
    return strfmt("\"{}\" -> \"{}\" [color=\"black:white:black\" arrowhead=\"none\"] ", from, to)
  } else if type == "sorry" {
    return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", from, to)
  }
})

#figure(caption: [Kite of Modal Logics], numbering: none)[
  #raw-render(
    raw(
      "
  digraph ModalLogicsKite {
    rankdir = BT;

    node [
      margin=0.1
      width=0
      height=0
    ]

    edge [
      style = solid
      arrowhead = vee
      arrowsize = 0.75
    ];

    {rank = same; \"LO.Modal.Logic.Triv\"; \"LO.Modal.Logic.Ver\";}
    {rank = same; \"LO.Modal.Logic.KD\"; \"LO.Modal.Logic.KB\"; \"LO.Modal.Logic.K4\"; \"LO.Modal.Logic.K5\";}
    {rank = same; \"LO.Modal.Logic.KT\"; \"LO.Modal.Logic.KDB\"; \"LO.Modal.Logic.KD4\"; \"LO.Modal.Logic.KD5\"; \"LO.Modal.Logic.K45\";}
    {rank = same; \"LO.Modal.Logic.KTB\"; \"LO.Modal.Logic.S4\"; \"LO.Modal.Logic.KD45\"; \"LO.Modal.Logic.KB4\";}
    {rank = same; \"LO.Modal.Logic.GL\"; \"LO.Modal.Logic.Grz\";}
    {rank = same; \"LO.Modal.Logic.GL\"; \"LO.Modal.Logic.K4Henkin\"; \"LO.Modal.Logic.K4Loeb\"; \"LO.Modal.Logic.K4Hen\";}
    {rank = same; \"LO.Modal.Logic.GLPoint2\"; \"LO.Modal.Logic.GrzPoint2\";}
    {rank = same; \"LO.Modal.Logic.GLPoint3\"; \"LO.Modal.Logic.GrzPoint3\";}
    {rank = same; \"LO.Modal.Logic.GLPoint3\"; \"LO.Modal.Logic.GrzPoint3\";}
    {rank = same; \"LO.Modal.Logic.S5Grz\"; \"LO.Modal.Logic.Triv\";}
    {rank = same; \"LO.Modal.Logic.KP\"; \"LO.Modal.Logic.KD\";}
    {rank = same; \"𝐄𝐌𝐂𝐍\"; \"LO.Modal.Logic.K\";}
  "
        + arrows.join("\n")
        + "}",
    ),
    labels: (
      "𝐄": $Logic("E")$,
      "𝐄𝐂": $Logic("EC")$,
      "𝐄𝐂𝐍": $Logic("ECN")$,
      "𝐄𝐊": $Logic("EK")$,
      "𝐄𝐌": $Logic("EM")$,
      "𝐄𝐌𝐂": $Logic("EMC")$,
      "𝐄𝐌𝐂𝐍": $Logic("EMCN")$,
      "𝐄𝐌𝐍": $Logic("EMN")$,
      "𝐄𝐍": $Logic("EN")$,
      "LO.Modal.Logic.Dum": $Logic("Dum")$,
      "LO.Modal.Logic.DumPoint2": $Logic("Dum.2")$,
      "LO.Modal.Logic.DumPoint3": $Logic("Dum.3")$,
      "LO.Modal.Logic.Dz": $Logic("Dz")$,
      "LO.Modal.Logic.Empty": $emptyset$,
      "LO.Modal.Logic.GL": $Logic("GL")$,
      "LO.Modal.Logic.GLPoint2": $Logic("GL.2")$,
      "LO.Modal.Logic.GLPoint3": $Logic("GL.3")$,
      "LO.Modal.Logic.Grz": $Logic("Grz")$,
      "LO.Modal.Logic.GrzPoint2": $Logic("Grz.2")$,
      "LO.Modal.Logic.GrzPoint2M": $Logic("Grz.2M")$,
      "LO.Modal.Logic.GrzPoint3": $Logic("Grz.3")$,
      "LO.Modal.Logic.K": $Logic("K")$,
      "LO.Modal.Logic.K4": $Logic("K4")$,
      "LO.Modal.Logic.K45": $Logic("K45")$,
      "LO.Modal.Logic.K4Hen": $Logic("K4Hen")$,
      "LO.Modal.Logic.K4Henkin": $Logic("K4") + Rule("Henkin")$,
      "LO.Modal.Logic.K4Loeb": $Logic("K4") + Rule("Löb")$,
      "LO.Modal.Logic.K4McK": $Logic("K4McK")$,
      "LO.Modal.Logic.K4Point2": $Logic("K4.2")$,
      "LO.Modal.Logic.K4Point2Z": $Logic("K4.2Z")$,
      "LO.Modal.Logic.K4Point3": $Logic("K4.3")$,
      "LO.Modal.Logic.K4Point3Z": $Logic("K4.3Z")$,
      "LO.Modal.Logic.K4Z": $Logic("K4Z")$,
      "LO.Modal.Logic.K5": $Logic("K5")$,
      "LO.Modal.Logic.KB": $Logic("KB")$,
      "LO.Modal.Logic.KB4": $Logic("KB4")$,
      "LO.Modal.Logic.KB5": $Logic("KB5")$,
      "LO.Modal.Logic.KD": $Logic("KD")$,
      "LO.Modal.Logic.KD4": $Logic("KD4")$,
      "LO.Modal.Logic.KD45": $Logic("KD45")$,
      "LO.Modal.Logic.KD5": $Logic("KD5")$,
      "LO.Modal.Logic.KDB": $Logic("KDB")$,
      "LO.Modal.Logic.KHen": $Logic("KHen")$,
      "LO.Modal.Logic.KMcK": $Logic("KMcK")$,
      "LO.Modal.Logic.KP": $Logic("KP")$,
      "LO.Modal.Logic.KT": $Logic("KT")$,
      "LO.Modal.Logic.KTB": $Logic("KTB")$,
      "LO.Modal.Logic.KTc": $Logic("KTc")$,
      "LO.Modal.Logic.KTMk": $Logic("KTMk")$,
      "LO.Modal.Logic.N": $Logic("N")$,
      "LO.Modal.Logic.S": $Logic("S")$,
      "LO.Modal.Logic.S4": $Logic("S4")$,
      "LO.Modal.Logic.S4McK": $Logic("S4McK")$,
      "LO.Modal.Logic.S4Point2": $Logic("S4.2")$,
      "LO.Modal.Logic.S4Point2McK": $Logic("S4.2McK")$,
      "LO.Modal.Logic.S4Point2Point4M": $Logic("S4.2.4M")$,
      "LO.Modal.Logic.S4Point3": $Logic("S4.3")$,
      "LO.Modal.Logic.S4Point3McK": $Logic("S4.3McK")$,
      "LO.Modal.Logic.S4Point4": $Logic("S4.4")$,
      "LO.Modal.Logic.S4Point4McK": $Logic("S4.4McK")$,
      "LO.Modal.Logic.S4Point9": $Logic("S4.4") + Axiom("M18")$,
      "LO.Modal.Logic.S5": $Logic("S5")$,
      "LO.Modal.Logic.S5Grz": $Logic("S5Grz")$,
      "LO.Modal.Logic.Triv": $Logic("Triv")$,
      "LO.Modal.Logic.Univ": $bot$,
      "LO.Modal.Logic.Ver": $Logic("Ver")$,
    ),
    width: 640pt,
  )
]
