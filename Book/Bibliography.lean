import VersoManual

open Verso.Genre.Manual

-- TODO: Book
def CZ97 : ArXiv where
  title := inlines!"Modal Logic"
  authors := #[
    inlines!"A. Chagrov",
    inlines!"M. Zakharyaschev"
  ]
  year := 1997
  id := "none"

-- TODO: Book
def Boo94 : ArXiv where
  title := inlines!"The Logic of Provability"
  authors := #[inlines!"G. Boolos"]
  year := 1994
  id := "none"

-- TODO: Book
def CH07 : ArXiv where
  title := inlines!"A New Introduction to Modal Logic"
  authors := #[
    inlines!"G. E. Hudges",
    inlines!"M. J. Cresswell",
  ]
  year := 2007
  id := "none"

def Seg71 : Thesis where
  title := inlines!"An Essay in Classical Modal Logic"
  author := inlines!"K. Segerberg"
  year := 1971
  degree := inlines!"Ph.D Thesis"
  university := inlines!"Stanford University"

def Kop23 : ArXiv where
  title := inlines!"The Finite Model Property of Some Non-normal Modal Logics with the Transitivity Axiom"
  authors := #[
    inlines!"K. Kopnev",
  ]
  year := 2023
  id := "2305.08605"

def Lew74 : Article where
  title := inlines!"Intensional Logics without Iterative Axioms"
  authors := #[
    inlines!"D. Lewis",
  ]
  journal := inlines!"Journal of Philosophical Logic"
  year := 1974
  month := some inlines!"October"
  volume := inlines!"3"
  number := inlines!"4"

def KO21 : Article where
  title := inlines!"Modal completeness of sublogics of the interpretability logic IL"
  authors := #[
    inlines!"Taishi. Kurahashi",
    inlines!"Yuya. Okawa",
  ]
  journal := inlines!"Mathematical Logic Quarterly"
  year := 2021
  month := some inlines!"May"
  volume := inlines!"67"
  number := inlines!"2"

-- TODO: `Book`
def Vis88 : ArXiv where
  title := inlines!"Preliminary Notes on Interpretability Logic"
  authors := #[
    inlines!"Albert. Visser",
  ]
  year := 1988
  id := "none"

def Rov20 : Thesis where
  title := inlines!"Interpretability Logics and Generalized Veltman Semantics in Agda"
  author := inlines!"Jan Mas. Rovira"
  year := 2020
  degree := inlines!"Master thesis"
  university := inlines!"The University of Amsterdam"
  url := some "https://diposit.ub.edu/dspace/handle/2445/173054"

-- TODO: `incollection`
def DV90 : ArXiv where
  title := inlines!"Provability Logics for Relative Interpretability"
  authors := #[
    inlines!"Dick. de Jongh",
    inlines!"Frank. Veltman",
  ]
  year := 1990
  id := "none"

def Joo04 : Thesis where
  title := inlines!"Interpretability Formalized"
  author := inlines!"Joost Johannes. Joosten"
  year := 2004
  degree := inlines!"Ph.D Thesis"
  university := inlines!"Utrecht University"

-- TODO: `Book`
def Vis97 : ArXiv where
  title := inlines!"An Overview of Interpretability Logic"
  authors := #[
    inlines!"Albert. Visser",
  ]
  year := 1997
  id := "none"

-- TODO: `incollection`
def JD98 : ArXiv where
  title := inlines!"The Logic of Provability"
  authors := #[
    inlines!"Giorgi. Japaridze",
    inlines!"Dick. de Jongh",
  ]
  year := 1998
  id := "none"

-- TODO: `incollection`
def JRMV24 : InProceedings where
  title := inlines!"An Overview of Verbrugge Semantics, a.k.a. Generalised Veltman Semantics"
  authors := #[
    inlines!"Joost J. Joosten",
    inlines!"Jan Mas. Rovira",
    inlines!"Luka. Mikec",
    inlines!"Mladen. Vuković",
  ]
  year := 2024
  booktitle := inlines!"Dick de Jongh on Intuitionistic and Provability Logics"

-- TODO: `incollection`
def Werner97 : ArXiv where
  title := inlines!"Sets in types, types in sets"
  authors := #[
    inlines!"Benjamin. Werner",
  ]
  year := 1997
  id := "none"

def Carneiro19 : Thesis where
  title := inlines!"The Type Theory of Lean"
  author := inlines!"Mario Carneiro"
  year := 2019
  university := inlines!"Carnegie Mellon University"
  url := some "https://github.com/digama0/lean-type-theory/releases/download/v1.0/main.pdf"
  degree := inlines!"Master thesis"
