import Foundation.Vorspiel.Vorspiel
import Foundation.Vorspiel.Order
--import Foundation.Vorspiel.Meta

import Foundation.Logic.LogicSymbol
import Foundation.Logic.Semantics
import Foundation.Logic.System

-- AutoProver

-- import Foundation.AutoProver.Litform
-- import Foundation.AutoProver.Prover

-- Propositional

import Foundation.Propositional.Classical.Basic.Formula
import Foundation.Propositional.Classical.Basic.Calculus
import Foundation.Propositional.Classical.Basic.Semantics
import Foundation.Propositional.Classical.Basic.Completeness
import Foundation.Propositional.Classical.Basic

-- import Foundation.Propositional.Translation

-- FirstOrder

import Foundation.FirstOrder.Basic

import Foundation.FirstOrder.Ultraproduct

import Foundation.FirstOrder.Completeness.Coding
import Foundation.FirstOrder.Completeness.SubLanguage
import Foundation.FirstOrder.Completeness.SearchTree
import Foundation.FirstOrder.Completeness.Completeness

import Foundation.FirstOrder.Order.Le
import Foundation.FirstOrder.Interpretation

import Foundation.FirstOrder.Arith.Basic
import Foundation.FirstOrder.Arith.Hierarchy
import Foundation.FirstOrder.Arith.StrictHierarchy
import Foundation.FirstOrder.Arith.Theory
import Foundation.FirstOrder.Arith.Model
import Foundation.FirstOrder.Arith.CobhamR0
import Foundation.FirstOrder.Arith.PeanoMinus
import Foundation.FirstOrder.Arith.Representation
import Foundation.FirstOrder.Arith.Nonstandard

import Foundation.FirstOrder.Hauptsatz

-- IntFO

import Foundation.IntFO.Basic
import Foundation.IntFO.Translation

-- IntProp
import Foundation.IntProp.Hilbert.Glivenko

import Foundation.IntProp.Kripke.Classical
import Foundation.IntProp.Kripke.Completeness
import Foundation.IntProp.Kripke.DP

import Foundation.IntProp.Heyting.Semantics

import Foundation.IntProp.Dialectica.Basic

-- Modal

/-
import Foundation.Modal.Hilbert.GL_Independency
import Foundation.Modal.Hilbert.Subst
import Foundation.Modal.Hilbert.Maximal.Unprovability

import Foundation.Modal.Hilbert.WeakerThan.GL_GLS
import Foundation.Modal.Hilbert.WeakerThan.K_K4
import Foundation.Modal.Hilbert.WeakerThan.K_K5
import Foundation.Modal.Hilbert.WeakerThan.K_KB
import Foundation.Modal.Hilbert.WeakerThan.K_KD
import Foundation.Modal.Hilbert.WeakerThan.K4_GL
import Foundation.Modal.Hilbert.WeakerThan.K4_Grz
import Foundation.Modal.Hilbert.WeakerThan.K4_K45
import Foundation.Modal.Hilbert.WeakerThan.K4_KD4
import Foundation.Modal.Hilbert.WeakerThan.K4_S4
import Foundation.Modal.Hilbert.WeakerThan.K4_Triv
import Foundation.Modal.Hilbert.WeakerThan.K45_KB4
import Foundation.Modal.Hilbert.WeakerThan.K5_K45
import Foundation.Modal.Hilbert.WeakerThan.K5_KD5
import Foundation.Modal.Hilbert.WeakerThan.KB_KDB
import Foundation.Modal.Hilbert.WeakerThan.KB5_S5
import Foundation.Modal.Hilbert.WeakerThan.KD_KDB
import Foundation.Modal.Hilbert.WeakerThan.KD_KT
import Foundation.Modal.Hilbert.WeakerThan.KD4_KD45
import Foundation.Modal.Hilbert.WeakerThan.KD45_S5
import Foundation.Modal.Hilbert.WeakerThan.KD5_KD45
import Foundation.Modal.Hilbert.WeakerThan.KDB_KTB
import Foundation.Modal.Hilbert.WeakerThan.KT_Grz
import Foundation.Modal.Hilbert.WeakerThan.KT_KTB
import Foundation.Modal.Hilbert.WeakerThan.KT_S4
import Foundation.Modal.Hilbert.WeakerThan.KTB_S5
import Foundation.Modal.Hilbert.WeakerThan.S4_S5

import Foundation.Modal.Hilbert.Equiv.GL
import Foundation.Modal.Hilbert.Equiv.KD_KP
import Foundation.Modal.Hilbert.Equiv.S5_KT4B
import Foundation.Modal.Hilbert.Equiv.S5Grz_Triv

import Foundation.Modal.ModalCompanion.GMT

import Foundation.Modal.Boxdot.K4_S4
import Foundation.Modal.Boxdot.GL_Grz
-/

import Foundation.Modal.Hilbert2.KP
import Foundation.Modal.Hilbert2.S5Grz
import Foundation.Modal.Hilbert2.GL.Alternatives
import Foundation.Modal.Hilbert2.GL.Independency

import Foundation.Modal.Kripke2.Hilbert.K
import Foundation.Modal.Kripke2.Hilbert.KT
import Foundation.Modal.Kripke2.Hilbert.KTB
import Foundation.Modal.Kripke2.Hilbert.KT4B
import Foundation.Modal.Kripke2.Hilbert.S4
import Foundation.Modal.Kripke2.Hilbert.S4Dot2
import Foundation.Modal.Kripke2.Hilbert.S4Dot3
import Foundation.Modal.Kripke2.Hilbert.S5
import Foundation.Modal.Kripke2.Hilbert.Triv
import Foundation.Modal.Kripke2.Hilbert.Ver

import Foundation.Modal.Kripke2.Hilbert.GL.Unnecessitation
import Foundation.Modal.Kripke2.Hilbert.GL.MDP

import Foundation.Modal.Kripke2.Hilbert.Grz.Completeness

import Foundation.Modal.Kripke2.NNFormula
import Foundation.Modal.Kripke2.ComplexityLimited
import Foundation.Modal.Kripke2.Undefinability

import Foundation.Modal.PLoN.Hilbert.N

import Foundation.Modal.ModalCompanion.GMT

import Foundation.Modal.Boxdot.K4_S4
import Foundation.Modal.Boxdot.GL_Grz
