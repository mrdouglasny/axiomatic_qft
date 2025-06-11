/-
Copyright (c) 2025 MRD. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

-- import PhysLean.Relativity.Lorentz.Algebra.Basic
-- import PhysLean.Relativity.Lorentz.Group.Basic
-- import PhysLean.Relativity.Lorentz.SpaceTime.Basic

/-!
# Axiomatic Quantum Field Theory

This should include the Wightman and Osterwalder-Schrader axioms.

The eventual goal could be to formulate and prove the reconstruction theorem relating the two.

Prerequisites which don't yet exist (but see PhysLean ?)
- Quantum mechanics on Hilbert space

General definitions
O-S axioms

-/

--set_option diagnostics true

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section

def STDimension := 4
-- def LSpaceTime := PhysLean.Relativity.Lorentz.SpaceTime.Basic STDimension
abbrev RSpaceTime := EuclideanSpace ℝ (Fin STDimension)
def μ := (volume : Measure RSpaceTime)


/- Space of fields -/

def FieldSpace := Lp (p := 2) (μ := (volume : Measure RSpaceTime)) ℝ
--def FieldSpace := Lp (p := 2) μ ℝ
attribute [reducible] FieldSpace

instance : MeasurableSpace FieldSpace := borel _
instance : BorelSpace    FieldSpace := ⟨rfl⟩

/- Probability distribution over fields -/

variable (dμ : ProbabilityMeasure FieldSpace)
