/-
Copyright (c) 2025 MRD. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
open scoped MeasureTheory

def STDimension := 4
-- def LSpaceTime := PhysLean.Relativity.Lorentz.SpaceTime.Basic STDimension
abbrev RSpaceTime := EuclideanSpace ℝ (Fin STDimension)
abbrev μ : Measure RSpaceTime := volume    -- Lebesgue, just named “μ”

/- Space of fields -/

abbrev FieldSpace := Lp (p := 2) (μ := μ) ℝ
instance : MeasurableSpace FieldSpace := borel _
instance : BorelSpace    FieldSpace := ⟨rfl⟩

variable (x : RSpaceTime) (φ : FieldSpace)

/- Probability distribution over fields -/

variable (dμ : ProbabilityMeasure FieldSpace)

/- Functionals (random variables) which appear in the action
   There is a conceptual problem: L^2 functions are defined almost
   everywhere so don't have unique values at points.  So, we need
   to coerce to a regular function, apply the operator and go back.
   Ultimately we may need a different function class than L^p.
-/

def polyEval (p : Polynomial ℝ) (φ : FieldSpace) : RSpaceTime → ℝ :=
  fun x ↦ p.eval ((φ : RSpaceTime →ₘ[μ] ℝ) x)

def polyObservable (p : Polynomial ℝ) (φ : FieldSpace) : ℝ :=
  ∫ x, p.eval ((φ : RSpaceTime →ₘ[μ] ℝ) x) ∂μ
