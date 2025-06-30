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

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section
open scoped MeasureTheory

def STDimension := 4
abbrev RSpaceTime := EuclideanSpace ℝ (Fin STDimension)
abbrev μ : Measure RSpaceTime := volume    -- Lebesgue, just named “μ”

/- Space of fields -/

abbrev FieldSpace := Lp (p := 2) (μ := μ) ℝ
instance : MeasurableSpace FieldSpace := borel _
instance : BorelSpace    FieldSpace := ⟨rfl⟩

variable (x : RSpaceTime) (φ : FieldSpace)

/- Probability distribution over fields -/

variable (dμ : ProbabilityMeasure FieldSpace)

def polyObservable (p : Polynomial ℝ) (φ : FieldSpace) : ℝ :=
  ∫ x, p.eval ((φ : RSpaceTime →ₘ[μ] ℝ) x) ∂μ
