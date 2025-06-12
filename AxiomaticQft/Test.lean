import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section
open scoped MeasureTheory        -- **inside** the section — not above it!

/-! ### Geometry -/
def STDimension : ℕ := 4
abbrev RSpaceTime := EuclideanSpace ℝ (Fin STDimension)
abbrev μ : Measure RSpaceTime := volume        -- Lebesgue, just named “μ”

/-! ### L² real-valued fields -/
abbrev FieldSpace' :=
  Lp (p := 2) (μ := μ) ℝ              -- p is an ℝ≥0∞ literal

--attribute [reducible] FieldSpace'

instance : MeasurableSpace FieldSpace' := borel _
instance : BorelSpace    FieldSpace' := ⟨rfl⟩

/-! ### Observable (p, φ) ↦ ∫ p(φ(x)) dμ(x) -/
noncomputable def polyObservable (p : Polynomial ℝ) (φ : FieldSpace') : ℝ :=
  ∫ x, p.eval ((φ : RSpaceTime →ₘ[μ] ℝ) x) ∂μ
--               ^ no space after →ᵐ    ^ no parentheses after ∂

end
