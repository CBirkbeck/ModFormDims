import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.RiemannZeta

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex ArithmeticFunction

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

variable (k : ℤ) (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+))

noncomputable def E_k := ModularForm.eisensteinSeries_MF hk a

theorem Eisenstein_Series_q_expansion_Bernoulli (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (riemannZeta k) * (E_k k hk a) z =
      2 * ((-1) ^ (k / 2 + 1) * 2 ^ (2 * (k / 2) - 1) * π ^ k * bernoulli k / k !) +
        2 * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by sorry
