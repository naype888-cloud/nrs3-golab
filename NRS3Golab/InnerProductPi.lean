/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib

/-!
# Inner product → Cauchy–Schwarz → exact `π`

In a real inner product space `V` the chain is:

1. **Cauchy–Schwarz** gives `|⟪x, y⟫ / (‖x‖ ‖y‖)| ≤ 1` (`cauchySchwarz_ratio`).
2. Hence `arccos` of that ratio is an honest angle: `cos (angle x y) = ⟪x, y⟫ / (‖x‖ ‖y‖)`
   (`cos_angle_of_cauchySchwarz`). Without Cauchy–Schwarz the ratio could leave `[-1, 1]` and
   `cos ∘ arccos` would not return it.
3. The straight angle is exactly `π` (`angle_self_neg`) and the three angles of every triangle
   add up to exactly `π` (`triangle_angle_sum`).
4. A chord between unit vectors at angle `θ` has length `2 sin (θ / 2)` (`norm_sub_unit`), so
   the regular `n`-gon inscribed in the unit circle has perimeter `2 n sin (π / n)`
   (`archimedesPerimeter`). It equals `6` for `n = 6` (`archimedesPerimeter_six`), it stays
   strictly below `2π` (`archimedesPerimeter_lt`), and it tends to `2π`
   (`tendsto_archimedesPerimeter`). The circumference over the diameter is `π`.

Compare `NRS3Golab.Hexagon`: in the hexagonal norm the unit circle *is* the hexagon, perimeter
`6`, so its `π` is `3`. In an inner product norm the inscribed hexagon still has perimeter `6`,
but the circle is the limit of the inscribed polygons, `2π > 6`. Only norms that come from an
inner product satisfy the parallelogram law (`parallelogram`, and `Mathlib`'s
`InnerProductSpace.ofNorm` for the converse of Jordan–von Neumann); the hexagonal norm
violates it (`NRS3Golab.hexNorm_not_parallelogram`).

## Scope

The circumference is taken as the limit of the perimeters of the inscribed regular polygons
(Archimedes). The arc length of `t ↦ (cos t, sin t)` as a variation is not computed here.
-/

namespace NRS3Golab

open Real InnerProductGeometry Filter Topology RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## 1. Cauchy–Schwarz makes the angle well defined -/

/-- **Cauchy–Schwarz**, normalized form. -/
theorem cauchySchwarz_ratio (x y : V) : |⟪x, y⟫ / (‖x‖ * ‖y‖)| ≤ 1 :=
  abs_real_inner_div_norm_mul_norm_le_one x y

/-- Because of Cauchy–Schwarz, `arccos` of the normalized inner product returns it under `cos`:
the angle is a genuine angle. -/
theorem cos_angle_of_cauchySchwarz (x y : V) :
    Real.cos (Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))) = ⟪x, y⟫ / (‖x‖ * ‖y‖) := by
  have h := abs_le.mp (cauchySchwarz_ratio x y)
  exact Real.cos_arccos h.1 h.2

/-! ## 2. The straight angle and the triangle are exactly `π` -/

/-- The angle between `x` and `-x` is exactly `π`. -/
theorem angle_self_neg {x : V} (hx : x ≠ 0) : angle x (-x) = π :=
  angle_self_neg_of_nonzero hx

/-- The three angles of every (possibly degenerate) triangle add up to exactly `π`. -/
theorem triangle_angle_sum {p₁ p₂ : V} (p₃ : V) (h : p₂ ≠ p₁) :
    EuclideanGeometry.angle p₁ p₂ p₃ + EuclideanGeometry.angle p₂ p₃ p₁ +
      EuclideanGeometry.angle p₃ p₁ p₂ = π :=
  EuclideanGeometry.angle_add_angle_add_angle_eq_pi p₃ h

/-- The parallelogram law, which characterizes norms coming from an inner product. -/
theorem parallelogram (x y : V) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  parallelogram_law_with_norm ℝ x y

/-! ## 3. Chords and the inscribed polygons of Archimedes -/

/-- A chord between unit vectors at angle `θ` has length `2 sin (θ / 2)`. -/
theorem norm_sub_unit {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - v‖ = 2 * Real.sin (angle u v / 2) := by
  have hcos : ⟪u, v⟫ = Real.cos (angle u v) := by
    rw [cos_angle, hu, hv]; simp
  have hsq : ‖u - v‖ ^ 2 = (2 * Real.sin (angle u v / 2)) ^ 2 := by
    rw [norm_sub_sq_real, hu, hv, hcos]
    have h2 : Real.cos (angle u v) = 1 - 2 * Real.sin (angle u v / 2) ^ 2 := by
      have hc := Real.cos_two_mul (angle u v / 2)
      rw [show 2 * (angle u v / 2) = angle u v by ring] at hc
      linarith [Real.sin_sq_add_cos_sq (angle u v / 2)]
    rw [h2]; ring
  have hs : 0 ≤ Real.sin (angle u v / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [angle_nonneg u v]
    · linarith [angle_le_pi u v, Real.pi_pos]
  exact (pow_left_inj₀ (norm_nonneg _) (by linarith) two_ne_zero).mp hsq

/-- Consecutive vertices of the regular `n`-gon inscribed in the unit circle are at angle
`2π / n`, so each side has length `2 sin (π / n)`. -/
theorem side_regular_polygon {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (n : ℕ)
    (h : angle u v = 2 * π / n) : ‖u - v‖ = 2 * Real.sin (π / n) := by
  rw [norm_sub_unit hu hv, h]; ring_nf

/-- Perimeter of the regular `n`-gon inscribed in the unit circle: `2 n sin (π / n)`. -/
noncomputable def archimedesPerimeter (n : ℕ) : ℝ := 2 * n * Real.sin (π / n)

/-- The inscribed hexagon has perimeter exactly `6`, the same number as the hexagonal norm. -/
theorem archimedesPerimeter_six : archimedesPerimeter 6 = 6 := by
  rw [archimedesPerimeter, show (π / ((6 : ℕ) : ℝ)) = π / 6 by norm_num, Real.sin_pi_div_six]
  norm_num

/-- Every inscribed polygon is strictly shorter than `2π`. -/
theorem archimedesPerimeter_lt {n : ℕ} (hn : 1 ≤ n) : archimedesPerimeter n < 2 * π := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.sin_lt (div_pos Real.pi_pos hn')
  calc archimedesPerimeter n = 2 * n * Real.sin (π / n) := rfl
    _ < 2 * n * (π / n) := by gcongr
    _ = 2 * π := by field_simp

/-- **Archimedes.** The perimeters of the inscribed polygons tend to `2π`: in an inner product
plane the circumference over the diameter is exactly `π`. -/
theorem tendsto_archimedesPerimeter :
    Tendsto archimedesPerimeter atTop (𝓝 (2 * π)) := by
  have h1 : Tendsto (fun n : ℕ => π / n) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat π, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact (div_pos Real.pi_pos hn').ne'
  have h2 := (Real.tendsto_sin_div_nhdsNE_zero.comp h1).const_mul (2 * π)
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  simp only [Function.comp, archimedesPerimeter]
  field_simp

/-- The inscribed hexagon is shorter than the circle: `6 < 2π`, that is `3 < π`. -/
theorem hexagon_lt_circle : archimedesPerimeter 6 < 2 * π := by
  rw [archimedesPerimeter_six]; linarith [Real.pi_gt_three]

end NRS3Golab
