/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib

/-!
# Ehrenfest: stable circular orbits exist exactly when the spatial dimension is `d < 4`

In `d` spatial dimensions Gauss's law spreads the flux of a point mass over a sphere `S^{d-1}`
of area `∝ r^{d-1}`, so the attractive force is `k / r^{d-1}`. For a particle of unit mass and
angular momentum `L` the effective radial force is

`G(r) = L² / r³ - k / r^{d-1}`  (`radialForce`),

centrifugal minus gravitational. A circular orbit of radius `r₀` is an equilibrium
`G(r₀) = 0`, which happens exactly for `L² = k r₀^{4-d}` (`radialForce_eq_zero_iff`); such an
`L` exists for every `r₀ > 0` (`exists_circular`). The orbit is stable when a small radial
displacement is pushed back, `G'(r₀) < 0`. The computation gives

`G'(r₀) = (d - 4) k r₀^{-d}`  (`deriv_radialForce_circular`),

so (`stable_iff`) the orbit is stable iff `d < 4`; for `d = 4` it is neutral
(`deriv_radialForce_circular_four`) and for `d ≥ 5` it is unstable.

Among the dimensions `d ≥ 3`, in which the potential vanishes at infinity so that bodies can
also escape, `d = 3` is the only one with stable orbits (`stable_iff_eq_three`): spacetime
dimension `d + 1 = 4` (`stable_iff_spacetime_four`).

## Scope

This is Newtonian mechanics with the force law fixed by Gauss's law in `d` dimensions
(Ehrenfest, 1917). General relativity and the quantum version (hydrogen in `d` dimensions,
Tangherlini 1963) are not treated here.

## References

* P. Ehrenfest, *In what way does it become manifest in the fundamental laws of physics that
  space has three dimensions?*, Proc. Amsterdam Acad. 20 (1917) 200–209.
* F. R. Tangherlini, *Schwarzschild field in n dimensions and the dimensionality of space
  problem*, Nuovo Cimento 27 (1963) 636–651.
-/

namespace NRS3Golab

/-- Effective radial force on a unit mass with angular momentum `L` around a point mass of
strength `k`, in `d` spatial dimensions: `L² / r³ - k / r^{d-1}`. -/
noncomputable def radialForce (L k : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  L ^ 2 * r ^ (-3 : ℤ) - k * r ^ (1 - (d : ℤ))

lemma hasDerivAt_radialForce (L k : ℝ) (d : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (radialForce L k d)
      (L ^ 2 * (((-3 : ℤ) : ℝ) * r ^ ((-3 : ℤ) - 1)) -
        k * (((1 - (d : ℤ) : ℤ) : ℝ) * r ^ ((1 - (d : ℤ)) - 1))) r :=
  ((hasDerivAt_zpow (-3) r (Or.inl hr)).const_mul (L ^ 2)).sub
    ((hasDerivAt_zpow (1 - (d : ℤ)) r (Or.inl hr)).const_mul k)

/-- A circular orbit of radius `r₀` is an equilibrium of the radial force exactly when
`L² = k r₀^{4-d}`. -/
theorem radialForce_eq_zero_iff (L k : ℝ) (d : ℕ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    radialForce L k d r₀ = 0 ↔ L ^ 2 = k * r₀ ^ (4 - (d : ℤ)) := by
  have h3 : (0 : ℝ) < r₀ ^ (-3 : ℤ) := zpow_pos hr₀ _
  have hsplit : r₀ ^ (1 - (d : ℤ)) = r₀ ^ (4 - (d : ℤ)) * r₀ ^ (-3 : ℤ) := by
    rw [← zpow_add₀ hr₀.ne']; congr 1; ring
  rw [radialForce, hsplit, sub_eq_zero, ← mul_assoc]
  exact ⟨fun h => mul_right_cancel₀ h3.ne' h, fun h => by rw [h]⟩

/-- For every radius `r₀ > 0` and attractive strength `k > 0` there is an angular momentum
making the circular orbit of radius `r₀` an equilibrium. -/
theorem exists_circular {k : ℝ} (hk : 0 < k) (d : ℕ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ L : ℝ, radialForce L k d r₀ = 0 := by
  refine ⟨Real.sqrt (k * r₀ ^ (4 - (d : ℤ))), (radialForce_eq_zero_iff _ _ _ hr₀).mpr ?_⟩
  exact Real.sq_sqrt (mul_nonneg hk.le (zpow_pos hr₀ _).le)

/-- **The restoring rate at a circular orbit**: `G'(r₀) = (d - 4) k r₀^{-d}`. -/
theorem deriv_radialForce_circular {L k : ℝ} (d : ℕ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hcirc : L ^ 2 = k * r₀ ^ (4 - (d : ℤ))) :
    deriv (radialForce L k d) r₀ = ((d : ℝ) - 4) * k * r₀ ^ (-(d : ℤ)) := by
  rw [(hasDerivAt_radialForce L k d hr₀.ne').deriv, hcirc]
  have e1 : r₀ ^ (4 - (d : ℤ)) * r₀ ^ (-4 : ℤ) = r₀ ^ (-(d : ℤ)) := by
    rw [← zpow_add₀ hr₀.ne']; congr 1; ring
  have e2 : r₀ ^ ((1 - (d : ℤ)) - 1) = r₀ ^ (-(d : ℤ)) := by congr 1; ring
  rw [e2]
  push_cast
  linear_combination (-3 * k) * e1

/-- In `d = 4` the circular orbit is neutral: the restoring rate vanishes. -/
theorem deriv_radialForce_circular_four {L k : ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hcirc : L ^ 2 = k * r₀ ^ (4 - ((4 : ℕ) : ℤ))) :
    deriv (radialForce L k 4) r₀ = 0 := by
  rw [deriv_radialForce_circular 4 hr₀ hcirc]; norm_num

/-- **Ehrenfest.** A circular orbit under an attractive force (`k > 0`) is stable,
`G'(r₀) < 0`, if and only if the spatial dimension is `d < 4`. -/
theorem stable_iff {L k : ℝ} (hk : 0 < k) (d : ℕ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hcirc : L ^ 2 = k * r₀ ^ (4 - (d : ℤ))) :
    deriv (radialForce L k d) r₀ < 0 ↔ d < 4 := by
  rw [deriv_radialForce_circular d hr₀ hcirc]
  have hpos : 0 < k * r₀ ^ (-(d : ℤ)) := mul_pos hk (zpow_pos hr₀ _)
  rw [mul_assoc, mul_neg_iff]
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, -⟩)
    · exact absurd hpos (not_lt.mpr h'.le)
    · exact_mod_cast (sub_neg.mp h)
  · intro hd
    exact Or.inr ⟨sub_neg.mpr (by exact_mod_cast hd), hpos⟩

/-- Every circular orbit is stable, for all strengths, radii and angular momenta. -/
def AllCircularOrbitsStable (d : ℕ) : Prop :=
  ∀ L k r₀ : ℝ, 0 < k → 0 < r₀ → radialForce L k d r₀ = 0 → deriv (radialForce L k d) r₀ < 0

/-- **`d = 3` is the only spatial dimension `d ≥ 3` with stable orbits.** -/
theorem stable_iff_eq_three {d : ℕ} (hd : 3 ≤ d) : AllCircularOrbitsStable d ↔ d = 3 := by
  constructor
  · intro h
    obtain ⟨L, hL⟩ := exists_circular one_pos d one_pos
    have := (stable_iff one_pos d one_pos
      ((radialForce_eq_zero_iff L 1 d one_pos).mp hL)).mp (h L 1 1 one_pos one_pos hL)
    omega
  · rintro rfl L k r₀ hk hr₀ h0
    exact (stable_iff hk 3 hr₀ ((radialForce_eq_zero_iff L k 3 hr₀).mp h0)).mpr (by norm_num)

/-- **Spacetime dimension four.** Among spatial dimensions `d ≥ 3`, all circular orbits are
stable exactly when the spacetime dimension `d + 1` is `4`. -/
theorem stable_iff_spacetime_four {d : ℕ} (hd : 3 ≤ d) :
    AllCircularOrbitsStable d ↔ d + 1 = 4 := by
  rw [stable_iff_eq_three hd]; omega

end NRS3Golab
