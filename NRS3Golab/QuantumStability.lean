/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib

/-!
# Quantum stability on the Hilbert space `ℂ^d`, and where the spatial dimension enters

1. **`ℂ^d`, every `d`.** Every operator `H` on `ℂ^d` satisfies
   `-(‖H‖ ‖ψ‖²) ≤ Re ⟪ψ, H ψ⟫` (`re_inner_ge_of_Cd`). The proof is Cauchy–Schwarz plus the
   operator norm. In finite dimension the energy is always bounded below: no collapse,
   whatever `d` is.

2. **`x, y, z` from `ℂ²`.** The three Pauli matrices pairwise anticommute (`pauli_anticomm_xy`,
   `pauli_anticomm_yz`, `pauli_anticomm_zx`) and square to `1` (`pauli_sq`). Three
   anticommuting generators on `ℂ²` are the three spatial axes. Maximality (no fourth one in
   `su(2)`) is Physlib PR #1762; the strict `d = 4` of the Dirac matrices is PR #1768.

3. **Continuum, `n` spatial axes.** For `-Δ - k / r^{n-2}` on `L²(ℝⁿ)`, the dilation
   `ψ_λ(x) = λ^{n/2} ψ(λ x)` multiplies the kinetic energy `T` by `λ²` and the potential
   energy `W` by `λ^{n-2}`, so `E(λ) = λ² T - k λ^{n-2} W` (`dilationEnergy`, the scaling is
   taken as the definition). Then
   * `n = 3`: `E(λ) ≥ -(k W)² / (4 T)` (`dilationEnergy_three_ge`);
   * `n = 4`: bounded below iff `k W ≤ T` (`bddBelow_four_iff`), so large coupling collapses;
   * `n ≥ 5`: `E(λ) → -∞` for every `k > 0` (`dilationEnergy_unbounded`): fall to the center.

   Hence among `n ≥ 3` the energy along the dilation orbit is bounded below for every
   coupling exactly when `n = 3` (`bddBelow_all_couplings_iff`). This is the quantum
   counterpart of `NRS3Golab.stable_iff_eq_three`.

## Scope

Part 3 works along the dilation orbit of one state with `T, W > 0`. It proves the collapse
for `n ≥ 5` (and `n = 4`, large `k`) rigorously as soon as one such state exists. For `n = 3`
the bound over all states needs Hardy's inequality, which is not proved here.

## References

* F. R. Tangherlini, Nuovo Cimento 27 (1963) 636–651.
* L. D. Landau, E. M. Lifshitz, *Quantum Mechanics*, §35 (fall to the center).
-/

namespace NRS3Golab

open scoped InnerProductSpace

/-! ## 1. `ℂ^d`: every operator is bounded below -/

/-- **Cauchy–Schwarz bound on `ℂ^d`.** For every `d`, every operator `H` and every `ψ`,
`-(‖H‖ ‖ψ‖²) ≤ Re ⟪ψ, H ψ⟫`. -/
theorem re_inner_ge_of_Cd (d : ℕ) (H : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (ψ : EuclideanSpace ℂ (Fin d)) :
    -(‖H‖ * ‖ψ‖ ^ 2) ≤ RCLike.re ⟪ψ, H ψ⟫_ℂ := by
  have h1 : ‖⟪ψ, H ψ⟫_ℂ‖ ≤ ‖ψ‖ * ‖H ψ‖ := norm_inner_le_norm _ _
  have h2 : ‖H ψ‖ ≤ ‖H‖ * ‖ψ‖ := H.le_opNorm ψ
  have h3 := abs_le.mp ((RCLike.abs_re_le_norm (⟪ψ, H ψ⟫_ℂ)))
  have h4 : ‖ψ‖ * ‖H ψ‖ ≤ ‖ψ‖ * (‖H‖ * ‖ψ‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg ψ)
  nlinarith [h3.1]

/-- Every linear map on `ℂ^d` is continuous, so the bound holds for every linear `H`. -/
theorem re_inner_ge_of_Cd_linear (d : ℕ)
    (H : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) :
    ∃ C : ℝ, ∀ ψ, -(C * ‖ψ‖ ^ 2) ≤ RCLike.re ⟪ψ, H ψ⟫_ℂ :=
  ⟨‖LinearMap.toContinuousLinearMap H‖, re_inner_ge_of_Cd d (LinearMap.toContinuousLinearMap H)⟩

/-! ## 2. `x, y, z` from `ℂ²`: the Pauli matrices -/

/-- `σ_x`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- `σ_y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- `σ_z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauli_anticomm_xy : pauliX * pauliY + pauliY * pauliX = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY]

theorem pauli_anticomm_yz : pauliY * pauliZ + pauliZ * pauliY = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY, pauliZ]

theorem pauli_anticomm_zx : pauliZ * pauliX + pauliX * pauliZ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ]

theorem pauli_sq : pauliX * pauliX = 1 ∧ pauliY * pauliY = 1 ∧ pauliZ * pauliZ = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 3. Continuum `L²(ℝⁿ)`: the dilation energy -/

/-- Energy of the dilated state `ψ_λ` for `-Δ - k / r^{n-2}` in `n` spatial axes, with
kinetic energy `T` and potential energy `W` of `ψ`: `λ² T - k λ^{n-2} W`. -/
def dilationEnergy (n : ℕ) (k T W lam : ℝ) : ℝ := lam ^ 2 * T - k * lam ^ (n - 2) * W

/-- `n = 3`: the dilation energy is bounded below by `-(k W)² / (4 T)`. -/
theorem dilationEnergy_three_ge {k T W : ℝ} (hT : 0 < T) (lam : ℝ) :
    -((k * W) ^ 2 / (4 * T)) ≤ dilationEnergy 3 k T W lam := by
  unfold dilationEnergy
  rw [show (3 : ℕ) - 2 = 1 from rfl, pow_one, neg_le, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * T * lam - k * W)]

/-- `n = 4`: the dilation energy is bounded below iff `k W ≤ T`. -/
theorem bddBelow_four_iff {k T W : ℝ} :
    (∃ B : ℝ, ∀ lam : ℝ, 0 < lam → B ≤ dilationEnergy 4 k T W lam) ↔ k * W ≤ T := by
  have hE : ∀ lam, dilationEnergy 4 k T W lam = (T - k * W) * lam ^ 2 := by
    intro lam; unfold dilationEnergy; rw [show (4 : ℕ) - 2 = 2 from rfl]; ring
  constructor
  · rintro ⟨B, hB⟩
    by_contra h
    have hc : 0 < k * W - T := by linarith [not_le.mp h]
    set lam := max 1 ((|B| + 1) / (k * W - T)) with hlam
    have hl1 : 1 ≤ lam := le_max_left _ _
    have hl2 : (|B| + 1) / (k * W - T) ≤ lam := le_max_right _ _
    have hl3 : |B| + 1 ≤ (k * W - T) * lam := by
      rw [div_le_iff₀ hc] at hl2; linarith
    have := hB lam (by linarith)
    rw [hE] at this
    nlinarith [le_abs_self B, neg_abs_le B]
  · intro h
    exact ⟨0, fun lam _ => by rw [hE]; exact mul_nonneg (by linarith) (sq_nonneg _)⟩

/-- `n ≥ 5`: for every coupling `k > 0` the dilation energy is unbounded below. -/
theorem dilationEnergy_unbounded {n : ℕ} (hn : 5 ≤ n) {k T W : ℝ} (hk : 0 < k) (hW : 0 < W)
    (M : ℝ) : ∃ lam : ℝ, 0 < lam ∧ dilationEnergy n k T W lam < M := by
  have hc : 0 < k * W := mul_pos hk hW
  set lam := max 1 ((|T| + |M| + 1) / (k * W)) with hlam
  have hl1 : 1 ≤ lam := le_max_left _ _
  have hl2 : |T| + |M| + 1 ≤ k * W * lam := by
    have := le_max_right 1 ((|T| + |M| + 1) / (k * W))
    rw [← hlam, div_le_iff₀ hc] at this; linarith
  have hpow : lam ^ 3 ≤ lam ^ (n - 2) := pow_le_pow_right₀ hl1 (by omega)
  have hl3 : lam * lam ^ 2 = lam ^ 3 := by ring
  refine ⟨lam, by linarith, ?_⟩
  unfold dilationEnergy
  have hsq : 1 ≤ lam ^ 2 := one_le_pow₀ hl1
  have hkw : k * lam ^ 3 * W ≤ k * lam ^ (n - 2) * W := by
    have := mul_le_mul_of_nonneg_left hpow hk.le
    exact mul_le_mul_of_nonneg_right this hW.le
  nlinarith [le_abs_self T, le_abs_self M, neg_abs_le M, abs_nonneg M]

/-- Bounded below for every coupling `k > 0`, along the dilation orbit of a state with
`T, W > 0`. -/
def BddBelowAllCouplings (n : ℕ) (T W : ℝ) : Prop :=
  ∀ k : ℝ, 0 < k → ∃ B : ℝ, ∀ lam : ℝ, 0 < lam → B ≤ dilationEnergy n k T W lam

/-- **Quantum Ehrenfest.** Among `n ≥ 3` spatial axes, the dilation energy is bounded below
for every coupling exactly when `n = 3`. -/
theorem bddBelow_all_couplings_iff {n : ℕ} (hn : 3 ≤ n) {T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    BddBelowAllCouplings n T W ↔ n = 3 := by
  constructor
  · intro h
    by_contra hne
    rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
    · obtain ⟨B, hB⟩ := h (2 * T / W) (by positivity)
      have := bddBelow_four_iff.mp ⟨B, hB⟩
      rw [div_mul_cancel₀ _ hW.ne'] at this
      linarith
    · obtain ⟨B, hB⟩ := h 1 one_pos
      obtain ⟨lam, hl, hE⟩ := dilationEnergy_unbounded h5 one_pos hW B
      linarith [hB lam hl]
  · rintro rfl k _
    exact ⟨_, fun lam _ => dilationEnergy_three_ge hT lam⟩

end NRS3Golab
