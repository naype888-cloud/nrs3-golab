/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib

/-!
# The two extremal cases of Gołąb's theorem: the hexagon (`π = 3`) and the square (`π = 4`)

Gołąb's theorem (S. Gołąb, 1932) says that in every normed plane the unit circle, measured
with the norm itself, has perimeter between `6` and `8`. Writing `π_N` for half of that
perimeter (the ratio circumference / diameter, since every diameter of the unit ball is `2`),
`3 ≤ π_N ≤ 4`. The lower value `3` is attained by the affinely regular hexagon, the upper
value `4` by the parallelogram.

This file proves the two equality cases on `ℝ × ℝ`.

* `hexNorm v = max (max |v.1| |v.2|) |v.1 - v.2|`. Its unit ball is the hexagon with vertices
  `(1,0), (1,1), (0,1), (-1,0), (-1,-1), (0,-1)`, an affine image of the regular hexagon.
* `sqNorm v = max |v.1| |v.2|`. Its unit ball is the square with vertices `(±1, ±1)`.

## Main results

* `hexNorm_add_le`, `hexNorm_smul`, `hexNorm_eq_zero_iff` : `hexNorm` is a norm.
* `hexNorm_vertex` : the six vertices lie on the unit circle.
* `hexNorm_edge` : every point of every edge lies on the unit circle.
* `hexNorm_edge_vector` : every edge has length `1` measured in `hexNorm`; the reason is
  `v (k+1) - v k = v (k+2)`, `hexVertex_edge_eq`.
* `hexPerimeter_eq_six`, `hexPi_eq_three` : perimeter `6`, `π_hex = 3`.
* `hexNorm_sub_le_two`, `hexNorm_diameter` : every diameter is at most `2`, and `2` is attained.
* `hexNorm_not_parallelogram` : `hexNorm` violates the parallelogram law, hence it does not
  come from an inner product (Jordan–von Neumann).
* `sqPerimeter_eq_eight`, `sqPi_eq_four` : the square gives `π_sq = 4`.

## Scope

The perimeter of the unit circle is computed as the sum of the norms of the edges of the
polygon. For a straight segment the length in a normed space is the norm of its endpoint
difference (`segment_length`, homogeneity telescopes along any partition), so this is the
length of the curve. The general inequality `6 ≤ perimeter ≤ 8` for every norm is not
proved here.

## References

* S. Gołąb, *Quelques problèmes métriques de la géometrie de Minkowski*,
  Trav. Acad. Mines Cracovie 6 (1932).
* J. J. Schäffer, *Geometry of Spheres in Normed Spaces*, Marcel Dekker, 1976.
-/

namespace NRS3Golab

/-! ## A. The hexagonal norm -/

/-- The hexagonal norm on `ℝ × ℝ`: `max (|x|, |y|, |x - y|)`. -/
noncomputable def hexNorm (v : ℝ × ℝ) : ℝ := max (max |v.1| |v.2|) |v.1 - v.2|

lemma hexNorm_nonneg (v : ℝ × ℝ) : 0 ≤ hexNorm v :=
  le_max_of_le_left (le_max_of_le_left (abs_nonneg _))

lemma abs_fst_le_hexNorm (v : ℝ × ℝ) : |v.1| ≤ hexNorm v :=
  le_max_of_le_left (le_max_left _ _)

lemma abs_snd_le_hexNorm (v : ℝ × ℝ) : |v.2| ≤ hexNorm v :=
  le_max_of_le_left (le_max_right _ _)

lemma abs_sub_le_hexNorm (v : ℝ × ℝ) : |v.1 - v.2| ≤ hexNorm v :=
  le_max_right _ _

/-- Triangle inequality for `hexNorm`. -/
theorem hexNorm_add_le (u v : ℝ × ℝ) : hexNorm (u + v) ≤ hexNorm u + hexNorm v := by
  refine max_le (max_le ?_ ?_) ?_
  · calc |(u + v).1| = |u.1 + v.1| := rfl
      _ ≤ |u.1| + |v.1| := abs_add_le _ _
      _ ≤ _ := add_le_add (abs_fst_le_hexNorm u) (abs_fst_le_hexNorm v)
  · calc |(u + v).2| = |u.2 + v.2| := rfl
      _ ≤ |u.2| + |v.2| := abs_add_le _ _
      _ ≤ _ := add_le_add (abs_snd_le_hexNorm u) (abs_snd_le_hexNorm v)
  · calc |(u + v).1 - (u + v).2| = |(u.1 - u.2) + (v.1 - v.2)| := by
          simp only [Prod.fst_add, Prod.snd_add]; ring_nf
      _ ≤ |u.1 - u.2| + |v.1 - v.2| := abs_add_le _ _
      _ ≤ _ := add_le_add (abs_sub_le_hexNorm u) (abs_sub_le_hexNorm v)

/-- Absolute homogeneity of `hexNorm`. -/
theorem hexNorm_smul (c : ℝ) (v : ℝ × ℝ) : hexNorm (c • v) = |c| * hexNorm v := by
  unfold hexNorm
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [← mul_sub, abs_mul, abs_mul, abs_mul, mul_max_of_nonneg _ _ (abs_nonneg c),
    mul_max_of_nonneg _ _ (abs_nonneg c)]

/-- `hexNorm` is definite. -/
theorem hexNorm_eq_zero_iff (v : ℝ × ℝ) : hexNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 : |v.1| ≤ 0 := h ▸ abs_fst_le_hexNorm v
    have h2 : |v.2| ≤ 0 := h ▸ abs_snd_le_hexNorm v
    exact Prod.ext (abs_nonpos_iff.mp h1) (abs_nonpos_iff.mp h2)
  · rintro rfl
    simp [hexNorm]

lemma hexNorm_neg (v : ℝ × ℝ) : hexNorm (-v) = hexNorm v := by
  have := hexNorm_smul (-1) v
  simpa using this

/-! ## B. The unit circle of `hexNorm` is a hexagon -/

/-- The six vertices of the unit ball of `hexNorm`, in counterclockwise order. -/
def hexVertex : Fin 6 → ℝ × ℝ :=
  ![(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)]

/-- Every vertex lies on the unit circle. -/
theorem hexNorm_vertex (k : Fin 6) : hexNorm (hexVertex k) = 1 := by
  fin_cases k <;> norm_num [hexNorm, hexVertex]

/-- The hexagon identity: each edge vector is again a vertex, `v (k+1) - v k = v (k+2)`. -/
theorem hexVertex_edge_eq (k : Fin 6) : hexVertex (k + 1) - hexVertex k = hexVertex (k + 2) := by
  fin_cases k <;> simp [hexVertex]

/-- Every edge has length `1` measured in `hexNorm`. -/
theorem hexNorm_edge_vector (k : Fin 6) : hexNorm (hexVertex (k + 1) - hexVertex k) = 1 := by
  rw [hexVertex_edge_eq, hexNorm_vertex]

private lemma max3_eq_one {a b c : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (h : a = 1 ∨ b = 1 ∨ c = 1) : max (max a b) c = 1 := by
  apply le_antisymm (max_le (max_le ha hb) hc)
  rcases h with h | h | h
  · exact h ▸ le_max_of_le_left (le_max_left _ _)
  · exact h ▸ le_max_of_le_left (le_max_right _ _)
  · exact h ▸ le_max_right _ _

/-- Every point of every edge lies on the unit circle: the unit circle contains the hexagon. -/
theorem hexNorm_edge (k : Fin 6) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    hexNorm (hexVertex k + t • (hexVertex (k + 1) - hexVertex k)) = 1 := by
  rw [hexVertex_edge_eq]
  have a1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have a2 : |1 - t| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have a3 : |1 + -t| ≤ 1 := by rw [← sub_eq_add_neg]; exact a2
  have a4 : |-1 + t| ≤ 1 := by rw [show -1 + t = -(1 - t) by ring, abs_neg]; exact a2
  fin_cases k <;> simp [hexNorm, hexVertex] <;>
    first
    | exact ⟨a1, a3⟩
    | exact ⟨a1, a4⟩
    | (apply max3_eq_one <;> first | assumption | norm_num)

private lemma max3_eq_one_cases {a b c : ℝ} (h : max (max a b) c = 1) :
    a = 1 ∨ b = 1 ∨ c = 1 := by
  rcases max_choice (max a b) c with h' | h'
  · rw [h'] at h
    rcases max_choice a b with h'' | h''
    · exact Or.inl (h'' ▸ h)
    · exact Or.inr (Or.inl (h'' ▸ h))
  · exact Or.inr (Or.inr (h' ▸ h))

/-- Conversely, every point of the unit circle lies on one of the six edges: the unit circle
of `hexNorm` is exactly the hexagon. -/
theorem exists_edge_of_hexNorm_eq_one {v : ℝ × ℝ} (hv : hexNorm v = 1) :
    ∃ k : Fin 6, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      v = hexVertex k + t • (hexVertex (k + 1) - hexVertex k) := by
  obtain ⟨x, y⟩ := v
  have hx : |x| ≤ 1 := hv ▸ abs_fst_le_hexNorm (x, y)
  have hy : |y| ≤ 1 := hv ▸ abs_snd_le_hexNorm (x, y)
  have hxy : |x - y| ≤ 1 := hv ▸ abs_sub_le_hexNorm (x, y)
  rw [abs_le] at hx hy hxy
  rcases max3_eq_one_cases hv with h | h | h <;>
    rcases (abs_eq (zero_le_one' ℝ)).mp h with h' | h' <;> simp only at h'
  · exact ⟨0, y, by linarith, by linarith, by simp [hexVertex, h']⟩
  · exact ⟨3, -y, by linarith, by linarith, by simp [hexVertex, h']⟩
  · exact ⟨1, 1 - x, by linarith, by linarith, by simp [hexVertex, h']⟩
  · exact ⟨4, x + 1, by linarith, by linarith, by
      ext <;> simp [hexVertex, h']⟩
  · exact ⟨5, x, by linarith, by linarith, by
      ext <;> simp [hexVertex]; linarith⟩
  · exact ⟨2, -x, by linarith, by linarith, by
      ext <;> simp [hexVertex]; linarith⟩

/-- The length of a straight segment from `p` to `p + w` along any partition
`0 = s 0 ≤ s 1 ≤ … ≤ s n = 1` is `‖w‖`: homogeneity telescopes. -/
theorem segment_length (w : ℝ × ℝ) (n : ℕ) (s : ℕ → ℝ) (hs : Monotone s)
    (h0 : s 0 = 0) (h1 : s n = 1) :
    ∑ i ∈ Finset.range n, hexNorm ((s (i + 1) - s i) • w) = hexNorm w := by
  have hterm : ∀ i, hexNorm ((s (i + 1) - s i) • w) = (s (i + 1) - s i) * hexNorm w := by
    intro i
    rw [hexNorm_smul, abs_of_nonneg (sub_nonneg.mpr (hs (Nat.le_succ i)))]
  simp only [hterm, ← Finset.sum_mul, Finset.sum_range_sub (f := s), h0, h1]
  ring

/-! ## C. Perimeter `6`, diameter `2`, `π_hex = 3` -/

/-- Perimeter of the unit circle of `hexNorm`, measured with `hexNorm`. -/
noncomputable def hexPerimeter : ℝ := ∑ k : Fin 6, hexNorm (hexVertex (k + 1) - hexVertex k)

/-- **Gołąb, equality case `6`.** -/
theorem hexPerimeter_eq_six : hexPerimeter = 6 := by
  simp only [hexPerimeter, hexNorm_edge_vector, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- Every two points of the unit ball are at distance at most `2`. -/
theorem hexNorm_sub_le_two {u v : ℝ × ℝ} (hu : hexNorm u ≤ 1) (hv : hexNorm v ≤ 1) :
    hexNorm (u - v) ≤ 2 := by
  have := hexNorm_add_le u (-v)
  rw [hexNorm_neg, ← sub_eq_add_neg] at this
  linarith

/-- The diameter `2` is attained by opposite vertices. -/
theorem hexNorm_diameter : hexNorm (hexVertex 0 - hexVertex 3) = 2 := by
  norm_num [hexNorm, hexVertex]

/-- `π` of the hexagonal plane: circumference over diameter. -/
noncomputable def hexPi : ℝ := hexPerimeter / 2

/-- **`π_hex = 3`.** -/
theorem hexPi_eq_three : hexPi = 3 := by
  rw [hexPi, hexPerimeter_eq_six]; norm_num

/-- `hexNorm` violates the parallelogram law, so it does not come from an inner product. -/
theorem hexNorm_not_parallelogram :
    hexNorm ((1, 0) + (0, 1)) ^ 2 + hexNorm ((1, 0) - (0, 1)) ^ 2 ≠
      2 * (hexNorm (1, 0) ^ 2 + hexNorm (0, 1) ^ 2) := by
  norm_num [hexNorm]

/-! ## D. The square norm: `π_sq = 4` -/

/-- The square (max) norm on `ℝ × ℝ`. -/
noncomputable def sqNorm (v : ℝ × ℝ) : ℝ := max |v.1| |v.2|

/-- The four vertices of the unit ball of `sqNorm`. -/
def sqVertex : Fin 4 → ℝ × ℝ := ![(1, 1), (-1, 1), (-1, -1), (1, -1)]

theorem sqNorm_vertex (k : Fin 4) : sqNorm (sqVertex k) = 1 := by
  fin_cases k <;> norm_num [sqNorm, sqVertex]

/-- Perimeter of the unit circle of `sqNorm`, measured with `sqNorm`. -/
noncomputable def sqPerimeter : ℝ := ∑ k : Fin 4, sqNorm (sqVertex (k + 1) - sqVertex k)

/-- **Gołąb, equality case `8`.** -/
theorem sqPerimeter_eq_eight : sqPerimeter = 8 := by
  simp [sqPerimeter, Fin.sum_univ_four, sqNorm, sqVertex]
  norm_num

/-- **`π_sq = 4`.** -/
theorem sqPi_eq_four : sqPerimeter / 2 = 4 := by
  rw [sqPerimeter_eq_eight]; norm_num

/-- The two extremal values of Gołąb's theorem are attained: `π_hex = 3 < π < 4 = π_sq`. -/
theorem golab_extremes : hexPi = 3 ∧ sqPerimeter / 2 = 4 ∧ hexPi < Real.pi ∧
    Real.pi < sqPerimeter / 2 :=
  ⟨hexPi_eq_three, sqPi_eq_four, hexPi_eq_three ▸ Real.pi_gt_three,
    sqPi_eq_four ▸ Real.pi_lt_four⟩

end NRS3Golab
