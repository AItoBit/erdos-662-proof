module

public import Research.Basic

/-!
# Exact small shells of the unit triangular lattice

Integer coordinates `(a,b)` represent
`a (1,0) + b (1/2, sqrt 3 / 2)`.  Their squared norm is
`a^2 + a*b + b^2`.
-/

@[expose] public section

namespace Research

/-- The integral quadratic form giving squared distance in the unit triangular lattice. -/
def triNormSq (p : ℤ × ℤ) : ℤ :=
  p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2

/-- The seven integer coordinates from `-3` through `3`, written explicitly
so the shell census has executable data rather than a classical interval. -/
def intWindow3 : Finset ℤ := {(-3 : ℤ), -2, -1, 0, 1, 2, 3}

/-- Coordinate vectors in the `[-3,3]^2` window with norm squared at most `s`. -/
def triCoordsWithin (s : ℤ) : Finset (ℤ × ℤ) :=
  ((intWindow3.product intWindow3).filter
    (fun p => triNormSq p ≤ s)).erase (0, 0)

/-- Every coordinate vector of triangular norm squared at most nine lies in the
`[-3,3]^2` enumeration window. -/
theorem tri_norm_le_nine_bounds (a b : ℤ)
    (h : a ^ 2 + a * b + b ^ 2 ≤ 9) :
    -3 ≤ a ∧ a ≤ 3 ∧ -3 ≤ b ∧ b ≤ 3 := by
  have ha2 : 3 * a ^ 2 ≤ 36 := by
    nlinarith [sq_nonneg (a + 2 * b)]
  have hb2 : 3 * b ^ 2 ≤ 36 := by
    nlinarith [sq_nonneg (2 * a + b)]
  constructor
  · by_contra hn
    have ha : a ≤ -4 := by omega
    nlinarith [sq_nonneg (a + 4)]
  constructor
  · by_contra hn
    have ha : 4 ≤ a := by omega
    nlinarith [sq_nonneg (a - 4)]
  constructor
  · by_contra hn
    have hb : b ≤ -4 := by omega
    nlinarith [sq_nonneg (b + 4)]
  · by_contra hn
    have hb : 4 ≤ b := by omega
    nlinarith [sq_nonneg (b - 4)]

/-- Membership characterization of the executable coordinate window. -/
theorem mem_intWindow3_iff (z : ℤ) :
    z ∈ intWindow3 ↔ -3 ≤ z ∧ z ≤ 3 := by
  simp [intWindow3]
  omega

/-- Every census with squared-radius at most nine is complete, not merely a
count inside an arbitrarily chosen finite window. -/
theorem mem_triCoordsWithin_iff_of_le_nine (s : ℤ) (hs : s ≤ 9)
    (p : ℤ × ℤ) :
    p ∈ triCoordsWithin s ↔ p ≠ (0, 0) ∧ triNormSq p ≤ s := by
  rcases p with ⟨a, b⟩
  constructor
  · simp only [triCoordsWithin, Finset.mem_erase, Finset.mem_filter]
    rintro ⟨hne, _, hq⟩
    exact ⟨hne, hq⟩
  · rintro ⟨hne, hq⟩
    have hq9 : a ^ 2 + a * b + b ^ 2 ≤ 9 := le_trans hq hs
    have bounds := tri_norm_le_nine_bounds a b hq9
    rcases bounds with ⟨hal, hau, hbl, hbu⟩
    simp only [triCoordsWithin, Finset.mem_erase, Finset.mem_filter]
    exact ⟨hne, Finset.mem_product.mpr
      ⟨(mem_intWindow3_iff a).2 ⟨hal, hau⟩,
       (mem_intWindow3_iff b).2 ⟨hbl, hbu⟩⟩, hq⟩

/-- The radius-three instance of census completeness. -/
theorem mem_triCoordsWithin_nine_iff (p : ℤ × ℤ) :
    p ∈ triCoordsWithin 9 ↔ p ≠ (0, 0) ∧ triNormSq p ≤ 9 := by
  rcases p with ⟨a, b⟩
  constructor
  · simp only [triCoordsWithin, Finset.mem_erase, Finset.mem_filter]
    rintro ⟨hne, _, hq⟩
    exact ⟨hne, hq⟩
  · rintro ⟨hne, hq⟩
    have bounds := tri_norm_le_nine_bounds a b hq
    rcases bounds with ⟨hal, hau, hbl, hbu⟩
    simp only [triCoordsWithin, Finset.mem_erase, Finset.mem_filter]
    exact ⟨hne, Finset.mem_product.mpr
      ⟨(mem_intWindow3_iff a).2 ⟨hal, hau⟩,
       (mem_intWindow3_iff b).2 ⟨hbl, hbu⟩⟩, hq⟩

/-- Exact enumeration of the first radius of the triangular lattice. -/
theorem triCoordsWithin_one_card : (triCoordsWithin 1).card = 6 := by
  decide

/-- There is no triangular-lattice shell at squared norm two. -/
theorem triCoordsWithin_two_card : (triCoordsWithin 2).card = 6 := by
  decide

/-- Exact enumeration through the radius `sqrt 3`. -/
theorem triCoordsWithin_three_card : (triCoordsWithin 3).card = 12 := by
  decide

/-- Coordinate census with a real squared-distance threshold below three. -/
noncomputable def triCoordsWithinReal (s : ℝ) : Finset (ℤ × ℤ) :=
  ((intWindow3.product intWindow3).filter
    (fun p => (triNormSq p : ℝ) ≤ s)).erase (0, 0)

/-- Between squared thresholds two (inclusive) and three (exclusive), the real
threshold census equals the executable squared-threshold-two census. -/
theorem triCoordsWithinReal_eq_two (s : ℝ) (h2 : 2 ≤ s) (h3 : s < 3) :
    triCoordsWithinReal s = triCoordsWithin 2 := by
  ext p
  simp only [triCoordsWithinReal, triCoordsWithin, Finset.mem_erase,
    Finset.mem_filter]
  constructor
  · rintro ⟨hne, hwin, hq⟩
    refine ⟨hne, hwin, ?_⟩
    have hqR : (triNormSq p : ℝ) < 3 := lt_of_le_of_lt hq h3
    have hqZ : triNormSq p < 3 := by exact_mod_cast hqR
    omega
  · rintro ⟨hne, hwin, hq⟩
    refine ⟨hne, hwin, ?_⟩
    have hqR : (triNormSq p : ℝ) ≤ 2 := by exact_mod_cast hq
    exact hqR.trans h2

/-- Consequently the natural triangular-lattice ball has six nonzero points
throughout the squared-threshold interval `[2,3)`. -/
theorem triCoordsWithinReal_card_of_two_le_lt_three (s : ℝ)
    (h2 : 2 ≤ s) (h3 : s < 3) : (triCoordsWithinReal s).card = 6 := by
  rw [triCoordsWithinReal_eq_two s h2 h3, triCoordsWithin_two_card]

/-- Exact enumeration through radius three.  The printed value 18 is not the
natural triangular-lattice ball count; the correct count is 36. -/
theorem triCoordsWithin_nine_card : (triCoordsWithin 9).card = 36 := by
  decide

/-- The standard real-plane realization of triangular-lattice coordinates. -/
noncomputable def triPoint (p : ℤ × ℤ) : ℝ × ℝ :=
  ((p.1 : ℝ) + (p.2 : ℝ) / 2, Real.sqrt 3 * (p.2 : ℝ) / 2)

/-- The coordinate quadratic form really is squared Euclidean distance from the origin. -/
theorem sqDist_triPoint_zero (p : ℤ × ℤ) :
    sqDist (triPoint p) (0, 0) = (triNormSq p : ℝ) := by
  rcases p with ⟨a, b⟩
  simp only [triPoint, sqDist, triNormSq, sub_zero]
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
  rw [div_pow, mul_pow, hs]
  norm_num
  ring

/-- Triangular-lattice integer coordinates represent distinct planar points. -/
theorem triPoint_injective : Function.Injective triPoint := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hy := congrArg Prod.snd h
  simp only [triPoint] at hy
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hbdR : (b : ℝ) = (d : ℝ) := by nlinarith
  have hbd : b = d := by exact_mod_cast hbdR
  subst d
  have hx := congrArg Prod.fst h
  simp only [triPoint] at hx
  have hacR : (a : ℝ) = (c : ℝ) := by nlinarith
  have hac : a = c := by exact_mod_cast hacR
  subst c
  rfl

end Research
