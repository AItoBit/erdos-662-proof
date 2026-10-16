module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Prod
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The global threshold formulation of Erdős Problem 662

Source: Erdős Problems, Problem 662, https://www.erdosproblems.com/662.
The printed question omits the factor given by the number of points in its
global pair-count comparison. Its example $f(3)=18$ also disagrees with the
closed Euclidean threshold count, for which $f(3)=36$; the count $18$ occurs
at radius $2$. This target uses the chosen corrected global formulation:
the directed close-pair count is at most the number of points times the
triangular-lattice neighbour count, once the configuration is sufficiently
large for the chosen radius. This is an explicit reconstruction of the
ambiguous printed question.
-/

@[expose] public section

namespace Erdos662

/-- Euclidean distance in the real plane. -/
noncomputable def euclideanDistance (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)

/-- The number of nonzero unit triangular-lattice vectors of length at most `t`.
The lattice basis is $(1,0)$ and $(1/2,\sqrt{3}/2)$, so the squared length of
the vector with integer coordinates $(a,b)$ is $a^2+ab+b^2$. -/
noncomputable def triangularNeighborCount (t : ℝ) : ℕ :=
  Nat.card {d : ℤ × ℤ // d ≠ (0, 0) ∧
    (d.1 : ℝ) ^ 2 + (d.1 : ℝ) * (d.2 : ℝ) + (d.2 : ℝ) ^ 2 ≤ t ^ 2}

/-- Every two distinct indexed points are at Euclidean distance at least one. -/
def OneSeparated {α : Type*} (p : α → ℝ × ℝ) : Prop :=
  ∀ i j, i ≠ j → 1 ≤ euclideanDistance (p i) (p j)

/-- Directed pairs of distinct indexed points at Euclidean distance at most `t`.
Each unordered pair contributes twice. -/
noncomputable def closeDirectedPairs {α : Type*} [Fintype α] [DecidableEq α]
    (t : ℝ) (p : α → ℝ × ℝ) : Finset (α × α) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun q =>
    q.1 ≠ q.2 ∧ euclideanDistance (p q.1) (p q.2) ≤ t

/-- For every radius $t\geq1$, there is a cutoff $N(t)$ such that every
one-separated indexed planar configuration with $n\geq N(t)$ points has at most
$n f(t)$ directed pairs at distance at most $t$, where $f(t)$ is the number of
nonzero unit triangular-lattice vectors of length at most $t$. -/
def GlobalThresholdConjecture : Prop :=
  ∀ t : ℝ, 1 ≤ t → ∃ N : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α],
    N ≤ Fintype.card α → ∀ p : α → ℝ × ℝ,
      OneSeparated p →
        (closeDirectedPairs t p).card ≤ triangularNeighborCount t * Fintype.card α

end Erdos662
