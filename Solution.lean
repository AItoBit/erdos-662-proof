module

public import Statement
public import Research.GlobalShellSix

/-!
# Disproof of the global threshold formulation of Erdős Problem 662

The counterexample and its exact counts are due to Colin Snyder / Star Fleet,
as formalized in `Research.GlobalShellSix`. This module connects that proof to
the independently stated full global threshold conjecture in `Statement`.
-/

@[expose] public section

namespace Erdos662

/-- The unrestricted triangular-lattice count agrees with the complete
radius-six enumeration in the supplied counterexample. -/
theorem triangularNeighborCount_six : triangularNeighborCount 6 = 126 := by
  rw [triangularNeighborCount, ← Research.triCoordsWithinThirtySix_card]
  apply Nat.subtype_card
  intro d
  rw [Research.mem_triCoordsWithinThirtySix_iff]
  constructor
  · rintro ⟨hne, hnorm⟩
    refine ⟨hne, ?_⟩
    have hcast : (Research.triNormSq d : ℝ) ≤ 36 := by exact_mod_cast hnorm
    norm_num [Research.triNormSq] at hcast ⊢
    exact hcast
  · rintro ⟨hne, hnorm⟩
    refine ⟨hne, ?_⟩
    have hcast : (Research.triNormSq d : ℝ) ≤ 36 := by
      norm_num [Research.triNormSq] at hnorm ⊢
      exact hnorm
    exact_mod_cast hcast

/-- At radius six, the full global statement has exactly the threshold and
normalization refuted by the supplied counterexample. -/
theorem globalThresholdConjecture_implies_shellSix
    (h : GlobalThresholdConjecture) : Research.EventualShellSixDirectedAverageBound := by
  obtain ⟨N, hN⟩ := h 6 (by norm_num)
  refine ⟨N, ?_⟩
  intro α _ _ hcard p hp
  have hbound := hN α hcard p hp
  have hpairs : closeDirectedPairs 6 p = Research.radiusSixOrdinaryDirectedPairs p := by
    unfold closeDirectedPairs Research.radiusSixOrdinaryDirectedPairs
    congr 1
  rw [hpairs, triangularNeighborCount_six] at hbound
  exact hbound

/-- The corrected global threshold conjecture is false. -/
theorem not_globalThresholdConjecture : ¬ GlobalThresholdConjecture := by
  intro h
  exact Research.not_eventualShellSixDirectedAverageBound
    (globalThresholdConjecture_implies_shellSix h)

end Erdos662
