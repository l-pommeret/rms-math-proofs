/-
# Q764 — aggregation module

This module imports every layer of the development and records, in one place, the public
results that are established.

## Preserved mathematical core (`RequestProject.Q764`, unchanged)

`Q764.covRad`, `Q764.covRad_le_iff`, `Q764.covRad'`, `Q764.exists_optimal_center_set`,
`Q764.FarthestFirst` with `Q764.FarthestFirst.two_approx` and
`Q764.FarthestFirst.covRad_le_two_mul`, `Q764.oneTwo_triangle`, the block lemmas
`Q764.blockRadius_eq_max`, `Q764.blockRadius_eq_mid`, `Q764.blockCost_eq`,
`Q764.exists_center_in_block`, `Q764.blockCost_mono_left`, `Q764.blockCost_mono_right`, and
the feasibility recurrence `Q764.coverPrefix_succ_iff`,
`Q764.coverPrefix_iff_exists_centers`.

## Unit-cost model (`RequestProject.Q764Cost`)

`Q764.OpCount` / `Q764.Counted` with costed primitives for reads, writes, arithmetic,
comparisons and metric distance queries, and loop cost lemmas.

## Stage 1 (`RequestProject.Q764Bridge`)

`Q764.covRad_le_iff_dominates`, `Q764.optimalRadius`, `Q764.optimalRadius_attained`,
`Q764.covRad'_mono`, `Q764.optimalRadius_eq_optimalRadiusLe`.

## Stage 2 — arbitrary finite metric (`RequestProject.Q764Metric`)

* farthest-first: `Q764.farthestFirstRun_spec`, `Q764.farthestFirstRun_work_le`,
  `Q764.farthestFirstAlgorithm_two_approx`, `Q764.farthestFirstAlgorithm_work_le`
  (`O(n*k)` operations, factor `2`, obtained from the preserved
  `Q764.FarthestFirst.covRad_le_two_mul`);
* exact enumeration: `Q764.exhaustiveMetric_correct`, `Q764.exhaustiveMetric_work_le`
  (`O((n choose k) * n * k)` operations).

## Stage 3 — exact algorithm for ordered real points

* `RequestProject.Q764LineCore` — the costed loop combinator `Q764.Line.countedIter`, the
  costed pointer search `Q764.Line.findFromC`, and the generic crossing minimum
  `Q764.Line.crossMin` with `Q764.Line.crossMin_spec` and `Q764.Line.crossMin_work_le`;
* `RequestProject.Q764LineTable` — the block-cost table `Q764.Line.blockTableRun` with
  `Q764.Line.blockTable_correct` and `Q764.Line.blockTable_work_le` (`O(n^2)`);
* `RequestProject.Q764LineDP` — the dynamic-programming layers `Q764.Line.dpRun` with
  `Q764.Line.dpRun_correct` and `Q764.Line.dpRun_work_le` (`O(k*n)`);
* `RequestProject.Q764LineAlg` — the whole algorithm `Q764.Line.lineKCenterRun` with
  `Q764.Line.lineKCenter_correct` (objective-level optimality for the original
  `Finset ℝ` point set) and `Q764.Line.lineKCenter_work_le` (`O(n^2 + k*n)`);
* `RequestProject.Q764LineFin` — the same for an indexed family `x : Fin n → ℝ`:
  `Q764.Line.lineKCenter_fin_correct` and `Q764.Line.lineKCenter_fin_work_le`.

## Stage 4 (`RequestProject.Q764Complexity`)

The uniform Boolean-circuit presentation of NP: `Q764.Circuit`, `Q764.PolynomiallyBounded`,
`Q764.InNP`, `Q764.InP`, `Q764.PolyReduction`, `Q764.CircuitSAT`, `Q764.NPHard`,
`Q764.NPComplete`, `Q764.PEqualsNP`, together with `Q764.circuitSAT_inNP`,
`Q764.inNP_polyReduces_circuitSAT`, `Q764.PolyReduction.trans`,
`Q764.InP.of_polyReduction` and `Q764.pEqualsNP_iff`.

## Stage 5 (`RequestProject.Q764Codes`, `RequestProject.Q764Gadget`,
`RequestProject.Q764MetricReduce`)

`Q764.vertexCover_iff_oneTwo_radius_one`,
`Q764.vertexCover_polyReduces_oneTwoKCenter`,
`Q764.oneTwoKCenter_polyReduces_metricKCenter`,
`Q764.vertexCover_polyReduces_metricKCenter`, the exact gap `Q764.vcToOneTwo_gap`, and the
unconditional solver transfers `Q764.vertexCover_inP_of_metricKCenter_inP`,
`Q764.vertexCover_inP_of_oneTwoKCenter_inP`.

See `SCOPE.md` for what is and is not covered relative to the full declared answer.
-/
import RMS.Q764
import RMS.Q764Cost
import RMS.Q764Bridge
import RMS.Q764Complexity
import RMS.Q764Codes
import RMS.Q764Metric
import RMS.Q764Line
import RMS.Q764LineCore
import RMS.Q764LineTable
import RMS.Q764LineDP
import RMS.Q764LineAlg
import RMS.Q764LineFin
import RMS.Q764Gadget
import RMS.Q764MetricReduce

namespace Q764

-- Stage 0: the preserved core still elaborates.
#check @Q764.exists_optimal_center_set
#check @Q764.FarthestFirst.covRad_le_two_mul
#check @Q764.coverPrefix_succ_iff
#check @Q764.coverPrefix_iff_exists_centers
#check @Q764.oneTwo_triangle

-- Gate (ii): the exact arbitrary-metric enumeration.
#check @Q764.exhaustiveMetric_correct
#check @Q764.exhaustiveMetric_work_le

-- Stage 2, extra: the compiled factor-2 approximation.
#check @Q764.farthestFirstAlgorithm_two_approx
#check @Q764.farthestFirstAlgorithm_work_le

-- Gate (i): the exact ordered-line algorithm.
#check @Q764.Line.lineKCenterRun
#check @Q764.Line.lineKCenter_correct
#check @Q764.Line.lineKCenter_work_le
#check @Q764.Line.lineKCenter_fin_correct
#check @Q764.Line.lineKCenter_fin_work_le
#check @Q764.Line.blockTable_correct
#check @Q764.Line.blockTable_work_le
#check @Q764.Line.dpRun_correct
#check @Q764.Line.dpRun_work_le
#check @Q764.Line.rho_le_iff
#check @Q764.Line.rho_le_iff_exists_centers

-- Stage 4.
#check @Q764.circuitSAT_inNP
#check @Q764.inNP_polyReduces_circuitSAT
#check @Q764.pEqualsNP_iff

-- Gate (iii): the concrete Vertex-Cover reduction and the unconditional solver transfer.
#check @Q764.vertexCover_iff_oneTwo_radius_one
#check @Q764.vertexCover_polyReduces_oneTwoKCenter
#check @Q764.oneTwoKCenter_polyReduces_metricKCenter
#check @Q764.vertexCover_polyReduces_metricKCenter
#check @Q764.vcToOneTwo_gap
#check @Q764.vertexCover_inP_of_metricKCenter_inP
#check @Q764.vertexCover_inP_of_oneTwoKCenter_inP

end Q764
