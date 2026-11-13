# Notice for Vendored `DifferentialGeometry` Library

This directory contains the 509 Lean 4 modules transitively imported by `BCG` from:

- **Upstream Repository:** [`qinz1yang/differential-geometry`](https://github.com/qinz1yang/differential-geometry) (`v0.1.5`, Diling Yang / Chow-Liao-Qin)
- **License:** Apache License, Version 2.0 (see [`LICENSE`](./LICENSE))

## Modifications for Lean 4 / Mathlib `v4.35.0` Compatibility

While upstream `qinz1yang/differential-geometry@v0.1.5` targets `leanprover/lean4:v4.35.0-rc3`, this vendored subset includes minor compatibility adjustments across 16 files so the library compiles cleanly against `leanprover/lean4:v4.35.0` and `mathlib4@v4.35.0`:

- `Analysis/Integration/DivergenceTheorem/Local/ChartInvariance.lean`
- `Analysis/ODE/Flow/HigherRegularity/FiniteOrder.lean`
- `Analysis/ODE/Flow/LinearODE/Solution.lean`
- `Bundle/PartialMfderiv/Basic.lean`
- `Geometry/Comparison/HopfRinow/ChartVelocityConvergence.lean`
- `Geometry/Connection/LeviCivita/Scaling.lean`
- `Geometry/Connection/ParallelTransport/AffineReparam.lean`
- `Geometry/Connection/Realization/Embedding.lean`
- `Geometry/Connection/TensorNabla/FixedChart/Nabla0S.lean`
- `Geometry/Coordinates/Frame/Coordinate.lean`
- `Geometry/Curvature/CurvatureOperator/Ricci/Basic.lean`
- `Geometry/Hyperbolic/Hyperboloid/RiemannianMetric.lean`
- `Geometry/Metric/TensorInner/FiberMetric/Tensor0SMetric.lean`
- `Tensor/Product/Pretrivialization.lean`
- `Tensor/RSTensor/Coordinates/Field.lean`
- `Topology/Manifold/OpenSubtype.lean`
