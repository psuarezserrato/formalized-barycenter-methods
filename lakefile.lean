import Lake
open Lake DSL

package «BCG» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.backward.isDefEq.respectTransparency, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

lean_lib «DifferentialGeometry» where
  -- Diling Yang / Chow-Liao-Qin DifferentialGeometry library (on-demand compilation of imported modules)

@[default_target]
lean_lib «BCG» where
  -- Master library for Besson-Courtois-Gallot Barycenter Method formalization
