import Lake
open Lake DSL

package «efficient-chad» where
  version := v!"0.1.0"

@[default_target]
lean_lib EfficientChad where
  roots := #[`EfficientChad]
