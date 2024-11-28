import Lake
open Lake DSL

package seq where
  version := v!"0.1.0"

@[default_target]
lean_lib SEq where

lean_lib SEq.test where
  globs := #[.submodules `test]
