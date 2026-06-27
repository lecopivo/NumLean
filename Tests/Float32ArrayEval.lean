import NumLean.Data.Scalars.Float32.Float32Array

open NumLean

/-- info: [1.000000, 2.000000, 3.000000] -/
#guard_msgs in
#eval Float32Array.mk #[1,2,3]
