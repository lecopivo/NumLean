module

public import NumLean
public import NumLean.Data.Scalars.Float64.RealModel
-- public meta import NumLean.Data.FinHTuple.Pretty

@[expose] public section

open NumLean

namespace FloatTensor

instance : HasDefaultFlatRepr Nat (Vector Nat) where
instance : HasDefaultFlatRepr Int (Vector Int) where

/-- info: ⊞[1, 2, 3] : ℕ^[3] -/
#guard_msgs in
#check ⊞[1,2,3]

/-- info: ⊞[-1, 2, 3] : ℤ^[3] -/
#guard_msgs in
#check ⊞[-1,2,3]

-- #check (Float^[2])^[2]

-- #eval show IO Unit from do
--   for h : i in 0...2 do
--     for h : j in 0...2 do
--       IO.println (⊞[[1.0,2],[3,4]][i,j])

/-- info: 2.0 • ⊞[1.0, 2, 3, 4] : Float^[4] -/
#guard_msgs in
#check 2.0 • ⊞[1.0,2,3,4]

/-- info: ⊞[1.0, 2, 3, 4] - ⊞[100.0, 0, 0, 0] : Float^[4] -/
#guard_msgs in
#check ⊞[1.0,2,3,4] - ⊞[100.0,0,0,0]

/-- info: ⊞[[1.0, 2], [3, 4]] - ⊞[[100.0, 0], [0, 0]] : Float^[2, 2] -/
#guard_msgs in
#check ⊞[[1.0,2],[3,4]] - ⊞[[100.0,0],[0,0]]

-- missing product of TensorIndexType
/-- info: ⊞[[1.0, 2], [3, 4]] : Float^[2, 2] -/
#guard_msgs in
#check ⊞[[1.0,2],[3,4]]
