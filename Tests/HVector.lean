import NumLean.Data.HVector

open NumLean

namespace Tests.HVector

abbrev Rank3 := HTuple.Profile.prod .leaf (.prod .leaf .leaf)

def v123 : HVector Nat Rank3 :=
  HVector.ofHTuple h(1, 2, 3)

example : v123.toHTuple = h(1, 2, 3) := by
  exact (HVector.equivHTuple Nat Rank3).right_inv h(1, 2, 3)

example : (HVector.left v123).toHTuple = h(1) := by
  apply HTuple.ext
  intro i
  cases i
  simp [v123]

example : (HVector.right v123).toHTuple = h(2, 3) := by
  apply HTuple.ext
  intro i
  cases i with
  | left i => cases i; simp [v123]
  | right i => cases i; simp [v123]

example : (v123.map (fun x => x + 1)).toHTuple = h(2, 3, 4) := by
  apply HTuple.ext
  intro i
  cases i with
  | left i => cases i; simp [v123]
  | right i =>
      cases i with
      | left i => cases i; simp [v123]
      | right i => cases i; simp [v123]

example : v123.foldMap (fun x => x) = 6 := by
  rfl

example :
    (v123.set (HTuple.Index.right (HTuple.Index.left HTuple.Index.leaf)) 9).toHTuple = h(1, 9, 3) := by
  apply HTuple.ext
  intro i
  cases i with
  | left i => cases i; simp [v123]
  | right i =>
      cases i with
      | left i => cases i; simp [v123]
      | right i => cases i; simp [v123]

end Tests.HVector
