module

public import NumLean.Experimental.Data.HVector.Basic

@[expose] public section

namespace NumLean

namespace HVector

variable {α : Type u} {β : Type v} {R : Type w}
variable {p : HTuple.Profile}

instance [Zero α] : Zero (HVector α p) where
  zero := ofFn fun _ => 0

instance [One α] : One (HVector α p) where
  one := ofFn fun _ => 1

instance [Add α] : Add (HVector α p) where
  add := map₂ (· + ·)

instance [Mul α] : Mul (HVector α p) where
  mul := map₂ (· * ·)

instance [Neg α] : Neg (HVector α p) where
  neg := map Neg.neg

instance [Sub α] : Sub (HVector α p) where
  sub := map₂ (· - ·)

instance [SMul R α] : SMul R (HVector α p) where
  smul r := map (fun x => r • x)

@[simp] theorem get_zero [Zero α] (i : HTuple.Index p) : (0 : HVector α p).get i = 0 := by
  change (ofFn (fun _ => 0) : HVector α p).get i = 0
  simp

@[simp] theorem get_one [One α] (i : HTuple.Index p) : (1 : HVector α p).get i = 1 := by
  change (ofFn (fun _ => 1) : HVector α p).get i = 1
  simp

@[simp] theorem get_add [Add α] (x y : HVector α p) (i : HTuple.Index p) :
    (x + y).get i = x.get i + y.get i := by
  change (map₂ (fun a b => a + b) x y).get i = x.get i + y.get i
  simp

@[simp] theorem get_mul [Mul α] (x y : HVector α p) (i : HTuple.Index p) :
    (x * y).get i = x.get i * y.get i := by
  change (map₂ (fun a b => a * b) x y).get i = x.get i * y.get i
  simp

@[simp] theorem get_neg [Neg α] (x : HVector α p) (i : HTuple.Index p) :
    (-x).get i = -x.get i := by
  change (map (fun a => -a) x).get i = -x.get i
  simp

@[simp] theorem get_sub [Sub α] (x y : HVector α p) (i : HTuple.Index p) :
    (x - y).get i = x.get i - y.get i := by
  change (map₂ (fun a b => a - b) x y).get i = x.get i - y.get i
  simp

@[simp] theorem get_smul [SMul R α] (r : R) (x : HVector α p) (i : HTuple.Index p) :
    (r • x).get i = r • x.get i := by
  change (map (fun a => r • a) x).get i = r • x.get i
  simp

end HVector

end NumLean
