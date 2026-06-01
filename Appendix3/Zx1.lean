import Mbse.Notation

wymore_system Zx1 = (SZx1, IZx1, OZx1, NZx1, RZx1) where
  SZx1 = {1},
  IZx1 = {2},
  OZx1 = {3},
  NZx1 = {((1, 2), 1)},
  RZx1 = {(1, 3)}.

#check Zx1
#print SZx1
#print NZx1

#check Zx1.sz_finite -- Proof that SZx1 is finite
-- #eval Fintype.card SZx1

example : Zx1.NZ SZx1.v1 IZx1.v2 = SZx1.v1 := rfl
example : Zx1.RZ SZx1.v1 = OZx1.v3 := rfl
