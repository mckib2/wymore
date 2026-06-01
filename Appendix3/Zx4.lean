import Mbse.Notation

wymore_system Zx4 = (SZx4, IZx4, OZx4, NZx4, RZx4) where
  SZx4 = {1, 2},
  IZx4 = {3, 4},
  OZx4 = {5, 6},
  NZx4 = {((1, 3), 2), ((1, 4), 2), ((2, 3), 1), ((2, 4), 1)},
  RZx4 = {(1, 5), (2, 6)}.
