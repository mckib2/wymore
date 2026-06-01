import Mbse.Notation

wymore_system Zx8 = (SZx8, IZx8, OZx8, NZx8, RZx8) where
  SZx8 = {1, 2},
  IZx8 = {3, 4},
  OZx8 = {5, 6},
  NZx8 = {((1, 3), 1), ((1, 4), 1), ((2, 3), 1), ((2, 4), 2)},
  RZx8 = {(1, 5), (2, 6)}.
