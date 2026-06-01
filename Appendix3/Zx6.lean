import Mbse.Notation

wymore_system Zx6 = (SZx6, IZx6, OZx6, NZx6, RZx6) where
  SZx6 = {1, 2},
  IZx6 = {3, 4},
  OZx6 = {5, 6},
  NZx6 = {((1, 3), 1), ((1, 4), 2), ((2, 3), 2), ((2, 4), 1)},
  RZx6 = {(1, 5), (2, 6)}.
