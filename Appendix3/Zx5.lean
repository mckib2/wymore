import Mbse.Notation

wymore_system Zx5 = (SZx5, IZx5, OZx5, NZx5, RZx5) where
  SZx5 = {1, 2},
  IZx5 = {3, 4},
  OZx5 = {5, 6},
  NZx5 = {((1, 3), 1), ((1, 4), 2), ((2, 3), 1), ((2, 4), 2)},
  RZx5 = {(1, 5), (2, 6)}.
