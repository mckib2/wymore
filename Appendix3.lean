import Appendix3.Zx1
import Appendix3.Zx2
import Appendix3.Zx3
import Appendix3.Zx4
import Appendix3.Zx5
import Appendix3.Zx6
import Appendix3.Zx7
import Appendix3.Zx8
import Appendix3.Zx9
import Appendix3.Zx10

/-!
# Appendix 3 — Worked `DiscreteSystem` Examples

Aggregates the ten worked Wymore systems `Zx1`–`Zx10` so they are built (and therefore
validated) as part of the default `lake build`. Each module defines a concrete system via the
`wymore_system` macro and proves properties about it, including the Definition 2.5 membership
obligations (see `Appendix3/Zx2.lean`).

**Def 2.5 gallery (permanent partial):** the textbook claims Zxk for every k ∈ [1, 168];
this repo formalizes **10** systems only. See [wymore_chapter2_audit.md](wymore_chapter2_audit.md).
-/
