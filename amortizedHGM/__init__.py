from .hgm_modpe import AmortizingHypergeometricData, compare

__all__ = ["AmortizingHypergeometricData", "compare"]

assert AmortizingHypergeometricData
assert compare

from .hgm import (
    AccRemForest,
    AmortizingHypergeometricData as AmortizingHypergeometricDatamodp,
    compare as comparemodp,
)

assert AccRemForest
assert AmortizingHypergeometricDatamodp
assert comparemodp
__all__ += ["AccRemForest", "AmortizingHypergeometricDatamodp", "comparemodp"]
