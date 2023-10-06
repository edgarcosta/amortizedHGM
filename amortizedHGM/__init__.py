from .hgm_modpe import AmortizingHypergeometricData

__all__ = ["AmortizingHypergeometricData"]

assert AmortizingHypergeometricData

from .hgm import (
    AccRemForest,
    AmortizingHypergeometricData as AmortizingHypergeometricDatamodp,
    compare as comparemodp,
)

assert AccRemForest
assert AmortizingHypergeometricDatamodp
assert comparemodp
__all__ += ["AccRemForest", "AmortizingHypergeometricDatamodp", "comparemodp"]
