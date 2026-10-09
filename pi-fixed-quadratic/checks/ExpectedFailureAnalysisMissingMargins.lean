import FixedQuadratic.AnalysisPort.Packet
open OAI.PiExponent OAI.PiExponent.FixedFieldAnalyticData
open OAI.PiExponent.FixedFieldLiteralAnalytic
example {nu : ℝ} (d : FixedFieldAnalyticData nu) [FiniteDimensional ℚ d.F]
    (hF : Module.finrank ℚ d.F = 2) (hnu : 2 < nu)
    (hminor : ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧ ∃ selection : Row d H → Column d H,
      Function.Injective selection ∧ (actualMinor d H selection).det ≠ 0) : False :=
  no_compatible_packet d hF hnu hminor
