# Hasse proof provenance and modifications

Adapted from [CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB),commit `e0284fdbcab2d6a1c3246b7ea362f4b96d7b2e10`,projects/HasseWeil/HasseWeil. Original copyright and author notices are preserved in every source. Licensed under Apache-2.0;see LICENSE. The upstream root NOTICE path returned404 at this commit.

The187 dependency modules are adapted to the existing Lean4.30.0/mathlib v4.30.0 toolchain. Imports are namespaced under ZhangLS.External.HasseWeil. Compatibility changes cover older Dirichlet/EDS names,explicit polynomial maps and derivatives,old ramification/inertia APIs,fraction-field rank comparisons,and zero cases in tensor induction. The theorem statements used by the Hasse capstone retain actual mathlib objects. Fifteen unused declarations affected by unfinished branches were removed:

- HasseWeil.Foundation.OmegaPullbackCoeff.omegaPullbackCoeff_mulByInt
- HasseWeil.Foundation.OmegaPullbackCoeff.wronskian_Φ_ΨSq
- HasseWeil.Foundation.OmegaPullbackCoeff.wronskian_Φ_ΨSq_nat
- HasseWeil.Foundation.OmegaPullbackCoeff.divPoly_wronskian_identity
- HasseWeil.Isogeny.FormalSeries.omegaPullbackCoeff_eq_formalIsogenyLeading
- HasseWeil.Isogeny.OmegaCoeffViaFormalGroup.omegaPullbackCoeff_mulByInt_via_formalGroup
- HasseWeil.Isogeny.OmegaCoeffViaFormalGroup.omegaPullbackCoeff_mulByInt_p_eq_zero_via_formalGroup
- HasseWeil.Isogeny.OmegaCoeffViaFormalGroup.omegaPullbackCoeff_localExpand_eq_coeff_one
- HasseWeil.Isogeny.OmegaCoeffViaFormalGroup.omegaPullbackCoeff_mem_F
- HasseWeil.Isogeny.OmegaCoeffViaFormalGroup.omegaPullbackCoeff_ordAtInfty_nonneg
- HasseWeil.Isogeny.OmegaCoeffViaFormalGroup.omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization
- HasseWeil.Isogeny.OmegaCoeffViaFormalGroup.omegaPullbackCoeff_isIntegral_polynomialX
- HasseWeil.HasseBound.WeilPairing.PencilComapPointValuation.pencilScalingComapDataCard_pDvdR
- HasseWeil.HasseBound.WeilPairing.PencilComapPointValuation.pencilScalingComapDataCard_sep
- HasseWeil.HasseBound.WeilPairing.PencilComapPointValuation.pencilScaling_holds

The clean temporary tree was freshly compiled module by module;all7900 declarations have zero unfinished-proof dependencies. HasseWeil.WeilPairing.hasse_bound independently uses only propext,Classical.choice,Quot.sound,and pointCount is Fintype.card of the actual Weierstrass point type. See audit/external_hasse_clean_manifest.json and audit/external_hasse_clean_capstone_axioms.txt for evidence before namespacing;Step133 records project verification after namespacing.
