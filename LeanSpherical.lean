module

public import LeanSpherical.Auto.ConvexDuality
public import LeanSpherical.Auto.RadialFourierTransform
public import LeanSpherical.Auto.Spherical.SphericalMaximal
public import LeanSpherical.Auto.Spherical.AHRS.TheoremOne
public import LeanSpherical.Auto.Spherical.SWW
public import LeanSpherical.Auto.Spherical.PowerWeights.PlanarClosure
public import LeanSpherical.Auto.Spherical.RS.TypeSetCharacterization
public import LeanSpherical.Auto.Spherical.LegendreAssouad
public import LeanSpherical.Auto.Spherical.BRRS.TheoremOne
public import LeanSpherical.Auto.Spherical.BRSRadial.MainTheorems
public import LeanSpherical.Auto.Spherical.FLLRS.MainTheorems
public import LeanSpherical.Auto.Spherical.FLLRS.Sec3SequenceBounds

/-!
# LeanSpherical

Root module of the project. It imports the main `Auto` entry points and checks the axioms of the
headline results with `#print axioms`.
-/

@[expose] public section

#check Auto.Spherical.PowerWeights.closure_typeSet_eq
#print axioms Auto.Spherical.PowerWeights.closure_typeSet_eq

#check Auto.Spherical.SWW.eLpNorm_restrictedSphericalMaximal_le
#print axioms Auto.Spherical.SWW.eLpNorm_restrictedSphericalMaximal_le

#check Auto.Spherical.SWW.eLpNorm_sphericalMaximal_le
#print axioms Auto.Spherical.SWW.eLpNorm_sphericalMaximal_le

#check Auto.Spherical.SWW.eLpNorm_lacunarySphericalMaximal_le
#print axioms Auto.Spherical.SWW.eLpNorm_lacunarySphericalMaximal_le

#check Auto.Spherical.AHRS.theorem_one
#print axioms Auto.Spherical.AHRS.theorem_one

#check Auto.Spherical.AHRS.theorem_one_Lp
#print axioms Auto.Spherical.AHRS.theorem_one_Lp

#check Auto.Spherical.SphericalMaximal.stein_spherical_maximal
#print axioms Auto.Spherical.SphericalMaximal.stein_spherical_maximal

#check Auto.Spherical.FLLRS.planar_spherical_maximal_endpoint
#print axioms Auto.Spherical.FLLRS.planar_spherical_maximal_endpoint
#check Auto.Spherical.FLLRS.full_spherical_maximal_endpoint
#print axioms Auto.Spherical.FLLRS.full_spherical_maximal_endpoint
#check Auto.Spherical.FLLRS.general_assouad_maximal_endpoint
#print axioms Auto.Spherical.FLLRS.general_assouad_maximal_endpoint
#print axioms Auto.Spherical.FLLRS.exists_synthesis_planar_shell_four_gain
#print axioms Auto.Spherical.FLLRS.exists_synthesis_planar_shell_all_p_gain
#check Auto.Spherical.FLLRS.sequence_iff
#print axioms Auto.Spherical.FLLRS.sequence_iff
#check Auto.Spherical.FLLRS.global_sequence_iff
#print axioms Auto.Spherical.FLLRS.global_sequence_iff
