/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

/-
# Mockenhaupt--Seeger--Sogge local smoothing

The implementation lives in `MSSBase`; the Kakeya proof of the light-ray
maximal estimate is consolidated in `MSSKakeya`.
-/

import LeanSpherical.Codex.Spherical.MSSBase
import LeanSpherical.Codex.Spherical.MSSKakeya

namespace Codex.Spherical.MSS

/-- The light-ray maximal estimate. -/
theorem hasLightRayMaximalEstimate : HasLightRayMaximalEstimate :=
  KakeyaFinal.final_hasLightRayMaximalEstimate

end Codex.Spherical.MSS
