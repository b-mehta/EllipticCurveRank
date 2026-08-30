/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve {id} has rank at least {rank}

The elliptic curve recorded as
[curve {id}](https://elliptic-rank.icarm.cloud/curve/{id}) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : {eq}`,   with
{coeffs}

over `ℚ`. It has Mordell-Weil rank at least `{rank}`.{attribution}
-/

namespace ECCompute

open WeierstrassCurve

{defblock}

{rankblock}

{ellblock}

{jblock}

end ECCompute
