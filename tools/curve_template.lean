/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve
import ECCompute.Soundness.JInvariant

/-!
# Curve {id} has rank at least {rank}

The elliptic curve recorded as
[curve {id}](https://elliptic-rank.icarm.cloud/curve/{id}) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : {eq}`,   with
{coeffs}

over `ℚ`. It has Mordell-Weil rank at least `{rank}`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve{id}.txt`; descent labels are in
`data/curve{id}-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

{defblock}

{rankblock}

{ellblock}

{jblock}

end ECCompute
