"""Generate rank certificates for every ICARM leaderboard curve not yet in the
Curves library, and rebuild the Curves.lean aggregator. Run from the repo root
with tools/gen_curve.py and tools/curve_template.lean present. Drives the CI
leaderboard-sync workflow; writes the PR body to $RUNNER_TEMP/pr_body.md and the
run outcome to $GITHUB_OUTPUT.

Curves that do not certify are skipped and listed, so one hard curve never blocks
the rest. The aggregator is reproduced directly (no lake); CI's mk_all --check
validates it on the resulting PR.
"""
import glob
import json
import os
import shutil
import subprocess
import sys
import urllib.request

DB_URL = "https://elliptic-rank.icarm.cloud/database.json"


def main():
    curves = json.load(urllib.request.urlopen(DB_URL, timeout=60))["curves"]
    new = [c for c in curves
           if not os.path.exists(f"Curves/Curve{int(c['id']):03d}.lean")]

    os.makedirs("_sync_tmp", exist_ok=True)
    generated, failed = [], []
    for c in sorted(new, key=lambda c: int(c["id"])):
        jf = f"_sync_tmp/c{c['id']}.json"
        with open(jf, "w") as fh:
            json.dump(c, fh)
        p = subprocess.run(
            [sys.executable, "tools/gen_curve.py", "--json", jf, "--repo", "."],
            capture_output=True, text=True)
        if p.returncode == 0:
            generated.append(int(c["id"]))
        else:
            tail = p.stderr.strip().splitlines()[-1] if p.stderr.strip() else "error"
            failed.append((int(c["id"]), tail))

    if generated:
        mods = sorted(os.path.splitext(os.path.basename(f))[0]
                      for f in glob.glob("Curves/Curve*.lean"))
        header = "module  -- shake: keep-all --deprecated_module: ignore\n\n"
        body = "\n".join(f"public import Curves.{m}" for m in mods) + "\n"
        with open("Curves.lean", "w") as fh:
            fh.write(header + body)

    lines = []
    if len(generated) == 1:
        lines.append(f"Adds leaderboard curve {generated[0]}.")
    elif generated:
        lines.append(f"Adds {len(generated)} leaderboard curves "
                     f"({min(generated)}–{max(generated)}).")
    if failed:
        lines.append("Did not certify, skipped: "
                     + ", ".join(str(i) for i, _ in failed) + ".")
    body_md = "\n\n".join(lines) or "No new leaderboard curves."
    with open(os.path.join(os.environ.get("RUNNER_TEMP", "."), "pr_body.md"), "w") as fh:
        fh.write(body_md + "\n")

    with open(os.environ.get("GITHUB_OUTPUT", os.devnull), "a") as fh:
        fh.write(f"has_new={'true' if generated else 'false'}\n")
        fh.write(f"count={len(generated)}\n")

    print(f"generated {len(generated)}, failed {len(failed)}: {body_md}")

    # Drop the pulled generator and scratch so only Curves/, data/, Curves.lean
    # remain as the change set.
    shutil.rmtree("tools", ignore_errors=True)
    shutil.rmtree("_sync_tmp", ignore_errors=True)


if __name__ == "__main__":
    main()
