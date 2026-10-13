#!/usr/bin/env python3
"""Retrieve the pinned base if requested, check its hash, and verify proofs.

Original publication material: CC0 1.0 Universal. Python standard library only.
The mathematical checking is performed by the external metamath-knife verifier.
"""

import argparse
import hashlib
from pathlib import Path
import shutil
import subprocess
import sys
import urllib.request


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true",
                        help="download the pinned set.mm if it is absent")
    parser.add_argument("--verifier", default="metamath-knife",
                        help="path to metamath-knife (default: search PATH)")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    pin = dict(line.split("=", 1) for line in
               (root / "set-mm-version.txt").read_text().splitlines() if line)
    verifier = shutil.which(args.verifier)
    if verifier is None:
        parser.error("metamath-knife is missing; see README.md for installation")
    verifier = str(Path(verifier).resolve())
    base = root / "set.mm"
    if not base.exists():
        if not args.fetch:
            parser.error("set.mm is missing; run with --fetch or supply the pinned file")
        print("Downloading the pinned public set.mm...", flush=True)
        with urllib.request.urlopen(pin["url"], timeout=120) as response:
            data = response.read()
        if hashlib.sha256(data).hexdigest() != pin["sha256"]:
            parser.error("downloaded set.mm has the wrong SHA-256; nothing was written")
        base.write_bytes(data)
    digest = hashlib.sha256(base.read_bytes()).hexdigest()
    if digest != pin["sha256"]:
        parser.error("existing set.mm has the wrong SHA-256; it was not overwritten")
    print("Base database SHA-256 matches the pin.", flush=True)
    version = subprocess.run([verifier, "--version"], cwd=root, check=False)
    if version.returncode:
        return version.returncode
    return subprocess.run(
        [verifier, "--verify", "--jobs", "4", "--time", "morley.mm"],
        cwd=root, check=False,
    ).returncode


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print(f"Verification setup failed: {error}", file=sys.stderr)
        sys.exit(1)
