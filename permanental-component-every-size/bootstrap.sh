#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake env lean --version
lake exe cache get
python3 replay-complete.py --jobs 3
