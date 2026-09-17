#!/usr/bin/env bash
# One command regenerates every certificate, the checker results, the summary and Figure 1.
set -euo pipefail
cd "$(dirname "$0")"
PY=${PY:-python3}
if [ ! -d .venv ]; then "$PY" -m venv .venv && .venv/bin/pip install -q -r requirements.txt; fi
cd results
echo "[1/5] certificates, K = 1000, cells of width 0.01 on [1.17, 1.80]"
../.venv/bin/python -u ../src/rigorous_crude.py | tee rigorous_crude.log
echo "[2/5] edge refinement, K = 2000, cells of width 0.005 on [1.73, 1.80]"
../.venv/bin/python -u ../src/edge_K2000.py | tee rigorous_crude_edge_K2000.log
echo "[3/5] independent checker (interval arithmetic, K = 150, three spot cells)"
../.venv/bin/python -u ../src/independent_check.py 150 90 | tee independent_check_K150.log
if [ "${CHECK_EDGE:-0}" = 1 ]; then
  echo "[3b/5] independent checker near the endpoint: K = 1000 on [1.730, 1.735], K = 2000 on [1.750, 1.755] (about 4 hours)"
  ../.venv/bin/python -u ../src/independent_check.py 1000 90 1.730:1.735 | tee independent_check_K1000_1.730-1.735.log
  ../.venv/bin/python -u ../src/independent_check.py 2000 90 1.750:1.755 | tee independent_check_K2000_1.750-1.755.log
fi
echo "[4/5] summary"
../.venv/bin/python ../src/summary.py > /dev/null
echo "[5/5] figure"
../.venv/bin/python ../src/make_figure.py
echo "done: results/certificate_summary.json, results/fig1_margin.png"
