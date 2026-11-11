#!/usr/bin/env python3
"""Generate exact integer Lean 4 cell certificates covering [117/100, 351/200].

For each rational subcell [la, lb] = [lna / ld, lnb / ld]:
  1. Computes exact integer 1-step RDE post-fixpoint envelopes `ua` (at `la`) and `lb_env` (at `lb`)
     via monotone Tarski iteration on the integer CDF lattice {0, ..., M}^{K+1}.
  2. Verifies the exact natural-number mirror of `GWSpeedCertificate.checkUpperEnv`,
     `GWSpeedCertificate.checkLowerEnv`, and `GWSpeedCertificate.checkCell` in Python.
  3. Exports parallel Lean 4 batch files `lean/GWSpeedCertificate/Certs/Batch*.lean`
     checked by pure kernel reduction (`Eq.refl true`, zero `native_decide`, zero floats),
     plus `lean/GWSpeedCertificate/Certs/AllCells.lean` gluing `[117/100, 351/200]`.
"""

from __future__ import annotations

from fractions import Fraction
from math import gcd
from pathlib import Path
import math
import time
import numpy as np

CELL_SCALE = 100_000_000


def exact_index_map(lnum: int, lden: int, K: int, nu: int, up: bool) -> list[int]:
    """Compute exact integer bin indices j in {0, ..., K} bounding condStep(lam, nu*a + i*h)."""
    lam = Fraction(lnum, lden)
    a = 1 - lam / 2
    b = 1 - lam / 3
    h = (b - a) / K
    out: list[int] = []
    for i in range(nu * K + 1):
        s = nu * a + i * h
        x = (s / (lam + s) - a) / h
        j = math.ceil(x) if up else math.floor(x)
        j = min(max(j, 0), K)
        out.append(j)
    return out


def verify_index_map_int(lnum: int, lden: int, K: int, nu: int, js: list[int], up: bool) -> bool:
    """Exact mirror of `checkIndexUpper` / `checkIndexLower` in `StochasticOrder.lean`."""
    D = 6 * lden * K
    Da = 3 * K * (2 * lden - lnum)
    Dlam = 6 * K * lnum
    prev_j = 0
    for cur_i, j in enumerate(js):
        if not (prev_j <= j <= K):
            return False
        Ds = nu * Da + cur_i * lnum
        Dxj = Da + j * lnum
        if up:
            if not (D * Ds <= Dxj * (Dlam + Ds)):
                return False
        else:
            if not (Dxj * (Dlam + Ds) <= D * Ds):
                return False
        prev_j = j
    return True


def build_envelopes(lnum: int, lden: int, K: int, M: int):
    """Tarski lattice iteration for exact 1-step upper/lower envelopes at `lnum / lden`."""
    j2u = exact_index_map(lnum, lden, K, 2, True)
    j3u = exact_index_map(lnum, lden, K, 3, True)
    j2l = exact_index_map(lnum, lden, K, 2, False)
    j3l = exact_index_map(lnum, lden, K, 3, False)

    assert verify_index_map_int(lnum, lden, K, 2, j2u, True)
    assert verify_index_map_int(lnum, lden, K, 3, j3u, True)
    assert verify_index_map_int(lnum, lden, K, 2, j2l, False)
    assert verify_index_map_int(lnum, lden, K, 3, j3l, False)

    denom = 2 * M * M
    j2u_arr = np.array(j2u, dtype=np.int64)
    j3u_arr = np.array(j3u, dtype=np.int64)
    j2l_arr = np.array(j2l, dtype=np.int64)
    j3l_arr = np.array(j3l, dtype=np.int64)

    u = np.zeros(K + 1, dtype=np.int64)
    u[K] = M
    for _ in range(500):
        s2 = np.convolve(u, u)
        s3 = np.convolve(s2, u)
        push = (
            M * np.bincount(j2u_arr, weights=s2, minlength=K + 1).astype(np.int64)
            + np.bincount(j3u_arr, weights=s3, minlength=K + 1).astype(np.int64)
        )
        Cu_new = np.cumsum(push) // denom
        Cu_new[-1] = M
        u_new = np.diff(Cu_new, prepend=0)
        if np.array_equal(u_new, u):
            break
        u = u_new

    l = np.zeros(K + 1, dtype=np.int64)
    l[0] = M
    for _ in range(500):
        s2 = np.convolve(l, l)
        s3 = np.convolve(s2, l)
        push = (
            M * np.bincount(j2l_arr, weights=s2, minlength=K + 1).astype(np.int64)
            + np.bincount(j3l_arr, weights=s3, minlength=K + 1).astype(np.int64)
        )
        Cl_new = (np.cumsum(push) + denom - 1) // denom
        Cl_new[-1] = M
        l_new = np.diff(Cl_new, prepend=0)
        if np.array_equal(l_new, l):
            break
        l = l_new

    # Verify exact integer CDF dominance (`checkCdfLe`)
    s2u = np.convolve(u, u)
    s3u = np.convolve(s2u, u)
    pu = (
        M * np.bincount(j2u_arr, weights=s2u, minlength=K + 1).astype(np.int64)
        + np.bincount(j3u_arr, weights=s3u, minlength=K + 1).astype(np.int64)
    )
    if not (int(u.sum()) == M and bool(np.all(denom * np.cumsum(u) <= np.cumsum(pu)))):
        return None

    s2l = np.convolve(l, l)
    s3l = np.convolve(s2l, l)
    pl = (
        M * np.bincount(j2l_arr, weights=s2l, minlength=K + 1).astype(np.int64)
        + np.bincount(j3l_arr, weights=s3l, minlength=K + 1).astype(np.int64)
    )
    if not (int(l.sum()) == M and bool(np.all(np.cumsum(pl) <= denom * np.cumsum(l)))):
        return None

    u_list = u.tolist()
    l_list = l.tolist()
    p2u = poly_mul_lean(u_list, u_list)
    p3u = poly_mul_lean(p2u, u_list)
    p2l = poly_mul_lean(l_list, l_list)
    p3l = poly_mul_lean(p2l, l_list)
    return u_list, j2u[: len(p2u)], j3u[: len(p3u)], l_list, j2l[: len(p2l)], j3l[: len(p3l)]


def poly_mul_lean(xs: list[int], ys: list[int]) -> list[int]:
    """Exact mirror of `GWSpeedCertificate.polyMul` in `StochasticOrder.lean`."""
    acc: list[int] = []
    for x in reversed(xs):
        if x == 0:
            acc = [0] + acc
        else:
            shifted = [0] + acc
            scaled = [x * y for y in ys]
            n = max(len(scaled), len(shifted))
            acc = [
                (scaled[k] if k < len(scaled) else 0) + (shifted[k] if k < len(shifted) else 0)
                for k in range(n)
            ]
    return acc


def check_cell_exact_int(lna: int, lnb: int, ld: int, K: int, M: int, env_cache: dict):
    """Exact mirror of `GWSpeedCertificate.checkCell`."""
    P = 6 * ld
    Pla = 6 * lna
    Plb = 6 * lnb
    PA = 3 * (2 * ld - lnb)
    PB = 2 * (3 * ld - lna)
    PE = 2 * P - Plb
    PK = 2 * P + Pla - 2 * Plb

    if not (ld < lna and lna <= lnb and lnb < 2 * ld and 2 * Plb < 2 * P + Pla):
        return None
    if not (PE * P + PK * PB < PE * Pla + 2 * PK * PA):
        return None
    if not (PE * P + 3 * PK * PB < PE * Pla + PK * PA + 2 * PE * PK):
        return None
    if not (PE * Pla + PK * PB < PE * P + 2 * PK * PA + 2 * PK * P):
        return None

    key_a = (Fraction(lna, ld), K, M)
    key_b = (Fraction(lnb, ld), K, M)
    if key_a not in env_cache:
        env_cache[key_a] = build_envelopes(lna, ld, K, M)
    if key_b not in env_cache:
        env_cache[key_b] = build_envelopes(lnb, ld, K, M)
    if env_cache[key_a] is None or env_cache[key_b] is None:
        return None

    ua, j2ua, j3ua, _, _, _ = env_cache[key_a]
    _, _, _, lb_env, j2lb, j3lb = env_cache[key_b]

    D = 6 * ld * K
    Dla = 6 * K * lna
    Dlb = 6 * K * lnb
    Daa = 3 * K * (2 * ld - lna)
    Dha = lna
    Dab = 3 * K * (2 * ld - lnb)
    Dhb = lnb
    E = 2 * D - Dlb
    Knum = 2 * D + Dla - 2 * Dlb

    c2a = np.convolve(ua, ua).tolist()
    c3a = np.convolve(c2a, ua).tolist()
    c2b = np.convolve(lb_env, lb_env).tolist()
    c3b = np.convolve(c2b, lb_env).tolist()

    nz_ua = [(i, w) for i, w in enumerate(ua) if w > 0]
    nz_lb = [(i, w) for i, w in enumerate(lb_env) if w > 0]
    nz_c2a = [(j, w) for j, w in enumerate(c2a) if w > 0]
    nz_c3a = [(j, w) for j, w in enumerate(c3a) if w > 0]
    nz_c2b = [(j, w) for j, w in enumerate(c2b) if w > 0]
    nz_c3b = [(j, w) for j, w in enumerate(c3b) if w > 0]

    raw_e2h = sum(
        wy * wt * ((CELL_SCALE * (Daa + i * Dha)) // ((Dla - D) + (Daa + i * Dha) + (2 * Dab + j * Dhb)) + 1)
        for i, wy in nz_ua
        for j, wt in nz_c2b
    )
    raw_e2l = sum(
        wy * wt * ((CELL_SCALE * (Dab + i * Dhb)) // ((Dlb - D) + (Dab + i * Dhb) + (2 * Daa + j * Dha)))
        for i, wy in nz_lb
        for j, wt in nz_c2a
    )
    raw_e3h = sum(
        wy * wt * ((CELL_SCALE * (Daa + i * Dha)) // ((Dla - D) + (Daa + i * Dha) + (3 * Dab + j * Dhb)) + 1)
        for i, wy in nz_ua
        for j, wt in nz_c3b
    )
    raw_e3l = sum(
        wy * wt * ((CELL_SCALE * (Dab + i * Dhb)) // ((Dlb - D) + (Dab + i * Dhb) + (3 * Daa + j * Dha)))
        for i, wy in nz_lb
        for j, wt in nz_c3a
    )
    raw_h3 = sum(
        wy
        * wt
        * (
            (CELL_SCALE * (D * E * (Daa + i * Dha) * ((3 * Daa + j * Dha) - E)))
            // ((E * (Dla - D) + Knum * ((Daa + i * Dha) + (3 * Daa + j * Dha))) ** 2)
            + 1
        )
        for i, wy in nz_ua
        for j, wt in nz_c3a
    )
    raw_h2 = sum(
        wy
        * wt
        * (
            (CELL_SCALE * (D * E * (Daa + i * Dha) * (D + (2 * Dab + j * Dhb))))
            // ((E * (Dla - D) + Knum * ((Daa + i * Dha) + (2 * Dab + j * Dhb))) ** 2)
            + 1
        )
        for i, wy in nz_ua
        for j, wt in nz_c2b
    )

    e2h = M * raw_e2h
    e2l = M * raw_e2l
    e3h = raw_e3h
    e3l = raw_e3l
    h3_up = raw_h3
    h2_up = M * raw_h2

    if e2l == 0 or e3l == 0:
        return None
    if e3h <= e2l:
        num_r2, den_r2 = e3h, e2l + e3h
    else:
        num_r2, den_r2 = 1, 2

    lhs_int = lnb * (e2h * den_r2 * h3_up + (e2h + e3l) * num_r2 * h2_up)
    rhs_int = ld * den_r2 * (2 * e2h + 3 * e3l) * (e2l + e3l)
    if lhs_int < rhs_int:
        pairs = len(nz_ua) * (len(nz_c2b) + len(nz_c3b) + len(nz_c3a) + len(nz_c2b)) + len(nz_lb) * (
            len(nz_c2a) + len(nz_c3a)
        )
        return {
            "lna": lna,
            "lnb": lnb,
            "ld": ld,
            "K": K,
            "M": M,
            "ua": ua,
            "j2ua": j2ua,
            "j3ua": j3ua,
            "lb_env": lb_env,
            "j2lb": j2lb,
            "j3lb": j3lb,
            "pairs": pairs,
        }
    return None


def fmt_list(xs: list[int]) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def frac_lean(q: Fraction) -> str:
    return f"({q.numerator} / {q.denominator} : ℝ)"


def main() -> None:
    t0 = time.time()
    repo_root = Path(__file__).resolve().parent.parent
    certs_dir = repo_root / "lean" / "GWSpeedCertificate" / "Certs"
    certs_dir.mkdir(parents=True, exist_ok=True)
    for old in certs_dir.glob("*.lean"):
        old.unlink()

    cur = Fraction(117, 100)
    target = Fraction(351, 200)
    env_cache: dict = {}
    cells: list[dict] = []

    widths = [
        Fraction(3, 100),
        Fraction(1, 50),
        Fraction(3, 200),
        Fraction(1, 100),
        Fraction(1, 200),
        Fraction(1, 400),
        Fraction(1, 1000),
    ]
    ks = [20, 30, 45, 65, 90, 120, 160]
    ms = [5000, 10000]

    while cur < target:
        best = None
        for width in widths:
            nxt = min(target, cur + width)
            actual_w = nxt - cur
            ld = (cur.denominator * nxt.denominator) // gcd(cur.denominator, nxt.denominator)
            lna, lnb = int(cur * ld), int(nxt * ld)
            for K in ks:
                for M in ms:
                    cert = check_cell_exact_int(lna, lnb, ld, K, M, env_cache)
                    if cert is not None:
                        score = float(cert["pairs"]) / float(actual_w)
                        if best is None or score < best[0]:
                            best = (score, nxt, cert)
                        break
        if best is None:
            raise RuntimeError(f"Failed to certify cell starting at {cur}")
        _, nxt, cert = best
        cert["idx"] = len(cells)
        cert["q_lo"] = cur
        cert["q_hi"] = nxt
        cells.append(cert)
        cur = nxt

    total_pairs = sum(c["pairs"] for c in cells)
    print(f"Certified {len(cells)} cells covering [117/100, 351/200] in {time.time() - t0:.2f}s (total pairs={total_pairs}).")

    # Partition into up to 14 balanced batches (heavy cells get their own batch for maximum 16-core parallelism)
    num_batches = min(14, len(cells))
    batch_loads = [0] * num_batches
    batch_cells: list[list[dict]] = [[] for _ in range(num_batches)]
    for cert in sorted(cells, key=lambda c: -c["pairs"]):
        b_idx = min(range(num_batches), key=lambda b: batch_loads[b])
        batch_cells[b_idx].append(cert)
        batch_loads[b_idx] += cert["pairs"]
    batch_cells = [sorted(bc, key=lambda c: c["idx"]) for bc in batch_cells if bc]

    batch_names: list[str] = []
    for b_i, bc in enumerate(batch_cells, start=1):
        bname = f"Batch{b_i:02d}"
        batch_names.append(bname)
        lines = [
            "import GWSpeedCertificate.CellVerifier",
            "",
            "/-!",
            f"# Generated Exact Integer Cell Certificates (`{bname}`)",
            "",
            "Verified in Lean's kernel via `Eq.refl true` (zero `native_decide`, zero floats).",
            "-/",
            "",
            "namespace GWSpeedCertificate.Certs",
            "",
            "open MeasureTheory",
            "",
            "set_option maxRecDepth 30000",
            "set_option maxHeartbeats 8000000",
            "",
        ]
        for cert in bc:
            idx = cert["idx"]
            lines.extend(
                [
                    f"def cell_{idx:02d} : CellCert where",
                    f"  lna := {cert['lna']}",
                    f"  lnb := {cert['lnb']}",
                    f"  ld := {cert['ld']}",
                    f"  K := {cert['K']}",
                    f"  M := {cert['M']}",
                    f"  ua := {fmt_list(cert['ua'])}",
                    f"  j2ua := {fmt_list(cert['j2ua'])}",
                    f"  j3ua := {fmt_list(cert['j3ua'])}",
                    f"  lb_env := {fmt_list(cert['lb_env'])}",
                    f"  j2lb := {fmt_list(cert['j2lb'])}",
                    f"  j3lb := {fmt_list(cert['j3lb'])}",
                    "",
                    f"theorem cell_{idx:02d}_ok : checkCell cell_{idx:02d} = true := Eq.refl true",
                    "",
                    f"theorem cell_{idx:02d}_anti {{mu : Measure InfTree23}} [IsGWTree23 mu] :",
                    f"    StrictAntiOn (fun lam => RFunc mu lam / lam)",
                    f"      (Set.Icc (({cert['lna']} : ℝ) / ({cert['ld']} : ℝ)) (({cert['lnb']} : ℝ) / ({cert['ld']} : ℝ))) :=",
                    f"  checkCell_sound cell_{idx:02d} cell_{idx:02d}_ok",
                    "",
                ]
            )
        lines.append("end GWSpeedCertificate.Certs\n")
        (certs_dir / f"{bname}.lean").write_text("\n".join(lines), encoding="utf-8")

    # Emit `AllCells.lean` gluing all contiguous certified cells across [117/100, 351/200]
    glue_lines = [f"import GWSpeedCertificate.Certs.{bn}" for bn in batch_names]
    glue_lines.extend(
        [
            "",
            "/-!",
            "# Contiguous Gluing of Certified Cells on `[117/100, 351/200]` (`AllCells.lean`)",
            "-/",
            "",
            "namespace GWSpeedCertificate.Certs",
            "",
            "open MeasureTheory",
            "",
            "theorem r_div_lam_strictAntiOn_117_to_1755 {mu : Measure InfTree23} [IsGWTree23 mu] :",
            "    StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (351 / 200 : ℝ)) := by",
        ]
    )
    c0 = cells[0]
    glue_lines.append(
        f"  have h_0 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc {frac_lean(c0['q_lo'])} {frac_lean(c0['q_hi'])}) := by"
    )
    glue_lines.append(
        f"    simpa only [show (({c0['lna']} : ℝ) / ({c0['ld']} : ℝ)) = {frac_lean(c0['q_lo'])} by norm_num, "
        f"show (({c0['lnb']} : ℝ) / ({c0['ld']} : ℝ)) = {frac_lean(c0['q_hi'])} by norm_num] using cell_00_anti (mu := mu)"
    )
    for k in range(1, len(cells)):
        ck = cells[k]
        glue_lines.append(
            f"  have hc_{k} : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc {frac_lean(ck['q_lo'])} {frac_lean(ck['q_hi'])}) := by"
        )
        glue_lines.append(
            f"    simpa only [show (({ck['lna']} : ℝ) / ({ck['ld']} : ℝ)) = {frac_lean(ck['q_lo'])} by norm_num, "
            f"show (({ck['lnb']} : ℝ) / ({ck['ld']} : ℝ)) = {frac_lean(ck['q_hi'])} by norm_num] using cell_{k:02d}_anti (mu := mu)"
        )
        glue_lines.append(
            f"  have h_{k} : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc {frac_lean(c0['q_lo'])} {frac_lean(ck['q_hi'])}) :="
        )
        glue_lines.append(
            f"    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_{k - 1} hc_{k}"
        )
    glue_lines.append(f"  exact h_{len(cells) - 1}")
    glue_lines.append("")
    glue_lines.append("end GWSpeedCertificate.Certs\n")
    (certs_dir / "AllCells.lean").write_text("\n".join(glue_lines), encoding="utf-8")
    print(f"Wrote {len(batch_names)} batch files + AllCells.lean to {certs_dir}")
    print("Batch pair loads:", [sum(c["pairs"] for c in bc) for bc in batch_cells])


if __name__ == "__main__":
    main()
