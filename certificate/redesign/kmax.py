#!/usr/bin/env python3
"""K_max(gamma) = 1 / (2 (2 C_tail + C_res) C_def(R_0, eps_0, gamma)).

Evaluates the universal constants of Theorem A by running the manuscript's
constants.py (certificate/manuscript_v2/constants.py, unchanged) in a temporary
directory and reusing its functions.  Floating point, as in constants.py; the
Lean side must re-evaluate these constants with upward rounding.
"""
import os, runpy, sys, tempfile
from math import log10

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "manuscript_v2", "constants.py")


def load():
    cwd = os.getcwd()
    with tempfile.TemporaryDirectory() as d:
        os.chdir(d)
        try:
            import io, contextlib
            with contextlib.redirect_stdout(io.StringIO()):
                ns = runpy.run_path(SRC)
        finally:
            os.chdir(cwd)
    return ns


NS = load()


def kmax(gamma):
    R = NS["R0"]
    eps = min(NS["eps_geo"], NS["eps0"](R))
    prod = (2 * NS["C_tail"] + NS["C_res"]) * NS["C_def"](R, eps, gamma)
    return 1 / (2 * prod), prod


if __name__ == "__main__":
    R = NS["R0"]; eps = min(NS["eps_geo"], NS["eps0"](R))
    print(f"R_0 = {R:.4e}, eps = {eps:.4e}, C_tail = {NS['C_tail']:.4e}, C_res = {NS['C_res']:.4e}")
    gs = [float(a) for a in sys.argv[1:]] or [1.37e-4, 1e-4, 1e-5, 1e-6, 1e-8]
    for g in gs:
        k, p = kmax(g)
        print(f"gamma = {g:.3e}:  C_def = {NS['C_def'](R, eps, g):.4e}  "
              f"(2C_tail+C_res) C_def = {p:.4e}  K_max = {k:.4e}  (log10 {log10(k):.2f})")
    # C_def * gamma is constant: K_max(gamma) = kappa * gamma
    k1, _ = kmax(1.0)
    print(f"K_max(gamma) = {k1:.6e} * gamma   (C_def proportional to 1/gamma: "
          f"{NS['C_def'](R, eps, 1e-4) * 1e-4:.6e} vs {NS['C_def'](R, eps, 1e-6) * 1e-6:.6e})")
