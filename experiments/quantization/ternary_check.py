"""Sanity check: how well does a quantized-input path act as the nested-MLMC control variate?
Haas-Giles test case: GBM, r=0.05, sigma=0.2, T=1, Euler-Maruyama, h_l = T/2^l, coarse path per
their eq.(5) (= coarse EM driven by summed fine increments). Arithmetic in double: only the
*inputs* Z are quantized, Zt = q(Z) (monotone/inverse-CDF coupling, as in the paper).
Reports v_l = V[dP_l - dPt_l] / V[dP_l]; nested per-level factor >= sqrt(v_l) however cheap Zt is."""
import numpy as np
from scipy.special import ndtri, ndtr
from scipy.stats import norm

r, sig, T, S0, K = 0.05, 0.2, 1.0, 1.0, 1.0
n = 400_000
Lmax = 7
rng = np.random.default_rng(2025)

def centroid_q(thr):
    edges = np.concatenate(([-np.inf], thr, [np.inf]))
    p = ndtr(edges[1:]) - ndtr(edges[:-1])
    pdf = norm.pdf(edges)
    vals = (pdf[:-1] - pdf[1:]) / p
    mse = 1.0 - np.sum(p * vals**2)
    return thr, vals, mse

def method1(d):                        # paper's Method 1: 2^d uniform-probability intervals
    return centroid_q(ndtri(np.arange(1, 2**d) / 2**d))

def lloyd_max(k, it=2000):
    thr = ndtri(np.arange(1, k) / k)
    for _ in range(it):
        _, vals, _ = centroid_q(thr)
        thr = 0.5 * (vals[:-1] + vals[1:])
    return centroid_q(thr)

def mm_ternary():                      # Kloeden-Platen 3-point = 3-pt Gauss-Hermite: {-sqrt3,0,sqrt3} w.p. 1/6,2/3,1/6
    thr = ndtri(np.array([1/6, 5/6])); vals = np.array([-np.sqrt(3), 0.0, np.sqrt(3)])
    p = np.array([1/6, 2/3, 1/6])
    Ezq = 2*np.sqrt(3)*norm.pdf(thr[1])
    mse = 1 - 2*Ezq + np.sum(p*vals**2)
    return thr, vals, mse

def q(z, Q): return Q[1][np.searchsorted(Q[0], z)]

QS = [("ternary moment-matched (1/6,2/3,1/6)", 1.585, mm_ternary(), False),
      ("ternary Lloyd-Max (MSE-optimal)",      1.585, lloyd_max(3), False),
      ("ternary Lloyd-Max + error feedback",   1.585, lloyd_max(3), True)]
for d in (1, 2, 3, 4, 6, 8, 10, 12):
    QS.append((f"paper Method 1, d={d:2d} bits", d, method1(d), False))

payoffs = {"call":    lambda S: np.maximum(S - K, 0.0),
           "linear":  lambda S: S,
           "digital": lambda S: (S > K).astype(float)}

res = {}   # (qname, payoff) -> list of v_l
for l in range(Lmax + 1):
    N = 2**l; h = T / N; sh = np.sqrt(h)
    Sf = np.full(n, S0); Sc = np.full(n, S0)
    A = {nm: [np.full(n, S0), np.full(n, S0), np.zeros(n)] for nm, *_ in QS}   # Sf~, Sc~, feedback err
    if l == 0:
        Z = rng.standard_normal(n)
        Sf *= 1 + r*h + sig*sh*Z
        for nm, _, Q, ef in QS:
            A[nm][0] *= 1 + r*h + sig*sh*q(Z, Q)
    else:
        for _ in range(N // 2):
            Za = rng.standard_normal(n); Zb = rng.standard_normal(n)
            Sf *= 1 + r*h + sig*sh*Za; Sf *= 1 + r*h + sig*sh*Zb
            Sc *= 1 + 2*r*h + sig*sh*(Za + Zb)
            for nm, _, Q, ef in QS:
                st = A[nm]
                if ef:
                    ta = q(Za + st[2], Q); st[2] = Za + st[2] - ta
                    tb = q(Zb + st[2], Q); st[2] = Zb + st[2] - tb
                else:
                    ta = q(Za, Q); tb = q(Zb, Q)
                st[0] *= 1 + r*h + sig*sh*ta; st[0] *= 1 + r*h + sig*sh*tb
                st[1] *= 1 + 2*r*h + sig*sh*(ta + tb)
    for pn, f in payoffs.items():
        dP = f(Sf) - (f(Sc) if l > 0 else 0.0)
        for nm, *_ in QS:
            dPt = f(A[nm][0]) - (f(A[nm][1]) if l > 0 else 0.0)
            V = dP.var(); VD = (dP - dPt).var()
            res.setdefault((nm, pn), []).append(VD / V if V > 0 else np.nan)

hdr = "".join(f"  l={l}" for l in range(Lmax + 1))
for pn in payoffs:
    print(f"\n=== payoff: {pn}   v_l = V[dP - dP~]/V[dP]   (speedup cap = 1/v, per-level factor >= sqrt(v)) ===")
    print(f"{'input quantizer':40s} {'bits':>5s} {'MSE':>8s} {'2*MSE':>7s}{hdr}")
    for nm, bits, Q, ef in QS:
        row = "".join(f" {x:6.3f}" if x >= 1e-3 else f" {x:6.0e}" for x in res[(nm, pn)])
        print(f"{nm:40s} {bits:5.2f} {Q[2]:8.2e} {2*Q[2]:7.1e}{row}")
