"""Second sanity check: Neuron-relevant formats. Same GBM/EM call test + coupling as ternary_check.py.
Low-precision path: arithmetic in FP32 (Neuron Vector/Scalar engines compute in FP32 internally);
we vary (a) the storage format of the random inputs and (b) the storage format of the state S
(rounded after every step, RN or stochastic rounding). Reports v_l = V[dP-dP~]/V[dP] (call payoff)."""
import numpy as np, ml_dtypes
from scipy.special import ndtri, ndtr
from scipy.stats import norm

r, sig, T, S0, K = 0.05, 0.2, 1.0, 1.0, 1.0
n, Lmax = 200_000, 7
rng = np.random.default_rng(7)
f32 = np.float32
BF16, E4M3, E5M2 = ml_dtypes.bfloat16, ml_dtypes.float8_e4m3fn, ml_dtypes.float8_e5m2

def lloyd_max3():
    thr = ndtri(np.array([1/3, 2/3]))
    for _ in range(2000):
        e = np.concatenate(([-np.inf], thr, [np.inf])); p = ndtr(e[1:]) - ndtr(e[:-1])
        vals = (norm.pdf(e[:-1]) - norm.pdf(e[1:])) / p; thr = 0.5*(vals[:-1] + vals[1:])
    return thr, vals
TT, TV = lloyd_max3()

inp = {"exact":   lambda z: z,
       "fp8e4m3": lambda z: z.astype(E4M3).astype(np.float64),
       "fp8e5m2": lambda z: z.astype(E5M2).astype(np.float64),
       "bf16":    lambda z: z.astype(BF16).astype(np.float64),
       "ternary": lambda z: TV[np.searchsorted(TT, z)]}

def st_fp32(x): return x
def st_fp16(x): return x.astype(np.float16).astype(f32)
def st_bf16_rn(x): return x.astype(BF16).astype(f32)
def st_bf16_sr(x):
    b = x.view(np.uint32) + rng.integers(0, 1 << 16, x.shape, dtype=np.uint32)
    return (b & np.uint32(0xFFFF0000)).view(f32)
state = {"fp32": st_fp32, "fp16-RN": st_fp16, "bf16-RN": st_bf16_rn, "bf16-SR": st_bf16_sr}

variants = [("exact", "fp32"), ("exact", "fp16-RN"), ("exact", "bf16-RN"), ("exact", "bf16-SR"),
            ("fp8e4m3", "fp32"), ("fp8e5m2", "fp32"), ("bf16", "fp32"), ("ternary", "fp32"),
            ("ternary", "bf16-SR")]
pay = lambda S: np.maximum(S - K, 0.0)
res = {v: [] for v in variants}
for l in range(Lmax + 1):
    N = 2**l; h = T / N; sh = np.sqrt(h)
    Sf = np.full(n, S0); Sc = np.full(n, S0)
    A = {v: [np.full(n, S0, f32), np.full(n, S0, f32)] for v in variants}
    if l == 0:
        Z = rng.standard_normal(n); Sf *= 1 + r*h + sig*sh*Z
        for v in variants:
            zt = inp[v[0]](Z).astype(f32)
            A[v][0] = state[v[1]]((A[v][0] * (f32(1 + r*h) + f32(sig*sh) * zt)).astype(f32))
    else:
        for _ in range(N // 2):
            Za = rng.standard_normal(n); Zb = rng.standard_normal(n)
            Sf *= 1 + r*h + sig*sh*Za; Sf *= 1 + r*h + sig*sh*Zb
            Sc *= 1 + 2*r*h + sig*sh*(Za + Zb)
            for v in variants:
                qa = inp[v[0]](Za).astype(f32); qb = inp[v[0]](Zb).astype(f32); rd = state[v[1]]
                s = A[v]
                s[0] = rd((s[0] * (f32(1 + r*h) + f32(sig*sh) * qa)).astype(f32))
                s[0] = rd((s[0] * (f32(1 + r*h) + f32(sig*sh) * qb)).astype(f32))
                s[1] = rd((s[1] * (f32(1 + 2*r*h) + f32(sig*sh) * (qa + qb))).astype(f32))
    dP = pay(Sf) - (pay(Sc) if l > 0 else 0.0)
    for v in variants:
        dPt = pay(A[v][0].astype(np.float64)) - (pay(A[v][1].astype(np.float64)) if l > 0 else 0.0)
        res[v].append((dP - dPt).var() / dP.var())

print("call payoff, v_l = V[dP - dP~]/V[dP]  (nested per-level factor >= sqrt(v); speedup cap = 1/v)")
print(f"{'inputs':9s} {'state':8s}" + "".join(f"   l={l}  " for l in range(Lmax + 1)))
for v in variants:
    print(f"{v[0]:9s} {v[1]:8s}" + "".join(f" {x:8.2e}" for x in res[v]))
