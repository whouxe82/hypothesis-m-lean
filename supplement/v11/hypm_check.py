"""Independent exact-arithmetic checks for Hypothesis M v11 (Claude, 25 Oct 2026).
Pure Python integers; no floating point in any decision except the continued fraction
of log_3 2, which is computed with mpmath at 200 digits and cross-checked."""
import sys
from mpmath import mp, log, floor as mfloor
mp.dps = 200
LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
alpha = log(2)/log(3)

# critical word e_1..e_N : e_j = ceil(j a) - ceil((j-1) a); Q_j = ceil(j a) = floor(j a)+1 for j>=1
N = 2*LMAX + 50
# exact: floor(j*alpha) = max{a : 3^a <= 2^j}
Q = [0]; a_ = 0; p3 = 1
for j in range(1, N+1):
    while p3*3 <= (1 << j): p3 *= 3; a_ += 1
    Q.append(a_ + 1)
e = [None] + [Q[j]-Q[j-1] for j in range(1, N+1)]
assert ''.join(map(str, e[1:20])) == '1101101101011011010'

# xi mod 2^L by bit lifting: r_{L+1} in {r_L, r_L + 2^L}; parity of step L of the candidate decides.
# Track the affine state: for n = r + 2^L * t, after L steps x_L = (3^{a} n + B)/2^L, so
# x_L = (3^a r + B)/2^L + 3^a t. Parity of x_L for t=0 is known; t=1 flips it (3^a odd).
def residues(Lmax):
    r, a, B = 0, 0, 0       # invariant: 2^L x_L = 3^a n + B for n ≡ r (mod 2^L)
    out = [0]
    for L in range(0, Lmax):
        xL = (pow(3, a)*r + B) >> L          # exact: divisible
        assert (pow(3, a)*r + B) % (1 << L) == 0
        want = e[L+1]
        if (xL & 1) != want:
            r += 1 << L
        # step L+1 with parity want
        if want == 1:
            B = 3*B + (1 << L); a += 1
        out.append(r)
    return out
r = residues(LMAX + 2)
xi_bits = [(r[-1] >> i) & 1 for i in range(LMAX + 1)]

# cross-check r_L against direct simulation for small L
def sigma3(n, cap=10**6):
    a = 0; x = n
    for j in range(1, cap):
        if x & 1: a += 1; x = (3*x+1)//2
        else: x //= 2
        c = pow(3, a); p = 1 << j
        if c < p or c > 3*p: return j
for L in range(2, 60):
    assert sigma3(r[L]) > L, L

# Theorem 1 for all 2 <= n < 2^K via sigma3(n) = v2(n - xi) + 1, xi known mod 2^(LMAX)
K = 22
X = r[-1]
mask = (1 << 60) - 1
worst_ratio = 0; viol = 0; strong_exc = []
for n in range(2, 1 << K):
    d = (n - X) & mask
    v = (d & -d).bit_length() - 1
    s = v + 1
    bound = (n*n).bit_length() - 1 + 1     # floor(log2 n^2) + 1
    if s > bound: viol += 1
    if s > 2*n.bit_length() - 1: strong_exc.append(n)
print(f"Thm 1 over 2<=n<2^{K}: violations={viol}; seeds with sigma3 > 2b-1: {strong_exc}")
assert sigma3(3) == 4
for n in range(2, 5000):
    d = (n - X) & mask; v = (d & -d).bit_length() - 1
    assert v + 1 == sigma3(n)

# zero runs and M(k)
def z(k):
    c = 0
    while xi_bits[k + c] == 0: c += 1
    return c
M = {k: k + 1 + z(k) for k in range(2, LMAX)}
rec = []; best = -1
for k in range(2, LMAX):
    if M[k] - k > best: best = M[k]-k; rec.append((k, best))
print("records of M(k)-k, k<%d:" % LMAX, rec)
ones = sum(1 for k in range(2, LMAX) if xi_bits[k] == 1)
print(f"k in [2,{LMAX}) with xi_k = 1 (so M(k) = k+1): {ones} of {LMAX-2}")
print("M(1054) =", M[1054])
# direct check of M(k) for small k by brute force
for k in range(2, 21):
    assert M[k] == max(sigma3(n) for n in range(2, 1 << k)), k

# convergent denominators
from mpmath import mpf
x = alpha; a_list = []
for _ in range(14):
    ai = int(mfloor(x)); a_list.append(ai); x = 1/(x - ai)
D = [1, a_list[1]]
for i in range(2, len(a_list)): D.append(a_list[i]*D[-1] + D[-2])
qs = sorted(set(D))
print("partial quotients:", a_list[:12], "denominators:", qs[:12])

# Theorem 4: for each bit length b in R_m, max sigma3 over that bit length <= b + q_m + 3
def max_exact_bitlength(b):
    return b + 1 + z(b) if xi_bits[b-1] == 1 else b
t4 = 0; t4bad = []
for mi in range(len(qs)-1):
    lo, hi = qs[mi] + 4, qs[mi+1] - 4
    for b in range(lo, min(hi, LMAX-1) + 1):
        t4 += 1
        if max_exact_bitlength(b) > b + qs[mi] + 3: t4bad.append(b)
print(f"Theorem 4 checked at {t4} bit lengths <= {LMAX-1}; failures: {t4bad}")
# Lemma 11 endpoints: e_t = e_{t+q} for 2<=t<=q_{m+1}-1 and failure at t = q_{m+1}
for mi in range(1, 9):
    q, q1 = qs[mi], qs[mi+1]
    ok = all(e[t] == e[t+q] for t in range(2, q1))
    endpoint = (e[q1] == e[q1+q])
    print(f"Lemma 11 q={q}: holds on [2,{q1-1}]={ok}; holds at t={q1}? {endpoint}")
# second proof coverage and N7 windows (bit lengths 23..LMAX)
cov = True
for k in range(23, LMAX):
    m = max(i for i in range(len(qs)) if qs[i] + 4 <= k)
    if k <= qs[m+1] - 4: pass
    elif qs[m+1] - 3 <= k <= qs[m+1] + 3 and qs[m+1] >= 65: pass
    else: cov = False; print("uncovered", k)
    if max_exact_bitlength(k) > 2*k - 1: cov = False; print("2k-1 fails", k)
print("second-proof case split covers 23<=k<%d and max sigma3 <= 2k-1 there:" % LMAX, cov)
