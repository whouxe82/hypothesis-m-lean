"""Exact reconstruction of xi mod 2^N and of the Corollary 2 certificate r_L^2 >= 2^L, 2 <= L <= N.
Timing goes to stderr, so stdout is deterministic.
Method independent of hypm_check.py: the inverse-parity series xi = -sum_i 2^{p_i} / 3^{i+1},
p_i = floor(i*log2 3) = bitlength(3^i) - 1 (exact), evaluated in Z/2^N Z.  Claude, 25 Oct 2026."""
import sys, hashlib, time
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
t0 = time.time()
# positions p_i < N, exactly
ps = []; p3 = 1; i = 0
while True:
    p = p3.bit_length() - 1
    if p >= N: break
    ps.append(p); p3 *= 3; i += 1
I = len(ps)
# S = sum_i 2^{p_i} 3^{I-1-i}  (Horner), then xi = -S * 3^{-I} mod 2^N
S = 0
for p in ps:
    S = S*3 + (1 << p)
MOD = 1 << N
xi = (-S * pow(3, -I, MOD)) % MOD
print(f"N={N}: {I} odd positions")
print(f"xi computed in {time.time()-t0:.1f}s", file=sys.stderr)
print("xi mod 2^64 =", hex(xi & ((1 << 64) - 1)))
print("SHA-256 of xi mod 2^N (little-endian bytes):", hashlib.sha256(xi.to_bytes((N+7)//8, 'little')).hexdigest())
bits = [(xi >> j) & 1 for j in range(N)] if N <= 200000 else None
# positions of one-bits
s = bin(xi)[2:][::-1]  # s[j] = bit j
ones = [j for j, c in enumerate(s) if c == '1']
# certificate: for each L, r_L = xi mod 2^L; need r_L^2 >= 2^L.
# h(L) = highest one-bit index < L.  r_L >= 2^h, r_L < 2^(h+1).
import bisect
fails = []; exact_checks = 0
for L in range(2, N+1):
    idx = bisect.bisect_left(ones, L) - 1
    h = ones[idx]
    if 2*h >= L: continue            # r_L >= 2^h with 2h >= L
    if 2*h + 2 <= L: fails.append(L); continue   # r_L < 2^(h+1), (h+1)*2 <= L
    # 2h + 1 == L: compare exactly
    exact_checks += 1
    rL = xi & ((1 << L) - 1)
    if rL*rL < (1 << L): fails.append(L)
print(f"certificate r_L^2 >= 2^L for 2<=L<={N}: failures={fails[:10]} (count {len(fails)}); exact comparisons needed: {exact_checks}")
# zero runs: z_k <= k-1 for k with 2k-1 < N, and M(k) - k records
def z(k):
    idx = bisect.bisect_left(ones, k)
    return ones[idx] - k
K = (N - 1)//2
rec = []; best = -1; viol = 0
for k in range(2, K):
    zk = z(k)
    if zk > k - 1: viol += 1
    if zk + 1 > best: best = zk + 1; rec.append((k, best))
print(f"zero runs z_k <= k-1 for 2<=k<{K}: violations={viol}")
print("records of M(k)-k = z_k + 1:", rec)
frac = sum(1 for k in range(2, K) if s[k] == '1') / (K - 2)
print(f"fraction of k in [2,{K}) with xi_k = 1 (M(k) = k+1): {frac:.5f}")
print(f"total time {time.time()-t0:.1f}s", file=sys.stderr)
# Theorem 4 per exact bit length b (Corollary N3 / Cor. 21 formula), for b < K
qs = [1, 2, 3, 8, 19, 65, 84, 485, 1054, 24727, 50508, 125743, 176251, 301994, 16785921]
bad = 0; cnt = 0
for m in range(len(qs) - 1):
    for b in range(qs[m] + 4, min(qs[m+1] - 4, K - 1) + 1):
        cnt += 1
        mx = b + 1 + z(b) if s[b-1] == '1' else b
        if mx > b + qs[m] + 3: bad += 1
print(f"Theorem 4 at {cnt} eligible bit lengths b < {K}: violations={bad}")
# Exact count of one-digits, and z_k <= k-2 for k >= 3 (the improvement after Corollary 21)
print(f"one-digits xi_k = 1 for 2<=k<{K}: {sum(1 for k in range(2, K) if s[k] == '1')} of {K-2}")
print(f"z_k <= k-2 for 3<=k<{K}: violations={sum(1 for k in range(3, K) if z(k) > k-2)}")
# Lemma 11 with exact critical word: floor(j*alpha) = max{a : 3^a <= 2^j}
J = qs[10] + qs[9] + 5
Qc = [0]; a_ = 0; p3_ = 1
for j in range(1, J + 1):
    while p3_ * 3 <= (1 << j): p3_ *= 3; a_ += 1
    Qc.append(a_ + 1)
e = [None] + [Qc[j] - Qc[j-1] for j in range(1, J + 1)]
for m in range(1, 10):
    q, q1 = qs[m], qs[m+1]
    inside = all(e[t] == e[t+q] for t in range(2, q1))
    print(f"Lemma 11 q={q}, q_next={q1}: holds for 2<=t<={q1-1}: {inside}; "
          f"at t={q1}: {e[q1] == e[q1+q]}; at t=1: {e[1] == e[1+q]}")
