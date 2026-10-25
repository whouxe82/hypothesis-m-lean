# Hypothesis M — supplementary computations for version 11.2

Exact-arithmetic checks cited in Section 11.2 of *Sharp Exit Bounds for the Critical Sturmian
Parity Word of the 3x+1 Map, with an Effective 2-adic Approximation Bound*
(W. C. Houze, version 11.2, October 2026).
All decisions use Python integers; no floating-point value decides any inequality
(the continued fraction of log_3 2 in `hypm_check.py` is computed with mpmath at 200 digits;
the critical word itself is computed exactly, from floor(j log_3 2) = max{a : 3^a <= 2^j}).

| File | What it checks | Run time |
|---|---|---|
| `hypm_check.py` | critical word; residues r_L by bit lifting (L ≤ 20000); Theorem 1 for all 2 ≤ n < 2^22; direct simulation for n < 5000; M(k) records for k < 20000; brute-force M(k) for k ≤ 20; Lemma 11 range and excluded upper endpoint; Theorem 4 at eligible bit lengths ≤ 19999; coverage of the second proof | about 15 s |
| `hypm_certificate.py` | ξ mod 2^(10^6) from the inverse-parity series, with p_i = bitlength(3^i) − 1 exactly; certificate r_L^2 ≥ 2^L for 2 ≤ L ≤ 10^6; z_k ≤ k − 1 for k < 499999; records of M(k) − k; fraction of k with ξ_k = 1; Theorem 4 at eligible bit lengths < 499999 | about 75 s |
| `check_20000.txt` | output of `python3 -I hypm_check.py 20000` | |
| `cert_1e6.txt` | output of `python3 -I hypm_certificate.py 1000000` | |

Requirements: Python 3.8 or later; `mpmath` for `hypm_check.py` only (`pip install mpmath`).

Reproduce:

    python3 -I hypm_check.py 20000 > check_20000.txt
    python3 -I hypm_certificate.py 1000000 > cert_1e6.txt
    sha256sum -c SHA256SUMS

The SHA-256 of ξ mod 2^(10^6) (little-endian bytes) is printed in `cert_1e6.txt`.
The Lean development, its workflows and the public run records are in the parent repository.
Scripts written by Claude (Anthropic) at the author's direction, 25 October 2026.

