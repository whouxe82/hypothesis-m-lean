# Hypothesis M — supplementary computations (versions 11.2–11.5)

Exact-arithmetic checks cited in Section 11.2 of *Sharp Exit Bounds for the Critical Sturmian
Parity Word of the 3x+1 Map, with an Effective 2-adic Approximation Bound*
(W. C. Houze, version 11.5, October 2026).

Every decision in these scripts is made with Python integers. The one numerical step is the
continued fraction of log_3 2 in `hypm_check.py`, computed with mpmath at 200 digits to list
the convergent denominators; the critical word itself is always computed exactly, from
floor(j log_3 2) = max{a : 3^a <= 2^j}. `hypm_certificate.py` uses a fixed list of the
denominators, which `hypm_check.py` reproduces.

| File | What it checks |
|---|---|
| `hypm_check.py` | critical word; residues r_L by bit lifting (L ≤ 20000); Theorem 1 for every 2 ≤ n < 2^22; direct simulation for n < 5000; records of M(k) − k for k < 20000; brute-force M(k) for k ≤ 20; Lemma 11 range and excluded upper endpoint for denominator pairs up to (1054, 24727); Theorem 4 at eligible bit lengths ≤ 19999; coverage of the second proof for 23 ≤ k < 20000 |
| `hypm_certificate.py` | ξ mod 2^(10^6) from the inverse-parity series, p_i = bitlength(3^i) − 1 exactly; certificate r_L^2 ≥ 2^L for 2 ≤ L ≤ 10^6; z_k ≤ k − 1 for 2 ≤ k ≤ 499998 and z_k ≤ k − 2 for 3 ≤ k ≤ 499998; records of M(k) − k for k ≤ 499998; the count of k with ξ_k = 1; Theorem 4 at every eligible bit length ≤ 499998; Lemma 11 range, upper endpoint and t = 1 for every denominator pair up to (24727, 50508) |
| `check_20000.txt` | standard output of `python3 -I hypm_check.py 20000` (about 15 s) |
| `cert_1e6.txt` | standard output of `python3 -I hypm_certificate.py 1000000` (about 75 s; timings go to the terminal, not to the file) |

Not in this folder: the dynamic counts behind Proposition 16 and Remark 17, the exact constants
of Remark 19 and the exhaustive certificate search behind Conjecture 26. These were made in the
version-10 completion round and are described in the archived manuscript in `v10_record/`.

Requirements: Python 3.8 or later; `mpmath` for `hypm_check.py` only (`pip install mpmath`).

Reproduce (both outputs are deterministic):

    python3 -I hypm_check.py 20000 > my_check_20000.txt
    python3 -I hypm_certificate.py 1000000 > my_cert_1e6.txt
    cmp my_check_20000.txt check_20000.txt && cmp my_cert_1e6.txt cert_1e6.txt
    sha256sum -c SHA256SUMS

The SHA-256 of ξ mod 2^(10^6) (little-endian bytes) is printed in `cert_1e6.txt`.
The Lean development, its workflows and the public run records are in the parent repository.
Scripts written by Claude (Anthropic) at the author's direction, 25 October 2026.
