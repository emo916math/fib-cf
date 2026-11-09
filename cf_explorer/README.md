# Continued-fraction explorer

A self-contained SageMath library for exploring
`(u_(n+1)/u_n)^k`, where `u_0=0`, `u_1=1`, and
`u_(n+2)=a*u_(n+1)+b*u_n`. No third-party dependencies beyond SageMath.
Tested with SageMath 10.7.

The notation follows `TwoPoint(3).tex`: junctions are `J_0,...,J_k`,
patches are `P_0,...,P_(k-1)`, and `J_i` lies between `P_(i-1)` and `P_i`.
The Toeplitz determinant is `Delta`; the leading-coefficient lattice index
is `lattice_index` (the paper's tilde-Delta). These are different quantities.

## Start

Extract the archive, start Sage in the directory containing `cf_explorer`,
and enter:

```python
from cf_explorer import *
```

From another working directory, add the directory containing `cf_explorer`
to Python's `sys.path` before importing. The implementation is ordinary
Python importing Sage, so it also works with `sage -python`.

## The five tasks

### (0) Direct continued fractions

```python
power_cf(1, 1, 5, 7)
# (10, 1, 3042, 2, 1, 1, 2, 9)
recurrence_pair(1, 1, 20)
# (10946, 6765)
```

Words are tuples of digits. The first digit is the integer part.
`power_cf` uses the canonical finite expansion with final digit greater
than 1 (apart from one-digit integer expansions). It accepts integral
`a,b`, `k>=1`, and `n>=0`; a zero `u_n` raises `ZeroDivisionError`.

### (1) Determinant polynomials

```python
delta_polynomial(5, 2)
# t^3 + 2*t^2 + 3*t - 6
Delta_polynomial(5, 2)
# a^6 + 2*a^4*b + 3*a^2*b^2 - 6*b^3
Delta(1, 1, 5, 2)
# 0
lattice_index(1, 1, 5, 1)
# 5
```

The algorithm expands `(x^2-t*x-t)^i`, forms the `(k-i)`-square central
Toeplitz matrix, and takes its determinant. With `w=i*(k-i)`, dividing
that determinant by `t^ceil(w/2)` and multiplying by `(-1)^w` gives the
monic `delta`. Weighted homogenization gives `Delta(a,b)` with the paper's
sign convention. There is no trinomial-coefficient summation.
Both boundary determinants equal 1.

### (2) One normalized junction and its neighboring patches

```python
junction(1, 1, 3, 1, 0)
# PJP(left=(4,), junction=(3, 2, 3), right=(4,))
junction(1, 1, 3, 1, 2)
# PJP(left=(4,), junction=(10,), right=(4,))
junction(1, 1, 3, 2, 0)
# PJP(left=(4,), junction=(2, 2), right=(1,))
junction(1, 1, 4, 3, 0)
# PJP(left=(11,), junction=(), right=(11,))
junction(1, 1, 3, 3, 0)
# PJP(left=(1,), junction=(), right=())
junction(1, 1, 5, 1, 0)
# PJP(left=(11,), junction=(10, 1, 1), right=())
junction(1, 1, 5, 3, 0)
# PJP(left=(), junction=(1, 17), right=(11,))
```

`PJP` is an immutable, hashable named tuple: unpack it as `L,J,R` or use
`.left`, `.junction`, and `.right`. Patches are *primitive periods*, not
repetition counts. An empty patch means a boundary or an adjacent monster.
`junction(1,1,5,2)` raises `MonsterJunctionError` because `J_2` itself is a
monster. Monsters elsewhere do not prevent computation.

`n` is a nonnegative representative of an asymptotic class. The result
need not be visible in the finite CF at that small index. It is computed
from exact local data at `n`, not by searching larger indices.

Normalization:

* Extend the left patch through matching digits, rotating its period as
  each digit is absorbed. Stop at the first departure from its periodic
  continuation. Thus the comparison is with `L[0]`, the *next predicted*
  digit, not `L[-1]`, the preceding digit.
* Absorb the longest possible suffix into the right patch, rotating that
  patch accordingly. This can leave an empty visible junction between
  unequal periods. The left-first convention resolves overlaps.
* An invisible junction has empty middle word and equal periods, both
  rotated to the lexicographically least word.
* At the initial or terminal boundary, absorb into the one available
  patch. At the terminal boundary, consider both positive finite CF
  expansions and take the shortest middle word (lexicographic tie-break).
* Before a monster, the side of approach determines the finite CF
  expansion; choosing the other expansion can force a negative monster.
  Only the valid positive expansion is shortened. After a monster, its
  integer part is absorbed into the monster, and the remaining middle
  word is shortened against the right patch.

Adjacent calls can therefore return different rotations of the same
patch. These triples are local descriptions; do not concatenate them
without reconciling phases and repetition counts.

### (3) A candidate modulus

```python
junction_modulus(1, 1, 3, 1)
# 3
junction_modulus(1, 1, 5, 1)
# 5
junction_modulus(1, 1, 5, 1, oriented=True)
# 10
junction_modulus(2, 2, 3, 1)
# 12
```

For `b=+1` or `b=-1`, the default is exactly the rank of apparition of
`lattice_index(a,b,k,i)`. It is found by modular matrix powering and
prime-factor stripping, rather than storing the recurrence's entire
orbit. The index comes from the saturated integral Padé space.

There is a necessary distinction next to monsters: the arithmetic rank
need not be a period of the *positive digit words*. For Fibonacci fifth
powers, both `J_1` and `J_3` have lattice index 5 and rank 5, but their
positive words can depend on parity. For example:

```python
junction(1, 1, 5, 1, 0).junction  # (10, 1, 1)
junction(1, 1, 5, 1, 5).junction  # (10, 2)
```

`oriented=True` retains this parity: for `b=1` and a neighboring monster
it returns `lcm(2,rank)`. For ordinary junctions and `b=-1` it returns the
rank unchanged. The enumeration function uses this oriented value.

For `|b|>1`, the provided recipe requires `t=a^2/b` integral and follows
Exercise `exer:main_gen`(c) of the paper. Let `Phi_i(X,Y)` be the
normalized Padé matrix (`Phi_i(1,0)=I`) and `c(A)` the least common
denominator of the 2x2 minors of the coefficient matrix of `A`. With
`N = lcm{c(Phi_i(X,aY/b)), c(Phi_i(X,Y/a))/t^i}`, we return the least
even `2m` with `N | u_{2m}/(a b^(m-1))`, using the auxiliary recurrence
`v_m = (t+2)v_{m-1} - v_{m-2}`.
`m_0=1`. It is conservative and can be very large; it is not
claimed to be the minimal word period. Near monsters, it is used as a
candidate for the same local arithmetic, not as a new proof of a general
monster-inclusive decomposition theorem.

### (4) All non-monster junctions

```python
table = all_junctions(1, 1, 5)
for i, row in table.items():
    print('J', i, 'modulus', row['modulus'])
    for triple, residues in row['classes'].items():
        print(residues, triple)
```

The result is indexed by junction number; monster indices are omitted.
Each row contains `arithmetic_modulus`, the default candidate,
`modulus`, the oriented enumeration modulus, and `classes`, a mapping
from distinct normalized PJP triples to their residue classes. Repeated
triples are grouped without discarding their residues.

By default enumeration refuses to exceed 10,000 total residue classes.
Use `max_classes=...` to raise this limit, or `None` to disable it.
For large nonunit examples, inspect individual junctions first.

## Exact local construction

Only the single space `V_(k,i)` is needed. A saturated integer kernel
produces pairs `(P_j,Q_j)` of degree at most `i` satisfying
`x^k Q_j-P_j = h^i E_j`. Homogeneous evaluation at `(u_(n+1),u_n)` gives
a two-column matrix `H`. The ordered projective points

```
H * kernel(Q_1(alpha), Q_2(alpha))
H * kernel(E_1(alpha), E_2(alpha))
```

are the incoming repelling point and outgoing attracting point. Reduce
the conjugate of the first by its exact quadratic continued fraction,
and then reduce the second in the same integral coordinates. Rational
points give boundaries next to monsters. The sign of the Padé error
selects the correct side of each rational cusp. No global transition
factorization, numerical fitting, or large-index sampling is required.
In a real quadratic Sage field, algebraic conjugation is computed as
`z.trace()-z`; complex conjugation would fix `z`.

## Scope and verification

Junction computations require integral `a>0`, nonzero `b`, `k>=1`, and
positive nonsquare `a^2+4*b`. Modulus/enumeration additionally requires
`b|a^2`. The local quadratic construction can be evaluated outside that
last hypothesis, but does not assert a periodic decomposition there.

Run the independent tests from the directory containing the package:

```bash
sage -python -m unittest discover -s cf_explorer -v
```

Tests cover symbolic determinant identities through `k=8`, lattice
indices, minimal ranks and nonunit divisibility, exact known junctions,
periodicity, enumeration, and comparison with directly computed rational
CFs at indices 200 through 209 for nine recurrence/power combinations,
including several non-Fibonacci monsters. Development also cross-checked
ordinary junctions against the supplied `patch_period.sage` extractor;
that old file is not a dependency of this package.
