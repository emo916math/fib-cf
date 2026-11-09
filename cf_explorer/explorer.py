"""Exact exploration of powers of recurrence convergents (SageMath).

Indices follow TwoPoint(3): J_i lies between P_{i-1} and P_i,
0 <= i <= k. Words are tuples; () denotes an absent patch/empty junction.
See README.md for conventions, hypotheses, and examples.
"""
from sage.all import (ZZ, QQ, AA, PolynomialRing, QuadraticField, matrix,
                      vector, identity_matrix, gcd, lcm, Integers,
                      continued_fraction, ceil)
from functools import lru_cache
from typing import NamedTuple

__all__ = ['recurrence_pair', 'power_cf', 'delta_polynomial',
           'Delta_polynomial', 'Delta', 'lattice_index', 'junction',
           'junction_modulus', 'all_junctions', 'PJP', 'MonsterJunctionError']

class MonsterJunctionError(ValueError):
    """The requested J_i is a monster (Delta_{k,i}=0)."""

class PJP(NamedTuple):
    left: tuple
    junction: tuple
    right: tuple


def _indices(k, i):
    k, i = ZZ(k), ZZ(i)
    if k < 1 or not 0 <= i <= k:
        raise ValueError('Require k >= 1 and 0 <= i <= k')
    return k, i


def recurrence_pair(a, b, n):
    """Return (u_{n+1},u_n), with u_0=0,u_1=1, using matrix powering."""
    a, b, n = map(ZZ, (a, b, n))
    if n < 0:
        raise ValueError('Require n >= 0')
    return tuple((matrix(ZZ, [[a,b],[1,0]])**n).column(0))


def power_cf(a, b, k, n):
    """Canonical finite CF of (u_{n+1}/u_n)^k; the final digit is >1.

    Unlike junction(), this allows arbitrary integral a,b and k>=1.
    A zero denominator raises ZeroDivisionError.
    """
    k, _ = _indices(k, 0)
    p, q = recurrence_pair(a, b, n)
    if not q:
        raise ZeroDivisionError('u_n is zero')
    return tuple(continued_fraction((QQ(p)/q)**k))


def _determinant(k, i, a, b, base):
    R = PolynomialRing(base, 'x')
    x = R.gen()
    coefficients = (x*x-a*x-b)**i
    return matrix(base, k-i, k-i,
                  lambda row,col: coefficients[i+row-col]
                  if 0 <= i+row-col <= 2*i else 0).det()


@lru_cache(None)
def delta_polynomial(k, i):
    """Monic delta_{k,i}(t), computed by expanding (x^2-t*x-t)^i."""
    k, i = _indices(k, i)
    R = PolynomialRing(ZZ, 't')
    t = R.gen()
    weight = i*(k-i)
    raw = _determinant(k, i, t, t, R)
    quotient, remainder = raw.quo_rem(t**((weight+1)//2))
    assert not remainder
    return (-1)**weight * quotient


@lru_cache(None)
def Delta_polynomial(k, i):
    """Delta_{k,i}(a,b) in ZZ[a,b], with the paper's sign convention."""
    k, i = _indices(k, i)
    R = PolynomialRing(ZZ, names=('a','b'))
    a, b = R.gens()
    weight = i*(k-i)
    d = weight//2
    return (-a if weight % 2 else R(1))*sum(
        c*a**(2*j)*b**(d-j)
        for j,c in enumerate(delta_polynomial(k,i)))


def Delta(a, b, k, i):
    """Evaluate the Padé--Toeplitz determinant."""
    return ZZ(Delta_polynomial(k,i)(ZZ(a),ZZ(b)))


@lru_cache(None)
def _field(a,b):
    a,b = ZZ(a),ZZ(b)
    D = a*a+4*b
    if a <= 0 or b == 0 or D <= 0 or D.is_square():
        raise ValueError('Junctions require a>0, b!=0, and positive nonsquare a^2+4*b')
    K = QuadraticField(D, 'sqrtD', embedding=AA(D).sqrt())
    return K,(a+K.gen())/2


@lru_cache(None)
def _basis(a,b,k,i):
    """Saturated integral basis of V_{k,i}; no neighboring spaces needed."""
    k,i = _indices(k,i)
    R = PolynomialRing(ZZ,'x'); x=R.gen()
    h = x*x-a*x-b
    if not i:
        return ((R(1),R(0)),(R(0),R(1)))
    remainders = [x**(k+j) % h**i for j in range(i+1)]
    equations = matrix(ZZ, max(i-1,0), i+1,
                       lambda row,col: remainders[col][i+1+row])
    basis = equations.right_kernel().basis()
    if len(basis) != 2:
        raise ArithmeticError('Unexpected dimension of the Padé space')
    return tuple((x**k*R(list(v)) % h**i, R(list(v))) for v in basis)


@lru_cache(None)
def lattice_index(a,b,k,i):
    """tilde-Delta_{k,i}: index of the leading-coefficient lattice."""
    k,i = _indices(k,i)
    if not Delta(a,b,k,i):
        raise MonsterJunctionError('J_%s is a monster' % i)
    pairs = _basis(ZZ(a),ZZ(b),k,i)
    return abs(matrix(ZZ, [[P[i] for P,Q in pairs],
                          [Q[i] for P,Q in pairs]]).det())


def _scalar_rank(a,b,d):
    """Least m>0 for d|u_m, assuming gcd(b,d)=1; factor/order method."""
    d = abs(ZZ(d))
    if d == 1:
        return ZZ(1)
    if gcd(b,d) != 1:
        raise ValueError('Rank requires gcd(b,d)=1')
    C = matrix(Integers(d),[[a,b],[1,0]])
    bound = lcm([p**e*(p*p-1) for p,e in d.factor()])
    assert (C**bound)[1,0] == 0
    for p,e in bound.factor():
        for _ in range(e):
            if (C**(bound//p))[1,0]:
                break
            bound //= p
    return ZZ(bound)


@lru_cache(None)
def _pade_coefficients(a,b,k,i):
    """Phi_i of Lemma lem:Phi: entry [j][c][l] is the X^(i-l)Y^l coefficient."""
    pairs = _basis(ZZ(a),ZZ(b),k,i)
    B = [[pairs[0][r], pairs[1][r]] for r in (0,1)]
    leading = matrix(QQ, [[B[r][c][i] for c in (0,1)] for r in (0,1)]).inverse()
    return [[[sum(B[j][s][i-l]*leading[s,c] for s in (0,1)) for l in range(i+1)]
             for c in (0,1)] for j in (0,1)]


def _minor_denominator(Phi, scale):
    """c(Phi(X, scale*Y)): least common denominator of the 2x2 minors."""
    i = len(Phi[0][0])-1
    M = matrix(QQ, [[Phi[j][c][l]*scale**l for c in (0,1)]
                    for j in (0,1) for l in range(i+1)])
    return lcm([m.denominator() for m in M.minors(2)])


def junction_modulus(a,b,k,i, oriented=False):
    """An admissible candidate m_i (not necessarily the smallest word period).

    For b=+-1: rank of apparition of tilde-Delta_{k,i}.
    Otherwise require t=a^2/b integral and use Exercise exer:main_gen(c):
      the least even 2m with
      lcm{c(Phi_i(X,aY/b)), c(Phi_i(X,Y/a))/t^i} | u_{2m}/(a b^(m-1)).
    With oriented=True retain parity beside monsters when b=1.
    The recipe is conservative, especially next to monsters. m_0=1.
    """
    a,b=ZZ(a),ZZ(b)
    k,i=_indices(k,i)
    _field(a,b)
    d = lattice_index(a,b,k,i)
    if abs(b)==1:
        rank=_scalar_rank(a,b,d)
        beside_monster=any(not Delta(a,b,k,j) for j in (i-1,i+1) if 0<=j<=k)
        return lcm(2,rank) if oriented and b==1 and beside_monster else rank
    if a*a % abs(b):
        raise NotImplementedError('A periodic modulus is only provided when b divides a^2')
    if i==0:
        return ZZ(1)
    t=a*a//b
    Phi=_pade_coefficients(a,b,k,i)
    modulus=lcm(QQ(_minor_denominator(Phi,QQ(a)/b)),
                QQ(_minor_denominator(Phi,1/QQ(a)))/t**i)
    if modulus.denominator()!=1:
        raise ArithmeticError('Non-integral modulus %s' % modulus)
    # v_m = u_{2m}/(a b^(m-1)) satisfies v_m = (t+2) v_{m-1} - v_{m-2}.
    return 2*_scalar_rank(t+2,-1,ZZ(modulus))


def _word_matrix(word):
    M=identity_matrix(ZZ,2)
    for digit in word:
        M *= matrix(ZZ,[[digit,1],[1,0]])
    return M


def _rotate_left(P):
    return P[1:]+P[:1]


def _rotate_right(P):
    return P[-1:]+P[:-1]


def _least_rotation(P):
    return min(P[j:]+P[:j] for j in range(len(P)))


def _normalize(L,J,R):
    """Move the left boundary first, then shorten against the right period.

    P[0] is the next predicted digit, not the preceding P[-1].
    Empty visible junctions between unequal cycles are allowed.
    """
    L,J,R = tuple(L),tuple(J),tuple(R)
    if L:
        while J and J[0]==L[0]:
            L,J=_rotate_left(L),J[1:]
        if not J and R:
            # Continue through the right periodic tail to the first mismatch.
            # Equal infinite tails are precisely an invisible junction.
            seen=set()
            while L[0]==R[0]:
                state=(L,R)
                if state in seen:
                    P=_least_rotation(L)
                    return PJP(P,(),P)
                seen.add(state)
                L,R=_rotate_left(L),_rotate_left(R)
    while J and R and J[-1]==R[-1]:
        J,R=J[:-1],_rotate_right(R)
    return PJP(L,J,R)


def _alternate(W):
    if not W:
        return W
    if len(W)==1 or W[-1]>1:
        return W[:-1]+(W[-1]-1,1)
    if len(W)>1:
        return W[:-2]+(W[-2]+1,)
    return W


def _finite_end(L,W):
    candidates=[_normalize(L,W,()),_normalize(L,_alternate(W),())]
    return min(candidates,key=lambda z:(len(z.junction),z))


def _endpoints(a,b,k,i,n):
    K,alpha=_field(a,b)
    pairs=_basis(a,b,k,i)
    R=pairs[0][0].parent(); x=R.gen(); h=x*x-a*x-b
    errors=[(x**k*Q-P)//h**i for P,Q in pairs]
    qrow=[Q(alpha) for P,Q in pairs]
    erow=[E(alpha) for E in errors]
    p,q=recurrence_pair(a,b,n)
    H=matrix(K,[[sum(P[j]*p**j*q**(i-j) for j in range(i+1)) for P,Q in pairs],
                [sum(Q[j]*p**j*q**(i-j) for j in range(i+1)) for P,Q in pairs]])
    return H*vector(K,[qrow[1],-qrow[0]]), H*vector(K,[erow[1],-erow[0]])


def _rational(v):
    return not v[1] or v[0]/v[1] in QQ


def _greater_one(v):
    return v[1]!=0 and v[0]/v[1]>1


def _right_data(v):
    cf=(v[0]/v[1]).continued_fraction()
    return tuple(cf.preperiod()),tuple(cf.period())


def _cusp_side(a,b,k,level,n,pairs,coefficients):
    """Sign of target minus the monster's rational Padé approximant.

    The sign is evaluated near alpha, so it is valid asymptotically even
    when the requested representative n is small. Even local transports
    preserve this orientation. No large recurrence index is needed.
    """
    c=(vector(QQ,[-coefficients[1]/coefficients[0],1])
       if coefficients[0] else vector(QQ,[1,0]))
    P=sum(c[j]*pairs[j][0] for j in range(2))
    Q=sum(c[j]*pairs[j][1] for j in range(2))
    common=P.gcd(Q)
    P,Q=P//common,Q//common
    x=P.parent().gen(); h=x*x-a*x-b
    E,rem=(x**k*Q-P).quo_rem(h**level)
    assert not rem
    alpha=_field(a,b)[1]
    return (E(alpha)/Q(alpha)).sign()*((-b)**(n*level)).sign()


def _after_cusp(v,w,side):
    """Remove the unbounded integer part in the correctly oriented chart."""
    if not v[1]:
        charts=[identity_matrix(ZZ,2),matrix(ZZ,[[-1,0],[0,1]])]
    else:
        W=tuple(continued_fraction(QQ(v[0]/v[1])))
        charts=[_word_matrix(W),_word_matrix(_alternate(W))]
    H=next(C for C in charts if -C.det()==side)
    tail=H.inverse()*w
    if not tail[1]:
        raise ArithmeticError('Coincident rational cusps')
    value=tail[0]/tail[1]
    fraction=value-value.floor()
    if not fraction:
        return PJP((),(),())
    cf=(1/fraction).continued_fraction()
    return _normalize((),tuple(cf.preperiod()),tuple(cf.period()))


def junction(a,b,k,i,n=0, max_steps=10000):
    """Return PJP(left, junction, right) for the asymptotic junction J_{i,n}.

    n is a class representative, not a demand to see full patches in the
    finite CF at small n. Each patch is its primitive period. A missing
    patch at a boundary or monster is (). J_i itself a monster raises
    MonsterJunctionError. Ordinary cases use exact quadratic CF reduction
    at n, with no finite-CF sampling or guessed stability thresholds.
    """
    a,b,n=ZZ(a),ZZ(b),ZZ(n)
    k,i=_indices(k,i)
    _field(a,b)
    if n<0:
        raise ValueError('Require n >= 0')
    if not Delta(a,b,k,i):
        raise MonsterJunctionError('J_%s is a monster (Delta_{%s,%s}=0)' % (i,k,i))
    if i==0:
        alpha=_field(a,b)[1]
        cf=(alpha**k).continued_fraction()
        return _normalize((),tuple(cf.preperiod()),tuple(cf.period()))
    v,w=_endpoints(a,b,k,i,n)
    if _rational(v):
        pairs=_basis(a,b,k,i)
        alpha=_field(a,b)[1]
        side=_cusp_side(a,b,k,i-1,n,pairs,[Q(alpha) for P,Q in pairs])
        return _after_cusp(v,w,side)
    left_repeller=v[0]/v[1]
    left_attractor=left_repeller.trace()-left_repeller
    cf=left_attractor.continued_fraction()
    L=tuple(cf.period())
    H=_word_matrix(tuple(cf.preperiod()))
    transform=H.inverse()
    tail=transform*w
    M=_word_matrix(L)
    for _ in range(max_steps):
        if _greater_one(tail):
            break
        tail=M*tail
        transform=M*transform
    else:
        raise ArithmeticError('Quadratic reduction exceeded max_steps')
    if _rational(w):
        W=tuple(continued_fraction(QQ(tail[0]/tail[1])))
        if i==k:
            return _finite_end(L,W)
        # The next junction is a monster. Its positive digit selects one
        # side of the rational cusp; a shorter alternate CF may be wrong.
        pairs=_basis(a,b,k,i)
        ring=pairs[0][0].parent(); x=ring.gen(); h=x*x-a*x-b
        alpha=_field(a,b)[1]
        es=[((x**k*Q-P)//h**i)(alpha) for P,Q in pairs]
        side=_cusp_side(a,b,k,i+1,n,pairs,es)*transform.det().sign()
        if -_word_matrix(W).det()!=side:
            W=_alternate(W)
        return _normalize(L,W,())
    J,R=_right_data(tail)
    return _normalize(L,J,R)


def all_junctions(a,b,k, max_classes=10000):
    """Enumerate every non-monster J_i over the candidate modulus m_i.

    Return rows with arithmetic_modulus, oriented modulus, and classes.
    classes maps each distinct PJP to its tuple of residues.
    Equal normalized triples are grouped; monsters are omitted. Guard
    against large nonunit moduli before enumeration (None disables guard).
    """
    k,_=_indices(k,0)
    moduli={i:junction_modulus(a,b,k,i,oriented=True) for i in range(k+1) if Delta(a,b,k,i)}
    total=sum(moduli.values())
    if max_classes is not None and total>max_classes:
        raise ValueError('Enumeration needs %s residue classes; increase max_classes or call junction individually' % total)
    result={}
    for i,m in moduli.items():
        groups={}
        for n in range(m):
            triple=junction(a,b,k,i,n)
            groups.setdefault(triple,[]).append(n)
        result[i]={'arithmetic_modulus':junction_modulus(a,b,k,i),'modulus':m,'classes':{p:tuple(rs) for p,rs in groups.items()}}
    return result
