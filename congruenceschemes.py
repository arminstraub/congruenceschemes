# -*- coding: iso-8859-1 -*-
"""
Congruence schemes

This package accompanies the paper
    "On congruence schemes for constant terms and their applications"
    by Armin Straub.

AUTHOR:

- Armin Straub (2021/10): Initial implementation

CONTRIBUTIONS:

- The underlying ideas and algorithms for computing congruence schemes were
  first described by Eric Rowland and Reem Yassawi ("Automatic congruences for
  diagonals of rational functions") and extended by Eric Rowland and Doron
  Zeilberger ("A case study in meta-automation: automatic generation of
  congruence automata for combinatorial sequences").
- As part of his 2019 master's thesis, Joel Henningsen (under the guidance of
  Armin Straub) implemented a subset of these algorithms in Sage.  The
  performance and design lessons learned from Joel's work have benefitted the
  present code.

"""

#############################################################################
#  Copyright (C) 2021 Armin Straub, http://arminstraub.com                  #
#                                                                           #
#  Distributed under the terms of the GNU General Public License (GPL)      #
#  either version 2, or (at your option) any later version                  #
#                                                                           #
#  http://www.gnu.org/licenses/                                             #
#############################################################################

from collections import deque
from sage.arith.all import gcd
from sage.misc.cachefunc import cached_method
from sage.rings.all import Zmod, ZZ

# We use PolyDict because at present multivariate Laurent polynomial rings are
# only implemented modulo primes. For instance:
# sage: R.<x,y> = LaurentPolynomialRing(Zmod(4))
# ValueError: base ring must be an integral domain
from sage.rings.polynomial.polydict import PolyDict


def polydict_from(poly, n=None, R=None):
    r"""
    Creates a Laurent polynomial (as a PolyDict instance) from an ordinary
    (Laurent) polynomial or constant.

    EXAMPLES::

        sage: R.<x,y> = LaurentPolynomialRing(Zmod(3))
        sage: f = polydict_from((1+x/y)^3); f
        PolyDict with representation {(0, 0): 1, (3, -3): 1}
        sage: f == polydict_from(f, 1, Zmod(3))
        True

        sage: R.<x,y> = LaurentPolynomialRing(Zmod(4))
        Traceback (most recent call last):
        ...
        ValueError: base ring must be an integral domain
        sage: R.<x,y> = LaurentPolynomialRing(ZZ)
        sage: f = polydict_from((1+x/y)^4, 2, ZZ); f
        PolyDict with representation {(0, 0): 1, (1, -1): 4, (2, -2): 6, (3, -3): 4, (4, -4): 1}
        sage: g = polydict_from((1+x/y)^4, 2, Zmod(4)); g
        PolyDict with representation {(0, 0): 1, (2, -2): 2, (4, -4): 1}
        sage: g == polydict_from(f, 2, Zmod(4))
        True
        sage: g == polydict_from(f, 2, Zmod(8))
        False

        sage: polydict_from(5, 3, Zmod(3))
        PolyDict with representation {(0, 0, 0): 2}
    """
    if not R:
        R = poly.base_ring()
    if not n:
        n = poly.parent().ngens()
    try:
        if n == 1 and not isinstance(poly, PolyDict):
            # exponents need to be tuples even in the univariate case
            coeffs = {(e,): R(c) for e,c in poly.dict().items()}
        else:
            coeffs = {e: R(c) for e,c in poly.dict().items()}
    except:
        # we also allow poly to be a constant (e.g. used for Q=1)
        coeffs = {n*(0,): R(poly)}

    return PolyDict(coeffs, zero=R(0),
            remove_zero=True, force_int_exponents=False, force_etuples=True)


def polydict_cancel(poly, d, R):
    r"""
    Cancel the common factor d from the coefficients.

    EXAMPLES::

        sage: R.<x,y> = LaurentPolynomialRing(ZZ)
        sage: polydict_cancel(polydict_from(3*x+6*y, 2, Zmod(9)), 3, Zmod(9))
        PolyDict with representation {(0, 1): 2, (1, 0): 1}
    """
    new_poly = {e: R(ZZ(poly[e])/ZZ(d)) for e in poly.dict()}
    return PolyDict(new_poly, zero=R(0),
            remove_zero=False, force_int_exponents=False, force_etuples=False)


def polydict_symmetries(poly):
    r"""
    Returns a list of tuples (a, b, c) indicating the symmetries of the given
    polynomial.

    Here, (a, b, c) encodes the fact that the polynomial is invariant under
    replacing the a-th variable with c times the b-th variable.  (If a or b
    are negative, then these refer to the inverses of the variables instead.)

    EXAMPLES::

        sage: R.<x> = LaurentPolynomialRing(Zmod(7))
        sage: polydict_symmetries(polydict_from(1/x+2+x))
        [(-1, 1, 1)]
        sage: polydict_symmetries(polydict_from(1/x+3+2*x))
        [(-1, 1, 2)]

        sage: R.<x> = LaurentPolynomialRing(ZZ)
        sage: polydict_symmetries(polydict_from((1/x+3+2*x)^2, 1, Zmod(49)))
        [(-1, 1, 2)]

        sage: R.<x,y> = LaurentPolynomialRing(ZZ)
        sage: polydict_symmetries(polydict_from((1/x+x)*(1/y+y)))
        [(2, 1, 1), (-1, 1, 1)]
        sage: polydict_symmetries(polydict_from((1/x+2*x)*(2/y+y)))
        [(-2, 1, 1), (-1, 1, 2)]
        sage: polydict_symmetries(polydict_from((1/x+x^2)*(1/y+3*y)))
        [(-2, 2, 3)]
        sage: f = polydict_from(((1+x)*(1+y)*(1+x+y))/x/y, 2, Zmod(9))
        sage: polydict_symmetries(f)
        [(2, 1, 1)]

        sage: R.<x,y,z> = LaurentPolynomialRing(ZZ)
        sage: polydict_symmetries(polydict_from((1/x+x)*(1/y+y)*(1/z+z)))
        [(3, 1, 1), (2, 1, 1), (-1, 1, 1)]
    """
    exponents = poly.exponents()
    e = exponents[0]
    n, R = len(e), poly[e].base_ring()

    symmetries = []

    def check_for_symmetry(m, k, sign):
        # check for a symmetry: xm^sign <=> c * xk
        for e in exponents:
            e_sym = list(e)
            e_sym[k], e_sym[m] = sign*e_sym[m], sign*e_sym[k]
            try:
                if poly[e] != poly[e_sym]:
                    return False
            except:
                return False
        symmetries.append((sign*(m+1), k+1, R(1)))
        return True

    def check_for_symmetry_1(m):
        # check for a symmetry: 1/xm <=> c * xm
        c = R(1)
        for e in exponents:
            if e[m] == 1:
                e_sym = list(e)
                e_sym[m] *= -1
                try:
                    c = R(ZZ(poly[e]) / ZZ(poly[e_sym]))
                    #TODO correctly handle cases where the coefficients are not invertible, such as:
                    # polydict_symmetries(polydict_from((1/x+3+2*x)^6, 1, Zmod(49)))
                except:
                    break
                break

        for e in exponents:
            e_sym = list(e)
            e_sym[m] *= -1
            try:
                if poly[e] != c**e[m] * poly[e_sym]:
                    return False
            except:
                return False
        symmetries.append((-(m+1), m+1, c))
        return True

    for m in range(n-1, -1, -1):
        symmetry_found = False
        for k in range(m):
            symmetry_found = check_for_symmetry(m, k, 1)
            if symmetry_found:
                break
            symmetry_found = check_for_symmetry(m, k, -1)
            if symmetry_found:
                break
        if not symmetry_found:
            symmetry_found = check_for_symmetry_1(m)

    return symmetries


def polydict_reduce_exponents(poly, r):
    r"""
    Given an exponent vector r, keeps only those monomials whose exponents e
    are a (componentwise) multiple of r.  For those monomials, the exponents e
    are replaced with r/e (with the quotient taken componentwise).

    EXAMPLES::

        sage: R.<x> = LaurentPolynomialRing(ZZ)
        sage: polydict_reduce_exponents(polydict_from(1/x+2+x), (2,))
        PolyDict with representation {(0,): 2}

        sage: R.<x,y> = LaurentPolynomialRing(ZZ)
        sage: polydict_reduce_exponents(polydict_from(1/x^2+2+x*y^3+4*y^3), (2,3))
        PolyDict with representation {(-1, 0): 1, (0, 0): 2, (0, 1): 4}
        sage: polydict_reduce_exponents(polydict_from((x*y+1/x+1/y)^2), (2,0))
        PolyDict with representation {(-1, 0): 1}
    """
    if not r:
        return poly
    new_poly = {}
    for e in poly.dict():
        # if the exponent vector e is a multiple of r, then we keep its reduction
        e_reduced = tuple(ei//max(ri,1) for (ei, ri) in zip(e, r)
                if (ri == 0 and ei == 0) or (ri > 0 and ei % ri == 0))
        if len(e_reduced) == len(e):
            new_poly[e_reduced] = poly[e]
    return PolyDict(new_poly, zero=0,
            remove_zero=False, force_int_exponents=False, force_etuples=True)


class ConstantTermBase:
    r"""
    This class precomputes all the powers of a Laurent polynomial (as a
    PolyDict instance) and keeps track of reductions in corresponding constant
    terms.

    EXAMPLES::

        sage: R.<x> = LaurentPolynomialRing(Zmod(2))
        sage: base = ConstantTermBase(polydict_from(1/x+1+x))
        sage: base_p, d = base.pow_p()
        sage: base_p.poly()
        PolyDict with representation {(-1,): 1, (0,): 1, (1,): 1}
        sage: d
        (2,)
        sage: base_p is base
        True
    """
    def __init__(self, poly):
        e = poly.exponents()[0]
        self._n = len(e)
        self._R = poly[e].base_ring()
        self._p, self._r = self._R.factored_order()[0]

        self._poly = poly

        self._power_reductions = None
        self._power_reductions_e = {}
        self._symmetries = None

    def poly(self):
        r"""
        Returns the underlying polynomial.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(ZZ)
            sage: ConstantTermBase(polydict_from(1/x+1+x, 1, Zmod(2))).poly()
            PolyDict with representation {(-1,): 1, (0,): 1, (1,): 1}
        """
        return self._poly

    @cached_method
    def pow(self, i):
        r"""
        Computes (and caches) the i-th power, where i should be between 0 and p.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(4))
            sage: ConstantTermBase(polydict_from(1/x+1+x)).pow(0)
            PolyDict with representation {(0,): 1}
            sage: ConstantTermBase(polydict_from(1/x+1+x)).pow(1)
            PolyDict with representation {(-1,): 1, (0,): 1, (1,): 1}
        """
        if i == 0:
            return self._poly**0
            # return polydict_from(1, self._n, self._R)
        else:
            return self.pow(i-1) * self._poly

    @cached_method
    def pow_p(self):
        r"""
        Computes the p-th power in the form (poly, d).

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(4))
            sage: b, d = ConstantTermBase(polydict_from(1/x+1+x)).pow_p()
            sage: (b.poly(), d)
            (PolyDict with representation {(-2,): 1, (-1,): 2, (0,): 3, (1,): 2, (2,): 1}, None)
        """
        poly = self.pow(self._p)

        d = tuple(gcd(e) for e in zip(*poly.exponents()))
        if set(d) == set([1]):
            d = None
        else:
            poly = polydict_reduce_exponents(poly, d)

        # check if the reduced polynomial is equal to ourselves
        if poly == self._poly:
            return (self, d)
        else:
            return (ConstantTermBase(poly), d)

    def power_reductions(self):
        r"""
        Returns (and caches) a list of pairs [k ,e] such that monomials that
        are not powers of x^e can be reduced modulo p^k.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: ConstantTermBase(polydict_from(1+2*x^3+x^6)).power_reductions()
            [[2, (6,)], [1, (3,)]]
            sage: ConstantTermBase(polydict_from(1+2*x^3+x^4+x^6)).power_reductions()
            [[2, (2,)]]
            sage: ConstantTermBase(polydict_from(1+4*x^3+x^6)).power_reductions()  #TODO: output could be compactified; worth it?
            [[2, (6,)], [1, (6,)]]
            sage: ConstantTermBase(polydict_from(1/x+1+x)).power_reductions()
            []
            sage: ConstantTermBase(polydict_from(1/x+1+x)**2).power_reductions()
            [[2, (2,)]]
            sage: ConstantTermBase(polydict_from(1/x+1+x)**4).power_reductions()
            [[2, (4,)], [1, (2,)]]
        """
        if self._power_reductions is None:
            self._power_reductions = []
            for k in range(1, self._r):
                poly_mod = polydict_from(self._poly, self._n, Zmod(self._p**k))
                d = tuple(gcd(e) for e in zip(*poly_mod.exponents()))
                if set(d) != set([1]):
                    self._power_reductions.append([self._r - k, d])
        return self._power_reductions

    def power_reductions_e(self, e):
        r"""
        Given an exponent e determines the ring modulo which the coefficient
        of x^e can be reduced.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: ConstantTermBase(polydict_from(1+2*x^3+x^4+x^6)).power_reductions_e((1,))
            Ring of integers modulo 4
            sage: ConstantTermBase(polydict_from(1+2*x^3+x^4+x^6)).power_reductions_e((2,))
            Ring of integers modulo 8
        """
        if not e in self._power_reductions_e:
            self._power_reductions_e[e] = self._R
            for k, d in self.power_reductions():
                # monomials that are not powers of x^d can be reduced modulo p^k
                if not all((di == 0 and ei == 0) or (di > 0 and ei % di == 0) for (ei, di) in zip(e, d)):
                    # we don't stop here because later pairs (k, d) might be applicable (with smaller k)
                    self._power_reductions_e[e] = Zmod(self._p**k)
        return self._power_reductions_e[e]

    def reduce_power_reductions(self, poly):
        r"""
        Return poly with power reductions applied.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: f = polydict_from(1/x^3+6*x^2+x^3)
            sage: ConstantTermBase(f).reduce_power_reductions(polydict_from(5+7*x))
            PolyDict with representation {(0,): 5, (1,): 3}
        """
        if not self.power_reductions():
            return poly

        poly_reduced = {e: self._R(self.power_reductions_e(e)(poly[e])) for e in poly.dict()}

        return PolyDict(poly_reduced, zero=self._R(0),
                remove_zero=True, force_int_exponents=False, force_etuples=True)

    def symmetries(self):
        r"""
        Returns (and caches) a list of tuples (a, b, c) indicating the
        symmetries of the underlying polynomial.

        EXAMPLES::

            sage: R.<x,y> = LaurentPolynomialRing(Zmod(7))
            sage: ConstantTermBase(polydict_from(x+y)).symmetries()
            [(2, 1, 1)]
            sage: ConstantTermBase(polydict_from((x+1/x)*(y+1/y))).symmetries()
            [(2, 1, 1), (-1, 1, 1)]

            sage: R.<x,y,z> = LaurentPolynomialRing(Zmod(13))
            sage: ConstantTermBase(polydict_from(x+y+1/z)).symmetries()
            [(-3, 1, 1), (2, 1, 1)]
        """
        if self._symmetries is None:
            self._symmetries = polydict_symmetries(self._poly)
        return self._symmetries

    def reduce_symmetries(self, poly):
        r"""
        Reduces the given poly according to the symmetries of the underlying
        polynomial.

        Each symmetry is a tuple (a, b, c) and results in the a-th variable
        getting substituted by c times the b-th variable.  (If a or b are
        negative, then these refer to the inverses of the variables instead.)

        EXAMPLES::

            sage: R.<x,y> = LaurentPolynomialRing(Zmod(7))
            sage: base = ConstantTermBase(polydict_from(x+y))
            sage: base.reduce_symmetries(polydict_from(x^2+3*x+y+y^2))
            PolyDict with representation {(1, 0): 4, (2, 0): 2}
            sage: base = ConstantTermBase(polydict_from(x+1/y))
            sage: base.reduce_symmetries(polydict_from(x+1/y+y))
            PolyDict with representation {(-1, 0): 1, (1, 0): 2}

            sage: R.<x,y,z> = LaurentPolynomialRing(Zmod(13))
            sage: base = ConstantTermBase(polydict_from(x+y+1/z))
            sage: base.reduce_symmetries(polydict_from(x^2*y^3+4*x^3*y^2+x^-2*y^3))
            PolyDict with representation {(3, -2, 0): 1, (3, 2, 0): 5}

            sage: R.<x> = LaurentPolynomialRing(Zmod(101))
            sage: base = ConstantTermBase(polydict_from(1/x+1+2*x))
            sage: base.reduce_symmetries(polydict_from(3/x^4-1/x+5+4*x+x^2))
            PolyDict with representation {(0,): 5, (1,): 2, (2,): 1, (4,): 48}
        """
        if not poly:
            return poly

        new_poly = {}

        def new_poly_add(e, c):
            e = tuple(e)
            try:
                new_poly[e] += c
            except KeyError:
                new_poly[e] = c

        for e in poly.exponents():
            coeff = poly[e]
            e = list(e)
            for a,b,c in self.symmetries():
                i, j = abs(a)-1, b-1
                ei = e[i] * (-1 if a < 0 else 1)
                if j == i:
                    # in this case, we only substitute negative powers of xi
                    if e[i] < 0:
                        e[i] *= -1
                        coeff *= c**ei
                else:
                    assert c == 1
                    # in this case, we only substitute if it increases the power of xj
                    # if e[j] < ei:
                    if abs(e[j]) < abs(ei):
                        e[j], e[i] = ei, e[j]
            new_poly_add(e, coeff)

        return PolyDict(new_poly, zero=self._R(0),
                remove_zero=True, force_int_exponents=False, force_etuples=True)


class ConstantTerm:
    r"""
    This class represents a constant term ct(base^n * poly).

    EXAMPLES::

        sage: R.<x> = LaurentPolynomialRing(Zmod(4))
        sage: ct = ConstantTerm(polydict_from(1/x+2+x), polydict_from(1-x)); ct
        CT[(x + 2 + x^-1)^n * (-x + 1)]
        sage: ct.offsprings()
        [CT[(x + 2 + x^-1)^n * (1)], CT[(x + 2 + x^-1)^n * (-x + 1)]]
    """
    def __init__(self, base, poly):
        if isinstance(base, ConstantTermBase):
            self._base = base
        else:
            self._base = ConstantTermBase(base)
        self._poly = poly

        self._n = self._base._n
        self._p = self._base._p
        self._R = self._base._R

        self._offsprings = None
        self._pivot_exponent = None

    def __repr__(self):
        r"""
        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(4))
            sage: ConstantTerm(polydict_from(1/x+1+x), polydict_from(1, 1, Zmod(4)))
            CT[(x + 1 + x^-1)^n * (1)]
        """
        if self._n < 5:
            variable_names = ['x', 'y', 'z', 'w'][:self._n]
        else:
            variable_names = ['x%d' % i for i in range(self._n)]
        return 'CT[(%s)^n * (%s)]' % (self._base.poly().poly_repr(variable_names),
                self._poly.poly_repr(variable_names))

    def base(self):
        r"""
        Returns the underlying base polynomial.
        """
        return self._base

    def poly(self):
        r"""
        Returns the underlying multiplier polynomial.
        """
        return self._poly

    def poly_gcd(self):
        r"""
        Returns the largest p^k that divides the multiplier poly.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: ConstantTerm(polydict_from(1/x+1+x), polydict_from(4+6*x)).poly_gcd()
            2
            sage: ConstantTerm(polydict_from(1/x+1+x), polydict_from(3+6*x)).poly_gcd()
            1
        """
        return gcd(self._poly.coefficients())

    def initial_value(self):
        r"""
        Returns the value of the constant term for n=0 (which is simply the
        constant term of the multiplier poly).
        """
        try:
            return self._poly[self._n*(0,)]
        except KeyError:
            return self._R(0)

    def normalized(self):
        r"""
        Returns (c, ct) such that self = c * ct where c is a unit and ct is
        normalized.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: ConstantTerm(polydict_from(1/x+1+x), polydict_from(3-x^2)).normalized()
            (3, CT[(x + 1 + x^-1)^n * (5*x^2 + 1)])
        """
        c = self.initial_value()
        ct = self
        if c and not c.is_unit():
            c = ct._R(ZZ(c) // ct._p**c.valuation(ct._p))
        if c == 1:
            pass
        elif c:
            ct = ct.scale(1/c)
        else:
            #TODO c == 0
            try:
                e = ct.pivot_exponent()
                c = self._poly[e]
                assert c.is_unit()
                ct = ct.scale(1/c)
            except:
                c = 1
        return (ct._R(c), ct)

    def pivot_exponent(self):
        r"""
        Returns an exponent that can be used to reduce other constant terms
        when creating a linear scheme.
        """
        if self._pivot_exponent is None:
            for e in self._poly.exponents():
                if self._poly[e].is_unit():
                    self._pivot_exponent = e
                    break
            else:
                raise ValueError('no pivot exponent')
        return self._pivot_exponent

    def offsprings(self):
        r"""
        Computes offsprings.  Important that this is cached.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(4))
            sage: ConstantTerm(polydict_from(1/x+1+x), polydict_from(1, 1, Zmod(4))).offsprings()
            [CT[(x^2 + 2*x + 3 + 2*x^-1 + x^-2)^n * (1)],
             CT[(x^2 + 2*x + 3 + 2*x^-1 + x^-2)^n * (1)]]
        """
        if not self._offsprings:
            self._offsprings = [self._offspring(j) for j in range(self._p)]
        return self._offsprings

    def _offspring(self, j):
        r"""
        Computes the j-th offspring.

        Reduce the j-th offspring of ct(powers[i]^n * f), namely the constant
        term that is obtained when n is replaced by p*n+j.  The returned value
        is the factor f' in that constant term.

        EXAMPLES::

            sage: R.<x,y> = LaurentPolynomialRing(ZZ)
            sage: f = polydict_from(((1+x)*(1+y)*(1+x+y))/x/y, 2, Zmod(9))
            sage: ConstantTerm(f, f^0).offsprings()[1].poly()
            PolyDict with representation {(-1, -1): 1, (-1, 0): 1, (-1, 1): 1, (0, 0): 3, (1, -1): 1, (1, 0): 2}
        """
        # the new constant term is ct(base^(pn+j) * poly)
        new_base, d = self._base.pow_p()
        new_poly = self._base.pow(j) * self._poly
        new_poly = polydict_reduce_exponents(new_poly, d)

        return ConstantTerm(new_base, new_poly).reduce()

    def scale(self, c):
        r"""
        Multiply poly with c and reduce.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: f = polydict_from(1/x^3+6*x^2+x^3)
            sage: ConstantTerm(f, polydict_from(5+7*x)).scale(2)
            CT[(x^3 + 6*x^2 + x^-3)^n * (2*x + 2)]
        """
        if c == 1:
            return self
        poly = self._poly.scalar_lmult(c)
        ct = ConstantTerm(self.base(), poly)
        return ct.reduce(use_symmetries=False)

    def reduce(self, use_symmetries=True):
        r"""
        Reduce poly to poly' so that ct(base^n * poly) = ct(base^n * poly') for all n.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: f = polydict_from(1/x^3+6*x^2+x^3)
            sage: ConstantTerm(f, polydict_from(5+7*x)).reduce()
            CT[(x^3 + 6*x^2 + x^-3)^n * (3*x + 5)]

            sage: R.<x> = LaurentPolynomialRing(Zmod(4))
            sage: f = polydict_from(1/x+1+x)
            sage: ConstantTerm(f^2, polydict_from(3+2*x)).reduce()
            CT[(x^2 + 2*x + 3 + 2*x^-1 + x^-2)^n * (3)]
            sage: ConstantTerm(f^2, f).reduce()
            CT[(x^2 + 2*x + 3 + 2*x^-1 + x^-2)^n * (1)]
        """
        poly = self.poly()

        if not poly:
            return self

        # first, reduce using symmetries
        if use_symmetries:
            poly = self.base().reduce_symmetries(poly)
            # assert poly == self.base().reduce_symmetries(poly)

        # second, reduce using power reductions
        poly = self.base().reduce_power_reductions(poly)

        return ConstantTerm(self.base(), poly)

    def is_multiple_of(self, ct):
        r"""
        Returns m if self == m*ct or None otherwise.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: ct = ConstantTerm(polydict_from(1/x+1+x), polydict_from(2+3*x))
            sage: ct.scale(2).is_multiple_of(ct)
            2
            sage: ct.scale(4).is_multiple_of(ct)
            4
            sage: ct.scale(4).is_multiple_of(ct.scale(2))
            2
        """
        assert self.base() is ct.base()
        p = self._p
        k = self.poly_gcd().valuation(p) - ct.poly_gcd().valuation(p)
        if k > 0:
            if self.poly() == ct.scale(p**k).poly():
                return self._R(p**k)
        #TODO handle the case k == 0 (shouldn't be needed in scaling schemes if there is unique normalizing)

    def subtract_off(self, cts):
        r"""
        Subtract off other constant terms.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: ct = ConstantTerm(polydict_from(1/x+1+x), polydict_from(2+3*x))
        """
        if not cts:
            return (self, {})

        rel = {}
        poly = self.poly()
        for ct in cts:
            e = ct.pivot_exponent()
            try:
                ct_poly = ct.poly()
                # poly[e] results in a KeyError if the coefficient e in poly is 0
                c = poly[e] / ct_poly[e]
                poly -= ct_poly.scalar_lmult(c)
                rel[ct] = c
            except KeyError:
                pass

        ct = ConstantTerm(self.base(), poly)
        ct = ct.reduce(use_symmetries=False)
        return (ct, rel)


class SequenceLinearScheme:
    r"""
    A sequence represented using a linear scheme.

    EXAMPLES::

    The Thue-Morse sequence::

        sage: S = SequenceLinearScheme([[0, 1], [1, 0]], [0, 1])
        sage: [S.nth_term(n) for n in [0..20]]
        [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0]
    """
    def __init__(self, transitions, initial_conds, states=None, base_ring=None, coerce=True):
        if not base_ring:
            base_ring = initial_conds[0].base_ring()
        # expand shortcut notation
        if transitions[0][0] in ZZ:
            transitions = [[{s: base_ring(1)} for s in t] for t in transitions]

        if coerce:
            initial_conds = [base_ring(i) for i in initial_conds]
            transitions = [[{a: base_ring(b) for a,b in t.items()} for t in st] for st in transitions]

        self._transitions = transitions
        self._initial_conds = initial_conds
        self._states = states
        self._base_ring = base_ring

    def __repr__(self):
        r"""
        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(ZZ)
            sage: CongruenceScheme(1/x+2+x, 1-x, p=2, r=3)
            Linear 2-scheme with 4 states over Ring of integers modulo 8
        """
        return 'Linear %d-scheme with %d states over %s' % (self.input_base(), self.nr_states(), self.base_ring())

    def _latex_(self):
        r"""
        A LaTeX representation of the transitions defining the scheme.
        
        EXAMPLES::
        
            sage: R.<x,y> = LaurentPolynomialRing(ZZ)
            sage: S = CongruenceSchemeScaling(((1+x)*(1+y)*(1+x+y))/x/y, p=2, r=2)
            sage: latex(S)
            \begin{align*}
            A_0(2n) &= A_0(n) \\
            A_0(2n+1) &= 3A_1(n) \\
            A_1(2n) &= A_0(n) \\
            A_1(2n+1) &= A_1(n)
            \end{align*}
        """
        latex_out = '\\begin{align*}\n'
        p = self.input_base()
        n = 'n'
        state_names = ['A_' + ('%d' if i <= 9 else '{%d}') % i for i in range(self.nr_states())]
        def offspring_latex(s, j):
            # A_s(pn+j)
            return '%s(%d%s%s)' % (state_names[state], p, n, '+%d' % j if j else '')
        def transition_latex(t):
            # c_0 A_0(n) + ...
            return ' + '.join('%s%s(%s)' % (t[s] if t[s] != 1 else '', state_names[s], n) for s in t) if t else '0'
        latex_lines = []
        for state, state_transitions in enumerate(self._transitions):
            for j, transition in enumerate(state_transitions):
                latex_lines.append('%s &= %s' % (offspring_latex(state, j), transition_latex(transition)))
        latex_out += ' \\\\\n'.join(latex_lines)
        latex_out += '\n\\end{align*}'
        return latex_out

    def base_ring(self):
        r"""
        Returns the ring over which this is scheme is defined.
        
        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(9))
            sage: S = CongruenceScheme(1/x+1+x, 1-x^2)
            sage: S.base_ring()
            Ring of integers modulo 9
        """
        return self._base_ring

    def modulus(self):
        r"""
        Returns m if this is a k-scheme modulo m.
        
        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(9))
            sage: S = CongruenceScheme(1/x+1+x, 1-x^2)
            sage: S.modulus()
            9
        """
        return self.base_ring().order()

    def input_base(self):
        r"""
        Returns k if this is a k-scheme modulo m.
        
        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(9))
            sage: S = CongruenceScheme(1/x+1+x, 1-x^2)
            sage: S.input_base()
            3
        """
        return len(self._transitions[0])

    def save(self, filename):
        r"""
        Saves the scheme to a file.
        
        EXAMPLES::
        
            sage: import tempfile
            sage: tmp = tempfile.NamedTemporaryFile()
            sage: R.<x> = LaurentPolynomialRing(Zmod(9))
            sage: S = CongruenceScheme(1/x+1+x, 1-x^2)
            sage: S.save(tmp.name)
            sage: SequenceLinearScheme.load(tmp.name)
            Linear 3-scheme with 6 states over Ring of integers modulo 9
        """
        data = [self.modulus(), self.initial_conds(), self.transitions()]
        with open(filename, 'w') as file:
            file.write(str(data))

    @classmethod
    def load(cls, filename, base_ring=None):
        r"""
        Loads a previously saved scheme from a file.
        
        EXAMPLES::
        
            sage: import tempfile
            sage: tmp = tempfile.NamedTemporaryFile()
            sage: R.<x> = LaurentPolynomialRing(Zmod(13))
            sage: S = CongruenceScheme(1/x+1+x, 1-x^2)
            sage: S.save(tmp.name)
            sage: T = SequenceLinearScheme.load(tmp.name)
            sage: S.transitions() == T.transitions()
            True
        """
        with open(filename, 'r') as file:
            n, i, t = eval(file.read())
        if not base_ring:
            base_ring = Zmod(n)
        return cls(t, i, base_ring=base_ring, coerce=True)

    def initial_conds(self):
        r"""
        Returns the initial conditions for each state as a list.
        
        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(7))
            sage: S = CongruenceSchemeAutomatic(1/x+1+x, 1-x^2)
            sage: S.initial_conds()
            [1, 1, 2, 4, 0, 2, 3, 5, 6]
        """
        return self._initial_conds

    def initial_cond(self, state_comb):
        r"""
        Returns the initial condition for the given state (combination) where
        the latter can be specified by index or as a dict or tuple.
        
        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(3))
            sage: S = CongruenceScheme(1/x+1+x, 1-x^2)
            sage: S.initial_cond(1)
            0
            sage: S.initial_cond(S.transition(S.initial_state(), 2))
            2
        """
        try:
            return self._initial_conds[state_comb]
        except TypeError:
            # we allow state_comb to be either a dict or a tuple
            state_comb_items = state_comb if type(state_comb) is tuple else state_comb.items()
            return self.base_ring()(sum(c*self.initial_cond(s) for s, c in state_comb_items))

    def initial_state(self):
        r"""
        Returns the initial state (combination) of the scheme.
        
        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(3))
            sage: S = CongruenceScheme(1/x+1+x, 1-x^2)
            sage: S.initial_state()
            {0: 1}
        """
        return {0: self.base_ring()(1)}

    def nr_states(self):
        r"""
        Return the number of states in this linear scheme.  This may be one
        less than self.nr_states_automaton() which may be more appropriate for
        automata where the zero state should be included in the count.
        
        EXAMPLES::
        
            sage: R.<x,y> = LaurentPolynomialRing(ZZ)
            sage: S = CongruenceSchemeAutomatic(((1+x)*(1+y)*(1+x+y))/x/y, p=3, r=1)
            sage: [S.nr_states(), S.nr_states_automaton()]
            [1, 2]
        """
        # we don't use self._states because it is optional
        return len(self._transitions)

    def nr_states_automaton(self):
        r"""
        Return the number of states in this scheme if it is treated as an
        automaton.  This is either the same as self.nr_states() or one more,
        depending on whether the transitions include a transition to the zero state.
        
        EXAMPLES::
        
            sage: R.<x,y> = LaurentPolynomialRing(ZZ)
            sage: S = CongruenceSchemeAutomatic(((1+x)*(1+y)*(1+x+y))/x/y, p=3, r=2)
            sage: [S.nr_states(), S.nr_states_automaton()]
            [4, 5]
        """
        return self.nr_states() + next((1 for st in self.transitions() if min(len(t) for t in st) == 0), 0)

    def states(self):
        r"""
        If available, returns the constant terms (or some other representation
        that was specified during the construction of the scheme) that
        correspond to the internal states.
        
        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: S = CongruenceSchemeScaling(1/x+2+x, 1-x)
            sage: S.states()
            [CT[(x + 2 + x^-1)^n * (-x + 1)],
             CT[(x^2 + 4*x + 6 + 4*x^-1 + x^-2)^n * (x + 1)],
             CT[(x^2 + 4*x + 6 + 4*x^-1 + x^-2)^n * (-x^2 + 1)],
             CT[(x^2 + 4*x + 6 + 4*x^-1 + x^-2)^n * (1)],
             CT[(x^2 + 4*x + 6 + 4*x^-1 + x^-2)^n * (3*x^2 + 1)]]
            sage: V = S.valuation_scheme()
            sage: V.states() == None
            True
        """
        return self._states

    def _state_comb_as_tuple(self, d):
        r"""
        Returns the state combination d (a dictionary) as a tuple.  This is
        useful in certain internal cases where we need something hashable
        (dict is not but tuple is).
        
        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(3))
            sage: S = CongruenceScheme(1/x+1+x, 1-x^2)
            sage: S.transitions()[1]
            [{}, {2: 2}, {0: 1, 1: 1, 2: 1}]
            sage: [S._state_comb_as_tuple(d) for d in S.transitions()[1]]
            [(), ((2, 2),), ((0, 1), (1, 1), (2, 1))]
        """
        return tuple((k, d[k]) for k in sorted(d.keys()))
    
    def transitions(self):
        r"""
        The transitions defining the scheme are returned in the form [t_1,
        t_2, ...] where t_i is a list (with p elements) containing the linear
        combinations of states that the i-th state transitions to for input
        0,1,...,p.
        
        EXAMPLES::
        
            sage: R.<x,y> = LaurentPolynomialRing(ZZ)
            sage: S = CongruenceSchemeScaling(((1+x)*(1+y)*(1+x+y))/x/y, p=2, r=2)
            sage: S.transitions()
            [[{0: 1}, {1: 3}], [{0: 1}, {1: 1}]]
        """
        return self._transitions

    def transition(self, state_comb, digit):
        r"""
        Determines the state (combination) that we transition into from
        state_comb when reading in the given input digit.
        
        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(3))
            sage: S = CongruenceScheme(1/x+1+x, 1-x^2)
            sage: S.transition(S.initial_state(), 2)
            {0: 2, 1: 2, 2: 2}
            sage: S.transition(S._state_comb_as_tuple(S.initial_state()), 2)
            ((0, 2), (1, 2), (2, 2))
        """
        # we allow state_comb to be either a dict or a tuple
        state_comb_items = state_comb if type(state_comb) is tuple else state_comb.items()
        # state_comb is of the form { .., state: coeff, ..  }
        new_state_comb = {}
        for state, c in state_comb_items:
            transition = self._transitions[state][digit]
            # new_state_comb = new_state_comb plus c*transition
            for s, d in transition.items():
                nd = new_state_comb.get(s, 0) + c*d
                if nd:
                    new_state_comb[s] = nd
                elif c*d:
                    del new_state_comb[s]
        # if the input was a tuple, we need to also return a tuple
        if type(state_comb) is tuple:
            new_state_comb = self._state_comb_as_tuple(new_state_comb)
        return new_state_comb

    def possible_state_combs(self, progress=False, tuples=False):
        r"""
        Determines a list of all possible state combinations of the scheme
        (that is, all the states that can be attained by some input).
        
        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(3))
            sage: S = CongruenceScheme(1/x+1+x, 1-x^2)
            sage: S.possible_state_combs()
            [{0: 1}, {0: 1, 1: 1}, {0: 1, 1: 1, 2: 1}, {0: 2, 1: 2, 2: 2}, {}, {0: 2, 1: 2}]
        """
        p = self.input_base()
        # we need both adding elements and checking for containment to be fast
        # hence, states should not be a regular list
        # states could be defined as a set but these don't remember insertion order
        # (order is somewhat desirable; at least the initial state must remain
        # the first item as this is assumed in the method automatic_scheme)
        # because there is no standard ordered set, we simple use a dict
        # (since python 3.6, dict's are insertion ordered)
        states_todo = deque([self._state_comb_as_tuple(self.initial_state())])
        states = {states_todo[0]: None}
        while states_todo:
            state_comb = states_todo.popleft()
            for digit in range(p):
                new_state_comb = self.transition(state_comb, digit)
                if new_state_comb not in states:
                    states[new_state_comb] = None
                    states_todo.append(new_state_comb)
                    # states.add(new_state_comb)
                    # states_todo.add(new_state_comb)
            if progress:
                todo = len(states_todo)
                done = len(states)
                print('\rstates todo/processed: %d/%d [%0.2f%%]' % (todo, done, 100*float(todo)/done), end=8*' ')
        if progress:
            print('')

        if tuples:
            return list(states.keys())
        else:
            return [dict(s) for s in states.keys()]

    def possible_values(self, progress=False):
        r"""
        Determines the possible outputs of the scheme.

        EXAMPLES::
        
            sage: R.<x,y> = LaurentPolynomialRing(ZZ)
            sage: CongruenceScheme(((1+x)*(1+y)*(1+x+y))/x/y, p=3, r=2).possible_values()
            {0, 1, 3, 6}
        """
        return {self.initial_cond(s) for s in self.possible_state_combs(progress)}

    def impossible_values(self, progress=False):
        r"""
        Determines those residues (mod p^r) that are not possible outputs of
        the scheme.

        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(ZZ)
            sage: CongruenceScheme(1/x+1+x, 1-x^2, p=5, r=2).impossible_values()
            {0}
            sage: CongruenceSchemeScaling(1/x+1+x, 1-x, p=2, r=5).impossible_values()
            {16}
        """
        return set(self.base_ring()) - self.possible_values(progress)

    def is_automatic(self):
        r"""
        Tests whether this scheme is automatic.

        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: S = CongruenceSchemeAutomatic(1/x+2+x, 1-x)
            sage: S.is_automatic()
            True
            sage: S = CongruenceSchemeScaling(1/x+2+x, 1-x)
            sage: S.is_automatic()
            False
            sage: S = CongruenceScheme(1/x+2+x, 1-x)
            sage: S.is_automatic()
            False
        """
        # check if there is a transition containing either a combination of more than one state or to a multiple of a state
        return next((False for st in self.transitions()
            if max(len(t) for t in st) > 1
            or next((True for t in st for c in t.values() if c != 1), False)), True)

    def is_scaling(self):
        r"""
        Tests whether this scheme is scaling.

        EXAMPLES::
        
            sage: R.<x> = LaurentPolynomialRing(Zmod(8))
            sage: S = CongruenceSchemeScaling(1/x+2+x, 1-x)
            sage: S.is_scaling()
            True
            sage: S = CongruenceScheme(1/x+2+x, 1-x)
            sage: S.is_scaling()
            False
        """
        return next((False for st in self.transitions() if max(len(t) for t in st) > 1), True)

    def valuation_scheme(self, simplify=True):
        r"""
        From a p-scheme for a sequence A(n) mod p^r constructs a scheme for
        the p-adic valuation of A(n) [or, more precisely, for p^v(A(n)) mod
        p^r where v is the p-adic valuation].

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(ZZ)
            sage: S = CongruenceSchemeScaling(1/x+1+x, 1-x^2, p=5, r=2).valuation_scheme()
            sage: S.possible_values()
            {1, 5}
            sage: CongruenceSchemeScaling(1/x+1+x, 1-x^2, p=13, r=2).valuation_scheme()
            Linear 13-scheme with 5 states over Ring of integers modulo 169
        """
        if not self.is_scaling():
            raise NotImplementedError('currently only implemented for scaling schemes')
        n = self.modulus()
        initial_conds = [i.gcd(n) for i in self.initial_conds()]
        transitions = [[{a: b.gcd(n) for a,b in t.items()} for t in st] for st in self.transitions()]

        S = SequenceLinearScheme(transitions, initial_conds)
        if simplify:
            S = S.simplify()
        return S

    def automatic_scheme(self, simplify=True, progress=False):
        r"""
        Returns an automatic scheme equivalent to self.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(ZZ)
            sage: S = CongruenceSchemeScaling(1/x+1+x, 1-x^2, p=5, r=2).automatic_scheme(); S
            Linear 5-scheme with 136 states over Ring of integers modulo 25
            sage: set([S.nth_term(n) == sum(binomial(n,2*k)*catalan_number(k) for k in [0..n]) for n in [0..100]])
            {True}
            sage: [CongruenceSchemeScaling(1/x+1+x, 1-x^2, p=2, r=r).automatic_scheme().nr_states() for r in [1..5]]
            [5, 15, 24, 76, 225]
        """
        p = self.input_base()
        R = self.base_ring()
        # states is a list of tuples
        states = self.possible_state_combs(tuples=True, progress=progress)
        assert states[0] == ((0, R(1)),)
        states_indices = dict(zip(states, range(len(states))))
        transitions = [[{states_indices[self.transition(s, j)]: R(1)} for j in range(p)] for s in states]
        initial_conds = [self.initial_cond(s) for s in states]

        S = SequenceLinearScheme(transitions, initial_conds)
        if simplify:
            S = S.simplify()
        return S

    def nth_term(self, n):
        r"""
        Compute n-th term of the sequence.

        EXAMPLES::

        The Thue-Morse sequence::

            sage: S = SequenceLinearScheme([[0, 1], [1, 0]], [0, 1])
            sage: [S.nth_term(n) for n in [0..20]]
            [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0]
        """
        p = self.input_base()
        state_comb = self.initial_state()
        while n > 0:
            digit = n % p
            n = n // p
            state_comb = self.transition(state_comb, digit)
        return self.initial_cond(state_comb)

    def terms(self, n):
        r"""
        Compute the first n terms of the sequence.

        EXAMPLES::

        The Thue-Morse sequence::

            sage: S = SequenceLinearScheme([[0, 1], [1, 0]], [0, 1])
            sage: S.terms(20)
            [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]
        """
        # TODO if speed is ever a concern, this could be easily sped up by not
        # computing each value individually
        return [self.nth_term(k) for k in range(n)]

    def simplify(self):
        r"""
        Simplifies the scheme by identifying some states that are equivalent.

        Currently, this is only implemented for scaling schemes (but
        not general linear schemes).  The implementation proceeds along the
        lines of Moore's algorithm for DFA minimization:
            https://en.wikipedia.org/wiki/DFA_minimization

        For automatic schemes, it should produce a minimal one.  For scaling
        ones, the current implementation does not attempt to identify states
        that are multiples of each other and so likely won't produce a minimal
        scheme.

        EXAMPLES::

            sage: R.<x> = LaurentPolynomialRing(ZZ)
            sage: S = CongruenceSchemeAutomatic(1/x+2+x, 1-x, p=3, r=2, simplify=False)
            sage: [S.nr_states(), S.simplify().nr_states()]
            [21, 20]
            sage: [[CongruenceSchemeAutomatic(1/x+2+x, 1-x, 2, r, simplify=s).nr_states_automaton() for s in [False,True]] for r in [1..6]]
            [[3, 3], [4, 4], [11, 11], [26, 26], [65, 56], [169, 134]]
            sage: [[CongruenceSchemeScaling(1/x+2+x, 1-x, 2, r, simplify=s).nr_states() for s in [False,True]] for r in [1..6]]
            [[2, 2], [2, 2], [5, 5], [9, 9], [17, 16], [33, 29]]
        """
        if not self.is_scaling():
            raise NotImplementedError('simplify is currently only implemented for scaling schemes')

        class StatesPartition:
            def __init__(self, S):
                self.scheme = S
                self.partition = set(tuple(s for s in range(S.nr_states()) if S.initial_cond(s) == v) for v in set(S.initial_conds()))
            def part_from_state(self, state):
                for part in self.partition:
                    if state in part:
                        return part
            def subdivide(self, part, subparts):
                self.partition.remove(part)
                # update is like union but replaces the original set instead of returning a new one
                self.partition.update(subparts)
            # given a state and an input digit, determine the output state (and multiplier)
            def transition(self, state, digit):
                try:
                    ((s, c),) = self.scheme._transitions[state][digit].items()
                except:
                    # transition to the empty state
                    return None
                return (self.part_from_state(s), c)

        # partition the states according to initial condition
        P = StatesPartition(self)

        partition_changed = True
        while partition_changed:
            partition_changed = False
            # even as we subdivide parts of the partition, we want to continue iterating over the remaining ones
            for part in P.partition.copy():
                for digit in range(self.input_base()):
                    # from the states in part, to which target parts do we transition given digit?
                    target_parts = {state: P.transition(state, digit) for state in part}
                    target_parts_set = set(target_parts.values())
                    if len(target_parts_set) > 1:
                        # split up the states in part according to their targets (including multiplier)
                        sub_parts = set(tuple(s for s in part if target_parts[s] == t) for t in target_parts_set)
                        P.subdivide(part, sub_parts)
                        partition_changed = True
                        # we are done with this part and move on to the next
                        break

        # combine states according to partition
        indices = sorted(min(part) for part in P.partition)
        initial_conds = [self._initial_conds[i] for i in indices]
        states = [self._states[i] for i in indices] if self._states else None
        # relabel transitions
        indices_new = dict(zip(indices, range(len(indices))))
        states_new = [indices_new[min(P.part_from_state(s))] for s in range(self.nr_states())]
        def reindex_transition(t):
            return {states_new[s]: c for s, c in t.items()}
        transitions = [[reindex_transition(t) for t in self._transitions[i]] for i in indices]

        return SequenceLinearScheme(transitions, initial_conds, states=states)


def CongruenceSchemeAutomatic(P, Q=1, p=None, r=1, simplify=None, progress=False):
    return CongruenceScheme(P, Q, p, r, scheme="automatic", simplify=simplify, progress=progress)
def CongruenceSchemeScaling(P, Q=1, p=None, r=1, simplify=None, progress=False):
    return CongruenceScheme(P, Q, p, r, scheme="scaling", simplify=simplify, progress=progress)
def CongruenceLinearScheme(P, Q=1, p=None, r=1, simplify=None, progress=False):
    return CongruenceScheme(P, Q, p, r, scheme="linear", simplify=simplify, progress=progress)

def CongruenceScheme(P, Q=1, p=None, r=1, scheme="linear", simplify=None, progress=False):
    r"""
    Compute a congruence scheme for the sequence a(n) of constant terms of P^n*Q.

    scheme can be: automatic, scaling, linear

    By default (simplify=None), scaling (including automatic) schemes get simplified.
    
    EXAMPLES::
    
    The Catalan sequence::

        sage: R.<x> = LaurentPolynomialRing(Zmod(8))
        sage: S = CongruenceScheme(1/x+2+x, 1-x)
        sage: [S.nth_term(n) for n in [0..10]]
        [1, 1, 2, 5, 6, 2, 4, 5, 6, 6, 4]
        sage: set([S.nth_term(n) == catalan_number(n) for n in [0..100]])
        {True}

        sage: R.<x> = LaurentPolynomialRing(ZZ)
        sage: S = CongruenceScheme(1/x+2+x, 1-x, p=3, scheme="automatic")
        sage: S.states()
        [CT[(x + 2 + x^-1)^n * (-x + 1)],
         CT[(x + 2 + x^-1)^n * (1)],
         CT[(x + 2 + x^-1)^n * (-x + 2)],
         CT[(x + 2 + x^-1)^n * (2)]]
        sage: [CongruenceScheme(1/x+2+x, 1-x, 2, r).nr_states() for r in [1..6]]
        [2, 2, 4, 8, 16, 32]

    The Motzkin numbers::

        sage: R.<x> = LaurentPolynomialRing(ZZ)
        sage: S = CongruenceScheme(1/x+1+x, 1-x^2, 5, 2)
        sage: set([S.nth_term(n) == sum(binomial(n,2*k)*catalan_number(k) for k in [0..n]) for n in [0..100]])
        {True}
        sage: [[CongruenceScheme(1/x+1+x, 1-x^2, 2, r, scheme=s).nr_states() for s in ["automatic", "scaling", "linear"]] for r in [1..4]]
        [[4, 4, 3], [14, 13, 5], [24, 17, 9], [76, 35, 17]]
        sage: [[CongruenceScheme(1/x+1+x, 1-x^2, p, 2, scheme=s).nr_states() for s in ["automatic", "scaling", "linear"]] for p in [3,5,7]]
        [[23, 9, 6], [136, 29, 8], [316, 28, 10]]

    The Little Schröder numbers::

        sage: R.<x> = LaurentPolynomialRing(ZZ)
        sage: S = CongruenceScheme(1/x+3+2*x, 1-2*x^2, 7, 2)
        sage: [S.nth_term(n) for n in [0..10]]
        [1, 3, 11, 45, 1, 21, 16, 17, 2, 47, 37]
        sage: [((1/x+3+2*x)^n * (1-2*x^2)).constant_coefficient() for n in [0..10]]
        [1, 3, 11, 45, 197, 903, 4279, 20793, 103049, 518859, 2646723]
        sage: [CongruenceScheme(1/x+3+2*x, 1-2*x^2, p=p).nr_states() for p in [3,5,7,11,13,17]]
        [3, 3, 3, 3, 3, 3]
        sage: [CongruenceScheme(1/x+3+2*x, 1-2*x^2, p=p, r=2).nr_states() for p in [3,5,7,11]]
        [6, 8, 10, 14]

    The Apery sequence associated to zeta(2)::

        sage: R.<x,y> = LaurentPolynomialRing(ZZ)
        sage: S = CongruenceScheme(((1+x)*(1+y)*(1+x+y))/x/y, p=3, r=2)
        sage: [S.nth_term(n) for n in [0..10]]
        [1, 3, 1, 3, 0, 3, 1, 6, 1, 3, 0]
        sage: [sum(binomial(n,k)^2*binomial(n+k,k) for k in [0..n]) % 9 for n in [0..10]]
        [1, 3, 1, 3, 0, 3, 1, 6, 1, 3, 0]
        sage: set([S.nth_term(n) == sum(binomial(n,k)^2*binomial(n+k,k) for k in [0..n]) for n in [0..100]])
        {True}
        sage: [CongruenceScheme(((1+x)*(1+y)*(1+x+y))/x/y, p=2, r=r).nr_states() for r in [1..5]]
        [1, 3, 7, 15, 31]
        sage: [CongruenceSchemeAutomatic(((1+x)*(1+y)*(1+x+y))/x/y, p=2, r=r).nr_states() for r in [1..4]]
        [1, 4, 17, 65]
        sage: [CongruenceSchemeScaling(((1+x)*(1+y)*(1+x+y))/x/y, p=2, r=r).nr_states() for r in [1..5]]
        [1, 2, 5, 9, 17]

        sage: S = CongruenceSchemeScaling(((1+x)*(1+y)*(1+x+y))/x/y, x^2, p=5, r=2)
        sage: S.nr_states()
        12
        sage: S.terms(10) == [((((1+x)*(1+y)*(1+x+y))/x/y)^n * x^2).constant_coefficient() for n in [0..9]]
        True

    The Apery sequence associated to zeta(3)::

        sage: R.<x,y,z> = LaurentPolynomialRing(ZZ)
        sage: S = CongruenceScheme(((x+y)*(1+z)*(x+y+z)*(1+y+z))/x/y/z, p=3, r=2)
        sage: [S.nth_term(n) for n in [0..10]]
        [1, 5, 1, 5, 7, 5, 1, 5, 1, 5, 7]
        sage: set([S.nth_term(n) == sum(binomial(n,k)^2*binomial(n+k,k)^2 for k in [0..n]) for n in [0..100]])
        {True}
    """
    linear_scheme = True
    scaling_scheme = False
    if scheme == "scaling":
        scaling_scheme = True
        linear_scheme = False
    if scheme == "automatic":
        linear_scheme = False
    # by default, we simplify schemes except linear ones
    if simplify is None:
        simplify = not linear_scheme

    # if p and r are not specified, we determine them from P 
    if not p:
        p, r = P.base_ring().factored_order()[0]
    R = Zmod(p**r)
    n = P.parent().ngens()
    P = polydict_from(P, n, R)
    Q = polydict_from(Q, n, R)

    class ConstantTermManager:
        def __init__(self):
            # cts[base] is a deque of constant terms of the form ct(base^n * poly)
            self.cts = {}
            self.cts_count = 0
            # linear_combinations[ct] expresses ct as a linear combination in the form {ct1: c1, ...}
            # for each ct in self.cts, all offspring must have such a linear combination registered
            self.linear_combinations = {}
            # todo[k] is a deque of constant terms to process that are multiples of p^k
            self.todo = {}
            self.todo_count = 0
            self.todo_processed = 0
        def add_todo(self, ct):
            k = ct.poly_gcd().valuation(p)
            if not k in self.todo:
                self.todo[k] = deque()
            self.todo[k].append(ct)
            self.todo_count += 1
        def pop_todo(self):
            k = min(self.todo.keys())
            try:
                ct = self.todo[k].popleft()
                self.todo_count -= 1
                self.todo_processed += 1
                return ct
            except IndexError:
                del self.todo[k]
                return self.pop_todo()
        def all_constant_terms(self):
            return [ct for b in self.cts for ct in self.cts[b]]
        def known_constant_terms(self, base):
            try:
                return self.cts[base]
            except KeyError:
                return deque()
        def register_ct_relation(self, ct, rel, ct_unscaled, c):
            if ct_unscaled is not ct:
                rel = {r: c*d for r, d in rel.items()}
            self.linear_combinations[ct_unscaled] = rel
        def add_ct(self, ct, ct_unscaled=None, c=None):
            if ct_unscaled:
                self.linear_combinations[ct_unscaled] = {ct: c}
            try:
                assert ct not in self.cts[ct.base()]
                self.cts[ct.base()].append(ct)
            except KeyError:
                self.cts[ct.base()] = [ct]
            self.cts_count += 1
            for o in ct.offsprings():
                self.add_todo(o)

    manager = ConstantTermManager()

    def find_relation(ct_new, cts):
        poly = ct_new.poly()
        if not poly:
            return {}
        for ct in cts:
            if poly == ct.poly():
                return {ct: R(1)}
        if scaling_scheme and not ct_new.poly_gcd().is_unit():
            for ct in cts:
                m = ct_new.is_multiple_of(ct)
                if m:
                    assert poly == ct.scale(m).poly()
                    return {ct: R(m)}

    # the initial constant term
    ct = ConstantTerm(P, Q).reduce()
    manager.add_todo(ct)

    while manager.todo_count > 0:
        ct = manager.pop_todo()

        # ct_unscaled = c * ct
        ct_unscaled, c = ct, R(1)
        if scaling_scheme or linear_scheme:
            # scale this constant term so that its initial value is 1 (or similarly normalized)
            c, ct = ct_unscaled.normalized()

        # cts_known is a list of other constant terms with the same base as ct
        cts_known = manager.known_constant_terms(ct.base())
        rel = find_relation(ct, cts_known)

        if rel is not None:
            manager.register_ct_relation(ct, rel, ct_unscaled, c)
        elif not linear_scheme:
            manager.add_ct(ct, ct_unscaled, c)
        else:
            # linear scheme
            ct_new, rel = ct.subtract_off(cts_known)
            if ct_new.poly():
                # we need to add poly as a new constant term, then adjust rel
                # so that it is a linear combination for the original ct
                d = ct_new.poly_gcd()
                if not d.is_unit():
                    # none of the coefficients is invertible
                    # TODO In the following, we divide out the common power of
                    # p; that way, the resulting constant term has a
                    # pivot_exponent that can be easily used for elimination.
                    # A potential price to pay is that this new constant term
                    # has more complicated offspring.  If there is a
                    # worthwhile example where this happens, we should adjust
                    # the elimination process instead of doing the following.
                    poly = polydict_cancel(ct_new.poly(), d, R)
                    ct_new = ConstantTerm(ct.base(), poly)
                else:
                    assert d == 1
                manager.add_ct(ct_new)
                rel[ct_new] = d
            # rel now is a linear combination equal to ct
            manager.register_ct_relation(ct, rel, ct_unscaled, c)

        if progress:
            todo = manager.todo_count
            done = manager.todo_processed
            print('\rtodo/processed: %d/%d [%0.2f%%], %d states so far' %
                    (todo, done, 100*float(todo)/done, manager.cts_count),
                    end=16*' ')

    if progress:
        print('')

    # assemble the constant terms into states of a linear scheme
    states = manager.all_constant_terms()
    indices = {ct: i for i, ct in enumerate(states)}
    def ct_to_indices(lc):
        return {indices[ct]: c for ct, c in lc.items()}
    transitions = [[ct_to_indices(manager.linear_combinations[ct.offsprings()[j]]) for j in range(p)] for ct in states]
    initial_conds = [ct.initial_value() for ct in states]

    S = SequenceLinearScheme(transitions, initial_conds, states=states, coerce=False)
    if simplify:
        S = S.simplify()
    return S

