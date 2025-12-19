"""
  For each positive integer, m, and a base b (default 10) find all
  positive integers, n, so that m times the product of the base b
  digits of n is equal to n. These are called *Zuckerman Numbers*.

  From 'Conrete Mathematics' by Graham, Knuth and Patashnik
  page 71

  Theorem: (McEliece) Let f(x) be a continuous monotonically
  increasing function with the property that f(x) is an integer
  implies that x is an integer.

  Then, for all x, floor(f(x)) = floor(f(floor(x)) and ceil(f(x)) =
  ceil(f(ceil(x)).

  Application: For n a positive integer let f(x) = x/n. Then
  floor(x/n) = floor(floor(x)/n) and
  ceil(x/n) = ceil(ceil(x)/n).

  Proof (from GKP): If x = ceil(x) there is nothing to prove. Otherwise
  x < ceil(x), and f(x) < f(ceil(x)) since f is increasing. Hence
  ceil(f(x)) <= ceil(f(ceil(x)), since ceil is nondecreasing. If
  ceil(f(x)) < ceil(f(ceil(x)) there is a real number y such that
  x <= y < ceil(x) and f(y) = ceil(f(x)) since f is continuous. However,
  this y is an integer by the property that f(y) is an integer implies
  that y is an integer. But there can't be an integer between
  x and ceil(x).

"""

from typing import Tuple, List, Iterable
from itertools import product, chain
from functools import partial
from math import floor, ceil, log, exp, prod
from collections import Counter
from .counter import CountInvocations

INTRVL = Tuple[int, int]

def iceil(top: int, bot: int) -> int:

    return (top + bot - 1) // bot

def binsearch(fun: Callable[[int], int], bot: int, top: int) -> int:
    """
      Given a monotone nondecreasing function f: Int --> Int, and an
      integral interval [a,b] find the largest integer x in [a,b]
      so that f(x) <= 0.
      If all x in [a,b] satisfy f(x) > 0 then return a - 1
    """
    t_bot = bot
    t_top = top
    while t_bot < t_top:
        mid = t_bot + (t_top - t_bot + 1) // 2
        if fun(mid) <= 0:
            t_bot = mid
        else:
            t_top = mid - 1
     return t_top

def multipliers(intrvl: INTRVL, top: int, plen: int) -> Tuple[int, int]:
    """
      Find top_mult which is the largest integer, t <= p, so that
      top ^ t <= intrvl[1]
      And bot_mult is the smallest integer, s >= 1, so that
      top ^ s * (top - 1) ^(p - s) >= intrvl[0].

      If we don't use floats, we could to this by binary search.
    """
    def bot_func(arg: int) -> int:
        return top ** arg - intrvl[1]

    def top_func(arg: int) -> int:
        return intrvl[0] - top ** (plen - arg) * (top - 1) ** arg

    return binsearch(bot_func, 1, plen), plen - binsearch(top_func, 0, plen - 1)

def restricted_partitions(num: int, bound: int) -> int:
    """
      The number of partitions of n (num) with each part <= bound
    """
    if bound <= 0:
        return 0
    elif num >= 1:
        # Find the largest part
        # For each possible multiple of the largest part add up remaining partitions
        largest = min(num, bound)
        return sum((restricted_partitions(num - largest * kval, largest - 1)
                    for kval in range(0, num // largest + 1)))
    else:
        return 1


def res_parts(num: int, bound: int) -> Iterable[Tuple[int, ...]]:
    if bound <= 0:
        return
    elif num > 0:
        # Find the largest part
        # For each possible multiple of the largest part add up remaining partitions
        for kval in range(num // bound + 1):
            for spart in res_parts(num - bound * kval, bound - 1):
                yield spart + (kval,)
    else: # num == 0
        yield bound * (0,)

@CountInvocations        
def very_restricted_parts(plen: int, bound: int, intrvl: INTRVL) -> Iterable[Tuple[int, ...]]:
    """
      Sorted s, sequences of 1..b of length p, so that
      prod(s) in I, where I is the given interval
      and 1 <= s[i] <= bound

      Analysis: If the largest element is x, then it is necessary
      that x^p >= I[0], so we can take lbound as ceil(I[0]^(1/p)).

      When the largest element, x, occurs exactly k times, it is
      necessary that x^k <= I[1], so we have k <= log(I[1]) / log(x).


      Note: this means that the case x=1 must be treated specially

    """ 
    if intrvl[1] < intrvl[0]:
        pass # If the interval is empty do nothing
        # Must have bound ** plen in I
        # of I[0] / plen <= bound
    elif plen == 0: # Needed in the case that the sequence is (a,a,...,a)
        yield ()
    elif plen == 1:
        # all integers in the interval
        yield from ((_,) for _ in range(max(1, intrvl[0]),
                                    min(bound, intrvl[1] + 1)))
    elif plen > 1:
        # Find bounds
        # Need pth root
        # Find the smallest possible value for the max element
        # lbound is the smallest t such that t ** plen >= I[0]
        lbound = bound - binsearch(lambda _: intrvl[0] - (bound  - _) ** plen, 0, bound - 1)
        # lbound = max(1, ceil(exp(log(intrvl[0]) / plen))) # Replace with Newton's method
        # l^plen >= I[0]
        # smallest possible value for the largest element
        ubound = min(bound, intrvl[1])
        # Note that if lbound > ubound this produces nothing
        # Treat 1 specially
        if lbound == 1:
            if intrvl[0] <= 1: # We already know that intrvl[1] >= intrvl[0]
                yield plen * (1,)
        for top in range(max(2, lbound), ubound + 1):
            # All possible values for the largest element
            # form new interval
            # Look at all multiples
            # diff = log(top)
            # Find ranges
            # We must have top^t < I[1] where t is the number of occurences
            top_mult, bot_mult = multipliers(intrvl, top, plen) 
            # top_mult = min(plen, floor(exp(log(intrvl[1]) / log(top))))
            # Since top > 1, if there are s occurences of top
            # We must have top ^ s * (top - 1)^(p-s) >= I[0]
            # Or (top/(top - 1))^s >= I[0] / (top - 1)^p
            # Taking logs, s >= (log(I[0]) - p * log(top - 1))/ log(top/(top-1))
            # bot_mult = max(1, ceil((log(intrvl[0]) - plen * log(top - 1))
            #                        / (log(top) - log(top-1))))
            for kval in range(bot_mult, top_mult + 1):
                nintrvl = [iceil(intrvl[0], top ** kval), intrvl[1] // (top ** kval)]
                yield from (_ + kval * (top,)
                            for _ in very_restricted_parts(plen - kval, top - 1, nintrvl))
                            
def count_restricted_parts(plen: int, bound: int, intrvl: Tuple[float, ...]) -> Iterable[Tuple[int, ...]]:
    """
      Sorted s, sequences of 1..b of length p, so that
      sum_j s[i] * log(i) in I, where I is the given interval

      
    """ 
    # The intersection of (1, bound ** plen) and interval must be nonempty
    # Intersection of (a,b) and (c,d) is (max(a,c), min(b,d))
    # print(f'len = {plen}, interval = {eintrvl}')
    if bound < 1:
        return 0
    elif plen == 0:
        return 0
    elif plen > 0:
        # Find bounds
        # top <= min(bound, eintrvl)
        # lbound = ceil(eintrvl[0] / pval)
        # ubound = floor(eintrvl[1] / pval)
        # Find bounds
        lbound = max(1, ceil(exp(intrvl[0] / plen)))
        # l^plen >= I[0]
        ubound = min(bound, floor(exp(intrvl[1] /  plen)))
        # u^plen <= I[1]
        contrib = 0
        for top in range(lbound, bound + 1):
            # form new interval
            # Look at all multiples
            diff = log(top)
            for kval in range(1, plen + 1): # Number to entries with top
                nintrvl = [intrvl[0] - kval * diff, intrvl[1] - kval * diff]
            
                contrib += count_restricted_parts(plen - kval, top - 1, nintrvl)
        return contrib

def candidates(base: int, mval: int, cutoff: int | None = None) -> Iterable[Tuple[int, ...]]:

    # Find the upper bound
    upper = floor(log(mval * base)/(log(base/(base - 1)))) if cutoff is None else cutoff
    # print(f'upper = {upper}')
    intx = [((base ** (_ - 1) + mval - 1) // mval, (base ** _ - 1) // mval)
            for _ in range(1, upper + 1)]
    intervals = ((_, (log(val[0]), log(val[1]))) for _, val in enumerate(intx, start=1)
                 if val[0] > 0 and val[1] > 0)
    # print(f'{intervals}')
    # return sum((count_restricted_parts(_, base - 1, intrvl)
    #             for _, intrvl in enumerate(intervals, start=1)))
    yield from chain(*(very_restricted_parts(_, base - 1, intrvl)
                       for _, intrvl in intervals))

def get_digits(base: int, val: int) -> Tuple[int, ...]:
    value = ()
    valx = val
    while valx > 0:
        value = (valx % base,) + value
        valx //= base
    return value

def multiples(base: int, mval: int) -> Iterable[Tuple[int, ...]]:

    yield from (result for _ in candidates(base, mval)
                if tuple(sorted(get_digits(base, result := mval * prod(_)))) == _)

def check_candidate(base: int, mval: int, cval: Tuple[int, ...]) -> bool:
    return ((ppp := prod(cval) * mval ) >= base ** (len(cval) - 1)
        and ppp < base ** len(cval))

def check_candidates(base: int, mval: int) -> int:
    """
      Return the number of infeasible candidates
    """
    return sum((int(not check_candidate(base, mval, _))
                for _ in candidates(base, mval)))

def bad_candidates(base: int, mval: int) -> int:
    """
      Return the number of infeasible candidates
    """
    yield from (cand for cand in candidates(base, mval)
                if not check_candidate(base, mval, cand))

def multiple_divisors(base: int, mult: int) -> Iterable[int]:
    """
      Given m > 1 find all integers, n, so that the product of its
      digits in base b, is equal to m * n.

      Method: We can prove that the number of digits in such a number
      is k <= (log(m * base)) / log(base/(base-1)).

      We can test all k-digits strings which are composed of 1..b
      in sorted order (since the order of the product doesn't matter).

      For each such we calculate m times their product and then test
      the digits of the resulting number for equality.
      We can immediately rule out those for which the product
      is not in [b^(k-1), b^k).

      Let B = floor of the right hand side. Find all partitions
    """
    pass
