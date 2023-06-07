import sys
import time
import itertools
from itertools import accumulate, product, permutations, combinations
import collections
from collections import Counter, OrderedDict, deque, defaultdict, ChainMap
from functools import lru_cache
import math
from math import sqrt, sin, cos, tan, ceil, fabs, floor, gcd, exp, log, log2
import fractions
from typing import List, Tuple
import numpy as np
import random
import heapq
# given a number, determine whether or not it is even.
def isEven(n):
  if n % 2 == 0:
    return True
  else:
    return False
# given a number m and a number n, determine whether n is divisible by m. Return a boolean value.
def isDivisible(m, n):
  if (n % m == 0):
    return True
  else:
    return False
# given a number, determine whether it is prime.
def isPrime(n):
    if n <= 1:
        return False
    elif isEven(n):
        return False
    else:
        for i in range(3, n):
            if isDivisible(i, n):
                return False
        return True

assert repr(str(isPrime(7))) == repr(str(True)) or (isPrime(7) == True)
assert repr(str(isPrime(8))) == repr(str(False)) or (isPrime(8) == False)


