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
# determine the nth fibonacci number given that the 0th and 1st numbers are 0 and 1, respectively.
def fib(n):
  if n == 0:
    return 0
  elif n == 1:
    return 1
  else:
    return fib(n-1) + fib(n-2)

assert repr(str(fib(0))) == repr(str(0)) or (fib(0) == 0)
assert repr(str(fib(1))) == repr(str(1)) or (fib(1) == 1)
