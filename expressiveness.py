import random
from z3 import *

def bimap_expressive():
    m, b, d0, d1, r0, r1, x = Reals('m c d0 d1 r0 r1 x')

    norm = If(d0 != d1, (x - d0) / (d1 - d0), 0.5)
    linear_interp = r0*(1 - norm) + r1*norm # d3's bimap implementation
    line = m*x + b # Define a general line

    domain_range_ok = And(d0 <= d1, r0 <= r1)
    point_in_domain = And(x >= d0, x <= d1)
    all_points_eq = ForAll([x],
                            Implies(point_in_domain,
                                    linear_interp == line))

    bimap_complete  = ForAll([m, b],
                             Exists([d0, d1, r0, r1],
                                    And(domain_range_ok,
                                        all_points_eq)))

    s = Solver()
    s.add(Not(bimap_complete))             # look for counter-example
    if s.check() == sat:
        model = s.model()
        print(model)
    else:
        print("UNSAT")

bimap_expressive()