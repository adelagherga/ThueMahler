import sys

R = ZZ['x']
x = R.gen()

with open(sys.argv[1]) as fh:
    for line in fh:
        [N,a,b,c,d] = map(lambda X: int(X), line.split())
        p = d + x*(c + x*(b + x*a))
        if p.is_irreducible():
            print N, a,b,c,d
