#!/usr/bin/env python3
# ROUTE C — SUZUKI symbolic polarization: can we recover coords from the frame values by a LINEAR/low-degree system?
#
# Represent GF(2)-polynomials in symbols x0..x3 and X0..X3, where Xi := sigma(xi) and (by hsigma) sigma(Xi)=xi^2.
# A monomial = frozenset? NO — variables can appear with exponent >1 (e.g. x0^2). Over GF(2), x_i^2 != x_i as a
# POLYNOMIAL (they are equal as FUNCTIONS on GF(2) but NOT on GF(2^n)), so we must keep true exponents.
# Monomial = tuple of 8 exponents (x0,x1,x2,x3,X0,X1,X2,X3). Poly = set of monomials (coeff in GF(2), so a set = the
# monomials with coeff 1). Addition = symmetric difference. Multiplication = exponent-add per pair.
#
# D_j F := F(shift x_j -> x_j+1, X_j -> X_j+1) + F.   (char 2; e_j shift also shifts Xj=sigma(xj).)
# We inspect deg and whether {values at frame} determine the coords.

from itertools import product

VARS = ['x0','x1','x2','x3','X0','X1','X2','X3']
def mono(**kw):
    e=[0]*8
    for k,v in kw.items(): e[VARS.index(k)]=v
    return tuple(e)
def M(*pairs):
    e=[0]*8
    for name,ex in pairs: e[VARS.index(name)]+=ex
    return tuple(e)

# Poly = frozenset of monomials (GF(2) coeffs)
def padd(*ps):
    r=set()
    for p in ps: r^=set(p)
    return frozenset(r)
def pmulm(p, m):
    return frozenset(tuple(a+b for a,b in zip(mn,m)) for mn in p)
def pmul(p,q):
    r=set()
    for m in q: r^=set(pmulm(p,m))
    return frozenset(r)
def var(name): return frozenset({mono(**{name:1})})
ONE=frozenset({mono()})

x0,x1,x2,x3=var('x0'),var('x1'),var('x2'),var('x3')
X0,X1,X2,X3=var('X0'),var('X1'),var('X2'),var('X3')
def sq(p): return pmul(p,p)

# The 5 Lean forms (s(xi)=Xi):  SF0 = X0*x0*x3 + X0*x1*x2 + X1*x1^2 + X2*x0^2, etc.
SF=[
 padd(pmul(pmul(X0,x0),x3), pmul(pmul(X0,x1),x2), pmul(X1,sq(x1)), pmul(X2,sq(x0))),
 padd(pmul(X0,sq(x2)),      pmul(pmul(X1,x0),x3), pmul(pmul(X1,x1),x2), pmul(X3,sq(x0))),
 padd(pmul(pmul(X0,x2),x3), pmul(pmul(X1,x1),x3), pmul(pmul(X2,x0),x2), pmul(pmul(X3,x0),x1)),
 padd(pmul(X0,sq(x3)),      pmul(pmul(X2,x0),x3), pmul(pmul(X2,x1),x2), pmul(X3,sq(x1))),
 padd(pmul(X1,sq(x3)),      pmul(X2,sq(x2)),      pmul(pmul(X3,x0),x3), pmul(pmul(X3,x1),x2)),
]

def total_deg(p):
    return max((sum(m) for m in p), default=0)

def shift_j(p, j):
    # substitute x_j -> x_j + 1  and  X_j -> X_j + 1 . Expand monomial by monomial.
    xi=j; Xi=j+4
    out=set()
    for m in p:
        # factors: (x_j)^{a} -> (x_j+1)^a ; (X_j)^{b} -> (X_j+1)^b ; rest fixed.
        a=m[xi]; b=m[Xi]
        base=list(m); base[xi]=0; base[Xi]=0; base=tuple(base)
        # (x_j+1)^a = sum_{i} C(a,i) x_j^i ; over GF(2), C(a,i) mod 2 (Lucas). Similarly for X_j.
        for i in range(a+1):
            if _binom2(a,i)==0: continue
            for k in range(b+1):
                if _binom2(b,k)==0: continue
                mm=list(base); mm[xi]+=i; mm[Xi]+=k
                out^={tuple(mm)}
    return frozenset(out)
def _binom2(n,k):
    return 1 if (k & ~n)==0 else 0   # C(n,k) odd  <=>  k submask of n

def Dj(p,j):
    return padd(shift_j(p,j), p)

def show(p):
    if not p: return "0"
    terms=[]
    for m in sorted(p):
        s="".join("%s^%d"%(VARS[i],m[i]) if m[i]>1 else (VARS[i] if m[i]==1 else "") for i in range(8))
        terms.append(s if s else "1")
    return " + ".join(terms)

if __name__=="__main__":
    print("Total degrees of SF_k (as polys in x,X):", [total_deg(p) for p in SF])
    print()
    for k in range(5):
        print("SF%d (deg %d): %s"%(k,total_deg(SF[k]),show(SF[k])))
    print()
    print("=== First discrete derivatives D_j SF_k (deg drop shows recoverable structure) ===")
    for k in range(5):
        for j in range(4):
            d=Dj(SF[k],j)
            print("D_%d SF%d (deg %d): %s"%(j,k,total_deg(d),show(d)))
        print()
    print("=== Second derivatives D_i D_j SF_k : if CONSTANT/linear, coords fall out ===")
    for k in range(5):
        for i in range(4):
            for j in range(i,4):
                d=Dj(Dj(SF[k],j),i)
                if d and total_deg(d)<=2:
                    print("D_%d D_%d SF%d (deg %d): %s"%(i,j,k,total_deg(d),show(d)))
