# Romik sequence d(n): Taylor coefficients of theta_3 at the CM point tau = i.
# Ramanujan-type system in the Cayley variable, rescaled so that all derivatives are integers:
#   U' = 2U(e+a-b), a' = 8a(e+a-b), b' = b(8e-16a+4b), e' = 4e^2-4a^2+2ab-b^2
#   e(0)=0, a(0)=b(0)=U(0)=1 ;  d(n) = U^{(2n)}(0) / 18^n
import sys, pickle
try:
    from gmpy2 import mpz
except ImportError:
    mpz = int
N = int(sys.argv[1])            # highest derivative order (2n)
out = sys.argv[2]
e=[mpz(0)]; a=[mpz(1)]; b=[mpz(1)]; U=[mpz(1)]
L1=[e[0]+a[0]-b[0]]; L2=[8*e[0]-16*a[0]+4*b[0]]
binom=[mpz(1)]
for n in range(N):
    # binom = row n of Pascal's triangle
    sU=sa=sb=se=mpz(0)
    for k in range(n+1):
        c=binom[k]; m=n-k
        sU+=c*U[k]*L1[m]
        sa+=c*a[k]*L1[m]
        sb+=c*b[k]*L2[m]
        se+=c*(4*e[k]*e[m]-4*a[k]*a[m]+2*a[k]*b[m]-b[k]*b[m])
    U.append(2*sU); a.append(8*sa); b.append(sb); e.append(se)
    L1.append(e[-1]+a[-1]-b[-1]); L2.append(8*e[-1]-16*a[-1]+4*b[-1])
    binom=[mpz(1)]+[binom[i]+binom[i+1] for i in range(n)]+[mpz(1)]
d=[]
for n in range(N//2+1):
    q,r=divmod(U[2*n],mpz(18)**n)
    assert r==0, n
    d.append(int(q))
assert all(U[k]==0 for k in range(1,N+1,2))
print(d[:8])
pickle.dump(d,open(out,'wb'))
