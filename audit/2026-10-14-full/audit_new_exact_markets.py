from fractions import Fraction as F
from itertools import permutations
from math import factorial, exp, log, sqrt
import json

def compositions(n,k,prefix=()):
    if k==1:
        yield prefix+(n,)
    else:
        for a in range(n+1):
            yield from compositions(n-a,k-1,prefix+(a,))

def run_market(m,q,prefs,counts):
    n=m*q
    active=set(range(m)); cap=[F(q) for _ in range(m)]; t=F(0)
    rank=F(0); f=F(1); atoms=[(F(q),F(0))]
    groups=[(p,c) for p,c in zip(prefs,counts) if c]
    old=[None]*len(groups)
    while active:
        choices=[next(g for g in p if g in active) for p,c in groups]
        if t:
            switching=sum(c for (_,c),g,o in zip(groups,choices,old) if g!=o)
            f+=F(switching,q*len(active))*(1-t)
            if switching: atoms.append((F(switching,len(active)),t))
        flow=[sum(c for (_,c),g in zip(groups,choices) if g==a) for a in range(m)]
        dt=min(cap[g]/flow[g] for g in active if flow[g])
        rank+=dt*F(sum(c*(p.index(g)+1) for (p,c),g in zip(groups,choices)),n)
        for g in active: cap[g]-=dt*flow[g]
        active={g for g in active if cap[g]}; old=choices; t+=dt
    assert t==1 and all(x==0 for x in cap)
    return rank,f,atoms

results=[]
for m,q in [(1,1),(1,5)]+[(2,q) for q in range(1,6)]+[(3,q) for q in range(1,4)]+[(4,1)]:
    prefs=list(permutations(range(m))); n=m*q; nf=factorial(n)
    den=factorial(m)**n
    e_rank=F(0); e_f=F(0); cost={t:0. for t in (0.01,.1,1.,2.,10.)}
    profiles=0; multisets=0
    for counts in compositions(n,len(prefs)):
        # Independent profiles sharing the same preference counts have identical PS paths.
        factprod=1
        for c in counts: factprod*=factorial(c)
        mult=nf//factprod
        r,f,atoms=run_market(m,q,prefs,counts)
        e_rank+=mult*r; e_f+=mult*f
        for theta in cost:
            cost[theta]+=mult*sum(float(w)*(1-exp(-theta*float(1-time))) for w,time in atoms)/(q*den)
        profiles+=mult; multisets+=1
    assert profiles==den
    e_rank/=den; e_f/=den
    affine=1+F(m-1,m)*(e_f-1)
    assert e_rank<=affine
    a=log(m)/q
    assert float(e_rank)<=1+sqrt(2*a)+a+1e-12
    for theta,value in cost.items():
        assert value<=theta+a+1e-10,(m,q,theta,value)
    results.append(dict(m=m,q=q,profiles=profiles,anonymous_profiles=multisets,
        expected_rank=str(e_rank),exposure=str(e_f),affine_upper=str(affine),
        expected_rank_decimal=float(e_rank),affine_slack=str(affine-e_rank),
        terminal_cost_checks=cost))
print(json.dumps(results,indent=2))
