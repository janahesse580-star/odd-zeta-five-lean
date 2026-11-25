"""Independently verify the B40a numerical certificate, using the Python standard library."""
from collections import Counter
from fractions import Fraction
from math import ceil
import json



def slot_weights(p, d, t):
    def count(a, b):
        return (b*d-t)//p - (a*d-t)//p
    m = 6 + 4*(t < 17*d) + 2*(t < 16*d)
    nd = 6*count(-25, 25) + 4*count(-17, 17) + 2*count(-16, 16) - m
    nz = 5*(count(-59, -34) + count(34, 59))
    v = nz-nd + 6*(50*d//p) + 4*(34*d//p) + 2*(32*d//p) - 10*(25*d//p)
    left, right = (34*d-t)//p, (34*d+t)//p
    best = 0
    for a in reversed(range(m)):
        for e in range(1, m-a+1):
            order = m-e-a
            inc = order if nd > 0 else min(order, nz)
            bad = (right > 0) if e % 2 else (left != right)
            best = max(best, a-v+inc+(e+4 if bad else 0))
        if best:
            yield best


def middle_value(mid):
    p, d = 4*mid.numerator, 4*mid.denominator
    residues = [(v*d)%p for v in (16, 17, 25, 34, 59)]
    walls = sorted({0, p//2, *(min(k, p-k) for k in residues)})
    bags = []
    for l, r in zip(walls, walls[1:]):
        b = (l+r)//2
        bag = sorted((w for start in (b, p-b) for t in range(start, 25*d, p)
                      for w in slot_weights(p, d, t)), reverse=True)
        bags.append((r-l, bag))

    def capped(counts):
        pop = total = 0
        for k in range(16, 0, -1):
            pop += counts[k]
            total += min(40*d, pop)
        return total

    raw = Counter()
    for qty, bag in bags:
        for v in bag:
            raw[v] += qty
    best = capped(raw)
    prior = Counter()
    qmax = 80*d//p
    for q in range(qmax+1):
        for qty, bag in bags:
            if q < len(bag):
                prior[bag[q]] += qty
        counts = prior.copy()
        for qty, bag in bags:
            for j in range(q+1, min(q+8, len(bag))):
                w = bag[j]-2*(j-q)
                if w > 0:
                    counts[w] += qty
        row = 80*d*(qmax-q) - p*((qmax+q+1)*(qmax-q)//2)
        best = min(best, row+capped(counts))
    return Fraction(best, 2000*d)


from pathlib import Path
from itertools import pairwise
from functools import cache
from math import floor, isqrt
from decimal import Decimal, localcontext

F = Fraction
UNIT = 10**12

def require(condition, message):
    if not condition:
        raise ValueError(message)

def up(x):
    return F(ceil(x * UNIT), UNIT)

def small_value(a, b):
    x = (a+b)/2
    n, d = x.numerator, x.denominator
    walls = sorted({0,d,*[(k*n)%d for k in (-59,-34,-25,-17,-16,0,16,17,25,34,59)]})
    first = second = 0
    for lo,hi in pairwise(walls):
        def count(l,r):
            return (2*r*n-lo-hi)//(2*d) - (2*l*n-lo-hi)//(2*d) - ((r-l)*n)//d
        w=max(0,4+6*count(-25,25)+4*count(-17,17)+2*count(-16,16)
              -5*count(-59,-34)-5*count(34,59))
        first += (hi-lo)*w
        second += (hi-lo)*((w-1)**2//4)
    def reciprocal(k):
        start=1 if a>=F(9,11) else 2
        return sum(up(1/(i+a)**k) for i in range(start,17))+up(1/((k-1)*(16+a)**(k-1)))
    return (reciprocal(2)*first + reciprocal(3)*F(first+second,80))/(50*d)

def rows_total(rows, count, first, last, cost):
    require(len(rows)==count,'row count')
    previous=first
    total=0
    for i,(lo,hi,upper) in enumerate(rows):
        a,b=F(lo),F(hi)
        require(a==previous and a<b and upper>=0,f'row coverage at {i}')
        require(ceil(UNIT*(b-a)*cost(a,b))==upper,f'row cost at {i}')
        previous=b
        total+=upper
    require(previous==last,'right endpoint')
    return F(total,UNIT)

def tail_cost():
    def capacity(x,j):
        return max(0,51-x)*sum(j<=14-2*k for k in range(10)) + (84-max(76,25+x))*sum(j<=10-2*k for k in range(6))
    total=0
    for j in range(1,15):
        for a,b in [(F(50),F(51)),(F(51),F(59))]:
            u,v=capacity(a,j),capacity(b,j)
            cuts=[a,b]
            if (u-40)*(v-40)<0:
                cuts.insert(1,a+(b-a)*(40-u)/(v-u))
            for x,y in pairwise(cuts):
                total+=(y-x)*(min(40,capacity(x,j))+min(40,capacity(y,j)))/2
    return total/2000+F(9,40)

# Intervals in units of 10^-12. Decimal.ln uses correctly rounded
# half-even arithmetic. Enclose the initial division and each logarithm.
def interval(x):
    return floor(x*UNIT), ceil(x*UNIT)

def add(*bounds):
    return sum(b[0] for b in bounds),sum(b[1] for b in bounds)

def scale(bounds,q):
    a,b=sorted((bounds[0]*q,bounds[1]*q))
    return floor(a),ceil(b)

@cache
def log_bounds(x):
    require(x>0,'log domain')
    with localcontext() as c:
        c.prec=52
        v=Decimal(x.numerator)/Decimal(x.denominator)
        lo=v.next_minus().ln().next_minus()
        hi=v.next_plus().ln().next_plus()
        return floor(F(lo)*UNIT),ceil(F(hi)*UNIT)

@cache
def atan_small(x):
    if x<0: return scale(atan_small(-x),-1)
    term=x
    value=F(0)
    for i in range(24):
        value+=(-1)**i * term/(2*i+1)
        term*=x*x
    return floor(value*UNIT),ceil((value+term/49)*UNIT)

PI=add(scale(atan_small(F(1,5)),16),scale(atan_small(F(1,239)),-4))
def atan(x):
    if x<0: return scale(atan(-x),-1)
    if x>1: return add(scale(PI,F(1,2)),scale(atan(1/x),-1))
    if x>F(1,2): return add(scale(PI,F(1,4)),atan_small((x-1)/(x+1)))
    return atan_small(x)

BLOCKS=[(0,50,5),(186,236,5),(68,168,-6),(84,152,-4),(86,150,-2)]
KNOTS=[[0,1700],[2500,2200],[5000,1000],[10000,-2000],[20000,-8100],
       [35000,-16300],[55000,-25700],[85000,-45500],[400000,-45500]]
PEAK=F(-8443338478,10**9)
def point(t):
    for (a,c),(b,d) in pairwise(KNOTS):
        if a<=t<=b:
            return F(118,100)-(c+F((d-c)*(t-a),b-a))/100000,F(t,100000)
    raise ValueError(t)

def primitive(x,y):
    angle=atan(x/y) if y else scale(PI,F(1 if x>0 else -1,2))
    return add(scale(log_bounds(x*x+y*y),x/2),interval(-x),scale(angle,y))

def square(z):
    x,y=z
    return x*x-y*y,2*x*y

def dist2(z,w):
    return (z[0]-w[0])**2+(z[1]-w[1])**2

def sqrt_lower(x):
    return F(isqrt(floor(x*10**12)),10**6)

def analytic(data):
    require(data['knots']==KNOTS,'contour knots')
    panels=data['panels']
    require(len(panels)==120 and panels==sorted(set(panels)) and panels[0]==0 and panels[-1]==400000
            and all(t in panels for t,c in KNOTS),'panel cover')
    raw=data['circles']
    require(len(raw)==34 and len({(x,y) for x,y,r,m in raw})==34 and sum(row[3] for row in raw)==1000,'witness mass')
    require(all(y>0 and 0<r<=1000 and m>0 and x*x+y*y<=9*10**6 for x,y,r,m in raw),'witness support')
    circles=[((F(x,1000),F(sign*y,1000)),F(r,1000),F(m,2000)) for x,y,r,m in raw for sign in (1,-1)]
    energy=F(0)
    for u,r,m in circles:
        for v,s,k in circles:
            separation=r*r if u==v else dist2(u,v)
            energy+=m*k*F(log_bounds(separation)[0],2*UNIT)
    @cache
    def field_upper(t):
        x,y=point(t)
        phase=scale(PI,-2*y)
        for l,r,k in BLOCKS:
            w=F(r-l,100)
            diff=add(primitive(x+F(r-118,100),y),scale(primitive(x+F(l-118,100),y),-1))
            phase=add(phase,scale(add(diff,scale(add(log_bounds(w),interval(-1)),-w)),k))
        z2=square((x,y))
        potential=sum(m*F(log_bounds(max(r*r,dist2(z2,u)))[1],2*UNIT) for u,r,m in circles)
        return F(phase[1],UNIT)+F(8,5)*potential
    for a,b in pairwise(panels):
        z,w=point(a),point(b)
        length2=dist2(z,w)
        ph=F(0)
        for l,r,k in BLOCKS:
            for v in (l,r):
                x=z[0]+F(v-118,100)
                y=w[0]+F(v-118,100)
                dx=max(0,min(x,y),-max(x,y))
                near=sqrt_lower(dx*dx+z[1]**2)
                require(near>0,'phase separation')
                ph+=abs(k)*length2/(2*near)
        c=F(0)
        z2,w2=square(z),square(w)
        for u,r,m in circles:
            d=max(r,sqrt_lower(min(dist2(z2,u),dist2(w2,u))))
            c+=m*(dist2(z2,w2)/(2*d*d)+length2/d)
        bound=max(field_upper(a),field_upper(b))+ph/4+F(2,5)*c
        require(bound<=PEAK,f'continuous chord {a}..{b}')
    tail=add(scale(log_bounds(F(5,4)),5),scale(log_bounds(F(7,5)),F(8,5)),
             scale(log_bounds(F(4)),-F(9,5)),scale(PI,-8))
    for l,r,k in BLOCKS:
        w=F(r-l,100)
        tail=add(tail,scale(add(log_bounds(w),interval(-1)),-k*w))
    require(F(tail[1],UNIT)<=PEAK,'ray budget')
    return F(12,5)-F(8,5)*F(log_bounds(F(8,5))[0],UNIT)+PEAK-F(4,5)*energy

def main():
    path=Path(__file__).resolve().parent/'b40a/certificate.json'
    data=json.loads(path.read_text(encoding='utf8'))
    require(data['model']=='B40a-v1','model')
    middle=rows_total(data['arithmetic']['middle'],1375,F(11,20),F(50),lambda a,b: middle_value((a+b)/2))
    small=rows_total(data['arithmetic']['small_period'],706,F(0),F(1),small_value)
    high=tail_cost()
    require(middle==F(5244756877432,UNIT) and high==F(1671,2000),'arithmetic totals')
    print(f'1375 middle rows: {middle}; 706 period rows: {small}; integrated high tail: {high}',flush=True)
    A=analytic(data['analytic'])
    C=small+middle+high
    require(A<=-F(619,100) and C<=F(61405,10000) and A+C<=-F(495,10000),'final inequalities')
    print(f'34 circle pairs; 119 continuous chord budgets; infinite-ray budget verified.')
    print(f'Independent analytic upper bound {A}; arithmetic upper bound {C}.')
    print('Rounded combined exponent <= -99/2000.')

if __name__=='__main__':
    main()
