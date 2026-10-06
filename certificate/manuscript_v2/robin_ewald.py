from mpmath import mp, mpf, e1, exp, pi, euler, log, sqrt
mp.dps=110
l=sqrt(2)/sqrt(sqrt(3))
# Ewald with q0 = (1/2)E1(pi r^2): R = -(gamma+log pi)/2 - 1/2 + sum_{v!=0} q0(v) + sum_{k!=0} e^{-pi k^2}/(2 pi k^2)
s1=mpf(0); s2=mpf(0)
for a in range(-16,17):
  for b in range(-16,17):
    if a==0 and b==0: continue
    r2=l*l*(a*a+a*b+b*b)
    s1+=e1(pi*r2)/2
    s2+=exp(-pi*r2)/(2*pi*r2)
R=-(euler+log(pi))/2-mpf(1)/2+s1+s2
print("R_Lambda =",R)
