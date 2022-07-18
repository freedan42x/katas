Ackermann=A=lambda m,n:m==0and n+1or n==0and A(m-1,1)or A(m-1,A(m,n-1))
