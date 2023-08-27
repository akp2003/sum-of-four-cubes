#Hello World! 
#This is Arshak Parsa!
#This code tries to find the solution in O(1)
#It's a wonderful problem! I hope u enjoy it :)
#for more info , check out this page:
#https://en.m.wikipedia.org/wiki/Sum_of_four_cubes_problem

def check(A, n):
	return sum([x**3 for x in A])==n

def test(a, b, c, n):
	x=n-a**3-b**3-c**3
	d=round(abs(x)**(1./3.))
	#print(a, b, c)
	if d**3==abs(x):
		if d!=0:
			d=(x//d**3)*d
		return (a, b, c, d)

def checkSquare(x, y, z, l, isfill, n):
	if isfill:
		for i in range(2*l+1):
			for j in range(2*l+1):
				r=test(x+i, y+j, z, n)
				if r!=None:
					return r
	else:
		for i in range(2*l+1):
			r=test(x+i, y, z, n)
			if r!=None:
				return r
			r=test(x+i, y+2*l, z, n)
			if r!=None:
				return r
		
		for i in range(1, 2*l):
			r=test(x, y+i, z, n)
			if r!=None:
				return r
			r=test(x+2*l, y+i, z, n)
			if r!=None:
				return r
			
def bruteforce(n, l):#l starts from 1
	for i in range(-l, l+1):
		r=checkSquare(-l, -l, i, l, (i==-l or i==l), n)
		if r!=None:
			return r
	return bruteforce(n, l+1)

def addList(k,L,n):
	x=L[0]*k
	for i in range(1,len(L)):
		x+=L[i]*n**i
	return x

def checkN(n,a,b,A,B,C,D):
	if n%a in [b,a-b]:
		k=1
		if n%a!=b:
			k=-1
		n=(n-b*k)//a
		return (addList(k,A,n), addList(k,B,n),addList(k,C,n),addList(k,D,n),	)					
	

def find(n):
	#wikipedia
	if n%6==0:
		n=n//6
		return (n+1, n-1, -n, -n)
	
	if n%6==3:
		n=(n-3)//6
		return (n, -n+4, 2*n-5, -2*n+4)					
	
	L=[
	[18,1,[14,2],[-23,-2],[-26,-3],[30,3]],
	[18,7,[2,1],[-1,6],[-2,8],[2,-9]],
	[18,8,[-5,1],[14,-1],[29,-3],[-30,3]],
	
	]
	
	for l in L:
		r=checkN(n,*l)
		if r!=None:
			return r
	
	return bruteforce(n, 1)

from time import time
st=time()
#Example
for i in range(-30, 60):
	a=find(i)
	print(i, a, check(a, i))
print(time()-st)
