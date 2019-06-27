#!/usr/bin/env python

P = int(input("prime number: "))
N = int(input("natural number: "))

import copy
import string
import numpy as np
import matplotlib.pyplot as plt
import time
import sys

class Polynom:

	def __init__(self, s, P):
		self.P = P

		if isinstance(s, list):
			n = len(s)
			if n > 0:
				assert s[n-1] != 0

			self.coeffs = s
		elif isinstance(s, str):
			xs = s.split(" + ")
			xs = list(map(lambda x: x.split("x^"),xs))
			# print(s)
			# print(xs)

			self.coeffs = [0] * (int(xs[len(xs)-1][1]) + 1)
			i = 0
			for x in xs:
				power = int(x[1])
				a = int(x[0])

				self.coeffs[power] = a

	def degree(self):
		return len(self.coeffs) - 1


	def __getitem__(self, i):
		return self.coeffs[i] if i <= self.degree() else 0

	def __add__(self, other):
		n = max(self.degree(), other.degree())
		new_coeffs = []

		# start at highest degree
		for i in range(n,-1,-1):
			c = (self[i] + other[i]) % self.P
			if c == 0 and len(new_coeffs) == 0:
				continue
			else:
				new_coeffs.append(c)

		return Polynom(list(reversed(new_coeffs)), self.P)

	def __mul__(self, other):
		if isinstance(other, self.__class__):
			return self.polynom_mul(other)
		elif isinstance(other, int):
			return self.scale(other)

	def polynom_mul(self, other):
		a = self.degree()
		b = other.degree()

		if a == -1 or b == -1:
			return Polynom([], self.P)

		n = a + b

		new_coeffs = []

		for i in range(0,(n+1)):
			c = 0
			for k in range(0, i+1):
				c += self[k]*other[i-k]

			new_coeffs.append(c % self.P)

		return Polynom(new_coeffs, self.P)

	def scale(self, scalar):
		for i in range(0, len(self.coeffs)):
			self.coeffs[i] = (self.coeffs[i] * scalar) % self.P
		return self

	def __mod__(self, other):
		# print(self, "%", other)

		f = copy.deepcopy(self)

		P = self.P
		n = f.degree()
		m = other.degree()

		b = inv(other[m],P)

		# cancel highest coeff as long as m <= n
		while n >= m:
			a = f[n]
			new_n = n
			uneq0 = False 
			for i in range(n,n-m-1, -1):
				# print("    in:", f.coeffs[i], - a*b*other[i-(n-m)])
				f.coeffs[i] = (f.coeffs[i] - a*b*other[i-(n-m)]) % P
				# print("    out:", f.coeffs[i])

				if f.coeffs[i] == 0 and not uneq0:
					new_n = new_n-1
				else:
					uneq0 = True # as long as the coeff is 0 we decrease the degree
			n = new_n
			# print("    g:", f)

		return f.prune()

	def is_divisible_by(self, other):
		return (self % other).degree() == -1


	# removes 0s
	def prune(self):
		n = self.degree()
		if n == -1:
			return self

		while self[n] == 0 and n >= 0:
			n = n - 1

		new_coeffs = []
		for i in range(0, n+1):
			new_coeffs.append(self[i])

		self.coeffs = new_coeffs

		return self

	def __str__(self):

		if self.degree() == -1:
			return "0"

		s = ""
		add = False
		for (i, a) in enumerate(self.coeffs):
			if a != 0 and add == False:
				if i == 0:
					s += f"{a}"
				elif i == 1 and a == 1:
					s += f"x"
				elif i == 1:
					s += f"{a}x"
				elif a == 1:
					s += f"x^{i}"
				else:
					s += f"{a}x^{i}"
				add = True
				continue

			if add == True:
				if a == 0:
					continue
				elif i == 1 and a == 1:
					s += f" + x"
				elif i == 1:
					s += f" + {a}x"
				elif a == 1:
					s += f" + x^{i}"
				else:
					s += f" + {a}x^{i}"
		return s

	def __repr__(self):
		return str(self)

	def __hash__(self):
		n = len(str(self.P))
		s = ""
		for a in reversed(self.coeffs):
			x = str(a)
			while len(x) < n: x = '0' + x
			s += x

		if s == "":
			return 0

		return int(s)

	def __eq__(self, other):
		return hash(self) == hash(other)


def inv(x, mod):
	for y in range(1, mod):
		if (x * y) % mod == 1:
			return y

def devisors(x):
	d = []
	for y in range(1,x):
		if (x % y) == 0:
			d.append(y)
	return d

def greatest_divisor(x):
	d = x - 1
	while (x % d) != 0:
		d = d -1
	return d

class Field:

	def __init__(self, N, P):

		self.N = N
		self.P = P

		self.divisors = devisors(N)
		self.elems = []
		self.symbols = dict()
		self.numbers = dict()
		self.addition = np.zeros((pow(P,N),pow(P,N)))
		self.multiplication = np.zeros((pow(P,N),pow(P,N)))


		t0 = time.time()

		self.find_field()

		t1 = time.time()
		print(f"found polynomial: {t1-t0}s")

		self.calculate_tables()
		t2 = time.time()
		print(f"calculated tables: {t2-t1}")
		print(f"total time: {t2-t0}s")

		self.plot()


	def find_field(self):
		# has to be of degree n
		# has to divide x^(p^n)-x
		# factors of x^(p^n)-x can only be divided by polynoms of degree k | n
		N = self.N
		P = self.P

		coeffs = [0] * (N+1)
		coeffs[N] = 1

		q = Polynom(f"-1x^1 + 1x^{pow(P,N)}", P)
		f = Polynom(coeffs, P)

		self.find_irreducible_polynom(N-1, q, f)

		hs = [0] * N
		hs[N-1] = 1
		h = Polynom(hs, P)

		self.find_all_normed_polynoms_of_degree(N-1, h, self.elems)

		# print(self.f)
		# print(self.elems, len(self.elems))

	def calculate_tables(self):
		for (i,x) in enumerate(self.elems):
			self.numbers[x] = i

		count = 0
		total = pow(self.P, self.N * 2)
		for (i,x) in enumerate(self.elems):
			for (j,y) in enumerate(self.elems):
				r = (x * y) % self.f
				s = (x + y) % self.f
				self.multiplication[i][j] = self.numbers[r]
				self.addition[i][j] = self.numbers[s]
				count += 1
				sys.stdout.write(f"{count}/{total} operations done...")
				sys.stdout.flush()



		# for (i,x) in enumerate(self.elems):
		# 	print(x, ",\thash:", hash(x), ",\tnum:", self.numbers[x])

		# n = pow(P,N)
		# if labels:
		# 	for i in range(0, n):
		# 		for j in range(0, n):
		# 			a = self.addition[i][j]
		# 			m = self.multiplication[i][j]
		# 			ax[I][N].text(i, j, str(int(a)), va='center', ha='center')
		# 			ax[J][N].text(i, j, str(int(m)), va='center', ha='center')

	def plot(self):
		P = self.P
		N = self.N

		fig, (ax0, ax1) = plt.subplots(1, 2, constrained_layout=True)

		fig.suptitle(r"$F_{" + str(pow(P,N)) + r"} = F_{" + f"{P}^{N}"  + r"} \cong \mathbb{Z}_{" + str(P) + r"} / (" + str(self.f) + ")$", fontsize=20, fontweight='bold')
		
		# ax0 = fig.add_subplot(gj[0])
		# ax1 = fig.add_subplot(gj[1])

		ax0.matshow(self.addition, cmap=plt.cm.Blues)
		ax1.matshow(self.multiplication, cmap=plt.cm.Blues)

		ax0.set_title('+',y=1.1)
		ax1.set_title('*', y=1.1)

		plt.show()


	def print_symbol_tables(self):
		abc = list(string.ascii_lowercase)

		for (i,x) in enumerate(self.elems, -2):
			if str(x) == "0":
				self.symbols[x] = "0"
			elif str(x) == "1":
				self.symbols[x] = "1"
			else:
				self.symbols[x] = abc[i]


		header = "\t"

		for x in self.elems:
			header += self.symbols[x] + "\t"

		mtable = header + "\n\n"
		atable = header + "\n\n"

		for x in self.elems:
			mrow = self.symbols[x] + "\t"
			arow = self.symbols[x] + "\t"
			for y in self.elems:
				r = (x * y) % self.f
				s = (x + y) % self.f
				mrow += self.symbols[r] + "\t"
				arow += self.symbols[s] + "\t"

			mtable += mrow + "\n"
			atable += arow + "\n"

		P = self.P
		N = self.N

		print(f"\nG({P}^{N}) ~ Z_{P} / ({self.f})")

		print("\nADDITION:\n")
		print(atable)

		print("\nMULTIPLICATION:\n")
		print(mtable)

	# f has to be of degree d, permutates 0 to d coeff
	def find_all_normed_polynoms_of_degree(self, d, f, a):
		P = self.P
		if d == 0:
			for k in range(0, P):
				f.coeffs[d] = k

				a.append(copy.deepcopy(f).prune())

		else:
			for k in range(0, P):
				f.coeffs[d] = k
				self.find_all_normed_polynoms_of_degree(d-1, f, a)

			
	def find_irreducible_polynom(self, i, q, f):
		P = self.P
		if i == 0:
			for k in range(0, P):
				f.coeffs[i] = k
				# print("f:", f, f.degree(), ", r:", q % f)
				if q.is_divisible_by(f):
					if self.is_irreducible(f):
						self.f = f
						return True

		else:
			for k in range(0, P):
				f.coeffs[i] = k
				if self.find_irreducible_polynom(i-1, q, f):
					return True


	def is_irreducible(self, f):
		for d in self.divisors:
			hs = [0] * (d + 1)
			hs[d] = 1 # d degree normed
			h = Polynom(hs, self.P)
			all_polys = []
			self.find_all_normed_polynoms_of_degree(d-1, h, all_polys)
			
			for g in all_polys:
				if f.is_divisible_by(g):
					return False

		return True


# all normed polynoms f of degree n are checked ~ p^n
# check if x^(p^n)-x is divisible by f ~ degree(x^(p^n)-x) = p^n
# check if f is irreducible, all normed polynoms of degree d | n are checked ~ sum(p^d * d: d|n)

# so ~ O(p^(2n)* d * p^d) < O(n/2 * p^(2n + n /2)), worsed case
# where d is greatest divisor of n
# e.g. n=4, p=5:  ~ O(2*5^(10)) = O(10^7)


# n = 3
# ps = [2, 3]

# fig = plt.figure()
# gs0 = fig.add_gridspec(1, len(ps))

# for (i,p) in enumerate(ps):
# 	gp = gs0[i].subgridspec(n, 1)

# 	for j in range(1, n):
# 		gj = gp[j].subgridspec(1,2)
# 		Field(N=j, P=p)

Field(N=N,P=P)

# f = Polynom("1x^0 + 1x^1 + 1x^4", P)
# g = Polynom("-1x^1 + 1x^2401", P)

# print(g % f)

