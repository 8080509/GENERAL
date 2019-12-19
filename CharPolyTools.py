from fractions import Fraction
from Matrix_Utils import Matrix

def factorial(n):
	acc = 1
	for i in range(n):
		acc *= (i+1)
	return acc

class polynomial(object):
	def __init__(self, input = None):
		a = type(input)
		if input == None:
			data = [0]
		elif a == type([]):
			data = list(input)
		elif a == type(self):
			data = list(input.coeffs)
		else:
			try:
				data = [Utils.classCorrection(input, Fraction)]
			except:
				raise
				raise TypeError('The input ' + repr(input) + ' of type ' + str(a) + ' is not supported for polynomial generation.')
		self.coeffs = list(map(Fraction, data))
		while (len(self.coeffs) > 1 and self.coeffs[-1] == 0):
			self.coeffs.pop(-1)
		self.order = len(self.coeffs) - 1
	
	def __mul__(self, tInput):
		input = Utils.classCorrection(tInput, polynomial)
		newList = [0]*(self.order + input.order + 1)
		for i in range(self.order + 1):
			for j in range(input.order + 1):
				newList[i+j] += self.coeffs[i]*input.coeffs[j]
		return polynomial(newList)
	
	__rmul__ = __mul__
	
	def synDiv(self, input):  #input is the zero you want to factor out
		newList = [0]*(self.order + 1)
		newList[-1] = self.coeffs[-1]
		i = self.order - 1
		while i >= 0:
			newList[i] = (newList[i + 1]*input) + self.coeffs[i]
			i -= 1
		rem = newList.pop(0)
		quo = polynomial(newList)
		return quo, rem
	
	def __str__(self, var = 'x'):
		msg = str(self.coeffs[0])
		if self.order >= 1:
			msg +=(' + ' + str(self.coeffs[1]) + var)
		for i in range(2, self.order + 1):
			msg +=(' + ' + str(self.coeffs[i]) + var + str(i))
		return msg
	
	def __repr__(self):
		msg = str(self)
		msg +=(' || order = ' + str(self.order))
		return msg
	
	def __add__(self, tInput):
		if type(tInput) != type(self):
			input = polynomial(tInput)
		else:
			input = tInput
		L1 = list(self.coeffs)
		L2 = list(input.coeffs)
		LT = max(len(L1),len(L2))
		L1 += ([0]*(LT - len(L1)))
		L2 += ([0]*(LT - len(L2)))
		L3 = [L1[i]+L2[i] for i in range(LT)]
		return polynomial(L3)
	
	__radd__ = __add__
	
	def __sub__(self, input):
		return self + (-1 * input)
	
	def __rsub__(self, input):
		return input + (-1* self)
	
	def polyDiv(self, input):  #input is a second polynomial  ||  Performs polynomial long division
		temp = polynomial(self)
		quo = polynomial()
		while temp.order >= input.order and any(temp.coeffs):
			#print(temp.order, input.order, temp.coeffs)
			lPoly = (temp.coeffs[-1]/input.coeffs[-1]) * polynomial.regBasis(temp.order - input.order)
			temp -= lPoly * input
			quo += lPoly
		rem = polynomial(temp)
		return quo, rem
	
	def regBasis(n):
		return polynomial(([0] * n) + [1])
	
	def basis(n, a = 0, factPow = 0): #regular by default.  -1 does falling factorial, +1 does rising.
		if a == 0:  #(xCk) = basis(k,-1,-1)
			return polynomial.regBasis(n)*(Fraction(factorial(n))**factPow)  #More efficient, though this clause could be removed.
		else:
			temp = polynomial(1)
			for i in range(n):
				temp *= polynomial([a * i,1])
			return temp*(Fraction(factorial(n))**factPow)
	
	def basisConv(order, tA1, tA2 = (0,0)):
		if type(tA1) != type((0,0)):
			a1 = (tA1, 0)
		else:
			if len(tA1) == 1:
				a1 = (*tA1, 0)
			else:
				a1 = tA1
		if type(tA2) != type((0,0)):
			a2 = (tA2, 0)
		else:
			if len(tA2) == 1:
				a2 = (*tA2, 0)
			else:
				a2 = tA2
		if a1 == a2:
			return (([0] * order) + [1])
		elif a2 == (0,0):
			return polynomial.basis(order, *a1).coeffs
		else:
			newL = []
			temp = polynomial.basis(order, *a1)
			num = 1
			while num > 0:
				fact = polynomial.basis(polynomial(temp).order, *a2)
				newL.append((temp//fact).coeffs[0])
				temp = temp % fact
				num = fact.order
			return newL[::-1]
	
	def __floordiv__(self, input):
		return self.polyDiv(polynomial(input))[0]
	
	def __rfloordiv__(self, input):
		return polynomial(input).polyDiv(self)[0]
	
	def __mod__(self, input):
		return self.polyDiv(polynomial(input))[1]
	
	def __rmod__(self, input):
		if type(input) == type(0):
			return self.synDiv(input)
		else:
			return polynomial(input).polyDiv(self)[1]
	
	def evaluate(self, input):
		acc = Fraction(0)
		for i in range(self.order + 1):
			acc += self.coeffs[i]*(input**i)
		return acc
	
	#def toMat(self):
	#	

"""class newComplex(object):
	def __init__(self, *args):
		self.real = Fraction(0)
		self.imag = Fraction(0)
		if len(args) == 1:
			if isinstance(args[0], (complex, newComplex)):
				self.real = Fraction(args[0].real)
				self.imag = Fraction(args[0].imag)
			else:
				self.real = Fraction(args[0])
		elif len(args) == 2:
			self.real = Fraction(args[0])
			self.imag = Fraction(args[1])
		elif len(args) >= 3:
			raise TypeError(str(args) + ' should have at most 2 entries for newComplex numbers.')
	
	def __add__(self, tInput):
		input = Utils.classCorrection(tInput, newComplex)
		return newComplex(self.real + input.real, self.imag + input.imag)
	
	__radd__ = __add__
	
	def __sub__(self, tInput):
		input = Utils.classCorrection(tInput, newComplex)
		return newComplex(self.real - input.real, self.imag - input.imag)
	
	def __rsub__(self, tInput):
		input = Utils.classCorrection(tInput, newComplex)
		return input.__sub__(self)
	
	def __mul__(self, tInput):
		input = Utils.classCorrection(tInput, newComplex)
		return newComplex((self.real * input.real) - (self.imag * input.imag), (self.imag * input.real) + (self.real * input.imag))
	
	__rmul__ = __mul__
	
	def __truediv__(self, tInput):
		input = Utils.classCorrection(tInput, newComplex)
		A = self.real
		B = self.imag
		a = input.real
		b = input.imag
		return newComplex(((A * a) + (B * b))/((a * a) + (b * b)),-(((A * b) - (B * a))/((a * a) + (b * b))))
	
	def __rtruediv__(self, tInput):
		input = Utils.classCorrection(tInput, newComplex)
		return newComplex(input).__truediv__(self)
	
	def __repr__(self):
		return (str(self.real) + ' + ' + str(self.imag) + ' i')
	
	def __str__(self):
		return ('(' + repr(self) + ')')
	
	def __pow__(self, exp):
		temp = newComplex(1)
		exp = Utils.classCorrection(exp, int)
		for i in range(exp):
			temp *= self
		return temp
	
	def __eq__(self, tInput):
		input = Utils.classCorrection(tInput, newComplex)
		return (self.real == input.real) and (self.imag == input.imag)"""

class Utils:
	def classCorrection(x, target):
		#print('Correcting', x, target)
		if isinstance(x, target):
			return x
		else:
			return target(x)
