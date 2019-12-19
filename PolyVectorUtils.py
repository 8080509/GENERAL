import Matrix_Utils
import CharPolyTools
from fractions import Fraction

def factorial(n):
	acc = 1
	for i in range(n):
		acc *= (i+1)
	return acc

def binomial(n,k):
	return int(factorial(n)/(factorial(k)*factorial(n - k)))

def synDivMat(order, root): #Note the order is the original order.
	return Matrix_Utils.Matrix.matFromCell(lambda i,j: 0 if i + 1 > j else root**(j - i - 1), order, order + 1)

def synMulMat(order, root):
	def cellEq(i,j):
		if i == j:
			return -root
		elif i == j + 1:
			return 1
		else:
			return 0
	return Matrix_Utils.Matrix.matFromCell(cellEq, order + 2, order + 1)

def transMat(order, h):
	return Matrix_Utils.Matrix.matFromCell(lambda i,j: 0 if i > j else binomial(j,i) * ((-h)**(j-i)), order + 1, order + 1)

def polyFromVect(vect, basis = (0,0)):
	acc = CharPolyTools.polynomial(0)
	for i in range(vect.m):
		acc += vect.content[i][0] * CharPolyTools.polynomial.basis(i, *basis)
	return acc

def basisConversionMat(n, a1, a2 = (0,0)):
	data = [[]] * (n + 1)
	for i in range(n + 1):
		data[i] = (CharPolyTools.polynomial.basisConv(i, a1, a2) + ([0] * (n - i)))
	return Matrix_Utils.Matrix(data).transpose()

def vectFromPoly(poly, basis = (0,0)):
	tVect = Matrix_Utils.Matrix([poly.coeffs]).transpose()
	return basisConversionMat(poly.order, (0,0), basis).matMult(tVect)

def descentPoly(S):
	I = set(S)
	if len(I) == 0:
		return CharPolyTools.polynomial(1)
	else:
		m = max(I)
		I.remove(m)
		tempPoly = descentPoly(I)
		return (tempPoly.evaluate(m)*CharPolyTools.polynomial.basis(m, -1, -1)) - tempPoly

def polySynDivMat(order, tRoot, basis = (0,0)):
	if type(tRoot) != type(list()):
		root = [tRoot]
	else:
		root = tRoot
	y = Matrix_Utils.Matrix.identity(order + 1)
	for i in range(len(root)):
		y = synDivMat(order - i, root[i]).matMult(y)
	if basis == (0,0) or basis == 0:
		return y
	else:
		x = basisConversionMat(order - len(root), 0, basis)
		z = basisConversionMat(order, basis)
		return x.matMult(y).matMult(z)

def basisConvOp(opMat, basis = (0,0), wBasis = (0,0)):
	order1 = opMat.n - 1
	order2 = opMat.m - 1
	return basisConversionMat(order2, wBasis, basis).matMult(opMat).matMult(basisConversionMat(order1, basis, wBasis))

def desPolyMDiv(m):
	x = basisConversionMat(m - 1, 0, -1)
	y = synDivMat(m,m)
	z = basisConversionMat(m, -1)
	return x.matMult(y).matMult(z)

def descPolySubMax(I):
	poly = descentPoly(I)
	return poly.synDiv(max(I))[0]

def genAllDescSets(m, noEmpty = False):
	dSets = list()
	start = int(noEmpty)
	for i in range(start, 2**m):
		dSets.append(set(filter(bool, [(j+1)*((i%(2**(j+1)))//(2**j)) for j in range(m)])))
	return dSets
