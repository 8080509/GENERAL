
from itertools import product

from Utils import defValDict

class MathObj(object):
	
	def __init__(self, data = ()):
		nData = defValDict(0)
		for arg in data:
			nData[arg[1:]] += arg[0]
		fData = []
		for key, value in nData.items():
			if value:
				fData.append((value,) + key)
		self.data = (*fData,)
	
	def __add__(self, other):
		return MathObj(self.data + other.data)
	
	def __mul__(self, other):
		return MathObj((i[0] * j[0],) + i[1:] + j[1:] for i, j in product(self.data, other.data))
	
	def __neg__(self):
		return nOne * self
	
	def __sub__(self, other):
		return self + -other
	
	def __repr__(self):
		return 'MathObj({!r})'.format(self.data)
	
	def __str__(self):
		if not self.data:
			return '0'
		return ' + '.join(' '.join(str(i) for i in j) for j in self.data).replace('+ -', '- ')
	
	def replace(self, replDict):
		acc = zero
		for term in self.data:
			nTerm = one
			for fact in term:
				nTerm *= replDict.get(fact, Variable(fact))
			acc += nTerm
		return acc

def Variable(name):
	if isinstance(name, str):
		return MathObj(((1, name),))
	return MathObj(((name,),))

zero = MathObj()
one = MathObj(((1,),))
nOne = MathObj(((-1,),))


































