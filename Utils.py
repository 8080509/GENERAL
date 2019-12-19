from weakref import WeakValueDictionary, WeakKeyDictionary, ref
from itertools import count

class defDict(object):
	
	def __init__(self, defVal, dataType = dict, *args): #defVal is an iterable yielding functions of the form func(parent, key) -> object bound to parent 'parent', at location parent[key]
		self.data = dataType(*args)
		self.defVal = iter(defVal)
	
	def __getitem__(self, key):
		if key not in self.data: self.data[key] = next(self.defVal)(self, key)
		return self.data[key]
	
	def __setitem__(self, key, value):
		self.data[key] = value
	
	def __iter__(self):
		return iter(self.data)
	
	def values(self):
		return self.data.values()
	
	def keys(self):
		return self.data.keys()
	
	def items(self):
		return self.data.items()
	
	def get(self, k, d):
		return self.data.get(k, d)

def repIter(val): #generator that endlessly yields a single value
	while True: yield val

def vFunc(val): #wrapper which returns a function that returns a value, regardless of argument.
	def out(*args, **kwargs): return val
	return out

def cFunc(func): #wrapper which voids arguments, calling its argument
	def out(*args, **kwargs): return func()
	return out

def defFuncDict(defFunc, *args):
	return defDict(repIter(defFunc), *args)

def defIterDict(iterable, *args):
	return defDict((vFunc(i) for i in iterable), *args)

def defValDict(val, *args):
	return defDict(repIter(vFunc(val)), *args)

def defCallDict(func, *args):
	return defDict(repIter(cFunc(func)), *args)

class housing(object):
	
	def __init__(self, val = None):
		self.value = val
	
	def __iter__(self): #Just for convenience so you can say x, = X; where X is a housing, and x is the stored value
		yield self.value
		return

class falseIndexible(object):
	
	def __init__(self, func):
		self.__getitem__ = func
		# self.func = func

	# def __getitem__(self, key):
		# return self.func(key)

def seqInd(seq, vals): #Takes a sorted sequence, and indexes each value from the vals iterable, also sorted.
	#print('Starting seqInd with ' + str((seq, vals)))
	i = 0
	x = iter(seq)
	for val in vals:
		while next(x) != val: #It is not implemented, but one should make this raise an exception if x raises a StopIteration exception.
			i += 1
		#print('yielding ' + str(i))
		yield i
		i += 1
	#print('Ending seqInd with ' + str((seq, vals)))

def square(val):
	return val*val

def plotLine(p1,p2, range = None): #p1,p2 are both (x,y) tuples.
	x1, y1 = p1
	x2, y2 = p2
	if range is not None: range.value = (x1, x2)
	return str((y2 - y1)/(x2 - x1)) + '*(x - ' + str(x1) + ') + ' + str(y1)

def iterMerge(*iters):
	x = iter(iters)
	while True:
		try:
			y = iter(next(x))
		except StopIteration:
			return
		except: raise
		while True:
			try:
				z = next(x)
			except StopIteration:
				break
			except: raise
			yield z

def nullFunc(*args, **kwargs):
	pass

class FalseContainer(object):
	
	def __init__(self, func):
		self.__contains__ = func

omniCont = FalseContainer(vFunc(True))

def powIterSub(iterator):
	try:
		val = [next(iterator)]
	except StopIteration:
		yield []
		return
	except: raise
	for sub in powIterSub(iterator):
		yield sub
		yield val + sub

def powIter(coll):
	return powIterSub(iter(coll))

#keyed singleton class
class kSing(object):
	
	instances = WeakValueDictionary()
	
	def __new__(cls, key):
		if key in instances:
			return instances[key]
		val = super(kSing, cls).__new__(cls)
		instances[key] = val
		return val

class uValDict(object):
	
	def __init__(self, dataType = dict, valIter = count, vIArgs = (0, 1))
		self.dType = dataType
		self.vIter = valIter
		self.vArgs = vIArgs
		self.clear()
	
	def clear(self):
		self.data = self.dType()
		self.recovered = set()
		self.valIter = self.vIter(*self.vArgs)
	
	def __getitem__(key):
		if key not in self.data:
			if self.recovered:
				val = self.recovered.pop()
			else:
				val = next(valIter)
			self.data[key] = val
		return self.data[key]
	
	def __delitem__(key):
		self.recovered.add(self.data.pop(key))































