from abc import ABC, abstractmethod

classNameDict = dict([
	])

searching = set()

proving = set()

disproving = set()

class ITER:
	def __init__(self, func):
		self.func = func
	
	def __iter__(self):
		temp = self.func()
		while True:
			try:
				yield next(temp)
			except:
				raise

class expression(ABC):
	
	@abstractmethod
	def evaluate(self):
		pass
	
	def stdInfo(self): #Returns a string, common to all equivalent expressions from that class.
		return ', '.join(list(map(lambda i: i.id, self.args)))
	
	def postInit(self):
		pass
	
	def preInit(self):
		pass
	
	def argCheck(self):
		return True
	
	def __init__(self, form, *args):
		if form not in self.forms:
			raise ValueError('\'' + form + '\' is an invalid form for a ' + repr(type(self)) + ' object.')
		self.key = form
		self.args = args
		self.preInit()
		if not self.argCheck():
			raise ValueError('\'' + self.key + '\' object argCheck failed when given ' + str(args) + '.')
		if getattr(self, 'associative', False):
			associativeSimp(self)
		if getattr(self, 'commutative', False):
			commutativeSimp(self)
		if getattr(self, 'idempotent', False):
			idempotentSimp(self)
		self.postInit()
		self.setId()
	
	def stdId(self):
		return self.key + '[' + self.stdInfo() + ']'
	
	def setId(self):
		self.id = self.stdId()
	
	def __str__(self):
		return self.id
	
	def __eq__(self, other):
		return self.id == other.id
	
	def __lt__(self, other):
		return self.id < other.id
	
	def __gt__(self, other):
		return self.id > other.id
	
	def __le__(self, other):
		return self.id <= other.id
	
	def __ge__(self, other):
		return self.id >= other.id
	
	def __ne__(self, other):
		return self.id != other.id
	
	def __contains__(self, other):
		if other == self:
			return True
		if getattr(self, 'contCheck', lambda i: False)(other):
			return True
		for arg in self.args:
			if other in arg:
				return True
		return False

def And(*args):
	return logic('and', *args)

def Or(*args):
	return logic('or', *args)

def Not(*args):
	return logic('not', *args)

class logic(expression): #Logic expressions should be all which evaluate to True and False.
	
	@abstractmethod
	def causes(self):
		pass
	
	@abstractmethod
	def counters(self):
		pass
	
	def prove(self):
		proving.add(self.id)
		for cause in self.causes():
			if cause.key == 'True':
				break
			elif self in cause:
				#Write some special important code here.
			else:
				raise NotImplementedError(cause.id + ' implies ' + self.id)
	
	forms = {'and','or','not','implies','equals','True','False','var'}
	
	def preInit(self):
	
	def postInit(self):
		out = self
		if self.key == 'not':
			arg = self.args[0]
			if arg.key == 'not':
				out = arg.args[0]
			elif arg.key == 'and':
				out = Or(list(map(lambda i: Not(i), arg.args)))
			elif arg.key == 'or':
				out = And(list(map(lambda i: Not(i), arg.args)))
			elif hasattr(arg, negClass):
				out = arg.negClass(arg.args)
		elif self.key == 'and':
			arg = None
			for i in range(len(self.args)):
				if self.args[i].key == 'or':
					arg = self.args.pop(i)
					break
			if arg != None:
				out = Or([And(self.args + [i]) for i in arg.args])
		self.key = out.key
		self.args = out.args

associativeSimp(self):
	args = self.args # Generalizable for associative operations. [a + (b + c) = (a + b) + c]
	newArgs = list()
	for arg in args:
		if arg.key == self.key:
			newArgs.extend(arg.args)
		else:
			newArgs.append(arg)
	self.args = newArgs

commutativeSimp(self):
	self.args.sort()

idempotentSimp(self):
	args = self.args
	i = 0
	while i < len(args): # Generalizable for idempotent operations. [a + b + b = a + b]
		while i + 1 < len(args):
			if args[i] == args[i + 1]:
				args.pop(i + 1)
			else:
				break
		i += 1

#Break from object orientation.



"""
class Not(logic):
	
	key = 'not'
	
	def argCheck(args)
		return len(args) == 1
	
	def genStdForm(self):
		arg = self.args[0].stdForm
		if isinstance(arg, Not):
			return arg.args[0].stdForm
		elif isinstance(arg, And):
			return Or(list(map(lambda i: Not(i), arg.args))).stdForm
		elif isinstance(arg, Or):
			return And(list(map(lambda i: Not(i), arg.args))).stdForm
		elif hasattr(arg, negClass):
			return arg.negClass(arg.args).stdForm
		else:
			return Not(arg)
	
	def causes(self):
		for counter in self.args.counters():
			yield counter
	
	def counters(self):
		for cause in self.args.causes():
			yield cause
	
class Or(logic):
	
	key = 'or'
	
	def contCheck(self, other):
		if isinstance(other, Or):
			i = 0
			j = 0
			m = len(self.args)
			n = len(other.args)
			while True:
				if self.args[i] == other.args[j]:
					i += 1
				else:
					j += 1
				if i == m:
					return True
				elif j == n:
					return False
	
	def genStdForm(self):
		args = list(map(lambda i: i.stdForm, self.args))
		newArgs = list()
		for arg in args:
			if isinstance(arg, Or):
				newArgs.extend(arg.args)
			else:
				newArgs.append(arg)
		i = 0
		while i < len(newArgs):
			j = i
			while j < len(newArgs):
				if newArgs[i] == newArgs[j]:
					newArgs.pop(j)
				else:
					j += 1
			i += 1
		newArgs.sort()
"""























