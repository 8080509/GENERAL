#This version is going to focus on logic without considering generalizations for sake of origination.

from abc import ABC, abstractmethod

objectRecoveryDict = dict()

class expression(ABC):
	
	type = 'expression'
	
	def __init__(self, *args, **kwargs):
		self.args = args
		if 'name' in kwargs:
			self.name = kwargs.pop('name')
		self.props = kwargs
		self.setId()
	
	def setId(self):
		out = ''
		if hasattr(self, 'name'):
			out += self.name + ' : '
		out += self.type + '[' + ', '.join(map(lambda i: str(i), self.args)) + ']'
		self.id = out
	
	def __str__(self):
		return getattr(self, 'name', self.id)
	
	def __hash__(self):
		return hash(self.id)
	
	def __eq__(self, other):
		return (self.id == other.id) and (self.props == other.props)
	
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

def iterAssumed(assumptions):
	post = assumptions.copy()
	pre = dict()
	base = True
	keys = set(post)
	while len(post) != 0:
		arg = keys.pop()
		desc = post.pop(arg)
		if arg.type == 'or':
			base = False
			break
		if arg.type == 'and':
			desc = 'Sub of ' + str(arg) + ' by: ' + desc
			pre.update(map(lambda i: [i, desc], arg.args))
		else:
			pre[arg] = desc
	if base:
		yield pre
		return
	case = 0
	vals = list()
	for j in arg.args:
		tDesc = 'Case ' + str(case) + ' of ' + str(arg) + ' by: ' + desc
		case += 1
		if j.type == 'and':
			tDesc = 'Sub of ' + str(j) + ' by: ' + tDesc
			vals.append([[k, tDesc] for k in j.args])
		else:
			vals.append([[j, tDesc]])
	for i in iterAssumed(post):
		temp = pre.copy()
		temp.update(i)
		for j in vals:
			k = temp.copy()
			k.update(j)
			yield k

class logic(expression):
	
	type = 'logic'
	
	def _prove(self, assumptions, proving):
		return (False, self)
	
	#def prove(self, assumptions = None):
	#	if assumptions is None:
	#		assumptions = dict()
	#	if self in assumptions:
	#		return (True, self.id + ':  ' + assumptions[self])
	#	opposite = Not(self)
	#	if opposite in assumptions:
	#		return (False, self)
	#	assumptions[opposite] = 'Contradiction'
	#	out = self._prove(assumptions)
	#	if out[0]:
	#		assumptions.pop(opposite)
	#		assumptions[self] = 'Proven'
	#	else:
	#		assumptions[opposite] = 'Alt Case'
	#	return out
	
	def prove(self, tAssumptions = None, proving = None):
		if tAssumptions is None:
			tAssumptions = dict()
		if proving is None:
			proving = dict()
		if self in proving:
			if proving[self] == True:
				return (True, 'Proven')
			else:
				return (False, self)
		output = list()
		altOut = list()
		case = 0
		failed = False
		proving[self] = False
		for assumptions in iterAssumed(tAssumptions):
			#if len(assumptions):
			#	test = And(*assumptions).disprove()
			#else:
			#	test = (False,)
			#if test[0]:
			#	out = (True, 'Case ' + str(case) + ':  Confliction of assumptions.')
			#else:
			opposite = Not(self)
			if self in assumptions:
				out = (True, self.id + ':  ' + assumptions[self])
			else:
				assumptions[opposite] = 'Contradiction Hypothesis'
				out = self._prove(assumptions, proving)
			if out[0]:
				output.append('Case ' + str(case) + ':  ' + out[1])
			else:
				altOut.append(out[1])
				failed = True
			case += 1
		if failed:
			proving.pop(self,None)
			return (False, And(*altOut))
		proving[self] = True
		return (True, str(self) + ':  [' + ', '.join(output) + ']')
	
	def disprove(self, assumptions = None, proving = None):
		return Not(self).prove(assumptions, proving)

def associativeSimp(args, key):
	newArgs = list()
	for arg in args:
		if arg.type == key:
			newArgs.extend(arg.args)
		else:
			newArgs.append(arg)
	return newArgs

def idempotentSimp(args):
	args = args.copy()
	i = 0
	while i < len(args):
		while i + 1 < len(args):
			if args[i] == args[i + 1]:
				args.pop(i + 1)
			else:
				break
		i += 1
	return args

def And(*args):
	args = associativeSimp(args, 'and')
	args.sort()
	args = idempotentSimp(args)
	if len(args) == 1:
		return args[0]
	arg = None
	for i in range(len(args)):
		if args[i].type == 'or':
			arg = args.pop(i)
			break
	if arg is not None:
		return Or(*[And(*args, i) for i in arg.args])
	return _And(*args)

class _And(logic):
	
	type = 'and'
	
	def _prove(self, assumptions, proving):  #Let Assumptions be a dictionary with assumed statements and their reasons.
		output = list()
		altOut = list()
		failed = False
		for arg in self.args:
			out = arg.prove(assumptions, proving)
			if out[0]:
				output.append(out[1])
			else:
				failed = True
				altOut.append(out[1])
		if failed:
			return (False, And(*altOut))
		return (True, str(self) + ':  [' + ', '.join(output) + ']')

def Or(*args):
	args = associativeSimp(args, 'or')
	args.sort()
	args = idempotentSimp(args)
	if len(args) == 1:
		return args[0]
	return _Or(*args)

class _Or(logic):
	
	type = 'or'
	
	def _prove(self, tAssumptions, proving):
		assumptions = tAssumptions.copy()
		altOut = list()
		for arg in self.args:
			out = arg.prove(assumptions)
			if out[0]:
				return (True, str(self) + ':  [' + out[1] + ']')
			else:
				altOut.append(out[1])
		return (False, Or(*altOut))

def Not(arg):
	if arg.type == 'or':
		return And(*[Not(i) for i in arg.args])
	if arg.type == 'and':
		return Or(*[Not(i) for i in arg.args])
	if arg.type == 'not':
		return arg.args[0]
	if hasattr(arg, 'lNot'):
		return arg.lNot()
	return _Not(arg)

class _Not(logic):
	
	type = 'not'
	
	def _prove(self, assumptions, proving):
		out = self.args[0].disprove(assumptions, proving)
		if out[0]:
			return (True, str(self) + ':  [' + out[1] + ']')
		return out

"""class _ForAll(logic):
	
	type = 'forall'
	
	def lNot(self):
		#NOTE TO SELF:  ADD CAUSES CLAUSE TO PROVE CODE - UPON FAILURE TRACK WHAT CONDITION WOULD BE SUFFICIENT TO PROVE OUR STATEMENT

class _Exists(logic):
	
	type = 'exists'"""

def Implies(p,q):
	return Or(Not(p), q)

def IFF(p,q):
	return And(Implies(p,q), Implies(q,p))


























