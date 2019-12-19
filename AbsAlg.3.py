#This version is going to focus on logic without considering generalizations for sake of origination.

from abc import ABC, abstractmethod

objectRecoveryDict = dict()

class expression(ABC):
	
	def __init__(self, *args, **kwargs)
		self.args = args
		self.props = kwargs
	
	def setId(self):
		self.id = self.type + '[' + ', '.join(map(lambda i: str(i), self.args)) + ']'
	
	def str(self):
		return getattr(self, 'name', self.id)
	
	def __hash__(self):
		return hash(self.id)
	
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

def iterAssumed(assumptions):
	post = assumptions.copy()
	pre = set()
	base = True
	while len(post) != 0:
		arg = post.pop()
		if arg.type == 'or':
			base = False
			break
		if arg.type == 'and':
			pre.update(arg.args)
		else:
			pre.add(arg)
	if base:
		yield pre
		return
	for i in iterAssumed(post):
		temp = pre.union(i)
		for j in arg.args:
			if j.type == 'and':
				temp.update(j.args)
			else:
				temp.add(j)
			yield temp

class logic(expression):
	
	def _prove(self, assumptions):
		return False
	
	def prove(self, assumptions = dict()):
		if self in assumptions:
			return self.id + ':  ' + assumptions[self]
		opposite = Not(self)
		if opposite in assumptions:
			return False
		assumptions[opposite] = 'Contradiction'
		out = self._prove(assumptions)
		if out:
			assumptions.pop(opposite)
			assumptions[self] = 'Proven'
		else:
			assumptions[opposite] = 'Alt Case'
		return out
	
	def disprove(self, assumptions = dict()):
		return Not(self).prove(assumptions)

associativeSimp(args, key):
	newArgs = list()
	for arg in args:
		if arg.type == key:
			newArgs.extend(arg.args)
		else:
			newArgs.append(arg)
	return newArgs

idempotentSimp(args):
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
	arg = None
	for i in range(len(args)):
		if self.args[i].type == 'or':
			arg = args.pop(i)
			break
	if arg != None:
		return Or(*[And(*args, i) for i in arg.args])
	return _And(*args)

class _And(logic):
	
	type = 'and'
	
	def _prove(self, assumptions = dict()):  #Let Assumptions be a dictionary with assumed statements and their reasons.
		output = list()
		for arg in self.args:
			out = arg.prove(assumptions)
			if out:
				output.append(out)
			else:
				return False
		return self.id + ':  [' + ', '.join(output) + ']'

def Or(*args):
	args = associativeSimp(args, 'or')
	args.sort()
	args = idempotentSimp(args)
	return _Or(*args)

class _Or(logic):
	
	type = 'or'
	
	def _prove(self, assumptions = dict()):
		for arg in self.args:
			out = arg.prove(assumptions)
			if out:
				return self.id + ':  [' + output + ']'
		return False

def Not(arg):
	if arg.type == 'or':
		return And(*[Not(i) for i in arg.args])
	if arg.type == 'and':
		return Or(*[Not(i) for i in arg.args])
	return _Not(arg)

class _Not(logic):
	
	type = 'not'
	
	def _prove(self, assumptions = dict()):
		out = self.args[0].disprove(assumptions)
		if out:
			return self.id + ':  [' + out + ']'
		return False




























