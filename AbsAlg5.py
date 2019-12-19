#This version is going to focus on logic without considering generalizations for sake of origination.

import abc, collections

indVar = 0

def ioDebug(func):
	def temp(*args, **kwargs):
		global indVar
		print(('|' * indVar) + 'Calculating:  ', func.__name__, args, kwargs)
		indVar += 1
		val = func(*args, **kwargs)
		indVar -= 1
		print(('|' * indVar) + 'Result:  ', func.__name__, args, kwargs, '  :  ', val)
		return val
	return temp

#objectRecoveryDict = dict()

class AssumptionError(ValueError):
	pass

#objectRecoveryDict['expression'] = expression

class expression(abc.ABC):
	
	type = 'expression'
	
	def __init__(self, *args, **kwargs):
		self.args = args
		if 'name' in kwargs:
			self.name = kwargs.pop('name')
		self.props = kwargs
		if self.props.get('id', False) == True:
			self.props['id'] = id(self)
		self.setId()
		self.postInit()
	
	def postInit(self):
		pass
	
	def setId(self):
		out = ''
		if hasattr(self, 'name'):
			out += self.name + ' : '
		out += self.type + '[' + ', '.join(map(lambda i: str(i), self.args)) + ']'
		self.id = out
	
	def __str__(self):
		return getattr(self, 'name', self.id)
	
	__repr__ = __str__
	
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
	
	#def substitute(self, old, new, tracker = None):
	#	if tracker == None:
	#		tracker = [0]
	#	def eSub(item):
	#		if item == old:
	#			tracker[0] += 1
	#			return new
	#		elif isinstance(item, expression):
	#			return item.substitute(old, new, tracker)
	#	args = [eSub(arg) for arg in self.args]
	#	#for i in range(len(self.args)):
	#	#	arg = self.args[i]
	#	#	if arg == old:
	#	#		self.args[i] = new
	#	#		acc += 1
	#	#	elif isinstance(arg, expression):
	#	#		arg = arg.copy()
	#	#		acc += arg.substitute(old, new):
	#	#		self.args[i] = arg
	#	props = {prop: eSub(self.props[prop]) for prop in self.props}
	#	#for i in self.props:
	#	#	prop = self.props[i]
	#	#	if prop == old:
	#	#		self.props[i] = new
	#	#		acc += 1
	#	#	elif isinstance(prop, expression):
	#	#		prop = prop.copy()
	#	#		acc += prop.substitute(old,new)
	#	#		self.props[i] = prop
	#	if hasattr(self, 'name'):
	#		props['name'] = self.name
	#	return #objectRecoveryDict[self.type](*args, **props)
	
	#def copy(self):
	#	props = self.props.copy()
	#	if hasattr(self, 'name'):
	#		props['name'] = self.name
	#	out = #objectRecoveryDict[self.type](*self.args, **props)
	#	return out

#def iterAssumed(assumptions):
#	post = assumptions.copy()
#	pre = dict()
#	base = True
#	keys = set(post)
#	while len(post) != 0:
#		arg = keys.pop()
#		desc = post.pop(arg)
#		if arg.type == 'or':
#			base = False
#			break
#		if arg.type == 'and':
#			desc = 'Sub of ' + str(arg) + ' by: ' + desc
#			pre.update(map(lambda i: [i, desc], arg.args))
#		else:
#			pre[arg] = desc
#	if base:
#		yield pre
#		return
#	case = 0
#	vals = list()
#	for j in arg.args:
#		tDesc = 'Case ' + str(case) + ' of ' + str(arg) + ' by: ' + desc
#		case += 1
#		if j.type == 'and':
#			tDesc = 'Sub of ' + str(j) + ' by: ' + tDesc
#			vals.append([[k, tDesc] for k in j.args])
#		else:
#			vals.append([[j, tDesc]])
#	for i in iterAssumed(post):
#		temp = pre.copy()
#		temp.update(i)
#		for j in vals:
#			k = temp.copy()
#			k.update(j)
#			yield k

#def iterAssumed(assumptions):
#	ors = list(assumptions)
#	pre = list()
#	for statement in post.copy():
#		if post.type != 'or':
#			ors.remove(statement)
#			pre.append(statement)

class AssumptionDict:
	
	def __init__(self, *args):
		temp = dict(*args)
		self.root = dict()
		self.versions = [dict()] # Let each variation be a dict, containing statements, and a reference to a root statement.
		self.eliminated = list()
		for key in temp:
			assert isinstance(temp[key], str)
			self[key] = temp[key]
	
	def __delitem__(self, key):
		raise NotImplementedError()
	
	def __getitem__(self, key):
		raise NotImplementedError()
	
	def __setitem__(self, key, item):
		#if isinstance(key, list):
		#	key = key[0]
		#else:
		#	test = key.disprove(self) #TODO:  key.disprove runs Not(key).prove which runs assumptions[key] = 'Contradiction Hypothesis' - Which will cause a loop.
		#	if test[0]:
		#		raise AssumptionError(test[1])
		self.root[key] = item
		newVers = list()
		if key.type == 'and':
			newVers = list()
			for var in self.versions:
				test = key.disprove(AssumptionDict(AssumptionSub(var,self)),tryCont = False)
				if test[0]:
					self.eliminated.append(test[1])
				else:
					temp = var.copy()
					for arg in key.args:
						if arg not in temp:
							temp[arg] = list()
						temp[arg].append(key) # add a new link to the
					newVers.append(temp)
		elif key.type == 'or': # We want to make copies of the variations
			for var in self.versions:
				for arg in key.args:
					test = arg.disprove(AssumptionDict(AssumptionSub(var,self)))
					if test[0]:
						self.eliminated.append(test[1])
					else:
						temp = var.copy()
						if arg not in temp:
							temp[arg] = list()
						temp[arg].append(key)
						newVers.append(temp)
		else:
			for var in self.versions:
				test = key.disprove(AssumptionDict(AssumptionSub(var,self)), tryCont = False)
				if test[0]:
					self.eliminated.append(test[1])
				else:
					temp = var.copy()
					if key not in temp:
						temp[key] = list()
					temp[key].append(key)
					newVers.append(temp)
		self.versions = newVers
	
	def __iter__(self):
		#if len(self.versions) == 0:
		#	yield dict()
		#	return
		out = iter(self.versions)
		while True:
			yield AssumptionSub(next(out), self)
	
	__len__ = lambda i: len(i.versions)
	
	def __repr__(self):
		return 'AssumptionDict(' + repr(self.root) + ')'

class AssumptionSub(collections.Mapping):
	
	def __init__(self, data, parent):
		self.data = data
		self.sup = parent
	
	def __len__(self):
		return len(self.data)
	
	def __getitem__(self, key):
		refs = self.data[key]
		out = [str(ref) + ' [' + self.sup.root[ref] + ']' for ref in refs]
		return 'Sub of:  [' + ', '.join(out) + ']'
	
	def __iter__(self):
		return iter(self.data)
	
	def __repr__(self):
		return 'AssumptionSub(' + repr(self.data) + ', ' + repr(self.sup) + ')'

#objectRecoveryDict['logic'] = logic

class logic(expression):
	
	type = 'logic'
	
	def postInit(self):
		self.freeVars = set()
		for arg in self.args:
			self.freeVars.update(arg.freeVars)
	
	@ioDebug
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
	
	@ioDebug
	def prove(self, tAssumptions = None, proving = None, tryCont = True):
		#print('Proving:  ' + self.id, 'Assuming:  ', tAssumptions.versions)
		if tAssumptions is None:
			tAssumptions = AssumptionDict()
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
		proving[self] = False # Ah HA!  I found the issue.  When this line is called, it is possible that the AssumptionDict does not cycle at all.
		for assumptions in tAssumptions: # Used to use iterAssumed(tAssumptions) - Now use tAssumptions as an AssumptionDict.
			#if len(assumptions):
			#	test = And(*assumptions).disprove()
			#else:
			#	test = (False,)
			#if test[0]:
			#	out = (True, 'Case ' + str(case) + ':  Confliction of assumptions.')
			#else:
			#print('Assuming:  ', dict(assumptions))
			if self in assumptions:
				out = (True, self.id + ':  ' + assumptions[self])
			else:
				assumptions = AssumptionDict(assumptions)
				if tryCont:
					assumptions[Not(self)] = 'Contradiction Hypothesis'
				out = self._prove(assumptions, proving)
			if out[0]:
				output.append('Case ' + str(case) + ':  ' + out[1])
			else:
				altOut.append(out[1])
				failed = True
			case += 1
		if failed:
			#print('Failed to prove:  ' + self.id)
			proving.pop(self, None)
			return (False, And(*altOut))
		proving[self] = True
		#print('Successfully proved:  ' + self.id, ', '.join(output))
		return (True, str(self) + ':  [' + ', '.join(output) + ']')
	
	def disprove(self, assumptions = None, proving = None, tryCont = True):
		return Not(self).prove(assumptions, proving, tryCont)

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

#objectRecoveryDict['and'] = _And

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
	
	@ioDebug
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

#objectRecoveryDict['or'] = _Or

def Or(*args):
	args = associativeSimp(args, 'or')
	args.sort()
	args = idempotentSimp(args)
	if len(args) == 1:
		return args[0]
	return _Or(*args)

class _Or(logic):
	
	type = 'or'
	
	@ioDebug
	def _prove(self, assumptions, proving):
		altOut = list()
		for arg in self.args:
			out = arg.prove(assumptions, proving)
			if out[0]:
				return (True, str(self) + ':  [' + out[1] + ']')
			else:
				altOut.append(out[1])
		return (False, Or(*altOut))

#objectRecoveryDict['not'] = _Not

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
	
	@ioDebug
	def _prove(self, assumptions, proving):
		out = self.args[0].disprove(assumptions, proving)
		#if out[0]:
		#	return (True, str(self) + ':  [' + out[1] + ']')
		return out

#objectRecoveryDict['forall'] = _ForAll

def ForAll(freeVar, Statement):
	newVar = expression(name = Statement.substitute(freeVar, expression(name = 'freeVar').id))
	return _ForAll(newVar, Statement.substitute(freeVar, newVar))

class _ForAll(logic):  #Todo:  Teach system how to handle ForAll and Exists in assumptions.
	
	type = 'forall'
	
	def postInit(self):
		self.freeVars = self.args[1].freeVars.copy()
		self.freeVars.discard(self.args[0])
	
	def _prove(self, assumptions, proving):
		out = self.args[1].prove(assumptions, proving)
		return out
	
	def lNot(self):
		return Exists(self.args[0], Not(self.args[1]))

#objectRecoveryDict['exists'] = _Exists

def Exists(freeVar, Statement):
	newVar = expression(name = True)
	newStatement = Statement.copy()
	newStatement.substitute(freeVar, newVar)
	return _Exists(newVar, newStatement)

class _Exists(logic):
	
	type = 'exists'
	
	def postInit(self):
		self.freeVars = self.args[1].freeVars.copy()
		self.freeVars.discard(self.args[0])
	
	def _prove(self, assumptions, proving):
		out = self.args[1].prove(assumptions, proving)
		return out
	
	def lNot(self):
		return ForAll(self.args[0], Not(self.args[1]))

def Implies(p,q):
	return Or(Not(p), q)

def IFF(p,q):
	return And(Implies(p,q), Implies(q,p))

#Begin Set Theory Axioms
#
#ZFC = dict()
#
##Defining Containment
#
#Contains = logic(name = 'Contains', id = True)
#
#ContainsX = expression(name = 'X', id = True)
#ContainsY = expression(name = 'Y', id = True)
#
#Contains.freeVars = {ContainsX, ContainsY}
#
##Defining Equality - Axiom of Extensionality
#
#Equals = logic(name = 'Equals', id = True)
#
#EqualsX = expression(name = 'X', id = True)
#EqualsY = expression(name = 'Y', id = True)
#
#Equals.freeVars = {EqualsX, EqualsY}
#
#ExtensionZ = expression(name = 'Z', id = True)
#
#ZFC[
#	ForAll(
#		EqualsX,
#		ForAll(
#			EqualsY,
#			IFF(
#				Equals,
#				ForAll(
#					ExtensionZ,
#					IFF(
#						Contains.substitute(ContainsX, ExtensionZ).substitute(ContainsY, EqualsX),
#						Contains.substitute(ContainsX, ExtensionZ).substitute(ContainsY, EqualsY)
#					)
#				)
#			)
#		)
#	)
#] = 'Extensionality'
#
#ZFC[
#	ForAll(
#		EqualsX,
#		ForAll(
#			EqualsY,
#			IFF(
#				Equals,
#				ForAll(
#					ExtensionZ,
#					IFF(
#						Contains.substitute(ContainsY, ExtensionZ).substitute(ContainsX, EqualsX),
#						Contains.substitute(ContainsY, ExtensionZ).substitute(ContainsX, EqualsY)
#					)
#				)
#			)
#		)
#	)
#] = 'Substitution of Equality'
#
##Axiom of Regularity
#
#Reg1 = expression(name = 'Reg1', id = True)
#Reg2 = expression(name = 'Reg2', id = True)
#Reg3 = expression(name = 'Reg3', id = True)
#
#ZFC[
#	ForAll(
#		ContainsY,
#		Implies(
#			Exists(
#				ContainsX,
#				Contains
#			),
#			Exists(
#				Reg1,
#				And(
#					Contains.substitute(ContainsX, Reg1),
#					ForAll(
#						ContainsX,
#						Or(
#							Not(Contains.substitute(ContainsY, Reg1),
#							Not(Contains)
#						)
#					)
#				)
#			)
#		)
#	)
#] = 'Regularity'
#
##Schema of Specification
#
#
#
#
#
















