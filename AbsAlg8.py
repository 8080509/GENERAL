from copy import copy
from Utils import nullFunc, powIterSub, defValDict

proofMethod = dict()

iterDbgFnCnts = defValDict(0)

def iterInpDbg(func):
	# return func
	name = func.__name__
	def out(arg):
		lstInp = [*arg]
		num = str(iterDbgFnCnts[name])
		print('Starting ' + name + ' #' + num + ' with args:\n\t' + repr(lstInp))
		iterDbgFnCnts[name] += 1
		res = func(lstInp)
		iterDbgFnCnts[name] -= 1
		print('Stopping ' + name + ' #' + num + ' returning:\n\t' + repr(res))
		return res
	return out

def varMap(nVL, vD, sVL):
	for var in sVL:
		if var not in vD:
			vD[var] = len(nVL)
			nVL.append(var)
		yield vD[var]

class Variable(object):
	
	def __init__(self, name = None):
		self.id = id(self)
		if name is None:
			self.name = 'v' + ('%X' % self.id)
		else:
			self.name = name
	
	def __lt__(self, other):
		return self.id < other.id
	
	def __repr__(self):
		return self.name

nullVar = Variable('null')

# - - - - - Logic - - - - - #

class Logic(object):
	
	#note to self:  the args in args get mutated!
	def __init__(self, args, type = 'logic', postInit = nullFunc, pip = None):
		self.args = (*map(copy, args),)
		self.type = type
		vList = []
		vDict = {nullVar: -1}
		for arg in self.args:
			arg.vars = (*varMap(vList, vDict, arg.vars),)
			arg.setId()
		self.vars = (*vList,)
		postInit(self, pip)
		self.setId()
	
	def setId(self):
		self.id = (self.type, self.args, self.vars)
		self.hash = hash(self.id)
	
	def copy(self):
		return copy(self)
	
	def __getitem__(self, key):
		arg = self.args[key].copy()
		#arg.vars = (*map(self.vars.__getitem__, arg.vars),) #like (*(self.vars[i] for i in arg.vars),) except faster!
		arg.vars = (*[nullVar if k == -1 else self.vars[k] for k in arg.vars],)
		arg.setId()
		return arg
	
	def __iter__(self):
		for arg in self.args:
			arg = arg.copy()
			# arg.vars = (*map(self.vars.__getitem__, arg.vars),)
			arg.vars = (*[nullVar if k == -1 else self.vars[k] for k in arg.vars],)
			arg.setId()
			yield arg
	
	def __contains__(self, item):
		return any(item == arg for arg in self)
	
	def prove(self, a, t): #a = assumptions, t = tracker; outputs: bool-succes
		key = tK(a, self)
		# print(key)
		# input('Prove ^ ')
		t.tryProving(key)
		if key in t:
			return t[key][0]
		if (self == a) or (a.type == 'and' and self in a):
			t[key] = (True, (key,))
			return True
		inDepA = {i for i in a.vars if (i is not nullVar) and (i not in self.vars)}
		t[key] = (False, (key,))
		if inDepA: #escape clause - P(x) -> Q is equivalent to Exists[x](P(x)) -> Q, as P(x) -> Q is shorthand for Forall[x](P(x) -> Q)
			nA = Exists(a, inDepA)
			t.startProving(key)
			res = self.prove(nA, t)	#forced closure
			t[key] = (res, t.stopProving(key, res))
			return res
		t.startProving(key)
		nA = And((a, Not(self)))
		res = (self.prove(nA, t)									#contradiction
			or Implies(a, self).prove(And(()), t)					#implication
			or any(Forall(self, {*close}).prove(a, t) for close in
					powIterSub(filter(nullVar.__ne__, self.vars)))	#universal
			or (self.type in proofMethod
			and proofMethod[self.type](self, a, t))					#direct Proof
			or all(self.prove(case, t) for case in caseIter(a)))	#proof By Cases
		fRes = t.stopProving(key, res)
		t[key] = (res, fRes)
		return res
	
	def __ne__(self, other):
		return self.id != other.id
	
	def __eq__(self, other):
		return self.id == other.id
	
	def __lt__(self, other):
		return self.id < other.id
	
	def __le__(self, other):
		return self.id <= other.id
	
	def __gt__(self, other):
		return self.id > other.id
	
	def __ge__(self, other):
		return self.id >= other.id
	
	def __hash__(self):
		return self.hash
	
	#makes a nice hierarchical representation of the given logic object.
	def expRepr(self, shift):
		msg = '\n'
		msg += '|  ' * shift
		msg += '>' + self.type
		msg += '[' + ', '.join(repr(var) for var in self.vars) + ']('
		msg += ''.join(arg.expRepr(shift + 1) for arg in self.args)
		msg += '\n' + ('|  ' * shift) + ')'
		return msg
	
	def __repr__(self):
		return self.expRepr(0)

nullLog = Logic(())

# - - - - - Assumptions & Proof Tracking - - - - - #

class Assumptions(Logic):
	pass

#returns an iterable which yields the different cases of an assumption.
def caseIter(s):
	if s.type == 'or':
		return s
	else:
		return (s,)

def conjIter(s):
	if s.type == 'and':
		return s
	else:
		return (s,)

class ProofTracker(dict):
	
	def __init__(self, *args, **kwargs):
		super(ProofTracker, self).__init__(*args, **kwargs)
		self.proving = [] #the proving history holds, for each statement, the statements it requested be proven
	
	#flags that a new statement is trying to be proven.
	def tryProving(self, key):
		if self.proving:
			self.proving[-1].append(key)
	
	#adds a new layer to the current proving history.
	def startProving(self, key):
		self.proving.append([key])
	
	#reads the last layer of the proving history.  Only returns the parts that match the result (and should thus imply it).
	#key for debug purposes only
	def stopProving(self, key, res):
		tgt = self.proving.pop()
		assert tgt.pop(0) is key
		return (*filter(lambda i: self[i][0] == res, tgt),)
	
	def fClear(self): #debug function.  Should not be needed.
		toRemove = set()
		for k, v in self.items():
			if not v:
				toRemove.add(k)
		for k in toRemove:
			del(self[k])

# - - - - - Variable Collector Utility - - - - - #

def vcuPi(s, _):
	s.vars = ()

#just a utility function which creates an object to house an assumption and a statement to be proven, and drop the value of the arguments (but preserve the relation between those in the assumption and statement).
def varCollUtil(args):
	return Logic(args, 'vcu', vcuPi)

#self explanatory
def vcuPM(s, a, t):
	raise ValueError('VCU type statement should NEVER have a proof request.')

#convenient pairing function.
def tK(a,s):
	return varCollUtil((a,s))

# - - - - - Extension - - - - - #

def extPi(s, count):
	s.vars += (*[Variable() for _ in range(count)],)

#mainly a utility for cooperation with schemas.
#adds free variables which have no effect on the truth of the statement.
def Ext(args, count):
	return Logic(args, 'ext', extPi, count)

def extPM(s, a, t):
	return s[0].prove(a, t)

proofMethod['ext'] = extPM

# - - - - - Open Statement - - - - - #

def staPi(s, vars):
	s.vars = vars

#convenient function to add open statements with some given variables.
def openSta(name, vars = ()):
	if name in proofMethod:
		raise ValueError('\'name\' parameter of statement definition must not be a defined logical type.')
	return Logic((), name, staPi, vars)

# - - - - - Conjunction - - - - - #

def idempotentSimp(args):
	prev = nullLog
	for arg in args:
		if arg == prev:
			continue
		prev = arg
		yield arg

@iterInpDbg
def And(args):
	nArgs = []
	args = iter(args)
	for arg in args:
		if arg.type == 'and':
			nArgs.extend(arg)
		elif arg.type == 'or':
			aList = [*nArgs, *args]
			return Or(And(aList + [sArg]) for sArg in arg)
		else:
			nArgs.append(arg)
	args = (*idempotentSimp(sorted(nArgs)),)
	if len(args) == 1:
		return args[0]
	return Logic(args, 'and')

def RevAnd(args):
	nArgs = []
	args = iter(args)
	for arg in args:
		if arg.type == 'and':
			nArgs.extend(arg)
		else:
			nArgs.append(arg)
	args = (*idempotentSimp(sorted(nArgs)),)
	if len(args) == 1:
		return args[0]
	return Logic(args, 'and')

def andPM(s, a, t):
	return all(arg.prove(a, t) for arg in s)

proofMethod['and'] = andPM

# - - - - - Disjunction - - - - - #

@iterInpDbg
def Or(args): # rewrite
	nArgs = []
	args = iter(args)
	for arg in args:
		if arg.type == 'or':
			nArgs.extend(arg)
		else:
			nArgs.append(arg)
	args = idempotentSimp(sorted(nArgs))
	sets = {arg: frozenset(conjIter(arg)) for arg in args}
	for arg in [*sets]: # really did not want to add this part, but it seems to be needed for efficiency.
		val = sets.pop(arg)
		if not any(map(val.issuperset, sets.values())): # if any conjunction contains an existing conjunction, the former can be removed.
			sets[arg] = val
	args = (*sets,)
	if len(args) == 1:
		return args[0]
	return Logic(args, 'or')

# def _Or(args):
	# nArgs = []
	# args = iter(args)
	# for arg in args:
		# if arg.type == 'or':
			# nArgs.extend(arg)
		# else:
			# nArgs.append(arg)
	# args = (*idempotentSimp(sorted(nArgs)),)
	# if len(args) == 1:
		# return args[0]
	# return Logic(args, 'or')

# def Or(args):
	# return Not(And(map(Not, args))) #... what?  Well, it's for optimization.  I could pass it through RevOr for the same effect.

#this may be very stupid...
# def Or(args):
	# out = RevOr(args)
	# if out.type == 'and':
		# return And(out)
	# return out

# def Or(args):
	# nArgs = []
	# args = iter(args)
	# for arg in args:
		# if arg.type == 'or':
			# nArgs.extend(arg)
		# elif arg.type == 'and':
			# aList = [*nArgs, *args]
			# nArgs = (Or(aList + [sArg]) for sArg in arg)
			# break
		# else:
			# nArgs.append(arg)
	# args = (*idempotentSimp(sorted(nArgs)),)
	# if len(args) == 1:
		# return args[0]
	# return Logic(args, 'or')

def RevOr(args):
	nArgs = []
	args = iter(args)
	for arg in args:
		if arg.type == 'or':
			nArgs.extend(arg)
		elif arg.type == 'and':
			aList = [*nArgs, *args]
			return RevAnd(RevOr(aList + [sArg]) for sArg in arg)
		else:
			nArgs.append(arg)
	args = (*idempotentSimp(sorted(nArgs)),)
	if len(args) == 1:
		return args[0]
	return Logic(args, 'or')

def orPM(s, a, t):
	return any(arg.prove(a, t) for arg in s)

proofMethod['or'] = orPM

# - - - - - Negation - - - - -

negProc = {}

negProc['and'] = lambda arg: Or(Not(sub) for sub in arg)
negProc['or'] = lambda arg: And(Not(sub) for sub in arg)
negProc['not'] = lambda arg: arg[0]

def allNegProc(s):
	s = s.copy()
	s.type = 'exists'
	s.args = (Not(*s.args),)
	s.setId()
	return s

def exNegProc(s):
	s = s.copy()
	s.type = 'forall'
	s.args = (Not(*s.args),)
	s.setId()
	return s

negProc['forall'] = allNegProc
negProc['exists'] = exNegProc

defNeg = lambda arg: Logic((arg,), 'not')

def Not(arg):
	return negProc.get(arg.type, defNeg)(arg)

# no PM for negations.  A root negation is a parity of an open (root) statement.  It can only be proven by connections in assumptions.

# - - - - - Universal Quantification - - - - - #

# note for mom aisha - qandisha

def allPi(s, closing):
	s.vars = (*[nullVar if var in closing else var for var in s.vars],)

def Forall(statement, closing):
	if not any(map(closing.__contains__, statement.vars)):
		return statement # If the statement has no dependence on the closing variables, we just want the same statement.  [forall x P(y)] = P(y)
	if statement.type == 'forall':
		out = statement.copy()
		allPi(out, closing)
		return out
	if statement.type == 'and':
		return And(Forall(arg, closing) for arg in statement)
	if statement.type == 'or':
		cArgs = []
		oArgs = []
		for arg in statement:
			if any(map(closing.__contains__, arg.vars)):
				cArgs.append(arg)
			else:
				oArgs.append(arg)
		oArgs.append(Logic((Or(cArgs),), 'forall', allPi, closing))
		return Or(oArgs)
	return Logic((statement,), 'forall', allPi, closing)

# def varReplGen(vIter, options):
	# try:
		# var = next(vIter)
	# except StopIteration:
		# yield ()
		# return
	# except: raise
	# if var is not nullVar:
		# var = (var,)
		# for arg in varReplGen(vIter, closing): yield var + arg
		# return
	# for arg in varReplGen(vIter, closing):
		# for var in options:
			# yield var + arg

def varReplGen(vIter, closing):
	try:
		var = next(vIter)
	except StopIteration:
		yield ()
		return
	except: raise
	if var is not nullVar:
		var = (var,)
		for arg in varReplGen(vIter, closing): yield var + arg
		return
	var = Variable()
	closing.add(var)
	var = (var,)
	nVar = (nullVar,)
	for arg in varReplGen(vIter, closing):
		yield  var + arg
		yield nVar + arg

# def allOpenGen(s):
	# # sVars = iter(s.vars)
	# # next(sVars)
	# vIter = varReplGen(iter(s.vars), set())
	# r = s.copy()
	# r.vars = next(vIter)
	# #we don't bother setting r.id, as we get rid of it two lines from now.
	# yield r[0]
	# for vars in vIter:
		# r = s.copy()
		# r.vars = vars
		# r.setId()
		# yield r

def allPM(s, a, t):
	r = s.copy()
	r.vars = (*[Variable() if var is nullVar else var for var in s.vars],)
	return r[0].prove(a, t)
	# return any(r.prove(a, t) for r in allOpenGen(s))

proofMethod['forall'] = allPM

# - - - - - Existential Quantification - - - - - #

exPi = allPi

def Exists(statement, closing):
	if not any(map(closing.__contains__, statement.vars)):
		return statement
	if statement.type == 'exists':
		out = statement.copy()
		exPi(out, closing)
		return out
	if statement.type == 'or':
		return Or(Exists(arg, closing) for arg in statement)
	if statement.type == 'and':
		cArgs = []
		aArgs = []
		for arg in statement:
			if any(map(closing.__contains__, arg.vars)):
				cArgs.append(arg)
			else:
				aArgs.append(arg)
		aArgs.append(Logic((And(cArgs),), 'exists', exPi, closing))
		return And(aArgs)
	return Logic((statement,), 'exists', exPi, closing)

# def exAllGen(s):
	# closing = set()
	# vIter = varReplGen(iter(s.vars), closing)
	# r = s.copy()
	# r.vars = next(vIter)
	# yield Forall(r[0], closing)
	# for vars in vIter:
		# r = s.copy()
		# r.vars = vars
		# r.setId()
		# yield Forall(r, closing)

# def exPM(s, a, t):
	# return any(r.prove(a, t) for r in exAllGen(s))

# proofMethod['exists'] = exPM

# Let's try no PM for existential quantification.  The axiom, Exists x (True) is an axiom, after all.

# - - - - - Schema - - - - - #

#this one is going to be more difficult.  I can easily show it in the 'meta-logic' implementation as a 'forall statements' line, but even for 'meta-logic' a schema is needed.

#They are easy enough to prove, at least.

# - - - - - Useful Macros - - - - - #

def Implies(A, B):
	return Or((Not(A), B))

def IFF(A, B):
	return Or((And((Not(A), Not(B))), And((A, B))))



























