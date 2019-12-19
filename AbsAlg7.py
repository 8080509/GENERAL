from copy import copy
from Utils import nullFunc

proofMethod = dict()

def varMap(nVL, vD, sVL):
	for var in sVL:
		if var not in vD:
			vD[var] = len(nVL)
			nVL.append(var)
		yield vD[var]

class Variable(object):
	
	def __lt__(self, other):
		return self.id < other.id

nullVar = Variable()

# - - - - - Logic - - - - - #

class Logic(object):
	
	def __init__(self, args, type = 'logic', postInit = nullFunc, pip = None):
		self.args = args
		self.type = type
		vList = []
		vDict = {0:0}
		for arg in self.args:
			arg.vars = (*varMap(vList, vDict, arg.vars),)
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
		arg.vars = (*map(self.vars.__getitem__, arg.vars),) #like (*(self.vars[i] for i in arg.vars),) except faster!
		arg.setId()
		return arg
	
	def __iter__(self):
		for arg in self.args:
			arg = arg.copy()
			arg.vars = (*map(self.vars.__getitem__, arg.vars),)
			arg.setId()
			yield arg
	
	def prove(self, a, t): #a = assumptions, t = tracker; outputs: bool-succes
		#nA = new Assumptions
		#rA = required Assumptions
		key = (a, self)
		if key in t:
			return t[key][0]
		t[key] = (False,)
		#Implement Cont. Hyp, and universal derivation here!
		aCont = Not(self)
		if aCont.type == 'or':  #Ensures aCont is not a disjunction, and thus reduces case demands.
			aCont = RevOr(aCont)
		if aCont.type != 'and':  #If aCont is a conjunction, we want each argument of aCont, otherwise, we want aCont itself to be added to nA.  Q:  Do we need to have two separate assumption dictionaries / sets?  I think so.  Also, need an intelligent way to handle universal and existential quantifiers.  We can have them sink through their respective junctions, but can this always be done to an arbitrary degree?  I doubt it.
			aCont = (aCont,)
		nA = a.union(aCont)
		#
		t.startProving(key)
		res= proofMethod[self.type](self, nA, t)
		fRes = t.stopProving(key, res)
		rA = set()
		for sKey in fRes:
			rA.update(t[sKey][2])
		rA = frozenset(rA.difference(aCont))
		t[key] = (res, fRes, rA)
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

nullLog = Logic(())

# - - - - - Assumptions & Proof Tracking - - - - - #

class Assumptions(frozenset):
	pass

class ProofTracker(dict):
	
	def __init__(self, *args, **kwargs):
		super(ProofTracker, self).__init__(*args, **kwargs)
		self.proving = []
	
	def startProving(self, key):
		self.proving.append([key])
	
	#key for debug purposes only
	def stopProving(self, key, res):
		tgt = self.proving.pop()
		assert tgt.pop(0) is key
		if not tgt:
			return ()
		if self[tgt[0]][0] != res:
			return (tgt[-1],)
		return (*tgt,)
	
	def fClear(self): #debug function.  Should not be needed.
		toRemove = set()
		for k, v in self.items():
			if not v:
				toRemove.add(k)
		for k in toRemove:
			del(self[k])

# - - - - - Extension - - - - - #

def extPi(s, count):
	s.vars += (*[Variable() for _ in range(count)],)

def Ext(args, count):
	return Logic(args, 'ext', extPi, count)

def extPM(s, a, t):
	return s[0].prove(a, t)

proofMethod['ext'] = extPM

# - - - - - Open Statement - - - - - #

def staPi(s, vars):
	s.vars = vars

def openSta(name, vars):
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

def And(args):
	nArgs = []
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

def Or(args):
	nArgs = []
	for arg in args:
		if arg.type == 'or':
			nArgs.exted(arg)
		else:
			nArgs.append(arg)
	args = (*idempotentSimp(sorted(nArgs)),)
	if len(args) == 1:
		return args[0]
	return Logic(args, 'or')

def RevOr(args):
	nArgs = []
	for arg in args:
		if arg.type == 'or':
			nArgs.exted(arg)
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
	s.type = 'Exists'
	s.args = (Not(*s.args),)
	s.setId()
	return s

def exNegProc(s):
	s = s.copy()
	s.type = 'Forall'
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
	return Logic((statement,), 'forall', allPi, closing)

def varReplGen(vIter, closing):
	try:
		var = next(vIter)
	except StopIteration:
		yield ()
		return
	except: raise
	if var is not nullVar:
		var = (var,)
		for arg in varReplGen(vIter): yield arg + var
		return
	var = Variable()
	closing.add(var)
	var = (var,)
	nVar = (nullVar,)
	for arg in varReplGen(vIter):
		yield arg + var
		yield arg + nVar

def allOpenGen(s):
	vIter = varReplGen(iter(s.vars), set())
	r = s.copy()
	r.vars = next(vIter)
	#we don't bother setting r.id, as we get rid of it two lines from now.
	yield r[0]
	for vars in vIter:
		r = s.copy()
		r.vars = vars
		r.setId()
		yield r

def allPM(s, a, t):
	return any(r.prove(a, t) for r in allOpenGen(s))

proofMethod['forall'] = allPM

# - - - - - Existential Quantification - - - - - #

exPi = allPi

def Exists(statement, closing):
	if not any(map(closing.__contains__, statement.vars)):
		return statement
	return Logic((statement,), 'exists', exPi, closing)

def exAllGen(s):
	closing = set()
	for vars in varReplGen(iter(s.vars), closing):
		r = s.copy()
		r.vars = vars
		r.setId()
		yield Forall(r, closing)

def exPM(s, a, t):
	return any(r.prove(a, t) for r in exAllGen(s))

proofMethod['exists'] = exPM

# - - - - - Schema - - - - - #

#this one is going to be more difficult.  I can easily show it in the 'meta-logic' implementation as a 'forall statements' line, but even for 'meta-logic' a schema is needed.

#They are easy enough to prove, at least.



























