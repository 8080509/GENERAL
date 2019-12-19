#Notes:

#the simplification system makes some statements take a long time, but allows the algorithm to evaluate faster for some other statements.

#the simplification system minimizes the arguments in an 'and' or 'or' type statement, and thereby increases efficiency, but does cause many calculations that are not needed for simpler statements.

#when a very large compound statement would be made, simplification does reduce the time to compute it, but it adds a lot of time when it can't reduce the statement at all.

from copy import copy
from Utils import nullFunc, powIterSub, defValDict
from itertools import chain

proofMethod = dict()

iterDbgFnCnts = defValDict(0)

def iterInpDbg(func):
	return func
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
	#not any more! - look two lines down
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
	
	def prove(self, a): #a = assumptions, t = tracker -- SHIFTED TO GLOBAL ; outputs: bool-succes
		key = tK(a, self)
		# print(key)
		# input('Prove ^ ')
		Tracker.tryProving(key)
		if key in Tracker:
			return Tracker[key][0]
		if (self == a) or (a.type == 'and' and self in a):
			Tracker[key] = (True, (key,))
			return True
		inDepA = {i for i in a.vars if (i is not nullVar) and (i not in self.vars)}
		Tracker[key] = (False, (key,))
		if inDepA: #escape clause - P(x) -> Q is equivalent to Exists[x](P(x)) -> Q, as P(x) -> Q is shorthand for Forall[x](P(x) -> Q)
			nA = Exists(a, inDepA)
			Tracker.startProving(key)
			res = self.prove(nA)	#forced closure
			Tracker[key] = (res, Tracker.stopProving(key, res))
			return res
		Tracker.startProving(key)
		nA = And((a, Not(self)))
		res = (self.prove(nA)									#contradiction
			or Implies(a, self).prove(And(()))					#implication
			or any(Forall(self, {*close}).prove(a) for close in
					powIterSub(filter(nullVar.__ne__, self.vars)))	#universal
			or (self.type in proofMethod
			and proofMethod[self.type](self, a))					#direct Proof
			or all(self.prove(case) for case in caseIter(a)))	#proof By Cases
		fRes = Tracker.stopProving(key, res)
		Tracker[key] = (res, fRes)
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
			self.proving[-1][1].append(key)
	
	#adds a new layer to the current proving history.
	def startProving(self, key):
		self.proving.append((key, [], []))
	
	#reads the last layer of the proving history.  Only returns the parts that match the result (and should thus imply it).
	#key for debug purposes only
	def stopProving(self, key, res):
		stor = self.proving.pop()
		tgt = stor[1]
		assert stor[0] is key
		return (*filter(lambda i: self[i][0] == res, tgt),)
	
	def trySimp(self, key):
		if self.proving:
			self.proving[-1][2].append(key)
	
	def startSimp(self, key):
		self.trySimp(key)
		self.startProving(key)
	
	def stopSimp(self, key):
		return self.stopProving(key, True)
	
	def fClear(self): #debug function.  Should not be needed.
		toRemove = set()
		for k, v in self.items():
			if not v:
				toRemove.add(k)
		for k in toRemove:
			del(self[k])

Tracker = ProofTracker()

# - - - - - Variable Collector Utility - - - - - #

def vcuPi(s, name):
	s.vars = (name,)

#just a utility function which creates an object to house an assumption and a statement to be proven, and drop the value of the arguments (but preserve the relation between those in the assumption and statement).
def varCollUtil(args, name):
	return Logic(args, 'vcu', vcuPi, name)

#self explanatory
def vcuPM(s, a):
	raise ValueError('VCU type statement should NEVER have a proof request.')

proofMethod['vcu'] = vcuPM

#convenient pairing function.
def tK(a,s):
	return varCollUtil((a,s), 'proof')

def sK(arg):
	return varCollUtil((arg,), 'simplify')

# - - - - - Simplification and Replacement Utility - - - - - #

#creates a 'replTemp' vcu, which functions as a \repl\acement \temp\late
def replUtil(orig, simp):
	out = varCollUtil((orig, simp), 'replTemp')
	# assert out.vars == orig.vars
	return out

#given a replacement template, and an original copy, the original ought to match the first entry of the transformed repl temp, the second entry being the desired output.
def simpRepl(repl, orig):
	repl = repl.copy()
	repl.vars = orig.vars
	assert repl[0] == orig
	return repl[1]

# - - - - - Extension - - - - - #

def extPi(s, count):
	s.vars += (*[Variable() for _ in range(count)],)

#mainly a utility for cooperation with schemas.
#adds free variables which have no effect on the truth of the statement.
def Ext(args, count):
	return Logic(args, 'ext', extPi, count)

def extPM(s, a):
	return s[0].prove(a)

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
	args = [*idempotentSimp(sorted(nArgs))]
	preSimp = Logic(args, 'and')
	simpKey = sK(preSimp)
	if simpKey in Tracker:
		return simpRepl(Tracker[simpKey][0], preSimp)
	if len(args) == 1:
		Tracker[simpKey] = (replUtil(preSimp, args[0]), ())
		return args[0]
	Tracker[simpKey] = (replUtil(preSimp, preSimp), ())
	Tracker.startSimp(simpKey)
	if any(
		any(
			Not(arg).prove(i)
			for i in args
		)
		for arg in args
	):
		out = Or(())
	else:
		nArgs = []
		while args: # for any arg, if another, say i, can prove arg, then arg is not needed.
			arg = args.pop(0)
			if not any((arg != i) and arg.prove(i) for i in chain(nArgs, args)):
				nArgs.append(arg)
		args = (*nArgs,)
		if len(args) == 1:
			out = args[0]
		else:
			out = Logic(args, 'and')
	fRes = Tracker.stopSimp(simpKey)
	Tracker[simpKey] = (replUtil(preSimp, out), fRes)
	return out

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

def andPM(s, a):
	return all(arg.prove(a) for arg in s)

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
	args = [*idempotentSimp(sorted(nArgs))]
	# ok, so the commented code below is just a special case of the immediately following code
	preSimp = Logic(args, 'or')
	simpKey = sK(preSimp)
	if simpKey in Tracker:
		return simpRepl(Tracker[simpKey][0], preSimp)
	if len(args) == 1:
		Tracker[simpKey] = (replUtil(preSimp, args[0]), ())
		return args[0]
	Tracker[simpKey] = (replUtil(preSimp, preSimp), ())
	Tracker.startSimp(simpKey)
	# Ok, experiment time!  We are going to add something stupid, disjunctions will be able to test if they are tautologies, and conjunctions will test for contradictions.  This will likely override the 'prove' algorithm as a whole, but ultimately the results will still be available to be read.
	if any(
		any(
			arg.prove(Not(i))
			for i in args
		)
		for arg in args
	):
		out = And(())
	else:
		nArgs = []
		while args:
			arg = args.pop(0)
			if not any((arg != i) and i.prove(arg) for i in chain(nArgs, args)):
				nArgs.append(arg)
		#sets = {arg: frozenset(conjIter(arg)) for arg in args}
		#for arg in [*sets]: # really did not want to add this part, but it seems to be needed for efficiency.
		#	val = sets.pop(arg)
		#	if not any(map(val.issuperset, sets.values())): # if any conjunction contains an existing conjunction, the former can be removed.
		#		sets[arg] = val
		args = (*nArgs,)
		if len(args) == 1:
			out = args[0]
		else:
			out = Logic(args, 'or')
	fRes = Tracker.stopSimp(simpKey)
	Tracker[simpKey] = (replUtil(preSimp, out), fRes)
	return out

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

def orPM(s, a):
	return any(arg.prove(a) for arg in s)

proofMethod['or'] = orPM

# - - - - - Negation - - - - -

negProc = {}

negProc['and'] = lambda arg: Or(Not(sub) for sub in arg)
negProc['or'] = lambda arg: And(Not(sub) for sub in arg)
negProc['not'] = lambda arg: arg[0]

# def allNegProc(s):
	# s = s.copy()
	# s.type = 'exists'
	# s.args = (Not(*s.args),)
	# s.setId()
	# return s

# def exNegProc(s):
	# s = s.copy()
	# s.type = 'forall'
	# s.args = (Not(*s.args),)
	# s.setId()
	# return s

def openIter(vars, opening):
	for var in vars:
		if var is nullVar:
			out = Variable()
			opening.add(out)
			yield out
		else:
			yield var

def allNegProc(s):
	s = s.copy()
	tempVars = set()
	s.vars = (*openIter(s.vars, tempVars),)
	return Exists(Not(s[0]), tempVars)

def exNegProc(s):
	s = s.copy()
	tempVars = set()
	s.vars = (*openIter(s.vars, tempVars),)
	return Forall(Not(s[0]), tempVars)

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
		out.setId()
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

def allPM(s, a):
	r = s.copy()
	r.vars = (*[Variable() if var is nullVar else var for var in s.vars],)
	return r[0].prove(a)
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
		out.setId()
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



























