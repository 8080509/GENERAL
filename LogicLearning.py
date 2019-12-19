from AbsAlg10 import Logic, Variable, ProofTracker
from Utils import kSing, defIterDict, uValDict
from itertools import chain, takewhile, starmap
from weakref import WeakKeyDictionary
import numpy as np

lSentinel = kSing('lSentinel')

# def LogicIterator(statement):
	# #logic type
	# yield statement.type
	# #variable list
	# for var in vars: yield var
	# yield lSentinel
	# #argument list
	# for val in chain.from_iterable(map(LogicIterator, statement.args)): yield val
	# yield lSentinel

def LogicIterator(statement):
	return chain(
		#logic type
		(statement.type,),
		#variable list
		statement.vars,
		(lSentinel,),
		#argument list
		chain.from_iterable(map(LogicIterator, statement)),
		(lSentinel,),
	)

tDict = uValDict(vIArgs = (0, 1))

def tDictRes():
	tDict.clear()
	tDict[lSentinel]# 0
	tDict['logic']	# 1
	tDict['vcu']	# 2
	tDict['ext']	# 3
	tDict['and']	# 4
	tDict['or']		# 5
	tDict['not']	# 6
	tDict['forall']	# 7
	tDict['exists']	# 8

def LogicReducer(i):
	return map(tDict.__getitem__, i)

def checkBase(s, a, t):
	key = tK(a, s)
	t.tryProving(key)
	if key in t:
		return key
	if (s == a) or (a.type == 'and' and s in a):
		t[key] = (True, ('assumption',))
		return key
	return False

t[key] = (False, (key,))
t.startProving(key)

fRes = t.stopProving(key, res)
	t[key] = (res, fRes)
	return res

def extPM(s, a):
	return Logic((s[0], a))

def andPM(s, a):
	return Logic((Logic((arg, a)) for arg in s), 'and')

def orPM(s, a):
	return Logic((Logic((arg, a)) for arg in s), 'or')

def allPM(s, a):
	if any(Variable.sDict[var] == s for var in a.vars):
		return Logic((Or(()),))
	r = s.copy()
	r.vars = (*[Variable(s, 'o') if var is nullVar else var for var in s.vars],)
	return Logic((r[0], a))

def exPMSub(s, a):
	ops = {*filter(nullVar.__ne__, a.vars)}
	for vars in exOpenGen(iter(s.vars), ops):
		r = s.copy()
		r.vars = vars
		yield Logic((r[0], a))

def exPM(s, a):
	return Logic(exPMSub(s, a), 'or')

proofMethod = {
	'ext'	: extPM,
	'and'	: andPM,
	'or'	: orPM,
	'forall': allPM,
	'exists': exPM,
}

def proveIter(s, a): #a = assumptions, t = tracker; outputs: bool-succes
	yield 'implication',	Logic((Implies(a, s), And(())
	yield 'contradiction',	Logic((s, And((a, Not(s)))))
	yield 'universal',		Logic((Logic((Forall(s, {*close}), a)) for close in powIterSub(filter(nullVar.__ne__, s.vars))), 'or')
	if s.type in proofMethod:
		yield 'direct',		proofMethod[s.type](s, a)
	yield 'cases',			Logic((Logic((s, case)) for case in caseIter(a)), 'and')

learnerLayers = [10, 10, 10]

layerCount = len(learnerLayers)

feedLen = learnerLayers[-1]

class Learner(object):
	
	def __init__(self, vals = None):
		if isinstance(vals, list):
			self.mats = vals
			return
		mSizes = [(learnerLayers[i-1], learnerLayers[i]) for i in range(layerCount)]
		if vals is None:
			self.mats = [*map(np.matrix, map(np.zeros, mSizes))]
			return
		if vals == 'rand':
			self.mats = [*map(np.matrix, map(lambda i: i * 2 - 1, starmap(np.random.rand, mSizes)))]
			return
		raise NotImplementedError('Given value ' + repr(vals) + ' could not initialize learner.')

def LearnerScore(statement, learner, prev):
	data = prev.copy()
	for val in LogicReducer(LogicIterator(statement)):
		data[0,0] = val
		data = learner(data)
	return data

routeKey = lambda i: i[0][0, 0]

routeFilter = lambda i: routeKey(i) < 0.5

def LearnerRun(statement, learner):
	tracker = ProofTracker()
	prevVals = [(False, iter([(LearnerScore(statement, learner, np.matrix(np.array([0] * feedLen))), ('root', statement))]))]
	res = False
	while True
		try:
			while True:
				if res != prevVals[-1][0]: #compare with default
					break
				pVal, (cause, sta) = next(prevVals[-1][1])
				yield False, sta
				if sta.type == 'logic':
					baseKey = checkBase(*sta, tracker):
					if baseKey:
						res = tracker[baseKey]
						yield True, res
						continue
					default = False
					staIter = filter(
						routeFilter,
						map(
							lambda i: (LearnerScore(i[1], learner, pVal), i),
							proveIter(sta)
						)
					)
				elif sta.type == 'and':
					#need all substatements true
					default = True
					staIter = map(
						lambda i: (LearnerScore(i, learner, pVal), (None, i)),
						sta
					)
				elif sta.type == 'or':
					#need any substatement true
					default = False
					staIter = filter(
						routeFilter,
						map(
							lambda i: (LearnerScore(i, learner, pVal), (None, i)),
							sta
						)
					)
				else:
					raise ValueError('Recived statement of inappropriate logical type.')
				res = default
				prevVals.append((default, iter(sorted(staIter, key = routeKey))))
		except StopIteration: pass
		except: raise
		#come here from break & StopIteration
		prevVals.pop()
		yield True, res #possibly add statement for verification purposes
		if not prevVals:
			






































