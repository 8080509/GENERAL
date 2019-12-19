from pyCas import *
from itertools import repeat

def reprParDrop(item, dropPar):
	val = getRep(item)
	if item.parent in dropPar:
		val = val[1:-1]
	return val

def texParDrop(item, dropPar):
	val = getTex(item)
	if item.parent in dropPar:
		val = val[6:-7]
	return val

multParDrop = {
	Add
}

def multIRepr(inst):
	return '(' + ' * '.join(map(reprParDrop, inst.args, repeat(multParDrop))) + ')'

def multITex(inst):
	return '\\left(' + ' '.join(map(texParDrop, inst.args, repeat(multParDrop))) + '\\right)'

def multIEval(op, inst):
	acc = multId
	for arg in inst.args:
		acc = acc.mul(arg)
	return acc

def commonIConstr(op, args):
	if len(args) == 0:
		return multId
	if len(args) == 1:
		return args[0]
	nArgs = []
	for arg in args:
		if arg.parent is op:
			nArgs.extend(arg.args)
		else:
			nArgs.append(arg)
	args = (*nArgs,)
	return MathObj(op, args)

Mult = MathOp('Mult', instEval = multIEval, instRepr = multIRepr, instConstr = commonIConstr)





































