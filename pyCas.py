# I know I could probably just use sage, but where is the fun in that?

def getTex(mObj):
	return mObj.tex()

class MathObj(object):
	
	def __init__(self, parent, args):
		self.parent = parent
		self.args = args
	
	def __repr__(self):
		self.parent.instRepr(self)
	
	def tex(self):
		return self.parent.instTex(self)

class MathOp(object):
	
	def __init__(self, name, argChk = None, instEval = None, instRepr = None, instTex = None, instConstr = None):
		self.cls = MathOp
		self.__name__ = name
		if argChk is not None:
			self.argChk = staticmethod(argChk)
		if instEval is not None:
			self.instEval = staticmethod(instEval)
		if instRepr is not None:
			self.instRepr = staticmethod(instRepr)
		if instTex is not None:
			self.instTex = staticmethod(instTex)
		if instConstr is not None:
			self.__call__ = instConstr
	
	@staticmethod
	def argChk(args):
		return True
	
	def instEval(op, inst):
		return inst
	
	@staticmethod
	def instRepr(inst):
		msg = inst.parent.__name__
		msg += repr(inst.args)
		return msg
	
	@staticmethod
	def instTex(inst):
		msg = inst.parent.__name__
		msg += '(' + ', '.join(map(getTex, inst.args) + ')'
		return msg
	
	def __call__(self, *args):
		if not self.argChk(args):
			raise ValueError(str(args) + ' is an invalid argument collection for operation \'' + self.__name__ + '\'.')
		return MathObj(self, args)





















































