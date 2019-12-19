class Expression:
	
	type = 'expression'
	
	def __init__(self, *args, type = None, **kwargs):
		self.args = args
		self.props = kwargs
		if type is not None:
			self.type = type
		self.vars = list() # Variables, listed in sequential order, with an assigned value, or 'False' if the variable is free.
		varStore = dict()
		i = 0
		for arg in self.args:
			for j, val in enumerate(arg.vars):
				if val in varStore:
					arg.vars[j] = varStore[val]
					continue
				self.vars.append(val) #This also means, self.vars[i] = val
				arg.vars[j] = i
				if val: #We only want to store this if the variable is bound, i.e. val != False
					varStore[val] = i
				i += 1
		self.setId()
		self.postInit()
	
	def postInit(self): #To be used by various special expressions, such as 'ForAll' and 'Exists' being able to remove variables.
		pass
	
	def setId(self):
		out = self.props.name + ' : ' if 'name' in self.props else ''
		out += self.type + '[' + ', '.join(map(lambda i: str(i), self.args)) + ']'
		self.id = out
	
	def __str__(self):
		return self.id
	
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

class Assumptions:
	
	def __init__(self, root = None):
		if root is None:
			root = set()
		self.statement = And(root)
		#if self.statement.type == 'and': self.root = set(self.statement.args)
		#else: self.root = {self.statement}
	
	def __hash__(self):
		return hash(self.statement)
	
	def __contains__(self, item):
		return item in self.root
	
	def __iter__(self):
		return iter(self.root)
	
	def add(self, item):
		self.root.add(item)
		self.statement = And({self.statement, item})
	
	def cases(self): #Iterates through cases
		if self.statement.type == 'or':
			for arg in self.statement:
				yield AssumptionCase(arg)
			return
		yield Assumptions({self.statement})
		return

#class AssumptionCase:
#	
#	def __init__(self, statement):
#		assert statement.type != 'or'
#		if statement.type == 'and': self.root = set(statement.args)
#		else: self.root = {statement}
#	
#	def __contains__(self, item):
#		return item in self.root
#	
#	def __iter__(self):
#		return iter(self.root)

class ProofTracker: #Tracker = Tracker, Traker[assumption] = Dictionary of results from a given assumption, Tracker[assumption][statement] = Specific results of proving 'statement' given 'assumptions.'  Basically a cache.
	
	def __init__(self):
		self.data = dict()
	
	def getItem(self, key):
		if key not in self.data:
			self.data[key] = dict()
		return self.data[key]

class Logic(Expression):
	
	type = 'logic'
	
	def _prove(self, assumptions, tracker): #Outputs:  'False' if unproven, or else (<!--Used Assumptions,--> explanation information)
		return False
	
	def prove(self, assumptions, tracker, tryCont = True): #Same outputs.  Also manipulates tracker.
		#if assumptions == None: assumptions = Assumptions()
		#if tracker = None: tracker = ProofTracker()

class _Extension(Logic):
	
	type = 'extension'
	
	def _prove(self, assumptions, tracker):
		return prove(self.args[0], 

def And(args):
	

class _And(Logic):
	
	def _prove(self, assumptions, tracker):
		out = list()
		#used = set()
		for arg in self.args:
			x = arg.prove(assumptions, tracker)
			if not x: return False
			out.append((x[0], arg))
			#used.update(x[1])
		return out



class _Or(Logic)
		





















































